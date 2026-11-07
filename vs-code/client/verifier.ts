import { toolchainEnvironment } from "../shared/toolchain";
export { toolchainEnvironment } from "../shared/toolchain";
import { promises as fs } from "fs";
import * as path from "path";
import * as os from "os";
import * as https from "https";
import * as http from "http";
import { createHash } from "crypto";
import { gunzipSync } from "zlib";
import { execFile } from "child_process";
import { promisify } from "util";
const run = promisify(execFile);
export class CompatibilityError extends Error {
    constructor(message: string) { super(message); this.name = "CompatibilityError"; }
}
/** Caravan and its linked Raven API travel with a matching OCaml stdlib and Z3. */
export interface Manifest {
    version: string;
    lsp_protocol: number;
    min_z3: string;
    ocaml_version: string;
    raven_api_version: number;
}
export interface Toolchain {
    source: "configured" | "managed" | "bundled" | "path";
    executable: string;
    arguments: string[];
    bundleRoot?: string;
    manifest?: Manifest;
}
export interface ResolveOptions {
    extensionPath: string;
    storagePath: string;
    executable?: string;
    arguments?: string[];
    channel: "stable" | "tag" | "bundled";
    version?: string;
}
export interface Release {
    tag: string;
    manifest: Manifest;
    assets: Map<string, string>;
}
export interface TransferOptions {
    signal?: AbortSignal;
    onProgress?: (message: string) => void;
    apiBase?: string;
    allowHttpForTests?: boolean;
    asset?: string;
}
export function normalizeVersion(v: string): string {
    return v.replace(/^v/, "");
}
function parts(v: string): RegExpMatchArray {
    const m = normalizeVersion(v).match(/^(0|[1-9]\d*)\.(0|[1-9]\d*)\.(0|[1-9]\d*)(?:-([0-9A-Za-z.-]+))?$/);
    if (!m)
        throw new Error(`Invalid version: ${v}`);
    return m;
}
export function compareVersions(a: string, b: string): number {
    const x = parts(a), y = parts(b);
    for (let i = 1; i < 4; i++) {
        const d = Number(x[i]) - Number(y[i]);
        if (d)
            return Math.sign(d);
    }
    if (x[4] === y[4])
        return 0;
    if (!x[4])
        return 1;
    if (!y[4])
        return -1;
    const aa = x[4].split("."), bb = y[4].split(".");
    for (let i = 0; i < Math.max(aa.length, bb.length); i++) {
        if (aa[i] === undefined)
            return -1;
        if (bb[i] === undefined)
            return 1;
        if (aa[i] === bb[i])
            continue;
        const an = /^\d+$/.test(aa[i]), bn = /^\d+$/.test(bb[i]);
        return an && bn ? Math.sign(Number(aa[i]) - Number(bb[i])) : an ? -1 : bn ? 1 : aa[i] < bb[i] ? -1 : 1;
    }
    return 0;
}
export function validateManifest(value: unknown): Manifest {
    const m = value as Manifest;
    if (!m || typeof m.version !== "string" || typeof m.min_z3 !== "string" || typeof m.ocaml_version !== "string" || !Number.isInteger(m.lsp_protocol) || m.lsp_protocol < 1 || !Number.isInteger(m.raven_api_version) || m.raven_api_version < 1)
        throw new Error("Incompatible or invalid Caravan manifest");
    if (m.lsp_protocol !== 1)
        throw new CompatibilityError(`Caravan ${m.version} uses editor protocol ${m.lsp_protocol}; this extension supports protocol 1. Update the Caravan extension to use this release.`);
    parts(m.version);
    parts(m.min_z3);
    if (!/^\d+\.\d+(?:\.\d+)?(?:[+~.-][\w.+~-]+)?$/.test(m.ocaml_version))
        throw new Error("Invalid OCaml version");
    return { version: m.version, lsp_protocol: m.lsp_protocol, min_z3: m.min_z3,
        ocaml_version: m.ocaml_version, raven_api_version: m.raven_api_version };
}
export async function readManifest(executable: string, bundleRoot?: string, arguments_: string[] = [], cwd?: string): Promise<Manifest> {
    const result = await run(executable, [...arguments_, "--manifest"], {
        env: toolchainEnvironment(bundleRoot),
        timeout: 15000,
        maxBuffer: 65536,
        cwd
    });
    return validateManifest(JSON.parse(result.stdout));
}
const exe = (name: string) => process.platform === "win32" ? `${name}.exe` : name;
/** Reject incomplete bundles before selecting or publishing them. */
async function inspect(root: string): Promise<Manifest> {
    const m = validateManifest(JSON.parse(await fs.readFile(path.join(root, "manifest.json"), "utf8")));
    const actual = await readManifest(path.join(root, "bin", exe("caravan")), root);
    if (JSON.stringify(m) !== JSON.stringify(actual)) {
        for (const k of Object.keys(m) as (keyof Manifest)[])
            if (m[k] !== actual[k])
                throw new Error("Executable manifest differs from bundle manifest");
    }
    await fs.access(path.join(root, "lib", "ocaml", "stdlib.cmi"));
    const z3 = await run(path.join(root, "bin", exe("z3")), ["--version"], {
        env: toolchainEnvironment(root),
        timeout: 15000,
        maxBuffer: 65536
    });
    const version = z3.stdout.match(/\b(\d+\.\d+\.\d+)\b/)?.[1];
    if (!version || compareVersions(version, m.min_z3) < 0)
        throw new Error("Bundled Z3 is too old");
    return m;
}
export async function resolveToolchain(o: ResolveOptions): Promise<Toolchain> {
    if (o.executable?.trim())
        return {
            source: "configured",
            executable: o.executable,
            arguments: o.arguments || []
        };
    const bundled = path.join(o.extensionPath, "bundled");
    let bm: Manifest | undefined;
    try {
        bm = await inspect(bundled);
    }
    catch {
    }
    if (o.channel !== "bundled") {
        const dir = path.join(o.storagePath, "verifier");
        let names: string[] = [];
        try {
            names = await fs.readdir(dir);
        }
        catch {
        }
        const candidates = names.filter(name => {
            try { parts(name); return normalizeVersion(name) === name; }
            catch { return false; }
        }).sort((a, b) => compareVersions(b, a));
        for (const name of candidates) {
            try {
                if (o.channel === "tag" && normalizeVersion(o.version || "") !== name)
                    continue;
                if (o.channel === "stable" && (parts(name)[4] || (bm && compareVersions(name, bm.version) < 0)))
                    continue;
                const root = path.join(dir, name), m = await inspect(root);
                if (normalizeVersion(m.version) !== name)
                    continue;
                return {
                    source: "managed",
                    executable: path.join(root, "bin", exe("caravan")),
                    arguments: [],
                    bundleRoot: root,
                    manifest: m
                };
            }
            catch {
            }
        }
    }
    if (bm)
        return {
            source: "bundled",
            executable: path.join(bundled, "bin", exe("caravan")),
            arguments: [],
            bundleRoot: bundled,
            manifest: bm
        };
    return {
        source: "path",
        executable: "caravan",
        arguments: []
    };
}
export function platformAsset(platform: NodeJS.Platform = process.platform, arch: string = process.arch): string | undefined {
    const target = `${platform}-${arch}`;
    return ["linux-x64", "darwin-arm64", "win32-x64"].includes(target) ? `caravan-${target}.tar.gz` : undefined;
}
async function download(url: string, options: TransferOptions, limit: number, redirects = 0): Promise<Buffer> {
    options.signal?.throwIfAborted();
    const u = new URL(url);
    if (u.protocol !== "https:" && !(options.allowHttpForTests && u.protocol === "http:" && ["127.0.0.1", "localhost", "[::1]"].includes(u.hostname)))
        throw new Error("HTTPS required");
    if (redirects > 5)
        throw new Error("Too many redirects");
    return new Promise((resolve, reject) => {
        const req = (u.protocol === "https:" ? https : http).get(u, {
            headers: {
                "User-Agent": "caravan-verifier",
                "Accept": "application/vnd.github+json"
            },
            signal: options.signal
        }, res => {
            if (res.statusCode && [301, 302, 303, 307, 308].includes(res.statusCode)) {
                res.resume();
                if (!res.headers.location) {
                    reject(new Error("Missing redirect"));
                    return;
                }
                download(new URL(res.headers.location, u).href, options, limit, redirects + 1).then(resolve, reject);
                return;
            }
            if (res.statusCode !== 200) {
                res.resume();
                reject(new Error(`HTTP ${res.statusCode}`));
                return;
            }
            const chunks: Buffer[] = [];
            let size = 0;
            res.on("data", (chunk: Buffer) => {
                size += chunk.length;
                if (size > limit) {
                    res.destroy(new Error("Download too large"));
                    return;
                }
                chunks.push(chunk);
            });
            res.on("end", () => resolve(Buffer.concat(chunks)));
            res.on("error", reject);
        });
        req.setTimeout(30000, () => req.destroy(new Error("Download timed out")));
        const timer = setTimeout(() => req.destroy(new Error("Download deadline exceeded")), 120000);
        req.on("close", () => clearTimeout(timer));
        req.on("error", reject);
    });
}
export async function fetchRelease(tag?: string, options: TransferOptions = {}): Promise<Release> {
    if (tag) parts(tag);
    const base = options.apiBase || "https://api.github.com/repos/nyu-acsys/caravan";
    const response = JSON.parse((await download(`${base}/releases/${tag ? "tags/" + encodeURIComponent(tag) : "?per_page=100"}`, options, 2 * 1024 * 1024)).toString());
    const data = tag ? response : Array.isArray(response) ? response.find((r: {
        tag_name?: string;
        draft?: boolean;
        prerelease?: boolean;
        assets?: {
            name: string;
        }[];
    }) => r && !r.draft && !r.prerelease && typeof r.tag_name === "string" && /^v?\d+\.\d+\.\d+$/.test(r.tag_name) && Array.isArray(r.assets) && r.assets.some(a => a && a.name === "manifest.json")) : undefined;
    if (!data)
        throw new Error("No Caravan verifier release found");
    if (typeof data.tag_name !== "string" || !Array.isArray(data.assets))
        throw new Error("Invalid release");
    parts(data.tag_name);
    const assets = new Map<string, string>();
    for (const a of data.assets)
        if (a && typeof a.name === "string" && typeof a.browser_download_url === "string")
            assets.set(a.name, a.browser_download_url);
    const manifestUrl = assets.get("manifest.json");
    if (!manifestUrl)
        throw new Error("Missing manifest");
    const manifest = validateManifest(JSON.parse((await download(manifestUrl, options, 65536)).toString()));
    if (normalizeVersion(manifest.version) !== normalizeVersion(data.tag_name))
        throw new Error("Release version mismatch");
    return {
        tag: data.tag_name,
        manifest,
        assets
    };
}
function checked(data: Buffer, name: string, sums: string): void {
    const lines = sums.split(/\r?\n/);
    const hashes = lines.map(l => l.match(/^([a-fA-F0-9]{64}) [ *](.+)$/)).filter(m => m && m[2] === name);
    if (hashes.length !== 1 || hashes[0]![1].toLowerCase() !== createHash("sha256").update(data).digest("hex"))
        throw new Error(`Checksum mismatch: ${name}`);
}
/** Only regular USTAR files and directories are accepted; links and PAX are rejected. */
async function extract(archive: Buffer, root: string, signal?: AbortSignal): Promise<void> {
    const tar = gunzipSync(archive, {
        maxOutputLength: 512 * 1024 * 1024
    });
    let offset = 0;
    const seen = new Set<string>();
    while (offset + 512 <= tar.length) {
        signal?.throwIfAborted();
        const h = tar.subarray(offset, offset + 512);
        offset += 512;
        if (h.every(v => v === 0))
            return;
        const str = (a: number, n: number) => h.subarray(a, a + n).toString("utf8").replace(/\0.*$/s, "");
        const raw = str(0, 100), prefix = str(345, 155);
        const name = (prefix ? prefix + "/" : "") + raw;
        const relative = name.replace(/^\.\//, "").replace(/\/$/, "");
        const type = str(156, 1);
        const sizeText = str(124, 12).trim();
        if (!/^[0-7]+$/.test(sizeText))
            throw new Error("Invalid tar size");
        const size = parseInt(sizeText, 8);
        let checksum = 0;
        for (let i = 0; i < 512; i++)
            checksum += i >= 148 && i < 156 ? 32 : h[i];
        if (checksum !== parseInt(str(148, 8).trim(), 8))
            throw new Error("Invalid tar checksum");
        if (!relative || relative.includes("\\") || relative.includes(":") || path.posix.isAbsolute(relative) || relative.split("/").some(p => p === "." || p === ".." || p === "" || /[. ]$/.test(p)) || seen.has(relative) || !["", "0", "5"].includes(type))
            throw new Error("Unsafe archive entry");
        seen.add(relative);
        if (offset + size > tar.length)
            throw new Error("Truncated archive");
        const dest = path.join(root, relative);
        if (type === "5") {
            await fs.mkdir(dest, {
                recursive: true
            });
        }
        else {
            await fs.mkdir(path.dirname(dest), {
                recursive: true
            });
            await fs.writeFile(dest, tar.subarray(offset, offset + size), {
                flag: "wx",
                mode: parseInt(str(100, 8).trim(), 8) & 511
            });
        }
        offset += Math.ceil(size / 512) * 512;
    }
    throw new Error("Truncated tar archive");
}
export async function installRelease(release: Release, storagePath: string, options: TransferOptions = {}): Promise<string> {
    if (!release || typeof release.tag !== "string" || !(release.assets instanceof Map))
        throw new Error("Invalid release");
    validateManifest(release.manifest);
    const version = normalizeVersion(release.tag);
    parts(version);
    if (version !== normalizeVersion(release.manifest.version))
        throw new Error("Release version mismatch");
    const asset = options.asset || platformAsset();
    if (!asset)
        throw new Error("Unsupported platform");
    const get = (name: string) => {
        const url = release.assets.get(name);
        if (!url)
            throw new Error(`Missing release asset: ${name}`);
        return url;
    };
    const sums = (await download(get("SHA256SUMS"), options, 1024 * 1024)).toString();
    const manifestBytes = await download(get("manifest.json"), options, 65536);
    checked(manifestBytes, "manifest.json", sums);
    const m = validateManifest(JSON.parse(manifestBytes.toString()));
    for (const key of Object.keys(release.manifest) as (keyof Manifest)[])
        if (m[key] !== release.manifest[key])
            throw new Error("Release manifest changed");
    options.onProgress?.("Downloading Caravan toolchain");
    const archive = await download(get(asset), options, 256 * 1024 * 1024);
    checked(archive, asset, sums);
    const parent = path.join(storagePath, "verifier");
    await fs.mkdir(parent, {
        recursive: true
    });
    const stage = await fs.mkdtemp(path.join(parent, ".install-"));
    const destination = path.join(parent, version);
    try {
        await extract(archive, stage, options.signal);
        const installed = await inspect(stage);
        for (const key of Object.keys(m) as (keyof Manifest)[])
            if (installed[key] !== m[key])
                throw new Error("Archive manifest mismatch");
        const smoke = await fs.mkdtemp(path.join(os.tmpdir(), "caravan-smoke-"));
        try {
            const file = path.join(smoke, "smoke.ml");
            await fs.writeFile(file, "let identity (x : int) = x\n(*@ r = identity x ensures r = x *)\n");
            await run(path.join(stage, "bin", exe("caravan")), ["--shh", file], {
                cwd: smoke, env: toolchainEnvironment(stage), timeout: 30000,
                maxBuffer: 65536, signal: options.signal
            });
        } finally {
            await fs.rm(smoke, { recursive: true, force: true });
        }
        options.signal?.throwIfAborted();
        try {
            await fs.access(destination);
            throw new Error("Version already installed");
        }
        catch (e) {
            if ((e as NodeJS.ErrnoException).code !== "ENOENT")
                throw e;
        }
        await fs.rename(stage, destination);
        return destination;
    }
    finally {
        await fs.rm(stage, {
            recursive: true,
            force: true
        });
    }
}
