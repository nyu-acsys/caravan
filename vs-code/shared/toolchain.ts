import * as path from "path";

export function toolchainEnvironment(bundleRoot?: string, base: NodeJS.ProcessEnv = process.env,
    platform: NodeJS.Platform = process.platform): NodeJS.ProcessEnv {
    const environment = { ...base };
    if (!bundleRoot) return environment;
    const windows = platform === "win32";
    const paths = windows ? path.win32 : path;
    let inheritedPath = base.PATH;
    if (windows) {
        // Node forwards only one spelling of each case-insensitive Windows variable.
        for (const key of Object.keys(environment)) {
            if (key.toUpperCase() === "PATH") {
                if (inheritedPath === undefined) inheritedPath = environment[key];
                delete environment[key];
            } else if (key.toUpperCase() === "OCAMLLIB") {
                delete environment[key];
            }
        }
    }
    environment.OCAMLLIB = paths.join(bundleRoot, "lib", "ocaml");
    environment.PATH = paths.join(bundleRoot, "bin") + (windows ? ";" : path.delimiter) + (inheritedPath || "");
    return environment;
}

/** Excludes developer opam and package-manager paths during native bundle tests. */
export function systemPath(base: NodeJS.ProcessEnv = process.env,
    platform: NodeJS.Platform = process.platform): string {
    if (platform !== "win32") return "/usr/bin:/bin";
    const rootKey = Object.keys(base).find(key => key.toUpperCase() === "SYSTEMROOT");
    const root = rootKey && base[rootKey];
    if (!root) throw new Error("Windows SystemRoot is missing");
    return path.win32.join(root, "System32") + ";" + root;
}
