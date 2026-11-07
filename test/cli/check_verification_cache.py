import json
import pathlib
import shutil
import subprocess
import tempfile


executable = shutil.which("caravan")
assert executable


with tempfile.TemporaryDirectory(dir=".", prefix="cache-check-") as directory:
    root = pathlib.Path(directory).resolve()
    source = root / "cached.ml"
    cache = root / "cache"
    args = ["--lsp-mode", "--lsp-annotations", "--cache-dir", str(cache), str(source)]

    def program(body="identity flag", extra="", prefix=""):
        return prefix + """let identity value = value
(*@ result = identity value pure ensures result === value *)

let first (flag : bool) = BODY
(*@ result = first flag ensures result === flag EXTRA *)

let second (value : int) = identity value
(*@ result = second value ensures result === value *)

let caller (flag : bool) = first flag
(*@ result = caller flag ensures result === flag *)

module Other = struct
  let retained (flag : bool) = not (not flag)
  (*@ result = retained flag ensures result === flag *)
end

let with_helper (flag : bool) =
  let helper value = not value in
  (*@ result = helper value ensures result === not value *)
  not (helper flag)
(*@ result = with_helper flag ensures result === flag *)
""".replace("BODY", body).replace("EXTRA", extra)

    def verify(text, success=True, streaming=False):
        source.write_text(text, encoding="utf-8")
        if streaming:
            request = {"id": "cache", "cwd": str(root), "args": args, "partial": True}
            process = subprocess.run([executable, "--server"], input=json.dumps(request) + "\n",
                                     text=True, capture_output=True, timeout=120)
            assert process.returncode == 0, process.stderr
            frames = [json.loads(line) for line in process.stdout.splitlines()]
            final = frames[-1]
            status, output = final["exit"], final["stdout"]
            assert any(frame.get("phase") == "scheduled" for frame in frames)
        else:
            process = subprocess.run([executable] + args, text=True,
                                     capture_output=True, timeout=120)
            status, output = process.returncode, process.stdout
        assert status == (0 if success else 1), (output, process.stderr)
        report = json.loads(output)
        return {member["name"]: member for member in report["members"]}

    def cached(members, names, expected=True):
        for name in names:
            assert members[name]["status"] == "verified", members[name]
            assert members[name]["cached"] is expected, members[name]

    leaves = ["first", "second", "caller", "Other.retained", "with_helper"]
    original = program()
    cached(verify(original), leaves, False)
    cached(verify(original, streaming=True), leaves)

    # New polymorphic calls and shifted source positions must not rename other checks.
    edited = program("let helper value = not value in\n"
                     "(*@ result = helper value ensures result === not value *)\n"
                     "let _ = identity (true, false) in not (helper flag)",
                     prefix="(* moved *)\n\n")
    members = verify(edited)
    cached(members, ["first"], False)
    cached(members, ["second", "caller", "Other.retained", "with_helper"])
    cached(verify(edited), leaves)

    # A contract edit invalidates callers, even though their own source is unchanged.
    contracted = program(extra="ensures result || not result")
    members = verify(contracted)
    cached(members, ["first", "caller"], False)
    cached(members, ["second", "Other.retained"])

    # Failed proofs never become successful cache entries.
    broken = program("assert flag; identity flag")
    for _ in range(2):
        members = verify(broken, success=False)
        assert members["first"]["status"] == "failed", members["first"]
        assert not members["first"]["cached"], members["first"]
        cached(members, ["second", "Other.retained"])
