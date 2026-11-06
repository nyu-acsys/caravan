"""Exercise source-interface discovery using an independent Dune workspace."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

caravan = shutil.which("caravan")
assert caravan
environment = dict(os.environ)
for name in ["DUNE_ROOT", "DUNE_SOURCEROOT", "DUNE_BUILD_DIR", "DUNE_WORKSPACE", "DUNE_INSIDE_DUNE"]:
    environment.pop(name, None)

def run(file, *args, success=True):
    result = subprocess.run(
        [caravan, "--shh", *args, str(file)],
        capture_output=True, text=True, timeout=30, env=environment,
    )
    if success:
        assert result.returncode == 0, result.stdout + result.stderr
    else:
        assert result.returncode != 0, result.stdout
    return result.stdout + result.stderr

with tempfile.TemporaryDirectory(prefix="caravan dune project ") as temporary:
    root = Path(temporary).resolve()
    files = {
        "dune-project": "(lang dune 3.12)\n(name discovery_fixture)\n",
        "values/dune": "(library (name values) (wrapped false))\n",
        "values/values.ml": "let increment value = value + 1\n",
        "values/values.mli": """val increment : int -> int
(*@ result = increment value
    requires 0 <= value && value < 1000
    ensures result === value + 1 *)
""",
        "values/values.proof": "This implementation proof must not be imported.\n",
        "middle/dune": "(library (name middle) (wrapped false) (libraries values))\n",
        "middle/middle.ml": "let step value = Values.increment (Values.increment value)\n",
        "middle/middle.mli": """val step : int -> int
(*@ result = step value
    requires 0 <= value && value < 998
    ensures result === value + 2 *)
""",
        "app/dune": "(executable (name main) (libraries middle))\n",
        "app/main.ml": """let run () =
  assert (Values.increment 41 = 42);
  assert (Middle.step 41 = 43)
""",
        "app/main.mli": "val run : unit -> unit\n",
        "unrelated/dune": "(library (name unrelated) (wrapped false))\n",
        "unrelated/unrelated.ml": "let impossible = ()\n",
        "unrelated/unrelated.mli": "val impossible : Unavailable.t\n",
    }
    for name, contents in files.items():
        target = root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(contents)
    main = root / "app/main.ml"
    assert "Verification successful." in run(main)
    report = json.loads(run(main, "--lsp-mode", "--lsp-annotations", "--lsp-annotations-only"))
    assert not report["errors"], report["errors"]
    dependencies = {Path(file).resolve() for file in report["dependencies"]}
    for name in ["dune-project", "values/dune", "values/values.mli", "middle/dune", "middle/middle.mli", "app/dune"]:
        assert root / name in dependencies, (name, dependencies)
    assert not any("unrelated" in path.parts for path in dependencies)
    assert not any(root.rglob("*.cmi")), "Discovery unexpectedly compiled the project"
    disabled = run(main, "--no-dune", success=False)
    assert "Unbound module Values" in disabled, disabled
    override = root / "manual"
    override.mkdir()
    (override / "values.mli").write_text(files["values/values.mli"].replace("value + 1", "value + 3"))
    rejected = run(main, "-I", str(override), success=False)
    assert "Verification Error:" in rejected, rejected
    assert "Internal Error:" not in rejected and "timed out" not in rejected, rejected
    (root / "dune-workspace").write_text("(lang dune 3.12)\n")
    nested = root / "nested"
    for name, contents in files.items():
        target = nested / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(contents.replace("discovery_fixture", "nested_fixture"))
    nested_main = nested / "app/main.ml"
    assert "Verification successful." in run(nested_main)
    report = json.loads(run(nested_main, "--lsp-mode", "--lsp-annotations", "--lsp-annotations-only"))
    dependencies = {Path(file).resolve() for file in report["dependencies"]}
    assert root / "dune-workspace" in dependencies, dependencies
    assert nested / "dune-project" in dependencies, dependencies
    assert nested / "values/values.mli" in dependencies, dependencies
    assert root / "values/values.mli" not in dependencies, dependencies
    (root / "values/values.mli").unlink()
    (root / "values/values.api").write_text(files["values/values.mli"])
    (root / "values/dune").write_text(files["values/dune"] + """(rule
 (target values.mli)
 (action (copy values.api %{target})))
""")
    generated = root / "_build/default/values/values.mli"
    generated.parent.mkdir(parents=True, exist_ok=True)
    generated.write_text(files["values/values.mli"])
    assert "Verification successful." in run(main)
    report = json.loads(run(main, "--lsp-mode", "--lsp-annotations", "--lsp-annotations-only"))
    dependencies = {Path(file).resolve() for file in report["dependencies"]}
    assert generated in dependencies, dependencies
    assert root / "values/dune" in dependencies, dependencies
    dune = shutil.which("dune")
    assert dune
    ready = root / "_build/discovery_lock_ready"
    release = root / "_build/discovery_lock_release"
    hold_lock = """from pathlib import Path
import sys
import time

ready, release = map(Path, sys.argv[1:])
ready.touch()
deadline = time.monotonic() + 90
while not release.exists():
    if time.monotonic() >= deadline:
        raise SystemExit("Build lock fixture was not released")
    time.sleep(0.02)
"""
    command = " ".join(
        json.dumps(arg, ensure_ascii=False)
        for arg in [sys.executable, "-c", hold_lock, str(ready), str(release)]
    )
    (root / "dune").write_text(f"(rule\n (alias hold_lock)\n (action (run {command})))\n")
    watcher = subprocess.Popen(
        [dune, "build", "-j1", "@hold_lock"],
        cwd=root, env=environment, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
    )
    try:
        deadline = time.monotonic() + 10
        while not ready.exists():
            assert watcher.poll() is None, watcher.stderr.read().decode()
            assert time.monotonic() < deadline, "Dune build did not start its lock-holding action"
            time.sleep(0.02)
        assert "Verification successful." in run(main)
        report = json.loads(run(main, "--lsp-mode", "--lsp-annotations", "--lsp-annotations-only"))
        assert not report["errors"], report["errors"]
        assert watcher.poll() is None, "Dune build released its lock during discovery"
    finally:
        release.touch()
        try:
            watcher.wait(timeout=5)
        except subprocess.TimeoutExpired:
            watcher.terminate()
            try:
                watcher.wait(timeout=5)
            except subprocess.TimeoutExpired:
                watcher.kill()
                watcher.wait(timeout=5)
        watcher.stderr.close()
    assert watcher.returncode == 0, "Dune lock-holding build failed"

print("Dune discovery verifies transitive source contracts without an explicit include path.")
print("Editor dependencies include project configuration; unrelated libraries stay excluded.")
print("Standalone mode and explicit interface overrides remain available.")
print("Nested projects use their enclosing workspace without confusing same-named libraries.")
print("Generated interfaces remain available while Dune holds the project build lock.")
