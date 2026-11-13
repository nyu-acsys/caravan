import json
import shutil
import subprocess
import tempfile

executable = shutil.which("caravan")
assert executable is not None


def run(*args, exit=0, file="members.ml"):
    process = subprocess.run(
        [executable, "--lsp-mode", "--lsp-annotations", *args, file],
        text=True, capture_output=True, timeout=120,
    )
    assert process.returncode == exit, (args, process.stdout, process.stderr)
    assert process.stderr == "", process.stderr
    return json.loads(process.stdout)


def members(report):
    return {member["name"]: member for member in report["members"]}


def errors(report):
    return [entry for entry in report["errors"] if entry["kind"] != "RelatedLoc"]


def failed_selection(name):
    report = run("--only", name, exit=1)
    assert any(error["kind"] == "Verification" for error in errors(report)), report
    assert members(report)[name]["status"] == "failed", report
    assert members(report)["good"]["status"] == "skipped", report
    return report


report = run("--only", "good")
assert not errors(report), report
inventory = members(report)
assert inventory["good"]["status"] == "verified", inventory
for name in ("bad", "Work.good", "Work.bad", "outer", "outer.helper", "loop", "proved"):
    assert inventory[name]["status"] == "skipped", (name, inventory[name])
assert "other.helper" in inventory, inventory

failed_selection("bad")
failed_selection("outer")
failed_selection("outer.helper")
failed_selection("loop")
proof = failed_selection("proved")
assert any(error["file"].endswith("members.proof") for error in errors(proof)), proof

module = run("--only", "Work", exit=1)
inventory = members(module)
assert inventory["Work.good"]["status"] == "verified", inventory
assert inventory["Work.bad"]["status"] == "failed", inventory
assert inventory["bad"]["status"] == "skipped", inventory

for name, text, file in (
    ("missing", "There is no member or module named missing", "members.ml"),
    ("duplicate", "ambiguous", "ambiguous.ml"),
):
    report = run("--only", name, exit=1, file=file)
    assert any(text in str(error["message"]) for error in errors(report)), report

frontend = run("--only", "good", exit=1, file="frontend.ml")
assert any(error["kind"] == "Type" for error in errors(frontend)), frontend

with tempfile.TemporaryDirectory(dir=".") as cache:
    fresh = run("--only", "good", "--cache-dir", cache)
    assert not members(fresh)["good"]["cached"], fresh
    cached = run("--only", "good", "--cache-dir", cache)
    assert members(cached)["good"]["cached"], cached
    assert members(cached)["bad"]["status"] == "skipped", cached
    assert not members(cached)["bad"]["cached"], cached
    full = run("--cache-dir", cache, exit=1)
    assert members(full)["good"]["cached"], full
    assert members(full)["bad"]["status"] == "failed", full

# Contract obligations can originate in the interface rather than the code.
for file, good, bad in (("pure.ml", "good", "bad"),
                        ("lemmas.ml", "good", "bad"),
                        ("generic.ml", "Make.good", "Make.bad"),
                        ("directives.ml", "Scope.good", "Scope.bad")):
    successful = run("--only", good, file=file)
    assert members(successful)[good]["status"] == "verified", successful
    assert members(successful)[bad]["status"] == "skipped", successful
    rejected = run("--only", bad, file=file, exit=1)
    assert any(error["kind"] == "Verification" for error in errors(rejected)), rejected
    assert members(rejected)[bad]["status"] == "failed", rejected

for incompatible in ("--emit-rav", "--check-stdlib", "--lsp-annotations-only"):
    process = subprocess.run(
        [executable, "--only", "good", incompatible, "members.ml"],
        text=True, capture_output=True, timeout=120,
    )
    assert process.returncode == 1, process
    assert "--only cannot be combined" in process.stderr, process

process = subprocess.run(
    [executable, "--only", "good"], text=True, capture_output=True, timeout=120,
)
assert process.returncode == 1 and "requires a source file" in process.stderr, process

directive_group = run("--only", "Scope", file="directives.ml", exit=1)
assert members(directive_group)["Scope.bad"]["status"] == "failed", directive_group

nested_directive = run("--only", "outer", file="directives.ml", exit=1)
assert members(nested_directive)["outer.helper"]["status"] == "failed", nested_directive

# A lowered loop after a line directive belongs to its lexical function.
run("--only", "good", file="directive_loop.ml")
loop = run("--only", "loop", file="directive_loop.ml", exit=1)
assert members(loop)["loop"]["status"] == "failed", loop

# The code and proof representations of a module are one source selection.
paired = run("--only", "Scope", file="paired.ml", exit=1)
assert members(paired)["Scope.bad"]["status"] == "failed", paired

# A resource's signature declaration and proof definition are selected together.
resource = run("--only", "Checked.owned", file="resources.ml")
owned = [m for m in resource["members"] if m["name"] == "Checked.owned"]
assert len(owned) == 2 and all(m["status"] != "skipped" for m in owned), resource
assert members(resource)["Checked.bad"]["status"] == "skipped", resource
run("--only", "Checked", file="resources.ml", exit=1)

resource = run("--only", "Checked.owned", file="interface_resources.ml")
owned = [m for m in resource["members"] if m["name"] == "Checked.owned"]
assert len(owned) == 2 and all(m["status"] != "skipped" for m in owned), resource
assert members(resource)["Checked.bad"]["status"] == "skipped", resource
run("--only", "Checked", file="interface_resources.ml", exit=1)
