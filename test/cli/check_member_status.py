import json
import pathlib
import shutil
import subprocess


executable = shutil.which("caravan")
assert executable is not None
cwd = str(pathlib.Path.cwd())
args = ["--lsp-mode", "--lsp-annotations", "editor_member_status.ml"]
requests = [
    "{invalid json",
    json.dumps({"id": "missing", "args": args}),
    json.dumps({"id": "cwd", "cwd": cwd + "/missing-directory", "args": args}),
    json.dumps({"id": "args", "cwd": cwd, "args": [17]}),
    json.dumps({"id": "flags", "cwd": cwd, "args": []}),
    json.dumps({"id": "quiet", "cwd": cwd, "args": ["--quiet"] + args, "partial": True}),
    json.dumps({"id": "next", "cwd": cwd, "args": args, "partial": True}),
]
process = subprocess.run(
    [executable, "--server"],
    input="\n".join(requests) + "\n",
    text=True,
    capture_output=True,
    timeout=120,
)
assert process.returncode == 0, process.stderr
frames = [json.loads(line) for line in process.stdout.splitlines()]
assert len([frame for frame in frames if frame.get("id") is None and "error" in frame]) == 3
for request_id in ("cwd", "flags"):
    assert any(frame.get("id") == request_id and "error" in frame for frame in frames)


def members(report):
    result = report["members"]
    assert len({member["id"] for member in result}) == len(result)
    assert all(member["file"].endswith("editor_member_status.ml") for member in result)
    return {member["name"]: member for member in result}


reports = []
for request_id in ("quiet", "next"):
    own = [frame for frame in frames if frame.get("id") == request_id]
    partials = [frame for frame in own if "partial" in frame]
    phases = [frame["phase"] for frame in partials]
    assert phases[0] == "typed", phases
    assert "scheduled" in phases and "progress" in phases, phases
    order = {"typed": 0, "scheduled": 1, "progress": 2, "final": 3}
    assert [order[phase] for phase in phases] == sorted(order[phase] for phase in phases)
    snapshots = [json.loads(frame["partial"]) for frame in partials]
    inventories = [members(report) for report in snapshots]
    final_frame = own[-1]
    assert "partial" not in final_frame and final_frame["exit"] == 1, final_frame
    assert final_frame["stderr"] == "", final_frame
    final = json.loads(final_frame["stdout"])
    final_members = members(final)
    reports.append(final)
    assert set(final_members) == {
        "editor_member_status.ml", "Work", "Work.succeeds", "Work.fails",
        "Make", "Make.identity", "Made",
    }, set(final_members)
    source_ids = {name: member["id"] for name, member in final_members.items()}
    assert all({name: member["id"] for name, member in inventory.items()} == source_ids
               for inventory in inventories)
    scheduled = inventories[phases.index("scheduled")]
    assert scheduled["Work.succeeds"]["status"] == "pending", scheduled
    assert scheduled["Work.fails"]["status"] == "pending", scheduled
    assert any(inventory["Work.fails"]["status"] == "failed" for inventory in inventories)
    assert any(inventory["Work.succeeds"]["status"] == "verified" for inventory in inventories)
    assert final_members["Work.fails"]["status"] == "failed", final_members
    assert final_members["Work"]["status"] == "failed", final_members
    assert final_members["Work"]["counts"].get("failed", 0) == 1
    assert sum(final_members["Work"]["counts"].values()) == 2
    assert final_members["Make"]["kind"] == "functor"
    assert final_members["Work.succeeds"]["start_line"] == 2
    assert final_members["Work.fails"]["start_line"] == 3
    assert any(error["kind"] == "Verification" for error in final["errors"])

assert reports[0] == reports[1], "A quiet request changed the next request's report"
ordinary = subprocess.run([executable] + args, text=True, capture_output=True, timeout=120)
assert ordinary.returncode == 1, ordinary.stderr
assert json.loads(ordinary.stdout) == reports[-1]
quiet = subprocess.run([executable, "--quiet"] + args, text=True, capture_output=True, timeout=120)
assert quiet.returncode == 1, quiet.stderr
assert json.loads(quiet.stdout) == reports[-1]
prefixed = subprocess.run(
    [executable, "--quiet", "--server"],
    input=json.dumps({"id": "prefix", "cwd": cwd, "args": args}) + "\n",
    text=True, capture_output=True, timeout=120,
)
assert prefixed.returncode == 0, prefixed.stderr
assert json.loads(json.loads(prefixed.stdout)["stdout"]) == reports[-1]
