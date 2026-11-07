import json
import pathlib
import sys


def offset(location, boundary):
    lines = pathlib.Path(location["file"]).read_bytes().splitlines(keepends=True)
    return (sum(map(len, lines[:location[boundary + "_line"] - 1]))
            + location[boundary + "_col"])


def source_slice(location):
    return pathlib.Path(location["file"]).read_bytes()[
        offset(location, "start"):offset(location, "end")
    ].decode("utf-8")


mode, path = sys.argv[1:]
report = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
steps = [a for a in report["annotations"] if a["kind"] == "ProofStep"]
contracts = [a for a in report["annotations"] if a["kind"] == "InheritedContract"]
assert len(steps) + len(contracts) == len(report["annotations"])
for step in steps:
    assert set(step) == {
        "file", "start_line", "start_col", "end_line", "end_col",
        "kind", "source_loc", "text",
    }
    assert set(step["source_loc"]) == {
        "file", "start_line", "start_col", "end_line", "end_col",
    }
    assert source_slice(step) == ""
    assert step["file"].endswith(".ml")
    assert step["source_loc"]["file"].endswith(".proof")
    original = source_slice(step["source_loc"])
    prefix = "Ghost.scope " if original.startswith("(fun") else (
        "" if original == "commit" else "proof "
    )
    assert step["text"] == prefix + original
    assert step["text"] != "manual"

if mode == "steps":
    assert report["errors"] == []
    assert len(contracts) == 3
    assert len(steps) == 4
    assert [s["start_line"] for s in steps] == [3, 4, 7, 8]
    assert [s["source_loc"]["start_line"] for s in steps] == [3, 4, 8, 13]
    assert [s["source_loc"]["start_col"] for s in steps] == [23, 30, 40, 28]
    for step, anchor in zip(steps, ["Atomic.make v", "Atomic.get c",
                                    "Atomic.get c", "Atomic.get c"]):
        line = pathlib.Path(step["file"]).read_bytes().splitlines()[step["start_line"] - 1]
        assert step["start_col"] == line.index(anchor.encode()) + len(anchor)
    assert "🙂" in steps[-1]["text"]
    assert steps[-1]["start_col"] > len("  let b = (* 🙂 *) Atomic.get c".encode("utf-16-le")) // 2
    assert all("let first = at" not in s["text"] for s in steps)
elif mode == "failure":
    assert any(e["kind"] == "Verification" for e in report["errors"])
    assert len(contracts) == 1
    assert len(steps) == 1
    assert steps[0]["text"] == "proof assert true"
else:
    raise AssertionError(mode)
