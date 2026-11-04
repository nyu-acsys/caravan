import json
import os
import pathlib
import shutil
import subprocess
import sys


def source_slice(location):
    lines = pathlib.Path(location["file"]).read_bytes().splitlines(keepends=True)
    start = sum(map(len, lines[:location["start_line"] - 1])) + location["start_col"]
    end = sum(map(len, lines[:location["end_line"] - 1])) + location["end_col"]
    return b"".join(lines)[start:end].decode("utf-8")


mode, path = sys.argv[1:]
report = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
if mode == "no-solver":
    if os.name != "nt":
        binary = shutil.which("caravan")
        assert binary
        completed = subprocess.run([
            binary, "--lsp-mode", "--lsp-annotations", "--lsp-annotations-only",
            "editor_contracts.ml",
        ], env={**os.environ, "PATH": "/nonexistent"}, check=True, capture_output=True)
        assert json.loads(completed.stdout) == report
    sys.exit(0)

assert "verified" not in report
annotations = report["annotations"]
if mode in {"alias", "value", "mismatch", "type"}:
    assert annotations == []
    assert report["errors"]
    if mode == "alias":
        assert any("function value aliases" in "\n".join(e["message"])
                   for e in report["errors"])
    if mode == "mismatch":
        assert any("another one here" in "\n".join(e["message"])
                   for e in report["errors"])
        assert any(e["kind"] == "RelatedLoc" and e["file"].endswith(".mli")
                   for e in report["errors"])
else:
    contracts = [a for a in annotations if a["kind"] == "InheritedContract"]
    steps = [a for a in annotations if a["kind"] == "ProofStep"]
    assert len(contracts) + len(steps) == len(annotations)
    if mode != "proof":
        assert steps == []
    annotations = contracts
    for annotation in contracts:
        assert annotation["kind"] == "InheritedContract"
        assert annotation["file"].endswith(".ml")
        assert source_slice(annotation) == annotation["source"].split(".")[-1]
        assert annotation["source_loc"]["file"].endswith((".mli", ".proof"))
        for clause in annotation["clauses"]:
            actual = source_slice(clause)
            words = clause["keyword"].split()
            for word in words:
                assert actual.startswith(word)
                actual = actual[len(word):].lstrip()
            assert actual == clause["text"]
    if mode == "contracts":
        assert report["errors"] == []
        by_name = {a["source"]: a for a in annotations}
        assert set(by_name) == {
            "increase", "Box.increase", "atomic_identity",
            "pure_identity", "exceptional",
        }
        assert len(annotations) == len(by_name)
        assert [c["keyword"] for c in by_name["increase"]["clauses"]] == [
            "requires", "ensures", "variant",
        ]
        assert "specified" in by_name["increase"]["clauses"][1]["text"]
        assert "actual" not in by_name["increase"]["clauses"][1]["text"]
        requires = by_name["increase"]["clauses"][0]
        assert "🙂" in requires["text"]
        assert requires["end_col"] > len(source_slice(requires).encode("utf-16-le")) // 2
        assert [c["keyword"] for c in by_name["atomic_identity"]["clauses"]] == [
            "atomic", "atomic requires", "atomic ensures", "atomic raises",
        ]
        assert [c["keyword"] for c in by_name["pure_identity"]["clauses"]] == [
            "pure", "ensures",
        ]
        assert [c["keyword"] for c in by_name["exceptional"]["clauses"]] == [
            "raises", "raises", "ensures",
        ]
    elif mode == "functor":
        assert report["errors"] == []
        assert len(annotations) == 1
        annotation = annotations[0]
        assert annotation["source_loc"]["file"] == "./editor_contract_api.mli"
        assert annotation["clauses"][0]["text"] == "result = specified + 1"
    elif mode == "proof":
        assert report["errors"] == []
        assert len(annotations) == 1
        annotation = annotations[0]
        assert annotation["source_loc"]["start_line"] == 1
        assert annotation["source_loc"]["start_col"] == len("proof ")
        assert source_slice(annotation["source_loc"]) == (
            "result = increase specified\n"
            "  requires (specified >= 0)\n"
            "  ensures (result = specified + 1)"
        )
        assert [c["text"] for c in annotation["clauses"]] == [
            "(specified >= 0)", "(result = specified + 1)",
        ]
        assert len(steps) == 1
        step = steps[0]
        assert source_slice(step) == ""
        assert source_slice(step["source_loc"]) == "assert (result = specified + 1)"
        assert step["text"] == "proof " + source_slice(step["source_loc"])
    elif mode == "failure":
        assert any(e["kind"] == "Verification" for e in report["errors"])
        assert len(annotations) == 1
        assert annotations[0]["clauses"][0]["text"] == "result = specified + 2"
    elif mode == "inline":
        assert report["errors"] == []
        assert annotations == []
    else:
        raise AssertionError(mode)
