import json
import pathlib
import sys

mode, path = sys.argv[1:]
report = json.loads(pathlib.Path(path).read_text(encoding="utf-8"))
if mode == "manifest":
    assert set(report) == {"version", "lsp_protocol", "min_z3", "ocaml_version", "raven_api_version"}
    assert report["version"] == "0.1.0"
    assert report["lsp_protocol"] == 1
    assert report["min_z3"] == "4.13.0"
    assert report["ocaml_version"].startswith("5.5.")
    assert isinstance(report["raven_api_version"], int)
elif mode == "plain":
    assert report == []
elif mode == "enriched":
    assert set(report) == {
        "errors", "dependencies", "annotations", "members", "references", "symbols"
    }
    assert report["errors"] == []
    assert {"editor_ok.ml", "editor_ok.mli", "editor_ok.proof"} <= set(report["dependencies"])
elif mode == "failure":
    errors = report["errors"]
    assert any(error["kind"] == "Verification" for error in errors)
    primary = next(error for error in errors if error["kind"] == "Verification")
    source = pathlib.Path(primary["file"]).read_text(encoding="utf-8")
    prefix = source.encode("utf-8")[:primary["start_col"]].decode("utf-8")
    assert "😀" in prefix
    assert primary["start_col"] > len(prefix.encode("utf-16-le")) // 2
    assert primary["start_line"] == primary["end_line"] == 1
    assert isinstance(primary["message"], list)
elif mode == "type":
    assert any(error["kind"] == "Type" for error in report)
elif mode == "warning":
    assert len(report) == 1
    assert report[0]["kind"] == "Warning"
    assert "trusted" in "\n".join(report[0]["message"])
elif mode == "multiple":
    assert any(error["kind"] == "Type" for error in report)
    assert any(error["kind"] == "Verification" for error in report)
else:
    raise AssertionError(mode)
