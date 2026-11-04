import json
import pathlib
import sys

mode, path = sys.argv[1:]
report = json.loads(pathlib.Path(path).read_text())
if mode == "plain":
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
    source = pathlib.Path(primary["file"]).read_text()
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
