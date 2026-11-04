import pathlib
import re
import sys


text = pathlib.Path(sys.argv[1]).read_text(encoding="utf-8")
assert len(re.findall(r"module Generic\[A0: Ocaml_Value_1\]", text)) == 1
assert len(re.findall(r"module Poly_nested_1\[A0: Ocaml_Value_1\]", text)) == 1
dictionaries = re.findall(
    r"module\s+(\w+)\s*:\s*Ocaml_ListValue_1\s*=\s*Ocaml_ListValue_1\[Generic\.A0\]", text
)
assert len(dictionaries) == 1
instances = re.findall(r"module\s+(\w+)\s*:\s*Generic\s*=\s*Generic\[([^\]]+)\]", text)
assert len(instances) == 3
assert len({name for name, _ in instances}) == 3
assert {argument.strip() for _, argument in instances} == {
    "Poly_nested_1.A0", "Poly_nested_1." + dictionaries[0], "Ocaml_IntValue_1"
}
assert "Generic.wrap(value)" in text
