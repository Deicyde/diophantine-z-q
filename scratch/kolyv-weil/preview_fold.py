#!/usr/bin/env python3
"""Preview only the import, binders and pole call changed by this binder fold."""

import difflib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = json.loads((HERE / "autofold.json").read_text())
MAIN = "ZInQKernel/OneProof/Main.lean"
SOURCE = (HERE.parents[1] / MAIN).read_text()


def replace_once(source, old, new):
    if source.count(old) != 1:
        raise SystemExit(f"Expected exactly one occurrence of {old!r}; check the integration base.")
    return source.replace(old, new, 1)


def preview():
    old_import = "import ZInQKernel.Contrib.OneProof.PoleCompletenessFromRCGenuineFinal\n"
    new_import = f"import {SPEC['imports'][0]}\n"
    old_binders = ("(hB : ZInQ.Manuscript.PoleS12.BCDTThmA)\n"
                   "    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1)")
    new_binders = "\n    ".join(
        f"({leaf['name']} : {leaf['type'].removeprefix('_root_.')})"
        for leaf in SPEC["discharges"][0]["leaves"]
    )
    bypass = SPEC["headline_bypass"]
    result = replace_once(SOURCE, old_import, new_import)
    result = replace_once(result, old_binders, new_binders)
    return replace_once(result, bypass["old_call"], bypass["new_call"])


if __name__ == "__main__":
    print("".join(difflib.unified_diff(SOURCE.splitlines(keepends=True),
                                       preview().splitlines(keepends=True),
                                       f"a/{MAIN}", f"b/{MAIN}")), end="")
