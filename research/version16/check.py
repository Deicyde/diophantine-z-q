"""Check Version 16's exact correction delta and artifact bindings.

This validates recorded relationships. It does not prove the mathematics or
replace the protected protocol check required for a public merge.
"""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def load(name):
    return json.loads((HERE / name).read_bytes())


def checked(path, expected):
    target = (ROOT / path).resolve()
    if not target.is_relative_to(ROOT):
        raise ValueError("Path outside repository")
    raw = target.read_bytes()
    if digest(raw) != expected:
        raise ValueError("SHA-256 mismatch: " + path)
    return raw


def main():
    edits = load("EDITS.json")
    before = checked(edits["baseline"], edits["baseline_sha256"])
    amendment = load("EDITORIAL-AMENDMENT.json")
    precision = load("TZ-PRECISION-AMENDMENT.json")
    after = checked(edits["manuscript"], precision["expected_amended_sha256"])
    reconstructed = before.decode("utf-8")
    expected_ids = {
        "version", "date", "horizontal-normalization",
        "finite-cover-fixed-lifts", "gr-lower-bound", "gr-isogeny-height",
        "gr-periods-bibliography", "tao-ziegler-proof-adaptation",
    }
    assert len(edits["edits"]) == len(expected_ids)
    assert {e["id"] for e in edits["edits"]} == expected_ids
    for edit in edits["edits"]:
        assert reconstructed.count(edit["old"]) == 1, edit["id"]
        reconstructed = reconstructed.replace(edit["old"], edit["new"], 1)
    reviewed = reconstructed.encode("utf-8")
    assert digest(reviewed) == edits["sha256"] == amendment["reviewed_manuscript_sha256"]
    assert amendment["manuscript"] == edits["manuscript"]
    assert len(amendment["edits"]) == 1
    for edit in amendment["edits"]:
        assert edit["id"] == "restore-original-ai-statement"
        assert reconstructed.count(edit["old"]) == 1
        reconstructed = reconstructed.replace(edit["old"], edit["new"], 1)
    pre_precision = reconstructed.encode("utf-8")
    assert digest(pre_precision) == amendment["manuscript_sha256"] == precision["source_sha256"]
    assert checked("research/version16/snapshots/pre-precision/quartic_v16.tex",
                   precision["source_sha256"]) == pre_precision
    assert precision["source_path"] == edits["manuscript"]
    assert reconstructed.count(precision["before"]) == precision["occurrences"] == 1
    reconstructed = reconstructed.replace(precision["before"], precision["after"], 1)
    assert reconstructed.encode("utf-8") == after
    assert pre_precision.count(b"\n") == after.count(b"\n")
    original = checked(amendment["original_statement_source"],
                       amendment["original_statement_source_sha256"]).decode("utf-8")
    def ai_statement(text):
        return text.split(r"\section*{AI usage statement}")[1].split(r"\end{document}")[0].replace("\r\n", "\n")
    expected = ai_statement(original).replace("with auditing from Fable 5.1.",
                                               "with auditing from Fable 5.1 and 5.2.")
    assert ai_statement(reconstructed) == expected
    b, a = before.decode("utf-8"), after.decode("utf-8")
    abstract = r"\\begin\{abstract\}.*?\\end\{abstract\}"
    assert re.findall(abstract, b, re.S) == re.findall(abstract, a, re.S)
    statements = r"\\begin\{(theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}"
    assert [m.group() for m in re.finditer(statements, b, re.S)] == [
        m.group() for m in re.finditer(statements, a, re.S)
    ]
    assert "Busy Beaver" not in a and "v15BB" not in a
    assert a.count(r"\bibitem{gr-periods2014}") == 1
    assert a.count(r"\bibitem{gr2014}") == 1
    assert a.count("{gr-periods2014}") == 3
    apps = load("APPLICATIONS.json")
    assert apps["manuscript_sha256"] == digest(reviewed)
    assert len(apps["applications"]) == 3
    for app in apps["applications"]:
        for field in ("source", "required", "constructed", "domain_coverage",
                      "maps", "conventions", "exceptions", "uniformity",
                      "consumer", "change"):
            assert app.get(field), (app["id"], field)
        assert all(n > 0 for n in app["lines"])
    build = load("BUILD.json")
    assert build["source_sha256"] == digest(after)
    assert checked(build["pdf"], build["pdf_sha256"]).startswith(b"%PDF-")
    assert build["tex_errors"] == build["unresolved_references"] == 0
    review = load("review/REVIEW.json")
    assert review["decision"] == "accepted_scoped_corrections"
    assert review["manuscript"] == edits["manuscript"]
    assert review["manuscript_sha256"] == digest(reviewed)
    assert review["baseline_sha256"] == digest(before)
    assert review["author_of_manuscript"] is False
    assert review["author_of_edits"] is False
    assert review["reviewer_identity"] != "/root"
    assert review["controller_acceptance_claimed"] is False
    assert review["substantive_limits"]
    assert {x["id"] for x in review["per_edit"]} == expected_ids
    assert all(x["disposition"].startswith("accepted") for x in review["per_edit"])
    checked(review["report"], review["report_sha256"])
    checked(review["application_record"], review["application_record_sha256"])
    checked(review["edits_record"], review["edits_record_sha256"])
    # These are record-consistency checks. They do not authenticate the reviewer
    # or establish the provider model; the protected controller does that.
    manifest = load("MANIFEST.json")
    for item in manifest["files"]:
        raw = checked(item["path"], item["sha256"])
        assert len(raw) == item["bytes"]
    assert manifest["manuscript_sha256"] == digest(after)
    assert any(x["path"].endswith("review/REVIEW.json") for x in manifest["files"])
    print(json.dumps({"status": "PASS", "version": 16,
                      "manuscript_sha256": digest(after),
                      "exact_edits": len(edits["edits"]),
                      "editorial_amendments": len(amendment["edits"]),
                      "precision_amendments": 1,
                      "abstract_and_theorem_statements_unchanged": True,
                      "files_verified": len(manifest["files"]),
                      "scope": "Finite artifact binding; not mathematical or App acceptance"},
                     indent=2))


if __name__ == "__main__":
    main()
