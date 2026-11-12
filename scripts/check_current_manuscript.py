"""Validate the current TeX/PDF pair and its recorded build, not its mathematical completeness."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re

ROOT = Path(__file__).resolve().parents[1]
PROFILE = "docs/current-manuscript.json"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def safe_path(root, name):
    """Accept portable repository-relative file paths, including resolved containment."""
    require(isinstance(name, str) and name and not any(ord(c) < 32 for c in name), "Invalid file path")
    parts = name.split("/")
    require(not PurePosixPath(name).is_absolute() and not any(c in name for c in '\\:<>"|?*')
            and all(p not in ("", ".", "..") and p == p.rstrip(" .") for p in parts),
            "Unsafe file path: " + name)
    reserved = {"con", "prn", "aux", "nul"} | {f"{p}{n}" for p in ("com", "lpt") for n in range(1, 10)}
    require(all(p.split(".")[0].lower() not in reserved for p in parts), "Reserved file path: " + name)
    path = root / name
    require(path.resolve().is_relative_to(root.resolve()), "File path escapes repository: " + name)
    require(path.is_file(), "Missing required file: " + name)
    return path


def read_pin(root, pin):
    require(type(pin) is dict and set(pin) == {"path", "sha256"}, "Expected exact path/SHA-256 pin")
    require(isinstance(pin["sha256"], str) and re.fullmatch(r"[0-9a-f]{64}", pin["sha256"]),
            "Invalid SHA-256 pin")
    raw = safe_path(root, pin["path"]).read_bytes()
    require(sha(raw) == pin["sha256"], "SHA-256 mismatch: " + pin["path"])
    return raw


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "Duplicate JSON key: " + key)
        result[key] = value
    return result


def load_json(raw):
    return json.loads(raw, object_pairs_hook=unique_object)


def validate(root=ROOT):
    root = Path(root).resolve()
    profile_raw = safe_path(root, PROFILE).read_bytes()
    profile = load_json(profile_raw)
    require(type(profile) is dict and set(profile) == {
        "schema", "version", "tex", "pdf", "build_record", "required_tex_inputs"}, "Invalid current manuscript profile")
    require(profile["schema"] == "current-manuscript/v1", "Unknown current manuscript schema")
    require(type(profile["version"]) is int and profile["version"] > 0, "Invalid manuscript version")
    require(type(profile["required_tex_inputs"]) is list, "Required TeX inputs must be a list")
    pins = [profile[k] for k in ("tex", "pdf", "build_record")] + profile["required_tex_inputs"]
    contents = {}
    for pin in pins:
        raw = read_pin(root, pin)
        name = pin["path"]
        require(name.casefold() not in {p.casefold() for p in contents}, "Duplicate artifact/input path: " + name)
        require(name.casefold() != PROFILE.casefold(), "Profile cannot pin itself")
        contents[name] = raw
    tex, pdf = profile["tex"], profile["pdf"]
    require(PurePosixPath(tex["path"]).suffix == ".tex", "Current source must be TeX")
    require(PurePosixPath(pdf["path"]).suffix == ".pdf", "Current output must be PDF")
    source = contents[tex["path"]].decode("utf-8")
    # This checks the project's explicit version subtitle; it is not a TeX interpreter.
    uncommented = re.sub(r"(?<!\\)%[^\n]*", "", source)
    require(r"\documentclass" in uncommented and r"\begin{document}" in uncommented
            and r"\end{document}" in uncommented, "Expected a full document source")
    preamble = uncommented.split(r"\begin{document}", 1)[0]
    editions = re.findall(r"\\large\s+Version\s+([1-9][0-9]*)\s*}", preamble)
    require(editions == [str(profile["version"])], "Manuscript edition does not match profile")
    require(contents[pdf["path"]].startswith(b"%PDF-"), "Current output is not a PDF")
    build = load_json(contents[profile["build_record"]["path"]])
    require(type(build) is dict, "Invalid build record")
    require(build.get("source") == tex["path"] and build.get("source_sha256") == tex["sha256"]
            and build.get("pdf") == pdf["path"] and build.get("pdf_sha256") == pdf["sha256"],
            "Stale build-record source/PDF mapping")
    require("manuscript_version" not in build or build["manuscript_version"] == profile["version"],
            "Build-record edition does not match profile")
    require(build.get("tex_errors") == 0 and build.get("unresolved_references") == 0,
            "Build record reports missing or unsuccessful diagnostics")
    require(isinstance(build.get("engine"), str) and build["engine"]
            and isinstance(build.get("bundle"), str) and build["bundle"], "Missing recorded build inputs")
    return profile, contents, {
        "profile_sha256": sha(profile_raw), "version": profile["version"],
        "tex": tex, "pdf": pdf, "build_record": profile["build_record"],
        "required_tex_inputs": profile["required_tex_inputs"],
        "scope": "File hashes, declared edition and recorded build mapping only. Mathematical completeness, "
                 "the recorded build's provenance and semantic PDF identity require independent review.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=ROOT)
    args = parser.parse_args()
    _, _, report = validate(args.repo)
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
