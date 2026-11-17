"""Live, test-only exercise of admission's intent and App reservation writes.

Uses the actual embedded outside_reserve implementation. It deliberately does
not run triage, reviewers, eligibility classification or merge. The separate
marker and neutral check name cannot count as live admission or acceptance.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import types

REPO = "elliotglazer/diophantine-z-q"
TEST_PR = 69
TEST_MARKER = "<!-- protocol-b-admission-permission-test-v1 -->"
TEST_CHECK = "Protocol B / test admission reservation"


def require(value, message):
    if not value:
        raise ValueError(message)


def load_program(path):
    raw = path.read_bytes()
    workflow = raw.decode("utf-8").replace("\r\n", "\n")
    block = workflow.split("<<'PROTOCOL_B_PYTHON'\n", 1)[1].split("          PROTOCOL_B_PYTHON\n", 1)[0]
    source = "\n".join(line[10:] if line.startswith("          ") else line for line in block.splitlines()) + "\n"
    module = types.ModuleType("protocol_b_admission_test_source")
    exec(compile(source, str(path), "exec"), module.__dict__)
    return module, hashlib.sha256(raw).hexdigest()


def exercise(gate, gh, app, env, save):
    require(env.get("MODE") == "test", "This exercise requires test mode")
    require(env.get("GITHUB_REPOSITORY") == REPO and env.get("GITHUB_REF") == "refs/heads/main"
            and env.get("GITHUB_EVENT_NAME") == "workflow_dispatch", "Only a manual run on this repository's main is allowed")
    require(re.fullmatch(r"[0-9a-f]{40}", env.get("GITHUB_SHA", "")), "Missing source commit")
    app_id = int(env["APP_ID"])
    require(app_id > 0 and app_id != 15368, "Dedicated App required")
    pr = gh.call(f"/pulls/{TEST_PR}")
    require(pr.get("number") == TEST_PR and pr.get("state") == "closed" and pr.get("merged") is False,
            "The fixed throwaway PR must remain closed and unmerged")
    require((pr.get("base", {}).get("repo") or {}).get("full_name") == REPO, "Wrong test repository")
    require(not TEST_MARKER.startswith(gate.OUTSIDE_MARKER) and TEST_CHECK != gate.OUTSIDE_CHECK,
            "Test records must be separate from live admission")
    events = []
    def once(client, path, method, data):
        event = {"method": method, "path": path, "request": data, "state": "intent"}
        events.append(event)
        save("write-events.json", events)
        # The production helper makes one request, with no HTTP retries.
        try:
            result = gate.outside_api_once(client, path, method, data)
        except Exception as error:
            event.update(state="unconfirmed", error_type=type(error).__name__)
            save("write-events.json", events)
            raise
        event.update(state="response_received", response=result)
        save("write-events.json", events)
        return result
    original = gate.OUTSIDE_MARKER, gate.OUTSIDE_CHECK
    gate.OUTSIDE_MARKER, gate.OUTSIDE_CHECK = TEST_MARKER, TEST_CHECK
    try:
        slot = gate.outside_reserve(gh, app, pr, env["GITHUB_SHA"], env["GITHUB_RUN_ID"],
                                   env["GITHUB_RUN_ATTEMPT"], app_id, once)
        expected_body = gate.outside_intent_body(slot["value"]["intent"])
    finally:
        gate.OUTSIDE_MARKER, gate.OUTSIDE_CHECK = original
    comment = gh.call("/issues/comments/"+str(slot["value"]["pointer_comment"]))
    check = app.call("/check-runs/"+str(slot["check"]))
    require(comment.get("body") == expected_body and comment.get("issue_url") ==
            f"https://api.github.com/repos/{REPO}/issues/{TEST_PR}", "Intent comment readback mismatch")
    require((comment.get("user") or {}).get("login") == "github-actions[bot]", "Unexpected comment actor")
    require(check.get("name") == TEST_CHECK and check.get("head_sha") == pr["head"]["sha"]
            and (check.get("app") or {}).get("id") == app_id and check.get("conclusion") == "neutral"
            and json.loads(check["output"]["text"]) == slot["value"], "App reservation readback mismatch")
    result = {"test": "live admission reservation", "mode": "test", "source_sha": env["GITHUB_SHA"],
              "pr": TEST_PR, "comment": comment, "check": check, "writes": len(events),
              "provider_requests": 0, "full_admission_tested": False,
              "scope": "Actual intent POST and dedicated-App reservation POST through outside_reserve, then API readback. "
                       "Not triage, eligibility, reviewer acceptance or a merge; test marker and check are excluded from live admission."}
    save("result.json", result)
    return result


def main():
    output = Path(os.environ["RUNNER_TEMP"])/"protocol-b-admission-test"
    output.mkdir(exist_ok=True)
    def save(name, value):
        (output/name).write_text(json.dumps(value, indent=2)+"\n", encoding="utf-8")
    gate, digest = load_program(Path(__file__).resolve().parents[1]/"workflows/protocol-b.yml")
    gh, app = gate.start_clients()
    save("source.json", {"workflow_sha256": digest, "source_sha": os.environ["GITHUB_SHA"]})
    result = exercise(gate, gh, app, os.environ, save)
    print(json.dumps({"comment": result["comment"]["html_url"], "check": result["check"]["id"], "provider_requests": 0}))


if __name__ == "__main__":
    main()
