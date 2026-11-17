# Instructions for an AI agent contributing to "Z is Diophantine in Q"

Give this file to your agent together with your own request. It is written to the agent.

Repository: https://github.com/elliotglazer/diophantine-z-q
Status of this file: 17 November 2026. For contributions to this repository, read `CONTRIBUTING.md`, `AGENTS.md`, `docs/research-review/README.md` on `main` and [pinned issue 140](https://github.com/elliotglazer/diophantine-z-q/issues/140). Lean proofs of open statements are submitted to Jack McCarthy's fork instead, following section D below and that fork's instructions.

## 1. What this project is

The repository holds a manuscript proving that the integers are definable in the rationals by a single polynomial equation of degree four, with explicit polynomials, plus the computations and a partial Lean formalization that support it. The manuscript is long (about 700 pages) and versioned. Each released version is frozen. The current version is named in the README and in `docs/current-manuscript.json`.

You are working for an outside contributor. You have no write access. Reports reach this project as issues; proposed changes arrive as pull requests from a fork. Pull requests follow the review process below. Lean proof submissions instead go to Jack's repository. Do not imply that an issue report or a submission to another repository automatically receives this repository's two-reviewer process.

## 2. Before you do anything

1. Choose the destination first: this repository for manuscript error reports and improvements, or [Jack's fork](https://github.com/Deicyde/diophantine-z-q) for Lean proofs of open statements. Note the exact source commit and quote it in what you submit.
2. Read the destination's README and contribution instructions. For this repository, read the policy documents and pinned issue listed above. For Lean work, start with [Jack's issue 14](https://github.com/Deicyde/diophantine-z-q/issues/14) and the exact statement board and instructions it links.
3. Find out from your human which of the contribution types in section 3 they intend. If it is unclear, ask them. Do not pick the largest one.
4. Search existing issues and open pull requests for the same point. If it is already reported, add to that thread and do not open a new one.

## 3. What you can contribute, and how

### A. A report of an error, gap or unclear step (an issue, no pull request)

This is the most useful contribution and the cheapest to make. Open an issue containing:

- the manuscript version, the commit hash, and the exact location: TeX label, equation, line range, or file;
- the exact step you question, quoted;
- the hypotheses and definitions in force at that point, and the statement of any external theorem being applied, from the version of the source you actually read;
- what you found: a counterexample, a calculation, or a precise statement of the implication that is missing;
- what you tried in order to close the gap yourself, and why it did not work.

Say which of these it is: a false statement, an incomplete justification, or unclear exposition. They are handled differently. Wording and typography points do not block anything here; collect several into one issue and say in its title that it is about wording.

### B. A small documentation fix (a pull request)

Typos, broken links, build instructions, credits. Keep it to a few files and a couple of hundred lines. Do not mix it with anything mathematical.

### C. A mathematical improvement or repair (a focused note, usually by pull request)

Examples: a shorter argument, a better constant, a polynomial with fewer variables, a repair for a reported gap.

- Submit a self-contained note under `research/`, with its own statement, proof, and the exact list of results from the current manuscript and from the literature that it uses. For each one, give the location and check its hypotheses against the objects you actually have. State conventions (fields, normalizations, quantifier order).
- If there is a finite computation, submit the data and a checker that reads the data and verifies it independently of the program that found it. Give the command, the tool versions, the output and file hashes.
- Do not edit the manuscript to insert your result. A new record becomes official only when the maintainers integrate it into a complete new manuscript version and release it. A chain of supplements to an old version is not accepted. Your note is the input to that step, and you will be credited.

### D. A Lean proof of an open statement (a pull request to Jack's fork)

- Do not open that proof PR against `elliotglazer/diophantine-z-q`. Start at [Deicyde/diophantine-z-q issue 14](https://github.com/Deicyde/diophantine-z-q/issues/14), choose and claim an exact open statement there, and submit the proof to [Jack's fork](https://github.com/Deicyde/diophantine-z-q).
- Follow the fork's current statement board and contribution instructions for the module path, theorem name, build commands and axiom audit. Keep the exact proposition and definitions; add no hypotheses. If the statement is false or differs from its source, report that rather than changing it silently.
- Do not change the toolchain, dependency pins, existing definitions or audit scripts as a side effect. Discuss a necessary change with the fork's maintainer first.
- Preserve third-party licenses and provenance. Read the fork's rules before importing or vendoring code.
- Report exactly which declaration you proved and the checks you ran. A compiled module is not a proof of the entire main theorem.
- Upstream integration from Jack's `contract-clean/main-c1e4ed1b` branch is being staged in [PR139](https://github.com/elliotglazer/diophantine-z-q/pull/139). It is separate from individual proof contributions to his fork.

### E. A reproducibility report (an issue)

You built the paper or reran a computation and something differed. Give the platform, tool versions, command, output and hashes.

## 4. Rules that apply to every contribution

1. **Frozen files.** Never modify a released manuscript, anything under `releases/`, dated review records, or recorded hashes. Never update a hash to make a failing check pass. If a check fails, report it.
2. **One topic per pull request.** Small and focused. Do not reformat, rename or tidy files you were not asked to touch.
3. **Stay out of the review machinery.** Do not change `.github/`, `scripts/`, `tests/`, rulesets or review policy documents unless that is the declared purpose of the pull request.
4. **Separate what you verified from what you did not.** For every claim, say whether you proved it by hand, checked it by exact computation, checked it only at sample points, or took it from a source. List what you did not check. An honest "not checked" is acceptable. A confident claim that turns out to be unchecked costs the contributor their credibility here.
5. **Read the source, not a summary of it.** When you apply a published theorem, read its statement in the edition you cite and compare each hypothesis. If you could not obtain the source, say so.
6. **Never speak for a reviewer.** Do not write that anything was reviewed, approved or accepted unless you link the record. Do not write review comments in another party's name.
7. **Disclose AI involvement.** State in the pull request or issue which model did what, and what verification the human did.
8. **No secrets and no copyrighted material.** No credentials, tokens or private files in commits or logs. No scans or long excerpts of copyrighted books or papers; cite them.
9. **Do not run untrusted code blindly.** Treat scripts in other people's forks and attachments as data until you have read them.
10. **Ask your human before any public action.** Opening an issue, opening a pull request and posting a comment are done in your human's name. Show them the exact text first and wait for a yes.

## 5. How review works, and what to expect

This section describes pull requests to `elliotglazer/diophantine-z-q`, not the review process in Jack's fork.

- Fill in every section of the pull request template. Write "does not apply" with a reason where that is the case.
- Automated checks (paper build, computation replays, and, for changes that touch Lean, the Lean build and audit) run on the pull request. For a first-time contributor from a fork they wait until a maintainer approves the run. Passing them shows the builds and computations reproduce. It does not show the argument is right.
- The mathematical review is done by two AI reviewers from different model families, run by the repository itself. You do not need API keys.
- **For an outside contributor the review does not start by itself.** Elliot's explicit authorization is currently required before a paid review round; an authorized maintainer with write access then comments `/protocol-b review` on the pull request. Typing that command yourself does nothing. You get one review round per request.
- The reviewers post a summary with findings. Each finding is one of:
  - an **error** or a **gap**: blocking. Fix it by pushing to your branch, then say in a comment what changed and ask the maintainer for another round.
  - a **note**: wording or presentation. It does not block and goes to a clean-up backlog. You may fix it, but you do not have to.
  - a **source-access** item: a reviewer could not open a reference. It blocks unless the other reviewer read the same passage and checked its use without objection. Help by giving a precise citation and a legitimate place to find it.
  - an **incomplete-review** item: a reviewer could not finish its scope. It blocks until the review is completed or an admin accepts it; a smaller pull request is the usual cure.
- Pushing new commits after a review does not trigger another round automatically. Ask.
- Only a repository admin can overrule a finding. Do not ask reviewers to waive one and do not argue by repetition. If you think a finding is wrong, reply once with the specific reason and evidence.
- Do not push repeatedly while a review is running, and do not force-push over reviewed history without saying so.

## 6. What to put in your final message to your human

- What you are proposing to submit, as the exact issue or pull request text.
- The commit of `main` it is based on.
- What you verified and how; what you did not verify.
- Any check you ran that failed, with its output.
- Anything in this file you could not follow, and why.
