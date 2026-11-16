# Contributing to "Z is Diophantine in Q": a memo for people

16 November 2026 · https://github.com/elliotglazer/diophantine-z-q

## The short version

- You can contribute with or without an AI agent. If you use one, give it `AGENT-INSTRUCTIONS.md` along with your request.
- The most valuable thing an outsider can do is find a step that is wrong or not justified and report it precisely. That takes an issue, not a pull request.
- Improvements (a better polynomial, a shorter proof, a Lean proof of one of the open premises) come in as a focused note or module. We integrate accepted improvements into the next full version of the manuscript and credit you.
- Every pull request that changes mathematics, proofs or policy is reviewed by two AI reviewers from different model families; purely editorial fixes can take a lighter path. For outside contributors a maintainer has to start that review. Wording quibbles do not block you.

## What the project is

A manuscript, currently about 700 pages, proving that the integers can be defined inside the rationals by a single explicit polynomial equation of degree four, together with the computations behind it and a partial formalization in Lean. It was written by a human working with several AI systems, and it is reviewed the same way. The README states the current results and who did what.

Because of how it was produced, we do not ask you to trust it. We ask you to check it.

## Ways to help

| You want to | Do this | Effort for you |
|---|---|---|
| Report an error, a gap or an unclear step | Open an issue with the version, the exact location, the step, and what you tried | Low |
| Fix a typo, link, credit or build instruction | Small pull request, documentation only | Low |
| Propose a mathematical improvement or a repair | Pull request adding a self-contained note, with any data and an independent checker | Medium to high |
| Prove something in Lean | Pull request adding a module under `ZInQKernel/Contrib/` | Medium to high |
| Report that a build or computation did not reproduce | Open an issue with platform, versions, command and output | Low |

If you are unsure where your idea fits, open an issue and ask before writing anything long.

## What happens to a pull request

1. You open it from a fork and fill in the template.
2. Automated checks run: the paper builds, the computations replay, and for Lean changes the code builds and is audited for axioms. For a first-time contributor a maintainer has to approve these runs. Green checks mean these reproduce. They do not mean the mathematics is right.
3. A maintainer looks at it and, if it is ready, starts the review. Outside contributors cannot start it themselves. This is deliberate: each round costs money and runs your changes through the project's reviewers.
4. Two AI reviewers read your change and the parts of the manuscript it touches. Each posts its report, and the gate posts one summary. Each finding is labelled:
   - **Error** or **gap**: has to be fixed or answered before merging.
   - **Note**: wording and presentation. Recorded in a backlog, does not hold you up.
   - **Source access**: a reviewer could not open a reference. It holds things up unless the other reviewer read the same passage; a precise citation usually settles it.
   - **Incomplete review**: a reviewer could not finish. Smaller pull requests avoid this.
5. You push fixes and ask for another round. One round per request.
6. The maintainer merges when both reviewers have no blocking finding. Only a repository admin can overrule a finding, and when that happens the record says so openly.

## What we ask of you

- **Be specific.** Version, commit, label or line, and the exact step. "Section 12 seems off" cannot be acted on.
- **Say what you checked and what you did not.** Proved by hand, verified by exact computation, tested at sample points, or taken from a source: these are different, and we need to know which. "Not checked" is a perfectly good answer.
- **Keep it small.** One topic per pull request. Do not reformat or reorganize.
- **Leave released versions alone.** Each released manuscript is frozen. Improvements go into the next version, which the maintainers assemble.
- **Disclose AI use.** Tell us which model did what and what you verified yourself. This is normal here and is not held against you.
- **Stay responsible for your agent.** It posts in your name. Read what it is about to submit before it submits. Agents are confident about things they have not checked; ours are too.
- **No copyrighted scans, no credentials, no large vendored code** without asking first.

## What you can expect from us

- Credit for what you contribute, in the repository and in the manuscript where it is used.
- A written reason for any rejection.
- That reviewer findings are preserved in the open, including the ones that went against us.
- Honest limits: the review is done by AI systems under one maintainer's supervision. Turnaround depends on that one person. The review process was reworked this week to be lighter for outside contributors, and parts of it, in particular a faster path for Lean proofs, are still being finished. If the process gets in your way, say so in an issue; that is a contribution too.

## Where things are

- `README.md`: current results, versions, credits.
- `CONTRIBUTING.md`: what a good report contains.
- `docs/research-review/README.md`: how review runs.
- `docs/lean-contributions.md`: Lean premises that are open, and the exact form a proof must take.
- `docs/release-policy.md`: how an improvement becomes an official record.
- `AGENT-INSTRUCTIONS.md`: what to hand your AI agent.
