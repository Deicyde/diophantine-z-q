# triage2 reading brief (for subagents)

Repo worktree: /home/jackmccarthy/dzq-wt/triage2 (Lean 4 project "Z is Diophantine in Q"). Read-only for you:
do NOT run Lean/lake, do NOT edit any file except your own notes file scratch/triage2/agent-<X>.md, no network.

Goal: for each assigned open hypothesis (a field of a Prop bundle), find the WEAKEST statement its consumers
on the live path of the single proof actually use, so that a one-agent task can remove the field outright
(by proving a weakened/specialized form, a "semantic prune" if a consumer ignores it, or a "bypass" if another
already-available statement gives what the consumer needs).

Where things are:
- Bundles: ZInQKernel/OneProof/H/TailZ34.lean (OpenResearchLeaves21, OpenAddedLeaves17), TailZ32.lean, TailX.lean.
  The top theorem sixContactMin_of_open28 converts bundles down a chain: openResearchLeaves20_of_OpenResearchLeaves21,
  ...19_of_...20, etc. (grep `_of_OpenResearchLeaves` / `_of_OpenAddedLeaves` / `theorem sixContactMin_of_open` in
  ZInQKernel/OneProof/H/*.lean). A field may be renamed/combined in a converter (e.g. `raynaudSemistable :=
  foo_of_SH n.raynaudSemistableSH n.strictHenselizationPair`), so follow the chain down to the theorems that really
  use the hypothesis (search for `.fieldname` and for the hypothesis' type name as a binder type `(h : TypeName)`).
- Field definitions and statements: docs/one-proof/OPEN.md (section per field), scratch/triage2/open_inscope.md.
- Earlier triage (line numbers stale, base e38375b3): docs/research/gap-triage.md, scratch/gap-triage/agent-*.md.
- Reports of tasks that proved things: docs/research/gt-*.md, sem-prune.md, yu-prune.md; contributions in
  ZInQKernel/Contrib/OneProof/*.lean.
- Libraries: Mathlib at .lake/packages/mathlib; vendored under ZInQKernel/Contrib/ (CloudW0*, Tau Ceti, Stacks,
  Mordell, FLT ports).
- Use grep/rg via Bash if you have it, otherwise search tools. Files are huge (LPrefix, TailC...): grep, don't read whole.

For EACH assigned field, write in your notes file:
1. Statement (Lean def name, file:line of the def) and a 3-line paraphrase.
2. Consumers: every theorem on the chain that uses it, file:line, and how (which conjuncts, which objects it is
   applied to — e.g. a specific prime p=5, a specific curve, a specific abelian variety, only one direction of an
   inequality, only for g = 1 or 2, only the existence part...). Follow until the use is concrete.
3. Weakest statement used (precise Lean-ish sketch).
4. Whether that weakest form looks provable now (from Mathlib, vendored libs, or by computing on the specific
   objects), or obtainable from another field/proved result (a bypass); or whether a consumer ignores it.
5. Tier guess (T1 hours / T2 day / T3 days / T4 research-scale) and a plan naming key declarations (give file:line
   for each declaration you cite so I can #check it).
Mark each claim VERIFIED (you read it in code, give file:line) or SPECULATIVE. Theorem numbers from memory: UNVERIFIED.
Be concise; it is fine to say "no narrowing found" with the evidence. Return a summary (<= 40 lines per field) as your
final message too.
