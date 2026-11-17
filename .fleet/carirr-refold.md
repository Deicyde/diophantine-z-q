# carirr-refold (2026-11-17)

**Verdict.** `carayolThmAIrr` is discharged by a new, weaker leaf, `CarayolRefold.CarayolThmAFrob`, in
`ZInQKernel/Contrib/OneProof/CarayolRefold.lean`. The leaf cannot sit on Carayol's own form of Théorème (A).

**The new leaf.**
- It has the per-Frobenius clause "trace a_p, det p ψ(p)". That is the normalization the manuscript reads off
  Carayol (diophantine_zq.tex L9784-9796).
- It asks for irreducibility over K_λ (Ribet).
- Its conductor clause is DDT's integral form.
- Oddness is no longer a clause. It is proved by `odd_of_frobDet`: one Chebotarev Frobenius element near complex
  conjugation, plus the ultrametric norm.
- carirr-odd's DDT 3.1 leaf implies it (`frob_of_DDT31`), so it is not stronger than the print.

**Why Carayol's own form is not reached.** At ramified p, Théorème (A) is local–global compatibility through the
local Langlands correspondence. Lean has no π_{f,p}, no Weil–Deligne representations and no local Langlands
(searched Mathlib 4.35, Tau Ceti and ZInQKernel). So the conductor clause stays a composite of Carayol, the
conductor compatibility of local Langlands, and Casselman Thm 1. Only DDT 3.1 prints it as one statement. Casselman
Thm 1 alone would be inert.

**Route issue (top of report).** The H proof's D5 step (L852-857) uses "local–global compatibility" without citing
anything, and also leaves Casselman uncited. The project imports the manuscript's only Carayol citation, L9778,
which is an appendix use for Theorem 5.3 at a place above 2. D5 needs places above 5 and 3. There is no deviation in
the argument; the citation gap is the manuscript's.

**Compiles (VERIFIED).**
- CarayolRefold.lean: no warnings, standard axioms.
- Full build of Main + Discharges: 16218 jobs.
- `#discharges`: `[OpenResearchLeaves48.carayolThmAIrr] by CarayolRefold.carayolThmAIrr_of_frob`, still assuming
  `[CarayolRefold.CarayolThmAFrob]`.
- The autofold dry-run module TailZ75 compiles. The fold is count-neutral (4/27 → 4/27): the new leaf is flagged
  unread and counts GLUE.

**Kinds rows.**
- Removed: `carayolThmAIrr`.
- Added: `research carayolThmAFrob published unread… GLUE GLUE … long-pole T4 unread elliotglazer/diophantine-z-q#37`.

**Remains.**
- A reader checks the leaf against DDT 3.1 (a)-(d) and Ribet Thm 2.3. That makes it GLUE −1.
- A locators.md row; proposed text is in report §4.

Report: docs/research/carirr-refold.md. Scratch: scratch/carirr-refold/.
