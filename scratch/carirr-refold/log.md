# carirr-refold results log

## Step 1 (2026-11-17 06:20)
- Merged origin/wip/carirr-odd (7b1ca2c16) into wip/carirr-refold: no conflicts (merge 3ca406194). VERIFIED (git).
- Base field: `carayolThmAIrr : CarayolPrinted.CarayolThmAIrr` (TailZ74, OpenResearchLeaves48 line 1299). VERIFIED (read).

## Step 3 (reading)
- H chain consumer: `carayolThmAIrr` -> `carayolThmA` (TailZ74 L721, Burnside) -> `r17 : LadicCond.CarayolR17'`
  -> `G0ModNewform.NewformLeaves` (TailD L149) -> step D5 (h-trust.md D5: level <= conductor). VERIFIED (read).
- Manuscript D5 = diophantine_zq.tex L852-857: "Local--global compatibility for the weight-two modular representation
  therefore bounds the primitive level N": no citation; coefficient places above 5 (p != 5) and 3 (p = 5) (L790-794). VERIFIED (read).
- Manuscript's only Carayol citation: L9778 (appendix, Thm 5.3 trace operators), coefficient place above 2, p odd,
  Pi_f^vee, rho_f = sigma(Pi_f^vee)^vee; normalization L9784-9796: arithmetic Frobenius polynomial X^2 - a_q X + q chi(q).
  Casselman Thm 1 at L9802-9806 used for local conductor one (ramified-character blocks). VERIFIED (read).
- CarayolRefold.lean §1-§2 (isOpen_ker_cycN, cycN_arithFrob, cycL_arithFrob, nearOne, odd_of_frobDet) compile, no warnings (lake env lean). VERIFIED.
- Carayol Thm A form: not expressible in Lean (no Weil-Deligne / local Langlands / automorphic reps in Mathlib 4.35,
  Tau Ceti, ZInQKernel; grep for WeilGroup/WeilDeligne/LocalLanglands/automorphic: no hits except an unrelated file). VERIFIED (search).
- Leaf CarayolThmAFrob: per-Frobenius det p*psi(p) (manuscript L9794 normalization) instead of global det; irreducible over K_lambda; DDT conductor.
- carayolThmAIrr_of_frob, frob_of_DDT31, carayolThmAIrr_of_DDT31, carayolR17'_of_frob compile (lake env lean, no warnings). VERIFIED.
- autofold dry run: strict count 4/27 on 31 -> 4/27 on 31 (count-neutral; unread leaf counts GLUE). VERIFIED.
- lake build +Main +Discharges +CarayolRefold: 16218 jobs, success; frozenTarget standard axioms. VERIFIED.
- #discharges: carayolThmAIrr by CarayolRefold.carayolThmAIrr_of_frob (assumes CarayolThmAFrob) and by carayolThmAIrr_of_DDT31; standard axioms. VERIFIED.
- Axioms of all 9 CarayolRefold declarations: standard. VERIFIED.
- Dry-run TailZ75 compiles; sixContactMin_of_open68 standard axioms. VERIFIED.
- Kinds rows from a real autofold run (reverted): -carayolThmAIrr consequence GLUE/GLUE; +carayolThmAFrob published GLUE/GLUE flag_class unread. VERIFIED.
