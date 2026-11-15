# ht-bypass (field `eigenformHTNew`): fleet summary

**Verdict.** The field cannot be removed with the abelian-variety fields. It is not false, vacuous or inert.
Counts are unchanged and no fold applies.

- **One use (VERIFIED).** The field becomes `r13 = EigenformHT` (TailX l.205). `r13` is read only by
  `g8_g12_of_leaves3` → `g12` → `G12Weight` (`g12Weight_of`). There it is applied once, at **ℓ = 5**, to the eigenform
  that Pan∘Berger attaches to G8's `r₅`. Its only job is to rule out weight **k ≥ 3**: at k = 2 the conclusion holds
  trivially with n = 0.
- **Weakest needed form.** `EigenformHTNew5Ge3`: the field at ℓ = 5, k ≥ 3, every level. It is still GLUE (c) and not in
  printed form, because Kato's `V_f` cannot be defined in Mathlib; the source is Kato 2004 §§9.2-9.4, locators.md R13.
  `G12Weight`, `g12`, `g8_g12` and `AfterG7` are re-proved in Lean with the weak form (`afterG7_of3Weak`).
- **Why the abelian-variety fields cannot help.** They reach only weight 2 (`r16` + the de Rham comparison), and the
  route never uses weight 2. Determinants, Weil/Ramanujan absolute values and Newton polygons are consistent with
  every k. Only the gap between the two Hodge–Tate weights of ρ_g tells k apart, and for k ≥ 3 that is exactly Kato's
  content (SPECULATIVE judgement; argument in report §3). ser-ell's route 1 (Serre's conjecture) would avoid both
  `r11r12` and this field, at a larger cost.

**What compiles.** `ZInQKernel/Contrib/OneProof/EigenformHTWeak.lean` (imports TailX), the same text as
`scratch/ht-bypass/HTBypass.lean`. All theorems use only the standard axioms. `#discharges` reports no discharge from
it, as expected since it proves no field (output in `scratch/ht-bypass/Discharges-output.txt`).

**What remains.** Optional: a weaker-leaf bypass fold from `AfterG7` upward to replace the field by
`EigenformHTNew5Ge3`. That needs integrator work and gains no GLUE count. Recommendation: keep the field and note the
ℓ = 5, k ≥ 3 instance in OPEN.md. `autofold.json` records that no autofold applies.
Report: `docs/research/ht-bypass.md`.
