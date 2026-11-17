# hodgetate-from-dr — fleet summary

**Result: `hodgeTateDecompAbVar` is removed (−1 field, −1 GLUE).** The field `HodgeSplit.HodgeTateDecompAbVar`
(`ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g`, GLUE because the exponents need `dim t_A = dim t*_{A'} = g`) is proved in Lean
with its exact type by `ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_printed`
(`ZInQKernel/Contrib/OneProof/HodgeTatePairing.lean`, helpers `HodgeTatePairing{Decomp,Weil,Core}.lean`). Its
hypotheses are:
* one new leaf, `HodgeTateDecompExists`: Fontaine 1982's decomposition with bases chosen and **both exponents
  unnamed** (`ℂ_p(1)^a ⊕ ℂ_p^b`). It specializes the printed statement and uses no dimension fact. Rated printed form,
  bases chosen; locator UNVERIFIED. It is implied by the field (`hodgeTateDecompExists_of_field`);
* fields already open: `mumfordTorsionAlgClosed` (T5, so `dim V_p = 2g`), plus the T9 leaves `picRepresentableAbVar`,
  `picZeroAbVar`, `mumfordKLFiniteSectionAC`, `mumfordPhiSurjectiveAC` and `weilPairingMumford` (the Weil pairing over
  any field).

Tate's theorems, Ax–Sen–Tate and the isogeny quasi-inverse come from contributions that are already folded.

Proof: the Weil pairing makes `V ≅ V^∨(1)`. Counting `Hom_{G_F}(V, ℂ_p(1))` in two ways with Tate's theorems gives
`a = b`, and `a + b = 2g`.

**Compiles (VERIFIED):** the `lake build` of the contribution together with `Main` and `Discharges` succeeded
(14105 jobs). Both theorems use only the axioms `propext`, `Classical.choice` and `Quot.sound`. `#discharges` shows
`OpenResearchLeaves28.hodgeTateDecompAbVar` discharged. The `autofold --dry-run` of `scratch/hodgetate-from-dr/autofold.json`
gives strict and strictest counts of 16/21 → 17/20, so GLUE goes down by one. The dry-run module compiles, and
`sixContactMin_of_open39` uses only the standard axioms.

**Not done / notes:** the de Rham route (de Rham ⇒ Hodge–Tate) was not taken. The kernel has no Hodge filtration,
`t`, or `gr B_dR`, and the Hodge numbers of `D_dR(H¹)` could only enter as a composite GLUE leaf (report §4).
dict-galois (not merged here) has a stronger leaf `ℂ_p(1)^g ⊕ ℂ_p^b`, which needs `dim t_A = g`. My files have
different names, so the two do not collide. The `locators.md` row for the new leaf is proposed in the report and not
added (another task's file). Report: `docs/research/hodgetate-from-dr.md`.
