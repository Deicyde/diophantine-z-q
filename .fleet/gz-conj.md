# gz-conj (fleet summary)

**Result: `ZInQ.GZHL3.GrossConjugationCd` is proved in Lean** (`ZInQ.GZConj.grossConjugationCd`,
`ZInQKernel/Contrib/OneProof/GrossConjugationCd.lean`, standard axioms only, no new leaf, statement unchanged).
The C_d split of hL3 (gz-weil) is now two leaves: `HeegnerPointRationalCd` (gz-heegner: from hCM +
`X0ModuliGaloisMero`) and `GrossZagierFormulaCd` (`grossZagierHeegnerCd_of_twoLeaves`,
`grossZagierHeegnerCd_of_printed`). GLUE −1 outside H (the consequence leaf GrossConjugationCd is gone).

Proof (all Lean): rootNumber = −1 for every newform of C_d (Tau Ceti FE vs the proved FunctionalEquation5 at
level 32d², L(f,s) ≢ 0) kills the ε=+1 clause; Fricke sign +1 ⇒ φ_f∘W_N = φ_f (fixed point i/√N);
conj φ_f(τ) = φ_f(1/(Nτ̄)); g₂,g₃ determine a lattice (new generic lemma `lattice_eq_of_g`) so conj commutes
with weierPt; Q* = [NC, B, A/N] permutes the Γ₀(N)-classes of residue β; so conj fixes the Heegner sum and
σy = y exactly. By-product: the ε = −1 clause of GrossConjugationAt for every E/ℚ (`conj_clause`).

Compiles: `lake build +ZInQKernel.Contrib.OneProof.GrossConjugationCd` (VERIFIED). MainEdit.lean (frozenTarget with hL3 replaced by the two remaining Heegner leaves, or by
X0ModuliGaloisMero + GrossZagierFormulaCd) compiles with standard axioms; `#discharges` shows no GZConj line because
GrossConjugationCd is not an open field until hL3 is split. Checks in scratch/gz-conj/
(Main.lean axioms; MainEdit.lean = frozenTarget with hL3 replaced; Discharges.lean); autofold spec
scratch/gz-conj/autofold.json (needs hL3 split into bundle fields first: hL3 is a top-level argument).

Remains: general-E ε=+1 clause (Manin–Drinfeld for the image of the cusp 0; not on the route);
the other two Heegner leaves (other tasks). Report: docs/research/gz-conj.md.
