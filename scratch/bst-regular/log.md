# bst-regular results log

Base 182e3388b7416a1d625b1786b945b2e2b77b2e4e (confirmed). Worktree needed `lean/.lake` (helper package build) copied in
(build artifact only, not committed).

## Step (a), (b): ZInQKernel/Contrib/OneProof/BstRegular/Abstract.lean — COMPILES (lake build OK)

- `BstRegular.IsRegularB p B H` (structure): `stable` (H maps B to B), `frac` ((Frac B)^H = B^H, fraction-free:
  x,y ∈ B, y ≠ 0, σx·y = x·σy ∀σ∈H ⇒ x = c·y, c ∈ B^H), `line` (b ∈ B, b ≠ 0, σb ∈ ℚ_p·b ∀σ∈H ⇒ ∃ b' ∈ B, b b' = 1).
- `isDomain_sub` (b): every ℚ_p-subalgebra of B_dR is a domain. VERIFIED.
- `IsRegularB.inv_fixed`: B^H is a field. VERIFIED.
- `repr_inclT`, `repr_tensorAct`, `toMatrix_vAct_det_ne_zero`: coordinate lemmas (bases 1 ⊗ e_i). VERIFIED.
- `isAdmissibleT_of_isAdmissible_of_regular` (a): IsRegularB B H → IsAdmissible B H ρ → IsAdmissibleT B H ρ. VERIFIED.
  #print axioms: [propext, Classical.choice, Quot.sound].
  Proof: N = dim V B^H-independent d_j ∈ D (exists_linearIndependent_of_le_finrank); coordinate matrix M over B;
  minimal-support kernel vector + `frac` ⇒ contradiction, so det M ≠ 0 (Matrix.exists_mulVec_eq_zero_iff, B domain);
  M = R(σ)·σ(M) ⇒ σ(det M) = det R(σ)^{-1} det M ⇒ `line` ⇒ det M unit ⇒ basis (Pi.basisFun mapped by toLinearEquiv').
- Compile pitfalls: `simpa using hsum` / `linearIndependent_iff'` on `dB` timed out (AddCommGroup unification);
  `Fintype.linearIndependent_iffₛ` works. `simp_rw [hrel]` loops (rhs contains lhs). No Field instance on BdR p
  (no map_inv₀); keep inverses in ℚ_p.

## Conditional targets: ZInQKernel/Contrib/OneProof/BstRegular/Bst.lean — COMPILES (lake build OK)

- Open Props (not proved; stated precisely, taken as theorem arguments, no axiom):
  - `BstFracInvariants` (c): ∀ p ε₀ h K finite, x,y ∈ BstFOf(ξ), y ≠ 0, z ∈ B_dR, z·y = x, z G_K-fixed ⇒ z ∈ BstFOf(ξ).
  - `BstLineUnits` (d): ∀ p ε₀ h K finite, b ∈ BstFOf(ξ), b ≠ 0, ∀σ∈G_K ∃c∈ℚ_p, σb = c·b ⇒ ∃ b' ∈ BstFOf(ξ), b b' = 1.
- `isRegularB_bst` : BstFracInvariants → BstLineUnits → IsRegularB (BstFOf ξ) G_K. VERIFIED (stability: bstF_stable).
- `isAdmissibleT_of_isAdmissible` (target 1, conditional on (c),(d)). VERIFIED.
- `isPstFBasis_iff_isPstF`, `localIsPstFBasis_iff_localIsPstF` (target 2, conditional). VERIFIED.
- `colmezThm01_iff_bergerSurveyF` (target 3, conditional; forward direction unconditional = bergerSurveyF_of_colmez). VERIFIED.
- #print axioms for all: [propext, Classical.choice, Quot.sound] (scratch/bst-regular/Axioms.lean).
- Tree check: `BergerBst.FontaineBstInvariants` (B_st^{G_K} = K_0, dimension form) is a named input, NOT proved;
  B_dR^{G_K} = K proved (dimension form, `BdRInv.bdRInvariantsPrinted_proof`); log[p̃] transcendental over B_cris/B_max
  proved (`LogPFontaine.logPTildeTranscendental_proof`); no Frobenius-based K ⊗_{K_0} B_cris → B_dR injectivity found.

## #print axioms output (scratch/bst-regular/Axioms.lean, lake env lean)
'HDec.PkgI4.BstRegular.isAdmissibleT_of_isAdmissible_of_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.PkgI4.BstRegular.isDomain_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.PkgI4.BstRegular.isRegularB_bst' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.PkgI4.BstRegular.isAdmissibleT_of_isAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.PkgI4.BstRegular.isPstFBasis_iff_isPstF' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.PkgI4.BstRegular.localIsPstFBasis_iff_localIsPstF' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.PkgI4.BstRegular.colmezThm01_iff_bergerSurveyF' depends on axioms: [propext, Classical.choice, Quot.sound]

## Reductions considered, not attempted (see report §4)
- d1 (line in B_cris[X] has degree 0): needs log[p̃] ∉ Frac(B_cris) + B_dR^{G_K} at general K; tree has G_{Q_p} only;
  at general K this needs K ⊗_{K_0} B_cris → B_dR injective (c2). Not pursued.
