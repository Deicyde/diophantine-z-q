/-! ## g0-assemble2: `ModelNoncomm` proved from `MulIsogeny`
-- (g0-assemble3: `hD.2^11` → `hD.2^11.1` (1×), for G7Data's added last clause `[L:ℚ] ≤ D`)

On G7's model `A_{L'} = (PK.A)_{L'}` (`IsQMModel`), let `ψ : 𝒪 → End(A_{L'})` be `ι` followed by
unram-tate's base-change ring maps `endBC`. If `ψ(i)` and `ψ(j)` commuted, then `ij = -ji` would give
`2·ψ(j)ψ(i) = 0`, hence `12 = 2·ψ(j)²·ψ(i)² = 0` in `End(A_{L'})` (`i² = 2`, `j² = -3`). But
`[12]` is an isogeny (`MulIsogeny`), so `0 = [12]` would be surjective; it factors through
`Spec L'` (a point), so `A_{L'}` would be a point, while `dim A_{L'} = 2` (`model_dim`). -/

noncomputable section

namespace HSyn.G0AssembleMod

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- An abelian variety of dimension `2` is not a point: the zero endomorphism (`1` in the
convolution monoid, `toUnit ≫ η`) is not surjective. -/
theorem not_surjective_zero_hom {K : Type} [Field K] (A : PkgI3.AbVar K) (hA : A.dim = 2) :
    ¬ Surjective ((0 : PkgI3.AbVar.End A).hom).left := by
  intro hs
  have hsub : Subsingleton A.X.left := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hs.surj a
    obtain ⟨b', rfl⟩ := hs.surj b
    have h0 : ((0 : PkgI3.AbVar.End A).hom) = toUnit A.X ≫ η[A.X] := rfl
    rw [h0, Over.comp_left, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    haveI : Subsingleton (PrimeSpectrum K) := inferInstance
    exact Subsingleton.elim (α := PrimeSpectrum K) _ _
  have hle := topologicalKrullDim_zero_of_discreteTopology A.X.left
  have h2 : topologicalKrullDim A.X.left = 2 := hA
  rw [h2] at hle
  exact absurd hle (by decide)

/-- **`ModelNoncomm` is proved** from g0-fibresimple's `MulIsogeny` (here from mul-rigidity's leaf
`MulEtale`) and g0-dim's proved `DimBaseChange`. -/
theorem modelNoncomm_of_mulIsogeny (hMul : G0FibreSimple.MulIsogeny) : ModelNoncomm := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD
  letI : NumberField L' := numberField_of_fd L'
  haveI : CharZero L' := charZero_of_injective_algebraMap (algebraMap ℚ L').injective
  have hdim : (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 :=
    G0Split.model_dim G0Split.dimBaseChange (algebraMap L' Qbar)
      ((LeafAdopt.abVarEquiv L').symm (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')))
      P.A hD.2.2.2.2.2.2.2.2.2.2.2.1 P.surface
  obtain ⟨K, hKL, PK, -, rfl⟩ := hD.1
  set ψ : LeafQM.O →+* PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) :=
    (@UnramTate.endBC L _ _ L' _ (incAlg hLL')).comp
      ((@UnramTate.endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) with hψ
  refine ⟨ψ UnramTate.iO, ψ UnramTate.jO, fun h => ?_⟩
  set x := ψ UnramTate.jO
  set y := ψ UnramTate.iO
  have hy2 : y * y = 2 := by
    rw [← map_mul, UnramTate.iO_sq, map_add, map_one]; norm_num
  have hx2 : x * x = -3 := by
    rw [← map_mul, UnramTate.jO_sq, map_neg, map_add, map_add, map_one]; norm_num
  have hanti : y * x = -(x * y) := by
    rw [← map_mul, ← map_mul, UnramTate.iO_jO, map_neg]
  have hxy : x * y = -(x * y) := h.symm.trans hanti
  have h2 : (2 : PkgI3.AbVar.End _) * (x * y) = 0 := by
    rw [two_mul]; nth_rewrite 2 [hxy]; exact add_neg_cancel _
  have h3 : x * ((2 : PkgI3.AbVar.End _) * (x * y)) * y = 0 := by rw [h2, mul_zero, zero_mul]
  have h4 : x * ((2 : PkgI3.AbVar.End _) * (x * y)) * y = 2 * (x * x) * (y * y) := by
    noncomm_ring
  rw [h4, hx2, hy2] at h3
  have h12 : ((12 : ℤ) : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) = 0 := by
    have : (2 : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) * -3 * 2 =
        -((12 : ℤ) : PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) := by
      push_cast; norm_num
    rw [this, neg_eq_zero] at h3
    exact h3
  have hiso := hMul L' (@PkgI3.AbVar.baseChange L _
    (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) 12 (by norm_num)
  rw [h12] at hiso
  exact not_surjective_zero_hom _ hdim hiso.2

end HSyn.G0AssembleMod

end
