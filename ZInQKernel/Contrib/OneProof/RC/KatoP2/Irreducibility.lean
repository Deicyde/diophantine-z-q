import ZInQKernel.Contrib.OneProof.RC.KatoP2.Abelian

/-! Absolute irreducibility follows from the two elementary transvections in
the image over the cyclotomic tower. This is a characteristic-zero argument. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2

open PrintsArith
open scoped TensorProduct

/-- The basis transvection remains the corresponding basis transvection
under any extension of scalars. -/
theorem coord_transvection_baseChange {R A M : Type} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 2) R M) (i j : Fin 2) (c : R) :
    (LinearMap.transvection (c • b.coord j) (b i)).baseChange A =
      LinearMap.transvection ((algebraMap R A c) • (b.baseChange A).coord j) (b.baseChange A i) := by
  have hb : Module.Dual.baseChange A (b.coord j) = (b.baseChange A).coord j := by
    apply (b.baseChange A).ext
    intro k
    rw [Module.Basis.baseChange_apply, Module.Dual.baseChange_apply_tmul]
    by_cases h : j = k <;>
      simp [Module.Basis.coord_apply, Module.Basis.repr_self, h]
  rw [LinearMap.transvection.baseChange, map_smul, hb, ← Module.Basis.baseChange_apply]
  congr 1
  exact (IsScalarTower.algebraMap_smul A c ((b.baseChange A).coord j)).symm

/-- The rational quadratic twist is absolutely irreducible over the
dyadic cyclotomic tower. Serre supplies both opposing transvections;
a nonzero invariant subspace must contain both basis vectors. -/
theorem kodaiAbsIrred_of_serre (hS : SerreThm3) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hCM : HasNoCM E) (hdet : DetTateTwoCyclotomic E) (χ : GalQ →* ℤˣ) :
    KodaiAbsIrred (rationalTwist E χ) := by
  obtain ⟨n, _, hopen⟩ := serre_SL2_part hS E hCM hdet
  let c : ℤ_[2] := (2 : ℤ_[2]) ^ n
  let b := tateBasis E
  have hlift (i j : Fin 2) (hij : i ≠ j) :
      ∃ g : GalQ, FixesDyadicRoots g ∧
        tateRep E 2 g = LinearMap.transvection (c • b.coord j) (b i) := by
    have hzero : (c • b.coord j) (b i) = 0 := by
      simp [Module.Basis.coord_apply, Module.Basis.repr_self, hij.symm]
    let u := LinearEquiv.transvection hzero
    exact hopen u (by simp [u, hzero]) (fun x => by
      refine ⟨b.coord j x • b i, ?_⟩
      simp [u, c, LinearMap.transvection.apply, mul_smul])
  intro K _ _ W hW
  let B := (b.baseChange ℚ_[2]).baseChange K
  let cK := algebraMap ℚ_[2] K (algebraMap ℤ_[2] ℚ_[2] c)
  have hcK : cK ≠ 0 := by
    have hc : c ≠ 0 := pow_ne_zero n two_ne_zero
    have hq : algebraMap ℤ_[2] ℚ_[2] c ≠ 0 := fun hz =>
      hc ((IsFractionRing.injective ℤ_[2] ℚ_[2]) (hz.trans (map_zero _).symm))
    exact (map_ne_zero (algebraMap ℚ_[2] K)).mpr hq
  have H (i j : Fin 2) (hij : i ≠ j) (x) (hx : x ∈ W) (hy : B.coord j x ≠ 0) :
      B i ∈ W := by
    obtain ⟨g, hg, hρ⟩ := hlift i j hij
    let s : ℚ_[2] := ((χ g : ℤ) : ℚ_[2])
    have hs : algebraMap ℚ_[2] K s ≠ 0 := by
      exact (map_ne_zero _).mpr (Int.cast_ne_zero.mpr (Units.ne_zero (χ g)))
    have hx' := hW g hg x hx
    change (s • (tateRep E 2 g).baseChange ℚ_[2]).baseChange K x ∈ W at hx'
    rw [LinearMap.baseChange_smul, ← IsScalarTower.algebraMap_smul K s,
      LinearMap.smul_apply] at hx'
    apply (W.smul_mem_iff_of_isUnit (isUnit_iff_ne_zero.mpr hs)).mp at hx'
    rw [hρ, coord_transvection_baseChange, coord_transvection_baseChange,
      LinearMap.transvection.apply] at hx'
    have hdiff := W.sub_mem hx' hx
    rw [add_sub_cancel_left, LinearMap.smul_apply, smul_eq_mul] at hdiff
    exact (W.smul_mem_iff_of_isUnit
      (isUnit_iff_ne_zero.mpr (mul_ne_zero hcK hy))).mp hdiff
  by_cases hw : W = ⊥
  · exact Or.inl hw
  · right
    obtain ⟨x, hx, hx0⟩ := (W.ne_bot_iff).mp hw
    have hcoords (y : K ⊗[ℚ_[2]] (ℚ_[2] ⊗[ℤ_[2]] TateMod E 2)) :
        y = ∑ i, B.coord i y • B i := (B.sum_repr y).symm
    have hpair : B 0 ∈ W ∧ B 1 ∈ W := by
      by_cases h1 : B.coord 1 x = 0
      · have h0 : B.coord 0 x ≠ 0 := by
          intro h0
          exact hx0 (by rw [hcoords x, Fin.sum_univ_two, h0, h1]; simp)
        have hy := H 1 0 (by decide) x hx h0
        exact ⟨H 0 1 (by decide) (B 1) hy (by simp), hy⟩
      · have hy := H 0 1 (by decide) x hx h1
        exact ⟨hy, H 1 0 (by decide) (B 0) hy (by simp)⟩
    apply top_unique
    intro y _
    rw [hcoords y, Fin.sum_univ_two]
    exact W.add_mem (W.smul_mem _ hpair.1) (W.smul_mem _ hpair.2)

end ZInQ.Manuscript.RC.KatoP2
