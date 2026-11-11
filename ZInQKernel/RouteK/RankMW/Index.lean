import ZInQKernel.RouteK.RankMW.PhiAdd

/-!
# Finiteness of `[E(K) : 2E(K)]` from finite Kummer images

For `E = E_b`, `E' = E_{b'}`, `b' = -4b`, the two-isogeny `φ : E → E'` and the dual
`φ̂ = λ ∘ φ_{b'} : E' → E` are homomorphisms (`mwPhiHom`), `φ̂ ∘ φ = [2]` (`rescale_phi_phi`),
`ker α_{b'} = φ(E)` and `ker α_b = φ̂(E')` (`kummer_eq_one_iff`). Hence
`2E = φ̂(ker α_{b'})`, and `[E : 2E] = [ker α_b : 2E] · [E : ker α_b]` is bounded by
`#α_{b'}(E') · #α_b(E)`. Only finiteness is recorded.
-/

namespace ZInQ.RouteK.Rank

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Descent

variable {K : Type*} [Field K] [DecidableEq K] {b b' b'' : K} [(shortCurve b).IsElliptic]
  [(shortCurve b').IsElliptic] [(shortCurve b'').IsElliptic]

/-- A Kummer map with finite image has a kernel of finite index. -/
theorem mwKer_kummer_finiteIndex (h : (Set.range (kummer b)).Finite) :
    (kummerHom (b := b)).ker.FiniteIndex := by
  have hfin : Finite (kummerHom (b := b)).range := by
    have : ((kummerHom (b := b)).range : Set (Additive (SqClass K))) =
        Additive.toMul ⁻¹' Set.range (kummer b) := by
      ext c
      simp only [SetLike.mem_coe, AddMonoidHom.mem_range, Set.mem_preimage, Set.mem_range]
      constructor
      · rintro ⟨P, rfl⟩; exact ⟨P, rfl⟩
      · rintro ⟨P, hP⟩; exact ⟨P, by rw [← kummerHom_apply] at hP; exact hP⟩
    have h' : (Additive.toMul ⁻¹' Set.range (kummer b)).Finite :=
      h.preimage (Additive.toMul.injective.injOn)
    rw [← this] at h'
    exact h'.to_subtype
  have : Finite ((shortCurve b).toAffine.Point ⧸ (kummerHom (b := b)).ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  exact ⟨AddSubgroup.index_ne_zero_of_finite⟩

variable (hb' : b' = -4 * b) (hb'' : b'' = -4 * b')

/-- The dual isogeny `φ̂ = λ_b ∘ φ_{b'} : E' → E`. -/
noncomputable def mwPhiHat : (shortCurve b').toAffine.Point →+ (shortCurve b).toAffine.Point :=
  (rescale (b := b) (b'' := b'') (by rw [hb'', hb']; ring)).toAddMonoidHom.comp (mwPhiHom hb'')

include hb' in
theorem mwPhiHat_phi (P : (shortCurve b).toAffine.Point) :
    mwPhiHat hb' hb'' (phi hb' P) = 2 • P :=
  rescale_phi_phi hb' hb'' P

include hb' in
/-- `ker α_b = φ̂(E')`. -/
theorem mwKer_kummer_eq_range :
    (kummerHom (b := b)).ker = (mwPhiHat hb' hb'').range := by
  have h16 : b'' = 16 * b := by rw [hb'', hb']; ring
  ext P
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  change kummer b P = 1 ↔ _
  rw [← (rescale h16).apply_symm_apply P, kummer_rescale, kummer_eq_one_iff hb'']
  constructor
  · rintro ⟨Q, hQ⟩
    exact ⟨Q, by simp only [mwPhiHat, AddMonoidHom.coe_comp, Function.comp_apply,
      mwPhiHom_apply, AddEquiv.coe_toAddMonoidHom]; rw [hQ]⟩
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, (rescale h16).injective ?_⟩
    rw [AddEquiv.apply_symm_apply] at hQ ⊢
    exact hQ

include hb'' in
/-- `2E ≤ φ̂(ker α_{b'})`, i.e. `ker α_{b'} ≤ φ̂⁻¹(2E)`. -/
theorem mwKer_kummer'_le_comap :
    (kummerHom (b := b')).ker ≤
      (nsmulAddMonoidHom (α := (shortCurve b).toAffine.Point) 2).range.comap
        (mwPhiHat hb' hb'') := by
  intro Q hQ
  rw [AddMonoidHom.mem_ker] at hQ
  change kummer b' Q = 1 at hQ
  obtain ⟨P, rfl⟩ := (kummer_eq_one_iff hb' Q).mp hQ
  rw [AddSubgroup.mem_comap, mwPhiHat_phi]
  exact ⟨P, rfl⟩

include hb' hb'' in
/-- **Finite index of `2E`** from finite Kummer images of `E_b` and `E_{-4b}`. -/
theorem mwFiniteIndex_two_of_kummer (h : (Set.range (kummer b)).Finite)
    (h' : (Set.range (kummer b')).Finite) :
    (nsmulAddMonoidHom (α := (shortCurve b).toAffine.Point) 2).range.FiniteIndex := by
  have hH := mwKer_kummer_finiteIndex h
  have hH' := mwKer_kummer_finiteIndex h'
  have hle : (nsmulAddMonoidHom (α := (shortCurve b).toAffine.Point) 2).range ≤
      (kummerHom (b := b)).ker := by
    rintro _ ⟨P, rfl⟩
    rw [AddMonoidHom.mem_ker]
    exact congrArg Additive.ofMul (kummer_two_nsmul P)
  have hc : ((nsmulAddMonoidHom (α := (shortCurve b).toAffine.Point) 2).range.comap
      (mwPhiHat hb' hb'')).FiniteIndex :=
    AddSubgroup.finiteIndex_of_le (mwKer_kummer'_le_comap hb' hb'')
  refine ⟨?_⟩
  rw [← AddSubgroup.relIndex_mul_index hle]
  refine mul_ne_zero ?_ hH.index_ne_zero
  rw [mwKer_kummer_eq_range hb' hb'', ← AddSubgroup.index_comap]
  exact hc.index_ne_zero

end ZInQ.RouteK.Rank
