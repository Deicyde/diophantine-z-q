import ZInQKernel.HDecomp.Objects
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.Valuation.ValuationSubring

open CategoryTheory AlgebraicGeometry

namespace SZRaynaud.WildPeriod

section Valuation

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
variable (w : ValuationSubring Ω)

/-- The strict displacement inequality defining wild inertia. -/
private abbrev SmallDisplacement (σ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x

private theorem valuation_apply_eq {σ : Ω ≃ₐ[K] Ω} (hσ : SmallDisplacement w σ) (x : Ω) :
    w.valuation (σ x) = w.valuation x := by
  by_cases hx : x = 0
  · simp [hx]
  simpa only [sub_add_cancel] using w.valuation.map_add_eq_of_lt_right (hσ x hx)

private theorem smallDisplacement_mul {σ τ : Ω ≃ₐ[K] Ω}
    (hσ : SmallDisplacement w σ) (hτ : SmallDisplacement w τ) :
    SmallDisplacement w (σ * τ) := by
  intro x hx
  rw [AlgEquiv.mul_apply, show σ (τ x) - x = (σ (τ x) - τ x) + (τ x - x) by ring]
  apply w.valuation.map_add_lt _ (hτ x hx)
  rw [← valuation_apply_eq w hτ x]
  exact hσ (τ x) ((map_ne_zero τ).mpr hx)

private theorem smallDisplacement_pow {σ : Ω ≃ₐ[K] Ω} (hσ : SmallDisplacement w σ) (m : ℕ) :
    SmallDisplacement w (σ ^ m) := by
  induction m with
  | zero =>
    intro x hx
    simpa only [pow_zero, AlgEquiv.one_apply, sub_self, map_zero] using
      (pos_iff_ne_zero.mpr ((map_ne_zero w.valuation).mpr hx) : 0 < w.valuation x)
  | succ m ih => rw [pow_succ]; exact smallDisplacement_mul w ih hσ

/-- Average the displacement `d = σ x - x`. If `σ^m x = x`, the sum of the translates
of `d` is zero. Thus `-m*d` is a sum of terms of valuation strictly below `v(d)`
when `d ≠ 0`, which is impossible when `v(m) = 1`. -/
private theorem fix_of_pow {σ : Ω ≃ₐ[K] Ω} (hσ : SmallDisplacement w σ)
    {m : ℕ} (hm : w.valuation (m : Ω) = 1) {x : Ω} (hx : (σ ^ m) x = x) : σ x = x := by
  by_contra hne
  let d := σ x - x
  have hd : d ≠ 0 := sub_ne_zero.mpr hne
  have hsum (k : ℕ) : ∑ i ∈ Finset.range k, (σ ^ i) d = (σ ^ k) x - x := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, show d = σ x - x from rfl, map_sub,
        pow_succ, AlgEquiv.mul_apply]
      ring
  have hlt := w.valuation.map_sum_lt (s := Finset.range m)
    (f := fun i => (σ ^ i) d - d) ((map_ne_zero w.valuation).mpr hd)
    (fun i _ => smallDisplacement_pow w hσ i d hd)
  rw [Finset.sum_sub_distrib, hsum m, hx, sub_self, zero_sub, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, w.valuation.map_neg, map_mul, hm, one_mul] at hlt
  exact (lt_irrefl _) hlt

private theorem valuation_natCast_eq_one {O : ValuationSubring K}
    (hw : w.comap (algebraMap K Ω) = O) {m : ℕ} (hm : IsUnit (m : O)) :
    w.valuation (m : Ω) = 1 := by
  let i : O →+* w := ((algebraMap K Ω).comp O.toSubring.subtype).codRestrict w.toSubring
    (fun a => ValuationSubring.mem_comap.mp (hw.symm ▸ a.property))
  have hu : IsUnit (m : w) := by simpa only [map_natCast] using hm.map i
  have h := (w.valuation_eq_one_iff (m : w)).mp hu
  change w.valuation (w.toSubring.subtype (m : w.toSubring)) = 1 at h
  rwa [map_natCast] at h

/-- Remove the `ℓ`-part of the order of the restriction of a wild automorphism to a finite
normal extension, using the displacement inequality and the fact that `ℓ` is a unit. -/
private theorem exists_coprime_fix_field [Normal K Ω] {O : ValuationSubring K}
    (hw : w.comap (algebraMap K Ω) = O) {σ : Ω ≃ₐ[K] Ω} (hσ : SmallDisplacement w σ)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O))
    (F : IntermediateField K Ω) [FiniteDimensional K F] [Normal K F] :
    ∃ N : ℕ, N.Coprime ℓ ∧ ∀ x ∈ F, (σ ^ N) x = x := by
  let s := AlgEquiv.restrictNormalHom F σ
  obtain ⟨b, m, hℓm, hs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos s).ne' ℓ hℓ.ne_one
  refine ⟨m, (hℓ.coprime_iff_not_dvd.mpr hℓm).symm, fun x hx => ?_⟩
  have horder : AlgEquiv.restrictNormalHom F ((σ ^ m) ^ (ℓ ^ b)) = 1 := by
    rw [map_pow, map_pow, ← pow_mul, mul_comm m (ℓ ^ b)]
    change s ^ (ℓ ^ b * m) = 1
    rw [← hs, pow_orderOf_eq_one]
  have hfix : ((σ ^ m) ^ (ℓ ^ b)) x = x :=
    (AlgEquiv.restrictNormal_eq_one_iff F _).mp horder x hx
  apply fix_of_pow w (smallDisplacement_pow w hσ m) _ hfix
  exact valuation_natCast_eq_one w hw (by simpa only [Nat.cast_pow] using hℓO.pow b)

end Valuation

section Points

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- An algebraic point of a scheme locally of finite type is fixed by automorphisms
fixing a finite field. Generalizes the affine argument of `ReductSplit.exists_fixing_field`
to an arbitrary algebraic extension. -/
private theorem exists_fixing_field [Algebra.IsAlgebraic K Ω]
    (X : Over (Spec (CommRingCat.of K))) [LocallyOfFiniteType X.hom]
    (q : PkgI3.AbVar.ptObj (K := K) Ω ⟶ X) :
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∀ σ : Ω ≃ₐ[K] Ω, (∀ y ∈ F, σ y = y) → PkgI3.AbVar.galHom σ ≫ q = q := by
  classical
  let q₀ : Spec (CommRingCat.of Ω) ⟶ X.left := q.left
  have hq₀ : q₀ ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := Over.w q
  let p : X.left := q₀ (IsLocalRing.closedPoint Ω)
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, -⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  change X.left.Opens at U
  change IsAffineOpen U at hU
  have hrange : Set.range q₀ ⊆ Set.range U.ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h : s = IsLocalRing.closedPoint Ω :=
      Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [h]
    exact hpU
  let q' := IsOpenImmersion.lift U.ι q₀ hrange
  have hq' : q' ≫ U.ι = q₀ := IsOpenImmersion.lift_fac _ _ _
  let e := hU.isoSpec
  let φ : Γ(X.left, U) ⟶ CommRingCat.of Ω := Spec.preimage (q' ≫ e.hom)
  let θ : CommRingCat.of K ⟶ Γ(X.left, U) := Spec.preimage (e.inv ≫ U.ι ≫ X.hom)
  have hφ : Spec.map φ = q' ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ U.ι ≫ X.hom := Spec.map_preimage _
  have hql : q₀ = Spec.map φ ≫ e.inv ≫ U.ι := by
    rw [hφ, Category.assoc, e.hom_inv_id_assoc, hq']
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K Ω) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, ← Category.assoc q', hq', hq₀]
  have hft : θ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hθ]
    infer_instance
  let : Algebra K Γ(X.left, U) := θ.hom.toAlgebra
  obtain ⟨s, hs⟩ := hft.out
  let φa : Γ(X.left, U) →ₐ[K] Ω :=
    { φ.hom with
      commutes' := fun c => congrArg (fun f => CommRingCat.Hom.hom f c) hcomp }
  have : Finite ((φa : Γ(X.left, U) → Ω) '' (s : Set Γ(X.left, U))) :=
    (s.finite_toSet.image _).to_subtype
  refine ⟨IntermediateField.adjoin K ((φa : Γ(X.left, U) → Ω) '' (s : Set _)),
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral), fun σ hσ => ?_⟩
  have hfix : (σ : Ω →ₐ[K] Ω).comp φa = φa := by
    apply AlgHom.ext_of_adjoin_eq_top hs
    intro r hr
    exact hσ _ (IntermediateField.subset_adjoin _ _ ⟨r, hr, rfl⟩)
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ q₀ = q₀
  rw [hql, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact DFunLike.congr_fun hfix r

private theorem galAct_iterate (A : PkgI3.AbVar K) (σ : Ω ≃ₐ[K] Ω) (x : A.Pt Ω) (k : ℕ) :
    (A.galAct σ)^[k] x = A.galAct (σ ^ k) x := by
  induction k with
  | zero =>
    change x = PkgI3.AbVar.galHom 1 ≫ x
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    change PkgI3.AbVar.galHom σ ≫ (PkgI3.AbVar.galHom (σ ^ k) ≫ x) =
      PkgI3.AbVar.galHom (σ * σ ^ k) ≫ x
    rw [PkgI3.AbVar.galHom_mul, Category.assoc]

/-- **ON THE SPOT (provenance (c)).** A wild automorphism has a period prime to any
prime invertible in the valuation ring, at each point of an abelian variety. Take
a finite field of definition, pass to its normal closure, and remove the `ℓ`-part of
the order there by averaging displacements. This does not require the point to be torsion. -/
theorem exists_coprime_period [IsAlgClosure K Ω] {O : ValuationSubring K} {w : ValuationSubring Ω}
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓO : IsUnit (ℓ : O)) {σ : Ω ≃ₐ[K] Ω}
    (hσ : ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x) (x : A.Pt Ω) :
    ∃ N : ℕ, N.Coprime ℓ ∧ (A.galAct σ)^[N] x = x := by
  obtain ⟨F, hF, h⟩ := exists_fixing_field A.X x
  let E := IntermediateField.normalClosure K F Ω
  have : FiniteDimensional K E := inferInstanceAs (FiniteDimensional K (IntermediateField.normalClosure K F Ω))
  have : Normal K E := inferInstanceAs (Normal K (IntermediateField.normalClosure K F Ω))
  obtain ⟨N, hcop, hfix⟩ := exists_coprime_fix_field w hw hσ hℓ hℓO E
  refine ⟨N, hcop, (galAct_iterate A σ x N).trans (h _ fun y hy => ?_)⟩
  exact hfix y (IntermediateField.le_normalClosure F hy)

end Points

#print axioms valuation_apply_eq
#print axioms smallDisplacement_mul
#print axioms smallDisplacement_pow
#print axioms fix_of_pow
#print axioms valuation_natCast_eq_one
#print axioms exists_coprime_fix_field
#print axioms exists_fixing_field
#print axioms galAct_iterate
#print axioms exists_coprime_period

end SZRaynaud.WildPeriod
