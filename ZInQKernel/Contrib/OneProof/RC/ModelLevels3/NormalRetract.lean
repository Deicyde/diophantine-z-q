import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! # Normal local rings from a split inclusion -/

namespace WeierstrassCurve.ModelLevels.Pinned

private theorem annihilators_sup_eq_top {S : Type*} [CommRing S]
    (hdom : ∀ (m : Ideal S) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    {a b : S} (hab : a * b = 0) :
    (⊥ : Ideal S).colon {a} ⊔ (⊥ : Ideal S).colon {b} = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let : m.IsPrime := hm.isPrime
  let : IsDomain (Localization.AtPrime m) := hdom m
  let f := algebraMap S (Localization.AtPrime m)
  have hzero : f a = 0 ∨ f b = 0 := by
    apply mul_eq_zero.mp
    rw [← map_mul, hab, map_zero]
  have hex (x : S) (hx : f x = 0) :
      ∃ s : S, s ∉ m ∧ s ∈ (⊥ : Ideal S).colon {x} := by
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl _ x).mp hx
    exact ⟨s, s.property, Submodule.mem_colon_singleton.mpr hs⟩
  rcases hzero with ha | hb
  · obtain ⟨s, hs, hs'⟩ := hex a ha
    exact hs (hle (Ideal.mem_sup_left hs'))
  · obtain ⟨s, hs, hs'⟩ := hex b hb
    exact hs (hle (Ideal.mem_sup_right hs'))

private theorem isDomain_of_split_local {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsLocalRing A] (r : S →ₗ[A] A) (hr : r 1 = 1)
    (hdom : ∀ (m : Ideal S) [m.IsMaximal], IsDomain (Localization.AtPrime m)) :
    IsDomain A := by
  have hlin (x : A) (y : S) : r (algebraMap A S x * y) = x * r y := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have hnd : NoZeroDivisors A := ⟨fun {a b} hab => by
    let f := algebraMap A S
    have hfab : f a * f b = 0 := by rw [← map_mul, hab, map_zero]
    have hh := annihilators_sup_eq_top hdom hfab
    have h1 : (1 : S) ∈ (⊥ : Ideal S).colon {f a} ⊔ (⊥ : Ideal S).colon {f b} :=
      (Ideal.eq_top_iff_one _).mp hh
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp h1
    have hs' : a * r s = 0 := by
      rw [← hlin, mul_comm, show s * f a = 0 from Submodule.mem_colon_singleton.mp hs, map_zero]
    have ht' : b * r t = 0 := by
      rw [← hlin, mul_comm, show t * f b = 0 from Submodule.mem_colon_singleton.mp ht, map_zero]
    have hst' : r s + r t = 1 := by rw [← map_add, hst, hr]
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (show IsUnit (r s + r t) by rw [hst']; exact isUnit_one) with h | h
    · exact Or.inl (h.mul_left_eq_zero.mp hs')
    · exact Or.inr (h.mul_left_eq_zero.mp ht')⟩
  exact (isDomain_iff_noZeroDivisors_and_nontrivial A).mpr ⟨hnd, inferInstance⟩

private theorem scaledRoot_dvd {D : Type*} [CommRing D] [IsDomain D] [IsIntegrallyClosed D]
    {a b : D} (p : Polynomial D) (hp : p.Monic) (h : (p.scaleRoots b).eval a = 0) :
    b ∣ a := by
  by_cases hb : b = 0
  · have ha : a ^ p.natDegree = 0 := by
      simpa [hb, Polynomial.scaleRoots_zero, hp.leadingCoeff] using h
    simp [hb, (eq_zero_of_pow_eq_zero ha : a = 0)]
  let K := FractionRing D
  let f := algebraMap D K
  have hne : f b ≠ 0 := fun hz => hb ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp hz)
  have ha : f b * (f a / f b) = f a := by rw [mul_comm, div_mul_cancel₀ _ hne]
  have hz : Polynomial.eval₂ f (f a) (p.scaleRoots b) = 0 := by
    rw [Polynomial.eval₂_at_apply, h, map_zero]
  rw [← ha, Polynomial.scaleRoots_eval₂_mul] at hz
  have hint : IsIntegral D (f a / f b) :=
    ⟨p, hp, (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hne)⟩
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨c, IsFractionRing.injective D K ?_⟩
  rw [map_mul, hc, ha]

private theorem isIntegrallyClosed_of_split {A S : Type*} [CommRing A] [CommRing S]
    [Algebra A S] [IsDomain A] (r : S →ₗ[A] A) (hr : r 1 = 1)
    (hdom : ∀ (m : Ideal S) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    (hclosed : ∀ (m : Ideal S) [m.IsMaximal], IsIntegrallyClosed (Localization.AtPrime m)) :
    IsIntegrallyClosed A := by
  let K := FractionRing A
  let f := algebraMap A K
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  obtain ⟨p, hp, hroot⟩ := hx
  have hp0 : (p.scaleRoots b).eval a = 0 := by
    apply IsFractionRing.injective A K
    rw [map_zero, ← Polynomial.eval₂_at_apply]
    exact Polynomial.scaleRoots_eval₂_eq_zero_of_eval₂_div_eq_zero
      (IsFractionRing.injective A K) hroot hb
  let g := algebraMap A S
  have hdvd : g b ∣ g a := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.mem_of_localization_maximal
    intro m hm
    let : m.IsPrime := hm.isPrime
    let : IsDomain (Localization.AtPrime m) := hdom m
    let : IsIntegrallyClosed (Localization.AtPrime m) := hclosed m
    let u := algebraMap S (Localization.AtPrime m)
    let v := u.comp g
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    apply scaledRoot_dvd (p.map v) (hp.map v)
    change ((p.map v).scaleRoots (v b)).eval (v a) = 0
    rw [← Polynomial.map_scaleRoots _ _ _ (by rw [hp.leadingCoeff, map_one]; exact one_ne_zero)]
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hp0, map_zero]
  obtain ⟨c, hc⟩ := hdvd
  have hc' : a = b * r c := by
    have hfix (z : A) : r (g z) = z := by
      rw [← mul_one (g z), ← Algebra.smul_def, map_smul, hr, smul_eq_mul, mul_one]
    rw [← hfix a, hc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  refine ⟨r c, ?_⟩
  rw [hc', map_mul, mul_comm, mul_div_cancel_right₀]
  exact fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hb) ((IsFractionRing.to_map_eq_zero_iff (K := K)).mp h)

/-- A local ring that is a module summand of a ring with normal local domains
at all maximal ideals is itself a normal domain. -/
theorem local_normal_of_split {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [IsLocalRing A] (r : S →ₗ[A] A) (hr : r 1 = 1)
    (hdom : ∀ (m : Ideal S) [m.IsMaximal], IsDomain (Localization.AtPrime m))
    (hclosed : ∀ (m : Ideal S) [m.IsMaximal], IsIntegrallyClosed (Localization.AtPrime m)) :
    IsDomain A ∧ IsIntegrallyClosed A :=
  ⟨isDomain_of_split_local r hr hdom,
    let : IsDomain A := isDomain_of_split_local r hr hdom
    isIntegrallyClosed_of_split r hr hdom hclosed⟩

#print axioms annihilators_sup_eq_top
#print axioms isDomain_of_split_local
#print axioms scaledRoot_dvd
#print axioms isIntegrallyClosed_of_split
#print axioms local_normal_of_split

end WeierstrassCurve.ModelLevels.Pinned
