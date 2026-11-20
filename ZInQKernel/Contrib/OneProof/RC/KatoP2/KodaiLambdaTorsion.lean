import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-! Global torsion at the dyadic coefficient ring. The two sign maps and
the power-series variable provide two height-one primes away from two that
detect the generic signs. This is ring-theoretic glue, independent of Kato's
cohomology and Euler system. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2.Checked

open PowerSeries

private abbrev G := Multiplicative (ZMod 2)
private abbrev B := MonoidAlgebra ℤ_[2] G
private abbrev A := PowerSeries ℤ_[2]
private abbrev R := PowerSeries B

private def g : G := Multiplicative.ofAdd (1 : ZMod 2)

private theorem casesG (u : G) : u = 1 ∨ u = g := by
  have h : ∀ v : G, v = 1 ∨ v = g := by decide
  exact h u

private theorem g_ne : g ≠ 1 := by decide
private theorem gg : g * g = 1 := by decide

private def signG (minus : Bool) : G →* ℤ_[2] where
  toFun u := if minus = true ∧ u = g then -1 else 1
  map_one' := by simp [Ne.symm g_ne]
  map_mul' u v := by
    rcases casesG u with rfl | rfl <;> rcases casesG v with rfl | rfl <;>
      cases minus <;> simp [gg, Ne.symm g_ne]

private def signB (minus : Bool) : B →ₐ[ℤ_[2]] ℤ_[2] :=
  MonoidAlgebra.lift ℤ_[2] ℤ_[2] G (signG minus)

private def sign (minus : Bool) : R →+* A := PowerSeries.map (signB minus).toRingHom

private theorem sign_surj (minus : Bool) : Function.Surjective (sign minus) := by
  apply PowerSeries.map_surjective
  intro x
  exact ⟨algebraMap ℤ_[2] B x, (signB minus).commutes x⟩

private theorem signB_eq (b : Bool) (x : B) :
    signB b x = x.coeff 1 + (if b then -1 else 1) * x.coeff g := by
  have h : x = MonoidAlgebra.single 1 (x.coeff 1) + MonoidAlgebra.single g (x.coeff g) := by
    ext u
    rcases casesG u with rfl | rfl <;> simp [g_ne, Ne.symm g_ne]
  conv_lhs => rw [h]
  cases b <;> simp [signB, MonoidAlgebra.lift_single, signG, Ne.symm g_ne,
    smul_eq_mul, mul_comm]

private theorem sign_joint_zero {x : R} (h₀ : sign false x = 0) (h₁ : sign true x = 0) : x = 0 := by
  ext n u
  have h (b : Bool) (hb : sign b x = 0) :
      (coeff n x).coeff 1 + (if b then -1 else 1) * (coeff n x).coeff g = 0 := by
    rw [← signB_eq]
    simpa only [sign, coeff_map, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_zero]
      using congrArg (coeff n) hb
  have hp := h false h₀
  have hm := h true h₁
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul] at hp hm
  have hy : (coeff n x).coeff g = 0 := by
    have he : (2 : ℤ_[2]) * (coeff n x).coeff g = 0 := by
      linear_combination hp - hm
    exact (mul_eq_zero.mp he).resolve_left (by norm_num)
  have hx : (coeff n x).coeff 1 = 0 := by simpa [hy] using hp
  rcases casesG u with rfl | rfl <;> simp [hx, hy]

private def sep (b : Bool) : R :=
  C (MonoidAlgebra.single 1 1 + if b then -MonoidAlgebra.single g 1 else MonoidAlgebra.single g 1)

private theorem sign_sep (b c : Bool) :
    sign c (sep b) = if c = b then (2 : A) else 0 := by
  unfold sign sep
  rw [PowerSeries.map_C]
  change C (signB c (MonoidAlgebra.single 1 1 +
    if b then -(MonoidAlgebra.single g 1) else MonoidAlgebra.single g 1)) = _
  cases b <;> cases c <;>
    simp [signB, MonoidAlgebra.lift_single, signG, Ne.symm g_ne, one_add_one_eq_two] <;>
    exact map_natCast (C (R := ℤ_[2])) 2

private theorem two_ne_zero_A : (2 : A) ≠ 0 := by
  intro h
  have hc : (constantCoeff : A →+* ℤ_[2]) 2 = 2 := map_natCast _ 2
  have hh := congrArg (constantCoeff : A →+* ℤ_[2]) h
  rw [hc, map_zero] at hh
  exact two_ne_zero hh

private def signPrime (b : Bool) : Ideal R :=
  RingHom.ker ((constantCoeff : A →+* ℤ_[2]).comp (sign b))

private instance (b : Bool) : (signPrime b).IsPrime := RingHom.ker_isPrime _

private theorem two_not_mem_signPrime (b : Bool) : (2 : R) ∉ signPrime b := by
  intro h
  let f := (constantCoeff : A →+* ℤ_[2]).comp (sign b)
  have h' : f 2 = 0 := h
  have hd : f 2 = 2 := map_natCast f 2
  exact two_ne_zero (hd.symm.trans h')

private theorem sep_not_mem_signPrime (b : Bool) : sep b ∉ signPrime b := by
  change constantCoeff (sign b (sep b)) ≠ (0 : ℤ_[2])
  rw [sign_sep, ite_eq_left rfl]
  have hc : (constantCoeff : A →+* ℤ_[2]) 2 = 2 := map_natCast _ 2
  rw [hc]
  exact two_ne_zero

private instance : IsNoetherianRing B :=
  IsNoetherianRing.of_finite ℤ_[2] B

private theorem signPrime_height (b : Bool) : (signPrime b).height = 1 := by
  let Xideal : Ideal R := Ideal.span {X}
  have hX : (X : R) ∈ signPrime b := by
    change constantCoeff (sign b X) = (0 : ℤ_[2])
    simp [sign]
  have hmin : signPrime b ∈ Xideal.minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hX⟩, ?_⟩
    intro I hI hle
    have hIX : (X : R) ∈ I := hI.2 (Ideal.subset_span (Set.mem_singleton _))
    have hsep : sep b ∉ I := fun hx => sep_not_mem_signPrime b (hle hx)
    have hker : RingHom.ker (sign b) ≤ I := by
      intro x hx
      have hmul : x * sep b = 0 := by
        apply sign_joint_zero <;> rw [map_mul, sign_sep] <;> cases b <;> simp_all [RingHom.mem_ker]
      exact (hI.1.mem_or_mem (hmul ▸ I.zero_mem)).resolve_right hsep
    intro x hx
    change constantCoeff (sign b x) = (0 : ℤ_[2]) at hx
    obtain ⟨t, ht⟩ := X_dvd_iff.mpr hx
    obtain ⟨s, hs⟩ := sign_surj b t
    have he : x - X * s ∈ RingHom.ker (sign b) := by
      change sign b (x - X * s) = 0
      rw [map_sub, map_mul, hs, show sign b X = X by simp [sign], ht, sub_self]
    simpa using I.add_mem (hker he) (I.mul_mem_right s hIX)
  have htop := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes Xideal _ hmin
  have hbot : 1 ≤ (signPrime b).height :=
    (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (show (X : R) ∈ nonZeroDivisors R from by
        rw [mem_nonZeroDivisors_iff_right]
        intro x hx
        apply sign_joint_zero
        · have h := congrArg (sign false) hx
          simp [sign, X_ne_zero] at h
          exact h
        · have h := congrArg (sign true) hx
          simp [sign, X_ne_zero] at h
          exact h)).trans (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem _).mpr hX))
  exact htop.antisymm hbot

private theorem sign_regular {x : R} (h₀ : sign false x ≠ 0) (h₁ : sign true x ≠ 0) :
    x ∈ nonZeroDivisors R := by
  rw [mem_nonZeroDivisors_iff_left]
  intro y h
  apply sign_joint_zero
  · exact (mul_eq_zero.mp (by simpa using congrArg (sign false) h)).resolve_left h₀
  · exact (mul_eq_zero.mp (by simpa using congrArg (sign true) h)).resolve_left h₁

set_option maxHeartbeats 800000 in
private theorem annihilate_at_sign {M : Type} [AddCommGroup M] [Module R M]
    (b : Bool) (m : M)
    (h : Module.IsTorsion (Localization.AtPrime (signPrime b))
      (LocalizedModule (signPrime b).primeCompl M)) :
    ∃ a : R, sign b a ≠ 0 ∧ a • m = 0 := by
  let p := signPrime b
  let S := Localization.AtPrime p
  let i := algebraMap R S
  let j := LocalizedModule.mkLinearMap p.primeCompl M
  obtain ⟨r, hr⟩ := h (x := j m)
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj p.primeCompl (r : S)
  change (r : S) * i s = i a at hs
  have ha : i a ∈ nonZeroDivisors S := by
    rw [← hs]
    exact mul_mem r.property (IsUnit.mem_nonZeroDivisors (IsLocalization.map_units S s))
  have hsep : i (sep b) ≠ 0 := by
    intro he
    have hh := (IsLocalization.eq_iff_exists p.primeCompl S).mp
      (show i (sep b) = i 0 from by simpa using he)
    obtain ⟨t, ht⟩ := hh
    have ht' := congrArg (sign b) ht
    have hn : sign b t ≠ 0 := by
      intro hz
      exact t.property (show constantCoeff (sign b t) = (0 : ℤ_[2]) by simp [hz])
    simp [sign_sep, hn, two_ne_zero_A] at ht'
  have han : sign b a ≠ 0 := by
    intro h
    have haz : a * sep b = 0 := by
      apply sign_joint_zero <;> rw [map_mul, sign_sep] <;> cases b <;> simp_all
    have he : i a * i (sep b) = 0 := by simpa [map_mul] using congrArg i haz
    exact hsep ((mem_nonZeroDivisors_iff_left.mp ha) _ he)
  have hm : i a • j m = 0 := by
    rw [← hs, mul_comm, mul_smul]
    change i (s : R) • ((r : S) • j m) = 0
    rw [show (r : S) • j m = 0 from hr, smul_zero]
  have hj : j (a • m) = 0 := by
    rw [map_smul, ← IsScalarTower.algebraMap_smul S]
    exact hm
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl j).mp hj
  have htn : sign b t ≠ 0 := by
    intro hz
    exact t.property (show constantCoeff (sign b t) = (0 : ℤ_[2]) by simp [hz])
  exact ⟨(t : R) * a, by simp [htn, han], by rw [mul_smul]; exact ht⟩

/-- Torsion at the tested primes detects torsion over the dyadic Iwasawa
ring. It suffices to test the two sign primes cut out by the series variable. -/
theorem isTorsion_of_kodaiLocal {M : Type} [AddCommGroup M] [Module R M]
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → (2 : R) ∉ p →
      Module.IsTorsion (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) :
    Module.IsTorsion R M := by
  intro m
  obtain ⟨a, ha, ham⟩ := annihilate_at_sign false m
    (h _ (signPrime_height false) (two_not_mem_signPrime false))
  obtain ⟨b, hb, hbm⟩ := annihilate_at_sign true m
    (h _ (signPrime_height true) (two_not_mem_signPrime true))
  let c := sep false * a + sep true * b
  have hc : c ∈ nonZeroDivisors R := by
    apply sign_regular <;> simp [c, sign_sep, ha, hb, two_ne_zero_A]
  exact ⟨⟨c, hc⟩, by simp [Submonoid.smul_def, c, add_smul, mul_smul, ham, hbm]⟩

/-- Finite generation upgrades primewise torsion to a single regular
annihilator of the entire module. -/
theorem exists_regular_annihilator_of_kodaiLocal {M : Type} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → (2 : R) ∉ p →
      Module.IsTorsion (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) :
    ∃ a : nonZeroDivisors R, ∀ x : M, a • x = 0 := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  choose a ha using fun x : M => isTorsion_of_kodaiLocal h (x := x)
  refine ⟨∏ x ∈ s, a x, ?_⟩
  intro x
  have hx : x ∈ Submodule.span R (↑s : Set M) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.mul_prod_erase s a hy, mul_comm, mul_smul, ha, smul_zero]
  | zero => exact smul_zero _
  | add _ _ _ _ hx hy => rw [smul_add, hx, hy, add_zero]
  | smul r _ _ hh => rw [smul_comm, hh, smul_zero]

end ZInQ.Manuscript.RC.KatoP2.Checked
