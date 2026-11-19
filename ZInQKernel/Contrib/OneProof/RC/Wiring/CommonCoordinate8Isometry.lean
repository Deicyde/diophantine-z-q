import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate8Centre

/-!
# Theorem 5.3, Lane RC32 round 5: the valuation ring of `w ∘ ι` is `ℤ̄_P`

For a valuation `w` of `ℚ̄_r` extending `v_r` and a `ℚ`-embedding `ι : ℚ̄ → ℚ̄_r`, the centre
`P = centre w ι = {x ∈ ℤ̄ : w(ι x) < 1}` is a prime of `ℤ̄` over `r` (`centre_isPrime`,
`centre_under`). This file identifies the valuation ring of the valuation `w ∘ ι` of `ℚ̄` with the
localization `ℤ̄_P`, and deduces that the decomposition group of `P` acts on `ℚ̄` by isometries of
`w ∘ ι` (up to equivalence of valuations). Classical references: Neukirch, *Algebraic Number
Theory*, I.11 (localizations of Dedekind domains are discrete valuation rings) and II.8–9.

* `exists_mul_eq_or_mul_eq_of_isDedekindDomain`: for a nonzero prime `p` of a Dedekind domain `O`
  with fraction field `K`, every `x ∈ K` satisfies `x s = a` or `x a = s` with `a, s ∈ O`,
  `s ∉ p` (`O_p` is a discrete valuation ring, hence a valuation ring);
* `le_one_iff_exists_frac`: `w(ι z) ≤ 1` iff `z = a/s` with `a, s ∈ ℤ̄` and `s ∉ P` (pass to the
  number field `ℚ(z)`, its ring of integers `O` and the nonzero prime `P ∩ O`);
* `le_one_iff_of_smul_eq`: if `g ∈ G_ℚ` fixes `P`, then `w(ι(g z)) ≤ 1 ↔ w(ι z) ≤ 1`;
* `isEquiv_comap_of_smul_eq`, `le_iff_of_smul_eq`, `lt_iff_of_smul_eq`,
  `le_ratCast_iff_of_smul_eq`: if `g • P = P`, the valuations `w ∘ ι ∘ g` and `w ∘ ι` of `ℚ̄` are
  equivalent; in particular `w(ι(g z)) ≤ w(ι q) ↔ w(ι z) ≤ w(ι q)` for every `q ∈ ℚ`.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.PrintsArith (GalQ Qbar)
open ZInQ.Manuscript.RC.AddressGenuine (Zbar coe_smul_Zbar)
open scoped Pointwise

/-! ## Localizations of Dedekind domains are valuation rings -/

/-- **Localizations of Dedekind domains at nonzero primes are valuation rings** (PROVED): for a
nonzero prime `p` of a Dedekind domain `O` with fraction field `K`, every `x ∈ K` satisfies
`x s = a` or `x a = s` for some `a, s ∈ O` with `s ∉ p` (`O_p` is a discrete valuation ring). -/
theorem exists_mul_eq_or_mul_eq_of_isDedekindDomain {O K : Type*} [CommRing O]
    [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] {p : Ideal O} [p.IsPrime]
    (hp : p ≠ ⊥) (x : K) :
    ∃ a s : O, s ∉ p ∧
      (x * algebraMap O K s = algebraMap O K a ∨ x * algebraMap O K a = algebraMap O K s) := by
  have hS : p.primeCompl ≤ nonZeroDivisors O := p.primeCompl_le_nonZeroDivisors
  have hmem : ∀ y ∈ Localization.subalgebra.ofField K p.primeCompl hS,
      ∃ a s : O, s ∉ p ∧ y * algebraMap O K s = algebraMap O K a := by
    rintro y ⟨a, s, hs, rfl⟩
    refine ⟨a, s, hs, ?_⟩
    have : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hS hs)
    exact inv_mul_cancel_right₀ this _
  have : IsDiscreteValuationRing (Localization.subalgebra.ofField K p.primeCompl hS) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hp _
  rcases ValuationRing.isInteger_or_isInteger (Localization.subalgebra.ofField K p.primeCompl hS)
    x with ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨a, s, hs, h⟩ := hmem y y.2
    refine ⟨a, s, hs, Or.inl ?_⟩
    rw [← hy]
    exact h
  · obtain ⟨a, s, hs, h⟩ := hmem y y.2
    by_cases hx : x = 0
    · refine ⟨0, 1, (Ideal.ne_top_iff_one p).mp (Ideal.IsPrime.ne_top ‹_›), Or.inl ?_⟩
      simp [hx]
    · refine ⟨a, s, hs, Or.inr ?_⟩
      rw [← h]
      change x * (algebraMap _ K y * _) = _
      rw [hy, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]

/-! ## The valuation ring of `w ∘ ι` is the localization of `ℤ̄` at the centre -/

section Isometry

variable {r : ℕ} {hr : r.Prime}

/-- An element of `ℤ̄` outside the centre has `w(ι s) = 1` (PROVED). -/
theorem eq_one_of_notMem_centre {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) {s : Zbar}
    (hs : s ∉ centre hw ι) : w (ι s) = 1 :=
  le_antisymm (le_one_of_mem_Zbar hw ι s) (not_lt.mp hs)

/-- **The valuation ring of `w ∘ ι`, inside a number field** (PROVED): if `z` lies in a number
field `K ⊂ ℚ̄` and `w(ι z) ≤ 1`, then `z = a/s` with `a, s ∈ ℤ̄` and `s` outside the centre. The
prime `p = P ∩ 𝓞_K` of `𝓞_K` is nonzero (it contains `r`), so `z s = a` or `z a = s` with
`a, s ∈ 𝓞_K`, `s ∉ p`; in the second case `a ∉ p`, since otherwise `w(ι z) w(ι a) < 1 = w(ι s)`. -/
theorem exists_frac_of_mem_of_le_one {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr)
    (K : IntermediateField ℚ Qbar) [FiniteDimensional ℚ K] {z : Qbar} (hzK : z ∈ K)
    (hz : w (ι z) ≤ 1) : ∃ a s : Zbar, s ∉ centre hw ι ∧ z * (s : Qbar) = (a : Qbar) := by
  have : NumberField K := NumberField.of_module_finite ℚ K
  let φ : 𝓞 K →+* Zbar :=
    (algebraMap (𝓞 K) Qbar).codRestrict (integralClosure ℤ Qbar) fun a => by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) K Qbar]
      exact (RingOfIntegers.isIntegral_coe a).algebraMap
  have hφ : ∀ a : 𝓞 K, ((φ a : Zbar) : Qbar) = algebraMap K Qbar (algebraMap (𝓞 K) K a) :=
    fun a => IsScalarTower.algebraMap_apply (𝓞 K) K Qbar a
  let p : Ideal (𝓞 K) := (centre hw ι).comap φ
  have hp : p ≠ ⊥ := by
    intro hbot
    have hr' : ((r : ℤ) : 𝓞 K) ∈ p := by
      show φ _ ∈ centre hw ι
      rw [map_intCast]
      have : (r : ℤ) ∈ (centre hw ι).under ℤ := by
        rw [centre_under]
        exact Ideal.mem_span_singleton_self _
      rw [Ideal.under_def, Ideal.mem_comap, eq_intCast] at this
      exact this
    rw [hbot, Ideal.mem_bot] at hr'
    exact hr.ne_zero (by exact_mod_cast hr')
  have hmap : ∀ a s : 𝓞 K, (⟨z, hzK⟩ : K) * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K a →
      z * ((φ s : Zbar) : Qbar) = ((φ a : Zbar) : Qbar) := by
    intro a s h
    have := congrArg (algebraMap K Qbar) h
    rw [map_mul] at this
    rw [hφ, hφ]
    exact this
  obtain ⟨a, s, hs, h | h⟩ := exists_mul_eq_or_mul_eq_of_isDedekindDomain hp (⟨z, hzK⟩ : K)
  · exact ⟨φ a, φ s, hs, hmap a s h⟩
  · have h' := hmap s a h
    by_cases ha : φ a ∈ centre hw ι
    · exfalso
      have h1 : w (ι (φ s : Qbar)) = 1 := eq_one_of_notMem_centre hw ι hs
      have h2 : w (ι (φ a : Qbar)) < 1 := ha
      rw [← h', map_mul, map_mul] at h1
      have h3 : w (ι z) * w (ι (φ a : Qbar)) ≤ w (ι (φ a : Qbar)) := mul_le_of_le_one_left' hz
      rw [h1] at h3
      exact absurd h3 (not_le.mpr h2)
    · exact ⟨φ s, φ a, ha, h'⟩

/-- **The valuation ring of `w ∘ ι` is the localization `ℤ̄_P` at the centre `P`** (PROVED):
`w(ι z) ≤ 1` iff `z = a/s` with `a, s ∈ ℤ̄` and `s ∉ P`. -/
theorem le_one_iff_exists_frac {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (z : Qbar) :
    w (ι z) ≤ 1 ↔ ∃ a s : Zbar, s ∉ centre hw ι ∧ z * (s : Qbar) = (a : Qbar) := by
  constructor
  · intro hz
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {z}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral z)
    exact exists_frac_of_mem_of_le_one hw ι _ (IntermediateField.mem_adjoin_simple_self ℚ z) hz
  · rintro ⟨a, s, hs, h⟩
    have h1 := eq_one_of_notMem_centre hw ι hs
    have h2 := le_one_of_mem_Zbar hw ι a
    rw [← h, map_mul, map_mul, h1, mul_one] at h2
    exact h2

/-! ## The decomposition group of the centre acts by isometries -/

/-- An element of `G_ℚ` fixing the centre `P` preserves membership in `P` (PROVED). -/
theorem smul_mem_centre_iff_of_smul_eq {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hg : g • centre hw ι = centre hw ι) (x : Zbar) :
    g • x ∈ centre hw ι ↔ x ∈ centre hw ι := by
  conv_lhs => rw [← hg]
  exact Ideal.smul_mem_pointwise_smul_iff

/-- An element of `G_ℚ` preserving membership in the centre maps the valuation ring of `w ∘ ι`
into itself (PROVED, from `le_one_iff_exists_frac`). -/
theorem le_one_of_le_one_of_smul_mem_iff {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hg : ∀ x : Zbar, g • x ∈ centre hw ι ↔ x ∈ centre hw ι) {z : Qbar} (hz : w (ι z) ≤ 1) :
    w (ι (g z)) ≤ 1 := by
  obtain ⟨a, s, hs, hzs⟩ := (le_one_iff_exists_frac hw ι z).mp hz
  refine (le_one_iff_exists_frac hw ι (g z)).mpr ⟨g • a, g • s, ?_, ?_⟩
  · rw [hg]
    exact hs
  · rw [coe_smul_Zbar, coe_smul_Zbar, ← map_mul, hzs]

/-- **The decomposition group of the centre preserves the valuation ring of `w ∘ ι`** (PROVED):
if `g ∈ G_ℚ` satisfies `g • P = P`, then `w(ι(g z)) ≤ 1 ↔ w(ι z) ≤ 1`. -/
theorem le_one_iff_of_smul_eq {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hg : g • centre hw ι = centre hw ι) (z : Qbar) :
    w (ι (g z)) ≤ 1 ↔ w (ι z) ≤ 1 := by
  have h1 := smul_mem_centre_iff_of_smul_eq hw ι g hg
  have h2 : ∀ x : Zbar, g⁻¹ • x ∈ centre hw ι ↔ x ∈ centre hw ι := fun x => by
    rw [← h1, smul_inv_smul]
  refine ⟨fun h => ?_, le_one_of_le_one_of_smul_mem_iff hw ι g h1⟩
  have h' := le_one_of_le_one_of_smul_mem_iff hw ι g⁻¹ h2 h
  have hz : (g⁻¹ : GalQ) (g z) = z := by
    rw [← AlgEquiv.smul_def, ← AlgEquiv.smul_def, inv_smul_smul]
  rw [hz] at h'
  exact h'

/-- **The decomposition group of the centre acts by isometries of `w ∘ ι`, up to equivalence**
(PROVED): if `g • P = P`, the valuations `w ∘ ι ∘ g` and `w ∘ ι` of `ℚ̄` are equivalent. -/
theorem isEquiv_comap_of_smul_eq {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hg : g • centre hw ι = centre hw ι) :
    (w.comap (ι.comp (g : Qbar →ₐ[ℚ] Qbar)).toRingHom).IsEquiv (w.comap ι.toRingHom) :=
  Valuation.isEquiv_of_val_le_one fun z => le_one_iff_of_smul_eq hw ι g hg z

/-- If `g • P = P`, then `w(ι(g x)) ≤ w(ι(g y)) ↔ w(ι x) ≤ w(ι y)` (PROVED). -/
theorem le_iff_of_smul_eq {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hg : g • centre hw ι = centre hw ι) (x y : Qbar) :
    w (ι (g x)) ≤ w (ι (g y)) ↔ w (ι x) ≤ w (ι y) :=
  isEquiv_comap_of_smul_eq hw ι g hg x y

/-- If `g • P = P`, then `w(ι(g x)) < w(ι(g y)) ↔ w(ι x) < w(ι y)` (PROVED). -/
theorem lt_iff_of_smul_eq {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hg : g • centre hw ι = centre hw ι) (x y : Qbar) :
    w (ι (g x)) < w (ι (g y)) ↔ w (ι x) < w (ι y) :=
  (isEquiv_comap_of_smul_eq hw ι g hg).lt_iff_lt (x := x) (y := y)

/-- **Comparison with rational numbers** (PROVED): if `g • P = P`, then
`w(ι(g z)) ≤ w(ι q) ↔ w(ι z) ≤ w(ι q)` for every `q ∈ ℚ` (`g` fixes `q`). -/
theorem le_ratCast_iff_of_smul_eq {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {w : Valuation (Qrbar r hr) Γ} (hw : ExtendsVr w) (ι : Qbar →ₐ[ℚ] Qrbar r hr) (g : GalQ)
    (hg : g • centre hw ι = centre hw ι) (z : Qbar) (q : ℚ) :
    w (ι (g z)) ≤ w (ι (q : Qbar)) ↔ w (ι z) ≤ w (ι (q : Qbar)) := by
  have h := le_iff_of_smul_eq hw ι g hg z (q : Qbar)
  have hq : g (q : Qbar) = q := map_ratCast g q
  rw [hq] at h
  exact h

end Isometry

end ZInQ.Manuscript.RC.Wiring
