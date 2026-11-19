import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate5Universal

/-!
# Theorem 5.3, Lane RC32 round 2: the residue of `e_q`, the text's unit argument

Lemma `ex:arith-common-coordinate`, tex 4196–4206: "Modulo `(2, I_G)` every group element and fixed
quadratic sign becomes one, while `a_q` is even. Thus `ē_q = t²/(1+t)` …, a unit; so `e_q` is a
unit of `𝒪[G]`."

* `resG`: the reduction `𝒪[G] → 𝒪[G]/(2, I_G) = 𝒪/2 = (ℤ/2)((t))` (the augmentation, then lane
  RC7's reduction `proj 1` modulo `2`);
* `aug_eU`: the augmentation of `e_q` is `e_q` at the trivial character (all signs one);
* `resG_eU_mul`: **`ē_q (1 + t) = t²`**, i.e. `ē_q = t²/(1+t)`, at every prime `q ∤ 6ℓ` (the
  text's computation; `a_q` even is `apE_even`);
* `isUnit_eU_text`: `e_q` is a unit of `𝒪[G]` by the text's route: `ē_q ≠ 0`, so `aug(e_q) ∉ (2)`,
  the maximal ideal of the discrete valuation ring `𝒪`, and units of `𝒪[G]` are detected by the
  augmentation. This replaces round one's proof-only DEPARTURE (`isUnit_eU`, through the `t²`
  coefficient) at the good primes, where the text argues.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Uniform
open ZInQ.Manuscript.RC.Determinant (OO lamToO SignGroup signGroup_mul_self)

/-- **The reduction modulo `(2, I_G)`** (definition; tex 4199–4200): `𝒪[G] → 𝒪 → 𝒪/2 = (ℤ/2)((t))`,
the augmentation followed by the reduction modulo `2`. -/
def resG (b : ℕ) : OG b →+* LaurentSeries (ZMod (2 ^ 1)) :=
  (Determinant.proj 1).comp (Determinant.aug : OG b →ₐ[OO] OO).toRingHom

/-- On `Λ`, the reduction is the reduction of the coefficients modulo `2` (PROVED). -/
theorem resG_lamToOG (b : ℕ) (f : Lambda) :
    resG b (lamToOG b f) = HahnSeries.ofPowerSeries ℤ _ (PowerSeries.map (PadicInt.toZModPow 1) f) := by
  have h : Determinant.aug (lamToOG b f) = lamToO f := by
    change Determinant.aug (algebraMap OO (OG b) (lamToO f)) = lamToO f
    rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  change Determinant.proj 1 (Determinant.aug (lamToOG b f)) = _
  rw [h]
  rfl

/-- **The augmentation of `e_q`** is the point factor at the trivial character (PROVED). -/
theorem aug_eU (ℓ : ℕ) (Fam : Family) (q : ℕ) (c : ZMod 2) :
    Determinant.aug (eU ℓ Fam q c) = lamToO (ptFac ℓ Fam 0 q) := by
  rw [eU, ptFac, pointFactor, pointFactor, map_sub, map_sub, aug_zU, aug_ziU, map_intCast,
    map_sub, map_sub, map_intCast]
  congr 2
  · simp [zAt, frobSign_zero]
  · simp [zAt, frobSign_zero]

/-- **`ē_q = t²/(1+t)`** (tex 4199–4206), as `ē_q (1 + t) = t²` in `(ℤ/2)((t))`, at every prime
`q ∤ 6ℓ` and for either Frobenius lift. PROVED: at the trivial character
`(1 + t) e_q = a_q (1 + t) − (1 + t)² − 1`, and `a_q` is even (`apE_even`). -/
theorem resG_eU_mul (ℓ : ℕ) (Fam : Family) {q : ℕ} (hq : q.Prime) (hgood : ¬ ((q : ℤ) ∣ 6 * ℓ))
    (c : ZMod 2) :
    resG Fam.b (eU ℓ Fam q c) * resG Fam.b (lamToOG Fam.b (1 + PowerSeries.X)) =
      resG Fam.b (lamToOG Fam.b (PowerSeries.X ^ 2)) := by
  obtain ⟨r, hr⟩ := apE_even (ℓ := ℓ) hq hgood
  have hkey : ptFac ℓ Fam 0 q * (1 + PowerSeries.X) =
      PowerSeries.X ^ 2 + 2 ^ 1 * ((r : Lambda) * (1 + PowerSeries.X) - 1 - PowerSeries.X -
        PowerSeries.X ^ 2) := by
    have h := one_add_X_mul_ptFac ℓ Fam 0 q
    rw [frobSign_zero, Units.val_one, Int.cast_one, hr, Int.cast_add] at h
    linear_combination h
  have hres : resG Fam.b (eU ℓ Fam q c) = Determinant.proj 1 (lamToO (ptFac ℓ Fam 0 q)) := by
    change Determinant.proj 1 (Determinant.aug (eU ℓ Fam q c)) = _
    rw [aug_eU]
  have hl : ∀ f : Lambda, resG Fam.b (lamToOG Fam.b f) = Determinant.proj 1 (lamToO f) := fun f => by
    rw [resG_lamToOG]; rfl
  have h2 : lamToO (2 ^ 1 : Lambda) = (2 : OO) ^ 1 := by rw [map_pow, map_ofNat]
  rw [hres, hl, hl, ← map_mul, ← map_mul, hkey, map_add, map_mul, h2, map_add (Determinant.proj 1),
    Determinant.proj_two_pow_mul, add_zero]

/-- **`e_q` is a unit of `𝒪[G]`, by the text's route** (tex 4196–4206): `ē_q (1 + t) = t² ≠ 0` in
`(ℤ/2)((t))`, so the augmentation of `e_q` lies outside the maximal ideal `(2)` of `𝒪`, hence is
a unit, and so is `e_q` (lane RC7's `isUnit_iff_isUnit_aug`). PROVED at every prime `q ∤ 6ℓ`. -/
theorem isUnit_eU_text (ℓ : ℕ) (Fam : Family) {q : ℕ} (hq : q.Prime)
    (hgood : ¬ ((q : ℤ) ∣ 6 * ℓ)) (c : ZMod 2) : IsUnit (eU ℓ Fam q c) := by
  rw [Determinant.isUnit_iff_isUnit_aug Determinant.isUnit_one_add_two_mul_OO signGroup_mul_self]
  have : Fact (1 < 2 ^ 1) := ⟨by norm_num⟩
  have hne : Determinant.proj 1 (Determinant.aug (eU ℓ Fam q c)) ≠ 0 := by
    intro h0
    have h := resG_eU_mul ℓ Fam hq hgood c
    have h' : resG Fam.b (eU ℓ Fam q c) = Determinant.proj 1 (Determinant.aug (eU ℓ Fam q c)) := rfl
    rw [h', h0, zero_mul, resG_lamToOG, map_pow, PowerSeries.map_X,
      HahnSeries.ofPowerSeries_X_pow] at h
    exact HahnSeries.single_ne_zero one_ne_zero h.symm
  by_contra hnu
  have hmem : Determinant.aug (eU ℓ Fam q c) ∈ IsLocalRing.maximalIdeal OO :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  rw [Rings.maximalIdeal_OO] at hmem
  exact hne ((Determinant.proj_eq_zero_iff_mem 1 _).mpr (by rwa [pow_one]))

end ZInQ.Manuscript.RC.Wiring
