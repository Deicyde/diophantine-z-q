import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Elliot

/-!
# GenusOdd: Galois descent for the twist (`TwistDescent`), PROVED

The GLUE statement `TwistDescent` of `Glue.lean` is proved here, so it is no longer an input:

1. `Gal(H/K)` and one `ρ` that is not `K`-linear generate `Gal(H/ℚ)` (restriction to the normal
   quadratic subfield `K`, whose automorphism group has order two), so the twisted equivariance
   `g x = ε_s(g) x` holds for every `g ∈ Gal(H/ℚ)`.
2. For `x = (X, Y)`, the coordinates `X` and `Y s` are then fixed by `Gal(H/ℚ)`, hence rational
   (`IsGalois.mem_range_algebraMap_iff_fixed`), and `(d X, d (Y s))` is a rational point of
   `E^{(d)}` (nonsingular, by the variable change `twistVC s` and base change), whose image under
   `ψ_s` is `x`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

section General

variable {K : Type} [Field K] [NumberField K] {H : Type} [Field H] [Algebra K H] [Algebra ℚ H]
  [IsScalarTower ℚ K H]

/-- A `ℚ`-automorphism of `H` trivial on `K` is `K`-linear (general `H`). -/
def toKEquiv' [Normal ℚ K] (g : H ≃ₐ[ℚ] H)
    (hg : g ∈ (AlgEquiv.restrictNormalHom (F := ℚ) K (K₁ := H)).ker) : H ≃ₐ[K] H :=
  AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun k => by
    have h1 := AlgEquiv.restrictNormal_commutes g K k
    have h2 : g.restrictNormal K = 1 := hg
    rw [h2, AlgEquiv.one_apply] at h1
    exact h1.symm

theorem restrictScalars_mem_ker' [Normal ℚ K] (σ : H ≃ₐ[K] H) :
    σ.restrictScalars ℚ ∈ (AlgEquiv.restrictNormalHom (F := ℚ) K (K₁ := H)).ker := by
  rw [MonoidHom.mem_ker]
  ext k
  apply (algebraMap K H).injective
  rw [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, AlgEquiv.restrictNormal_commutes]
  simp

/-- In a group with two elements, two non-identity elements are equal. -/
theorem eq_of_ne_one_of_card_two {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 2) {a b : G}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite G
  by_contra hab
  have h3 : ({1, a, b} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair hab]
  have := Finset.card_le_univ ({1, a, b} : Finset G)
  rw [h3, Fintype.card_eq_nat_card, hG] at this
  omega

theorem map_mul_algEquiv' (E : WeierstrassCurve ℚ) [DecidableEq H] (g h : H ≃ₐ[ℚ] H)
    (x : (E.baseChange H).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := E.toAffine) (g * h).toAlgHom x =
      WeierstrassCurve.Affine.Point.map (W' := E.toAffine) g.toAlgHom
        (WeierstrassCurve.Affine.Point.map (W' := E.toAffine) h.toAlgHom x) := by
  rw [WeierstrassCurve.Affine.Point.map_map]
  rfl

end General

open WeierstrassCurve in
/-- **Galois descent for the twist** (PROVED): the GLUE `TwistDescent` holds. -/
theorem twistDescent_proof : TwistDescent := by
  intro E _ h₁ h₃ K _ _ hK2 H _ _ _ _ _ _ _ d s hs hsd ρ hnotK x hσ hρ
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK2⟩
  have : CharZero H := charZero_of_injective_algebraMap (algebraMap ℚ H).injective
  set φ := AlgEquiv.restrictNormalHom (F := ℚ) K (K₁ := H)
  -- `ρ` is not in the kernel of the restriction
  have hρK : φ ρ ≠ 1 := fun h1 => hnotK ⟨toKEquiv' ρ h1, fun z => rfl⟩
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 2 := by rw [IsGalois.card_aut_eq_finrank, hK2]
  -- the twisted equivariance on `N = ker φ`
  have hN : ∀ g (hg : g ∈ φ.ker), Affine.Point.map (W' := E.toAffine) g.toAlgHom x =
      sgnAt s g • x := by
    intro g hg
    have := hσ (toKEquiv' g hg)
    have hfg : (toKEquiv' g hg).toAlgHom.restrictScalars ℚ = g.toAlgHom := AlgHom.ext fun z => rfl
    rw [hfg] at this
    rw [this]
    unfold sgnAt
    by_cases h : g s = s
    · rw [if_pos (by exact h), if_pos h, one_smul]
    · rw [if_neg (by exact h), if_neg h, neg_smul, one_smul]
  have hρ' : Affine.Point.map (W' := E.toAffine) ρ.toAlgHom x = sgnAt s ρ • x := by
    rw [hρ]
    unfold sgnAt
    split_ifs <;> simp
  -- every `g`
  have hall : ∀ g : H ≃ₐ[ℚ] H, Affine.Point.map (W' := E.toAffine) g.toAlgHom x = sgnAt s g • x := by
    intro g
    by_cases hg : g ∈ φ.ker
    · exact hN g hg
    · have hφg : φ g ≠ 1 := hg
      have heq : φ g = φ ρ := eq_of_ne_one_of_card_two hcard hφg hρK
      have hmem : ρ⁻¹ * g ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
      have hgdec : g = ρ * (ρ⁻¹ * g) := by group
      rw [hgdec, map_mul_algEquiv' E, hN _ hmem, map_zsmul, hρ', smul_smul]
      congr 1
      rw [sgnAt_mul hs hsd ρ (ρ⁻¹ * g)]
      ring
  -- coordinates
  rcases x with _ | ⟨X, Y, hxy⟩
  · exact ⟨0, map_zero _⟩
  have hsne : s ≠ -s := fun h => hs (by
    have : (2 : H) * s = 0 := by linear_combination h
    simpa using this)
  have hfix : ∀ g : H ≃ₐ[ℚ] H, g X = X ∧ g (Y * s) = Y * s := by
    intro g
    have h := hall g
    rw [Affine.Point.map_some] at h
    unfold sgnAt at h
    split_ifs at h with hgs
    · rw [one_smul, Affine.Point.some.injEq] at h
      refine ⟨h.1, ?_⟩
      rw [map_mul, show g Y = Y from h.2, show g s = s from hgs]
    · have hgs' : g s = -s := (apply_eq_or_neg hsd g).resolve_left hgs
      rw [neg_smul, one_smul, Affine.Point.neg_some, Affine.Point.some.injEq] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨h1, ?_⟩
      rw [map_mul, hgs']
      simp only [Affine.negY, baseChange, map, h₁, h₃, map_zero, zero_mul, sub_zero] at h2
      rw [show g Y = -Y from h2]; ring
  obtain ⟨X₀, hX₀⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) X).mpr fun g => (hfix g).1
  obtain ⟨Z₀, hZ₀⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := ℚ) (Y * s)).mpr
    fun g => (hfix g).2
  -- nonsingularity of `(d X₀, d Z₀)` on `E^{(d)}` over `ℚ`
  have heq := twistVC_smul E h₁ h₃ hs hsd
  have key : (E.baseChange H).toAffine.Nonsingular
      (((twistVC s).u : H) ^ 2 * (s ^ 2 * X) + (twistVC s).r)
      (((twistVC s).u : H) ^ 3 * (s ^ 3 * Y) + ((twistVC s).u : H) ^ 2 * (twistVC s).s *
        (s ^ 2 * X) + (twistVC s).t) := by
    have e1 : ((twistVC s).u : H) ^ 2 * (s ^ 2 * X) + (twistVC s).r = X := by
      simp only [twistVC, dif_neg hs, Units.val_mk0]; field_simp; simp
    have e2 : ((twistVC s).u : H) ^ 3 * (s ^ 3 * Y) + ((twistVC s).u : H) ^ 2 * (twistVC s).s *
        (s ^ 2 * X) + (twistVC s).t = Y := by
      simp only [twistVC, dif_neg hs, Units.val_mk0]; field_simp; simp
    rw [e1, e2]; exact hxy
  have hns1 := (Affine.variableChange_nonsingular (E.baseChange H) (twistVC s) _ _).mp key
  rw [heq] at hns1
  have ex : s ^ 2 * X = algebraMap ℚ H (d * X₀) := by rw [map_mul, hX₀, hsd]
  have ey : s ^ 3 * Y = algebraMap ℚ H (d * Z₀) := by
    rw [map_mul, hZ₀, ← hsd]; ring
  rw [ex, ey] at hns1
  have hns : (qtwist E d).toAffine.Nonsingular (d * X₀) (d * Z₀) :=
    (Affine.baseChange_nonsingular (W := (qtwist E d).toAffine) (f := Algebra.ofId ℚ H)
      (algebraMap ℚ H).injective _ _).mp hns1
  refine ⟨.some _ _ hns, ?_⟩
  obtain ⟨h', e⟩ := twistEmb_some E h₁ h₃ d hs hsd hns
  rw [e]
  congr 1
  · rw [← ex]; field_simp
  · rw [← ey]; field_simp

end ZInQ.Contrib.CloudB3RC53.GenusOdd
