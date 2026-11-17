import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Serre

/-!
# Kato's hypothesis (v) for `T₂E ⊗ χ` from Serre's open image theorem

Lane RC9. Kato's Theorem 13.4 (Astérisque 295, p. 226) assumes (v): *there is
`σ ∈ Gal(ℚ̄/ℚ(ζ_{p^∞}))` with `dim_L Ker(1 - σ; T ⊗ L → T ⊗ L) = 1`*. The manuscript verifies it
for `T = T₂E ⊗ χ`, `χ` a quadratic character (App. E ¶7, tex 7228–7231; also tex 1887–1889):
"The image over `ℚ(μ_{2^∞})` contains an open subgroup of `SL₂(ℤ₂)`. Intersecting with `ker χ`
keeps an open subgroup, which contains a nonidentity unipotent. It fixes a one-dimensional subspace
and gives condition (v)."

`kato_hyp_v` PROVES this from `SerreThm3` (PRINT) and the GLUE `DetTateTwoCyclotomic`: in a
`ℤ₂`-basis `b₀, b₁` of `T₂E`, the unipotent `α = 1 + 2^d N` (`N b₀ = 0`, `N b₁ = b₀`) lies in
`Γ_d`, so `α = ρ₂(τ)` with `τ` fixing the `2`-power roots of unity (`serre_SL2_part`); then
`σ = τ²` lies in the kernel of every quadratic character, still fixes `μ_{2^∞}`, and
`ρ₂(σ) = 1 + 2^{d+1} N`, whose fixed module is `ℤ₂ b₀`, of rank one. On `T ⊗ χ` the element `σ`
acts as `ρ₂(σ)` because `χ(σ) = 1`; and the rank over `ℤ₂` of the fixed module in `T` is the
dimension over `ℚ₂` of the fixed space in `T ⊗ ℚ₂` (kernels commute with the flat base change
`⊗ ℚ₂`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsArith

open scoped WeierstrassCurve

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- `2 ≠ 0` in `ℚ̄`. -/
theorem two_ne_zero_qbar : ((2 : ℕ) : Qbar) ≠ 0 := by
  exact_mod_cast (two_ne_zero : (2 : Qbar) ≠ 0)

/-- `T₂E` is a free `ℤ₂`-module (vendored Tau Ceti `WeierstrassCurve.free_tateModule`). -/
instance tateMod_two_free : Module.Free ℤ_[2] (TateMod E 2) :=
  (E⁄Qbar).free_tateModule two_ne_zero_qbar

/-- `T₂E` is a finitely generated `ℤ₂`-module. -/
instance tateMod_two_finite : Module.Finite ℤ_[2] (TateMod E 2) :=
  (E⁄Qbar).finite_tateModule two_ne_zero_qbar

/-- `T₂E` has rank two over `ℤ₂` (vendored Tau Ceti `WeierstrassCurve.finrank_tateModule`). -/
theorem tateMod_two_finrank : Module.finrank ℤ_[2] (TateMod E 2) = 2 :=
  (E⁄Qbar).finrank_tateModule two_ne_zero_qbar

/-- A `ℤ₂`-basis `b₀, b₁` of `T₂E`. -/
def tateBasis : Module.Basis (Fin 2) ℤ_[2] (TateMod E 2) :=
  Module.finBasisOfFinrankEq ℤ_[2] (TateMod E 2) (tateMod_two_finrank E)

/-- The nilpotent `N`: `N x = (b₁-coordinate of x) • b₀`, so `N b₀ = 0`, `N b₁ = b₀`, `N² = 0`. -/
def nilN : Module.End ℤ_[2] (TateMod E 2) :=
  ((tateBasis E).coord 1).smulRight ((tateBasis E) 0)

theorem nilN_apply (x : TateMod E 2) : nilN E x = (tateBasis E).coord 1 x • (tateBasis E) 0 :=
  rfl

theorem coord_one_basis_zero : (tateBasis E).coord 1 ((tateBasis E) 0) = 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp

theorem nilN_mul_self : nilN E * nilN E = 0 := by
  ext x
  simp only [Module.End.mul_apply, nilN_apply, map_smul, coord_one_basis_zero, smul_zero,
    zero_smul, LinearMap.zero_apply]

/-- `(1 + c N)(1 - c N) = 1`. -/
theorem one_add_smul_nilN_mul (c : ℤ_[2]) :
    (1 + c • nilN E) * (1 - c • nilN E) = 1 := by
  have h : (c • nilN E) * (c • nilN E) = 0 := by
    rw [smul_mul_smul_comm, nilN_mul_self, smul_zero]
  rw [mul_sub, mul_one, add_mul, one_mul, h, add_zero, add_sub_cancel_right]

theorem one_sub_smul_nilN_mul (c : ℤ_[2]) :
    (1 - c • nilN E) * (1 + c • nilN E) = 1 := by
  have h := one_add_smul_nilN_mul E (-c)
  simpa [sub_eq_add_neg, neg_smul] using h

/-- The unipotent automorphism `1 + c N`. -/
def unip (c : ℤ_[2]) : TateMod E 2 ≃ₗ[ℤ_[2]] TateMod E 2 :=
  LinearEquiv.ofLinearMap (1 + c • nilN E) (1 - c • nilN E)
    (by rw [← Module.End.mul_eq_comp, one_add_smul_nilN_mul]; rfl)
    (by rw [← Module.End.mul_eq_comp, one_sub_smul_nilN_mul]; rfl)

theorem unip_apply (c : ℤ_[2]) (x : TateMod E 2) : unip E c x = x + c • nilN E x := rfl

/-- `det(1 + c N) = 1`: its matrix in the basis `b₀, b₁` is `!![1, c; 0, 1]`. -/
theorem det_unip (c : ℤ_[2]) : LinearMap.det (unip E c).toLinearMap = 1 := by
  rw [← LinearMap.det_toMatrix (tateBasis E), Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, LinearEquiv.coe_coe, unip_apply, nilN_apply, map_add,
    map_smul, Module.Basis.repr_self, Module.Basis.coord_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.single_apply]
  simp

/-- The fixed module of `1 + c N`, `c ≠ 0`, is `ℤ₂ b₀`. -/
theorem ker_unip_sub_one {c : ℤ_[2]} (hc : c ≠ 0) :
    LinearMap.ker ((unip E c).toLinearMap - 1) = Submodule.span ℤ_[2] {(tateBasis E) 0} := by
  have hb0 : (tateBasis E) 0 ≠ 0 := (tateBasis E).ne_zero 0
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, unip_apply, Module.End.one_apply,
    add_sub_cancel_left, nilN_apply, smul_smul]
  constructor
  · intro h
    have h1 : c * (tateBasis E).coord 1 x = 0 :=
      (smul_eq_zero.mp h).resolve_right hb0
    have h2 : (tateBasis E).coord 1 x = 0 := (mul_eq_zero.mp h1).resolve_left hc
    refine ⟨(tateBasis E).coord 0 x, ?_⟩
    have hsum := (tateBasis E).sum_repr x
    rw [Fin.sum_univ_two] at hsum
    rw [Module.Basis.coord_apply] at h2
    rw [h2, zero_smul, add_zero] at hsum
    rw [Module.Basis.coord_apply]
    exact hsum
  · rintro ⟨r, rfl⟩
    rw [map_smul, coord_one_basis_zero, smul_zero, mul_zero, zero_smul]

/-- The rank-one fixed module. -/
theorem finrank_span_basis_zero :
    Module.finrank ℤ_[2] (Submodule.span ℤ_[2] {(tateBasis E) 0}) = 1 := by
  have hli : LinearIndependent ℤ_[2] (fun _ : Fin 1 => (tateBasis E) 0) :=
    (tateBasis E).linearIndependent.comp (fun _ : Fin 1 => (0 : Fin 2))
      (fun i j _ => Subsingleton.elim i j)
  have h := finrank_span_eq_card hli
  rw [Fintype.card_fin] at h
  have hr : Set.range (fun _ : Fin 1 => (tateBasis E) 0) = {(tateBasis E) 0} :=
    Set.range_const
  rw [hr] at h
  exact h

/-- `(1 + c N)² = 1 + 2c N`. -/
theorem unip_mul_unip (c : ℤ_[2]) :
    (unip E c).toLinearMap * (unip E c).toLinearMap = (unip E (2 * c)).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe, unip_apply, map_add, map_smul,
    nilN_apply, coord_one_basis_zero, smul_zero, add_zero, zero_smul]
  rw [add_assoc, ← add_smul, two_mul]

/-- **Kato's hypothesis (v) of Theorem 13.4 for `T₂E ⊗ χ`** (PROVED from `SerreThm3` and the GLUE
`DetTateTwoCyclotomic`; tex 7228–7231, 1887–1889): for non-CM `E/ℚ` and every quadratic character
`χ : G_ℚ → {±1}` there is `σ ∈ G_{ℚ(μ_{2^∞})}` with `χ(σ) = 1` whose fixed module in `T₂E` has rank
exactly one. -/
theorem kato_hyp_v (hS : SerreThm3) (hE : HasNoCM E) (hdet : DetTateTwoCyclotomic E)
    (χ : GalQ →* ℤˣ) :
    ∃ σ : GalQ, (∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ) ∧ χ σ = 1 ∧
      Module.finrank ℤ_[2] (LinearMap.ker (tateRep E 2 σ - 1)) = 1 := by
  obtain ⟨d, -, h⟩ := serre_SL2_part hS E hE hdet
  set c : ℤ_[2] := (2 : ℤ_[2]) ^ d with hc
  have hc0 : c ≠ 0 := pow_ne_zero _ two_ne_zero
  obtain ⟨τ, hτμ, hτ⟩ := h (unip E c) (det_unip E c) fun x => ⟨nilN E x, unip_apply E c x⟩
  refine ⟨τ * τ, fun k ζ hζ => ?_, ?_, ?_⟩
  · show τ (τ ζ) = ζ
    rw [hτμ k ζ hζ, hτμ k ζ hζ]
  · rw [map_mul]
    exact Int.units_mul_self (χ τ)
  · have hρ : tateRep E 2 (τ * τ) = (unip E (2 * c)).toLinearMap := by
      rw [map_mul, hτ, unip_mul_unip]
    rw [hρ, ker_unip_sub_one E (mul_ne_zero two_ne_zero hc0), finrank_span_basis_zero]

end ZInQ.Manuscript.RC.PrintsArith
