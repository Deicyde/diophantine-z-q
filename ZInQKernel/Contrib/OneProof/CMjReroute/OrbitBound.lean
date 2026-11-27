import ZInQKernel.Contrib.OneProof.Y3HodgePrint
import ZInQKernel.Contrib.OneProof.RayClassShimura
import ZInQKernel.Contrib.OneProof.GR512Bridge

/-!
# The orbit bound at a CM point of `Y₃`

Let `Ψ : ℍ^± × (B ⊗ 𝔸_f)^× → Y₃(ℂ)` have fibres the double cosets
`B^× \ (ℍ^± × (B ⊗ 𝔸_f)^× / K₃)` (the fibre clause) and satisfy Shimura's reciprocity law at CM
points (the reciprocity clause); these are the only two clauses of `Y3Hodge.DeligneBodyAtPM` used.
Let `y` be a `ℚ̄`-point with `ιC^* y = Ψ(τ, u)`, `u ∈ 𝒪̂^×`, where `τ` is the CM point of an embedding
`q : K → B` of an imaginary quadratic field `K`; let `R = q⁻¹(𝒪)` and let `H` be the ring class field
of `R`. Assume that every idele `s` of `K` with `q̂(s) ∈ 𝒪̂^×` has trivial Artin symbol on `H`. If `y`
lies in a finite `Gal(ℚ̄/ℚ)`-stable set `S` of `ℚ̄`-points, then `card Pic R ≤ card S`; in particular
`card Pic R ≤ 324` when `card S ≤ 324`.

1. `mem_range_of_mobPM_fix`: the stabiliser of `τ` in `B^×` is `q(K^×)` (an element fixing `τ` has
   `(τ, 1)ᵀ` as an eigenvector, hence commutes with `q(K)`, and the centraliser of a non-central
   element `β` of `B` is `ℚ + ℚβ`, `mem_range_of_comm`).
2. `artin_trivial_of_galPt_fix`: if `σ ∈ Aut ℂ` fixes `ιC^* y` and acts on `K^ab` as `[s, K]`, then
   `[s, K]` is trivial on `H` (reciprocity gives `Ψ(τ, q̂(s)^ε u) = Ψ(τ, u)`; the fibre clause and
   step 1 give `q̂(t⁻¹ s^ε) ∈ u K₃ u⁻¹ ⊆ 𝒪̂^×` for some `t ∈ K^×`, `artin_trivial_of_eq`).
3. `exists_extend_gal`: every element of `Gal(H/K)` is the restriction of some `σ ∈ Aut ℂ`.
4. `card_gal_le_ncard`: `g ↦ σ_g(y)` is injective on `Gal(H/K)`; `card_pic_le_ncard`,
   `card_pic_le_324`: with `[H : K] = card Pic R`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

namespace HDec.CMBranch.CMjReroute

/-! ## 1. The stabiliser of a CM point -/

section Stabiliser

variable {K : Type} [Field K] [NumberField K]

/-- An element of `B^×` fixing a point of `ℍ` has positive reduced norm:
`Im(γz) = nrd(γ) Im(z) / |j(γ, z)|²`. -/
theorem nrd_pos_of_mobPM_fix (gm : LeafQM.B) (hγ : ShimuraGlue.nrdQ ℚ gm ≠ 0)
    (τ : UpperHalfPlane)
    (h : Y3Hodge.mobPM (iotaGL gm hγ) (Y3Hodge.toPM τ) = Y3Hodge.toPM τ) :
    0 < ShimuraGlue.nrdQ ℚ gm := by
  have him := congrArg (fun z : Y3Hodge.HPM => z.1.im) h
  simp only [Y3Hodge.mobPM, Y3Hodge.toPM] at him
  rw [Y3Hodge.im_num_div_denom, Y3Hodge.det_iotaGL] at him
  have h2 : 0 < (τ : ℂ).im := τ.im_pos
  have h3 := Y3Hodge.normSq_denom_pos (iotaGL gm hγ) τ.im_pos.ne'
  by_contra hn
  push Not at hn
  have hn' : (ShimuraGlue.nrdQ ℚ gm : ℝ) ≤ 0 := by exact_mod_cast hn
  have h4 : (ShimuraGlue.nrdQ ℚ gm : ℝ) * (τ : ℂ).im /
      Complex.normSq (UpperHalfPlane.denom (iotaGL gm hγ) τ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hn' h2.le) h3.le
  linarith

/-- At a fixed point `τ` of `γ ∈ B^×`, the vector `(τ, 1)ᵀ` is an eigenvector of `ι(γ)`
(`ι(γ)(τ, 1)ᵀ = j(γ, τ)(γτ, 1)ᵀ`). -/
theorem eig_of_mobPM_fix (gm : LeafQM.B) (hγ : ShimuraGlue.nrdQ ℚ gm ≠ 0) (τ : UpperHalfPlane)
    (h : Y3Hodge.mobPM (iotaGL gm hγ) (Y3Hodge.toPM τ) = Y3Hodge.toPM τ) :
    ∃ lam : ℂ, Matrix.mulVec (iotaC gm) ![(τ : ℂ), 1] = lam • ![(τ : ℂ), 1] := by
  have hpos := nrd_pos_of_mobPM_fix gm hγ τ h
  have hfix : iotaGL gm hpos.ne' • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos (by rw [Y3Hodge.det_iotaGL]; exact_mod_cast hpos)]
    exact congrArg Subtype.val h
  have e := Y3Hodge.iota_mulVec_vτ gm hpos τ
  rw [hfix] at e
  exact ⟨_, e⟩

/-- A quadratic field has an element outside `ℚ`. -/
theorem exists_not_rat (hK : Module.finrank ℚ K = 2) : ∃ θ : K, ∀ r : ℚ, θ ≠ r := by
  by_contra h
  push Not at h
  have h1 := finrank_le_one (R := ℚ) (1 : K) fun w => by
    obtain ⟨r, hr⟩ := h w
    exact ⟨r, by rw [hr, Rat.smul_def, mul_one]⟩
  omega

/-- **The centraliser of `q(θ)`, `θ ∉ ℚ`, in `B = (2, −3 | ℚ)` is `q(K)`.** For pure parts
`x = (x₁, x₂, x₃)` of `γ` and `y` of `q(θ)`, the commutator `[γ, q(θ)]` has coordinates
`6(x₂y₃ − x₃y₂), 4(x₁y₃ − x₃y₁), 2(x₁y₂ − x₂y₁)`; these vanish only if `x = s y`, and then
`γ = q(r + sθ)`. -/
theorem mem_range_of_comm (q : K →ₐ[ℚ] LeafQM.B) {θ : K} (hθ : ∀ r : ℚ, θ ≠ r)
    {gm : LeafQM.B} (hc : gm * q θ = q θ * gm) : gm ∈ Set.range q := by
  obtain ⟨b, hb⟩ : ∃ b, q θ = b := ⟨_, rfl⟩
  rw [hb] at hc
  have e1 := congrArg QuaternionAlgebra.imI hc
  have e2 := congrArg QuaternionAlgebra.imJ hc
  have e3 := congrArg QuaternionAlgebra.imK hc
  simp only [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul] at e1 e2 e3
  have m1 : gm.imJ * b.imK = gm.imK * b.imJ := by linear_combination e1 / 6
  have m2 : gm.imI * b.imK = gm.imK * b.imI := by linear_combination e2 / 4
  have m3 : gm.imI * b.imJ = gm.imJ * b.imI := by linear_combination e3 / 2
  -- `q(θ)` is not central, since `q` is injective and `θ ∉ ℚ`
  have hnr : ¬ (b.imI = 0 ∧ b.imJ = 0 ∧ b.imK = 0) := by
    rintro ⟨h1, h2, h3⟩
    apply hθ b.re
    apply q.toRingHom.injective
    show q θ = q (b.re : K)
    rw [hb, ← eq_ratCast (algebraMap ℚ K), AlgHom.commutes]
    ext <;> simp [h1, h2, h3]
  obtain ⟨N, hN⟩ : ∃ N : ℚ, N = b.imI ^ 2 + b.imJ ^ 2 + b.imK ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℚ, D = gm.imI * b.imI + gm.imJ * b.imJ + gm.imK * b.imK := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by
    intro h0
    apply hnr
    have hsum : b.imI ^ 2 + b.imJ ^ 2 + b.imK ^ 2 = 0 := by rw [← hN, h0]
    have a1 : b.imI ^ 2 = 0 := by nlinarith [sq_nonneg b.imI, sq_nonneg b.imJ, sq_nonneg b.imK]
    have a2 : b.imJ ^ 2 = 0 := by nlinarith [sq_nonneg b.imI, sq_nonneg b.imJ, sq_nonneg b.imK]
    have a3 : b.imK ^ 2 = 0 := by nlinarith [sq_nonneg b.imI, sq_nonneg b.imJ, sq_nonneg b.imK]
    exact ⟨(pow_eq_zero_iff two_ne_zero).1 a1, (pow_eq_zero_iff two_ne_zero).1 a2,
      (pow_eq_zero_iff two_ne_zero).1 a3⟩
  -- the pure part of `γ` is `(D/N)` times that of `q(θ)`
  have k1 : gm.imI * N = D * b.imI := by
    rw [hN, hD]; linear_combination b.imJ * m3 + b.imK * m2
  have k2 : gm.imJ * N = D * b.imJ := by
    rw [hN, hD]; linear_combination (-b.imI) * m3 + b.imK * m1
  have k3 : gm.imK * N = D * b.imK := by
    rw [hN, hD]; linear_combination (-b.imI) * m2 + (-b.imJ) * m1
  have hs1 : D / N * b.imI = gm.imI := by rw [div_mul_eq_mul_div, div_eq_iff hN0]; exact k1.symm
  have hs2 : D / N * b.imJ = gm.imJ := by rw [div_mul_eq_mul_div, div_eq_iff hN0]; exact k2.symm
  have hs3 : D / N * b.imK = gm.imK := by rw [div_mul_eq_mul_div, div_eq_iff hN0]; exact k3.symm
  refine ⟨algebraMap ℚ K (gm.re - D / N * b.re) + algebraMap ℚ K (D / N) * θ, ?_⟩
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hb, ← Algebra.smul_def]
  ext
  · simp only [QuaternionAlgebra.re_add, QuaternionAlgebra.re_smul, smul_eq_mul,
      QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.re_coe]
    ring
  · simp only [QuaternionAlgebra.imI_add, QuaternionAlgebra.imI_smul, smul_eq_mul,
      QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.imI_coe, zero_add]
    exact hs1
  · simp only [QuaternionAlgebra.imJ_add, QuaternionAlgebra.imJ_smul, smul_eq_mul,
      QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.imJ_coe, zero_add]
    exact hs2
  · simp only [QuaternionAlgebra.imK_add, QuaternionAlgebra.imK_smul, smul_eq_mul,
      QuaternionAlgebra.coe_algebraMap, QuaternionAlgebra.imK_coe, zero_add]
    exact hs3

/-- **The stabiliser of a CM point**: an element `γ ∈ B^×` fixing the CM point `τ` of `q` lies in
`q(K)`. -/
theorem mem_range_of_mobPM_fix (hK : Module.finrank ℚ K = 2) (q : K →ₐ[ℚ] LeafQM.B)
    (κ : K →+* ℂ) (τ : UpperHalfPlane) (hcm : IsCMPoint q κ τ) (gm : LeafQM.B)
    (hγ : ShimuraGlue.nrdQ ℚ gm ≠ 0)
    (h : Y3Hodge.mobPM (iotaGL gm hγ) (Y3Hodge.toPM τ) = Y3Hodge.toPM τ) :
    gm ∈ Set.range q := by
  obtain ⟨lam, hlam⟩ := eig_of_mobPM_fix gm hγ τ h
  obtain ⟨θ, hθ⟩ := exists_not_rat hK
  have hθv : Matrix.mulVec (iotaC (q θ)) ![(τ : ℂ), 1] = κ θ • ![(τ : ℂ), 1] := hcm θ
  refine mem_range_of_comm q hθ (iota_eig_inj (τ := (τ : ℂ)) τ.im_pos.ne' ?_)
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hθv, hlam,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hlam, hθv, smul_smul, smul_smul, mul_comm]

end Stabiliser

/-! ## 2. Equal orbit points have trivial Artin symbol -/

section Orbit

variable {K : Type} [Field K] [NumberField K]

/-- `𝒪̂^×` is closed under products. -/
theorem OhatU_mul {a b : BAQˣ} (ha : a ∈ OhatU) (hb : b ∈ OhatU) : a * b ∈ OhatU := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact OhatQ_mul ha.1 hb.1
  · rw [mul_inv_rev, Units.val_mul]; exact OhatQ_mul hb.2 ha.2

/-- `𝒪̂^×` is closed under inverses. -/
theorem OhatU_inv {a : BAQˣ} (ha : a ∈ OhatU) : a⁻¹ ∈ OhatU :=
  ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

/-- `K₃ ⊆ 𝒪̂^×`. -/
theorem OhatU_of_K3Q {k : BAQˣ} (hk : k ∈ K3Q) : k ∈ OhatU := ⟨hk.1, hk.2.1⟩

/-- **Equal orbit points, double coset form.** If `Ψ(τ, q̂(s)^ε u) = Ψ(τ, u)` at the CM point `τ`
of `q`, `u ∈ 𝒪̂^×`, then by the fibre clause `q̂(s)^ε u = γ u k` with `γ` fixing `τ` and `k ∈ K₃`;
by step 1, `γ = q(t)`, `t ∈ K^×`, so `q̂(t⁻¹ s^ε) = u k u⁻¹ ∈ 𝒪̂^×`. Hence `[s, K]^ε` is trivial on
every abelian `L/K` on which the ideles `s'` with `q̂(s') ∈ 𝒪̂^×` act trivially, and `ε = ±1`. -/
theorem artin_trivial_of_eq (hK : Module.finrank ℚ K = 2)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (hfib : ∀ z g z' g', Ψ z g = Ψ z' g' ↔ Y3Hodge.DCRelPM z g z' g') (ε : ℤˣ)
    (q : K →ₐ[ℚ] LeafQM.B) (κ₀ : K →+* ℂ) (τ : UpperHalfPlane) (hcm : IsCMPoint q κ₀ τ)
    {u : BAQˣ} (hu : u ∈ OhatU)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (hker : ∀ s : IdeleGroup (𝓞 K) K, qHatU q s ∈ OhatU →
      ideleClassArtinMap K L (QuotientGroup.mk s) = 1)
    (s : IdeleGroup (𝓞 K) K)
    (heq : Ψ (Y3Hodge.toPM τ) (qHatU q s ^ (ε : ℤ) * u) = Ψ (Y3Hodge.toPM τ) u) :
    ideleClassArtinMap K L (QuotientGroup.mk s) = 1 := by
  obtain ⟨gm, hγ, hmob, k, hk, hg⟩ := (hfib _ _ _ _).1 heq.symm
  obtain ⟨t, rfl⟩ := mem_range_of_mobPM_fix hK q κ₀ τ hcm gm hγ hmob
  have ht : t ≠ 0 := by
    rintro rfl
    apply hγ
    simp [ShimuraGlue.nrdQ_apply]
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, c = Units.mk0 t ht := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = IdeleGroup.unitEmbedding (𝓞 K) K c := ⟨_, rfl⟩
  have hqe : ((qHatU q e : BAQˣ) : BAQ) = bEmb (q t) := by
    rw [he, qHatU_unitEmbedding, hc, Units.val_mk0]
  have hunit : qHatU q s ^ (ε : ℤ) * u = qHatU q e * u * k := by
    apply Units.ext
    rw [hg]
    simp only [Units.val_mul, hqe]
  have hconj : qHatU q (e⁻¹ * s ^ (ε : ℤ)) = u * k * u⁻¹ := by
    rw [map_mul, map_inv, map_zpow]
    calc (qHatU q e)⁻¹ * qHatU q s ^ (ε : ℤ)
        = (qHatU q e)⁻¹ * (qHatU q s ^ (ε : ℤ) * u) * u⁻¹ := by group
      _ = u * k * u⁻¹ := by rw [hunit]; group
  have h1 := hker _ (by
    rw [hconj]; exact OhatU_mul (OhatU_mul hu (OhatU_of_K3Q hk)) (OhatU_inv hu))
  -- the principal idele `e` is trivial in the idele class group
  have hmk : (QuotientGroup.mk (e⁻¹ * s ^ (ε : ℤ)) : IdeleClassGroup (𝓞 K) K) =
      QuotientGroup.mk (s ^ (ε : ℤ)) := by
    rw [QuotientGroup.eq]
    refine MonoidHom.mem_range.2 ⟨c, ?_⟩
    rw [← he, mul_inv_rev, inv_inv, inv_mul_cancel_comm]
  rw [hmk, QuotientGroup.mk_zpow, map_zpow] at h1
  rcases Int.units_eq_one_or ε with rfl | rfl
  · simpa using h1
  · simpa using h1

/-- **Equal orbit points have trivial Artin symbol.** Let `hrec` be Shimura's reciprocity law at the
CM point `τ` for the reflex embedding `κ`. If `σ ∈ Aut ℂ` acts on `K^ab` as `[s, K]` and fixes
`Ψ(τ, u)`, `u ∈ 𝒪̂^×`, then `[s, K]` is trivial on every abelian `L/K` on which the ideles `s'` with
`q̂(s') ∈ 𝒪̂^×` act trivially. -/
theorem artin_trivial_of_galPt_fix (hK : Module.finrank ℚ K = 2)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (hfib : ∀ z g z' g', Ψ z g = Ψ z' g' ↔ Y3Hodge.DCRelPM z g z' g') (ε : ℤˣ)
    (q : K →ₐ[ℚ] LeafQM.B) (κ κ₀ : K →+* ℂ) (τ : UpperHalfPlane) (hcm : IsCMPoint q κ₀ τ)
    (hrec : ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ (Y3Hodge.toPM τ) g) =
        Ψ (Y3Hodge.toPM τ) (qHatU q s ^ (ε : ℤ) * g))
    {u : BAQˣ} (hu : u ∈ OhatU)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (hker : ∀ s : IdeleGroup (𝓞 K) K, qHatU q s ∈ OhatU →
      ideleClassArtinMap K L (QuotientGroup.mk s) = 1)
    (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K) (hs : ArtinCondC κ σ s)
    (hfix : galPt σ (Ψ (Y3Hodge.toPM τ) u) = Ψ (Y3Hodge.toPM τ) u) :
    ideleClassArtinMap K L (QuotientGroup.mk s) = 1 :=
  artin_trivial_of_eq hK hfib ε q κ₀ τ hcm hu L hker s (by rw [← hrec σ s hs u, hfix])

end Orbit

/-! ## 3. Every element of `Gal(L/K)` is the restriction of an automorphism of `ℂ` -/

section Extend

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
/-- **Every element of `Gal(L/K)` comes from `Aut ℂ`**: for a field embedding `j : L → ℂ` and
`g ∈ Gal(L/K)`, there is `σ ∈ Aut ℂ` with `σ ∘ j = j ∘ g`; it extends an automorphism `σ_ℚ̄` of
`ℚ̄` that extends `g` (on `j(L) ⊆ ℚ̄`). -/
theorem exists_extend_gal (L : Type) [Field L] [NumberField L] [Algebra K L] (j : L →+* ℂ)
    (g : L ≃ₐ[K] L) :
    ∃ (σ : ℂ ≃+* ℂ) (σQ : Qbar ≃ₐ[ℚ] Qbar), (∀ a, σ (ιC a) = ιC (σQ a)) ∧
      ∀ x : L, σ (j x) = j (g x) := by
  obtain ⟨jQ, hjQ⟩ := exists_lift_ringHom (L := L) j
  let _ : Algebra L Qbar := jQ.toAlgebra
  have _ : IsScalarTower ℚ L Qbar := IsScalarTower.of_algebraMap_eq fun r => by
    rw [eq_ratCast (algebraMap ℚ Qbar), eq_ratCast (algebraMap ℚ L), map_ratCast]
  let χ : L ≃ₐ[ℚ] L := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun r => by
    rw [eq_ratCast (algebraMap ℚ L)]
    exact map_ratCast g.toRingEquiv r
  let σQ : Qbar ≃ₐ[ℚ] Qbar := χ.liftNormal Qbar
  have hσQ : ∀ x : L, σQ (jQ x) = jQ (g x) := fun x => χ.liftNormal_commutes Qbar x
  obtain ⟨σ, hσ⟩ := T5Glue.exists_ringEquiv_extend (ιC : Qbar →+* ℂ) σQ.toRingEquiv
  have hσ' : ∀ a, σ (ιC a) = ιC (σQ a) := fun a => hσ a
  refine ⟨σ, σQ, hσ', fun x => ?_⟩
  rw [← hjQ x, ← hjQ (g x), hσ', hσQ]

end Extend

/-! ## 4. The count -/

section Count

/-- The identity of `ℂ` acts trivially on `ℂ`-points. -/
theorem galPt_refl {Y : Over (Spec (CommRingCat.of ℚ))} (y : fieldPt ℂ ⟶ Y) :
    galPt (RingEquiv.refl ℂ) y = y := by
  apply Over.OverMorphism.ext
  simp only [galPt, Over.comp_left, fieldMap_left]
  have e : ((((RingEquiv.refl ℂ : ℂ ≃+* ℂ) : ℂ →+* ℂ).toRatAlgHom : ℂ →ₐ[ℚ] ℂ) : ℂ →+* ℂ) =
      RingHom.id ℂ := rfl
  rw [e, CommRingCat.ofHom_id, Spec.map_id]
  exact Category.id_comp _

/-- `Aut ℂ` acts on `ℂ`-points: `(σ' ∘ σ)(y) = σ'(σ(y))`. -/
theorem galPt_trans {Y : Over (Spec (CommRingCat.of ℚ))} (σ σ' : ℂ ≃+* ℂ)
    (y : fieldPt ℂ ⟶ Y) : galPt (σ.trans σ') y = galPt σ' (galPt σ y) := by
  apply Over.OverMorphism.ext
  simp only [galPt, Over.comp_left, fieldMap_left]
  have key : Spec.map (CommRingCat.ofHom
      ((((σ.trans σ' : ℂ ≃+* ℂ) : ℂ →+* ℂ).toRatAlgHom : ℂ →ₐ[ℚ] ℂ) : ℂ →+* ℂ)) =
      Spec.map (CommRingCat.ofHom (((σ' : ℂ →+* ℂ).toRatAlgHom : ℂ →ₐ[ℚ] ℂ) : ℂ →+* ℂ)) ≫
        Spec.map (CommRingCat.ofHom (((σ : ℂ →+* ℂ).toRatAlgHom : ℂ →ₐ[ℚ] ℂ) : ℂ →+* ℂ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [key]
  exact Category.assoc _ _ _

/-- Galois stability of a set of `ℚ̄`-points, from its `Aut ℂ`-form on `ιC^*`. -/
theorem stab_of_stabC {Y : Over (Spec (CommRingCat.of ℚ))} (S : Set (fieldPt Qbar ⟶ Y))
    (hS : ∀ σ : ℂ ≃+* ℂ, ∀ y' ∈ S, ∃ y'' ∈ S, galPt σ (fieldMap ιC ≫ y') = fieldMap ιC ≫ y'') :
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ y' ∈ S, fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y' ∈ S := by
  intro σ y' hy'
  obtain ⟨σC, hσC⟩ := T5Glue.exists_ringEquiv_extend (ιC : Qbar →+* ℂ) σ.toRingEquiv
  obtain ⟨y'', hy'', he⟩ := hS σC y' hy'
  rw [galPt_fieldMap y' σ σC (fun a => hσC a)] at he
  rw [fieldMap_ιC_inj he]
  exact hy''

/-- **The Galois orbit bound.** Let `Ψ` have fibres the double cosets `DCRelPM` (`hfib`) and satisfy
Shimura's reciprocity law at CM points of `K` (`hrec`). Let `y ∈ S` be a `ℚ̄`-point with
`ιC^* y = Ψ(τ, u)`, `u ∈ 𝒪̂^×`, `τ` the CM point of `q : K → B`, and `L/K` a finite abelian extension
on which every idele `s` with `q̂(s) ∈ 𝒪̂^×` has trivial Artin symbol. If `S` is finite and
`Gal(ℚ̄/ℚ)`-stable, then `card Gal(L/K) ≤ card S`: for `g ∈ Gal(L/K)` pick `σ_g ∈ Aut ℂ` extending `g`
(step 3); if `σ_g(y) = σ_{g'}(y)`, then `σ_{g'}⁻¹ σ_g` fixes `y` and acts on `K^ab` as some
`[s, K]`, so by step 2 it is trivial on `L`, i.e. `g = g'`. -/
theorem card_gal_le_ncard
    {Y : Over (Spec (CommRingCat.of ℚ))} {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (hfib : ∀ z g z' g', Ψ z g = Ψ z' g' ↔ Y3Hodge.DCRelPM z g z' g')
    (hrec : ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ (Y3Hodge.toPM z) g) =
        Ψ (Y3Hodge.toPM z) (qHatU q s ^ (ε : ℤ) * g))
    (S : Set (fieldPt Qbar ⟶ Y)) (hSfin : S.Finite)
    (hstab : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ y' ∈ S, fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y' ∈ S)
    (y : fieldPt Qbar ⟶ Y) (hy : y ∈ S)
    (q : K →ₐ[ℚ] LeafQM.B) (κ₀ : K →+* ℂ) (τ : UpperHalfPlane) (u : BAQˣ) (hu : u ∈ OhatU)
    (hcm : IsCMPoint q κ₀ τ) (hτu : Ψ (Y3Hodge.toPM τ) u = fieldMap ιC ≫ y)
    (L : Type) [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]
    (hker : ∀ s : IdeleGroup (𝓞 K) K, qHatU q s ∈ OhatU →
      ideleClassArtinMap K L (QuotientGroup.mk s) = 1) :
    Nat.card (L ≃ₐ[K] L) ≤ S.ncard := by
  obtain ⟨ε, δ, hrec⟩ := hrec
  -- the reflex embedding in the convention `δ`
  let κ : K →+* ℂ := if δ then κ₀ else (starRingEnd ℂ).comp κ₀
  have hκκ : (if δ then κ else (starRingEnd ℂ).comp κ) = κ₀ := by
    cases δ <;> ext a <;> simp [κ]
  have hrecτ : ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ (Y3Hodge.toPM τ) g) =
        Ψ (Y3Hodge.toPM τ) (qHatU q s ^ (ε : ℤ) * g) :=
    hrec κ q τ (by rw [hκκ]; exact hcm)
  -- an embedding `j : L → ℂ` over `κ`
  let _ : Algebra K ℂ := κ.toAlgebra
  let j' : L →ₐ[K] ℂ := IsAlgClosed.lift
  let j : L →+* ℂ := j'
  have hj : j.comp (algebraMap K L) = κ := by
    ext a; exact j'.commutes a
  -- `σ_g ∈ Aut ℂ` extending `g ∈ Gal(L/K)`, through `σ_g|ℚ̄ ∈ Gal(ℚ̄/ℚ)`
  choose σ σQ hσQ hσj using fun g : L ≃ₐ[K] L => exists_extend_gal L j g
  have hfixκ : ∀ g a, σ g (κ a) = κ a := fun g a => by
    have e : j (algebraMap K L a) = κ a := RingHom.congr_fun hj a
    rw [← e, hσj g, AlgEquiv.commutes]
  have _ : Finite S := hSfin.to_subtype
  let F : (L ≃ₐ[K] L) → S := fun g => ⟨fieldMap (σQ g : Qbar →ₐ[ℚ] Qbar) ≫ y, hstab _ y hy⟩
  have hFinj : Function.Injective F := by
    intro g g' hgg
    have h1 : fieldMap (σQ g : Qbar →ₐ[ℚ] Qbar) ≫ y =
        fieldMap (σQ g' : Qbar →ₐ[ℚ] Qbar) ≫ y := congrArg Subtype.val hgg
    have h2 : galPt (σ g) (fieldMap ιC ≫ y) = galPt (σ g') (fieldMap ιC ≫ y) := by
      rw [galPt_fieldMap y (σQ g) (σ g) (hσQ g), galPt_fieldMap y (σQ g') (σ g') (hσQ g'), h1]
    -- `ρ = σ_{g'}⁻¹ σ_g` fixes `ιC^* y` and `κ(K)`
    have h3 : galPt ((σ g).trans (σ g').symm) (fieldMap ιC ≫ y) = fieldMap ιC ≫ y := by
      rw [galPt_trans, h2, ← galPt_trans, RingEquiv.self_trans_symm, galPt_refl]
    have hρκ : ∀ a : K, ((σ g).trans (σ g').symm) (κ a) = κ a := fun a => by
      show (σ g').symm (σ g (κ a)) = κ a
      rw [hfixκ g a, RingEquiv.symm_apply_eq, hfixκ g' a]
    obtain ⟨s, hs⟩ := exists_artinCondC κ ((σ g).trans (σ g').symm) hρκ
    have hart := artin_trivial_of_galPt_fix hK hfib ε q κ κ₀ τ hcm hrecτ hu L hker
      ((σ g).trans (σ g').symm) s hs (by rw [hτu]; exact h3)
    -- so `ρ` is trivial on `j(L)`
    have h6 : ∀ x : L, ((σ g).trans (σ g').symm) (j x) = j x := fun x => by
      rw [hs L j hj x, hart, AlgEquiv.one_apply]
    apply AlgEquiv.ext
    intro x
    apply j.injective
    have h7 := h6 x
    change (σ g').symm (σ g (j x)) = j x at h7
    rw [hσj g x, RingEquiv.symm_apply_eq, hσj g' x] at h7
    exact h7
  have hle := Nat.card_le_card_of_injective F hFinj
  rwa [Nat.card_coe_set_eq] at hle

/-- **The orbit bound for `Pic`.** In the setting of `card_gal_le_ncard`, with `R = q⁻¹(𝒪)` an
order of `K` and `L = H` its ring class field: `card Pic R = [H : K] = card Gal(H/K) ≤ card S`.
The two clauses of the uniformization used are the fibre clause `hfib` and the reciprocity clause
`hrec` (as in `Y3Hodge.DeligneBodyAtPM`). -/
theorem card_pic_le_ncard
    {Y : Over (Spec (CommRingCat.of ℚ))} {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (hfib : ∀ z g z' g', Ψ z g = Ψ z' g' ↔ Y3Hodge.DCRelPM z g z' g')
    (hrec : ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ (Y3Hodge.toPM z) g) =
        Ψ (Y3Hodge.toPM z) (qHatU q s ^ (ε : ℤ) * g))
    (S : Set (fieldPt Qbar ⟶ Y)) (hSfin : S.Finite)
    (hstab : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ y' ∈ S, fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y' ∈ S)
    (y : fieldPt Qbar ⟶ Y) (hy : y ∈ S)
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (q : K →ₐ[ℚ] LeafQM.B) (κ₀ : K →+* ℂ) (τ : UpperHalfPlane) (u : BAQˣ) (hu : u ∈ OhatU)
    (hcm : IsCMPoint q κ₀ τ) (hτu : Ψ (Y3Hodge.toPM τ) u = fieldMap ιC ≫ y)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (hRCK : ∀ s : IdeleGroup (𝓞 K) K, qHatU q s ∈ OhatU →
      ideleClassArtinMap K
        (ringClassField (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf))
        (QuotientGroup.mk s) = 1) :
    Nat.card (CommRing.Pic (LeafQM.O.comap q.toRingHom)) ≤ S.ncard := by
  obtain ⟨ε, δ, hrec⟩ := hrec
  have h := card_gal_le_ncard K hK hfib ⟨ε, δ, hrec K hK⟩ S hSfin hstab y hy q κ₀ τ u hu hcm hτu
    (ringClassField (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf)) hRCK
  rwa [IsGalois.card_aut_eq_finrank, GR512Bridge.finrank_ringClassField_eq_card_pic,
    GR512Bridge.toOrder_toSubring] at h

/-- **The orbit bound: `card Pic R ≤ 324`** when the Galois-stable set `S` has at most `324` points. -/
theorem card_pic_le_324
    {Y : Over (Spec (CommRingCat.of ℚ))} {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (hfib : ∀ z g z' g', Ψ z g = Ψ z' g' ↔ Y3Hodge.DCRelPM z g z' g')
    (hrec : ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ (Y3Hodge.toPM z) g) =
        Ψ (Y3Hodge.toPM z) (qHatU q s ^ (ε : ℤ) * g))
    (S : Set (fieldPt Qbar ⟶ Y)) (hSfin : S.Finite) (hS : S.ncard ≤ 324)
    (hstab : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ y' ∈ S, fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y' ∈ S)
    (y : fieldPt Qbar ⟶ Y) (hy : y ∈ S)
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (q : K →ₐ[ℚ] LeafQM.B) (κ₀ : K →+* ℂ) (τ : UpperHalfPlane) (u : BAQˣ) (hu : u ∈ OhatU)
    (hcm : IsCMPoint q κ₀ τ) (hτu : Ψ (Y3Hodge.toPM τ) u = fieldMap ιC ≫ y)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (hRCK : ∀ s : IdeleGroup (𝓞 K) K, qHatU q s ∈ OhatU →
      ideleClassArtinMap K
        (ringClassField (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf))
        (QuotientGroup.mk s) = 1) :
    Nat.card (CommRing.Pic (LeafQM.O.comap q.toRingHom)) ≤ 324 :=
  (card_pic_le_ncard hfib hrec S hSfin hstab y hy K hK q κ₀ τ u hu hcm hτu hR hf hRCK).trans hS

/-- `card_pic_le_324` with the stability of `S` in its `Aut ℂ`-form on `ιC^*`. -/
theorem card_pic_le_324_of_stabC
    {Y : Over (Spec (CommRingCat.of ℚ))} {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)}
    (hfib : ∀ z g z' g', Ψ z g = Ψ z' g' ↔ Y3Hodge.DCRelPM z g z' g')
    (hrec : ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ (Y3Hodge.toPM z) g) =
        Ψ (Y3Hodge.toPM z) (qHatU q s ^ (ε : ℤ) * g))
    (S : Set (fieldPt Qbar ⟶ Y)) (hSfin : S.Finite) (hS : S.ncard ≤ 324)
    (hstab : ∀ σ : ℂ ≃+* ℂ, ∀ y' ∈ S, ∃ y'' ∈ S,
      galPt σ (fieldMap ιC ≫ y') = fieldMap ιC ≫ y'')
    (y : fieldPt Qbar ⟶ Y) (hy : y ∈ S)
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (q : K →ₐ[ℚ] LeafQM.B) (κ₀ : K →+* ℂ) (τ : UpperHalfPlane) (u : BAQˣ) (hu : u ∈ OhatU)
    (hcm : IsCMPoint q κ₀ τ) (hτu : Ψ (Y3Hodge.toPM τ) u = fieldMap ιC ≫ y)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (hRCK : ∀ s : IdeleGroup (𝓞 K) K, qHatU q s ∈ OhatU →
      ideleClassArtinMap K
        (ringClassField (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf))
        (QuotientGroup.mk s) = 1) :
    Nat.card (CommRing.Pic (LeafQM.O.comap q.toRingHom)) ≤ 324 :=
  card_pic_le_324 hfib hrec S hSfin hS (stab_of_stabC S hstab) y hy K hK q κ₀ τ u hu hcm hτu
    hR hf hRCK

/-- `card_pic_le_324` from the whole print-form Deligne body (its fibre and reciprocity clauses). -/
theorem card_pic_le_324_of_body
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)} (hb : Y3Hodge.DeligneBodyAtPM Y Φ Ψ)
    (S : Set (fieldPt Qbar ⟶ Y)) (hSfin : S.Finite) (hS : S.ncard ≤ 324)
    (hstab : ∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ y' ∈ S, fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ y' ∈ S)
    (y : fieldPt Qbar ⟶ Y) (hy : y ∈ S)
    (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    (q : K →ₐ[ℚ] LeafQM.B) (κ₀ : K →+* ℂ) (τ : UpperHalfPlane) (u : BAQˣ) (hu : u ∈ OhatU)
    (hcm : IsCMPoint q κ₀ τ) (hτu : Ψ (Y3Hodge.toPM τ) u = fieldMap ιC ≫ y)
    (hR : LeafQM.O.comap q.toRingHom ≤ (integralClosure ℤ K).toSubring)
    (hf : LeafQM.AV.conductor (LeafQM.O.comap q.toRingHom) ≠ 0)
    (hRCK : ∀ s : IdeleGroup (𝓞 K) K, qHatU q s ∈ OhatU →
      ideleClassArtinMap K
        (ringClassField (GR512Bridge.toOrder (LeafQM.O.comap q.toRingHom) hR hf))
        (QuotientGroup.mk s) = 1) :
    Nat.card (CommRing.Pic (LeafQM.O.comap q.toRingHom)) ≤ 324 :=
  card_pic_le_324 hb.2.1 hb.2.2.2.2 S hSfin hS hstab y hy K hK q κ₀ τ u hu hcm hτu hR hf hRCK

end Count

end HDec.CMBranch.CMjReroute
