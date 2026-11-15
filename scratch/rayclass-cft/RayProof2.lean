import RayProof1

/-! # rayclass-cft, Part P2: the Props (leaves and glue) and the core argument -/

set_option linter.all false

noncomputable section

namespace RayClassCFT

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)

/-! ## P2a. Copies (t5-glue `Field.lean`, Mathlib only): extension of automorphisms of `ℚ̄` to `ℂ` -/

open MvPolynomial in
/-- An automorphism of the polynomial ring on a transcendence basis extends to `K`
(verbatim from `scratch/t5-glue/Field.lean`). -/
theorem exists_aut_extend {k K : Type*} [Field k] [Field K] [IsAlgClosed K] [Algebra k K]
    {ιT : Type*} {v : ιT → K} (hv : IsTranscendenceBasis k v)
    (ψ : MvPolynomial ιT k ≃+* MvPolynomial ιT k) :
    ∃ σ : K ≃+* K, ∀ p : MvPolynomial ιT k, σ (aeval v p) = aeval v (ψ p) := by
  let e := hv.1.aevalEquiv
  let φ : Algebra.adjoin k (Set.range v) ≃+* Algebra.adjoin k (Set.range v) :=
    e.symm.toRingEquiv.trans (ψ.trans e.toRingEquiv)
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range v)) K := hv.isAlgebraic
  have : IsAlgClosure (Algebra.adjoin k (Set.range v)) K := ⟨inferInstance, inferInstance⟩
  refine ⟨IsAlgClosure.equivOfEquiv K K φ, fun p => ?_⟩
  rw [← hv.1.algebraMap_aevalEquiv, IsAlgClosure.equivOfEquiv_algebraMap,
    ← hv.1.algebraMap_aevalEquiv]
  congr 1
  simp [φ, e]

open MvPolynomial in
/-- **Extension of automorphisms** (verbatim from `scratch/t5-glue/Field.lean`). -/
theorem exists_ringEquiv_extend {k K : Type*} [Field k] [Field K] [IsAlgClosed K]
    (ι : k →+* K) (ρ : k ≃+* k) : ∃ σ : K ≃+* K, ∀ a : k, σ (ι a) = ι (ρ a) := by
  let _ : Algebra k K := ι.toAlgebra
  have : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).2 ι.injective
  obtain ⟨T, hT⟩ := exists_isTranscendenceBasis k K
  obtain ⟨σ, hσ⟩ := exists_aut_extend hT (MvPolynomial.mapEquiv T ρ)
  refine ⟨σ, fun a => ?_⟩
  have h := hσ (C a)
  simp only [aeval_C, mapEquiv_apply, map_C] at h
  exact h

/-! ## P2b. The Props -/

/-- `𝒪̂^× ⊆ (B ⊗ 𝔸_f)^×` (the kernel's `ShimuraGlue.Kfull`, with `𝓞 ℚ` in place of `ℤ`). -/
def OhatU : Set BAQˣ := {u | (u : BAQ) ∈ OhatQ ∧ ((u⁻¹ : BAQˣ) : BAQ) ∈ OhatQ}

/-- The body of shimura-cft's `ShimuraDeligneBody` with the map `Ψ` as an argument (its text after
`∃ Ψ, `, verbatim). -/
def DeligneBodyAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
    (∀ y : fieldPt ℂ ⟶ Y, ∃ τ g, Ψ τ g = y) ∧
    (∀ τ g τ' g', Ψ τ g = Ψ τ' g' ↔ DCRel τ g τ' g') ∧
    (∀ g, ShimuraSplit.IsHolFamily (X := Y.left) (fun τ => (Ψ τ g).left)) ∧
    HDec.HSyn.G0Split.FibreQM.IsShimuraHolFamily Y Φ (fun τ => Ψ τ 1) ∧
    ∃ (ε : ℤˣ) (δ : Bool),
      ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      ∀ (κ : K →+* ℂ) (q : K →ₐ[ℚ] LeafQM.B) (z : UpperHalfPlane),
        IsCMPoint q (if δ then κ else (starRingEnd ℂ).comp κ) z →
      ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 K) K), ArtinCondC κ σ s →
      ∀ g : BAQˣ, galPt σ (Ψ z g) = Ψ z (qHatU q s ^ (ε : ℤ) * g)

theorem shimuraDeligneBody_iff (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) :
    ShimuraDeligneBody Y Φ ↔ ∃ Ψ, DeligneBodyAt Y Φ Ψ := Iff.rfl

/-- **The moduli clause at every `u ∈ 𝒪̂^×`**: the object at `Ψ(τ, u)` is, as a QM pair, the torus
`ℂ²/ι(𝒪)(τ, 1)ᵀ` with its `ι` (the moduli part of `IsShimuraHolFamily`, verbatim, at `Ψ(τ, u)` in
place of `Ψ(τ, 1)`). In the moduli description of `Sh_{K₃}` the point `[τ, g]` is the torus
`ℂ²/ι(B ∩ 𝒪̂g⁻¹)(τ,1)ᵀ` with the level structure induced by `g`; for `g = u ∈ 𝒪̂^×` the lattice is
`ι(𝒪)(τ,1)ᵀ` and only the level structure changes. -/
def ModuliAtUnits (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
  ∀ u ∈ OhatU, ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, Φ ℂ (Ψ τ u) = M3.mk P ∧
    ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
      IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
      HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φu

/-- **LEAF `ShimuraMainThmIDeligneY3AbU`**: shimura-cft's leaf `ShimuraMainThmIDeligneY3Ab` with its
moduli clause stated at every `u ∈ 𝒪̂^×` instead of `u = 1` (`ModuliAtUnits`).

*Published statements* (locators recalled, UNVERIFIED; no network): as for
`ShimuraMainThmIDeligneY3Ab` (Shimura, Ann. of Math. 85 (1967), Main Theorem I and §§2-3;
Deligne, Sém. Bourbaki 389 (1971), §§3-4; Milne, *Introduction to Shimura varieties*, §§12-14). In the
moduli interpretation of `Sh_K(B^×, ℍ^±)` for a quaternion algebra over `ℚ` (Deligne §4; Milne Ex. 14),
`[τ, g]` is the class of `(ℂ²/ι(L_g)(τ,1)ᵀ, ι, η_g)` with `L_g = B ∩ 𝒪̂g⁻¹`; for `g ∈ 𝒪̂^×`,
`L_g = 𝒪`. *Form*: a consequence (the moduli clause is kept for `g ∈ 𝒪̂^×` only, and only the QM pair,
not the level structure, is described). -/
def ShimuraMainThmIDeligneY3AbU : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y),
    LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ ∧ ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ

/-- The new leaf implies shimura-cft's (drop `ModuliAtUnits`). -/
theorem mainThmI_of_U (h : ShimuraMainThmIDeligneY3AbU) : ShimuraMainThmIDeligneY3Ab := by
  obtain ⟨Y, Φ, h1, Ψ, hb, -⟩ := h
  exact ⟨Y, Φ, h1, Ψ, hb⟩

/-- **LEAF `ClassNumberOneB` (Eichler)**: `(B ⊗ 𝔸_f)^× = B^× · 𝒪̂^×`, i.e. the maximal order
`𝒪 = ℤ⟨1, i, (1+j)/2, (i+k)/2⟩` of the indefinite algebra `B = (2, −3 | ℚ)` has one class of locally
principal left ideals.

*Published statement* (locators recalled, UNVERIFIED): Eichler's class number theorem: an Eichler
order (in particular a maximal order) in an indefinite quaternion algebra over `ℚ` has class number one
(Eichler, J. reine angew. Math. 195 (1955); Vignéras, *Arithmétique des algèbres de quaternions*,
LNM 800, Cor. III.5.7; Voight, *Quaternion algebras*, GTM 288, Cor. 28.5.17), read adelically:
`Cls 𝒪 = B^× \ (B ⊗ 𝔸_f)^× / 𝒪̂^×` (Voight 27.6). *Form*: the printed statement (adelic form). -/
def ClassNumberOneB : Prop :=
  ∀ g : BAQˣ, ∃ γ : LeafQM.B, ShimuraGlue.nrdQ ℚ γ ≠ 0 ∧
    ∃ u ∈ OhatU, (g : BAQ) = bEmb γ * (u : BAQ)

/-- **GLUE `QHatIntegral k`** (adelic algebra): if `q(𝒪_k) ⊆ 𝒪`, then `q̂` maps the ideles of the
congruence subgroup of the modulus `3·𝒪_k` (units at every finite place, `≡ 1 mod 3` above 3) into
`K₃`. True: `q̂(𝒪̂_k) ⊆ 𝒪̂` because `𝒪̂_k = ℤ̂ ⊗ 𝒪_k` under Tau Ceti's base change
`𝔸_{ℚ,f} ⊗_ℚ k ≅ 𝔸_{k,f}`, and `q̂(1 + 3x) = 1 + 3 q̂(x)`. -/
def QHatIntegral (k : Type) [Field k] [NumberField k] : Prop :=
  ∀ q : k →ₐ[ℚ] LeafQM.B, (∀ x : 𝓞 k, InO (q x)) →
    ∀ s ∈ ideleCongruenceSubgroup (ShimuraGlue.Ray.mod3 k), qHatU q s ∈ K3Q

/-- **GLUE `CMBaseChange`**: the CM relations of `P/ℚ̄` pass to an object `Q/ℂ` that is a base change
of `P` (the kernel's relation `IsBaseChangeOf`). True: the endomorphism `φ` of `P.A` gives
`φ_ℂ = pullback.lift (g ≫ φ) Q.A.hom`, a pointed morphism of abelian varieties, hence a homomorphism
(rigidity), commuting with `ι_Q` and satisfying the same polynomial identity. -/
def CMBaseChange : Prop :=
  ∀ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q : QML3 ℂ), IsBaseChangeOf ιe P Q →
    (HasCM4 P.q → HasCM4 Q.q) ∧ (HasCM3 P.q → HasCM3 Q.q) ∧ (HasCM24 P.q → HasCM24 Q.q)

/-- **GLUE `CMAnalytic`**: for a QM surface `Q/ℂ` uniformized `ι`-compatibly by
`Λ_τ = ι(𝒪)(τ, 1)ᵀ`, the analytic representation is a ring map `End_𝒪(Q) → 𝒪` whose values have
`(τ, 1)ᵀ` as an eigenvector. True: every endomorphism `f` lifts to a `ℂ`-linear `M` with `M Λ_τ ⊆ Λ_τ`
(the kernel's textbook leaf `T11a_RiemannEnd`); `f ∈ End_𝒪` makes `M` commute with `ι(𝒪)`, hence
`M = λ`; `λ(τ, 1)ᵀ ∈ Λ_τ` gives `β ∈ 𝒪` with `ι(β)(τ, 1)ᵀ = λ(τ, 1)ᵀ`; `f ↦ β` is a ring map
because lifts are unique. -/
def CMAnalytic : Prop :=
  ∀ (τ : UpperHalfPlane) (Q : QML3 ℂ) (Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu →
    HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu →
    ∃ ρ : com Q.q →+* LeafQM.B, ∀ φ : com Q.q, InO (ρ φ) ∧ ∃ lam : ℂ,
      Matrix.mulVec ((BPAnalytic.QM.iota (ρ φ)).map (algebraMap ℝ ℂ)) ![(τ : ℂ), 1] =
        lam • ![(τ : ℂ), 1]

/-! ## P2c. Units of `B` and of `𝒪̂` -/

theorem nrd_ne_zero_of_mul {x y : LeafQM.B} (h : x * y = 1) : ShimuraGlue.nrdQ ℚ x ≠ 0 := by
  intro h0
  have := congrArg (ShimuraGlue.nrdQ ℚ) h
  rw [map_mul, h0, zero_mul, map_one] at this
  exact zero_ne_one this

/-- `γ⁻¹ = nrd(γ)⁻¹ γ̄`. -/
def binv (γ : LeafQM.B) : LeafQM.B := (ShimuraGlue.nrdQ ℚ γ)⁻¹ • star γ

theorem mul_binv {γ : LeafQM.B} (h : ShimuraGlue.nrdQ ℚ γ ≠ 0) : γ * binv γ = 1 := by
  rw [binv, mul_smul_comm, ← nrd_coe_eq]
  rw [QuaternionAlgebra.coe_algebraMap.symm, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem binv_mul {γ : LeafQM.B} (h : ShimuraGlue.nrdQ ℚ γ ≠ 0) : binv γ * γ = 1 := by
  rw [binv, smul_mul_assoc, star_mul_eq, ← nrd_coe_eq]
  rw [QuaternionAlgebra.coe_algebraMap.symm, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]

theorem nrd_binv_pos {γ : LeafQM.B} (h : 0 < ShimuraGlue.nrdQ ℚ γ) : 0 < ShimuraGlue.nrdQ ℚ (binv γ) := by
  have h1 := congrArg (ShimuraGlue.nrdQ ℚ) (mul_binv h.ne')
  rw [map_mul, map_one] at h1
  by_contra hn
  push Not at hn
  nlinarith

theorem OhatQ_mul {x y : BAQ} (hx : x ∈ OhatQ) (hy : y ∈ OhatQ) : x * y ∈ OhatQ := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  refine ⟨ShimuraGlue.mulCoordR n m, fun j => ?_, ShimuraGlue.ofQ_mul n m⟩
  have e : ShimuraGlue.mulCoordR (fun i => ZhatS.subtype ⟨n i, hn i⟩)
      (fun i => ZhatS.subtype ⟨m i, hm i⟩) j =
      ZhatS.subtype (ShimuraGlue.mulCoordR (fun i => (⟨n i, hn i⟩ : ZhatS)) (fun i => ⟨m i, hm i⟩) j) := by
    fin_cases j <;> simp [ShimuraGlue.mulCoordR]
  exact e ▸ (ShimuraGlue.mulCoordR (fun i => (⟨n i, hn i⟩ : ZhatS)) (fun i => ⟨m i, hm i⟩) j).2

theorem OhatQ_one : (1 : BAQ) ∈ OhatQ := by
  simpa using bEmb_mem_of_inO (x := 1) ⟨![1, 0, 0, 0], by ext <;> simp [LeafQM.ofInt]⟩

theorem OhatQ_add {x y : BAQ} (hx : x ∈ OhatQ) (hy : y ∈ OhatQ) : x + y ∈ OhatQ := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  exact ⟨n + m, fun i => ZhatS.add_mem (hn i) (hm i), ShimuraGlue.ofQ_add n m⟩

theorem OhatQ_natCast (n : ℕ) : (n : BAQ) ∈ OhatQ := by
  induction n with
  | zero => exact ⟨0, fun i => ZhatS.zero_mem, by simp [ShimuraGlue.ofQ_zero]⟩
  | succ n ih => push_cast; exact OhatQ_add ih OhatQ_one

/-- `K₃` is normalized by `𝒪̂^×`. -/
theorem conj_mem_K3Q {u k : BAQˣ} (hu : u ∈ OhatU) (hk : k ∈ K3Q) : u⁻¹ * k * u ∈ K3Q := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hk1, hk2, y, hy, hky⟩ := hk
  refine ⟨?_, ?_, ((u⁻¹ : BAQˣ) : BAQ) * y * u, OhatQ_mul (OhatQ_mul hu2 hy) hu1, ?_⟩
  · simp only [Units.val_mul]; exact OhatQ_mul (OhatQ_mul hu2 hk1) hu1
  · rw [mul_inv_rev, mul_inv_rev, inv_inv]
    simp only [Units.val_mul]
    first | exact OhatQ_mul (OhatQ_mul hu2 hk2) hu1 | exact OhatQ_mul hu2 (OhatQ_mul hk2 hu1)
  · simp only [Units.val_mul, hky]
    have h3 : ((u⁻¹ : BAQˣ) : BAQ) * 3 = 3 * ((u⁻¹ : BAQˣ) : BAQ) := (Commute.ofNat_right _ 3).eq
    have h1 : ((u⁻¹ : BAQˣ) : BAQ) * (u : BAQ) = 1 := by simp
    calc ((u⁻¹ : BAQˣ) : BAQ) * (1 + 3 * y) * u
        = ((u⁻¹ : BAQˣ) : BAQ) * u + (((u⁻¹ : BAQˣ) : BAQ) * 3) * y * u := by noncomm_ring
      _ = 1 + 3 * (((u⁻¹ : BAQˣ) : BAQ) * y * u) := by rw [h1, h3]; noncomm_ring

/-- `bEmb` of a unit of `B` with explicit inverse, as a unit. -/
def bUnit (x y : LeafQM.B) (h1 : x * y = 1) (h2 : y * x = 1) : BAQˣ where
  val := bEmb x
  inv := bEmb y
  val_inv := by rw [← map_mul, h1, map_one]
  inv_val := by rw [← map_mul, h2, map_one]

/-- `1 + i ∈ 𝒪^×`, of reduced norm `−1`. -/
def mu : LeafQM.B := ⟨1, 1, 0, 0⟩
def muInv : LeafQM.B := ⟨-1, 1, 0, 0⟩

theorem mu_mul : mu * muInv = 1 := by ext <;> simp [mu, muInv] <;> norm_num
theorem mul_mu : muInv * mu = 1 := by ext <;> simp [mu, muInv] <;> norm_num
theorem nrd_mu : ShimuraGlue.nrdQ ℚ mu = -1 := by simp [ShimuraGlue.nrdQ_apply, mu]; norm_num
theorem inO_mu : InO mu := ⟨![1, 1, 0, 0], by ext <;> simp [mu, LeafQM.ofInt]⟩
theorem inO_muInv : InO muInv := ⟨![-1, 1, 0, 0], by ext <;> simp [muInv, LeafQM.ofInt]⟩

/-- **Class number one with `nrd γ > 0`** (from `ClassNumberOneB`, with `1 + i` of norm `−1`). -/
theorem exists_pos_decomp (hCN : ClassNumberOneB) (g : BAQˣ) :
    ∃ γ : LeafQM.B, 0 < ShimuraGlue.nrdQ ℚ γ ∧ ∃ u ∈ OhatU, (g : BAQ) = bEmb γ * (u : BAQ) := by
  obtain ⟨γ, hγ, u, hu, hg⟩ := hCN g
  rcases lt_or_gt_of_ne hγ with hneg | hpos
  · refine ⟨γ * mu, by rw [map_mul, nrd_mu]; linarith, bUnit muInv mu mul_mu mu_mul * u, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simp only [Units.val_mul]
        exact OhatQ_mul (bEmb_mem_of_inO inO_muInv) hu.1
      · rw [mul_inv_rev]; simp only [Units.val_mul]
        exact OhatQ_mul hu.2 (bEmb_mem_of_inO inO_mu)
    · rw [hg, Units.val_mul, map_mul]
      show bEmb γ * (u : BAQ) = bEmb γ * bEmb mu * (bEmb muInv * (u : BAQ))
      rw [mul_assoc, ← mul_assoc (bEmb mu), ← map_mul, mu_mul, map_one, one_mul]
  · exact ⟨γ, hpos, u, hu, hg⟩

/-! ## P2d. The relation `DCRel` -/

/-- `ι(γ)` as an element of `GL₂(ℝ)` (for `nrd γ ≠ 0`). -/
def iotaGL (γ : LeafQM.B) (h : ShimuraGlue.nrdQ ℚ γ ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (BPAnalytic.QM.iota γ)
    (by rw [det_iota]; exact_mod_cast h)

theorem iotaGL_coe (γ : LeafQM.B) (h : ShimuraGlue.nrdQ ℚ γ ≠ 0) :
    ((iotaGL γ h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = BPAnalytic.QM.iota γ := rfl

theorem K3Q_one : (1 : BAQˣ) ∈ K3Q :=
  ⟨by simpa using OhatQ_one, by simpa using OhatQ_one, 0, ⟨0, fun i => ZhatS.zero_mem, by
    simp [ShimuraGlue.ofQ_zero]⟩, by simp⟩

/-- Move `γ ∈ B^×_+` from `g = γu` to the half plane. -/
theorem dcRel_of_decomp {γ : LeafQM.B} (hγ : 0 < ShimuraGlue.nrdQ ℚ γ) (τ : UpperHalfPlane)
    {g u : BAQˣ} (hg : (g : BAQ) = bEmb γ * (u : BAQ)) :
    DCRel τ g ((iotaGL (binv γ) (nrd_binv_pos hγ).ne') • τ) u := by
  refine ⟨binv γ, nrd_binv_pos hγ, ⟨_, iotaGL_coe _ _, rfl⟩, 1, K3Q_one, ?_⟩
  rw [hg, Units.val_one, mul_one, ← mul_assoc, ← map_mul, binv_mul hγ.ne', map_one, one_mul]

/-- A CM point is fixed: `DCRel τ u τ (γ u k)` for `γ` with eigenvector `(τ, 1)ᵀ` and `nrd γ > 0`. -/
theorem dcRel_fix {γ : LeafQM.B} (hγ : 0 < ShimuraGlue.nrdQ ℚ γ) (τ : UpperHalfPlane) {lam : ℂ}
    (heig : Matrix.mulVec ((BPAnalytic.QM.iota γ).map (algebraMap ℝ ℂ)) ![(τ : ℂ), 1] =
      lam • ![(τ : ℂ), 1]) (u k g' : BAQˣ) (hk : k ∈ K3Q)
    (hg' : (g' : BAQ) = bEmb γ * (u : BAQ) * (k : BAQ)) : DCRel τ u τ g' := by
  refine ⟨γ, hγ, ⟨iotaGL γ hγ.ne', iotaGL_coe _ _, ?_⟩, k, hk, hg'⟩
  exact smul_eq_of_eig _ τ (by rw [iotaGL_coe]; exact heig)

end RayClassCFT
