import ZInQKernel.Contrib.OneProof.RayClassShimura

/-!
# The CM dictionary at a CM point of `Y₃`, for an arbitrary order

Let `Q` be a QM abelian surface over `ℂ` uniformized `ι`-compatibly by
`Λ_τ = ι(𝒪)(τ, 1)ᵀ ⊂ ℂ²`, and let `τ` be the CM point of an embedding `q : K → B` of a quadratic field,
with reflex embedding `κ`: `ι(q(a))(τ, 1)ᵀ = κ(a)(τ, 1)ᵀ` for all `a ∈ K`. Put `R' = q⁻¹(𝒪)`, an order of
`K` which need not be maximal.

* (`endOf`) For `t ∈ R'`, multiplication by `κ(t)` on `ℂ²` preserves `Λ_τ`
  (`κ(t) ι(β)(τ, 1)ᵀ = ι(β q(t))(τ, 1)ᵀ`), hence is induced by a unique endomorphism of `Q.A`
  (realization of lattice maps, the Hom–lattice correspondence over `ℂ`).
* (`endOf_mem_center`) Such an endomorphism commutes with every endomorphism of `Q.A`: every
  endomorphism lifts to a `ℂ`-linear map of `ℂ²` (lifting), and a scalar commutes with it.
* (`comEquiv`) `t ↦ endOf t` is a ring isomorphism `R' ≃ End_𝒪(Q)`. Injectivity: a linear map with
  values in the discrete lattice is `0`. Surjectivity: an `𝒪`-linear endomorphism acts on `ℂ²` by a
  scalar `λ` with `λ(τ, 1)ᵀ = ι(β)(τ, 1)ᵀ`, `β ∈ 𝒪`; `β` commutes with `q(θ)` for `θ ∈ K ∖ ℚ`, and the
  centralizer of a non-central element of `B` is spanned by `1` and that element, so `β ∈ q(K)`.

In particular `End_𝒪(Q)` is the order `q⁻¹(𝒪)` itself (not only an order containing it, nor only one
contained in it), and it lies in the centre of `End(Q.A)`.
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.LeafQM _root_.LeafQM.AV ShimuraCFT RayClassCFT
open _root_.ZInQ.LeafPush2 (CPts IsUniformization)

/-! ## 1. Quaternion algebra: the centralizer of a non-central element -/

/-- In `B = (2, −3 | ℚ)`, an element commuting with an irrational element `γ` lies in `ℚ + ℚγ`: the commutator of the
pure parts is `(−2c₃ m₁, 2c₁ m₂, 2 m₃)` in the basis `i, j, k`, `mᵢ` the `2 × 2` minors, and
`c₁ = 2, c₃ = −3 ≠ 0`. -/
theorem exists_eq_add_smul_of_commute {β gm : LeafQM.B}
    (hgm : gm.imI ≠ 0 ∨ gm.imJ ≠ 0 ∨ gm.imK ≠ 0) (h : β * gm = gm * β) :
    ∃ r s : ℚ, β = algebraMap ℚ LeafQM.B r + s • gm := by
  have e1 := congrArg QuaternionAlgebra.imI h
  have e2 := congrArg QuaternionAlgebra.imJ h
  have e3 := congrArg QuaternionAlgebra.imK h
  simp only [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul] at e1 e2 e3
  have m1 : β.imJ * gm.imK = β.imK * gm.imJ := by linarith
  have m2 : β.imI * gm.imK = β.imK * gm.imI := by linarith
  have m3 : β.imI * gm.imJ = β.imJ * gm.imI := by linarith
  rcases hgm with h1 | h2 | h3
  · refine ⟨β.re - β.imI / gm.imI * gm.re, β.imI / gm.imI, ?_⟩
    ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> field_simp <;> linarith
  · refine ⟨β.re - β.imJ / gm.imJ * gm.re, β.imJ / gm.imJ, ?_⟩
    ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> field_simp <;> linarith
  · refine ⟨β.re - β.imK / gm.imK * gm.re, β.imK / gm.imK, ?_⟩
    ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> field_simp <;> linarith

/-- An element of `B` not in `ℚ` has a nonzero pure part. -/
theorem pure_ne_zero_of_not_rat {gm : LeafQM.B} (h : gm ∉ Set.range (algebraMap ℚ LeafQM.B)) :
    gm.imI ≠ 0 ∨ gm.imJ ≠ 0 ∨ gm.imK ≠ 0 := by
  by_contra hc
  push Not at hc
  apply h
  refine ⟨gm.re, ?_⟩
  ext <;> simp [QuaternionAlgebra.algebraMap_eq, hc.1, hc.2.1, hc.2.2]


/-! ## 2. The lattice `Λ_τ` and the CM point -/

/-- `ι(β)(τ, 1)ᵀ ∈ Λ_τ` for `β ∈ 𝒪` (the converse of `exists_of_mem_qmLattice`). -/
theorem mem_qmLattice_of_inO {τ : ℂ} (hτ : τ.im ≠ 0) {β : LeafQM.B} (hβ : InO β) :
    Matrix.mulVec (iotaC β) ![τ, 1] ∈ BPAnalytic.QM.qmLattice hτ := by
  obtain ⟨c, rfl⟩ := hβ
  rw [BPAnalytic.QM.qmLattice_eq, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨c, ?_⟩
  have e : LeafQM.ofInt c = ∑ i, c i • BPAnalytic.QM.oBasis i := by
    ext <;> simp [LeafQM.ofInt, BPAnalytic.QM.oBasis, Fin.sum_univ_four] <;> ring
  rw [e, map_sum, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Matrix.smul_mulVec]
  rfl

variable {K : Type} [Field K] [NumberField K]

/-- The order `q⁻¹(𝒪)` of `K` attached to an embedding `q : K → B`. -/
abbrev ordR (q : K →ₐ[ℚ] LeafQM.B) : Subring K := LeafQM.O.comap q.toRingHom

theorem mem_ordR {q : K →ₐ[ℚ] LeafQM.B} {t : K} : t ∈ ordR q ↔ InO (q t) := Iff.rfl

/-- A quadratic field has an irrational element. -/
theorem exists_irr_of_finrank_two (hK : Module.finrank ℚ K = 2) :
    ∃ θ : K, θ ∉ Set.range (algebraMap ℚ K) := by
  by_contra h
  push Not at h
  have htop : (⊥ : Subalgebra ℚ K) = ⊤ := by
    ext x
    simp only [Algebra.mem_top, iff_true]
    obtain ⟨r, rfl⟩ := h x
    exact Subalgebra.algebraMap_mem _ r
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
  omega

variable {τ : UpperHalfPlane}

/-- **Eigenvectors at a CM point.** If `τ` is the CM point of `q : K → B` (`K` quadratic) and
`(τ, 1)ᵀ` is an eigenvector of `ι(b)`, then `b ∈ q(K)`. -/
theorem mem_range_of_eig (hK : Module.finrank ℚ K = 2) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) {b : LeafQM.B} {mu : ℂ}
    (hb : Matrix.mulVec (iotaC b) ![(τ : ℂ), 1] = mu • ![(τ : ℂ), 1]) : ∃ t : K, q t = b := by
  obtain ⟨θ, hθ⟩ := exists_irr_of_finrank_two hK
  have hgm : q θ ∉ Set.range (algebraMap ℚ LeafQM.B) := by
    rintro ⟨r, hr⟩
    apply hθ
    refine ⟨r, q.toRingHom.injective ?_⟩
    show q (algebraMap ℚ K r) = q θ
    rw [AlgHom.commutes]; exact hr
  have hθv : Matrix.mulVec (iotaC (q θ)) ![(τ : ℂ), 1] = κ θ • ![(τ : ℂ), 1] := hcm θ
  have hcomm : b * q θ = q θ * b := by
    apply iota_eig_inj τ.im_pos.ne'
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hθv, Matrix.mulVec_smul,
      hb, Matrix.mulVec_smul, hθv, smul_smul, smul_smul, mul_comm]
  obtain ⟨r, s, hrs⟩ := exists_eq_add_smul_of_commute (pure_ne_zero_of_not_rat hgm) hcomm
  exact ⟨algebraMap ℚ K r + s • θ, by rw [map_add, AlgHom.commutes, map_smul, hrs]⟩

/-! ## 3. The dictionary `q⁻¹(𝒪) ≅ End_𝒪(Q)` -/

section Dict

variable {Q : QML3 ℂ} {Φu : (Fin 2 → ℂ) → CPts Q.A (RingHom.id ℂ)}

/-- Multiplication by `κ(t)`, `t ∈ q⁻¹(𝒪)`, preserves `Λ_τ`. -/
theorem smul_mem_lam (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ) (hcm : IsCMPoint q κ τ) {t : K}
    (ht : t ∈ ordR q) {x : Fin 2 → ℂ} (hx : x ∈ LamT τ) : κ t • x ∈ LamT τ := by
  obtain ⟨β, hβ, rfl⟩ := exists_of_mem_qmLattice τ.im_pos.ne' hx
  have hv : Matrix.mulVec (iotaC (q t)) ![(τ : ℂ), 1] = κ t • ![(τ : ℂ), 1] := hcm t
  have e : κ t • Matrix.mulVec (iotaC β) ![(τ : ℂ), 1] =
      Matrix.mulVec (iotaC (β * q t)) ![(τ : ℂ), 1] := by
    rw [map_mul, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  rw [e]
  exact mem_qmLattice_of_inO τ.im_pos.ne' (LeafQM.O.mul_mem hβ ht)

/-- A linear lift of an endomorphism preserves `Λ_τ` (the kernel of `Φu`). -/
theorem lam_of_lift (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    {N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)} {f : PkgI3.AbVar.End Q.A}
    (hf : ∀ z, Φu (N z) = Φu z ≫ f.hom) : ∀ z ∈ LamT τ, N z ∈ LamT τ := by
  intro z hz
  rw [← hU.2.1, hf z, (hU.2.1 z).2 hz]
  exact MonObj.one_comp _

/-- Two endomorphisms with the same linear lift are equal (realization is unique). -/
theorem end_eq_of_lift (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    {N : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)} {f g : PkgI3.AbVar.End Q.A}
    (hf : ∀ z, Φu (N z) = Φu z ≫ f.hom) (hg : ∀ z, Φu (N z) = Φu z ≫ g.hom) : f = g :=
  (hcorr.2 Q.A Q.A 2 2 (LamT τ) (LamT τ) Φu Φu (dim_two Q) (dim_two Q) hU hU N
    (lam_of_lift hU hf)).unique hf hg

/-- The endomorphism of `Q.A` induced by multiplication by `κ(t)`. -/
theorem exists_endOf (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) (t : ordR q) :
    ∃ f : PkgI3.AbVar.End Q.A, ∀ z, Φu (κ t • z) = Φu z ≫ f.hom := by
  obtain ⟨f, hf, -⟩ := hcorr.2 Q.A Q.A 2 2 (LamT τ) (LamT τ) Φu Φu (dim_two Q) (dim_two Q) hU hU
    (κ t • LinearMap.id) (fun z hz => smul_mem_lam q κ hcm t.2 hz)
  exact ⟨f, fun z => by simpa using hf z⟩

/-- `endOf t`: the endomorphism induced by `κ(t)`. -/
def endOf (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) (t : ordR q) : PkgI3.AbVar.End Q.A :=
  (exists_endOf hcorr hU q κ hcm t).choose

theorem endOf_spec (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) (t : ordR q) (z : Fin 2 → ℂ) :
    Φu (κ t • z) = Φu z ≫ (endOf hcorr hU q κ hcm t).hom :=
  (exists_endOf hcorr hU q κ hcm t).choose_spec z

theorem endOf_unique (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) (t : ordR q) {f : PkgI3.AbVar.End Q.A}
    (hf : ∀ z, Φu (κ t • z) = Φu z ≫ f.hom) : f = endOf hcorr hU q κ hcm t :=
  end_eq_of_lift (N := κ t • LinearMap.id) hcorr hU (fun z => by simpa using hf z)
    (fun z => by simpa using endOf_spec hcorr hU q κ hcm t z)

/-- **`endOf t` is central in `End(Q.A)`.** -/
theorem endOf_mem_center (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) (t : ordR q) (g : PkgI3.AbVar.End Q.A) :
    endOf hcorr hU q κ hcm t * g = g * endOf hcorr hU q κ hcm t := by
  set e := endOf hcorr hU q κ hcm t
  have hHL := ZInQ.HomUnify.homLinearLift_of_corr hcorr
  set M := liftM hHL hU g
  have hM : ∀ z, Φu (M z) = Φu z ≫ g.hom := liftM_spec hHL hU g
  apply end_eq_of_lift (N := (κ t • LinearMap.id) ∘ₗ M) hcorr hU
  · intro z
    show Φu (κ t • M z) = Φu z ≫ (g.hom ≫ e.hom)
    rw [endOf_spec hcorr hU q κ hcm t, hM, Category.assoc]
  · intro z
    show Φu (κ t • M z) = Φu z ≫ (e.hom ≫ g.hom)
    rw [← map_smul, hM, endOf_spec hcorr hU q κ hcm t, Category.assoc]

/-- The ring homomorphism `q⁻¹(𝒪) → End(Q.A)`. -/
def endHom (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) : ordR q →+* PkgI3.AbVar.End Q.A where
  toFun := endOf hcorr hU q κ hcm
  map_one' := by
    symm; apply endOf_unique hcorr hU q κ hcm
    intro z
    show Φu (κ ((1 : ordR q) : K) • z) = Φu z ≫ 𝟙 _
    simp
  map_mul' t t' := by
    symm; apply endOf_unique hcorr hU q κ hcm
    intro z
    show Φu (κ ((t * t' : ordR q) : K) • z) =
      Φu z ≫ ((endOf hcorr hU q κ hcm t').hom ≫ (endOf hcorr hU q κ hcm t).hom)
    rw [Subring.coe_mul, map_mul, mul_smul, endOf_spec hcorr hU q κ hcm t,
      endOf_spec hcorr hU q κ hcm t', Category.assoc]
  map_zero' := by
    symm; apply endOf_unique hcorr hU q κ hcm
    intro z
    show Φu (κ ((0 : ordR q) : K) • z) = Φu z ≫ (1 : Q.A.X ⟶ Q.A.X)
    rw [ZeroMemClass.coe_zero, map_zero, zero_smul, (hU.2.1 0).2 (Submodule.zero_mem _),
      MonObj.comp_one]
  map_add' t t' := by
    symm; apply endOf_unique hcorr hU q κ hcm
    intro z
    show Φu (κ ((t + t' : ordR q) : K) • z) =
      Φu z ≫ ((endOf hcorr hU q κ hcm t).hom * (endOf hcorr hU q κ hcm t').hom)
    rw [Subring.coe_add, map_add, add_smul, hU.1, endOf_spec hcorr hU q κ hcm t,
      endOf_spec hcorr hU q κ hcm t', MonObj.comp_mul]

theorem endHom_injective (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) : Function.Injective (endHom hcorr hU q κ hcm) := by
  intro t t' h
  have h' : ∀ z, Φu ((κ t • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) =
      Φu ((κ t' • LinearMap.id : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z) := by
    intro z
    show Φu (κ t • z) = Φu (κ t' • z)
    rw [endOf_spec hcorr hU q κ hcm t, endOf_spec hcorr hU q κ hcm t']
    exact congrArg (fun f : PkgI3.AbVar.End Q.A => Φu z ≫ f.hom) h
  have hM := lift_unique hU h'
  have hk : κ t = κ t' := by
    have := congrArg (fun M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) => M ![1, 0] 0) hM
    simpa using this
  exact Subtype.ext (κ.injective hk)

/-- **The CM dictionary.** `endHom` maps `q⁻¹(𝒪)` onto `End_𝒪(Q)`: every `𝒪`-linear endomorphism
is `endOf t` for some `t ∈ q⁻¹(𝒪)`. -/
theorem exists_endOf_eq (hcorr : ZInQ.HomUnify.HomLatticeCorr) (hK : Module.finrank ℚ K = 2)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (hι : HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) {φ : PkgI3.AbVar.End Q.A} (hφ : φ ∈ com Q.q) :
    ∃ t : ordR q, endHom hcorr hU q κ hcm t = φ := by
  have hτ := τ.im_pos.ne'
  have hHL := ZInQ.HomUnify.homLinearLift_of_corr hcorr
  set v : Fin 2 → ℂ := ![(τ : ℂ), 1] with hv
  set lam : ℂ := liftM hHL hU φ ![1, 0] 0
  have hlam : ∀ z, liftM hHL hU φ z = lam • z := fun z => liftM_scalar hHL hU hι hφ z
  have hmem : lam • v ∈ LamT τ := by
    rw [← hlam v, ← hU.2.1, liftM_spec hHL hU, (hU.2.1 v).2 (qmVec0_mem hτ)]
    exact MonObj.one_comp _
  obtain ⟨β, hβO, hβ⟩ := exists_of_mem_qmLattice hτ hmem
  obtain ⟨t, rfl⟩ := mem_range_of_eig hK q κ hcm hβ
  have ht : t ∈ ordR q := hβO
  have hk : κ t = lam := by
    have h1 : Matrix.mulVec (iotaC (q t)) v = κ t • v := hcm t
    have h2 := congrFun (h1.symm.trans hβ) 1
    simpa [hv] using h2
  refine ⟨⟨t, ht⟩, (endOf_unique hcorr hU q κ hcm ⟨t, ht⟩ (f := φ) (fun z => ?_)).symm⟩
  show Φu (κ t • z) = Φu z ≫ φ.hom
  rw [hk, ← hlam z, liftM_spec hHL hU]

/-- `endHom` lands in `End_𝒪(Q)` (indeed in the centre of `End(Q.A)`). -/
theorem endHom_mem_com (hcorr : ZInQ.HomUnify.HomLatticeCorr)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) (t : ordR q) : endHom hcorr hU q κ hcm t ∈ com Q.q := by
  rw [com, Subring.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  exact (endOf_mem_center hcorr hU q κ hcm t _).symm

/-- **The CM dictionary as a ring isomorphism** `q⁻¹(𝒪) ≃+* End_𝒪(Q)`, for every order. -/
def comEquiv (hcorr : ZInQ.HomUnify.HomLatticeCorr) (hK : Module.finrank ℚ K = 2)
    (hU : IsUniformization (RingHom.id ℂ) (LamT τ) Φu)
    (hι : HDec.HSyn.G0Split.FibreQM.IotaCompatible Q Φu) (q : K →ₐ[ℚ] LeafQM.B) (κ : K →+* ℂ)
    (hcm : IsCMPoint q κ τ) : ordR q ≃+* com Q.q :=
  RingEquiv.ofBijective
    ((endHom hcorr hU q κ hcm).codRestrict (com Q.q) (endHom_mem_com hcorr hU q κ hcm))
    ⟨fun t t' h => endHom_injective hcorr hU q κ hcm (congrArg Subtype.val h),
     fun φ => by
       obtain ⟨t, ht⟩ := exists_endOf_eq hcorr hK hU hι q κ hcm φ.2
       exact ⟨t, Subtype.ext ht⟩⟩

end Dict

end HDec.CMBranch.CMjReroute
