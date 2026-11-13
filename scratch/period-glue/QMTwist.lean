import PGBase
/-! # period-glue: `QMTwistLattice` from the `Hom` form of T11a and a lattice statement

Task period-glue, 2026-11-13. `QMTwistLattice` (period-map, `PGBase`, unchanged) is proved from
* `T11aRiemannHom` (**LEAF**, textbook: the `Hom` form of T11a), and
* `QMLatticeTwistAlg` (**GLUE**, pure linear algebra over `ℚ`/`ℂ`: the twist relation on lattices
  is the `Γ*`-relation on `ℍ`),
by `qmTwistLattice_of`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH

/-- **LEAF (T11a, `Hom` form; textbook).** For abelian varieties `A, A'/ℂ` of dimension `g` with
analytic uniformizations `Φ : ℂ^g → A(ℂ)`, `Φ' : ℂ^g → A'(ℂ)` with kernels `Λ, Λ'`: every
`ℂ`-linear `M` with `MΛ ⊆ Λ'` is the analytic representation of exactly one homomorphism
`f : A → A'` (`Φ'(Mz) = f(Φ z)`), and every homomorphism has an analytic representation.

Sources: for complex tori, `Hom(ℂ^g/Λ, ℂ^g/Λ') = {M : MΛ ⊆ Λ'}` (Mumford, *Abelian Varieties*,
§1, the analytic description of homomorphisms; Birkenhake–Lange, *Complex Abelian Varieties*,
Prop. 1.2.1; locators UNVERIFIED), and every holomorphic homomorphism of abelian varieties is
algebraic (GAGA: Serre, *Géométrie algébrique et géométrie analytique*, 1956, Thm. 3 / Cor.;
Mumford §1 / §4; UNVERIFIED). The kernel's `T11aRiemannEnd` is the case `A = A'`, `Φ = Φ'`
(this statement is the same text with `Hom A A'` in place of `End A`). -/
def T11aRiemannHom : Prop :=
  ∀ (A A' : PkgI3.AbVar ℂ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (Φ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → A'.dim = (g : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) Λ Φ → IsUniformization (RingHom.id ℂ) Λ' Φ' →
    (∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ Λ, M z ∈ Λ') →
      ∃! f : PkgI3.AbVar.Hom A A', ∀ z, Φ' (M z) = Φ z ≫ f.hom) ∧
    (∀ f : PkgI3.AbVar.Hom A A', ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      ∀ z, Φ' (M z) = Φ z ≫ f.hom)

/-- `T11aRiemannEnd` is the special case `A = A'` of `T11aRiemannHom` (proved). -/
theorem t11aRiemannEnd_of_hom (h : T11aRiemannHom) : T11aRiemannEnd :=
  fun A g Λ Φ hA hU => h A A g Λ Λ Φ Φ hA hA hU hU

/-- **GLUE (pure algebra: twists of QM lattices).** For `τ, τ' ∈ ℍ`: there are `α ∈ Aut(𝒪)` and
a `ℂ`-linear automorphism `M` of `ℂ²` with `MΛ_τ = Λ_τ'` and `M ∘ ι(α(a)) = ι(a) ∘ M` for all
`a ∈ 𝒪` iff `τ' ∈ Γ*τ`.

Why true (model argument, Shimura 1967 §1-2 for the general statement):
(⇐) `g = ι(u) ∈ Γ*` with `u ∈ N_B(𝒪)`, `nrd u > 0`: take `M = (cτ + d)⁻¹ι(u)` and
`α(a) = u⁻¹au` (in `Aut(𝒪)` because `u` normalizes `𝒪`); then
`MΛ_τ = (cτ+d)⁻¹ι(u𝒪u⁻¹)ι(u)v_τ = ι(𝒪)v_τ' = Λ_τ'`.
(⇒) `α` extends to a `ℚ`-algebra automorphism of `B = 𝒪 ⊗ ℚ`, inner by Skolem–Noether (the
kernel's `TSkolemKW.leafSkolemNoether`): `α(a) = u⁻¹au`, `u ∈ N_B(𝒪)`. Then `M ι(u)⁻¹`
commutes with `ι(B)`, which spans `M₂(ℂ)`, so `M = c ι(u)`, `c ∈ ℂ^×`. From `MΛ_τ = Λ_τ'`:
`v_τ' = c ι(x)v_τ` for some `x ∈ 𝒪u`, and `ι(𝒪)ι(x)v_τ = ι(𝒪)ι(u)v_τ`; `b ↦ ι(b)v_τ` is
injective on `B` (`ι(b)` is invertible for `b ≠ 0`, `B` a division algebra, and `v_τ ≠ 0`), so
`𝒪x = 𝒪u`, `x = eu` with `e ∈ 𝒪^×`, so `x ∈ N_B(𝒪)`; `ι(x)τ = τ' ∈ ℍ` forces
`det ι(x) = nrd x > 0`, so `g = ι(x) ∈ Γ*` and `gτ = τ'`. Size: medium (Skolem–Noether is
proved in the kernel; the rest is `2 × 2` linear algebra over `ℚ(√2)`). -/
def QMLatticeTwistAlg : Prop :=
  ∀ τ τ' : UpperHalfPlane,
    ((∃ α : LeafQM.O ≃+* LeafQM.O, ∃ M : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
        (∀ z, z ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' ↔
          M z ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne') ∧
        ∀ (a : LeafQM.O) (z : Fin 2 → ℂ), M ((qmMat (α a)).mulVec z) = (qmMat a).mulVec (M z)) ↔
      ∃ g ∈ PkgI1.GammaStar, g • τ = τ')

/-- A homomorphism keeps the identity point. -/
theorem one_comp_hom {A A' : PkgI3.AbVar ℂ} (f : PkgI3.AbVar.Hom A A') :
    (1 : CPts A (RingHom.id ℂ)) ≫ f.hom = 1 := MonObj.one_comp f.hom

/-- Points of the kernel: a map `M` lifting a homomorphism sends `Λ` into `Λ'`. -/
theorem lift_maps_lattice {A A' : PkgI3.AbVar ℂ} {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)}
    {Φ : (Fin 2 → ℂ) → CPts A (RingHom.id ℂ)} {Φ' : (Fin 2 → ℂ) → CPts A' (RingHom.id ℂ)}
    (hU : IsUniformization (RingHom.id ℂ) Λ Φ) (hU' : IsUniformization (RingHom.id ℂ) Λ' Φ')
    {M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)} {f : PkgI3.AbVar.Hom A A'}
    (hM : ∀ z, Φ' (M z) = Φ z ≫ f.hom) : ∀ z ∈ Λ, M z ∈ Λ' := by
  intro z hz
  rw [← hU'.2.1, hM, (hU.2.1 z).mpr hz, one_comp_hom]

theorem qmTwistLattice_of (hH : T11aRiemannHom) (hA : QMLatticeTwistAlg) : QMTwistLattice := by
  intro Q Q' τ τ' ⟨Φ, hU, hc⟩ ⟨Φ', hU', hc'⟩
  set Λ := BPAnalytic.QM.qmLattice τ.im_pos.ne' with hΛ
  set Λ' := BPAnalytic.QM.qmLattice τ'.im_pos.ne' with hΛ'
  have : DiscreteTopology Λ := by rw [hΛ]; unfold BPAnalytic.QM.qmLattice; infer_instance
  have : DiscreteTopology Λ' := by rw [hΛ']; unfold BPAnalytic.QM.qmLattice; infer_instance
  have H := hH Q.A Q'.A 2 Λ Λ' Φ Φ' Q.surface Q'.surface hU hU'
  have H' := hH Q'.A Q.A 2 Λ' Λ Φ' Φ Q'.surface Q.surface hU' hU
  have HQ := hH Q.A Q.A 2 Λ Λ Φ Φ Q.surface Q.surface hU hU
  have HQ' := hH Q'.A Q'.A 2 Λ' Λ' Φ' Φ' Q'.surface Q'.surface hU' hU'
  rw [← hA τ τ']
  constructor
  · rintro ⟨α, ⟨e⟩⟩
    obtain ⟨M, hM⟩ := H.2 e.φ
    obtain ⟨N, hN⟩ := H'.2 e.ψ
    have hNM : N ∘ₗ M = LinearMap.id := lift_unique hU fun z => by
      rw [LinearMap.comp_apply, hN, hM, Category.assoc, e.left, Category.comp_id,
        LinearMap.id_apply]
    have hMN : M ∘ₗ N = LinearMap.id := lift_unique hU' fun z => by
      rw [LinearMap.comp_apply, hM, hN, Category.assoc, e.right, Category.comp_id,
        LinearMap.id_apply]
    refine ⟨α, LinearEquiv.ofLinearMap M N hMN hNM, fun z => ⟨fun hz => ?_, fun hz => ?_⟩,
      fun a z => ?_⟩
    · exact lift_maps_lattice hU hU' hM z hz
    · have := lift_maps_lattice hU' hU hN _ hz
      simpa [LinearEquiv.coe_ofLinearMap, ← LinearMap.comp_apply, hNM] using this
    · show M ((qmMat (α a)).mulVec z) = (qmMat a).mulVec (M z)
      have key : M ∘ₗ Matrix.toLin' (qmMat (α a)) = Matrix.toLin' (qmMat a) ∘ₗ M :=
        lift_unique hU' fun w => by
          rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
            Matrix.toLin'_apply, hM, hc, hc', hM, Category.assoc, Category.assoc]
          congr 1
          exact e.equivariant a
      have := LinearMap.congr_fun key z
      simpa [Matrix.toLin'_apply] using this
  · rintro ⟨α, M, hML, hMeq⟩
    have hMΛ : ∀ z ∈ Λ, (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈ Λ' :=
      fun z hz => (hML z).mp hz
    have hNΛ : ∀ z ∈ Λ', (M.symm : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) z ∈ Λ := fun z hz => by
      rw [hML]; simpa using hz
    obtain ⟨φ, hφ, -⟩ := H.1 M hMΛ
    obtain ⟨ψ, hψ, -⟩ := H'.1 M.symm hNΛ
    have hφ' : ∀ z, Φ' (M z) = Φ z ≫ φ.hom := hφ
    -- uniqueness of the endomorphism lifting `id`
    obtain ⟨one, -, hone⟩ := HQ.1 LinearMap.id (fun z hz => hz)
    obtain ⟨one', -, hone'⟩ := HQ'.1 LinearMap.id (fun z hz => hz)
    have hleft : φ.hom ≫ ψ.hom = 𝟙 _ := by
      have h1 := hone (PkgI3.AbVar.Hom.mk' (φ.hom ≫ ψ.hom)) fun z => by
        rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hφ, ← hψ]; simp
      have h2 := hone 1 fun z => by
        change Φ z = Φ z ≫ 𝟙 _
        rw [Category.comp_id]
      exact congrArg PkgI3.AbVar.Hom.hom (h1.trans h2.symm)
    have hright : ψ.hom ≫ φ.hom = 𝟙 _ := by
      have h1 := hone' (PkgI3.AbVar.Hom.mk' (ψ.hom ≫ φ.hom)) fun z => by
        rw [PkgI3.AbVar.Hom.hom_mk', ← Category.assoc, ← hψ, ← hφ]; simp
      have h2 := hone' 1 fun z => by
        change Φ' z = Φ' z ≫ 𝟙 _
        rw [Category.comp_id]
      exact congrArg PkgI3.AbVar.Hom.hom (h1.trans h2.symm)
    refine ⟨α, ⟨{ φ := φ, ψ := ψ, left := hleft, right := hright, equivariant := ?_ }⟩⟩
    intro a
    -- both sides lift `M ∘ ι(α a) = ι(a) ∘ M`
    have hlat : ∀ z ∈ Λ, (M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ))
        ((qmMat (α a)).mulVec z) ∈ Λ' := by
      intro z hz
      apply hMΛ
      have := lift_maps_lattice hU hU (f := Q.q.iota (α a))
        (M := Matrix.toLin' (qmMat (α a))) (fun w => by rw [Matrix.toLin'_apply, hc]) z hz
      simpa [Matrix.toLin'_apply] using this
    obtain ⟨f, -, hf⟩ := H.1 ((M : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ)) ∘ₗ
      Matrix.toLin' (qmMat (α a))) (fun z hz => by simpa [Matrix.toLin'_apply] using hlat z hz)
    have e1 := hf (PkgI3.AbVar.Hom.mk' ((Q.q.iota (α a)).hom ≫ φ.hom)) fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', LinearMap.comp_apply, Matrix.toLin'_apply, hφ, hc,
        Category.assoc]
    have e2 := hf (PkgI3.AbVar.Hom.mk' (φ.hom ≫ (Q'.q.iota a).hom)) fun z => by
      rw [PkgI3.AbVar.Hom.hom_mk', LinearMap.comp_apply, Matrix.toLin'_apply]
      change Φ' (M ((qmMat (α a)).mulVec z)) = _
      rw [hMeq, hc', hφ', Category.assoc]
    exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)

/-! ## `QMLatticeTwistAlg`, direction `τ' ∈ Γ*τ ⇒ twist` (proved) -/

open scoped Matrix

/-- `ι(x)` as a complex matrix. -/
def cM (x : LeafQM.B) : Matrix (Fin 2) (Fin 2) ℂ := (BPAnalytic.QM.iota x).map (fun r : ℝ => (r : ℂ))

theorem qmMat_eq (a : LeafQM.O) : qmMat a = cM a := rfl

theorem cM_mul (x y : LeafQM.B) : cM (x * y) = cM x * cM y := by
  unfold cM
  have : BPAnalytic.QM.iota (x * y) = BPAnalytic.QM.iota x * BPAnalytic.QM.iota y :=
    PeriodMap.iota_mul x y
  rw [this]
  exact Matrix.map_mul (f := Complex.ofRealHom)

theorem cM_one : cM 1 = 1 := by
  unfold cM
  have : BPAnalytic.QM.iota 1 = 1 := PeriodMap.iota_one
  rw [this]
  exact Matrix.map_one _ (by simp) (by simp)

theorem latVec_eq (b : LeafQM.B) (τ : ℂ) : BPAnalytic.QM.latVec b τ = cM b *ᵥ ![τ, 1] := rfl

theorem latVec_mul (x y : LeafQM.B) (τ : ℂ) :
    BPAnalytic.QM.latVec (x * y) τ = cM x *ᵥ BPAnalytic.QM.latVec y τ := by
  rw [latVec_eq, latVec_eq, cM_mul, Matrix.mulVec_mulVec]

theorem latVec_ofInt (c : Fin 4 → ℤ) (τ : ℂ) :
    ∑ i, c i • BPAnalytic.QM.qmVec τ i = BPAnalytic.QM.latVec (LeafQM.ofInt c) τ := by
  ext k
  fin_cases k <;>
    simp [BPAnalytic.QM.qmVec, BPAnalytic.QM.latVec, BPAnalytic.QM.iota, BPAnalytic.QM.oBasis,
      LeafQM.ofInt, BPAnalytic.QM.Mi, BPAnalytic.QM.Mj, Fin.sum_univ_four, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two] <;> ring

theorem mem_qmLattice_iff {τ : ℂ} (hτ : τ.im ≠ 0) (z : Fin 2 → ℂ) :
    z ∈ BPAnalytic.QM.qmLattice hτ ↔ ∃ b : LeafQM.B, b ∈ LeafQM.O ∧ z = BPAnalytic.QM.latVec b τ := by
  rw [BPAnalytic.QM.qmLattice_eq, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨LeafQM.ofInt c, ⟨c, rfl⟩, by rw [← hc, latVec_ofInt]⟩
  · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, latVec_ofInt c τ⟩

theorem inO_iff (x : LeafQM.B) : PkgI1.InO x ↔ x ∈ LeafQM.O := by
  refine ⟨fun h => mem_O_of_inO h, fun ⟨n, hn⟩ => ⟨n, ?_⟩⟩
  rw [hn]
  ext <;> simp [LeafQM.ofInt, PkgI1.oBasis, Fin.sum_univ_four] <;> ring

/-- **`QMLatticeTwistAlg`, (⇐) (proved).** -/
theorem qmLatticeTwistAlg_mpr (τ τ' : UpperHalfPlane) (hg : ∃ g ∈ PkgI1.GammaStar, g • τ = τ') :
    ∃ α : LeafQM.O ≃+* LeafQM.O, ∃ M : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ),
      (∀ z, z ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' ↔
        M z ∈ BPAnalytic.QM.qmLattice τ'.im_pos.ne') ∧
      ∀ (a : LeafQM.O) (z : Fin 2 → ℂ), M ((qmMat (α a)).mulVec z) = (qmMat a).mulVec (M z) := by
  obtain ⟨g, ⟨x, ⟨y, hxy, hyx, hN⟩, hgx, hdet⟩, hgτ⟩ := hg
  have hN' : ∀ a : LeafQM.B, a ∈ LeafQM.O → y * a * x ∈ LeafQM.O ∧ x * a * y ∈ LeafQM.O := by
    intro a ha
    obtain ⟨h1, h2⟩ := hN a ((inO_iff a).mpr ha)
    exact ⟨(inO_iff _).mp h2, (inO_iff _).mp h1⟩
  have key1 : ∀ a : LeafQM.B, x * (y * a * x) * y = a := fun a => by
    calc x * (y * a * x) * y = (x * y) * a * (x * y) := by noncomm_ring
      _ = a := by rw [hxy, _root_.one_mul, _root_.mul_one]
  have key2 : ∀ a : LeafQM.B, y * (x * a * y) * x = a := fun a => by
    calc y * (x * a * y) * x = (y * x) * a * (y * x) := by noncomm_ring
      _ = a := by rw [hyx, _root_.one_mul, _root_.mul_one]
  let α : LeafQM.O ≃+* LeafQM.O :=
    { toFun := fun a => ⟨y * a * x, (hN' a a.2).1⟩
      invFun := fun a => ⟨x * a * y, (hN' a a.2).2⟩
      left_inv := fun a => Subtype.ext (key1 a)
      right_inv := fun a => Subtype.ext (key2 a)
      map_mul' := fun a b => Subtype.ext (by
        change y * ((a : LeafQM.B) * b) * x = (y * a * x) * (y * b * x)
        calc y * ((a : LeafQM.B) * b) * x = y * a * 1 * b * x := by noncomm_ring
          _ = y * a * (x * y) * b * x := by rw [hxy]
          _ = (y * a * x) * (y * b * x) := by noncomm_ring)
      map_add' := fun a b => Subtype.ext (by
        change y * ((a : LeafQM.B) + b) * x = y * a * x + y * b * x
        noncomm_ring) }
  have hα : ∀ a : LeafQM.O, ((α a : LeafQM.O) : LeafQM.B) = y * a * x := fun a => rfl
  have hgM : (g : Matrix (Fin 2) (Fin 2) ℝ).map (fun r : ℝ => (r : ℂ)) = cM x := by
    rw [hgx]; rfl
  set c := UpperHalfPlane.denom g τ with hc
  have hc0 : c ≠ 0 := UpperHalfPlane.denom_ne_zero g τ
  have hXY : cM x * cM y = 1 := by rw [← cM_mul, hxy, cM_one]
  have hYX : cM y * cM x = 1 := by rw [← cM_mul, hyx, cM_one]
  let Mf : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := c⁻¹ • Matrix.toLin' (cM x)
  let Mg : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) := c • Matrix.toLin' (cM y)
  have h1 : Mf ∘ₗ Mg = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    simp only [Mf, Mg, LinearMap.comp_apply, LinearMap.smul_apply, Matrix.toLin'_apply,
      LinearMap.id_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec,
      smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have h2 : Mg ∘ₗ Mf = LinearMap.id := by
    refine LinearMap.ext fun z => ?_
    simp only [Mf, Mg, LinearMap.comp_apply, LinearMap.smul_apply, Matrix.toLin'_apply,
      LinearMap.id_apply, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hYX, Matrix.one_mulVec,
      smul_smul, mul_inv_cancel₀ hc0, one_smul]
  let M : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ) := LinearEquiv.ofLinearMap Mf Mg h1 h2
  have hM : ∀ z, M z = c⁻¹ • (cM x *ᵥ z) := fun z => rfl
  -- `ι(x)(τ, 1)ᵀ = c (τ', 1)ᵀ`
  have hτ' : ((τ' : UpperHalfPlane) : ℂ) = UpperHalfPlane.num g τ / c := by
    rw [← hgτ]
    exact UpperHalfPlane.coe_smul_of_det_pos (by rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hdet) τ
  have hv : cM x *ᵥ ![(τ : ℂ), 1] = c • ![((τ' : UpperHalfPlane) : ℂ), 1] := by
    rw [← hgM, hτ']
    ext k
    fin_cases k
    · have hc0' : (τ : ℂ) * ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) +
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := by
        have : ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * τ +
            ((g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) ≠ 0 := hc0
        rwa [mul_comm] at this
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.num, hc,
        UpperHalfPlane.denom]
      field_simp
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hc, UpperHalfPlane.denom]
  have hlat : ∀ b : LeafQM.B, M (BPAnalytic.QM.latVec b τ) =
      BPAnalytic.QM.latVec (x * b * y) τ' := by
    intro b
    rw [hM, ← latVec_mul]
    have : x * b = (x * b * y) * x := by
      calc x * b = x * b * 1 := (_root_.mul_one _).symm
        _ = x * b * (y * x) := by rw [hyx]
        _ = (x * b * y) * x := by noncomm_ring
    conv_lhs => rw [this]
    rw [latVec_mul, latVec_eq x, hv, Matrix.mulVec_smul, smul_smul, inv_mul_cancel₀ hc0,
      one_smul, ← latVec_eq]
  refine ⟨α, M, fun z => ⟨fun hz => ?_, fun hz => ?_⟩, fun a z => ?_⟩
  · obtain ⟨b, hb, rfl⟩ := (mem_qmLattice_iff _ z).mp hz
    rw [hlat]
    exact (mem_qmLattice_iff _ _).mpr ⟨_, (hN' b hb).2, rfl⟩
  · obtain ⟨b', hb', hzb⟩ := (mem_qmLattice_iff _ _).mp hz
    have : z = BPAnalytic.QM.latVec (y * b' * x) τ := by
      apply M.injective
      rw [hzb, hlat, key1]
    rw [this]
    exact (mem_qmLattice_iff _ _).mpr ⟨_, (hN' b' hb').1, rfl⟩
  · have e : x * (y * (a : LeafQM.B) * x) = a * x := by
      calc x * (y * (a : LeafQM.B) * x) = (x * y) * a * x := by noncomm_ring
        _ = a * x := by rw [hxy, _root_.one_mul]
    rw [hM, hM, qmMat_eq, qmMat_eq, hα, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← cM_mul, ← cM_mul, e]

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.qmTwistLattice_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.qmLatticeTwistAlg_mpr
