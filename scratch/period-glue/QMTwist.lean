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
  haveI : DiscreteTopology Λ := by rw [hΛ]; unfold BPAnalytic.QM.qmLattice; infer_instance
  haveI : DiscreteTopology Λ' := by rw [hΛ']; unfold BPAnalytic.QM.qmLattice; infer_instance
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
    refine ⟨α, LinearEquiv.ofLinear M N hMN hNM, fun z => ⟨fun hz => ?_, fun hz => ?_⟩,
      fun a z => ?_⟩
    · exact lift_maps_lattice hU hU' hM z hz
    · have := lift_maps_lattice hU' hU hN _ hz
      simpa [LinearEquiv.ofLinear_apply, ← LinearMap.comp_apply, hNM] using this
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
      rw [hMeq, hc', hφ, Category.assoc]
    exact congrArg PkgI3.AbVar.Hom.hom (e1.trans e2.symm)

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.qmTwistLattice_of
