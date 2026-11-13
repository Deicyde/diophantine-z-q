/-! ## period-glue: `QMTwistLattice` from the `Hom` form of T11a

Task period-glue, 2026-11-13. `PeriodMapH.QMTwistLattice` (period-map's `part_heavy.lean`,
unchanged) is proved from one new textbook leaf, `T11aRiemannHom` (the `Hom` form of the kernel's
T11a: Riemann/GAGA for homomorphisms between two complex abelian varieties), in
`qmTwistLattice_of`. Skolem–Noether for `B` is made explicit (`PeriodGlueTL.exists_intertwiner`).

(⇐) `g = ι(x) ∈ Γ*` with `gτ = τ'` gives `T = (cτ+d)⁻¹ι(x)` with `TΛ_τ = Λ_τ'` and
`T ι(x⁻¹ a x) = ι(a) T`; T11a-Hom lifts `T`, `T⁻¹` to mutually inverse homomorphisms, `𝒪`-equivariant
for the twist `α = x⁻¹(·)x` (uniqueness of lifts).
(⇒) An isomorphism of the twisted pair has analytic representation `T` with `TΛ_τ = Λ_τ'` and
`T ι(α a) = ι(a) T`; with `u ≠ 0`, `a u = u α(a)` (explicit Skolem–Noether), `T ι(ū)` commutes with
`ι(i), ι(j)`, so `T = c ι(u)`; comparing `(τ', 1) ∈ Λ_τ'` and `T(τ, 1) ∈ Λ_τ'` gives `o₁ ∈ 𝒪^×` with
`(τ', 1) ∈ ℂ ι(u o₁)(τ, 1)`, and `x = u o₁` normalizes `𝒪`; a real matrix carrying `ℍ` into `ℍ` has
positive determinant. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlueH

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMapH HSyn.G0Split.FibreQM.PeriodGlueTL
open Matrix

/-- **TEXTBOOK leaf (T11(a), Riemann/GAGA for homomorphisms).** For abelian varieties `A, A'` over
`ℂ` of dimension `g` with uniformizations `Φ, Φ'` (kernels `Λ, Λ'`) at `σ = id`, the homomorphisms
`A → A'` are exactly the `ℂ`-linear maps `M` of `ℂ^g` with `MΛ ⊆ Λ'`: each such `M` is induced by a
unique homomorphism `f` (`Φ'(Mz) = f ∘ Φ(z)`), and each `f` is induced by some `M`.

Source: Mumford, *Abelian varieties*, §1 (Hom of complex tori) and §2 (Riemann's theorem); Birkenhake–Lange,
*Complex abelian varieties*, Prop. 1.2.1 (`Hom(X, X') ≅ {M : MΛ ⊆ Λ'}` for complex tori); GAGA (Serre
1956) for "holomorphic ⇒ algebraic" (locators UNVERIFIED). The kernel's `T11aRiemannEnd` is the case
`A = A'`. Published (textbook). -/
def T11aRiemannHom : Prop :=
  ∀ (A A' : PkgI3.AbVar ℂ) (g : ℕ) (Λ Λ' : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (Φ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → A'.dim = (g : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) Λ Φ → IsUniformization (RingHom.id ℂ) Λ' Φ' →
    (∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ z ∈ Λ, M z ∈ Λ') →
      ∃! f : PkgI3.AbVar.Hom A A', ∀ z, Φ' (M z) = Φ z ≫ f.hom) ∧
    (∀ f : PkgI3.AbVar.Hom A A', ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ z, Φ' (M z) = Φ z ≫ f.hom)

/-- `T11aRiemannHom` contains the kernel's `T11aRiemannEnd` (proved). -/
theorem t11aEnd_of_hom (h : T11aRiemannHom) : T11aRiemannEnd :=
  fun A g Λ Φ hA hU => h A A g Λ Λ Φ Φ hA hA hU hU

/-! ### Conversions -/

theorem qmMat_eq (a : LeafQM.O) : qmMat a = Mc (a : LeafQM.B) := rfl

theorem inO_iff_mem (x : LeafQM.B) : x ∈ LeafQM.O ↔ ∃ n, x = ofIntB n := Iff.rfl

theorem inO_of_mem_O {x : PkgI1.B} (hx : (x : LeafQM.B) ∈ LeafQM.O) : PkgI1.InO x := by
  obtain ⟨n, hn⟩ := hx
  exact ⟨n, by rw [hn]; ext <;> simp [LeafQM.ofInt, PkgI1.oBasis, Fin.sum_univ_four] <;> ring⟩

theorem ofIntB_mem (n : Fin 4 → ℤ) : ofIntB n ∈ LeafQM.O := ⟨n, rfl⟩

theorem iota_eq (x : PkgI1.B) : PkgI1.iota x = BPAnalytic.QM.iota x := rfl

/-! ### The lattice `Λ_τ` -/

theorem vec_mem (τ : UpperHalfPlane) : (![(τ : ℂ), 1] : Fin 2 → ℂ) ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' := by
  refine (mem_qmLattice_iff (τ := (τ : ℂ)) τ.im_pos.ne' _).mpr ?_
  exact ⟨![1, 0, 0, 0], by
    rw [show ofIntB ![1, 0, 0, 0] = 1 by ext <;> simp [ofIntB]]
    ext i; fin_cases i <;> simp [Mc_explicit, Matrix.mulVec, dotProduct, Fin.sum_univ_two]⟩

theorem mem_iff (τ : UpperHalfPlane) (z : Fin 2 → ℂ) :
    z ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' ↔
      ∃ o : LeafQM.B, o ∈ LeafQM.O ∧ z = Mc o *ᵥ ![(τ : ℂ), 1] := by
  refine (mem_qmLattice_iff (τ := (τ : ℂ)) τ.im_pos.ne' z).trans ?_
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨_, ofIntB_mem n, rfl⟩
  · rintro ⟨o, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩

theorem Mc_mem (τ : UpperHalfPlane) {o : LeafQM.B} (ho : o ∈ LeafQM.O) :
    Mc o *ᵥ ![(τ : ℂ), 1] ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' :=
  (mem_iff τ _).mpr ⟨o, ho, rfl⟩

theorem Mc_stable (τ : UpperHalfPlane) {o : LeafQM.B} (ho : o ∈ LeafQM.O) {z : Fin 2 → ℂ}
    (hz : z ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne') :
    Mc o *ᵥ z ∈ BPAnalytic.QM.qmLattice τ.im_pos.ne' := by
  obtain ⟨o', ho', rfl⟩ := (mem_iff τ z).mp hz
  rw [Matrix.mulVec_mulVec, ← Mc_mul]
  exact Mc_mem τ (LeafQM.O.mul_mem ho ho')

/-- `ι(x)(τ, 1)ᵀ = (cτ + d)(gτ, 1)ᵀ` for `g = ι(x)` with positive determinant. -/
theorem Mc_vec_of_smul (x : LeafQM.B) (g : GL (Fin 2) ℝ)
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = BPAnalytic.QM.iota x)
    (hdet : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det) (τ : UpperHalfPlane) :
    Mc x *ᵥ ![(τ : ℂ), 1] = UpperHalfPlane.denom g τ • ![((g • τ : UpperHalfPlane) : ℂ), 1] := by
  have hfix : ((g • τ : UpperHalfPlane) : ℂ) * UpperHalfPlane.denom g τ = UpperHalfPlane.num g τ := by
    rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using hdet),
      div_mul_cancel₀ _ (UpperHalfPlane.denom_ne_zero g τ)]
  have hMc : Mc x = (g : Matrix (Fin 2) (Fin 2) ℝ).map (fun r : ℝ => (r : ℂ)) := by rw [hg]; rfl
  rw [hMc]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom] at hfix
  ext i; fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom]
    linear_combination -hfix
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, UpperHalfPlane.denom]

end HSyn.G0Split.FibreQM.PeriodGlueH

end
