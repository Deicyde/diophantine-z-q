import ZInQKernel.Contrib.OneProof.Y3Lattice412.Lattice
import ZInQKernel.Contrib.OneProof.DeligneNarrow

/-! # The print's moduli description in `L_g` form implies the field's clause at units

* B1 `IsHodgeH1PrintAt P τ L`: `Y3Hodge.IsHodgeH1Print` with a lattice `L ⊆ B` in place of `𝒪`
  (the same clauses: paths `c b`, `b ∈ L`; bijectivity `L → H₁`; `ι_A(a)_* c(b) = c(ab)` for `a ∈ 𝒪`,
  `b ∈ L`; the same Hodge clause). `isHodgeH1PrintAt_O_iff`: at `L = 𝒪` it is `IsHodgeH1Print`.
* B2 `ModuliAtLattice Y Φ Ψ`: at every `(τ, g)` the point `Ψ(τ, g)` carries `IsHodgeH1PrintAt` with
  `L = L_g = latticeAt g` (the description of `[h_τ, g]` through `T̂(B) = k⁻¹(V̂_ℤ)`, Deligne 4.12 as
  recorded in `DeligneY3Bridges/README.md`). `moduliAtUnitsHP_of_lattice`: it implies the field's clause
  `Y3Hodge.ModuliAtUnitsHP`; `moduliAtUsedUnitsHP_of_lattice`: and the narrowed clause.

Nothing here is used in place of a frozen clause: `ModuliAtLattice` is stronger than
`ModuliAtUnitsHP`. -/

noncomputable section

namespace Y3Lattice412

open CategoryTheory AlgebraicGeometry Limits Topology MonObj
open PkgI3 (AbVar)
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid ShimuraCFT RayClassCFT Y3Hodge
open ZInQ.LeafPush2 (CPts IsUniformization)
open ZInQ.HomLattice (IsAnalyticHom)

attribute [local instance] CloudB3W17Hodge.classicalTopology

/-! ## B1 -/

/-- **`IsHodgeH1Print` with a lattice `L ⊆ B` in place of `𝒪`**: `(H₁(A, ℤ), ι_*, h_A) ≅ (L, left
multiplication by `𝒪`, h_τ)`. The clauses are those of `Y3Hodge.IsHodgeH1Print`; the `𝒪`-linearity clause
is stated for `a ∈ 𝒪`, `b ∈ L` with `ab ∈ L` (for `L = latticeAt g` this holds for all `a ∈ 𝒪`, `b ∈ L`:
`latticeAt_mul_left`). -/
def IsHodgeH1PrintAt (P : QML3 ℂ) (τ : UpperHalfPlane) (L : Set LeafQM.B) : Prop :=
  ∃ (n : ℕ) (e : (Fin n → ℂ) → CPts P.A (RingHom.id ℂ))
    (β : Matrix (Fin 2) (Fin 2) ℝ ≃ₗ[ℝ] (Fin n → ℂ)) (c : L → Path (1 : P.A.Pt ℂ) 1),
    IsAnalyticHom (RingHom.id ℂ) e ∧
    (∀ (b : L) (t : unitInterval), c b t = e (((t : ℝ) : ℂ) • β (BPAnalytic.QM.iota (b : LeafQM.B)))) ∧
    Function.Bijective (fun b => loopClass (c b)) ∧
    (∀ (a : O) (b : L) (hab : (a : LeafQM.B) * b ∈ L),
      loopClass (pushLoop (P.q.iota a) (c b)) = loopClass (c ⟨_, hab⟩)) ∧
    (∀ M, β (M * Y3Fix.Jmat τ) = Complex.I • β M)

/-- `{b | InO b} ≃ 𝒪` (the same elements). -/
def setOEquiv : ({b : LeafQM.B | InO b} : Set LeafQM.B) ≃ O where
  toFun b := ⟨b.1, b.2⟩
  invFun b := ⟨b.1, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **B1. The generalization is faithful: at `L = 𝒪` it is `IsHodgeH1Print`.** -/
theorem isHodgeH1PrintAt_O_iff (P : QML3 ℂ) (τ : UpperHalfPlane) :
    IsHodgeH1PrintAt P τ {b | InO b} ↔ IsHodgeH1Print P τ := by
  constructor
  · rintro ⟨n, e, β, c, he, hc, hbij, hpush, hJ⟩
    refine ⟨n, e, β, fun b => c (setOEquiv.symm b), he, fun b t => hc _ t, ?_, ?_, hJ⟩
    · exact hbij.comp setOEquiv.symm.bijective
    · intro a b
      exact hpush a (setOEquiv.symm b) (a * b).2
  · rintro ⟨n, e, β, c, he, hc, hbij, hpush, hJ⟩
    refine ⟨n, e, β, fun b => c (setOEquiv b), he, fun b t => hc _ t, ?_, ?_, hJ⟩
    · exact hbij.comp setOEquiv.bijective
    · intro a b hab
      exact hpush a (setOEquiv b)


/-! ## B2 -/

/-- **The print's moduli description in `L_g` form**: at every `(τ, g)`, `Ψ(τ, g)` is an object `P` with
`(H₁(P.A, ℤ), ι_*, h_A) ≅ (L_g, left multiplication, h_τ)`, `L_g = B ∩ 𝒪̂ g⁻¹`. -/
def ModuliAtLattice (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)) : Prop :=
  ∀ (τ : UpperHalfPlane) (g : BAQˣ), ∃ P : QML3 ℂ, Φ ℂ (Ψ (toPM τ) g) = M3.mk P ∧
    IsHodgeH1PrintAt P τ (latticeAt g)

/-- **B2. The `L_g` description implies the field's moduli clause at units** (`L_u = 𝒪`,
`latticeAt_of_mem_OhatU`, and B1). -/
theorem moduliAtUnitsHP_of_lattice {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : ModuliAtLattice Y Φ Ψ) : ModuliAtUnitsHP Y Φ Ψ := by
  intro u hu τ
  obtain ⟨P, hP, hH⟩ := h τ u
  rw [latticeAt_of_mem_OhatU hu] at hH
  exact ⟨P, hP, (isHodgeH1PrintAt_O_iff P τ).1 hH⟩

/-- **B2 (corollary). The narrowed clause `ModuliAtUsedUnitsHP`** for the restriction of `Ψ` to `ℍ`. -/
theorem moduliAtUsedUnitsHP_of_lattice {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : HPM → BAQˣ → (fieldPt ℂ ⟶ Y)} (h : ModuliAtLattice Y Φ Ψ) :
    ModuliAtUsedUnitsHP Y Φ (fun τ g => Ψ (toPM τ) g) :=
  fun u hu τ _ => moduliAtUnitsHP_of_lattice h u hu τ

end Y3Lattice412

end
