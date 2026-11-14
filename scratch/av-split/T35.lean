import ZInQKernel.HDecomp.LeafPush2.T
import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.Contrib.AbVarBC.Points

/-!
# av-split, row H-38 (`ZInQ.LeafPush2.UniformizationExists`, T35)

The row is imported from `ZInQKernel/HDecomp/LeafPush2/T.lean` (unchanged). LEAF
`MumfordUniformizationC`: the row's own statement at `K = ℂ`, `σ = id` (Mumford, *Abelian
varieties*, §1, with Serre's GAGA for the analytic space of a complex variety). Proof of the row
from the leaf: for `σ : K → ℂ` apply the leaf to `A_ℂ = A ×_{K,σ} ℂ` (`dim A_ℂ = dim A`,
`dim_baseChange`) and compose with the projection `A_ℂ → A`: on points it is `AbVarBC.bcPt`
(a group isomorphism `A_ℂ(ℂ) ≃* A(ℂ)_σ`), Zariski opens of `A` pull back to Zariski opens of
`A_ℂ`, and a regular function `s` on `U ⊆ A` pulls back to a regular function on the preimage with
the same values (`Scheme.comp_appLE`).
-/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace AvSplit

open PkgI3
open ZInQ.LeafPush2 (CPts IsUniformization cDom cEvalAt UniformizationExists)

/-- **LEAF (H-38; published form).** Mumford, *Abelian varieties* (1970), §1 (UNVERIFIED
locator), for the analytic space `X^an` of Serre, *Géométrie algébrique et géométrie analytique*,
Ann. Inst. Fourier 6 (1956), §2 (UNVERIFIED): for a complex abelian variety `X` of dimension `g`,
`X^an` is a compact connected complex Lie group of dimension `g`, so `X(ℂ) = ℂ^g/Λ` with `Λ` a
lattice, the quotient map `ℂ^g → X^an` being the exponential map (a surjective holomorphic
homomorphism and a covering). The Lean form records the consequences that the project uses:
`Φ : ℂ^g → A(ℂ)` is a surjective homomorphism with kernel a full lattice `Λ`, preimages of Zariski
opens are open (Zariski opens are open in `X^an`, Serre §2) and regular functions are holomorphic
along `Φ` (they are holomorphic on `X^an`, Serre §2). This is the row itself at `K = ℂ`,
`σ = id`, with nothing added. -/
def MumfordUniformizationC : Prop :=
  ∀ (A : AbVar ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization (RingHom.id ℂ) Λ Φ

section BC

variable {K : Type} [Field K] (A : AbVar K) (σ : K →+* ℂ)

/-- `A_ℂ = A ×_{K,σ} ℂ`. -/
def bcC : AbVar ℂ := letI := σ.toAlgebra; A.baseChange ℂ

/-- The projection `A_ℂ → A` on underlying schemes. -/
def projC : (bcC A σ).X.left ⟶ A.X.left :=
  pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ))

/-- `A_ℂ(ℂ) ≃* A(ℂ)_σ` (task unram-tate's `bcPt`). -/
def ptE : CPts (bcC A σ) (RingHom.id ℂ) ≃* CPts A σ := by
  letI := σ.toAlgebra
  exact ZInQ.Contrib.AbVarBC.bcPt A ℂ

theorem ptE_left (p : CPts (bcC A σ) (RingHom.id ℂ)) : (ptE A σ p).left = p.left ≫ projC A σ := by
  change 𝟙 _ ≫ p.left ≫ pullback.fst _ _ = _
  rw [Category.id_comp]
  rfl

theorem preimage_ptE (p : CPts (bcC A σ) (RingHom.id ℂ)) (U : A.X.left.Opens) :
    (ptE A σ p).left ⁻¹ᵁ U = p.left ⁻¹ᵁ (projC A σ ⁻¹ᵁ U) := by
  rw [ptE_left]
  rfl

theorem cEvalAt_ptE (p : CPts (bcC A σ) (RingHom.id ℂ)) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) :
    cEvalAt (ptE A σ p) U s = cEvalAt p (projC A σ ⁻¹ᵁ U) ((projC A σ).app U s) := by
  have key : ∀ (f : (ZInQ.LeafPush2.cptObj σ).left ⟶ A.X.left) (hf : f = p.left ≫ projC A σ)
      (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ p.left ⁻¹ᵁ (projC A σ ⁻¹ᵁ U)),
      f.appLE U ⊤ h s = p.left.appLE (projC A σ ⁻¹ᵁ U) ⊤ h' ((projC A σ).app U s) := by
    rintro f rfl h h'
    have := Scheme.Hom.comp_appLE p.left (projC A σ) U ⊤ h
    exact (congrArg (fun φ => φ.hom s) this).trans rfl
  unfold cEvalAt
  split <;> split <;> rename_i h1 h2
  · exact congrArg _ (key _ (ptE_left A σ p) h1 h2)
  · exact absurd ((preimage_ptE A σ p U) ▸ h1) h2
  · exact absurd ((preimage_ptE A σ p U).symm ▸ h2) h1
  · rfl

theorem cDom_ptE {g : ℕ} (Φ' : (Fin g → ℂ) → CPts (bcC A σ) (RingHom.id ℂ)) (U : A.X.left.Opens) :
    cDom (fun z => ptE A σ (Φ' z)) U = cDom Φ' (projC A σ ⁻¹ᵁ U) := by
  ext z
  change ⊤ ≤ (ptE A σ (Φ' z)).left ⁻¹ᵁ U ↔ ⊤ ≤ (Φ' z).left ⁻¹ᵁ (projC A σ ⁻¹ᵁ U)
  rw [preimage_ptE]
  exact Iff.rfl

/-- A uniformization of `A_ℂ` at `id` gives one of `A` at `σ` (composition with `A_ℂ → A`). -/
theorem isUniformization_ptE {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ' : (Fin g → ℂ) → CPts (bcC A σ) (RingHom.id ℂ)}
    (hΦ : IsUniformization (RingHom.id ℂ) Λ Φ') :
    IsUniformization σ Λ (fun z => ptE A σ (Φ' z)) := by
  obtain ⟨hmul, hker, hsurj, hopen, hhol⟩ := hΦ
  refine ⟨fun z w => ?_, fun z => ?_, ?_, fun U => ?_, fun U s => ?_⟩
  · simp only [hmul, map_mul]
  · rw [MulEquiv.map_eq_one_iff]
    exact hker z
  · exact (ptE A σ).surjective.comp hsurj
  · rw [cDom_ptE]
    exact hopen _
  · rw [cDom_ptE]
    have := hhol (projC A σ ⁻¹ᵁ U) ((projC A σ).app U s)
    refine this.congr fun z _ => ?_
    exact cEvalAt_ptE A σ (Φ' z) U s

theorem dim_bcC : (bcC A σ).dim = A.dim := by
  letI := σ.toAlgebra
  exact AbVar.dim_baseChange A ℂ

end BC

/-- **Row H-38 from its published-form leaf (proved).** -/
theorem uniformizationExists_of_mumford (h : MumfordUniformizationC) : UniformizationExists := by
  intro K _ A σ g hg
  obtain ⟨Λ, Φ', hd, hz, hΦ⟩ := h (bcC A σ) g ((dim_bcC A σ).trans hg)
  exact ⟨Λ, fun z => ptE A σ (Φ' z), hd, hz, isUniformization_ptE A σ hΦ⟩

/-- Conversely the leaf is the row at `K = ℂ`, `σ = id` (so the two are equivalent). -/
theorem mumford_of_uniformizationExists (h : UniformizationExists) : MumfordUniformizationC :=
  fun A g hg => h ℂ A (RingHom.id ℂ) g hg

end AvSplit

#print axioms AvSplit.uniformizationExists_of_mumford
#print axioms AvSplit.mumford_of_uniformizationExists
