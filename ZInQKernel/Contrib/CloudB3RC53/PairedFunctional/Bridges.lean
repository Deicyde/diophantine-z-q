import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.Proposition
import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.MatrixForm

/-!
# RC53 PairedFunctional: the paired functional in the forms its consumers take

Proposition `ex:arith-paired-functional` (tex L3704–3880) is consumed by the determinant clearing
(5.9), the central lemmas (base zero, (4.6), (4.7)) and the uniform lower bound (5.5). The consumer
interfaces take the functional's integrality through argument types rather than through a separate
hypothesis. This file restates those argument shapes verbatim, as conclusions about the closed
functional `λ_z = pairedFunctional pd2 e.inv (c z)` produced by `PairedFunctionalIntegral`. The
interface files are not imported; the copied text and its source are recorded in each docstring
(RC interface files at `79c2699a5`).

Nodes (GLUE, PROVED):
* `exists_closed_pairedFunctional`: the hypotheses of `PairedFunctionalIntegral` give an
  `S`-linear `λ_z : C_U^2 → S` vanishing on `d(C_U^1)` (tex L3850–3863; exponent `a = 0`, L3864–3869).
* `ScalarDataMuIntegral` (consumer: `RC/Determinant/Clearing.lean`, `structure ScalarData`, fields
  `μH : S` and `μE : Fin (B.m 2) → S`, "the `H_2` and `E_2` coordinates of the transported closed
  functional `μ = 2^a λ_z`", tex 5577–5584): for any exponent `a` and any `H_2`, `E_2` basis
  vectors of `C_U^2`, the coordinates of `μ = 2^a λ_z` are elements `μH : S`, `μE : Fin m₂ → S`, and
  they are the coordinates of a closed functional.
* `TwoTermClosedRow` (consumer: `RC/Central/BaseZero.lean` `baseZero_core` and
  `RC/Central/Coordinate.lean` `coord_specializes`, argument `(z w : Fin (m + 1) → A)`, "an integral
  closed functional `λ` (`w`; integral by the paired-functional proposition, tex 4334–4336)"): on the
  two-term model `[A^{m+1} --D--> A^{m+1}]`, `λ_z` is a row vector `w : Fin (m + 1) → A` with
  `w ᵥ* D = 0`.
* `FunctionalExponentBound` (consumer: `RC/Uniform/OuterContradiction.lean`
  `terminal_lower_bound`, hypothesis
  `(hβ : ∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (β j))`, tex 4957–4962, gap B2-b):
  for `β j` the generic value of integral functionals (`v ≥ 0` on the image of each integral ring),
  `hβ` holds for every `a : ℕ`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open CategoryTheory Limits Matrix

/-- **The integral closed paired functional** (tex L3850–3869), from the hypotheses of
`PairedFunctionalIntegral`: there is a homotopy equivalence `e` with `e.hom = j` such that
`λ_z = pairedFunctional pd2 e.inv (c z)` is `S`-linear and vanishes on `d(C_U^1)`.
Classification: GLUE (PROVED from `pairedFunctionalIntegral_proof`). -/
theorem exists_closed_pairedFunctional (S : Type) [CommRing S]
    (CU C' C Z : CochainComplex (ModuleCat.{0} S) ℤ) (j : C' ⟶ C)
    (c : Z ⟶ C) (z : Z.X 1) (pd1 : CU.X 1 →ₗ[S] C'.X 2 →ₗ[S] S)
    (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S) (pd3 : CU.X 3 →ₗ[S] C'.X 0 →ₗ[S] S) (ε ε' : S)
    (ι : Type) [Fintype ι] (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module S (M v)]
    (A Cin D : ∀ v, Module.End S (M v)) (hDC : ∀ v, D v * Cin v = Cin v * A v) (n : ι → ℤ)
    (hunit : ∀ v, (IsUnit (A v) ∧ IsUnit (D v)) ∨ IsUnit (Cin v))
    (hcone : Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
      (⨁ fun v => (tameComplex (A v) (Cin v) (D v) (hDC v))⟦n v⟧)))
    (hz : (Z.d 1 2).hom z = 0)
    (hL1 : ∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y))
    (hL2 : ∀ w y, pd2 w ((C'.d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y) :
    ∃ e : HomotopyEquiv C' C, e.hom = j ∧
      ∀ w : CU.X 1, pairedFunctional pd2 e.inv ((c.f 1).hom z) ((CU.d 1 2).hom w) = 0 := by
  obtain ⟨e, he, -, -, hcl, -⟩ := pairedFunctionalIntegral_proof S CU C' C Z j c z pd1 pd2 pd3 ε ε'
    ι M A Cin D hDC n hunit hcone hz hL1 hL2
  exact ⟨e, he, hcl⟩

/-- **RC7 `ScalarData`: the coordinates of `μ = 2^a λ_z` are integral** (consumer:
`RC/Determinant/Clearing.lean`, `structure ScalarData (B : SmithBlocks S O)` with fields
`μH : S`, `μE : Fin (B.m 2) → S`, tex 5577–5584; here `m₂` stands for `B.m 2`). For a closed
`S`-linear functional `λ` on `C_U^2` (as produced by `exists_closed_pairedFunctional`), every
exponent `a`, an `H_2` vector `eH` and `E_2` vectors `eE : Fin m₂ → C_U^2`, the coordinates
`μH = 2^a λ(eH)`, `μE i = 2^a λ(eE i)` are elements of `S`, and `μ = 2^a λ` is again closed.
Classification: GLUE (PROVED). -/
def ScalarDataMuIntegral : Prop :=
  ∀ (S : Type) [CommRing S] (CU : CochainComplex (ModuleCat.{0} S) ℤ) (lam : CU.X 2 →ₗ[S] S),
    (∀ w : CU.X 1, lam ((CU.d 1 2).hom w) = 0) →
    ∀ (a m₂ : ℕ) (eH : CU.X 2) (eE : Fin m₂ → CU.X 2),
      ∃ (μH : S) (μE : Fin m₂ → S), μH = 2 ^ a * lam eH ∧ (∀ i, μE i = 2 ^ a * lam (eE i)) ∧
        ∀ w : CU.X 1, ((2 : S) ^ a • lam) ((CU.d 1 2).hom w) = 0

theorem scalarDataMuIntegral_proof : ScalarDataMuIntegral := by
  intro S _ CU lam hcl a m₂ eH eE
  refine ⟨2 ^ a * lam eH, fun i => 2 ^ a * lam (eE i), rfl, fun _ => rfl, fun w => ?_⟩
  rw [LinearMap.smul_apply, hcl, smul_zero]

/-- **RC15 `w : Fin (m + 1) → A`: the functional on the two-term model is a closed integral row**
(consumers: `RC/Central/BaseZero.lean` `baseZero_core`, argument `(z w : Fin (m + 1) → A)`, and
`RC/Central/Coordinate.lean` `coord_specializes`, argument `(z w : Fin n → A)`; tex 4334–4336,
3882–3892). If `C_U^1`, `C_U^2` are identified with `A^{m+1}` by linear equivalences `e₁`, `e₂`
under which `d¹` is the matrix `D`, then a closed `A`-linear `λ` on `C_U^2` is
`x ↦ w ⬝ᵥ x` (in the coordinates `e₂`) for a row vector `w : Fin (m + 1) → A` with `w ᵥ* D = 0`.
Classification: GLUE (PROVED, from `ClosedFunctionalMatrixForm`). -/
def TwoTermClosedRow : Prop :=
  ∀ (A : Type) [CommRing A] (CU : CochainComplex (ModuleCat.{0} A) ℤ) (m : ℕ)
    (D : Matrix (Fin (m + 1)) (Fin (m + 1)) A) (e₁ : CU.X 1 ≃ₗ[A] (Fin (m + 1) → A))
    (e₂ : CU.X 2 ≃ₗ[A] (Fin (m + 1) → A)),
    (∀ x, e₂ ((CU.d 1 2).hom x) = D *ᵥ e₁ x) →
    ∀ lam : CU.X 2 →ₗ[A] A, (∀ w : CU.X 1, lam ((CU.d 1 2).hom w) = 0) →
      ∃ w : Fin (m + 1) → A, w ᵥ* D = 0 ∧ ∀ y : Fin (m + 1) → A, lam (e₂.symm y) = w ⬝ᵥ y

theorem twoTermClosedRow_proof : TwoTermClosedRow := by
  intro A _ CU m D e₁ e₂ hd lam hcl
  have hcl' : ∀ x, (lam ∘ₗ e₂.symm.toLinearMap) (D *ᵥ x) = 0 := by
    intro x
    have h := hcl (e₁.symm x)
    rw [← e₂.symm_apply_apply ((CU.d 1 2).hom (e₁.symm x)), hd, e₁.apply_symm_apply] at h
    simpa using h
  obtain ⟨w, hw, hrep⟩ := (closedFunctionalMatrixForm_proof A (m + 1) D).1 _ hcl'
  exact ⟨w, hw, fun y => by simpa using hrep y⟩

/-- **RC16 `hβ`: the functional exponent bound** (consumer: `RC/Uniform/OuterContradiction.lean`
`terminal_lower_bound`, hypothesis
`(hβ : ∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (β j))`, tex 4957–4962; gap B2-b of the
independent manuscript check). Let `v : AddValuation K (WithTop ℤ)` and, for each index `j`, an integral ring `S j`
with a map `φ j : S j → K` landing in the valuation ring (`0 ≤ v (φ j s)`), a closed `S j`-linear
functional `lam j` (the integral representative of `ex:arith-paired-functional`, with exponent
`a = 0`, tex L3864–3869) and a vector `x j`. Then `β j = φ j (lam j (x j))` satisfies `hβ` for
every `a : ℕ`. Classification: GLUE (PROVED). -/
def FunctionalExponentBound : Prop :=
  ∀ (K : Type) [Field K] (v : AddValuation K (WithTop ℤ)) (ι : Type) (𝒰 : Ultrafilter ι)
    (S : ι → Type) [∀ j, CommRing (S j)] (φ : ∀ j, S j →+* K),
    (∀ j s, (0 : WithTop ℤ) ≤ v (φ j s)) →
    ∀ (X : ι → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module (S j) (X j)]
      (lam : ∀ j, X j →ₗ[S j] S j) (x : ∀ j, X j) (a : ℕ),
      let β : ι → K := fun j => φ j (lam j (x j))
      ∀ᶠ j in (𝒰 : Filter ι), (((-a : ℤ)) : WithTop ℤ) ≤ v (β j)

theorem functionalExponentBound_proof : FunctionalExponentBound := by
  intro K _ v ι 𝒰 S _ φ hint X _ _ lam x a β
  refine Filter.Eventually.of_forall fun j => le_trans ?_ (hint j _)
  exact_mod_cast (by omega : (-(a : ℤ)) ≤ 0)

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
