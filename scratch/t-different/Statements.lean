import Mathlib

/-!
# t-different: the textbook leaves T20, T21, T22, copied verbatim

Copied from `scratch/h-decomposition/Leaves.lean` (base 01267822): the `PkgI6` definitions
(lines 5029-5133: `lowerRam`, `lowerRamR`, `herbrandPhi`, `upperRam`, `lowerRam_tower`, and the leaves
`DifferentBound` (I6.6 = T21 local), `HilbertDifferentFormula` (I6.7 = T20 local),
`HerbrandQuotient` (I6.8 = T22a), `HerbrandTransitivity` (I6.9 = T22b)) and the `GlueConductor`
definitions (lines 5717-5746: `ramGroup`, `ramCard`, and the global leaves
`HilbertDifferentFormula` (T20) and `SerreDifferentBound` (T21)).
-/

namespace PkgI6

section Ramification

open IsLocalRing

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

/-- **Definition (Serre IV §1).** The lower ramification group `G_i` (`i ≥ 0`) of `B/A`:
the `σ` with `v_B(σ b − b) ≥ i + 1` for all `b ∈ B`.  Written with Mathlib's
`AddSubgroup.inertia` (the subgroup acting trivially modulo `𝔪_B^{i+1}`), as glue-conductor's
`ramGroup` does in the global setting. -/
def lowerRam (i : ℕ) : Subgroup (B ≃ₐ[A] B) :=
  (maximalIdeal B ^ (i + 1)).toAddSubgroup.inertia (B ≃ₐ[A] B)

lemma mem_lowerRam {i : ℕ} {σ : B ≃ₐ[A] B} :
    σ ∈ lowerRam A B i ↔ ∀ b : B, σ b - b ∈ maximalIdeal B ^ (i + 1) := Iff.rfl

/-- Lower numbering for a real index `u ≥ -1` (Serre IV §3): `G_u = G_{⌈u⌉}`, `G_{-1} = G`. -/
noncomputable def lowerRamR (u : ℝ) : Subgroup (B ≃ₐ[A] B) :=
  if u ≤ -1 then ⊤ else lowerRam A B (⌈u⌉.toNat)

/-- **Definition (Serre IV §3).** Herbrand's function
`φ_{B/A}(u) = ∫₀ᵘ dt / (G₀ : G_t)`. -/
noncomputable def herbrandPhi (u : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..u, (Nat.card (lowerRamR A B t) : ℝ) / (Nat.card (lowerRamR A B 0) : ℝ)

/-- **Definition (Serre IV §3).** Upper numbering `G^v = G_{ψ(v)}`, `ψ = φ⁻¹`; here `ψ(v)` is
written `sInf {u ≥ -1 | v ≤ φ(u)}` (`φ` is a continuous increasing bijection of `[-1, ∞)`). -/
noncomputable def upperRam (v : ℝ) : Subgroup (B ≃ₐ[A] B) :=
  lowerRamR A B (sInf {u : ℝ | -1 ≤ u ∧ v ≤ herbrandPhi A B u})

/-- The subgroup rule for lower numbering (Serre IV §1 Prop. 2): for an intermediate ring `C`,
`(B/C)_i = (B/A)_i ∩ Gal(B/C)`.  GLUE: immediate from the definition (proved). -/
theorem lowerRam_tower (C : Type) [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    (i : ℕ) :
    lowerRam C B i = (lowerRam A B i).comap (AlgEquiv.restrictScalarsHom A) := by
  ext σ; rfl

end Ramification

section LocalLeaves

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Leaf I6.6 (Serre's bound for the different).** For a finite separable extension of
complete discrete valuation rings with perfect residue field, `v_B(𝔇_{B/A}) ≤ e − 1 + v_B(e)`,
where `e` is the ramification index.  Serre, *Corps locaux*, III §6, remark after Prop. 13
(UNVERIFIED locator).  Written `𝔇 ∣ 𝔪_B^{e-1}·(e)` (ideals of a DVR are ordered by divisibility;
if `e = 0` in `B` the right side is `⊥` and the statement is empty).  Mathlib has only the lower
bound `pow_sub_one_dvd_differentIdeal`. -/
def DifferentBound : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)],
    differentIdeal A B ∣
      maximalIdeal B ^ (Ideal.ramificationIdx (maximalIdeal B) A - 1) *
        Ideal.span {((Ideal.ramificationIdx (maximalIdeal B) A : ℕ) : B)}

/-- **Leaf I6.7 (Hilbert's formula for the different).** For `B/A` as above and Galois,
`v_B(𝔇_{B/A}) = ∑_{i ≥ 0} (|G_i| − 1)`.  Serre, *Corps locaux*, IV §1, Prop. 4 (UNVERIFIED
locator). -/
def HilbertDifferentFormula : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    ∃ N : ℕ, lowerRam A B N = ⊥ ∧
      differentIdeal A B =
        maximalIdeal B ^ (∑ i ∈ Finset.range N, (Nat.card (lowerRam A B i) - 1))

/-- **Leaf I6.8 (Herbrand's theorem).** For a tower `A → C → B` with `B/A` and `C/A` Galois and
`r : Gal(B/A) → Gal(C/A)` the restriction, `Gal(C/A)^v = r(Gal(B/A)^v)` for all `v`.
Serre, *Corps locaux*, IV §3, Prop. 14 (UNVERIFIED locator).  (`r` is determined by `hr`.) -/
def HerbrandQuotient : Prop :=
  ∀ (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [IsGalois (FractionRing A) (FractionRing C)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)]
    [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]
    (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (_hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) (v : ℝ),
    upperRam A C v = (upperRam A B v).map r

/-- **Leaf I6.9 (transitivity of Herbrand's function).** For a tower `A → C → B` with `B/A`
Galois (hence `B/C` Galois) and `C/A` Galois, `φ_{B/A} = φ_{C/A} ∘ φ_{B/C}`.
Serre, *Corps locaux*, IV §3, Prop. 15 (UNVERIFIED locator). -/
def HerbrandTransitivity : Prop :=
  ∀ (A C B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
    [Module.IsTorsionFree A C] [Algebra.IsSeparable (FractionRing A) (FractionRing C)]
    [IsGalois (FractionRing A) (FractionRing C)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)]
    [Algebra C B] [IsScalarTower A C B] [Module.Finite C B] [Module.IsTorsionFree C B],
    ∀ u : ℝ, -1 ≤ u → herbrandPhi A B u = herbrandPhi A C (herbrandPhi C B u)


end LocalLeaves

end PkgI6

namespace GlueConductor

open Finset

open NumberField

/-- The lower ramification group `G_i` of `P` in `Gal(L/ℚ)`. -/
abbrev ramGroup (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) :
    Subgroup Gal(L/ℚ) :=
  (P ^ (i + 1)).inertia Gal(L/ℚ)

/-- `|G_i|`. -/
noncomputable abbrev ramCard (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) : ℕ :=
  Nat.card (ramGroup L P i)

/-- **Leaf (Hilbert's different formula; Serre, *Corps locaux*, IV §1, Prop. 4, with `G_i = 1`
for large `i`, IV §1; UNVERIFIED numbering).** For a Galois number field `L` and a nonzero prime
`P` of `𝓞 L`, some `G_n` is trivial and the exact power of `P` in the different of `𝓞 L/ℤ` is
`∑_{i<n} (|G_i| - 1)`. -/
def HilbertDifferentFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L] (P : Ideal (𝓞 L)) [P.IsPrime], P ≠ ⊥ →
    ∃ n, ramGroup L P n = ⊥ ∧
      P ^ (∑ i ∈ range n, (ramCard L P i - 1)) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (∑ i ∈ range n, (ramCard L P i - 1) + 1) ∣ differentIdeal ℤ (𝓞 L)

/-- **Leaf (Serre's bound for the different; Serre, *Corps locaux*, III §6, remark after
Prop. 13: `v_L(𝔇_{L/K}) ≤ e - 1 + v_L(e)`; UNVERIFIED numbering).** At `K = ℚ_p`,
`v_L(e) = e·v_p(e)`. Stated for any number field `L` and prime `P | p` of `𝓞 L`. -/
def SerreDifferentBound : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (p : ℕ), p.Prime → ∀ (P : Ideal (𝓞 L)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    ¬ P ^ (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ) + 1)
      ∣ differentIdeal ℤ (𝓞 L)


end GlueConductor
