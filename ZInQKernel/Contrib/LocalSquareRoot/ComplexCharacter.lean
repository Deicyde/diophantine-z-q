import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Square roots of complex-valued characters

This module supplies the character-target step for the finite-level local square-root
criterion, without repeating its cyclotomic arithmetic. The doubling-kernel argument
is adapted from `GlueSqrtLocal.exists_half_iff` in the frozen source
`533aa66cc3485e21f2d90303e3a34f79d081722d:scratch/glue-sqrt-disj/Disj.lean`,
lines 303–326. Its rational-circle extension step is replaced by the same Baer
extension property for `Additive ℂˣ`.

Nonzero complex numbers have roots of every positive order, by algebraic closedness.
Thus `Additive ℂˣ` is divisible over `ℤ`, hence satisfies Baer's criterion. A character
therefore has a square root precisely when it is trivial on the kernel of squaring.
No finiteness assumption is needed. All characters here are abstract group
homomorphisms; this module makes no continuity or absolute-Galois assertion.

This is a focused proof contribution, not a manuscript release or independent
acceptance. No release artifacts or existing theorem statements are changed.
-/

namespace ZInQ.LocalSquareRoot.ComplexCharacter

/-- The frozen doubling-kernel proof, with its target generalized to any abelian
group satisfying Baer's criterion over `ℤ`. -/
theorem exists_half_iff_of_baer {Γ D : Type*} [AddCommGroup Γ] [AddCommGroup D]
    (hD : Module.Baer ℤ D) (χ : Γ →+ D) :
    (∃ ψ : Γ →+ D, ∀ g, 2 • ψ g = χ g) ↔
      ∀ g : Γ, 2 • g = 0 → χ g = 0 := by
  constructor
  · rintro ⟨ψ, hψ⟩ g hg
    rw [← hψ, ← map_nsmul, hg, map_zero]
  · intro h
    let d : Γ →+ Γ :=
      { toFun := fun g => 2 • g
        map_zero' := smul_zero 2
        map_add' := fun a b => smul_add 2 a b }
    have hker : d.ker ≤ χ.ker := fun g hg => h g (AddMonoidHom.mem_ker.mp hg)
    let χq := QuotientAddGroup.lift d.ker χ hker
    let e := QuotientAddGroup.quotientKerEquivRange d
    let χr : d.range →+ D := χq.comp e.symm.toAddMonoidHom
    obtain ⟨ψ, hψ⟩ := hD.extension_property_addMonoidHom
      d.range.subtype Subtype.val_injective χr
    refine ⟨ψ, fun g => ?_⟩
    have hm : d g ∈ d.range := AddMonoidHom.mem_range.mpr ⟨g, rfl⟩
    have h1 := DFunLike.congr_fun hψ ⟨d g, hm⟩
    have h2 : e.symm ⟨d g, hm⟩ = (g : Γ ⧸ d.ker) := by
      rw [AddEquiv.symm_apply_eq]
      rfl
    calc
      2 • ψ g = ψ (d g) := (map_nsmul ψ 2 g).symm
      _ = χr ⟨d g, hm⟩ := h1
      _ = χ g := by
        simp only [χr, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, h2, χq,
          QuotientAddGroup.lift_mk]

/-- Divisibility of the additive type tag of the nonzero complex numbers.
Kept as a named value rather than a global instance. -/
@[instance_reducible]
noncomputable def complexUnitsDivisible : DivisibleBy (Additive ℂˣ) ℤ := by
  letI : DivisibleBy (Additive ℂˣ) ℕ :=
    divisibleByOfSMulRightSurj (Additive ℂˣ) ℕ fun {n} hn a => by
      obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a.toMul : ℂ)
        (Nat.pos_of_ne_zero hn)
      have hz0 : z ≠ 0 := by
        intro h
        subst z
        rw [zero_pow hn] at hz
        exact a.toMul.ne_zero hz.symm
      refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
      change ((Units.mk0 z hz0) ^ n : ℂˣ) = a.toMul
      apply Units.ext
      change z ^ n = (a.toMul : ℂ)
      exact hz
  exact AddGroup.divisibleByIntOfDivisibleByNat (Additive ℂˣ)

/-- The extension property required by the doubling-kernel proof is unconditional
for the complex-unit character target. -/
theorem complexUnits_baer : Module.Baer ℤ (Additive ℂˣ) := by
  let _ := complexUnitsDivisible
  exact Module.Baer.of_divisible (Additive ℂˣ)

/-- Additive complex-unit analogue of the frozen rational-circle `exists_half_iff`.
This can replace that theorem in the finite-level argument after changing its target. -/
theorem exists_half_iff {Γ : Type*} [AddCommGroup Γ] (χ : Γ →+ Additive ℂˣ) :
    (∃ ψ : Γ →+ Additive ℂˣ, ∀ g, 2 • ψ g = χ g) ↔
      ∀ g : Γ, 2 • g = 0 → χ g = 0 :=
  exists_half_iff_of_baer complexUnits_baer χ

/-- A complex-unit character of an abelian group has a character square root if
and only if it is trivial on every element whose square is `1`. In particular,
this applies to finite abelian groups, with no additional target hypotheses. -/
theorem exists_squareRoot_iff {G : Type*} [CommGroup G] (χ : G →* ℂˣ) :
    (∃ ψ : G →* ℂˣ, ∀ g, ψ g ^ 2 = χ g) ↔
      ∀ g : G, g ^ 2 = 1 → χ g = 1 := by
  constructor
  · rintro ⟨ψ, hψ⟩ g hg
    rw [← hψ, ← map_pow, hg, map_one]
  · intro h
    have hχ : ∀ g : Additive G, 2 • g = 0 → χ.toAdditive g = 0 := by
      intro g hg
      change g.toMul ^ 2 = 1 at hg
      change χ g.toMul = 1
      exact h g.toMul hg
    obtain ⟨ψ, hψ⟩ := (exists_half_iff χ.toAdditive).mpr hχ
    refine ⟨MonoidHom.toAdditive.symm ψ, fun g => ?_⟩
    exact congrArg Additive.toMul (hψ (Additive.ofMul g))

end ZInQ.LocalSquareRoot.ComplexCharacter

#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.exists_half_iff_of_baer
#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.complexUnitsDivisible
#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.complexUnits_baer
#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.exists_half_iff
#print axioms ZInQ.LocalSquareRoot.ComplexCharacter.exists_squareRoot_iff
