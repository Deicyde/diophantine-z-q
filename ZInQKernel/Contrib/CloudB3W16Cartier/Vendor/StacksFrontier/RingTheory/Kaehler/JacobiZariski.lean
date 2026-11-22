/-
Adapted from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/RingTheory/Kaehler/JacobiZariski.lean
Source SHA256: d6edb2ba9f5c16f3e06c138a08f29d5d8e1efd6df2f7d81411730616378ab392
Apache-2.0; see LICENSE and NOTICE.md.
Changes: isolated vendor namespaces and import paths; citation attributes removed.
-/
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

namespace ZInQ.Contrib.CloudB3W16Cartier.Vendor
open _root_.Algebra


/-!
# The Jacobi-Zariski sequence and the sequence of differentials of a tower

Let `A → B → C` be ring maps, let `α : A[x_s, s ∈ S] → B` be a presentation with kernel `I`, let
`β : B[y_t, t ∈ T] → C` be a presentation with kernel `J`, and let `γ : A[x_s, y_t] → C` be the
induced presentation of `C` with kernel `K`. The naive cotangent complexes of the three
presentations give the Jacobi-Zariski exact sequence of `C`-modules
```
H₁(NL_{B/A} ⊗_B C) → H₁(L_{C/A}) → H₁(L_{C/B}) → C ⊗_B Ω_{B/A} → Ω_{C/A} → Ω_{C/B} → 0.
```
Exactness at the four right hand nodes is `Algebra.H1Cotangent.exact_map_δ`,
`Algebra.H1Cotangent.exact_δ_mapBaseChange`, `KaehlerDifferential.exact_mapBaseChange_map` and
`KaehlerDifferential.map_surjective`. This file proves exactness at `H₁(L_{C/A})`: inside `K/K²`,
the image of `H₁(NL_{B/A} ⊗_B C) = Ker(I/I² ⊗_B C → Ω_{A[x_s]/A} ⊗ C)` under the map
`I/I² ⊗_B C → K/K²` induced by `A[x_s] → A[x_s, y_t]` is the intersection of
`H₁(L_{C/A}) = Ker(K/K² → Ω_{A[x_s, y_t]/A} ⊗ C)` with the kernel of the map `K/K² → J/J²`
induced by `A[x_s, y_t] → B[y_t]`. It also shows that `C ⊗_B Ω_{B/A} → Ω_{C/A}` is injective
when `H₁(L_{C/B}) = 0`, for instance when `B → C` is smooth.

## Main results

* `Algebra.Generators.Cotangent.map_ker_baseChange_cotangentComplex`: the Jacobi-Zariski sequence
  is exact at `H₁(L_{C/A})`, as an equality of `C`-submodules of `K/K²`.
* `KaehlerDifferential.mapBaseChange_injective`: if `H₁(L_{B/A}) = 0`, then
  `KaehlerDifferential.mapBaseChange R A B : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R]` is injective, so that
  `0 → B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0` is exact.

## Implementation notes

The presentations `α`, `β` and `γ` are `P : Algebra.Generators R S σ`,
`Q : Algebra.Generators S T ι` and `Q.comp P`, so `P.toExtension.Cotangent`,
`(Q.comp P).toExtension.Cotangent` and `Q.toExtension.Cotangent` are `I/I²`, `K/K²` and `J/J²`.
Exactness at `H₁(L_{C/A})` is recorded as an equality of submodules of `K/K²` rather than as a
`Function.Exact`.

In `KaehlerDifferential.mapBaseChange_injective` the tower is written `R → A → B`, matching
`KaehlerDifferential.mapBaseChange`, and the hypothesis is
`Subsingleton (Algebra.H1Cotangent A B)`, which holds by instance inference when `A → B` is smooth
or formally smooth.

## References

* [StacksProject 00S2](https://stacks.math.columbia.edu/tag/00S2)
* [StacksProject 04B2](https://stacks.math.columbia.edu/tag/04B2)
* [StacksProject 00RS](https://stacks.math.columbia.edu/tag/00RS)
-/

section

universe w₁ w₂ u₁ u₂ u₃

-- `Generators.{w, u₁, u₂}` depends on three universe variables and to improve performance
-- of universe unification, it should hold that `w > u₁` and `w > u₂` in the lexicographic
-- order.

namespace Stacks.KaehlerDifferential.JacobiZariski

open Algebra

/-- The image in `K/K²` of the cycles of `NL(α) ⊗_B C` is the intersection of the cycles of
`NL(γ)` with the kernel of `K/K² → J/J²`. -/
theorem solution {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]
    {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    {ι : Type w₁} {σ : Type w₂} (Q : Generators S T ι) (P : Generators R S σ) :
    Submodule.map ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T)
        (LinearMap.ker (P.toExtension.cotangentComplex.baseChange T)) =
      LinearMap.ker (Q.comp P).toExtension.cotangentComplex ⊓
        LinearMap.ker (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
  have key : ∀ y, (Q.comp P).toExtension.cotangentComplex
        ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T y) =
      (Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange T
        (P.toExtension.cotangentComplex.baseChange T y) := fun y ↦
    (DFunLike.congr_fun
      (Generators.H1Cotangent.map_comp_cotangentComplex_baseChange Q P) y).symm
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, key, LinearMap.mem_ker.mp hy, map_zero]
    · exact (Generators.Cotangent.exact Q P).apply_apply_eq_zero y
  · rintro x ⟨hx₁, hx₂⟩
    obtain ⟨y, rfl⟩ := (Generators.Cotangent.exact Q P) x |>.mp hx₂
    refine Submodule.mem_map.mpr ⟨y, ?_, rfl⟩
    refine LinearMap.mem_ker.mpr
      (Generators.CotangentSpace.map_toComp_injective Q P ?_)
    rw [map_zero, ← key]
    exact hx₁

end Stacks.KaehlerDifferential.JacobiZariski

section

namespace Algebra.Generators.Cotangent

variable {R : Type u₁} {S : Type u₂} [CommRing R] [CommRing S] [Algebra R S]
variable {T : Type u₃} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {ι : Type w₁} {σ : Type w₂}

/-- **The Jacobi-Zariski sequence is exact at `H₁(L_{C/A})`**: let `A → B → C` be ring maps, let
`α : A[x_s, s ∈ S] → B` be a presentation with kernel `I`, let `β : B[y_t, t ∈ T] → C` be a
presentation with kernel `J`, and let `γ : A[x_s, y_t] → C` be the induced presentation of `C`
with kernel `K`. Then the image in `K/K²` of
`H₁(NL_{B/A} ⊗_B C) = Ker(I/I² ⊗_B C → Ω_{A[x_s]/A} ⊗ C)`, under the map `I/I² ⊗_B C → K/K²`
induced by `A[x_s] → A[x_s, y_t]`, is the intersection of
`H₁(L_{C/A}) = Ker(K/K² → Ω_{A[x_s, y_t]/A} ⊗ C)` with the kernel of the map `K/K² → J/J²`
induced by `A[x_s, y_t] → B[y_t]`, i.e. with the kernel of `H₁(L_{C/A}) → H₁(L_{C/B})`. -/
theorem map_ker_baseChange_cotangentComplex (Q : Generators S T ι)
    (P : Generators R S σ) :
    Submodule.map ((Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange T)
        (LinearMap.ker (P.toExtension.cotangentComplex.baseChange T)) =
      LinearMap.ker (Q.comp P).toExtension.cotangentComplex ⊓
        LinearMap.ker (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) :=
  Stacks.KaehlerDifferential.JacobiZariski.solution Q P

end Algebra.Generators.Cotangent

end

section

/-- **The sequence of differentials of a tower is exact on the left**: let `R → A → B` be ring
maps such that `H₁(L_{B/A}) = 0`, for instance with `A → B` smooth. Then the canonical map
`B ⊗_A Ω_{A/R} → Ω_{B/R}` is injective, so that `0 → B ⊗_A Ω_{A/R} → Ω_{B/R} → Ω_{B/A} → 0` is
a short exact sequence. -/
theorem KaehlerDifferential.mapBaseChange_injective (R : Type*) [CommRing R]
    (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Subsingleton (Algebra.H1Cotangent A B)] :
    Function.Injective (KaehlerDifferential.mapBaseChange R A B) :=
  (LinearMap.injective_iff_eq_zero_of_exact
    (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B)).mpr (Subsingleton.elim _ _)

namespace Stacks.KaehlerDifferential.LeftExactness

/-- For a tower `R → A → B` with `H₁(L_{B/A}) = 0`, the canonical map
`B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` is injective. -/
alias solution := _root_.ZInQ.Contrib.CloudB3W16Cartier.Vendor.KaehlerDifferential.mapBaseChange_injective

end Stacks.KaehlerDifferential.LeftExactness

end
end
end ZInQ.Contrib.CloudB3W16Cartier.Vendor
