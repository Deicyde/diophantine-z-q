import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Kaehler`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Kähler differentials do not see a surjective change of base ring

For a tower `R → S → B` of commutative rings in which `R → S` is **surjective**, the comparison
map `Ω[B⁄R] → Ω[B⁄S]` of `Mathlib.RingTheory.Kaehler.Basic` is an isomorphism: **the module of
Kähler differentials of `B` depends on the base ring only through its image in `B`.**

## Main results

* `Stacks.RelativeDifferentialStalkMap.kaehlerMap_bijective_of_surjective`: the comparison map
  `KaehlerDifferential.map R S B B` is bijective when `R → S` is surjective.
* `Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective`: that comparison read as a
  linear equivalence `Ω[B⁄R] ≃ₗ[B] Ω[B⁄S]`, with
  `Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective_D` and
  `Stacks.RelativeDifferentialStalkMap.kaehlerMapEquivOfSurjective_symm_D` saying that it
  matches universal differentials on both sides.

## Implementation notes

Surjectivity of `R → S` is only used through `KaehlerDifferential.subsingleton_of_surjective`,
which says `Ω[S⁄R] = 0`.  Mathlib's exact sequence

```
B ⊗[S] Ω[S⁄R] ⟶ Ω[B⁄R] ⟶ Ω[B⁄S] ⟶ 0
```

— `KaehlerDifferential.exact_mapBaseChange_map` together with
`KaehlerDifferential.map_surjective` — then has a vanishing left-hand term, so its middle map is
injective as well as surjective.  Nothing else is needed; in particular neither
`KaehlerDifferential.kerTotal_map` nor `KaehlerDifferential.ker_map` is used, and the kernel is
never computed.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/


open scoped TensorProduct

universe u v w

namespace Stacks.RelativeDifferentialStalkMap
#cloudR2LocalInstances

variable (R : Type u) (S : Type v) (B : Type w) [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
#cloudR2Vendor kaehlerMap_bijective_of_surjective in

/-- **The comparison map `Ω[B⁄R] → Ω[B⁄S]` is bijective when `R → S` is surjective.**

Surjectivity is `KaehlerDifferential.map_surjective`.  Injectivity holds because the kernel is
the image of `B ⊗[S] Ω[S⁄R]` by `KaehlerDifferential.exact_mapBaseChange_map`, and `Ω[S⁄R]`
vanishes for a surjective `R → S`. -/

theorem kaehlerMap_bijective_of_surjective
    (h : Function.Surjective (algebraMap R S)) :
    Function.Bijective (KaehlerDifferential.map R S B B) := by
  refine ⟨?_, KaehlerDifferential.map_surjective R S B⟩
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S B
  have hsub : Subsingleton (KaehlerDifferential R S) :=
    KaehlerDifferential.subsingleton_of_surjective R S h
  rw [← LinearMap.ker_eq_bot, hex.linearMap_ker_eq, LinearMap.range_eq_bot]
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul b y => rw [Subsingleton.elim y 0]; simp
  | add a b ha hb => rw [map_add, ha, hb]; simp
#cloudR2Vendor kaehlerMapEquivOfSurjective in

/-- **Kähler differentials are invariant under a surjective change of base ring.**  For a tower
`R → S → B` with `R → S` surjective, `Ω[B⁄R] ≃ₗ[B] Ω[B⁄S]`, by the comparison map. -/

noncomputable def kaehlerMapEquivOfSurjective
    (h : Function.Surjective (algebraMap R S)) :
    KaehlerDifferential R B ≃ₗ[B] KaehlerDifferential S B :=
  LinearEquiv.ofBijective (KaehlerDifferential.map R S B B)
    (kaehlerMap_bijective_of_surjective R S B h)
#cloudR2Vendor kaehlerMapEquivOfSurjective_D in

/-- The equivalence carries the universal `R`-differential of an element of `B` to its universal
`S`-differential. -/
theorem kaehlerMapEquivOfSurjective_D (h : Function.Surjective (algebraMap R S)) (b : B) :
    kaehlerMapEquivOfSurjective R S B h (KaehlerDifferential.D R B b) =
      KaehlerDifferential.D S B b := by
  change KaehlerDifferential.map R S B B (KaehlerDifferential.D R B b) = _
  rw [KaehlerDifferential.map_D]
  simp
#cloudR2Vendor kaehlerMapEquivOfSurjective_symm_D in

/-- The inverse equivalence carries the universal `S`-differential of an element of `B` to its
universal `R`-differential. -/
theorem kaehlerMapEquivOfSurjective_symm_D (h : Function.Surjective (algebraMap R S))
    (b : B) :
    (kaehlerMapEquivOfSurjective R S B h).symm (KaehlerDifferential.D S B b) =
      KaehlerDifferential.D R B b :=
  (LinearEquiv.symm_apply_eq _).2 (kaehlerMapEquivOfSurjective_D R S B h b).symm

end Stacks.RelativeDifferentialStalkMap


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
