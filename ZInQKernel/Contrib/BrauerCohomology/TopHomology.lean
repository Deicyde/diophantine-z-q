/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; a copy is in docs/research/t14-t15-brauer-cochains.md.
Authors: The Tau Ceti contributors

Adapted for Lean 4.35.0 / Mathlib v4.35.0 (AI-assisted; model identity not recorded),
2026-11-13. Source: TauCeti revision 61090fff281d0c6cece0176aa8436ab748b53048, file
`TauCeti/Algebra/Category/ModuleCat/Topology/Homology.lean` (SHA-256
`34f6afefabb0fd9016c01277f550bcdadc03f5b7ad7f5d89149023cb3f42e35e`).
Changes: moved into the namespace `ZInQ.Contrib.BrauerCohomology.TopHom`; kept only the
elementwise description of cycles and homology (`homologyIsoCoker`, surjectivity of the class map,
its kernel, injectivity of the cycle inclusion, `cyclesMkOfEq`, and the naturality of the class of
an elementwise cycle); dropped the discreteness, `descHomologyₗ` and exactness parts and the two
Tau Ceti imports they need. Proofs are re-checked against the pinned Mathlib.
-/
import Mathlib.Algebra.Category.ModuleCat.Topology.Homology
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

set_option autoImplicit false

/-!
# Homology in `TopModuleCat` as a concrete subquotient

Mathlib makes `TopModuleCat R` a `CategoryWithHomology` through the concrete kernel
`TopModuleCat.ker` and cokernel `TopModuleCat.coker`, but the homology object it produces is chosen
by `Classical.choice`. The lemmas below describe it elementwise:

* `homologyπ_surjective`: every homology class is the class of a cycle (an epimorphism of
  topological modules need not be surjective, so this is not formal);
* `homologyπ_eq_zero_iff`: a cycle has zero class iff it is a boundary;
* `iCycles_injective`, `cyclesMkOfEq`: cycles are the elements of the middle term killed by the
  outgoing differential;
* `homologyMap_homologyπ_cyclesMkOfEq`: a chain map sends the class of a cycle to the class of
  its image.

These are exactly the facts needed to compare `continuousCohomology` with explicit cochains.
-/

open CategoryTheory Limits

namespace ZInQ.Contrib.BrauerCohomology.TopHom

section ShortComplex

variable {R : Type*} [Ring R] [TopologicalSpace R] (S : ShortComplex (TopModuleCat R))

/-- The homology of a short complex of topological modules is the concrete cokernel of
`S.toCycles`. -/
noncomputable def homologyIsoCoker : S.homology ≅ TopModuleCat.coker S.toCycles :=
  IsColimit.coconePointUniqueUpToIso S.homologyIsCokernel (TopModuleCat.isColimitCoker S.toCycles)

theorem homologyπ_comp_homologyIsoCoker_hom :
    S.homologyπ ≫ (homologyIsoCoker S).hom = TopModuleCat.cokerπ S.toCycles :=
  IsColimit.comp_coconePointUniqueUpToIso_hom S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) WalkingParallelPair.one

theorem cokerπ_comp_homologyIsoCoker_inv :
    TopModuleCat.cokerπ S.toCycles ≫ (homologyIsoCoker S).inv = S.homologyπ :=
  IsColimit.comp_coconePointUniqueUpToIso_inv S.homologyIsCokernel
    (TopModuleCat.isColimitCoker S.toCycles) WalkingParallelPair.one

/-- The class map onto the homology of a short complex of topological modules is surjective. -/
theorem homologyπ_surjective : Function.Surjective S.homologyπ.hom := by
  intro x
  obtain ⟨y, hy⟩ := TopModuleCat.cokerπ_surjective S.toCycles ((homologyIsoCoker S).hom x)
  refine ⟨y, ?_⟩
  have h := ConcreteCategory.congr_hom (cokerπ_comp_homologyIsoCoker_inv S) y
  simp only [ConcreteCategory.comp_apply] at h
  change S.homologyπ y = x
  rw [← h, hy, Iso.hom_inv_id_apply]

/-- A cycle has zero homology class exactly when it is a boundary. -/
theorem homologyπ_eq_zero_iff {x : S.cycles} :
    S.homologyπ x = 0 ↔ x ∈ Set.range S.toCycles.hom := by
  rw [← (homologyIsoCoker S).toContinuousLinearEquiv.map_eq_zero_iff]
  have h := ConcreteCategory.congr_hom (homologyπ_comp_homologyIsoCoker_hom S) x
  simp only [ConcreteCategory.comp_apply] at h
  change (homologyIsoCoker S).hom (S.homologyπ x) = 0 ↔ _
  rw [h, TopModuleCat.hom_cokerπ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range

/-- The inclusion of the cycles into the middle term is injective. -/
theorem iCycles_injective : Function.Injective S.iCycles.hom :=
  ConcreteCategory.injective_of_mono_of_preservesPullback
    ((forget₂ (TopModuleCat R) TopCat).map S.iCycles)

/-- The cycle determined by an element of the middle term killed by `S.g`. -/
noncomputable def cyclesMkOfEq (x : S.X₂) (hx : S.g x = 0) : S.cycles :=
  (S.isoCyclesOfIsLimit (TopModuleCat.isLimitKer S.g)).hom ⟨x, hx⟩

@[simp]
theorem iCycles_cyclesMkOfEq (x : S.X₂) (hx : S.g x = 0) :
    S.iCycles (cyclesMkOfEq S x hx) = x := by
  have h := ConcreteCategory.congr_hom
    (S.isoCyclesOfIsLimit_hom_iCycles (TopModuleCat.isLimitKer S.g)) ⟨x, hx⟩
  simp only [ConcreteCategory.comp_apply, Limits.KernelFork.ι_ofι] at h
  exact h

end ShortComplex

section Complex

variable {R : Type*} [Ring R] [TopologicalSpace R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (TopModuleCat R) c) {n : ι}

theorem homologyπ_surjective' [K.HasHomology n] : Function.Surjective (K.homologyπ n).hom :=
  homologyπ_surjective (K.sc n)

theorem homologyπ_eq_zero_iff' [K.HasHomology n] {m : ι} (hm : c.prev n = m)
    {x : K.cycles n} : K.homologyπ n x = 0 ↔ x ∈ Set.range (K.toCycles m n).hom := by
  subst hm
  exact homologyπ_eq_zero_iff (K.sc n)

theorem iCycles_injective' : Function.Injective (K.iCycles n).hom :=
  iCycles_injective (K.sc n)

/-- The degree-`n` cycle determined by an element killed by the differential to degree `j`. -/
noncomputable def cyclesMkOfEq' (x : K.X n) (j : ι) (hj : c.next n = j)
    (hx : (K.d n j).hom x = 0) : K.cycles n :=
  cyclesMkOfEq (K.sc n) x (by subst hj; exact hx)

@[simp]
theorem iCycles_cyclesMkOfEq' (x : K.X n) (j : ι) (hj : c.next n = j)
    (hx : (K.d n j).hom x = 0) : K.iCycles n (cyclesMkOfEq' K x j hj hx) = x := by
  subst hj
  exact iCycles_cyclesMkOfEq (K.sc n) x _

/-- The differential vanishes on the underlying element of a cycle. -/
@[simp]
theorem d_iCycles_apply (j : ι) (z : K.cycles n) : (K.d n j).hom (K.iCycles n z) = 0 := by
  have h := ConcreteCategory.congr_hom (K.iCycles_d n j) z
  simpa only [ConcreteCategory.comp_apply, TopModuleCat.hom_zero_apply] using h

/-- The underlying element of the boundary cycle `K.toCycles i n x` is `d x`. -/
@[simp]
theorem iCycles_toCycles_apply (i : ι) (x : K.X i) :
    K.iCycles n (K.toCycles i n x) = (K.d i n).hom x := by
  have h := ConcreteCategory.congr_hom (K.toCycles_i i n) x
  simpa only [ConcreteCategory.comp_apply] using h

variable {K} in
/-- A chain map carries the class of an elementwise cycle to the class of its image. -/
theorem homologyMap_homologyπ_cyclesMkOfEq {L : HomologicalComplex (TopModuleCat R) c}
    (f : K ⟶ L) [K.HasHomology n] [L.HasHomology n] (x : K.X n) (j : ι)
    (hj : c.next n = j) (hx : (K.d n j).hom x = 0) :
    HomologicalComplex.homologyMap f n (K.homologyπ n (cyclesMkOfEq' K x j hj hx)) =
      L.homologyπ n (cyclesMkOfEq' L ((f.f n).hom x) j hj (by
        have h := ConcreteCategory.congr_hom (f.comm n j) x
        simp only [ConcreteCategory.comp_apply] at h
        change (L.d n j).hom ((f.f n).hom x) = 0
        rw [h, hx, map_zero])) := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply]
  congr 1
  apply iCycles_injective' L
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i, ConcreteCategory.comp_apply,
    iCycles_cyclesMkOfEq', iCycles_cyclesMkOfEq']

end Complex

end ZInQ.Contrib.BrauerCohomology.TopHom
