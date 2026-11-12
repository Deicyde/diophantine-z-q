# obj-bridge: a shared object layer for the I2 and I3 leaves

## Main result (VERIFIED: compiled)

`scratch/obj-bridge/Objects.lean` compiles with `lake env lean` and has no errors, no `sorry`
and no `axiom`. Every audited declaration depends only on `propext`, `Classical.choice` and
`Quot.sound`. The file contains:

1. **One object layer.** The object is I2's `Grp (Over (Spec K))` with
   `[PkgI2.IsAbelianVariety A]`, with `K : Type` as the single universe. I3's `Hom`, `End`, `End⁰`,
   `T_ℓ`, `V_ℓ`, `galRep`, `dim` and `tateHomZl` reach it through `ObjBridge.ofGrp`. The
   abbreviations are `ObjBridge.Hom A B`, `End A`, `End0 A`, `T A ℓ`, `V A ℓ`, `galRep A ℓ`,
   `dim A` and `tateHomZl A B ℓ`.
2. **The bridge is a bijection on objects and on morphisms.**
   - On objects, `toGrp : AbVar K → Grp …` comes with an `IsAbelianVariety` instance, and both
     round trips hold by `rfl`: `ofGrp_toGrp` and `toGrp_ofGrp`.
   - On morphisms, `homOfGrp : (A ⟶ B) → Hom A B` has the inverse `grpOfHom` (built with
     `Grp.homMk`). Together they give `homEquiv : (A ⟶ B) ≃ Hom A B` and `homOfGrp_bijective`.
   - The bridge respects composition and identities. `homOfGrp_comp_end` gives
     `homOfGrp (f ≫ g) = homOfGrp g * homOfGrp f`, and `endMulEquiv` is a monoid isomorphism
     `CategoryTheory.End A ≃* End A`.
   - Zero and sums: `homOfGrp_eq_zero_iff` says `homOfGrp f = 0 ↔ f.hom.hom = 1`. `hom_sum_zsmul`
     says that `∑ cᵢ • fᵢ` corresponds to `∏ fᵢ.hom ^ cᵢ`.
3. **One definition of points, Galois action and base change.**
   - Points, Galois action, torsion, inertia and good reduction are I2's definitions. For a field
     `L` they are I3's by `rfl`: `pts_eq`, `galAct_eq`, `galHom_eq`, `mem_torsion_iff`.
   - I2's base change (`mapGrp` of `Over.pullback`) of an abelian variety is again an abelian
     variety (`isAbelianVariety_baseChange`).
   - `ofGrp_baseChange : ofGrp (PkgI2.baseChange A L) = (ofGrp A).baseChange L` holds by `rfl`.
   - `T_ℓ` is a functor on the shared objects: `homT_comp`, `homT_id`. A morphism acts on points
     by composition: `ptMap_homOfGrp`.
4. **Every leaf restated, with a proof of equivalence with the original.**

   | Leaf | Restatement in `ObjBridge` | Equivalence with the original |
   |---|---|---|
   | I2-P, I2-NOS, I2-ST2, I2-SS, I2-Ray, I2-NMP, I2-Red, I2-AbDVR | I2's text at `Type` | `Iff.rfl` with `PkgI2.X.{0}` |
   | I2-Tors | as above, with `dim A` | `Iff.rfl` |
   | I2-Char `CharpolyIndependentOfEll` | `φ : End B` instead of `φ : B ⟶ B` | `charpolyIndependentOfEll_iff`, a term proof through `homOfGrp`/`grpOfHom` |
   | I2-Rank `HomRankBound` | `∑ cᵢ • fᵢ = 0` in the ℤ-module `Hom A B` | `homRankBound_iff`, through the bijection and `hom_sum_zsmul` |
   | I3 `EndDivision` | over `End A` | `Iff.rfl` |
   | I3.F1, F2, M0, M1, M2, M3, Q | `A : Grp …` with `[IsAbelianVariety A]` | `*_iff`, round trips through `toGrp`/`ofGrp` |
   | I3.M2, second form | `φ : A ⟶ A` (`charPolyIndepOfEll_iff_grp`) | through `forall_hom_iff` |
   | `I3Leaves` | the structure | `i3Leaves_iff` |

5. **The I3 glue restated and proved over the shared layer.**
   - `homT_galT` and `range_tateHomZl_subset`.
   - `exists_hom_ne_one_of_equivariant`: a nonzero equivariant map `V_ℓ A → V_ℓ B` gives a
     morphism of group objects `f : A ⟶ B` with `f.hom.hom ≠ 1`.
   - `equivEnd` and `finrank_equivEnd`.
6. **One leaf removed (new).** `homRankBound_of_homFreeFinite` proves that I2-Rank follows from
   I3.M1. Its form for the original definitions is `pkgI2_homRankBound_of_pkgI3_homFreeFinite`,
   from `PkgI3.HomFreeFinite` to `PkgI2.HomRankBound.{0}`. **I2-Rank therefore does not need to
   be announced as a separate leaf.**

## How the file is organised

- §A is `scratch/pkg-I3/I3.lean`, copied verbatim. It provides `PkgI3.*`: the Tate module,
  `AbVar`, the leaves and the glue.
- §B is `scratch/pkg-I2/I2.lean`, copied verbatim with one omission: the glue theorem
  `goodReduction_of_QM_rational3` (A6), whose proof in pkg-I2 is `sorry`. §B provides `PkgI2.*`.
- §C is the shared layer and the bijection. §D contains the restated leaves, the equivalences and
  the I3 glue. §E covers base change and functoriality, §F the I2-Rank consolidation.

The copies are there because scratch files cannot import each other. They let every equivalence be
stated against the original constants. To integrate the work, keep §C–§F and replace §A/§B with
imports.

## Technical findings (VERIFIED, from compiling)

- `ofGrp` has to be a plain `def`. With `@[reducible]`, `(ofGrp A).X` reduces to `A.X`, and
  instance search then cannot find I3's `Ring (End _)` or `IsCommMonObj (_ : AbVar).X`.
- Instance search cannot see I3's `IsCommMonObj` instance through `ofGrp`. The shared layer
  therefore needs its own instance `ObjBridge.isCommMonObj : IsCommMonObj A.X` for Grp objects,
  derived from Mathlib's `isCommMonObj_of_isProper_of_geometricallyIntegral`.
- Mathlib 4.35's `CategoryTheory.End X` is a structure (`End.of`, `asHom`), not a synonym for
  `X ⟶ X`. `endMulEquiv` goes through `End.homEquiv`.
- Proving `faltingsTate_iff` directly as a term hit the 200000-heartbeat limit (in `whnf`). It
  works once the motive is abstracted (`forall₂_abVar_iff`), so that `ofGrp (toGrp A) = A` is
  checked by structure eta.
- `rw` fails on goals that mix `(ofGrp A).X` and `A.X` (the motive is not type correct).
  `exact congrArg …` works.

## What remains

- The I2 glue theorems `inertiaTrivial_of_goodReduction`, `fixed_of_unipSq_of_iterate` and
  `D2_fixed_of_raynaud` were already stated over the shared object and the shared points. They are
  usable unchanged at universe 0 and are kept in §B. A6 (`goodReduction_of_QM_rational3`) is
  still `sorry` in pkg-I2 and is not restated here.
- Two more consolidations look possible but are not proved: I2-Tors (finite level) against I3.M0
  (`T_ℓ` free of rank `2g`), and I2-Char (finite level) against I3.M2 (`V_ℓ`). In both cases the
  two leaves are stated at different levels, so going between them would need surjectivity of
  `T_ℓ A → A[ℓⁿ]`, which is not available here.
- No change to the faithfulness verdicts of rv-leaves-b. The restated leaves are equivalent to the
  originals, so those verdicts carry over.
