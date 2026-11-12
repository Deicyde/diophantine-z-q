# obj-bridge results log

## Step 1 (23:3x PST): shared layer + bijection — VERIFIED (compiled)
- File: scratch/obj-bridge/Objects.lean. §A = scratch/pkg-I3/I3.lean verbatim; §B = scratch/pkg-I2/I2.lean
  verbatim minus `goodReduction_of_QM_rational3` (sorry there); §C shared layer; §D restated leaves.
- Shared object: `Grp (Over (Spec (.of K)))` + `[PkgI2.IsAbelianVariety A]`, `K : Type`.
- `ObjBridge.ofGrp` (plain def; `@[reducible]` broke instance search for `Ring (End _)`),
  `toGrp`, `ofGrp_toGrp`/`toGrp_ofGrp` both `rfl`.
- Needed instance `ObjBridge.isCommMonObj : IsCommMonObj A.X` for Grp objects (instance search
  cannot see I3's `IsCommMonObj (A : AbVar).X` through `ofGrp`).
- `homOfGrp`, inverse `grpOfHom` (= `Grp.homMk`), `homEquiv : (A ⟶ B) ≃ Hom A B`,
  `homOfGrp_bijective`; `endMulEquiv : CategoryTheory.End A ≃* End A` (Mathlib 4.35 `End` is a
  structure `End.of`/`asHom`); `homOfGrp_eq_zero_iff`, `hom_sum_zsmul`, `forall_hom_iff`.
- Points: `pts_eq`, `galAct_eq`, `galHom_eq`: I2's and I3's definitions agree by `rfl` for fields.

## Step 2: restated leaves — VERIFIED (compiled, no errors; axioms propext, Classical.choice, Quot.sound)
- I2 (universe 0): PurityBranchLocus, NeronOggShafarevich, SerreTatePotentialGood,
  GrothendieckMonodromy, RaynaudCriterion, NeronMappingAbelianScheme, ReductionTorsionBijective,
  TorsionStructure (dim A), AbhyankarDVR: each `Iff.rfl` with `PkgI2.X.{0}`.
- I2-Char `CharpolyIndependentOfEll` (φ : End B): iff via homOfGrp/grpOfHom, term proof.
- I2-Rank `HomRankBound` (∑ c i • f i = 0 in Hom A B): iff via bijection + hom_sum_zsmul.
- I3: EndDivision (Iff.rfl), FaltingsSemisimple, FaltingsTate (needed abstracted motive
  `forall₂_abVar_iff`; direct term timed out at whnf, 200000 heartbeats), TateModuleFree,
  HomFreeFinite, CharPolyIndepOfEll (+ `_iff_grp` form over φ : A ⟶ A), PoincareReducibility,
  QMDichotomy, I3Leaves: each `_iff` proved.
- I3 glue restated & proved: homT_galT, range_tateHomZl_subset, exists_hom_ne_one_of_equivariant
  (conclusion: ∃ f : A ⟶ B, f.hom.hom ≠ 1), equivEnd, finrank_equivEnd.

## Step 3: base change and functoriality — VERIFIED (compiled)
- `isAbelianVariety_baseChange`: I2's `baseChange` (mapGrp of Over.pullback) of an abelian variety
  is one (fields taken from I3's `AbVar.baseChange`).
- `ofGrp_baseChange : ofGrp (PkgI2.baseChange A L) = (ofGrp A).baseChange L := rfl`.
- `ptMap_homOfGrp` (rfl), `homT_comp`, `homT_id` (T_ℓ is a functor on the shared objects).
- `rw` fails on goals mixing `(ofGrp A).X` and `A.X` (motive not type correct); `exact congrArg ..`
  works.
- Final compile: `lake env lean scratch/obj-bridge/Objects.lean`: no errors; every audited
  declaration depends only on propext, Classical.choice, Quot.sound. File has no sorry/axiom.
