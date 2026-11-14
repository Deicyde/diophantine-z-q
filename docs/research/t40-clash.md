# t40-clash: T40 can now be imported next to the other Contrib Tau Ceti modules

## Verdict

Fixed. `ZInQKernel.Contrib.RLeaf.T40` (T40 and T39 from the single leaf `X0Transitive`, tasks
t40-tate and t40-igusa) now imports in the same Lean environment as
`ZInQKernel.Contrib.Mobius.Main`, the frob-chain Contrib modules, `ZInQKernel.Contrib.GZTheta.ALFinal`,
`ZInQKernel.Contrib.RLeaf.T36Torsion` and the vendored
`ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic`
(`scratch/t40-clash/Together.lean`, see section 4 for the run). The fix changes one Lean file,
`ZInQKernel/Contrib/TauCeti/Backport/Algebra/Group/Units/Basic.lean`, and adds one line to the
modified list in `ThirdParty/TauCeti/NOTICE`. No pinned file, no RLeaf file and no other
Backport/ file was touched.

## 1. The clash

`git grep -n val_mul_zpow_natCast_mul` finds two declarations:

| name | vendored `TauCeti/Algebra/GroupWithZero/Units/Basic.lean` (commit 5a01f5fe) | t40-tate's `TauCeti/Backport/Algebra/Group/Units/Basic.lean` (commit 4d91513e) |
|---|---|---|
| `Units.val_mul_zpow_natCast_mul` | `[CommGroupWithZero K]` | `[DivisionCommMonoid M]` |
| `Units.val_mul_zpow_neg_natCast_succ_mul` | `[CommGroupWithZero K]` | `[DivisionCommMonoid M]` |
| `TauCeti.mem_range_iff_exists_units_map_eq` | `MonoidWithZeroHomClass` out of a group with zero, `[Nontrivial M₀]` | `MonoidHomClass` with `[IsLocalHom f]` |

So three names clash, not one. In each case the statement is the same, and the Backport copy is
Tau Ceti's later generalization: between the two commits Tau Ceti moved these lemmas from the
group-with-zero file to the monoid file. t40-tate's Backport/ file for `Algebra/Group/Units/Basic`
holds what the commit-4d91513e module has and the vendored commit-5a01f5fe module of the
same path lacks. It does not check the vendored *GroupWithZero* module, which still has the old
copies. The two modules never met inside T40's closure, but the GaloisCohomology modules
(`Coefficients`, `Inflation`, `Kummer`) import the GroupWithZero one, and through them so do most
Contrib consumers of Tau Ceti class field theory.

Reproduction (`scratch/t40-clash/Clash2.lean`, importing those two modules only), before the fix:

```
Clash2.lean:2:0: error: import ZInQKernel.Contrib.TauCeti.Backport.Algebra.Group.Units.Basic failed,
environment already contains 'Units.val_mul_zpow_natCast_mul' from
ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic
```

## 2. The fix

`Backport/Algebra/Group/Units/Basic.lean` now:

* drops its three copies (`TauCeti.mem_range_iff_exists_units_map_eq`,
  `Units.val_mul_zpow_natCast_mul`, `Units.val_mul_zpow_neg_natCast_succ_mul`);
* adds `public import ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic`, so every
  downstream file still finds the names;
* keeps its only other declaration, `Units.eq_of_mul_mul_inv_eq_of_commute`;
* rewrites its module docstring and extends its `-- Modified for the Z-in-Q kernel: ...` line to
  name the three removed declarations and the reason (task t40-clash).

`ThirdParty/TauCeti/NOTICE` lists the file in its modified list.

Why this is enough. The only uses of the two `val_mul_zpow` lemmas in the repository are four
`simp`/`simpa` calls in
`Backport/AlgebraicGeometry/EllipticCurve/TateCurve/CoordinateEvaluation.lean`. There the
carrier is a `NormedField`, hence a `CommGroupWithZero`, so the vendored statements apply. They
rewrite the same terms as before, and the module builds unchanged. Nothing in the repository
uses the Backport `mem_range_iff_exists_units_map_eq` (the two uses, in GaloisCohomology
`Coefficients` and `Inflation`, already resolve to the vendored group-with-zero version).
Lost: the monoid generalizations of the three lemmas. No Lean file needs them. If one ever
does, it should be added under a new name, because the vendored module owns the old one.

Rejected alternative: renaming the Backport copies (for example with a prime) and updating
`CoordinateEvaluation.lean`. That edits two files instead of one and creates names that exist
neither in Tau Ceti nor in Mathlib, and the generality it would keep is unused.

## 3. Other clashes? (static scan)

`scratch/t40-clash/dupscan.py` is a heuristic scan. For every git-tracked Lean file under
`ZInQKernel/` it collects the declared names (theorem/lemma/def/abbrev/structure/class/
inductive/opaque/axiom, with `namespace`/`end` tracking, `_root_` handled, `private` skipped). It
then reports names declared in two files where one file lies in T40's forward import closure
(350 files) and the other lies outside it. After the fix the only hits are false positives:
docstring words matched at the start of a line, such as `of`, `is`, `and`, `group`, and
`TauCeti.of`. Instances and auto-generated names are not scanned. The compile test in
section 4 is the real check for the modules it imports.

The scan does find pre-existing parallel copies elsewhere: Backport `Global/Kummer/Norm`,
`Kummer/AuxiliaryPlaces`, `PrescribedInvariant` and `Ideles/Ray/ClassQuotient` against their
vendored namesakes, from tasks kw-new and ring-class. Neither copy is in T40's closure, and
NOTICE records that those Backport files replace the vendored ones rather than sit beside them.
So they are outside this task. Code that imports a vendored file and its Backport/ replacement
together would hit the same kind of error.

## 4. What compiles

All runs used `lake build` or `lake env lean` from the worktree, one Lean process at a time.

1. `scratch/t40-clash/Clash2.lean` (the two clashing modules together): fails before the fix
   (section 1) and compiles after it.
2. `lake build ZInQKernel.Contrib.RLeaf.T40 ZInQKernel.Contrib.RLeaf.TateCuspTorsion`: success
   (9396 jobs, 3 min, no errors). The `#print axioms` lines of T40.lean report
   `[propext, Classical.choice, Quot.sound]`. These two targets cover every module that imports
   the changed file, directly or transitively (`scratch/t40-clash/rdeps.py`):
   Backport TateCurve `CoordinateEvaluation`, `Equation`, `Line`, `XCoordinate`,
   `Uniformization`, `Injectivity`, `Homomorphism`, and RLeaf `TateCusp`, `TateCuspMuN`,
   `TateCuspTorsion`, `T40`. Every one of them was rebuilt in this run.
3. `scratch/t40-clash/Together.lean` imports `RLeaf.T40`, `Mobius.Main`,
   `FrobPieces.SmoothGeomConnIntegral`, `Chebotarev.FrobeniusDense`, `AbsFrob.Basic`,
   `GZTheta.ALFinal`, `RLeaf.T36Torsion` and `TauCeti.Algebra.GroupWithZero.Units.Basic`, and
   `#check`s the three formerly clashing names, `Units.eq_of_mul_mul_inv_eq_of_commute` and
   T40's `x1RationalCusp_of_x0Transitive` / `x1ConstantField_of_x0Transitive`. First
   `lake build` of the six Contrib imports: success (10690 jobs, 8.5 min, no errors). Then
   `lake env lean scratch/t40-clash/Together.lean`: **compiles**, and every `#check` prints
   (section 5).

There is no module `ZInQKernel.Contrib.FrobChain`. The frob-chain Contrib modules are
`FrobPieces/`, `Chebotarev/` and `AbsFrob/`, and the test imports one module from each.

## 5. Result of the together test

`Together.lean` compiles with no errors. Output:

```
@Units.val_mul_zpow_natCast_mul : ∀ {K : Type u_1} [inst : CommGroupWithZero K] (u v : Kˣ) (n : ℕ),
  ↑(u * v) ^ ↑n * ↑u = ↑u ^ (n + 1) * ↑v ^ n
@Units.val_mul_zpow_neg_natCast_succ_mul : ... [inst : CommGroupWithZero K] ...
@TauCeti.mem_range_iff_exists_units_map_eq : ... [inst : GroupWithZero G₀] ... [inst_4 : MonoidWithZeroHomClass F G₀ M₀] ...
@Units.eq_of_mul_mul_inv_eq_of_commute : ∀ {A : Type u_1} [inst : Monoid A] {a z : A} (u : Aˣ),
  ↑u * a * ↑u⁻¹ = z → Commute z ↑u → a = z
ZInQ.RLeaf.x1RationalCusp_of_x0Transitive : ZInQ.RLeaf.X0Transitive → X1Belyi.X1RationalCusp
ZInQ.RLeaf.x1ConstantField_of_x0Transitive : ZInQ.RLeaf.X0Transitive → X1Belyi.X1ConstantField
```

Caveat: none of the six named Contrib modules (`Mobius.Main`, `FrobPieces.SmoothGeomConnIntegral`,
`Chebotarev.FrobeniusDense`, `AbsFrob.Basic`, `GZTheta.ALFinal`, `RLeaf.T36Torsion`) imports
`TauCeti.Algebra.GroupWithZero.Units.Basic` (checked on their forward import closures). So
those six alone would not have reproduced the clash. `Together.lean` therefore also imports
the GroupWithZero module itself, and that import is what exercises the fix. The clash arises with
any module whose closure contains the GaloisCohomology files (`Coefficients`, `Inflation`,
`Kummer`), such as the Kronecker-Weber / class-field Contrib modules. Section 6 covers the
broader test of T40 against all of Contrib.

## 6. T40 against all of Contrib

`ZInQKernel/Contrib/` has 74 top-level modules: those that no other Contrib module imports
(`scratch/t40-clash/contrib-tops.txt`). Their import closures cover all 2027 Contrib modules.

* `lake build` of all 74: success (11928 jobs, 15.7 min, no errors).
* `scratch/t40-clash/AllContrib.lean` imports T40 and the other 73 at once. It **fails on a
  clash that does not involve T40**: `Subgroup.stabilizerInclusion` (and
  `stabilizerInclusion_injective`) is declared both in the vendored commit-5a01f5fe
  `TauCeti/GroupTheory/GroupAction/Stabilizer.lean` and in the vendored commit-97a5b235
  `TauCeti/GroupTheory/GroupAction/Stabilizer/Basic.lean`. Neither file is in T40's closure. The
  clash predates this task, and those files are outside its edit scope. So some pairs of
  existing Contrib modules cannot be imported together with each other, with or without T40.
  Fixing that would be a separate task, done the same way as this one: drop the 97a5b235
  duplicates and import the 5a01f5fe module, or rename.
* Pairwise test `scratch/t40-clash/pairwise.sh`: for each of the 73 other top-level modules
  `M`, compile `import ZInQKernel.Contrib.RLeaf.T40` + `import M` with `lake env lean`, one after
  another. **73/73 compile** (`scratch/t40-clash/pairwise-result.txt`). An import clash is a
  property of a pair of modules, and every Contrib module lies in the closure of some top-level
  module. So the pairwise test shows that T40's closure clashes with no Contrib module. Eight
  of the 73 contain `GroupWithZero.Units.Basic` in their closure and so clashed with T40 before
  the fix: `KroneckerWeber.Leaves`, `LocalKW.T30`, `T14.WP3`, `TYZGenus.ShimuraFricke`, and the
  Tau Ceti modules `FieldTheory.GaloisCohomology.Congr`,
  `ClassFieldTheory.Global.Kummer.AuxiliaryPlaces`, `Global.Kummer.Norm` and
  `Global.PrescribedInvariant`.

Strictly, the pairwise test checks clashes between T40's closure and each other module, not
clashes among the other modules. That second kind is the Stabilizer clash above, and it
predates T40.

## What remains

* Nothing for T40: it can join the H assembly's import set.
* Pre-existing, not T40: `Subgroup.stabilizerInclusion` is declared twice
  (`TauCeti/GroupTheory/GroupAction/Stabilizer.lean` and `.../Stabilizer/Basic.lean`). An
  assembly that needs modules from both sides will hit it.
* The heuristic scan (section 3) does not look at instances or auto-generated names. For the
  T40 side, the pairwise compile test makes up for that.

## Files

* `ZInQKernel/Contrib/TauCeti/Backport/Algebra/Group/Units/Basic.lean`: the fix.
* `ThirdParty/TauCeti/NOTICE`: one entry in the modified list.
* `scratch/t40-clash/Clash2.lean`: two-import reproduction.
* `scratch/t40-clash/Together.lean`: T40 with the assembly's Contrib modules.
* `scratch/t40-clash/rdeps.py`: reverse import closure of a module over the tracked files.
* `scratch/t40-clash/dupscan.py`: heuristic duplicate-declaration scan.
* `scratch/t40-clash/AllContrib.lean`: T40 with all 73 other top-level Contrib modules (fails on the
  pre-existing Stabilizer clash, section 6).
* `scratch/t40-clash/pairwise.sh`, `contrib-tops.txt`, `pairwise-result.txt`: the pairwise test.
* `scratch/t40-clash/log.md`: results log.
