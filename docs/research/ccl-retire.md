# Cai–Chen–Liu retirement

The retirement was checked at `f5299bb9d6f9ada2fcd170099f784f0e0945bf79`,
which merges main `29bfbc3f6793d98b7c1ac637f9728fe51e701e5b` and includes
the two review docstring fixes. The staged chain supplies the full-anchor
witness after proving the unit factor is one.
[Retirement plan](ccl-unit-index2.md#retirement-at-fold) ·
[Prior consumer audit](../../scratch/ccl-retire2/log.md) ·
[Verification log](../../scratch/ccl-retire4/log.md)

## Deleted declarations and files

Paths below are relative to `ZInQKernel/Contrib/`. Structure-generated
declarations are covered by the removal of their parent structures.

- `OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean` contained
  `e2ProviderOn`, `e2ProviderOn_succ`, `CommonCoordinateInputsGenuineE2`
  (fields `elliptic`, `milne`, `iwasawa`, `chains`),
  `commonCoordinateInputsGenuineK_of_E2`,
  `commonCoordinateInputsNF_of_genuineE2`, and
  `commonCoordinateTarget_of_genuineE2`.
- `OneProof/RC/Wiring/CommonCoordinate18E2.lean` contained
  `classSupport`, `ActualPresentation.ps_getD_pos`,
  `ActualPresentation.ps_getD_prime`, `E2ChainInputs`, and `e2Provider`.
  The fields of `E2ChainInputs` were `cp`, `emb`, `κ`, `print`,
  `hψ`, `d`, `hd`, `hd2`, `hdS0`, `htwo`, `hgood`, `hsep`,
  `hq`, `hsplit`, `f`, `hf`, `hθ`, and `hfd`. Its namespace
  contained `chainCond_pos`, `chainCond_coprime`, `cond_not_mem`,
  `mem_S_of_cond`, `classSupport_subset`, `hSd`, `hm`, `hgood'`,
  `hpl`, `hfd_cond`, `datum`, `anchor`, `hcop`, `hadmD`, `hsplitD`,
  `g`, `hanti`, `hwd`, `stepFactor_eq`, `hG`, and `hloc`.
  The staged import now takes `chainCond` and `dvd_chainCond` from
  `OneProof/RC/Wiring/ChainCond.lean` and imports its other
  dependencies directly. [Conductor definitions](../../ZInQKernel/Contrib/OneProof/RC/Wiring/ChainCond.lean)
- `CloudB3E2Norm/H20HeegnerNorm.lean` contained `HeegnerTransportAt`,
  `hnorm_of_normRelations`, `hnorm_of_print`, and `nonVacuity_transport`.
- `CloudB3E2Norm/H20Transport.lean` lost `hnorm_of_print_on` and now
  imports `PrintsArith.Heegner` directly for its subgroup transport.
  [Subgroup transport](../../ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean)
- `CloudB3E2Norm/H20Anchor.lean` lost `CCLGenuine` and
  `hnorm_of_genuine_print`. The full-anchor dictionary uses
  `GenuineHeegnerAnchor` and its coordinate lemmas.
  [Anchor](../../ZInQKernel/Contrib/CloudB3E2Norm/H20Anchor.lean)
- `OneProof/RC/PrintsArith/Heegner.lean` lost
  `CCLThm2_15Applied`. The staged application starts with
  `CCLThm2_15AppliedWithUnits`, then derives the anchored
  `HeegnerPointData.NormRelations` that the additive transport takes.
  [Arithmetic interface](../../ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean)

## Respelled premises

Each premise unfolds the retired abbreviation at the same full anchor.

| Declaration | Explicit premise |
| --- | --- |
| `H20DictFields.hnorm_of_full_anchor` | `∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K p ι κ D` |
| `H20PresClass.gx_step_anchored` | `∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D` |
| `H20PresClassOf.gx_step_heegner` | `∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D` |
| `H20PresClassMatch.gx_step_heegner_at` | `∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D` |

## Builds and axioms

All 47 Lake targets passed in separate invocations under a 60 GiB
memory cap. They cover the proof and discharge roots, the new conductor
module, the previous build targets, every changed project module still
present, and the nine downstream modules that lost `H20HeegnerNorm`
from their import closure. The three retired module paths have no
surviving imports. [Build results](../../scratch/ccl-retire4/builds.txt)

The rerun of `scratch/ccl-retire/Check.lean` checked 21 declarations,
including `ZInQ.OneProof.frozenTarget`. The only axioms reported were
`propext`, `Classical.choice`, and `Quot.sound`.
[Axiom output](../../scratch/ccl-retire4/axioms.txt)

## Count

**Count lowered: none.** At `f5299bb9d6f9ada2fcd170099f784f0e0945bf79`,
the import closures contain 10,587 project modules for
`ZInQKernel.OneProof.Main` and 380 for the type of `hRC`, including
their respective roots. Both module sets match pinned main and
exclude every changed or deleted module.
[Closure evidence](../../scratch/ccl-retire4/log.md#import-closure-and-count)

`hRC` is an explicit hypothesis of `ZInQ.OneProof.frozenTarget` at
`ZInQKernel/OneProof/Main.lean:269`. Its type is defined at
`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean:217`, and its GLUE
entry is at `docs/one-proof/kinds.tsv:23` and `docs/one-proof/OPEN.md:149`.
The retirement removes zero `frozenTarget` fields and zero GLUE or LEAF
rows. The H part has 21 hypotheses, with 4 published and 17 GLUE under
the strict reading at `docs/one-proof/OPEN.md:16` and
`docs/one-proof/OPEN.md:18`.
[Main](../../ZInQKernel/OneProof/Main.lean#L269) ·
[Type of hRC](../../ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean#L217) ·
[GLUE entry](../one-proof/OPEN.md#hrc)

## Known issues

- The retired unweighted application allowed `d = 1` under generic
  premises that can hold at `D_K = -4`. The staged path uses the
  manuscript's companion field exclusion and proves the unit factor
  equals one before applying the unweighted norms.
  [Prior counterexample checks](../../scratch/ccl-unit-index/Check.lean) ·
  [Manuscript point relations](../../diophantine_zq.tex#L2914)
- The earlier level shortcut fails modulo 8 because `2² ≡ −4 mod 8`.
  The modulo-16 proof excludes the two exceptional discriminants
  under its level hypothesis. The staged path uses the companion
  data. [Unit-index proofs](../../ZInQKernel/Contrib/OneProof/RC/CCLUnitIndex/Units.lean)
- The report uses the recorded reading of Cai–Chen–Liu, Theorem 2.15,
  Trans. Amer. Math. Soc. 370 (2018), p. 3730. The manuscript's use at
  `diophantine_zq.tex:2914` through `diophantine_zq.tex:2936` agrees
  with that reading. The journal page still awaits an independent
  reread. Global compatibility of the point family and the
  analytic-to-algebraic parametrization comparison remain inputs.
  [Prior source and manuscript audit](ccl-unit-index2.md#manuscript-check)
- The Lean comments that named the retired witness or wiring now point
  at `CCLThm2_15AppliedWithUnits`, `E2ChainInputsS`,
  `CommonCoordinateInputsGenuineS` and `hnorm_of_normRelations_on`. The
  comments that labelled the unweighted relation (4.1) as the print
  (in the CCL, Wiring, BaseZero, HeegnerAlgebra and GlueSweep files) now
  say it is the print only once the unit index is one (`D_K < -4`). The
  Kinds lines of `H20Transport`, `H20Anchor` and `H20DictFields` are
  restored without the retired name. [Retired-name check](../../scratch/ccl-retire4/log.md#retired-names)
