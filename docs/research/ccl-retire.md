# Retirement of the old Cai–Chen–Liu transport

The retirement removes the generic unweighted witness `CCLThm2_15Applied`
and its old transport. In the recorded reading of Cai–Chen–Liu, *Trans.
Amer. Math. Soc.* 370 (2018), Theorem 2.15, p. 3730, `u_m` multiplies the
relative trace. In the manuscript’s application, `diophantine_zq.tex`
2914–2936, `c = d` and `m = 1`, so the factor is the unit index
`[𝒪_K^× : ℤ^×]`. The old witness permits discriminant −4 and omits the
factor. The staged chain uses `CCLThm2_15AppliedWithUnits`, discharges the
factor using its companion data, and uses `HeegnerPointData.NormRelations`
for the point equations that feed the cochain identity with the boundary
term at tex 4157–4172. [Retirement plan](ccl-unit-index2.md#retirement-at-fold)

## Deletions and move

Paths below are relative to `ZInQKernel/Contrib/`.

- `OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean` and `e2ProviderOn`,
  `e2ProviderOn_succ`, `CommonCoordinateInputsGenuineE2`,
  `commonCoordinateInputsGenuineK_of_E2`,
  `commonCoordinateInputsNF_of_genuineE2`, and
  `commonCoordinateTarget_of_genuineE2`.
- `OneProof/RC/Wiring/CommonCoordinate18E2.lean` and `classSupport`,
  `ActualPresentation.ps_getD_pos`, `ActualPresentation.ps_getD_prime`,
  `E2ChainInputs`, and `e2Provider`. The declarations in the
  `E2ChainInputs` namespace were `chainCond_pos`, `chainCond_coprime`,
  `cond_not_mem`, `mem_S_of_cond`, `classSupport_subset`, `hSd`, `hm`,
  `hgood'`, `hpl`, `hfd_cond`, `datum`, `anchor`, `hcop`, `hadmD`,
  `hsplitD`, `g`, `hanti`, `hwd`, `stepFactor_eq`, `hG`, and `hloc`.
  Deleting the two structures also removes their generated declarations.
- `CloudB3E2Norm/H20HeegnerNorm.lean` and `HeegnerTransportAt`,
  `hnorm_of_normRelations`, `hnorm_of_print`, and `nonVacuity_transport`.
- `hnorm_of_print_on` in `CloudB3E2Norm/H20Transport.lean` and
  `CCLGenuine` and `hnorm_of_genuine_print` in
  `CloudB3E2Norm/H20Anchor.lean`. `H20Transport` now imports
  `PrintsArith.Heegner` directly for the subgroup transport.
- `CCLThm2_15Applied` in `OneProof/RC/PrintsArith/Heegner.lean`.

`chainCond` and `dvd_chainCond` moved to `OneProof/RC/Wiring/ChainCond.lean`.
`CommonCoordinate19E2` imports it along with the existing transport and
moving-character modules. The base audit records the three imports of
retired modules and the declaration references. There was no aggregate
import of a retired module. [Consumer audit](../../scratch/ccl-retire/log.md)

## Respelled premises

Each of these theorems takes
`∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K … D`.
This is the body of its former premise and the result that the staged
bridge already supplies.

- `CloudB3E2Norm/H20DictFields.lean` → `hnorm_of_full_anchor`
- `CloudB3E2Norm/H20PresClass.lean` → `gx_step_anchored`
- `CloudB3E2Norm/H20PresClassOf.lean` → `gx_step_heegner`
- `CloudB3E2Norm/H20PresClassMatch.lean` → `gx_step_heegner_at`

## Verification

Lake passed 39 distinct targets, including `ZInQKernel.OneProof.Main`,
`ZInQKernel.OneProof.Discharges`, all 18 surviving direct base importers
of edited or deleted modules, and the edited modules and their
prerequisites. The 21 checks in `Check.lean` cover the 20 declarations
from the unit-index report and `ZInQ.OneProof.frozenTarget`. Every check
reported only `propext`, `Classical.choice`, and `Quot.sound`.
[Build list](../../scratch/ccl-retire/builds.txt) ·
[Axiom script](../../scratch/ccl-retire/Check.lean) ·
[Axiom output](../../scratch/ccl-retire/axioms.txt)

## Known issues

- The journal formula uses the reading recorded in the unit-index report.
  The manuscript’s cited PDF could not be retrieved for an independent
  reread. The mathematical issue recorded here is in the old Lean witness.
  [Prior verification](ccl-unit-index2.md#known-issues)
- The global compatibility of the CM point family and the comparison of
  the analytic parametrization with the algebraic map remain existing
  GLUE identifications of the weighted applied interface.
  [Manuscript check](ccl-unit-index2.md#manuscript-check)
- Historical notes and comments outside the retirement plan still refer
  to the older names. The base audit identifies those references.
  [Consumer audit](../../scratch/ccl-retire/log.md)
- The base fetch returned HTTP 403. The preexisting local base and remote
  tracking ref both matched the supplied SHA.
