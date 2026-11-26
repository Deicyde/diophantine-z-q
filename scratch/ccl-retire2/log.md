# Cai–Chen–Liu retirement consumer audit

Pinned main `2ba691fde6bfb9e514a429414ba92a6c6893a63f`. Merged base `5222492581202af090762d7ac62d6b042de53865`.
The requested fetch returned HTTP 403. Both pinned commits were present locally
and the merge completed cleanly.

`git grep -I -n -E` searched production Lean sources for the deleted modules
and declarations, the moved conductor definitions, and the member names of the
two deleted structures. The exact-name search and the direct-import search
also ran on pinned main, where the retired definitions are still present.
The earlier base (`a59ea33fe90ba2b0aa39f896137097180aad5f6e`) provides the comparison for new uses.

Exact names searched:

```text
ActualPresentation.ps_getD_pos ActualPresentation.ps_getD_prime CCLGenuine CCLThm2_15Applied CommonCoordinate18E2 CommonCoordinate18LeafE2 CommonCoordinateInputsGenuineE2 E2ChainInputs H20HeegnerNorm HeegnerTransportAt chainCond classSupport commonCoordinateInputsGenuineK_of_E2 commonCoordinateInputsNF_of_genuineE2 commonCoordinateTarget_of_genuineE2 dvd_chainCond e2Provider e2ProviderOn e2ProviderOn_succ hnorm_of_genuine_print hnorm_of_normRelations hnorm_of_print hnorm_of_print_on nonVacuity_transport ps_getD_pos ps_getD_prime
```

Member names searched, including projections and namespace lemmas:

```text
anchor chainCond_coprime chainCond_pos chains classSupport_subset cond_not_mem cp d datum elliptic emb f g hG hSd hadmD hanti hcop hd hd2 hdS0 hf hfd hfd_cond hgood hgood' hloc hm hpl hq hsep hsplit hsplitD htwo hwd hθ hψ iwasawa mem_S_of_cond milne print stepFactor_eq κ
```

## Exact-name matches added on pinned main since the earlier base

```text
(none)
```

## Exact-name matches on the merged base

```text
ZInQKernel/Contrib/CloudB3E2Norm/CochainNorm.lean:60:   actual classes with the classes of the Heegner points `y_T` (the anchor of `CCLThm2_15Applied`).
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:48:    ∀ j, q ∣ chainCond d ps j → q ∣ d ∨ ∃ m < j, q ∣ ps.getD m 1
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:201:      exact not_two_primes (P.ps_getD_prime hi) (P.ps_getD_prime hj) hne hmem hjmem
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:204:      have hqp := P.ps_getD_prime hi
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:228:              have hpm := P.ps_getD_prime hmi
ZInQKernel/Contrib/CloudB3E2Norm/GlobalCochain.lean:48:(`CCLThm2_15Applied`'s anchor); (5) the local components `hU`, `hL` (item 3 of the
ZInQKernel/Contrib/CloudB3E2Norm/H20Dictionary.lean:38:  `hnorm_of_print_on`) and (i)–(iv).
ZInQKernel/Contrib/CloudB3E2Norm/H20Dictionary.lean:272:(PROVED from the PRINT `CCLThm2_15Applied` and the field-level dictionary (i)–(iv), tex 2914–2936):
ZInQKernel/Contrib/CloudB3E2Norm/H20PresAssembly.lean:17:* the norm relation `hnorm` (`H20HeegnerNorm.hnorm_of_print`, the Cai–Chen–Liu print), the division
ZInQKernel/Contrib/OneProof/RC/PrintsArith/Bundle.lean:14:statements (`KatoZetaLeaf`, `CCLThm2_15Applied`, `CJReductionData.Thm3_1KappaOne`) are not bundled:
ZInQKernel/Contrib/OneProof/RC/Wiring/ChainCond.lean:5:def chainCond (d : Nat) (ps : List Nat) : Nat → Nat
ZInQKernel/Contrib/OneProof/RC/Wiring/ChainCond.lean:7:  | j + 1 => chainCond d ps j * ps.getD j 1
ZInQKernel/Contrib/OneProof/RC/Wiring/ChainCond.lean:10:theorem dvd_chainCond (d : Nat) (ps : List Nat) : ∀ j, d ∣ chainCond d ps j
ZInQKernel/Contrib/OneProof/RC/Wiring/ChainCond.lean:12:  | j + 1 => Nat.dvd_mul_right_of_dvd (dvd_chainCond d ps j) _
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18Leaf.lean:21:  `CommonCoordinateInputsGenuineE2` discharges it);
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18Leaf.lean:37:    included; `CommonCoordinateInputsGenuineE2` (`CommonCoordinate18LeafE2.lean`) pins it to lane
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18Leaf.lean:38:    E2's classes (`e2Provider`);
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18Leaf.lean:52:`CommonCoordinateInputsGenuineE2` the provider is lane E2's Kummer classes of the actual points
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:195:  P.S₀ s ∪ {v | ((chainCond d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:200:theorem StagedPresentation.ps_getD_pos (P : StagedPresentation C D Fam x G.toFamily) (j : ℕ) :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:210:theorem StagedPresentation.ps_getD_prime (P : StagedPresentation C D Fam x G.toFamily) {i : ℕ}
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:266:    6 * chainCond d P.ps i * CST.newformLevel (Ecurve ℓ) * (discr C.K).natAbs
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:287:theorem chainCond_pos : ∀ j, 0 < chainCond I.d P.ps j
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:289:  | j + 1 => Nat.mul_pos (chainCond_pos j) (P.ps_getD_pos j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:293:theorem chainCond_coprime : ∀ j, Nat.Coprime (chainCond I.d P.ps j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:299:    · refine (Nat.Prime.coprime_iff_not_dvd (P.ps_getD_prime hj)).2 fun h => I.hq j hj ?_
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:300:      exact h.trans ⟨3 * chainCond I.d P.ps j, by ring⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:308:    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∉ (P.pl (p, c)).asIdeal
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:314:    change (((chainCond I.d P.ps j * P.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ (P.pl (p, c)).asIdeal at h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:327:    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ P.S (t + 1)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:330:    change (((chainCond I.d P.ps j * P.ps.getD j 1 : ℕ) : 𝓞 C.K)) ∈ v.asIdeal at h
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:351:    ((chainCond I.d P.ps j : ℕ) : 𝓞 C.K) ∈ v.asIdeal → v ∈ classSupportS P (t + 1) I.d j :=
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:427:theorem hcop (j : ℕ) : Nat.Coprime (chainCond I.d P.ps j) (I.datum.N * I.datum.DK.natAbs) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:434:    I.datum.Admissible (chainCond I.d P.ps i) (P.ps.getD i 1) := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:435:  refine ⟨I.chainCond_pos i, ?_, P.ps_getD_prime hi, ?_⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:449:theorem hα (j : ℕ) [NeZero (chainCond I.d P.ps j)] :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:451:        (heegnerL (chainCond I.d P.ps j) (I.hSd j)) ≤
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:456:  exact h I.hθ (dvd_chainCond I.d P.ps j) (I.hSd j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:462:  haveI : NeZero (chainCond I.d P.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:467:    I.anchor (I.classSupport_subset j) (chainCond I.d P.ps j) (I.hcop j) (I.hSd j) (I.hm j)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:510:theorem hwd {i : ℕ} (hi : i < P.ps.length) [NeZero (chainCond I.d P.ps i)] :
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:513:      ((chainCond I.d P.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:515:        (CST.conductorOrder C.K (chainCond I.d P.ps i)).conductorModulus ∧
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:517:        (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := C.K) (chainCond I.d P.ps i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:520:  have hnot : ((chainCond I.d P.ps i : ℕ) : 𝓞 C.K) ∉ w.1.asIdeal := by
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:525:  have hJ := mem_primeTo_of_not_mem (chainCond I.d P.ps i) (NeZero.ne _) w.1 hnot
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:592:  have : NeZero (chainCond I.d P.ps i) := ⟨(I.chainCond_pos i).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:593:  have : NeZero (P.ps.getD i 1) := ⟨(P.ps_getD_pos i).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:602:    (I.hm i) (I.hm (i + 1)) (I.hgood' i) (I.hgood' (i + 1)) I.d I.hθ (dvd_chainCond I.d P.ps i)
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:640:  have : NeZero (chainCond I.d P.ps j) := ⟨(I.chainCond_pos j).ne'⟩
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19Theta.lean:16:Two inputs of lane E2's class provider (`CommonCoordinate18E2.lean`) are derived here.
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19Theta.lean:209:`E2ChainInputs` (`CommonCoordinate18E2.lean`). -/
```

## Direct imports of changed or retired modules on pinned main

```text
ZInQKernel/Contrib/CloudB3E2Norm/CentralSpec.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:1:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
ZInQKernel/Contrib/CloudB3E2Norm/H20AmbientS.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields
ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor
ZInQKernel/Contrib/CloudB3E2Norm/H20HeegnerNorm.lean:1:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/CloudB3E2Norm/H20PairedLift.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassMatch.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClass
ZInQKernel/Contrib/CloudB3E2Norm/H20ThetaMono.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20HeegnerNorm
ZInQKernel/Contrib/CloudB3E2Norm/H20Untwisted.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20Transport
ZInQKernel/Contrib/CloudB3E2Norm/HeegnerRCBridge.lean:3:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/RingClassMono.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields
ZInQKernel/Contrib/OneProof/RC/CCLUnitIndex/Units.lean:1:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/HeegnerAnchor/Comparison.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor
ZInQKernel/Contrib/OneProof/RC/O7Actual/Reduction.lean:2:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/PrintsArith/Bundle.lean:2:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18E2.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean:2:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:3:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19Leaf.lean:1:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
```

## Direct imports of changed modules on the merged base

```text
ZInQKernel/Contrib/CloudB3E2Norm/CentralSpec.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/E2ChainActual.lean:1:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
ZInQKernel/Contrib/CloudB3E2Norm/H20AmbientS.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields
ZInQKernel/Contrib/CloudB3E2Norm/H20DictFields.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor
ZInQKernel/Contrib/CloudB3E2Norm/H20PairedLift.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassMatch.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/H20PresClassOf.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClass
ZInQKernel/Contrib/CloudB3E2Norm/H20ThetaMono.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/CloudB3E2Norm/H20Transport.lean:1:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/CloudB3E2Norm/H20Untwisted.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20Transport
ZInQKernel/Contrib/CloudB3E2Norm/HeegnerRCBridge.lean:3:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
ZInQKernel/Contrib/CloudB3E2Norm/RingClassMono.lean:1:import ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields
ZInQKernel/Contrib/OneProof/RC/CCLUnitIndex/Units.lean:1:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/HeegnerAnchor/Comparison.lean:2:import ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor
ZInQKernel/Contrib/OneProof/RC/O7Actual/Reduction.lean:2:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/PrintsArith/Bundle.lean:2:import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:3:import ZInQKernel.Contrib.OneProof.RC.Wiring.ChainCond
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19E2.lean:4:import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch
ZInQKernel/Contrib/OneProof/RC/Wiring/CommonCoordinate19Leaf.lean:1:import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
```

The new member-name matches are local binders, prose, or members of
other structures. A qualified-member search on the merge, including
constructors and recursors, found no uses of either deleted structure.
The short `ps_getD_pos` and `ps_getD_prime` references resolve to
`StagedPresentation`. The surviving `chainCond` and `dvd_chainCond`
references use the moved definitions. The other surviving exact-name
matches are comments. No Lean source on the merge imports a retired
module. No deletion needed to be restored during the consumer audit.

## Import closure and count

The import closure was rerun against pinned main and the merge using
`scratch/ccl-unit-index2/closure.py`. A second pass restricted the
graph to Lean import headers, excluding the example imports in the
`Discharges` doc comment. The output below counts modules under
`ZInQKernel` and `CMSerreTateSupport`. The exclusion set is the Lean module paths from
`git diff --name-only 2ba691fde 522249258 -- ZInQKernel`, which
includes every old declaration owner, all four premise owners, and
the new conductor module. The roots for `frozenTarget` and `hRC`
are `ZInQKernel.OneProof.Main` and
`ZInQKernel.Contrib.OneProof.SelmerTwoPower`, respectively.

```text
2ba691fde6bfb9e514a429414ba92a6c6893a63f
  ZInQKernel.OneProof.Main (10580 project modules including root)
    changed or retired modules: none
  ZInQKernel.Contrib.OneProof.SelmerTwoPower (380 project modules including root)
    changed or retired modules: none
  ZInQKernel.OneProof.Discharges (1 project modules including root)
    changed or retired modules: none
  ZInQKernel (613 project modules including root)
    changed or retired modules: none
  ZInQKernel.Contrib.CloudB3RC53.Assembly (1311 project modules including root)
    changed or retired modules: none
  ZInQKernel.Contrib.OneProof.RC.Assembly (1323 project modules including root)
    changed or retired modules: none
  ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves (2505 project modules including root)
    changed or retired modules: ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
  ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Leaf (2410 project modules including root)
    changed or retired modules: ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor, ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields, ZInQKernel.Contrib.CloudB3E2Norm.H20HeegnerNorm, ZInQKernel.Contrib.CloudB3E2Norm.H20PresClass, ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch, ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf, ZInQKernel.Contrib.CloudB3E2Norm.H20Transport, ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner, ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate18E2, ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
  Reverse closure of changed modules: 640 importers
  Terminal affected targets: 86
5222492581202af090762d7ac62d6b042de53865
  ZInQKernel.OneProof.Main (10580 project modules including root)
    changed or retired modules: none
  ZInQKernel.Contrib.OneProof.SelmerTwoPower (380 project modules including root)
    changed or retired modules: none
  ZInQKernel.OneProof.Discharges (1 project modules including root)
    changed or retired modules: none
  ZInQKernel (613 project modules including root)
    changed or retired modules: none
  ZInQKernel.Contrib.CloudB3RC53.Assembly (1311 project modules including root)
    changed or retired modules: none
  ZInQKernel.Contrib.OneProof.RC.Assembly (1323 project modules including root)
    changed or retired modules: none
  ZInQKernel.Contrib.OneProof.RC.Wiring.Leaves (2505 project modules including root)
    changed or retired modules: ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner
  ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19Leaf (2409 project modules including root)
    changed or retired modules: ZInQKernel.Contrib.CloudB3E2Norm.H20Anchor, ZInQKernel.Contrib.CloudB3E2Norm.H20DictFields, ZInQKernel.Contrib.CloudB3E2Norm.H20PresClass, ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassMatch, ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf, ZInQKernel.Contrib.CloudB3E2Norm.H20Transport, ZInQKernel.Contrib.OneProof.RC.PrintsArith.Heegner, ZInQKernel.Contrib.OneProof.RC.Wiring.ChainCond, ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19E2
  Reverse closure of changed modules: 640 importers
  Terminal affected targets: 86
```

There is no intersection for either theorem root even on pinned main,
where the old declarations still existed. The import path from the
separate `Wiring.Leaves` candidate to the changed `Heegner` module goes
through `PrintsArith.Bundle`. Its mention of the unweighted witness is
in a comment. The staged common-coordinate package uses the
weighted interface.

**Count lowered: none.** On pinned main, `hRC` is the argument at
`ZInQKernel/OneProof/Main.lean:265`, with its type defined at
`ZInQKernel/Contrib/OneProof/SelmerTwoPower.lean:217`. It is GLUE at
`docs/one-proof/kinds.tsv:23` and `docs/one-proof/OPEN.md:149` and
`docs/one-proof/OPEN.md:462`. The H total and strict breakdown are
at `docs/one-proof/OPEN.md:16` and `docs/one-proof/OPEN.md:18`.
No count or row changes under this retirement.
