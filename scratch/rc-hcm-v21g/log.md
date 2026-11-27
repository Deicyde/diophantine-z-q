# rc-hcm-v21g log

Base 498e4e5713267326a2cd42aef9da8d64dd97fe49 (present locally; no fetch run).

## Part (0)
- New `ZInQKernel/Contrib/OneProof/RC/HCMV21/DeuringRankFour.lean`:
  - `VoightThm4219 : Prop` (printed candidate, Voight Thm 42.1.9 p. 784, UNVERIFIED; `[CharP k q]`, no `IsAlgClosed`, `Module.finrank ℤ A.End = 4`).
  - `SupersingularTorsionRankFour : Prop` (GLUE; Voight Prop. 42.1.7(ii) → rank 4; not provable from the tree: it is Deuring's rank theorem).
  - `deuringSupersingularEndOrder_of_rankFour : VoightThm4219 → SupersingularTorsionRankFour → DeuringSupersingularEndOrder` (proved).
  - `exists_referenceEndOrder_of_rankFour` (proved; rank-four frame from 42.1.9 + 14.1.3 candidate).
- Docstring-only: `HCMV21/GeometricOrders.lean` (module docstring, `DeuringSupersingularEndOrder`), `HCMV21/ReferenceOrder.lean` (`QuaternionRamificationUniqueness` re-cited to Main Thm 14.1.3 p. 218).
- Build `ZInQKernel.Contrib.OneProof.RC.HCMV21.DeuringRankFour`: OK (9220 jobs).

## Part (1)
- `PMAdelic/Comparison.lean`: `JetchevKane ell h N hN hcop X` keeps only `classes` (GLUE docstring; hcop bound explicitly in the header); new `OperatorComparison ell h N hN hcop X J : Prop` with `hecke`, `atkin`, `frobenius` (statements unchanged, `classes` read as `J.classes`; ELLIOT docstring). `idealClasses` stays in `JetchevKane`; `hecke_compare`, `atkin_compare`, `frobenius_compare`, `frobenius_ss` moved to `OperatorComparison` (`include O in`, `J` implicit).
- `#check @PMAdelic.JetchevKane`: `(ell) [Fact] (h) (N) (hN) (hcop) (X) → Type`, the same arity as at 498e4e57 (scratch/rc-hcm-v21g/arity.txt).
- Consumers: an `O` binder added after each `J` (family or single); positional call sites fixed, including `AtkinSign/Family.lean:49` and `AtkinPin/Assembly.lean:81,93`, which the first `PMQuotient.Assembly` build flagged. `PMWire/Fibre.lean`: `adaptComparison` is split into `adaptComparison` plus `adaptOperators`.
- Builds: four sinks OK, nine docstring-edited modules OK, Main OK (19896 jobs), Discharges OK (scratch/rc-hcm-v21g/builds.txt).

## Part (2)
Files, all in ZInQKernel/Contrib/OneProof/RC/HCMV21/. Each was built with lake build, one at a time, LEAN_NUM_THREADS=4; all OK.
- LevelOrderClasses.lean: classSetEquivOfReference (+ _self, leftRing_classSetEquivOfReference), exists_levelReferenceCoordinates (no hD).
- LeftIdealMirror.lean: two_re_int_of_isIntegral, order_star_mem, LeftIdeal, mirror/unmirror, leftClassSetEquiv.
- PrimeToRepresentative.lean: exists_global_approx, LeftIdeal.exists_local_generator (Nakayama over ℤ_q), LeftIdeal.exists_integral_primeTo. Also ℤ_p scalar-tower instances on Bp.
- EnhancedObjects.lean: IsSupersingular (rank form), SupersingularEnhanced, EnhancedIso, enhancedSetoid, EnhancedClasses, exists_generator, exists_referenceFrame.
- VoightCandidates.lean: postcomp, homPull, IsEtaleIsogeny, HomPlacement; candidates VoightThm4232Invertible / Etale / EssSurj, VoightCor4237 (EssSurj and Cor require integral ideals containing an integer prime to q), SeparableIsogenyExists (GLUE).
- HomPlacementBasic.lean: exists_mul_right, exists_unit, translate, transport, levelLattice, levelIdeal, localLattice_levelLattice_eq, levelIdeal_locallyPrincipal_away.
- LevelIdealTate.lean: homBasis, tateToLocal (+ _tateHom, _comp), span_tateHom_eq_top, levelHom_iff_closure, span_levelHom_cyclic.
- LevelIdealPrincipal.lean: levelIdeal_locallyPrincipal_tate.
- LevelDeuringMap.lean: placedLevelIdeal_locallyPrincipal, placedLevelClass_eq, placedLevelClass_iso, levelDeuringClass, levelDeuringClass_reference.
- EndPlacement.lean: endRightHom, endRight_mem_levelRight, endRight_injective.
- LevelOrderLemma.lean: exists_nsmul_of_forall_primary, mem_of_primary_pow_mem, exists_chainIso, tateToLocal_injective, mem_levelHom_of_comp, exists_endRight_eq_level, levelEndEquivRight.
- LevelDeuringOrder.lean: mem_rightRing_iff_mem_mirror_leftRing, conjSubringEquiv, levelDeuringClass_order, levelDeuringClass_reference_order.
- LevelDeuringInjective.lean: orderSpan_levelLattice, nonempty_enhancedIso_of_translate, levelDeuringClass_injective.

Findings:
- ι and γ are reserved tokens under this file's opens; Lean names use emb / gam.
- Builds of the last modules take 10–16 min of wall time with ~10 s of CPU, i.e. waiting on the host; elaboration itself takes about 5 s (profiler).
- Scoped stop after injectivity: surjectivity and the Equiv remain.
