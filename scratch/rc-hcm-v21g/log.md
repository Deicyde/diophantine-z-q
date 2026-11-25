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
