# Results

| Item | Statement or outcome |
| --- | --- |
| Print | Silverberg–Zarhin, Theorem 3.3, p. 405; AI page read 11-17 |
| `SZRaynaud.SilverbergZarhinThm33` | Absolute closure case, both directions: semistability at the base iff all inertia differences in the rational Tate module are inertia-fixed, conditional on semistability at a finite separable subextension or at the base |
| `tate_tmul_injective` (private) | The map `t ↦ 1 ⊗ t` on the inverse-limit Tate module of an abelian group is injective |
| `SZRaynaud.elliot_of_sz33` | `SilverbergZarhinThm33 → ElliotWildInertiaTrivial`; uses `wildPeriodCoprime_proof` |
| `lake build +ZInQKernel.Contrib.OneProof.SZThm33` | Passed (14,231 jobs); both new theorems and the imported `wildPeriodCoprime_proof` have only `propext`, `Classical.choice`, `Quot.sound` |
| `autofold.py --dry-run` | `TailZ90`, `OpenResearchLeaves64`, `sixContactMin_of_open83`; strict and strictest each 5 LEAF / 28 GLUE on 33 H rows before and after |
| Baseline Lake build | Passed; `OneProof.Main` and `OneProof.Discharges` (16,364 jobs) |
| `#discharges` before fold | Exact discharge shown below; 34 open hypotheses, 13,526 theorems checked |
| Dry run / live fold | `TailZ90.lean` matches generated preview; `Main.lean` switches to the previewed import, bundle and entry point |
| Folded Lake build | Passed; `OneProof.Main`, `OneProof.Discharges`, `Contrib.OneProof.SZThm33` (16,368 jobs) |
| `FoldCheck.lean` | Bundle conversion, `sixContactMin_of_open83` and `frozenTarget`: `propext`, `Classical.choice`, `Quot.sound` |
| Hash guard | 24,772 → 24,810 declarations; 38 added, none removed, only `ZInQ.OneProof.frozenTarget` changed |
| `OpenStatements.lean`; `render_open.py --check` | Passed; 34 hypotheses, all classified; four generated files current |
| GLUE including pole completeness | Strict and strictest both 29 → 29 while pending; 28 if rated LEAF/LEAF |

```text
DISCHARGES [OpenResearchLeaves63.elliotWildInertiaTrivial] by SZRaynaud.elliot_of_sz33
  still assumes: [SZRaynaud.SilverbergZarhinThm33]
  axioms: [propext, Classical.choice, Quot.sound]
```
