# Focused finite controls for the four local-interface modules

Date: 2026-11-10. Author: internal Codex agent
`/root/normalization_adversarial_checks`.
This design is written before the first execution of `check_controls.py`.

The runner uses standard-library exact integer and rational arithmetic. It
checks the selected module bytes against `ORIGIN.json`, then exercises the
following algebraic models. It does not parse or execute Lean proofs; native
build and statement/axiom checking are separate evidence.

| Interface | Positive model | Required adverse control |
| --- | --- | --- |
| Boundary/cup representative correction | Alexander–Whitney cups on an oriented 3-by-3 simplicial torus, with nonzero differentials and a nonzero H1 cup pairing. Closed local directions differ by an exact cup correction, killed by the chain trace. | Wrong correction sign; a nonclosed local direction; replacing the trace by evaluation on one simplex. |
| Cone comparison | The actual degreewise fibre formula `j(g,u,q)=(g,a*u,q+h*u)` with its inclusion homotopy relation, over finite rings. | Changing only the sign of the correction fails the chain-map equation. These degreewise inputs are not claimed to be whole Selmer complexes. |
| Homotopy inverse and localization | Two-term finite complexes with `k=id+dH+Hd`; the top cohomology class is unchanged, also after a compatible scalar localization map. | An actual abstract isomorphism of a zero-differential complex may change a localized class if the common-projection premise is absent. Nilpotent t in `(Z/4)[t]/t^2` has no inverse. |
| Conjugate coefficients and H1 evaluation | Pull back a crossed cocycle on C8 over Z/32 along inversion, retaining the pulled-back coefficient action. | The same pullback fails the original action's cocycle equation. Evaluation at a nontrivially acting element does not kill all coboundaries and therefore need not descend to H1. |
| Functional normalization | A small exact raw-cup calculation uses one coefficient J, one common transport unit, and one common trace factor on both branches. | Inserting J twice or omitting the tame sign changes the expected evaluation. Rescaling only one closed functional by 2 preserves closedness but changes its valuation. |

The torus, cone and sign calculations are selected/adapted from existing
research scripts at `33483f751e6dcd3f91fb303969838aca33ad0458`.
`CONTROLS_PROVENANCE.json` records original paths, blob identities, hashes and
the changes. The full determinant/cofactor and universal-descent parts of the
older integration script are deliberately not included: they are outside this
four-module PR. The C8 coefficient-type control is new bounded algebra.

The module identity check covers the four submitted files only. The runner
has no import or runtime dependency on the frozen 39-target package, another
Lean module, the research worktree, or the canonical manuscript. Every positive
case and adverse witness is a diagnostic model, not an actual Galois/Selmer
instance or an arithmetic existence proof. A scope boundary is not an observed
defect in the manuscript.

Run from the candidate repository root:

```sh
python -B research/local-boundary-interfaces/check_controls.py
```

The script refuses optimized Python before any assertions run. The retained
command receipt records interpreter, source hashes, exit code, complete stdout
and stderr; the separate optimized-mode receipt records the expected refusal.
The checker and interpretation require a non-author review before acceptance.
