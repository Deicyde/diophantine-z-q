# Initial native port attempts

All checks use stock Lean 4.35.0 on the dedicated private checkout. No source
proof using an error placeholder is accepted. Historical logs below are failed
or cancelled attempts, **not** successful compilation or axiom evidence.

## Attempt 00 — original factoring scaffold

The rational-residue first part emitted invalid-field errors after private root
helpers were promoted into `P2MW` namespaces. The first ordinary scoped
`Polynomial` open also selected a local namesake, breaking `K[X]` notation.
The failing chain was cancelled; the independent RR chain was cancelled before
its terminal verdict to apply the same scaffold correction. Their partial raw
logs are retained in `attempt00/`.

Correction: transparent private root abbreviations restore original field lookup
in each factoring module, without assuming any mathematical statement. Ordinary
scoped opens now explicitly name `_root_` namespaces.

## Subsequent localized fixes

* Select `TensorProduct.induction_on` explicitly rather than relying on the
  version-dependent default induction eliminator.
* Pin pole-correction definition/equality expressions before unfolding or casts;
  the original equalities are proved, not assumed.
* Include attribute-prefixed private data definitions in the promotion/bridge
  map, preserving their original attributes and bodies.

The first corrected RR parts 1–3 and rational-residue parts 1–2 compiled. The
complete five-part conditional RR edge and its facade then compiled. Further
edges and complete axiom reports remain tracked by the final verification report;
this historical note does not claim a complete H102 discharge.
