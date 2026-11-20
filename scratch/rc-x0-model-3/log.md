- Base: `ecddf799e810fca2ad339aaa984ac80c8203700a`.
- Scope error (inherited): tex 8468–8474, Jetchev–Kane citation omits
  level one. Recorded in the report and handoff.
- Exact normalized-branch proof found at `398868586`, an ancestor of
  the proved fixed-scale parametrization.
- Required user systemd scope works with sandbox escalation.
- Model port (namespace and imports only): `0dd0d3af4`.
- `exists_stabilizer_germ_match`: exact handoff statement; no extra
  branch input. `complexPoint_eq_iff`: both directions for every nonzero
  level. `model`: same rational normalization, field and expansions.
- `lake --old build`, user scope at 60 GB, one Lean compiler at a time;
  audited dependency reuse from matching source trees and pinned manifests.
- Build passed for `Unramified`, `AffineEval`, `Overlap`; 28 axiom
  checks, all within the allowed set.
- `Model`: build passed; 3 axiom checks.
- `projectiveValue_eq_of_complexPoint`: injectivity identifies the
  fixed-scale rational value with the selected elliptic point.
- `datumReduction_projectiveValue`: the rational value of the
  Artin-conjugate source reduces to the Stage Kummer conjugate.
- `hpi_iff_specialize_projectiveValue`: exact pointwise PM rewrite.
- `specialize_of_integral_extension`: generic equality over a
  separated target gives equality on the residue section.
- `Specialize`: build passed; 4 axiom checks.
- Final build exit: 0. All 35 checks report only `propext`,
  `Classical.choice`, `Quot.sound`.
- O.7 gap: identify the PM special-fibre quotient on the actual
  reduced source points with the specialization of the fixed
  rational parametrization (ELLIOT, tex 8476–8479).
