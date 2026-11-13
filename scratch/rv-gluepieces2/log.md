# rv-gluepieces2 results log

Target: the 27 fields of `HSyn.GluePieces2` in scratch/g0-assemble/G0Assemble.lean (L41938-41998).

- VERIFIED (cmp/diff): scratch/g0-assemble/Leaves.lean differs from scratch/h-decomposition/Leaves.lean
  (current, post pin-apply) exactly by pin-apply's patch: `R1famProps`, `R1univProps`, `QMFamily`,
  `IsFibreOf` and namespace `Pin` are absent from G0Assemble.lean; its `R1fpProps` is the
  pre-repair 4-clause version (no fam/univ clauses).

## QM-PIN fields (4 fibreComTrivial, 10 fibreQMPeriod, 13 kernelFieldExists, 27 modelG3G6)

- VERIFIED (read): all four quantify over every `(Y, Φ, π)` with `R1fpProps Y Φ ∧ R2fpProps Y Φ π`
  (directly, or through `FibreCtx`, L39149). In G0Assemble.lean `R1fpProps` (L15152) is the
  pre-repair 4-clause list (proper, smooth rel. dim 1, a ℚ̄-point, naturality).
- VERIFIED (read, already proved in the file): parts/40_fibresimple.lean §5
  `r1fpProps_twistBy`, `r2fpProps_twistBy`, `fibreComTrivial_twisted`: under the 4-clause list,
  `FibreComTrivial` applied to `Φ ∘ σ` asserts NoCM at every rational value whose π-fibre a
  natural point-relabeling σ can exchange with the fibre over J(u). So the field is equivalent to
  an open arithmetic statement (no ℚ-isomorphism of finite étale fibres between a non-contact
  rational fibre and a rational CM fibre). Same mechanism for 10, 13 (via NoCM in End⁰ = B) and
  27 (G6 half).
- 27 `ModelG3G6`, G3 half: not pin-dependent. `IsQMModel` makes `A = (PK.A)_L` with `PK : QML3 K`;
  `Level3` (L14331ff) = `𝒪`-linear `η : 𝒪 → A(K)` with kernel `3𝒪`, i.e. full rational 3-torsion
  on a surface. Raynaud (semistable at p ≠ 3) + potentially good reduction of QM surfaces ⇒ good
  reduction at p ≠ 3; `G3Out` (L37281) excludes p = ℓ. TRUE (STANDARD).
- 27, G6 half: noncommutativity from `PK.q.iota` (injective) after base change: TRUE. `EndDivision`
  of `A_{L'}` needs NoCM of `P` (CM ⇒ `A_ℚ̄ ≅ E²`): pin-dependent.

## Pinned rebase check (Lean)

- `build_prefix.sh`: scratch/h-decomposition/Leaves.lean (post pin-apply, verbatim) → olean/LPrefix.olean:
  exit 0 in 603 s, 0 errors, 190 `#print axioms` lines (VERIFIED, olean/prefix_out.txt).
- Tail = `import LPrefix` + g0-assemble's imports_extra + g0-assemble's parts verbatim except
  parts/40_fibresimple.lean (§5 demo lemmas `r1fpProps_twistBy`, `fibreComTrivial_twisted` take
  `R1famProps ∧ R1univProps` for the twisted Φ as an extra hypothesis; they are not used
  downstream) + checks/c1_g10.lean (g10-odd L102-239 verbatim + `g10Glue_of_conjTwist_new`).
