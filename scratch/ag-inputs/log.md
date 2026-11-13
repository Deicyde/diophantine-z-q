# ag-inputs results log

Task: adversarial review of pi0-x6's `r1pi0Props_of_X6Props` (Galois-component argument for
`π₀(X₆) = 1`), then prove as much of `AGInputs` (over0, overInf, descend) as Mathlib v4.35 allows
and state the rest as leaves.

## Lean

- L1 (VERIFIED, compiled 01:30 PST, `lake env lean scratch/ag-inputs/T1.lean`, no errors, no
  warnings; Mathlib only): `descend_of_leaf : ConnectedGeomConnected → IsProper X.hom →
  ConnectedSpace (X ×_ℚ Spec ℚ̄) → GeometricallyConnected X.hom`.
- L2 (VERIFIED, compiled 01:40 PST, `lake env lean scratch/ag-inputs/AGInputs.lean`, exit 0, no
  errors, no warnings; 15 `#print axioms` lines all `[propext, Classical.choice, Quot.sound]`,
  output in `compile_out.txt`; no `sorry`, no `axiom`). `AGInputs.lean` = pi0-x6's `Pi0X6.lean`
  (namespace renamed `AGIn`) plus §8-§9:
  - `ConnectedGeomConnected` (leaf AG-GC), `spec_rat_ext`, `descend_of_leaf` (proved);
  - `CurveComponentDichotomy` (leaf AG-CD), `meets_fibre_of_finite` (proved);
  - `qmIsoOfConj` (inner twists are isomorphic, proved), `AutModInnFinite` (leaf AutO),
    `twistClasses_finite`, `fibres_finite` (finite `π₆`-fibres from `R2X6Props` + AutO, proved);
  - `agInputs_of_leaves : ConnectedGeomConnected → CurveComponentDichotomy → AutModInnFinite →
    IsProper → SmoothOfRelativeDimension 1 → R2X6Props → AGInputs π₆` (proved; all three fields);
  - `r1pi0Props_of_leaves : X6Props → R2X6Props → R5ptProps → R5fpCount → R2X6CMExact →
    ConnectedGeomConnected → CurveComponentDichotomy → AutModInnFinite →
    GeometricallyConnected X.hom` (proved).

## Findings (review of pi0-x6 §2)

- F1 (VERIFIED, compiled deduction; read) The Galois-component deduction is correct: the three
  cases of `hcount` on `x₁, x₂, σx₁` close (`subsingleton_of_galois` recompiled).
- F2 (VERIFIED as an argument; refs UNVERIFIED) Residue fields `ℚ(i)` over 0 and `ℚ(√−3)` over ∞
  also follow from Shimura reciprocity `k·ℚ(P) = H_R = k` (h = 1) and `X^D(ℝ) = ∅`, independently
  of the exact form of R5pt.
- F3 (VERIFIED, read) pi0-x6's (d) is not pure AG: `over0`/`overInf` need finite `π₆`-fibres,
  i.e. `Aut(𝒪)/Inn(𝒪^×)` finite (Skolem–Noether + Atkin–Lehner group finite). Now leaf
  `AutModInnFinite`.
- F4 (VERIFIED, read) (c) `R2X6CMExact` is not a bundle clause; derivable from `R2X6PropsIff` +
  QM dichotomy + maximality of ℤ[i], ℤ[ζ₃] (c2, not in Lean) or adopted (c1).
- F5 (VERIFIED as an argument) pi0-x6 F1 (the rv-blueprints parity sketch is incomplete) confirmed:
  two degree-2 components would each be branched over 0, ∞, −16/27, and RH allows B = 4, g = 1.

- L3 (VERIFIED, compiled 02:00 PST, `lake env lean scratch/ag-inputs/T2.lean`, no errors; one
  deprecation warning `dif_pos`): `AGInO.extAut : (O ≃+* O) → (B ≃ₐ[ℚ] B)` with
  `extAut_coe : extAut α a = α a` (the ℚ-linear extension of a ring automorphism of 𝒪, via
  denominators `nOf`), `AtkinLehnerFinite` (leaf AL), `conjAut`, `autSet`,
  `autModInnFinite_of : GlueDescent.LeafSkolemNoether → AtkinLehnerFinite → AutModInnFinite`.
  `GlueDescent.LeafSkolemNoether` (ZInQKernel/HDecomp/Descent/B1Quat.lean) is verbatim the
  statement `TSkolemKW.LeafSkolemNoether` proved by t-skolem-kw (VERIFIED, read both).
- L4 (VERIFIED, compiled 02:02 PST, `lake env lean scratch/ag-inputs/AGInputs.lean`, exit 0, no
  errors, one deprecation warning; 18 `#print axioms` lines all `[propext, Classical.choice,
  Quot.sound]`, `compile_out.txt`): T2 merged as §10 (namespace `AGInO`), plus
  `AGInO.r1pi0Props_of_leaves' : X6Props → R2X6Props → R5ptProps → R5fpCount → R2X6CMExact →
  ConnectedGeomConnected → CurveComponentDichotomy → LeafSkolemNoether → AtkinLehnerFinite →
  GeometricallyConnected X.hom`.
