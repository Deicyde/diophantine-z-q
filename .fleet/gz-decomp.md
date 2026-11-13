# gz-decomp report

**Main result.** The premise `ZInQ.Literature.GrossZagier` is decomposed into three literature
leaves, and all of the glue is proved in Lean. Theorem 1.1 follows from `SixContactMin`,
`TYZThm35ReadingA` and the three leaves:

```lean
theorem ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves :
    ZInQ.SixContactMin → ZInQ.Literature.TYZThm35ReadingA → ZInQ.GZDecomp.HeckeThetaNewform →
      ZInQ.GZDecomp.FHNonvanishing → ZInQ.GZDecomp.GrossZagierHeegner → ZInQ.FrozenTarget
theorem ZInQ.GZDecomp.grossZagierCd_of_leaves' :
    HeckeThetaNewform → FHNonvanishing → GrossZagierHeegner → GrossZagierCd
```

`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every declaration
(`scratch/gz-decomp/out_check_axioms.txt`).

**Scope.** Only `C_d` with `d ≡ 5 (mod 8)` squarefree is used (VERIFIED from every Lean use).
`GZDecomp.GrossZagierCd` suffices:

- `frozenTarget_of_sixContactMin_tyzThm35ReadingA_grossZagierCd : SixContactMin →
  TYZThm35ReadingA → GrossZagierCd → FrozenTarget`, and the same with `PropN.TYZInputs`;
- `grossZagierCd_of_grossZagier : GrossZagier → GrossZagierCd`.

Proposed to the owner, not made: replace `GrossZagier` by `GrossZagierCd`, or by the three leaves.

**Leaves**, stated over Tau Ceti's `Newform`, Mathlib's `qExpansion`, `LSeries` and
`Affine.Point`. All locators are UNVERIFIED (no copies on this host).

- **L1 `HeckeThetaNewform`** (textbook). The Hecke series `heckeCoeff d` of `ψ_d` (`d ≡ 1 (4)`)
  is a weight-2 newform of trivial character (Hecke; Shimura 1971; Miyake Thm 4.8.2).
  - Modularity is a leaf, not glue: the theta series of a Grössencharacter is not in Mathlib or
    Tau Ceti.
- **L2 `FHNonvanishing`** (research). Root number `−1` gives infinitely many odd `D < 0` with the
  Heegner hypothesis and `L(f ⊗ χ_D, 1) ≠ 0` (Friedberg–Hoffstein 1995 Thm B; BFH 1990).
- **L3 `GrossZagierHeegner`** (research). Under `L(f, s)` with a simple zero at 1 and
  `L(f ⊗ χ_D, 1) ≠ 0`, `E(ℚ(√D))` has `y` of infinite order with `σy − y` torsion (GZ 1986;
  Gross 1984).
  - Folded in: the parametrization (Eichler–Shimura, Faltings) and nondegeneracy of `ĥ`. They
    cannot be split off because `X₀(N)` and Heegner points have no Lean definition.

**Glue, all proved:**

- `modular_cd` (Deuring, from HeckeFE/GaussFE);
- `isEntireCont_of_isLContinuation`;
- `signOfSimpleZero` (root number `−1` from a simple zero, via Tau Ceti's functional equation);
- `exists_isEntireCont_twist` (Tau Ceti `CuspForm.twist`);
- `exists_rat_point_of_heegner` (Tau Ceti point descent);
- `exists_quadratic_field`;
- `grossZagierCd_of_leaves`.

**What compiles.** `lake build ZInQKernel.Contrib.GZDecomp.Decomp`, which builds:

- the new files `ZInQKernel/Contrib/GZDecomp/{Scope,Decomp}.lean`;
- 243 newly vendored oct16 Tau Ceti modules (newforms, the functional-equation sign, twists,
  canonical height, Galois descent; list `scratch/gz-decomp/tc-modules.txt`). There are two port
  fixes; the one in `ModularForms/Basic.lean` is byte-identical to `wip/t25-newform`'s.

**What remains.**

- A human must read the leaves' printed theorems. Open question: does FH/BFH allow the level
  `32d²`?
- PARI rechecks were blocked: `~/pyenv` is missing and there is no network.
- Making L1 glue needs Hecke's theta transformation (large).
- Splitting L3 needs `X₀(N)`, `J₀(N)` and CM points (very large).

Deliverables: `docs/research/gz-decomp.md`, `ZInQKernel/Contrib/GZDecomp/*.lean`,
`ZInQKernel/Contrib/TauCeti/**` (243 new), `scratch/gz-decomp/{Check.lean, log.md,
check_chiD.py, out_*.txt, tc-modules.txt}`.
