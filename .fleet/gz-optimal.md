# gz-optimal (fleet summary)

**Result:**
- The Gross–Zagier leaf is restated for the strong Weil (optimal) parametrization only, as
  `ZInQ.GZOptimal.GrossZagierModuliOptCd`. That statement is printed under either reading of Gross–Zagier Ch. V,
  and it is proved weaker than gz-moduli's leaf.
- The consumer `GZHL3.GrossZagierFormulaCd` is proved from it in Lean. Each of two routes adds a statement the
  kernel lacks.
- The fold is not a clean −1 today. Route A becomes −1 once one period computation (`CdOptimal`) is proved.

Optimal means: the lift of φ is `c φ_f` and `L = c Λ_f`, i.e. `φ_*` is onto `H₁`, i.e. `J₀(N) → E` has connected
kernel. That is the strong Weil definition; "minimal degree" cannot be stated. The leaf takes `y = n · y_K` with
`n ≠ 0`, because heegner-32 makes the Heegner point rational only for even `c`.

**The two routes:**
- **Route A** (`grossZagierFormulaCd_of_selfOptimal`): the leaf plus `CdOptimal` (GLUE: `L(C_d) = c₀ Λ_f`). Every
  admissible φ is then `[n] ∘ φ_opt`.
  - Numerically `Λ_f = L(C_d)` for all 18 tested values of d ≡ 5 (mod 8) squarefree, 5 ≤ d ≤ 165 (GP period
    computation). PARI `ellweilcurve` confirms d = 5 and 13.
- **Route B** (`grossZagierFormulaCd_of_transfer`): the leaf plus `StrongWeilOptimalCd` and
  `AnalyticIsogenyRational` (both textbook, composite: +1 GLUE). Here `φ = ψ ∘ φ'`. The formula transfers along
  `ψ̂ : C_d → E'` by a torsion argument, so no height comparison between curves is needed.

**y_K:** Gross–Zagier's `Tr_{H/K} φ(x)` equals the sum over a complete set of Heegner points with fixed 𝔫, which is
gz-moduli's form. No fix is needed.

**Compiles** (standard axioms only, VERIFIED):
- `ZInQKernel/Contrib/OneProof/GrossZagierOptimal.lean` and `.../GrossZagierOptimal/NonVacuous.lean`
  (`lake build`);
- the checks in `scratch/gz-optimal/`: Target (rfl), Check, Discharges, MainEdit.
- Glue proved along the way: additivity of `weierPt` for `y² = x³ + a₄x + a₆`, the torsion criterion, lattice index
  lemmas.
- `MainEdit.lean` (with heegner-32 and gz-conj merged) proves `FrozenTarget` with `hL3` replaced by
  `{GrossZagierModuliOptCd, CdOptimal}`, or by the three route-B statements.
- `#discharges` shows no GZOptimal line, because `hL3` is a top-level argument (as for gz-moduli).
- Autofold specs: `scratch/gz-optimal/autofold.json` (route A) and `autofold-routeB.json`, both for the field
  `grossZagierFormulaCd`.

**What remains:**
- a statement check of Gross–Zagier V §2 (p. 312) on the hypothesis on φ. If it covers every parametrization,
  gz-moduli's leaf gives −1 directly;
- a Lean proof (or a published source) of `CdOptimal`;
- the explicit constant.

Report: `docs/research/gz-optimal.md`.
