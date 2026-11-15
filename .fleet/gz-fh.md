# gz-fh: hL2 = `ZInQ.GZDecomp.FHNonvanishing`, now one printed leaf

**Result.** `FHNonvanishing` (hL2 of `frozenTarget`, rated composite) is proved from a single printed leaf.
The root number of the quadratic twists is proved in Lean. Standard axioms only.
* `ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE : FriedbergHoffsteinB_FE → FHNonvanishing`
  (`ZInQKernel/Contrib/OneProof/FHNonvanishing.lean`, helpers in `FHNonvanishing/{Basic,FE,TwistFE}.lean`).
* `FriedbergHoffsteinB_FE` (LEAF, research): Friedberg–Hoffstein, Ann. of Math. 142 (1995), Thm B, specialized to
  weight-2 newforms of trivial nebentypus and `χ₀ = χ_{D₀}` unramified at `S ⊇ {p ∣ 2N}`. The local conditions
  are written as `D/D₀ ∈ (ℚ_p^×)²` and `ε(½, π⊗χ₀) = 1` as the FE sign `+1` of the completed twisted
  L-function. Rated: printed form up to a stated dictionary, never stronger. Recalled from memory (UNVERIFIED).
* **Proved:** `twistFunctionalEquation`, i.e. `(f ⊗ χ_D) ∣ W_{N D²} = χ_D(−N) ε_N(f) (f ⊗ χ_D)` for `D` odd
  fundamental with `(D, N) = 1`, hence the twisted FE. The proof uses Gauss-sum reindexing over Tau Ceti's
  `CuspForm.twist`, primitivity of `χ_D` and a Γ₀(N) matrix identity. With Dirichlet (Mathlib):
  `D₀ = −q`, `q ≡ −1 mod 8N`, so the sign is `(−1)(−1) = +1`. Reducing `ℤ_p → ℤ/p` and `ℤ_2 → ℤ/8` turns the
  local squares into the Heegner hypothesis.
* Variants kept (they compile and discharge hL2): {`FriedbergHoffsteinB`, `TwistNewformRootNumber`} (two printed
  leaves) and {`FriedbergHoffsteinB_FE`, `TwistFunctionalEquation`}.

**Compiles.** `lake build +ZInQKernel.Contrib.OneProof.FHNonvanishing` succeeds. `#discharges` reports
`DISCHARGES [hL2] by ZInQ.GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE, still assumes: [FriedbergHoffsteinB_FE]`
(`scratch/gz-fh/Discharges-output.txt`). The proposed Main.lean edit (`hL2` → `hFH : FriedbergHoffsteinB_FE`) is
checked in scratch (`gzfh_frozenTarget`), and so is the `FHNonvanishingCd` corollary.

**Cd form.** It is no longer needed for the root number, which is now proved at every level. It would only narrow
the FH statement check to one dihedral family.

**Remains.** Human check of FH Thm B against the print (gz-statements §6 H1 (a)–(f)). For the integrator: the
Main.lean edit and the kinds.tsv/locators.md rows (docs/research/gz-fh.md §4).
