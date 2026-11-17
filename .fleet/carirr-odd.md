# carirr-odd: fleet summary

**Result.** Both unproved Lean steps of Carayol's leaf (queue10 verdict, carIrr) are now proved. The leaf is
restated clause by clause as Darmon–Diamond–Taylor 1997 Thm 3.1 (weight 2). New file
`ZInQKernel/Contrib/OneProof/CarayolDDTOdd.lean`. It builds with no warnings, and every declaration uses only the
standard axioms.

* **`χ_ℓ(c) = −1`, proved.** Complex conjugation in `Gal(ℚ̄/ℚ)` is built from an embedding `ℚ̄ → ℂ`
  (`exists_complexConj`). Mathlib's `ℓ`-adic cyclotomic character is `−1` on it (`cycL_eq_neg_one`), and the
  mod-`N` character is `−1` (`cycN_eq_neg_one`). In weight 2 the nebentypus is even (`chi_neg_one_eq_one`, from
  Tau Ceti's parity lemma). So `det ρ = ψ·χ_ℓ` gives oddness (`odd_of_det`).
* **Irreducibility.** The leaf now says "absolutely irreducible", meaning irreducible over
  `AlgebraicClosure K_{f,λ}`, which transcribes 3.1(c). Irreducibility over `K_{f,λ}` is proved from it
  (`irreducible_of_absIrreducible`). The Burnside step is r17-rebase's `adjoin_eq_top_of_irreducible_odd`,
  used as glue.
* **New leaf `CarayolDDT.CarayolDDT31`.** Its clauses: continuous; absolutely irreducible;
  `det ρ(σ) = ψ(σ mod N)·ι(χ_ℓ(σ))`, for some continuous `ι : ℤ_ℓ → K_λ` (unique, proved) and at every `σ` with
  `ψ(σ mod N) ∈ K_f`; unramified with arithmetic-Frobenius trace `a_p`; the conductor in DDT's integral form
  (carayol-herbrand's clause, untouched). Rated a printed form, never stronger (reasons in the report §2).
  Variant `CarayolDDT31Cond` states the conductor as `condExp`; the two are proved equivalent.
* **`#discharges` on main** (`scratch/carirr-odd/discharges.txt`):
  `DISCHARGES [OpenResearchLeaves38.carayolThmA] by CarayolDDT.carayolThmA_of_DDT31`, still assuming
  `[CarayolDDT.CarayolDDT31]`, standard axioms. The chain is DDT31 → carayol-herbrand's `CarayolThmAIrrDDT` →
  `CarayolThmAIrr` → `CarayolThmA`.
* **Fold dry run** (`scratch/carirr-odd/autofold.json`, leaf published, flagged unread): strict and strictest
  counts both go from 16/18 to 17/17 on 34, so **GLUE −1**. The generated module compiles, and
  `sixContactMin_of_open56` uses only the standard axioms.

**Remaining.**

* A statement check against the DDT 3.1 print: "absolutely irreducible", `det = ψ ε^{k−1}`, which Frobenius
  convention is used, and the conductor (carayol-herbrand's item).
* The fold itself. Merge this branch, which already contains carayol-herbrand's `CarayolHerbrand.lean`, then run
  autofold.
* A `locators.md` row (text in the report §4).
* The verdict file `queue10-verdict.md` was not in the tree; I worked from the brief's summary of it.

Report: `docs/research/carirr-odd.md`.
