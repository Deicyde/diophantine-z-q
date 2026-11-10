# redei-plan report: Rédei's formula in Lean (plan and probe)

All deliverables are committed:
- the plan, `docs/research/redei-plan.md`;
- the probe, `scratch/redei-plan/Probe.lean`, which compiles with `lake env lean` after
  `lake build ZInQKernel.RouteK.Rank5b.Sec3.TYZ`;
- the log, `scratch/redei-plan/log.md`.

No file under `ZInQKernel/`, `blueprint/` or other notes was edited.

## Summary

- **TYZ's statement was checked against the arXiv source** (`Period7.tex`, lines 361–366, 998). It
  reads `g(d) := #(2Cl(ℚ(√−d)))`, the order of the subgroup of squares of the ideal class group. The
  Lean target uses exactly this:
  `gCl n = Nat.card (powMonoidHom 2 : ClassGroup (𝓞 (QNeg n)) →* _).range`, with
  `QNeg n = QuadraticAlgebra ℚ (−n) 0`.
- **Target theorem:** `gCl_eq_gBit : Odd d → Squarefree d → B.Nonempty →
  ((gCl (dProd B) : ℕ) : ZMod 2) = gBit d B`.
- **Hypothesis:** `CertifiedRankTYZCl` is `CertifiedRankTYZ` with `T5bCl` (TYZ's `g`) in place of
  `T5b`. The probe proves `T5bCl_eq_T5b` and `certifiedRankTYZ_iff : CertifiedRankTYZCl ↔
  CertifiedRankTYZ` from `gCl_eq_gBit`. The trust statement would then cite only TYZ and
  Gross–Zagier–Kolyvagin.
- **Mathlib v4.35.0 has every ingredient except genus theory itself:**
  - quadratic fields for variable `d` (`QuadraticAlgebra`, with `Field`, `NumberField`, `IsGalois` and
    `Fintype (ClassGroup (𝓞 _))` all inferred);
  - the Galois fundamental identity on primes;
  - `Ideal.absNorm` and `relNorm`;
  - Jacobi reciprocity;
  - **Dirichlet's theorem** (`Nat.forall_exists_prime_gt_and_zmodEq`).

  Absent: the ring of integers of quadratic fields, the splitting law, `𝔞σ𝔞 = (N𝔞)`, Hilbert symbols,
  Hasse–Minkowski, Legendre's ternary theorem, binary forms.
- **Chosen route (c):** genus characters `χ_q([𝔞]) = (N𝔞/q)` plus Dirichlet plus ambiguous classes
  plus counting. The count `[Cl : 2Cl] = #Cl[2] ≤ 2^{t−1} ≤ #im χ` gives the principal genus theorem
  `2Cl = ker χ`. Then `Cl[2] ∩ 2Cl = ψ(ker of the Rédei matrix)`, and 𝔽₂ linear algebra gives
  `redeiG`.
  - It avoids Hilbert symbols, Hasse–Minkowski/Legendre, the explicit integral basis, and the kernel
    computation of tyz-5b (G1). Residue-field arguments replace them: `σ` acts trivially on `𝓞/𝔭`
    for ramified `𝔭`.
  - Route (a) (tyz-5b §2.2 with Legendre's theorem) is estimated at about 3,600 lines.
  - Route (b) (binary forms) is over 5,000 lines and was rejected.
- **The probe proves** `card_gal`, `isIntegral_omega`, `algNorm_eq`, `norm_nonneg`,
  `fundamental_identity` (`#primesOver · e · f = 2` on `𝓞 (QNeg n)`), `exists_conj_eq` and
  `odd_card_range_sq_iff`. It typechecks with `sorry` all 16 intermediate statements of the plan and
  the target.

## Size estimate

The chosen route takes 8 modules and about 2,650 lines; budget 3,500. That is three or four fleet
tasks, comparable to cr5b-sec3's 4,150 lines.

| Module | Lines |
| --- | --- |
| Field | 250 |
| Primes | 500 |
| Ambiguous | 400 |
| Genus | 400 |
| Dirichlet | 350 |
| FourRank | 250 |
| Kernel | 250 |
| Bridge | 250 |

- **First leaf:** `Primes.prime_trichotomy` and `dvd_of_ramified`.
- **Safe parallel leaf:** `Kernel.kernel_trivial_iff_redeiG`, which is pure 𝔽₂ algebra on the existing
  `Sec3` lemmas.
- **Mathematical risk:** low; no gap was found. The edge cases `n = 3`, `t = 1` and both residues mod 4
  were checked on paper.
- **Engineering risks:** ideal bookkeeping with `σ • I`, the choice-based definition of `χ`, Jacobi
  signs, and reindexing `(dProd B).primeFactors` to `B`.

## Recommendation

**Not worth doing now; it is a good background project later.** Only one classical input leaves the
trust statement: Rédei 1934, already cross-checked against PARI for all squarefree `n < 20000`. The
deep inputs, TYZ and Gross–Zagier–Kolyvagin, stay. The gain is precision of the citation, not a
change in the kind of trust. SixContactMin and the UNCHECKED journal statement of TYZ have larger
payoff.

**Cheap step worth taking now** (about 100 lines, needs a task allowed to edit `ZInQKernel/`):
- move `QNeg`, `gCl`, `T5bCl`, `CertifiedRankTYZCl` and a Prop `RedeiFormula` (the statement of
  `gCl_eq_gBit`) into `ZInQKernel/RouteK/Rank5b/Sec3/`;
- prove `RedeiFormula → (CertifiedRankTYZCl ↔ CertifiedRankTYZ)`; the probe's proof works as is.

Rédei then enters the trust statement as an exact Lean statement instead of prose, and a later
formalization discharges it without touching anything else.

## Resource notes

- One Lean process at a time throughout; the load stayed below 16.
- `lake build ZInQKernel.RouteK.Rank5b.Sec3.TYZ` took 3.5 min, because the `Rank5b` tree was not built
  in this worktree.
- Each probe compile takes about 6 s.
