# linyang-printed (fleet report)

**Result.** theta-glue's composite leaf `LinYangThetaCurve` is now a theorem from two leaves stated in printed form:
- `IgusaThetaExpressions` (Igusa 1964/1967): on 𝔥₂, the genuine Siegel Eisenstein series ψ₄, ψ₆ (sum over Γ∞\Sp₄(ℤ))
  and Igusa's 1962 cusp forms χ₁₀, χ₁₂ equal theta-glue's theta expressions;
- `LinYangEx29All` (Lin–Yang 2020, arXiv v1 Ex. 29): for the normalized Hauptmodul j₆ of Γ*\ℍ, wherever j₆ = z ≠ ∞,
  s₃² = z s₂³, s₅ = s₂s₃, s₆ = (z+1)s₂³. `LinYangEx29` is the variant that also asserts j₆ exists.

Eliminating j is linear algebra where j₆ is finite. The j₆ = ∞ orbit is countable, so continuity on ℍ finishes the
proof. igusa-alg's Kronecker engine is not needed for this step.

**Fourier check.** All 76 Fourier coefficients agree exactly (py/fourier.py) between the theta expressions and
Eisenstein series with Igusa's constants. This pins the ψ₆ sign and Igusa's recalled 1962 constants.

**igusaPsi4 / igusaChi10.** I proved in Lean that the Siegel Eisenstein series is modular: ψ_k(MΩ) = det(CΩ+D)^k ψ_k(Ω)
for even k, with no convergence needed. The proof also gives det(CΩ+D) ≠ 0 and Sp₄(ℤ)𝔥₂ ⊆ 𝔥₂. As a result the
kernel's research fields `QMSplit.Theta.IgusaPsi4` and `IgusaChi10`, and `PkgI1.ThetaModularity`, are theorems from
`IgusaThetaExpressions`, for all of Sp₄(ℤ).
- At chain level, `HDec.HSyn.sixContactMin_of_open15P` proves SixContactMin from 31 research fields instead of 32.
  The total goes from 61 fields to 60.
- gap-triage's note is correct: r4 is used only at M4 and M6 along Ω(z). Route 1 as previously stated does not
  remove the two fields; `IgusaThetaExpressions` does.

**Compiled (lake env lean, standard axioms, no sorry):**
- `scratch/linyang-printed/LinYangPrinted.lean` (TailU, 13 s);
- `LinYangPrintedChain.lean` (TailZ19, 31-field bundle, 13 s);
- `LinYangPrintedFull.lean` (igusa-alg's file verbatim + mine, 1 min 45 s, 13.4 GB). It gives
  `thetaPointOfFibre_of_printed[All]` and `thetaRatiosAtQM_of_printed`, i.e. Route 1 from the printed leaves.

Also proved: `qmHauptmodul_of_printed`, and `jTuple_of_sForm` (the s-form gives R3's J-tuple).

**What remains.**
- The Route 1 bundle fold is integration work: replace `thetaRatiosAlgebraic` by `linYangEx29All` and reroute TailK's
  consumer to `thetaPointOfFibre_of_printedAll` (`l.qmHauptmodul` is available there).
- `QMDenZeroCM3` was not derived from the printed leaves. It needs "no common zero of ψ₄, ψ₆, χ₁₀, χ₁₂", so the valence
  and Shimizu fields stay.
- Locators of Igusa and Lin–Yang are UNVERIFIED (no network); Lin–Yang's display was not re-read.
- Oleans came from ~/dzq-check2 (29885092), whose diffs against this base are docstring-only. No chain rebuild was run.

Report: docs/research/linyang-printed.md. Log: scratch/linyang-printed/log.md.
