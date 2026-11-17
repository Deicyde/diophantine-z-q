# cd-optimal: fleet summary

**Verdict.** `ZInQ.GZOptimal.CdOptimal` (`L(C_d) = c₀ Λ_f`, `c₀ ∈ ℚ`) is **reduced in Lean**, not proved outright.
It now rests on two statements:
- `EtaW32Character`: a **printed leaf**, one instance of the Newman / Gordon–Hughes eta-quotient transformation law.
  It says `v = η(8τ)η(32τ)²/η(16τ)³` has character `(2/d)` on `Γ₀(32)`.
- `CdTwistedPeriodOdd`: **glue, not printed**. Some period of `f_d` is not in `(1+i)L`. This is strictly smaller than
  `CdOptimal`.

Theorems: `ZInQ.CdOpt.cdOptimal_of` and `grossZagierFormulaCd_of_cdLeaves`. So `hL3` becomes
`GrossZagierModuliOptCd + EtaW32Character + CdTwistedPeriodOdd`. **The target "hL3 ← GrossZagierModuliOptCd alone"
was not reached.** The glue count is unchanged (one glue replaced by a smaller one), and there is one new printed
leaf.

**What compiles** (`ZInQKernel/Contrib/OneProof/CdOptimal.lean` + `CdOptimal/{Unif,Structure,Level32}.lean`; standard
axioms only, checked by `scratch/cd-optimal/Check.lean`):
- unconditional uniqueness of a period lattice given `g₂, g₃` (`lattice_eq_of_g₂_g₃`), via gz-weil's argument in a
  general form;
- `Λ_f` and every lattice of `C_d` are `ℤ[i]`-modules stable under conjugation;
- the classification `lattice_eq_of_periods`: `Λ_f ⊆ L` plus a period outside `(1+i)L` gives `L = c₀Λ_f`;
- from the eta leaf, **`Λ_f ⊆ L` for every admissible `d`** (`periodLattice_le_of_etaW32`), sharpening gz-weil's
  `2Λ_f ⊆ L`. It uses a new model `x₁ = (x − y/w)/2` of `C₁ = 32a2` on x0-32's eta model, invariant under
  `Γ₀(32) ∩ {(2/d) = 1}`.

Checks:
- `MainEdit.lean` (`frozenTarget_cdoptimal`) has standard axioms.
- `#discharges` gives 61 open, the same 9 discharges, no `CdOpt` line (`hL3` is top-level).
- `Target.lean`: the verbatim copy of `CdOptimal` is `rfl` against the original.
- `autofold.json` (field `cdOptimal`) and `autofold-formula.json` (field `grossZagierFormulaCd`).

**Findings** (numerical, PARI):
- `Λ_{f₁} = ((1+i)/2)L₁` at level 32;
- periods mod `L₁` form the congruence character `χ₈(d)`;
- periods mod `(1+i)L₁` are **non-congruence**. This is why `CdTwistedPeriodOdd` cannot come from eta or cusp
  computations;
- a mod-2 reduction to level 32 confirms `CdTwistedPeriodOdd` for all 32 squarefree `d ≡ 5 (mod 8)` with
  `d ≤ 301`.

**What remains:**
- prove `CdTwistedPeriodOdd`. One possible route is Ihara / the congruence subgroup property; it is speculative
  (report §4);
- optionally formalize the odd-power eta multiplier, which would remove the printed leaf.

Report: `docs/research/cd-optimal.md`.
