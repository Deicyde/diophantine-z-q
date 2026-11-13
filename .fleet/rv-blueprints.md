# rv-blueprints (adversarial review of bp-faltings, bp-modcurves, bp-qmmoduli)

Report: `docs/research/rv-blueprints.md` (verdicts first). Scratch and log: `scratch/rv-blueprints/`.

**Verdicts.** All three blueprints are **SOUND AFTER REPAIRS**. Exact replacement texts are in
the report: §1.5, §2.4 and §3.3.
- **bp-faltings.** The central claim is right: the `EReal` infimum over smooth group models is
  the stable Faltings height in Faltings' normalization, and `h_D = h_F + (g/2) log π`. Repairs:
  - (F1) Additivity in the direction that step E4 uses, `h(A)+h(Z) ≤ h(A×Z)`, is not
    definitional for the infimum. It needs Néron models (M5) and H5. h-decomposition's remark
    under R20, "additivity follows from the definition", is wrong for additivity.
  - (F2) Each of R18-R22 is a consequence only together with H5. H5 must be proved or made an
    explicit leaf.
  - (F3) AT1 is a plumbing test. Add AT4 (`h(E₁×E₂)`, the first test at `g = 2`) and AT5 (base
    change).
  - (F4) R19 is the one normalization-sensitive leaf. R18 and R20-R22 hold in either
    normalization (proved in Lean).
- **bp-modcurves.** The interface `ρ_{f,ℓ} ⊂ V_ℓ(J₁(N))`, `g ≤ N²` and Belyi degree `≤ N²` is
  faithful. The Albanese predicate with an existence leaf is neither vacuous nor a disguised
  conclusion. Repair (M1): drop leaf MC9, which is stated over an undefined "Shimura canonical
  model", and state R16 for the `K_N` model. The existential R16 transfers along `J ≅ J'`
  (proved in Lean).
- **bp-qmmoduli.** "Field points suffice" holds for the h-trust route, not for N5 as printed,
  which uses Buzzard's integral model and its universal abelian scheme at L444-530 (Q1). The
  field-point package is too weak in four places:
  - (Q2) A10 needs `k ⊆ ℚ(x)`, which the degree-form R5fp lacks. Counterexample to sufficiency:
    `𝒪_{ℚ(√−19)}`. Repaired as `R5fpStrong`, compiled.
  - (Q3) F1 needs R1an in family form: every `τ` occurs and `τ ↦ π(P_τ)` is holomorphic.
  - (Q4) Lemma NV step 4 needs `π₀(X₆) = 1`, as a leaf or as glue.
  - (Q5) R2fp's CM clauses must be biconditionals (Lemma NV step 2).

  The §2.2 polarization sign claim is numerically VERIFIED.

**What compiles.**
- All 11 blueprint Lean files compile with no errors and no `sorry`. An appended
  `collectAxioms` audit over all 629 declarations finds only `propext`, `Classical.choice`,
  `Quot.sound`.
- New files, all with standard axioms only:
  - `Normalizations.lean`: `bost_F_of_D`, `log_pi_lt_three`, `faltings_kappa_le`.
  - `R5Repair.lean`: `R5fpStrong` and `R5fp_of_R5fpStrong`.
  - `R16Transfer.lean`: `exists_quotient_transfer`.
- Computations: `at3_check.py` (`faltingsHeightEC` at `j = 0` is −1.3211174284, matching the
  η-product and Deligne's −0.74875 − ½ log π) and `sheet_check.py`.

**What remains.**
- No primary source was read (no network), so the normalizations of Gaudron–Rémond and
  Javanpeykar rest on locators.md.
- The repairs are not applied to the blueprints (other tasks' files).
- The glue sketch for Q4 is unchecked.
- The uncompiled signatures (R1fp, R1hecke, R2fp, R1rec, GroupModel.height, MC7) were reviewed
  as mathematics only.
