# rv-leaves48: adversarial review of the 48 concrete leaves of the H decomposition

Task rv-leaves48, 2026-11-12. Base: wip/integrate-w34b, 01267822. Scope: every concrete field of
`HSyn.ResearchLeaves` and `HSyn.TextbookLeaves` in `scratch/h-decomposition/Leaves.lean`
(lines 19109-19200), after leaf-adopt. That is 49 numbered items, counting R1 once although its
part (b) is still a placeholder. They fill 56 bundle fields. The 8 placeholders (R1(b), R3, R17,
R18, R22, T10, T11, T12) are out of scope.

Method. I reviewed the leaf-adopt QM leaves myself (R1R2fpRep, R1rec, R5fp, R5fpCount, H5). Four
reading-only sub-reviews covered the rest, one per cluster:
- A: I2/I3/T9/T27;
- B: I4, HSyn §1, I1;
- C: I6, conductor, descent, T29;
- D: R16, T33, T34, R19-R21.

Their reports are `scratch/rv-leaves48/agentA.md` … `agentD.md`. I re-read the leaves they flagged
as risky, and every leaf whose correctness depends on a definition. All Lean was compiled here,
one process at a time. The results log is `scratch/rv-leaves48/log.md`.

Marks. VERIFIED means read in Leaves.lean or Mathlib, or compiled. STANDARD means published
mathematics with a reference. SPECULATIVE means an assessment. There is no network on this host,
so every theorem number recalled from memory is UNVERIFIED. For locators I rely on
`docs/research/locators.md`.

## Verdict

**No concrete leaf is OVER-STRONG, VACUOUS or MISSTATED. All 56 bundle fields are OK** as Lean
statements: each is the published statement, or a consequence of it, over genuine definitions.
Some residual risks remain, and they are not in the Lean text:

- **Unread primary sources.** Faltings' Lemma 5 (R20), SGA 7 IX 4.7 at `m = 3` (R6), Serre–Tate
  1968 (R7), SGA 7 IX 3.5/3.6 (R8), Faltings 1983 (R9) and Bost's display (R21) were not read by
  the locator audit. Their theorem numbers stay UNVERIFIED.
- **H5 carries the risk of the height definition.** If `stableFaltingsHeight` were mis-encoded,
  `H5.StableHeightFinite` would be **false**, not junk-true. The bundle would then be
  unsatisfiable. That is the safe direction of failure, and I found no encoding error.
- **The QM leaves depend on a premise.** They are consequences only together with rv-qm-polar's
  Lemma P: there is a unique principal polarization of the fixed Rosati type `μ = 2j + ij`. That
  lemma has had model review only.

Non-verdict findings (repair text in `scratch/rv-leaves48/Repairs.md`):

1. **`X1ModelExists` is in neither bundle.** `r16` and `t34` quantify over `IsJ1 N J`, which is
   inhabited only given `X1ModelExists` together with T33. leaf-modcurves records it as a glue
   target, but nothing proves it. Until it is proved or added as a leaf, r16 and t34 cannot feed
   C9, E1 or E2. Compiled: the bundles plus `X1ModelExists` give `ModCurveLeaves` and `exists_J1`.
2. **"Not yet known non-vacuous" is the wrong description of R19-R21.** This applies to the
   docstring at 19181 and to h-decomposition.md (lines 260, 340, 758, 773, 783, 821, 881). The
   height is `⊤` or the true stable height (compiled iff). So R19-R21 are true for the
   definition, and only `H5` can expose a defect.
3. **Docstrings.**
   - The QM premise at 19112 lacks the Rosati type. Without the type, the polarization is not
     unique.
   - T23 is called "Exact"; it is a consequence.
   - t16b should name the arithmetic normalization. rv-leaves-b's claim that θ ↦ θ⁻¹ "preserves
     every clause" is false for clause 3, although the leaf is still true.
   - T31's citation of `cd Ẑ = 1` is inconsistent between notes.
4. **Glue note.** `HSyn.GaloisRep` (r14, r15) and `PkgI4.GaloisRep` (r13, PanFor) are distinct
   structures, so the glue must convert between them.

## Verdict per leaf (worst residual risk first)

| field | Lean name (line) | verdict | reason (short; details in the log and agent reports) |
|---|---|---|---|
| h5 | `LeafAdopt.H5` (18767) | OK | `StableHeightFinite`: for a number field, the index set of the infimum is nonempty (Néron model over a semistable `L` with its true uniformization), and the value is the stable height. `NeronModelMinimal`: `ω_𝒩 ⊆ ω_𝒢` by the Néron mapping property. Every field of `MetrizedModel` is pinned (lattice `⋀^g ω_𝒢`, periods `ker Φ`, `coeff = jacDet`, metric `\|c\|²·covol`), and `IsAnalyticUniformization` is satisfiable by the true uniformization. A defect would make H5 false (compiled D-P3) |
| r1r2 | `LeafAdopt.R1R2fpRep` (18705) | OK (composite consequence; Lemma P) | Checked: level structure on `K`-points ⇔ constant `A[3]` in char 0; `A[3]` free of rank 1 over `𝒪/3𝒪` although `3 ∣ disc B`; `Γ(3)` torsion-free (`nrd(ζ−1) ∈ {1,2,3}`); `Y₃` has two geometric components (not required connected); `π₀(X₆) = 1`; fibres = `W`-orbits since `Aut 𝒪 = N(𝒪)/ℚ^×`; the CM equations force the maximal orders `ℤ[i]`, `ℤ[ζ₆]`, `ℤ[√−6]`; values `0, ∞, −16/27` free by `PGL₂(ℚ)` |
| r1rec | `LeafQM.AV.R1rec` (15444) | OK (consequence; Lemma P) | `fieldOfModuli3 P ⊆ E(y)`; `E(y)/E` unramified outside 3 (`K(3)_ℓ = 𝒪_ℓ^×`, `ℓ ≠ 3`, optimal embedding); `E` unramified outside `{2,3}` |
| r5 | `LeafQM.AV.R5fp` (15579) | OK (Lemma P) | González–Rotger Thm 5.12; `b = 0` gives degree `h` (e.g. `ℚ(√−6)`: degree 2, not containing `k`, consistent with `X₆(ℝ) = ∅`); `conductor` is 0 for non-orders, so `Coprime` fails |
| r5count | `LeafQM.AV.R5fpCount` (15612) | OK (Lemma P) | Eichler: `h(R)∏_{p∣6}(1−(k/p)) = 2^{#inert} h(R)`, type number 1 |
| r20 | `ZInQ.DefFaltings.R20_FaltingsLemma5` (18565) | OK, source unread | `\|h(A)−h(B)\| ≤ ½ log deg`, from Lemma 5 with `0 ≤ [K:ℚ]⁻¹ log #s*Ω ≤ log deg`; stable heights by base change. Junk `⊤` only makes it vacuous (D-P2) |
| r19 | `ZInQ.DefFaltings.R19_GaudronRemond` (18555) | OK | locators.md R19: GR use Faltings' original normalization, both directions bounded by `κ(A)`. (A Deligne-normalized GR would have made the leaf over-strong, because `κ` grows with `h`.) |
| r21 | `ZInQ.DefFaltings.R21_Bost` (18572) | OK | `h_F ≥ −g log(π√2) ≈ −1.4913g ≥ −1.5g` under the Deligne reading of Bost (the only one consistent with `y² = x³+1`, `h_F = −1.32`); GR's printed use read |
| r10 | `PkgI4.DeRhamComparison` (4510) | OK | `IsDeRhamOver`, `htMultOver` on Mathlib's `BDeRham` (classical: `ker θ` principal for `𝓞_{ℂ_p}`); weights 0, −1 each `g` times |
| r11r12 | `PkgI4.PanBerger` (4616) | OK | `5 ≤ p` (Pan's `p = 3` exception avoided); de Rham for pst via Berger; conclusion existential, so either Frobenius normalization gives it |
| r13 | `PkgI4.EigenformHT` (4535) | OK | weights `{0, 1−k}` with cyclotomic weight −1 (Mathlib's `cyclotomicCharacter` is genuine on `PadicAlgCl p`); every level (Kato) |
| t23 | `PkgI4.T23_FontaineClosure` (4692) | OK | matrix form on `V^∨`, continuity where needed; docstring "Exact" should say "Consequence" |
| r16 | `LeafModCurves.R16_EichlerShimuraJ1'` (16348) | OK (usage: needs `X1ModelExists`) | Shimura 1973 Thm 1 unconditional clauses + rank 2 over `K_f⊗ℚ_ℓ` + char poly `X²−a_pX+χ(p)p` of arithmetic Frobenius on covariant `V_ℓ`; the `ā_p` convention is absorbed by `θ∘c`; `IsNewform` is Li's newform by strong multiplicity one |
| t34 | `LeafModCurves.DimJ1Genus` (16373) | OK (same usage note) | genus formula for `±Γ₁(N)`; `dim Jac = genus` |
| t33 | `LeafModCurves.JacobianExists ℚ` (16157) | OK | Albanese property with `∃!`; a trivial `J` satisfies it only in genus 0, where it is the Jacobian |
| r14 | `HSyn.EigenformRepExists` (18933) | OK | Deligne / Deligne–Serre for every `ℓ, ιC, ιL`; the eigenform hypothesis excludes 0 (compiled B-P3) |
| r15 | `HSyn.DeligneSerreConseq` (18942) | OK | DS Thm 4.1 + Chebotarev + Brauer–Nesbitt; semisimplicity kept |
| r6 | `PkgI2.RaynaudCriterion` (1474) | OK, `m = 3` locator unread | `A[m]` rational, `m ≥ 3` invertible ⇒ semistable ⇒ `(σ−1)² = 0` |
| r7a, r7b | `PkgI2.NeronOggShafarevich`, `SerreTatePotentialGood` (1416, 1437) | OK | genuine inertia (Mathlib stabilizer/kernel), any discretely valued `K` |
| r8 | `PkgI2.GrothendieckMonodromy` (1457) | OK | one `K'` for all `ℓ` (semistability is `ℓ`-independent) |
| r9a, r9b | `PkgI3.FaltingsSemisimple`, `FaltingsTate` (2784, 2791) | OK | abstract semisimplicity equals continuous semisimplicity for finite-dimensional `V_ℓ` |
| r4 | `PkgI1.ThetaModularity` (232) | OK | standard `θ[a,b]`; Mathlib's `J` gives the same `Sp₄(ℤ)`; `χ₁₀` has trivial character (`∏θ² = (∏θ)²`) |
| t1-t5 | `PkgI2.PurityBranchLocus` … `TorsionStructure` | OK | t1 matches Stacks 0BMB's hypotheses; t2's index is a length, nonzero on primes; t4 strictly henselian `w` |
| t6-t8, t26, t27 | `PkgI3.HomFreeFinite`, `CharPolyIndepOfEll`, `PoincareReducibility`, `TateModuleFree`, `QMDichotomyYu` | OK | t8: `A = 0` makes `f ≠ 0` impossible; t27 with indefiniteness (Yu), list of cases complete (`M₂(ℚ)` excluded) |
| t9 | `LeafPush.T09_WeilPairing` (11839) | OK | compatibility exponent `^m` correct; the "nondegenerate up to `d`" clause excludes the trivial pairing |
| t13, t17, t18, t19, t24, t25 | HSyn §1, `PkgI4.NewformOfEigenform` | OK | t24 holds for imprimitive `ψ` (formal recursion with `χ' = χψ²`); t18 via the normal core of `U`; t19 for any group over any char-0 field |
| t14a, t14b, t15 | `PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC` | OK | cochain forms (rv-leaves-b repair 3 applied); `ZMod 2` discrete |
| t16a, t16b | `PkgI6.LocalKroneckerWeber`, `LocalReciprocityUpper` | OK | t16b true in the arithmetic normalization (docstring repair P5) |
| t20, t21 | `GlueConductor.HilbertDifferentFormula`, `SerreDifferentBound` | OK | global `G_i` = local `G_i`; transport citation present |
| t22a, t22b | `PkgI6.HerbrandQuotient`, `HerbrandTransitivity` | OK | `v < −1` gives `⊤` on both sides |
| t28 | `PkgI1.IgusaClebschSeparation` (774) | OK | `J10 ≠ 0` ⇔ six distinct roots on `ℙ¹`; ⇐ via the invariant ring with `I₁₅` up to sign (`e ↦ −e`) |
| t29a, t29b | `LeafPush.T29a_DivisionNormalizer`, `T29b_SplitNormalizer` | OK | anisotropy forces a division algebra; parity of `v(nrd)` |
| t30, t31 | `GlueDescent.B2Q.LeafSqrtCrit`, `LeafUnramified` | OK | t30: finite-order `ψ` of `ℚ_p^×` is a square iff `ψ(−1) = 1`; `rec(−1)` acts by `ζ ↦ ζ⁻¹` on `μ_{p^k}`; `k = 0` forces `u = 1`. t31: the class dies under inflation |

## What compiles (VERIFIED)

- `lake env lean scratch/h-decomposition/Leaves.lean`: EXIT 0 (3m39s), with one `sorry`
  (`glueOutputs_of_leaves`). It first needs
  `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant`.
- `scratch/rv-leaves48/Probes.lean`, a verbatim copy of Leaves.lean plus probe sections: EXIT 0
  (3m34s). The new theorems use only `propext`, `Classical.choice` and `Quot.sound`. The probes:
  - `RvLeaves48D.sfh_eq_top_iff`: `stableFaltingsHeight A = ⊤ ↔` no `MetrizedModel` of `A`
    exists.
  - `r21_trivial_of_empty` and `r19r20_hyp_false_of_empty`: in the `⊤` case R21 is trivial at
    `A` and the hypothesis of R19/R20 is unsatisfiable.
  - `H5_forces_metrized_model` and `r19_hyp_satisfiable`: H5 forces a metrized model for every
    `A` over a number field.
  - B-P3: the zero cusp form is not a normalized eigenform.
  - The bundle field types, and the HSyn = PkgI4/PkgI6 duplicates by `rfl`.
  - QM-P1: `μ = 2j + k` satisfies `μ² = −6` in `(2, −3)`.
  - Bundle check: `ResearchLeaves + TextbookLeaves + X1ModelExists → ModCurveLeaves`, and
    `exists_J1`.
  - A/C notation facts: `ℍ[ℚ,a,b]`, `G_K = Aut(K̄/K)`, `G^0 = G_0`.

## What remains

- No Lean probe can build a positive witness of a scheme-level hypothesis: an abelian surface
  with QM, a `MetrizedModel`, or a model of `X₁(N)`. Non-vacuity of those hypotheses therefore
  rests on mathematics (STANDARD) and is not compiled.
- Primary sources not read (the locators listed under Verdict) remain UNVERIFIED, as in
  locators.md.
- Lemma P (rv-qm-polar) has model review only, no human review.
