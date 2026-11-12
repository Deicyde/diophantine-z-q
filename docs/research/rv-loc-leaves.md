# rv-loc-leaves: the Lean leaves against the locator audit

Task: check the leaf statements of `scratch/h-decomposition/Leaves.lean` (with their sources in
`scratch/pkg-I*/`, `scratch/leaf-push/`, `scratch/def-ladic-cond/`) against the corrections of
`docs/research/locators.md` (the audit), items (a)-(j). Compiled Lean in `scratch/rv-loc-leaves/`.
Log: `scratch/rv-loc-leaves/log.md`.

## Verdicts

| Item | Lean object(s) | Verdict |
|---|---|---|
| (a) Pan∘Berger | `PkgI4.PanFor`, `PkgI4.PanBerger`, `GaloisRep.AttachedUpToTwist` | **FAITHFUL** (a consequence). The leaf is stated only for `p ≥ 5`, so Pan's `p = 3` exception does not arise. The Frobenius and dualization conventions are right. Only the docstring needs a repair |
| (b) Serre–Tate, potential good reduction | `PkgI2.NeronOggShafarevich`, `PkgI2.SerreTatePotentialGood`, `GrothendieckMonodromy`, `R08_GrothendieckMonodromy`, `RaynaudCriterion` (+ `ObjBridge` copies) | **FAITHFUL.** Every potential-good or semistable form uses **one** finite `K'` (one open subgroup of inertia) for all `n`. NOS is per-`m`, and that is correct for good reduction |
| (c) Pazuki | `R22_Pazuki` (opaque), pkg-I5 `PazukiGoodGenus2` (`+ log π`), rv-leaves-a's `PazukiGoodGenus2'` (`+3`), glue `GlueAssembly.PazukiOutput` | **FAITHFUL** (both forms are consequences). I proved the audit's three consequence steps in Lean, from a literal form with truncated heights, `|·|`, `min` and `h_D = h_F + log π`. The `R22` placeholder docstring is out of date (repaired) |
| (d) Baba–Granath branch data | `R02_BabaGranath` (opaque), `PkgI1.QMHauptmodul`, docstring of `GlueRepo.PR` (Prop. TS, `e_b`) | **R02 docstring WRONG → repaired.** `QMHauptmodul` is **FAITHFUL**: it states no ramification index, and its "order 4, 6, 2" is orbifold data of `Γ*`. The `(4,6,2)` used by Lemma PR(i) for `Y₃ → P¹_j` is correct, but as orbifold orders plus torsion-freeness of the level-3 group (glue), not as indices of `X₆ → X₆/W`, which are `(2,2,2)` (compiled check) |
| (e) CM points (González–Rotger) | `R05_GonzalezRotger` (opaque) | **WRONG (docstring) → repaired** to `#CM(R) = 2^b h(R)`, `b = #{p ∣ 6 inert in k}`. The underlying notes (rv-h-cm §3.3) already use `2^b h(R)`. No Lean statement carries the wrong count |
| (f) Carayol R17 | `LadicCond.CarayolR17'`, `LadicCond.CarayolR17`, `PkgI4.CarayolFor`, `PkgI4.CarayolUnramified` | **FAITHFUL.** Every `ℓ` (including 2) and every `p ≠ ℓ` (including `p ∣ N`) is covered, as the audit confirms. Docstrings that call `p ∣ N` coverage "UNVERIFIED / open" should be updated |
| (g) R13, R14 | `PkgI4.EigenformHT`, `PkgI4.EigenformRepExists` (= `HSyn.EigenformRepExists`) | **FAITHFUL, cusp forms only** (`CF N k` is Mathlib's `CuspForm` on `Γ₁(N)`). Eisenstein forms are excluded by the type, and no consumer needs them (Pan's output is cuspidal) |
| (h) R15 | `PkgI4.DeligneSerreFinite` (= `HSyn.DeligneSerreConseq`) | **FAITHFUL.** `ρ.IsSemisimple` is a hypothesis |
| (i) T27 | `PkgI3.QMDichotomy` (= `ObjBridge.QMDichotomy`, bundle field `t27`) | **STRONGER THAN Yu's theorem as cited** (it drops "indefinite"). It is still true, as a consequence of Mumford §21 (no type III when `g = 2`, char 0), but not of the refereed locator. **Repaired** to `QMDichotomyYu` (compiled). The old form implies the new one, and the project's `B = (2,-3)` satisfies the new hypothesis |
| (j) R16 | `R16_EichlerShimuraJ1` (opaque) | **Placeholder, consequence form OK.** It does not use Shimura 1973's zeta clause, so the Fricke condition does not enter. The docstring is **repaired** to name the three suppliers: Thm 1's unconditional clauses, rank 2 over `K_f ⊗ ℚ_ℓ`, and the Eichler–Shimura relation. It also fixes the Hecke-convention remark |

None of the ten items is VACUOUS. The only Lean statement that has to change is T27, and the
change is a weakening. Five docstrings are wrong or out of date: R02, R05, R16, R17, R22. Item (a)
also needs a docstring addition.

## (a) Pan∘Berger

Lean (Leaves.lean L4565-4581):
```lean
def PanFor (IsPst : LocalPred) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ ρ : GaloisRep p 2,
    ρ.IsIrreducible → ρ.FinitelyRamified → IsPst p 2 (ρ.restrictLocal p) → ρ.IsOdd →
    ρ.DistinctHTWeights p → ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : CF N k), 0 < N ∧ 1 ≤ k ∧
      IsNormalizedEigenform g χ ∧ ∃ (ψ : GaloisChar p) ιC ιL (S : Finset ℕ), ρ.AttachedUpToTwist ψ ιC ιL g S
def PanBerger : Prop := PanFor fun p _ n ρ => LocalIsDeRham p n ρ
-- AttachedUpToTwist: ∀ q ∉ S prime, ρ unramified at q ∧ ∃ α, ιC α = a_q(g) ∧
--   ∀ v σ, LiesOver v q → IsArithFrob σ v q → tr ρ(σ) = ψ(σ) · ιL α
```
- **What the audit says.** Pan arXiv v2 Thm 1.0.4 is VERIFIED. At `p = 3` the local residual
  semisimplification must not be `η ⊕ ηω`; there is no such proviso at `p = 5`. Pan uses geometric
  Frobenius and cyclotomic HT weight `−1`; arithmetic traces need dualization and a twist.
  De Rham can replace pst only through R11.
- **The `p = 3` exception.** The leaf quantifies over `p ≥ 5` only, which is strictly weaker than
  Pan (VERIFIED: the `5 ≤ p` binder). The route uses `r₅` (`p = 5`), so nothing is lost. A `p = 3`
  form would have to add the residual clause, which needs residual representations. Not needed.
- **Conventions (VERIFIED by the compiled lemma `RvLocLeaves.trace_inv_smul_fin_two`).** Suppose
  Pan's conclusion holds: `ρ ≅ ρ_g ⊗ ψ'` with `tr ρ_g(Frob_geom) = a_q`, `det ρ_g(Frob_geom) = χ(q)q^{k−1}`.
  - Then `tr ρ(Frob_arith) = ψ'(Frob_arith)·a_q χ(q)^{-1} q^{1−k}`.
  - Here `a_q χ(q)^{-1} = conj(a_q) = a_q(g^ρ)`, where `g^ρ` is the conjugate normalized eigenform
    with character `χ̄` (STANDARD).
  - And `q^{1−k} = ε(Frob_arith)^{1−k}`, with `ε` the ℓ-adic cyclotomic character.

  So `AttachedUpToTwist` holds with `g^ρ`, `χ̄` and `ψ = ψ'ε^{1−k}` (continuous). The leaf's
  existential quantifiers over `g`, `χ`, `ψ`, `ιC`, `ιL` absorb the change. `IsOdd`, `IsIrreducible`
  (over the algebraically closed `ℚ̄_p`) and `DistinctHTWeights` do not depend on the convention.
  `LocalIsDeRham` handles the finite coefficient field by restriction of scalars:
  `finrank_{ℚ_p} D_dR = n·[E:ℚ_p]`, which answers the audit's admissibility remark.
- **Docstring repair** (paste over the `PanFor` docstring's first sentence):
  > Pan, JAMS 35 (2022), 1031-1169 (journal numbering UNVERIFIED) = arXiv:1901.07166v2
  > Thm 1.0.4 (VERIFIED, audit and h-a011). Stated for `p ≥ 5` only. At `p = 3` Pan excludes
  > `ρ̄|_{G_{ℚ_3}}^{ss} ≅ η ⊕ ηω`, and the leaf does not cover `p = 3`. Pan's geometric-Frobenius
  > conclusion `ρ ≅ ρ_g ⊗ ψ'` gives this arithmetic-Frobenius trace form with `g^ρ` (character `χ̄`)
  > and `ψ = ψ'ε^{1−k}` (`tr(M⁻¹) = tr M / det M`, `RvLocLeaves.trace_inv_fin_two`).

## (b) Serre–Tate and potential good reduction

Lean (Leaves.lean L1426-1437, identical copy in `ObjBridge` L10862):
```lean
def SerreTatePotentialGood : Prop := ∀ K O [DVR O] w, w.comap _ = O → ∀ A [IsAbelianVariety A] ℓ, ℓ.Prime → IsUnit (ℓ : O) →
  ((∃ K', FiniteDimensional K K' ∧ HasGoodReduction (baseChange A K') (w.comap _)) ↔
   (∃ K', FiniteDimensional K K' ∧ ∀ σ, IsInertia w σ → (∀ x ∈ K', σ x = x) →
        ∀ n : ℕ, ∀ x ∈ torsion A K̄ (ℓ ^ n), galAct A σ x = x))
```
- **The quantifier order.** The audit warns that the open subgroup must be one subgroup for all
  `n`. Here `∃ K'` comes before `∀ σ … ∀ n`, so a single `K'`, i.e. the single open subgroup
  `I ∩ G_{K'}`, fixes every `A[ℓⁿ]`. This means "the image of inertia in `Aut T_ℓ A` is finite", which
  is Serre–Tate's condition. The leaf is not vacuous, and the per-`n` weakening is absent.
  VERIFIED (read).
- **The other forms.** `GrothendieckMonodromy` and `R08_GrothendieckMonodromy` (leaf-push) are
  quantified the same way: `∃ K'` before `∀ σ ∀ ℓ ∀ n`. `RaynaudCriterion` concludes for **every**
  inertia `σ`, with no `K'`, from `A[m]` rational with `m ≥ 3`; that is the semistable conclusion
  and does not need an open subgroup. `NeronOggShafarevich` is per-`m` with no `K'`, which is
  exactly NOS for good reduction.
- **Remaining issues.** Serre–Tate 1968 itself is UNVERIFIED (the audit could not read it), as is
  the `m = 3` boundary of R6 (outside this item).

## (c) Pazuki

Lean: `R22_Pazuki` is an opaque placeholder. Its docstring is the hardened form
`X_D = max(1, h_F + 3)`. Two concrete special cases exist in pkg-I5 (Mathlib only):
`PazukiGoodGenus2` with `max 1 (faltingsHeightGood E + Real.log Real.pi)`, and rv-leaves-a's
`PazukiGoodGenus2'` with `+ 3`. Here `faltingsHeightGood` is Faltings' original `(i/2)^g`
normalization (`hypVol`, VERIFIED read). The glue interface `GlueAssembly.PazukiOutput` uses `hA + 3`.

- **What the audit says.**
  - `|H_Θ − H_D/2| ≤ C₂ log(min(H_Θ,H_D)+2)` with truncated `H_Θ = max(1,h_Θ)`, `H_D = max(1,h_D)`.
  - `h_D = h_F + log π` (`g = 2`).
  - The auxiliary bound must dominate `max(1, h_D)`.
- **What compiles** (`scratch/rv-loc-leaves/PazukiR22.lean`, a copy of `I5.lean` plus a new section):
  - `PazukiLiteral hθ hD`: the literal corollary at `g = r = 2`, with absolute value, truncations
    and minimum.
  - `pazuki_upper_of_literal`: from `PazukiLiteral hθ (hF + log π)` and `max 1 (hF + log π) ≤ XD`,
    conclude `hθ ≤ XD/2 + C₂ log(XD + 2)`. These are the audit's three consequence steps, proved.
  - `pazuki_logpi_of_literal` and `pazuki_plus3_of_literal` (with `log π ≤ 3`).
  - `PazukiGoodGenus2Literal`: the literal form for pkg-I5's genus-2 objects.
  - `pazukiGoodGenus2_of_literal`, `pazukiGoodGenus2'_of_literal`, `pazukiGoodGenus2'_of_pazukiGoodGenus2`.

  All print `[propext, Classical.choice, Quot.sound]`.
- **Verdict.** Both `PazukiGoodGenus2` and `PazukiGoodGenus2'` are FAITHFUL consequences.
  `max 1 (h_F + 3) ≥ max 1 (h_F + log π) = H_D` dominates the truncated Deligne height, as the
  audit requires. `h_Θ ≤ H_Θ` handles the truncation. The rv-leaves-a "UNVERIFIED normalization"
  risk is closed by the audit's reading `h_D = h_F + log π`.
- **Open.** It is still not checked that Pazuki's level-2 theta height is the Thomae point's
  Euclidean height (pkg-I5's reading; UNVERIFIED here). `PazukiOutput` uses sup norms `≤` Euclidean,
  which is the safe direction. The repaired `R22` docstring is in `Placeholders.lean`.

## (d) Baba–Granath's branch data

- **`R02_BabaGranath` docstring (L12110).** It says "branched over `0, ∞, −16/27` with indices 4, 6, 2".
  This is **WRONG**, as the audit says: a degree-4 map cannot have index 6.
  - Compiled check (`Conventions.lean`). In Elkies' model `y₁² = −t`, `y₂² = 3(t−1)` of
    `X₆ → X₆/W` with `t = 1 + 27j/16` (`PkgI1.elkies_t`), the fibre over `t = 1` (`j = 0`) is
    exactly `{(±i, 0)}` (`fibre_t_one`), and the fibre over `t = 0` (`j = −16/27`) is exactly
    `{(0, ±i√3)}` (`fibre_t_zero`). The two points are distinct (`fibre_points_distinct`).
  - So the index of the Galois degree-4 cover is 2 at both values. Index 2 at `j = ∞` is the
    audit's reading; it was not checked in Lean.
  - The repaired text is in `Placeholders.lean`: moduli identification from Thm 2.1/Lemma 3.1, and
    orbifold orders `(4,6,2)` of `Γ*` from §3.1 p. 740 and Prop. 3.9/Thm 3.10.
- **`PkgI1.QMHauptmodul`.** It makes no ramification claim. It gives a continuous surjection
  `ℍ → P¹(ℂ)` whose fibres are the `Γ*`-orbits, with values at the fixed points of `ι(x)` for
  `x² = −1`, `x² − x + 1 = 0`, `x² = −6`.
  - "Order 4, 6, 2" appears only in the docstring, as elliptic (orbifold) orders of `Γ*`, and that
    is correct.
  - Each value clause is a single point of `X₆/W`. By the corrected R5 count, `CM(ℤ[i])` and
    `CM(ℤ[ζ₃])` have 2 points each on `X₆` (one `W`-orbit), and `CM(ℤ[√−6])` has 2 points
    (`h = 2`, `b = 0`) forming one orbit. So the clauses are consistent. **FAITHFUL** (verdict of
    rv-leaves-a unchanged).
- **Lemma PR(i) (`GlueRepo.PR` docstring, L9951).** It uses `(e₀, e_∞, e_{−16/27}) = (4,6,2)` for
  `Y₃ → P¹_j`, attributed to "(A2)". The values are right for that map. `Y₃(ℂ)` is a union of
  `Γ(3)\ℍ`, and `Γ(3) = O¹ ∩ (1 + 3O)` is torsion-free, which is proved (`GlueRepo.TorsionFree`,
  `1 + 3M_r(ℤ₃)`). It is also normal in `Γ*`. So the index over an elliptic point equals its
  orbifold order. The attribution should read: "orbifold orders of `Γ*` (Baba–Granath §3.1) and
  torsion-freeness of the level-3 group", not "indices of `X₆/W`".

## (e) CM points

`R05_GonzalezRotger` (L12123): "`#CM(R) = h(R)` on `X₆`". This is **WRONG** (audit; GR Prop. 5.6
has the factor `2^{#{p ∣ D(R)N(R)}}`).
- **The repaired count** (in `Placeholders.lean`). For `(f,6) = 1`, `N = 1`:
  `#CM(R) = 2^b h(R)` with `b = #{p ∣ 6 inert in k}`, and `W(R) × Gal(H_R/k)` acts simply
  transitively. This is the statement rv-h-cm §3.3 already uses (VERIFIED read).
- **Consistency checks.**
  - It agrees with the orbifold signature: `e₂ = e₃ = 2` on `X₆` (`b = 1`, `h = 1`).
  - It gives 4 points at discriminant −19 (`b = 2`). The Legendre data are compiled:
    `RvLocLeaves.cm_count_factor_disc_neg19`, `cm_count_factor_disc_neg4_neg3`.
- **The field clause.** `ℚ(x) = H_R` if `D(R) ≠ 1`, index 2 otherwise (Thm 5.12). It was right
  before and is kept. The repaired text also says it concerns `X₆`, not `Y₃` or `X₆/W` (audit
  note 1, the `j = −16/27` example).
- **Impact on glue.** NoCM (G6) relies on the rv-h-cm argument, which already uses `2^b h(R)`, so
  nothing proved changes. h-decomposition.md's R5 paragraph should be corrected the same way
  (not edited here: another task's file).

## (f) Carayol R17 (def-ladic-cond)

Lean (`scratch/def-ladic-cond/LadicCond.lean` L431-443):
```lean
def CarayolR17' : Prop := ∀ ℓ [Fact ℓ.Prime] ιC ιL N χ (f : CF N 2) (ρ : GaloisRep ℓ 2) p [Fact p.Prime],
    0 < N → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f → p ≠ ℓ →
      condExp (ρ.restrictLocal p) = (N.factorization p : ℚ)
-- CarayolR17: the same at every adapted level L (condAt L); equivalent given SwanIndependent/AdaptedExists
```
- **What the audit says.** Théorème A covers every finite `p` and every coefficient place of
  different residue characteristic, including `p ∣ N` and `ℓ = 2`. The even-degree hypothesis does
  not apply to `ℚ`. Contragredient and unramified-twist conventions do not change the conductor.
- **The statement.** It quantifies over every `ℓ` and every `p ≠ ℓ`, with no `p ∤ N` and no
  `ℓ ≠ 2` restriction, so it matches the audit's coverage.
- **The objects.**
  - `condExp = codim V^{I} + Sw` is the Serre–Tate conductor of the ℓ-adic representation. It
    equals the WD conductor and does not change under duals, so the Tate normalization of
    `AttachedTo` (the dual of Deligne's `ρ_f`) is harmless.
  - A semisimple `ρ` attached by traces is isomorphic to Carayol's (Chebotarev + Brauer–Nesbitt).
  - The level `v_p(N)` is the newform conductor `a(π_p)` (Casselman; locator UNVERIFIED).

  **FAITHFUL.**
- **`CarayolR17`.** It is a consequence of `CarayolR17'` plus the glue `SwanIndependent`
  (`carayolR17_of_R17'`, compiled there). It is not a separate published statement and should be
  labeled as such (it is).
- **Docstring repair** (paste into LadicCond.lean / Leaves.lean when folded in). Replace "(theorem
  letter VERIFIED …; content and coverage of `p ∣ N` UNVERIFIED)" by:
  > Ann. Sci. ÉNS 19 (1986), Théorème (A), pp. 409-411 and §0.8 p. 411 (read by the locator audit:
  > all finite `p` and every `ℓ ≠ p`, including `p ∣ N` and `ℓ = 2`; the finite discrete-series
  > hypothesis concerns only totally real `F` of even degree), with `a(π_p) = v_p(N)` for newforms
  > (Casselman 1973, locator UNVERIFIED). Do not replace it by Théorème (B) or by the `Γ₀`
  > elliptic-curve corollary.

  The same applies to the R17 placeholder docstring (`Placeholders.lean`) and to
  `PkgI4.CarayolUnramified` (its "content UNVERIFIED" becomes "coverage VERIFIED by the audit").

## (g) R13 and R14: cusp forms only

```lean
abbrev CF (N : ℕ) (k : ℤ) := CuspForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k
def EigenformHT : Prop := ∀ ℓ ιC ιL N k χ (g : CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → IsNormalizedEigenform g χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL g →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}
def EigenformRepExists : Prop := ∀ ℓ ιC ιL N k χ (g : CF N k),
    0 < N → 1 ≤ k → IsNormalizedEigenform g χ → ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL g
```
- **Cusp forms only.** `g` ranges over Mathlib's cusp forms, so Eisenstein series are excluded by
  the type. This is the audit's "narrow the leaf" option, and it is already in place.
- **Do any consumers need Eisenstein forms?** No:
  - `PanFor` produces `g : CF N k`, i.e. a cuspidal eigenform, which is also Pan's printed
    conclusion.
  - G12 applies R13/R14/R15 to that `g` and its twists. `EigenformTwist` stays in `CF`.
- **R13 conventions.**
  - Weights `{0, 1−k}` are in the Tate normalization: `AttachedTo` uses arithmetic Frobenius with
    trace `a_p`, i.e. the dual of Deligne's cohomological `ρ_g` (weights `{0, k−1}`). This agrees
    with the audit's "dualize to `{0, 1−k}`".
  - Every level is covered, as the audit wants, through Kato §§9.2-9.4 for newforms.
  - General cuspidal eigenforms (old forms that are `U_p`-eigen) reduce to the newform with the
    same eigenvalues away from `N` (`NewformOfEigenform`) and Brauer–Nesbitt. `ρ.IsSemisimple` is
    needed for this, and it is a hypothesis.
- **R14.** It covers weight 1 through Deligne–Serre (arithmetic Frobenius explicit) and weight ≥ 2
  through Deligne's construction, dualized. There is no `ℓ = 2` exclusion, in agreement with the
  audit.
- **Docstring repair for R13.** Cite Kato, Astérisque 295 (2004), §9.2 (9.2.2) pp. 187-188 and
  §9.4 as the checked all-level supplier. Saito 1997 stays UNVERIFIED and must not be listed as
  checked.

## (h) R15: semisimplicity

`DeligneSerreFinite` (L4511) and `HSyn.DeligneSerreConseq` (L12076) both have the hypothesis
`ρ.IsSemisimple` before `ρ.AttachedTo ιC ιL g → (Set.range ρ.toHom).Finite`. Semisimplicity is
kept: VERIFIED (read). **FAITHFUL**, as Deligne–Serre Thm 4.1 plus their Lemma 3.2
(Chebotarev/Brauer–Nesbitt). Without the hypothesis the statement would be false, since a
non-split extension can have the same traces. Its presence is essential and should be noted in
the docstring.

## (i) T27: indefinite quaternion division algebra

```lean
def QMDichotomy : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
    ∀ a b : ℚ, (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) → Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
      Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨ ∃ d : ℚ, d < 0 ∧ Nonempty (End0 A ≃ₐ[ℚ] M₂(ℚ[X]/(X² − d)))
```
- **What the audit says.** Yu, JPAA 217 (2013) Thm 1.1 (journal p. 907) is the checked refereed
  locator, and its hypothesis "indefinite quaternion division algebra" must be kept.
- **Finding.** The Lean statement has no indefiniteness hypothesis, so it is **stronger than Yu's
  theorem**. For definite `B` it is still true:
  - Simple `A` cannot have a definite quaternion `End⁰` when `g = 2` in characteristic 0
    (Mumford §21, type III excluded; STANDARD, locator UNVERIFIED).
  - Non-simple `A` gives `M₂(k)`.

  So it is a consequence of the Albert classification, not of the cited Yu theorem.
- **Repair** (compiled, `scratch/rv-loc-leaves/T27Yu.lean`, a copy of pkg-I3 plus a new section):
  ```lean
  def QuatIndefinite (a b : ℚ) : Prop := 0 < a ∨ 0 < b
  def QMDichotomyYu : Prop :=
    ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : AbVar k), A.dim = 2 →
      ∀ a b : ℚ, QuatIndefinite a b → (∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x) →
        Nonempty (ℍ[ℚ, a, b] →ₐ[ℚ] End0 A) →
          Nonempty (End0 A ≃ₐ[ℚ] ℍ[ℚ, a, b]) ∨
            ∃ d : ℚ, d < 0 ∧
              Nonempty (End0 A ≃ₐ[ℚ] Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)))
  theorem qmDichotomyYu_of_qmDichotomy (h : QMDichotomy) : QMDichotomyYu
  theorem quatIndefinite_two_neg_three : QuatIndefinite 2 (-3)
  theorem qmDichotomy_B6 (h : QMDichotomyYu) … -- the A9/G5 use at B = (2,-3)
  ```
  The axioms are standard. No Lean consumer of `QMDichotomy` exists in Leaves.lean besides the
  bundle field `t27` and `ObjBridge.qmDichotomy_iff`, so the swap is local.

## (j) R16 and Shimura 1973's Fricke condition

`R16_EichlerShimuraJ1` is opaque. Its docstring says `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` has a 2-dimensional
`G_ℚ`-stable subquotient with `tr(Frob_p) = ι(a_p(f))`, and cites Shimura 1971 Thm 7.9 and
Shimura 1973 Thm 1.

- **What the audit says.**
  - Thm 1 gives the quotient `A_f`, the `K_f`-action and the dimension unconditionally.
  - Only its final Euler-factor clause has the extra `Γ₀`/Fricke condition.
  - The individual-embedding rank-2 realization and the Frobenius–Hecke relation must still be
    supplied.
- **Verdict.** The leaf does not use the zeta clause, so the Fricke condition is neither needed
  nor silently dropped. The statement is a consequence of three suppliers:
  1. Thm 1's unconditional clauses.
  2. `V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`.
  3. The Eichler–Shimura congruence relation on `J₁(N)` (Shimura 1971 Thm 7.9).

  The docstring repair names all three. It also records that under the other Hecke convention on
  `J₁(N)` the trace is `ι(conj a_p)`, which is the case of `f^ρ`, so the statement over all
  newforms is unaffected. The repaired text is in `Placeholders.lean`.
- No Lean content can be checked, because `J₁(N)` is not in any library.

## Paste-ready list for the integrator

1. **T27.** In Leaves.lean `PkgI3`, add `QuatIndefinite`, `QMDichotomyYu`,
   `qmDichotomyYu_of_qmDichotomy`, `quatIndefinite_two_neg_three` and `qmDichotomy_B6`, verbatim
   from the last section of `scratch/rv-loc-leaves/T27Yu.lean`. Change the bundle field to
   `t27 : PkgI3.QMDichotomyYu`. Change the docstring locator to "Chia-Fu Yu, JPAA 217 (2013),
   Thm 1.1 (journal p. 907; audit: checked); without 'indefinite' the old form is a consequence of
   Mumford §21 only". In `ObjBridge`, add the same hypothesis (or keep `qmDichotomy_iff` for the old
   form).
2. **Placeholders R02, R05, R16, R17, R22.** Replace the five docstrings in Leaves.lean `HSyn` §2
   by those of `scratch/rv-loc-leaves/Placeholders.lean` (namespace `HSyn`, same names).
3. **R22 concrete.** Optionally fold in from `scratch/rv-loc-leaves/PazukiR22.lean`:
   `PazukiLiteral`, `PazukiGoodGenus2Literal`, `pazuki_upper_of_literal`,
   `pazukiGoodGenus2'_of_literal`. `GlueAssembly.PazukiOutput` follows from `pazuki_plus3_of_literal`
   and the sup ≤ L² comparison.
4. **Checks.** `scratch/rv-loc-leaves/Conventions.lean` (`trace_inv_fin_two`,
   `trace_inv_smul_fin_two`, `fibre_t_one`, `fibre_t_zero`, `fibre_points_distinct`), Mathlib only.
5. **Docstrings only, no Lean change.**
   - `PkgI4.PanFor`: the p = 3 proviso and the convention (§(a)).
   - `LadicCond.CarayolR17` and `CarayolR17'`, `PkgI4.CarayolUnramified`: coverage (§(f)).
   - `PkgI4.EigenformHT`: the Kato locator (§(g)).
   - `PkgI4.DeligneSerreFinite`: note that semisimplicity is essential (§(h)).
   - `GlueRepo.PR` header: the source of `(4,6,2)` (§(d)).
   - h-decomposition.md: R2, R5, R16, R17 and R22 paragraphs, the same corrections.

## What compiles

Each file was checked with `lake env lean scratch/rv-loc-leaves/<file>.lean`, one at a time.
- `T27Yu.lean`
- `PazukiR22.lean`
- `Conventions.lean`
- `Placeholders.lean`

All new theorems print `[propext, Classical.choice, Quot.sound]`.

## Not checked

- I did not re-read any primary source; I have no network. Every reading of a paper above is the
  audit's or an earlier note's and is labeled so.
- The identification of Pazuki's theta height with the Thomae point (pkg-I5) is not checked.
- Index 2 at `j = ∞` for `X₆ → X₆/W` was not proved in Lean; only the finite branch values were.
- Leaves.lean itself was not recompiled. The repaired texts compile in copies, and Leaves.lean's
  versions of the same definitions are identical by `diff` (QMDichotomy, read for the rest).
