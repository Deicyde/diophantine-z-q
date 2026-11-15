# elkies-coord: `elkiesX6StarPrinted` discharged from Elkies' theorem in his function-field form `ℚ(X₆)^W = ℚ(t)`

Task elkies-coord, 2026-11-15. Base 24f97774 (leaf-fold20, top `sixContactMin_of_open27`, 58 H fields). Lean:
`ZInQKernel/Contrib/OneProof/ElkiesX6StarPrinted.lean` (the contribution; imports only
`ZInQKernel.Contrib.OneProof.ElkiesX6Star`, the module that declares the statement); `scratch/elkies-coord/`
(log, working copy, `#discharges` check and output, autofold spec, dry-run and its compile check). No other file under
`ZInQKernel/` or `blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, computed, or read in a file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (no network).

## 1. Main result

**The research field `elkiesX6StarPrinted` is a theorem from one new leaf, `ElkiesX6StarFunctionField`: Elkies'
statement in his own wording, "`t` is a coordinate on `X*(6) = X₆/W`", read in function fields as `ℚ(X₆)^W = ℚ(t)`,
with the CM values and the equations of `X₆` over the `t`-line unchanged.** The step that made the old field a
consequence (from "`t` generates `ℚ(X₆)^W`" to "the fibres of `t` on `X₆(ℚ̄)` are the `W`-orbits") is now a Lean proof.
VERIFIED: compiled, standard axioms only.

```
DISCHARGES [OpenResearchLeaves20.elkiesX6StarPrinted] by HDec.QMSplit.Moduli.ElkiesCoord.elkiesX6StarPrinted_of_functionField
  still assumes: [HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 65 open hypotheses, 1344 theorems checked, 6 discharge one
```

(`scratch/elkies-coord/Discharges.lean`, output `scratch/elkies-coord/discharges.txt`. It was run after
`lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ElkiesX6StarPrinted`
(12983 jobs, success; `frozenTarget` uses standard axioms). The other five DISCHARGES lines come from
contributions already in the tree.)

The autofold dry-run (`scratch/elkies-coord/autofold.json`) reports
`strict count: 47/11 on 58 -> 48/10 on 58; strictest 46/12 -> 47/11`: one GLUE field fewer in both columns (the old
row was kind `consequence`, GLUE/GLUE; the new leaf is kind `published`, flag `locator UNVERIFIED`). The generated
module (`scratch/elkies-coord/FoldDryRun.lean`: `OpenResearchLeaves21`, `sixContactMin_of_open28`) compiles, and
`#print axioms HDec.HSyn.sixContactMin_of_open28` gives the standard three. VERIFIED.

## 2. The Lean statements (namespace `HDec.QMSplit.Moduli.ElkiesCoord`)

```lean
/-- The comorphism g^* : ℚ(Z) → ℚ(Z) of an automorphism of an integral scheme (Mathlib's function field = stalk at
the generic point; g fixes the generic point, genericPoint_eq_of_isOpenImmersion). -/
noncomputable def ffPullback {Z : Scheme} [IsIntegral Z] (g : Z ≅ Z) : Z.functionField →+* Z.functionField :=
  (Z.presheaf.stalkSpecializes (gen_specializes g) ≫ g.hom.stalkMap (genericPoint Z)).hom

/-- ℚ(X₆)^W. -/
def fixedByW {X} [IsIntegral X.left] (Ψ) : Set X.left.functionField :=
  {φ | ∀ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, ffPullback ((Over.forget _).mapIso g) φ = φ}

/-- LEAF: Elkies 1998 §3 (UNVERIFIED locator), function-field form, on the canonical witness. -/
def ElkiesX6StarFunctionField : Prop :=
  ∃ Y Φ X Ψ fY (t : ToP1 X.left),
    R1fpPropsAb Y Φ ∧ X6Props Y Φ X Ψ fY ∧
    (∀ (_ : IsIntegral X.left) (hη : genericPoint X.left ∈ t.U),
      fixedByW Ψ = (Subfield.closure {X.left.presheaf.germ t.U _ hη t.f} : Set X.left.functionField)) ∧  -- ℚ(X₆)^W = ℚ(t)
    (CM clause of ElkiesX6StarPrinted, verbatim) ∧
    X6Glue.ElkiesCharts X t                                                                               -- s² = −t, r² = 3(t − 1)

theorem elkiesX6StarPrinted_of_functionField (h : ElkiesX6StarFunctionField) : ElkiesX6Star.ElkiesX6StarPrinted
```

(Exact text in the file; binders abbreviated here.) Every object is a genuine definition: Mathlib's
`Scheme.functionField`, `Scheme.Hom.stalkMap`, `stalkSpecializes`, `Subfield.closure`; the kernel's `ToP1`
(a morphism to `P¹` by charts), `X6Props`, `R1fpPropsAb`, `X6Glue.ElkiesCharts`; gt-elkies' `atkinLehnerW` (the
automorphisms of `X₆` acting on moduli as `w_m`, `m = 1, 2, 3, 6`). `ℚ(t)` is `Subfield.closure {t}`: the function
field has characteristic `0`, so this subfield contains the prime field `ℚ`.

## 3. The proof (all VERIFIED, compiled)

0. **`X₆` is integral** (`elkiesRing_isDomain`, `isIntegral_open`, `irreducibleSpace_of_charts`,
   `isReduced_of_charts`, `isIntegral_of_charts`, `genericPoint_mem_of_charts`). Elkies' ring is a domain (it embeds
   in `AdjoinRoot (r² + 3(s² + 1))` over `ℚ[s]`, a monic quadratic with no root, hence prime in the UFD `ℚ[s][r]`). So
   `t.U` and `t.V` are integral affine opens; they meet, so `X₆ = t.U ∪ t.V ⊆ closure t.U` is irreducible; its stalks
   are stalks of `t.U` or `t.V`, so it is reduced.

Fix the witness and Elkies' charts `φU : ℚ[t,s,r]/(s² + t, r² − 3(t − 1)) ≅ Γ(t.U)`, `φV` likewise on `t.V`, glued by
`s·a = 1`, `r·a = b`. Write `τ, S, R ∈ ℚ(X₆)` for the germs of `t, s, r`.

1. **Germ calculus** (`ffPullback_germ`, `res_eq_of_germ_eq`, `ev_comp_hom`, `ev_eq_of_germ_eq`,
   `ev_mul_eq_one_of_germ`). `g^*` of a germ is the germ of `g.app`; two sections with equal germs at the generic
   point agree on the intersection of their opens (`germ_injective_of_isIntegral`), hence have equal values at every
   `ℚ̄`-point there; the value of a section at `y ≫ g` is the value of `g.app` of it at `y`.
2. **`W` acts on Elkies' coordinates by signs** (`memU_comp_iff`, `conicMapL_comp_of_signs`). Every `g ∈ W` fixes
   `τ`, because `τ ∈ ℚ(t) = ℚ(X₆)^W`. From `g^*τ = τ` and `τ·(1/τ) = 1`, `g` maps `{t ≠ ∞}` to itself on `ℚ̄`-points:
   otherwise a value of `g.app(1/t)·t` would be `0·(…) = 1`. From `S² = −τ` and `R² = 3(τ − 1)`, `g^*S = cS` and
   `g^*R = dR` with `c, d = ±1`. Through step 1, `g` acts on x6-glue's conic model `conicMapL : X₆(ℚ̄) ≃ C(ℚ̄)` as
   `(s, r) ↦ (cs, dr)` on `t ≠ ∞` and as `b ↦ cdb` at `t = ∞` (since `b = r/s`).
3. **`ℚ(X₆)^W = ℚ(t)` forces all sign changes** (`thetaOf`, `not_mem_closure`, `exists_neg`). The ring automorphisms
   `s ↦ −s` and `r ↦ −r` of Elkies' ring extend to automorphisms of `ℚ(X₆) = Frac Γ(t.U)`
   (`functionField_isFractionRing_of_isAffineOpen`, `IsFractionRing.ringEquivOfRingEquiv`); they fix `τ`, hence fix
   `ℚ(t)` pointwise. Since `S, R, SR ≠ 0` (values at explicit `ℚ̄`-points of the charts) and `2 ≠ 0`, none of
   `S, R, SR` lies in `ℚ(t)`. So some `g₁ ∈ W` negates `S`, some `g₂` negates `R`, and some `g₃` negates `SR`.
4. **The orbit relation is transitive** (`orbit_trans`). This uses gt-elkies' proved moduli step `orbit_iff_twist`
   and the composition of twists (`twistIso`, `twistComp`: `(ι ∘ α) ∘ β = ι ∘ (β.trans α)`).
5. **Fibres = orbits** (`all_signs`, `signAct_of_val`, `val_eq_of_signAct`, `fibre_of_ff`). The sign pairs realized
   by the orbit relation are closed under products (step 4 and `conicMapL` bijective), and `g₁, g₂, g₃` generate
   `{±1}²`. On the conic model, `t = −s²` on `t ≠ ∞` and `t = ∞` at the two points `b² = −3`. So two `ℚ̄`-points have the same
   `t`-value iff they differ by a sign change `(c, d)`, iff they are in one `W`-orbit.

`elkiesX6StarPrinted_of_functionField` keeps the witness, `R1fpPropsAb`, `X6Props`, the CM clause and the charts,
and fills the fibre clause with step 5.

## 4. Leaf and glue table

| statement | kind | source | rating |
|---|---|---|---|
| `ElkiesX6StarFunctionField` | published leaf, on the canonical witness | Elkies 1998 (ANTS-III, LNCS 1423) §3 (section, display and `0/∞` orientation UNVERIFIED) | **printed form**: see below |
| `ffPullback`, `fixedByW` | definitions (Mathlib objects) | — | — |
| `elkiesX6StarPrinted_of_functionField` and the lemmas of §3 | glue, proved | chain: `orbit_iff_twist`, `conicMapL` (x6-glue) | proved |

**Rating of the new leaf: printed form**, for these reasons. SPECULATIVE judgement; not yet checked against the paper.
* Elkies' sentence is "`t` is a coordinate on `X*(6) = X(6)/W`", and he gives `X(6)` by its function field over
  `ℚ(t)`. The leaf's first clause is that sentence in function fields: the function field of `X₆/W` is
  `ℚ(X₆)^W`, which is the definition of the quotient's function field (STANDARD: Serre, *Groupes algébriques et
  corps de classes* III §12; Mumford, *Abelian varieties* §7; locators UNVERIFIED). "`t` is a coordinate on the
  genus-0 curve" is `ℚ(X*(6)) = ℚ(t)`. Unlike the old field, no statement about `ℚ̄`-points or fibres is assumed;
  that is now proved (§3).
* "`X₆` integral" and "`t` regular at the generic point" are presupposed by the sentence: `X(6)` is a curve, and `t`
  is a rational function on it. The leaf states the clause **under** these two hypotheses (`∀`), so it asserts nothing
  beyond them. Both are **proved** from the charts (`isIntegral_of_charts`, `genericPoint_mem_of_charts`):
  `ℚ[t, s, r]/(s² + t, r² − 3(t − 1)) ≅ ℚ[s][r]/(r² + 3(s² + 1))` is a domain, since a root `b ∈ ℚ[s]` would have
  leading coefficient with `lc(b)² = −3`; and `t.U ∩ t.V` contains the `ℚ̄`-point `s = 1`, `r = √−6`.
* The CM clause and the charts are `ElkiesX6StarPrinted`'s verbatim (x6-glue: the charts are the smooth model of
  Elkies' function field `ℚ(t)(√−t, √(3(t − 1)))`).
* Remaining modelling choice, the same as gt-elkies': Elkies' `W` is generated by the normalizer of `𝒪` acting on
  the Shimura curve; the leaf takes gt-elkies' moduli definition `atkinLehnerW` (`w_m` twists the `𝒪`-action by
  `Ad μ_m`), the standard moduli interpretation (Rotger 2004; Baba–Granath 2008 §2; locators UNVERIFIED).

**Not stronger than the old field, and not shown equivalent.** The leaf is used only through
`elkiesX6StarPrinted_of_functionField`. The converse (point form ⇒ function-field form) would need automorphisms of `X₆`
to be determined by their action on `ℚ̄`-points, and `[ℚ(X₆) : ℚ(t)] = 4`. It is not proved and not needed. The leaf
is true for the canonical model if Elkies' theorem is: `W` has exactly four elements, since an automorphism of a reduced
`ℚ`-curve is determined on `ℚ̄`-points and `Ψ` is a bijection.

## 5. What remains, and caveats

* **The `0/∞` orientation and the display** are UNVERIFIED readings of Elkies, as before (gt-elkies §5).
* The contribution imports `ZInQKernel.Contrib.OneProof.ElkiesX6Star` (gt-elkies' module, where
  `ElkiesX6StarPrinted`, `atkinLehnerW` and `orbit_iff_twist` live). It does not import `ZInQKernel.OneProof.Main`.

## 6. Files and checks

* `ZInQKernel/Contrib/OneProof/ElkiesX6StarPrinted.lean`: the contribution (≈ 46 KB, 76 declarations). It reuses
  x6-glue's `conicMapL`, `conicMapL_injective/surjective`, `val_of_inl/inr`, `ev` and gt-elkies'
  `orbit_iff_twist`, and copies none of them.
* `scratch/elkies-coord/ElkiesCoord.lean`: working copy (identical to the contribution).
* `scratch/elkies-coord/Discharges.lean`, `discharges.txt`: the `#discharges` check.
* `scratch/elkies-coord/autofold.json`, `autofold-dryrun.txt`, `FoldDryRun.lean`: the fold spec, its dry-run, and
  the generated module (first line stripped) with `#print axioms` on the new top theorem.
* `scratch/elkies-coord/log.md`: results log.

## 7. For the integrator

* Fold: `python3 scripts/one_proof/autofold.py scratch/elkies-coord/autofold.json` (the dry-run output is in
  `scratch/elkies-coord/autofold-dryrun.txt`). It removes `elkiesX6StarPrinted` from the research bundle and adds
  `elkiesX6StarFunctionField` (kind `published`, flag `locator UNVERIFIED (section, display, 0/infinity orientation)`).
* Proposed `docs/research/locators.md` row (not added here, since that file belongs to other tasks):
  `ElkiesX6StarFunctionField` | Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998), §3 (`X*(6)`):
  "`t` is a coordinate on `X*(6) = X(6)/W`", the CM values `t = 0, 1, ∞` at `D = −24, −4, −3`, and
  `ℚ(X(6)) = ℚ(t)(√−t, √(3(t − 1)))` | section, display and the `0/∞` orientation UNVERIFIED (not read; recalled) |
  statement check to do: confirm the coordinate sentence and the function-field display.
* The leaf supersedes gt-elkies' `ElkiesX6StarPrinted` as the published input. `ElkiesX6StarPrinted` stays a proved
  consequence, as `ElkiesEquationsX6Ab` did after gt-elkies.
