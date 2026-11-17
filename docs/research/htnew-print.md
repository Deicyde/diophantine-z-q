# htnew-print: `eigenformHTNew` from a reading-robust printed leaf

Task htnew-print, branch `wip/htnew-print`, base c0f3d085 (main; `git merge origin/main`: already up to date),
2026-11-16/17. Lean: `ZInQKernel/Contrib/OneProof/EigenformHTPrinted.lean` (same text in
`scratch/htnew-print/EigenformHTPrinted.lean`), with the helper `ZInQKernel/Contrib/OneProof/NewformDict.lean`
(newform-dict's file, byte-identical copy of `origin/wip/newform-dict:ZInQKernel/Contrib/OneProof/NewformDict.lean`,
which is not on main). Log: `scratch/htnew-print/log.md`. Nothing else under `ZInQKernel/` was edited. This is model
work with no human review.

Marks: **VERIFIED** = compiled, or read in a file on this host. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number, locator or printed wording recalled without a
source (there is no network on this host).

## 0. Verdict

**`eigenformHTNew` (consequence, GLUE) is discharged by one new leaf, `EigenformHTPrinted.ModularHTPrinted`, stated
so that no printed wording of the theorem is weaker than it; every step between the leaf and the field is proved in
Lean. Target −1 GLUE: met if the leaf is accepted as printed form (flag `unread`), as the contributor kit rules
for a new printed leaf.** No statement was changed. The field is not false, vacuous or inert (ht-bypass §4).

1. **Kato's statement cannot be restated verbatim (VERIFIED from the definitions, as ht-exists found).** Kato
   (Astérisque 295, 2004, §§9.2-9.4, (9.2.2), pp. 187-188, read by the locator audit) proves de Rham-ness for
   `V_{F_λ}(f)`, a Hecke quotient of étale cohomology of `Y₁(N)` with coefficients `Sym^{k−2}` of the universal
   elliptic curve. Mathlib has neither étale cohomology with coefficients nor the universal elliptic curve, so no
   Lean statement can name `V_{F_λ}(f)`. Every Lean form of the theorem is therefore an **existence form**
   ("there is a `ρ` with these Frobenius traces and these Hodge–Tate weights"), which is how the theorem is printed
   in its existence-form statements (surveys; §3). ht-exists's leaf was such a form but was flagged *pending
   reading* on three points. This task removes all three by changing the statement, not the reading:
   - **normalization / sign convention:** the leaf's conclusion is the disjunction of the two self-consistent
     normalizations (arithmetic Frobenius trace `a_p` with weights `{0, 1 − k}`, or geometric Frobenius trace
     `a_p` with weights `{0, k − 1}`, in the kernel's convention). Any correct print, whatever its Frobenius and
     weight conventions, is one disjunct after translating its convention to the kernel's `htMult`;
   - **semisimplicity:** dropped from the leaf. New Lean (§6 of the file): *the semisimplification of a
     2-dimensional Hodge–Tate representation is Hodge–Tate with the same weights* (`exists_ss`);
   - **Frobenius clause:** only the trace, in the universal form "if `ιC α = a_p` then `tr ρ(Frob) = ιL α`" (no
     algebraicity of `a_p` asserted; the discharge gets it from the LEAF field `eigenformCoeffFieldFinite`); the
     "characteristic polynomial" wording gives it (`trace_of_charpoly`).
   The newform is Tau Ceti's printed `HeckeRing.GL2.Newform N k` (newform-dict's dictionary).
2. **Discharge (VERIFIED, compiled, standard axioms):**
   `eigenformHTNew_of_printed : ModularHTPrinted → DSCoeffExt.EigenformCoeffFieldFinite → EigenformHTNew`.
3. **Converse (VERIFIED):** `printed_of_eigenformHTNew : DSThm965Printed → EigenformCoeffFieldFinite →
   DSThm966Printed → EigenformHTNew → ModularHTPrinted` and `printed_iff`. All three inputs are LEAF fields of
   `OpenResearchLeaves31`, so the new leaf is no stronger than the field it replaces.
4. **`tateTwistInvariants` and `axSenTate`** (inputs of ht-exists's discharge) are already proved on main
   (`ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof`, `axSenTate_proof`, VERIFIED read); the new file uses them,
   so the discharge has no Tate inputs.
5. **Count.** If the leaf enters as `published` with flag `unread` (as the contributor kit prescribes for a new
   printed leaf, CONTRIBUTING.md l.38-41), the strict count goes from 11 published / 18 glue to 12 / 17 (§4,
   dry run). If a rater rules that only Kato's `V_{F_λ}(f)` statement is "the print", the leaf is a consequence
   of it by ∃-introduction (witness `V_{F_λ}(f) ⊗ ℚ̄_ℓ`) and the fold is count-neutral; §3 gives the case for the
   printed-form rating.

## 1. The statements

```lean
-- the field (TailS.lean l.1275), unchanged
def ZInQ.Contrib.HodgeSplit.EigenformHTNew : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

-- the new leaf
def EigenformHTPrinted.ModularHTPrinted : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) [NeZero N] (k : ℤ) (f : HeckeRing.GL2.Newform N k), 2 ≤ k →
    ∃ ρ : GaloisRep ℓ 2,
      ((∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧
          ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
            ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
              (ρ.mat σ).trace = ιL α) ∧
        ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}) ∨
      ((∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧
          ∀ α : Qbar, ιC α = coeff (f.toCuspForm : CF N k) p →
            ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
              (ρ.mat σ⁻¹).trace = ιL α) ∧
        ρ.HasHTWeightsAtSelf ℓ {0, k - 1})
```

All objects are genuine definitions: Tau Ceti's `Newform` (vendored; `cuspFormsNew` is the Petersson complement of
the old space), pkg-I4's `GaloisRep`, `UnramifiedAt`, `IsArithFrob`, `coeff`, and `HasHTWeightsAtSelf` over
`htMult` (Tate's `dim (ℂ_ℓ(w) ⊗ V)^{G_{ℚ_ℓ}}`). No structure was invented. The file sets `autoImplicit false`.

**Why the disjunction is exactly the reading robustness (SPECULATIVE judgement with the computation).** In the
kernel's convention (weight `w` iff `(ℂ_ℓ(w) ⊗ V)^G ≠ 0`, i.e. iff `gr^w D_dR(V) ≠ 0`; the cyclotomic character has
weight `−1`, VERIFIED from the docstring and `htSpace_cycRep_eq_bot` in I4Layer.lean), `V_ℓ(E)` of an elliptic curve
(arithmetic Frobenius char. poly. `x² − a_p x + p`) has weights `{0, −1}` and `H¹ = V_ℓ(E)^∨` (geometric Frobenius
char. poly. `x² − a_p x + p`) has `{0, 1}` (STANDARD). For weight `k`, the two normalizations of `ρ_f` have weights
`{0, 1 − k}` (arithmetic) and `{0, k − 1}` (geometric). The two other combinations are false. A print that uses the
opposite sign convention (cyclotomic weight `+1`) says `{0, k − 1}` for the arithmetic normalization, which
translates to the kernel's `{0, 1 − k}`: the first disjunct. So a correct print lands in a disjunct under every
convention.

## 2. The Lean (all VERIFIED: compiled, `[propext, Classical.choice, Quot.sound]`)

| section | theorem | statement |
|---|---|---|
| §1-§5 | `dualGR`, `HTDual`, `htDual_proof` | ht-exists's (c-to-printed2's) contragredient and `HTDual` (weights of `ρ^∨` are `−S`), verbatim |
| §6 | `htDual` | `HTDual`, unconditional (Tate's theorems from main) |
| §6a | `isSemisimple_of_diag` | a diagonal `ρ` is semisimple |
| §6a | `exists_invariant_line`, `exists_gl_col` | a non-semisimple 2-dimensional `ρ` has an invariant line; a basis change makes it upper triangular |
| §6a | `conjGR`, `isConj_conjGR`, `diagGR` | `P⁻¹ρP`; the diagonal part of an upper triangular `ρ` as a `GaloisRep` |
| §6b | `sum_finrank_Ysp_le` | Tate–Sen bound `Σ_{j∈J} dim_K Y_j(ρ) ≤ n` (from the kernel's `Ysp_linearIndependent`) |
| §6b | `finrank_Ysp_le_diag` | `dim_E Y_i(ρ) ≤ dim_E Y_i(ρ^{ss})` for `ρ` upper triangular (rank–nullity for the first coordinate) |
| §6c | `ht_diag` | the diagonal part of an upper triangular `ρ` with weights `S` (`|S| = 2`) has weights `S` (the bound forces equality termwise) |
| §6c | `exists_ss` | **semisimplification**: every 2-dimensional `ρ` with weights `S` has a semisimple `ρ'` with the same traces, unramified where `ρ` is, with weights `S` |
| §7 | `ModularHTPrinted` | the new leaf |
| §7 | `trace_of_charpoly` | `charpoly M = x² − a x + b ⇒ tr M = a` (the "characteristic polynomial" wording gives the leaf's clause) |
| §7 | `dual_arith_of_geom` | geometric normalization of `ρ` ⇒ arithmetic normalization of `ρ^∨` |
| §7 | `attached_of_univ`, `attached_of_trace`, `exists_alg_coeff` | the leaf's clause + algebraicity of `a_p` (LEAF field `eigenformCoeffFieldFinite`) ⇒ `AttachedTo`; same traces ⇒ attached |
| §7 | `ht_of_attached` | ht-exists's transport (Chebotarev + Brauer–Nesbitt `attachedConj_proof`, `htConj_proof`), verbatim |
| §7 | `eigenformHTNew_of_printed` | **the discharge** |
| §7 | `printed_of_eigenformHTNew`, `printed_iff` | converse over `dsThm965Printed`, `eigenformCoeffFieldFinite`, `dsThm966Printed` |

Proof of the discharge: newform-dict turns `IsNewform f χ` into a Tau Ceti newform `g` with `g.toCuspForm = f`;
the leaf gives `ρ₀`; in the geometric case replace it by `ρ₀^∨` (`dual_arith_of_geom`, `HTDual`); the semisimplification
`ρ'` of `ρ₀` keeps the weights `{0, 1 − k}` and the traces (`exists_ss`); `ρ'` and the given semisimple attached `ρ`
are conjugate (`attachedConj_proof`), so `ρ` has weights `{0, 1 − k}` (`htConj_proof`).

Proof of `exists_ss` (the new mathematics, elementary): if `ρ` is not semisimple, an invariant subspace without
invariant complement is a line `ℚ̄_ℓ w`; conjugating by a matrix with first column `w` makes `ρ` upper triangular
`[[χ₁, *], [0, χ₂]]`; `ρ' = diag(χ₁, χ₂)` is semisimple with the same traces. On a finite Galois `E/ℚ_ℓ` carrying
both, the Tate–Sen spaces `Y_i` (the kernel's `Ysp`, `htMult = dim_E Y_{−w}`, `htMult_eq_finrank_Ysp`) satisfy
`dim Y_i(ρ) ≤ dim Y_i(ρ')` (project to the first coordinate: the image lies in `Y_i(χ₁)`, the kernel in `Y_i(χ₂)`),
and `Σ_{i ∈ J} dim Y_i(ρ') ≤ 2` for every finite `J` (Tate–Sen independence). Since `Σ_i dim Y_i(ρ) = 2`, equality
holds termwise.

## 3. Rating of the new leaf

**Proposed: kind `published`, flag `unread: new printed leaf ...; locator UNVERIFIED` (counts LEAF).** Reasons:

- *Printed form.* The theorem is printed in existence form ("for a newform `f` of weight `k ≥ 2` and `ι`, there is
  a continuous `ρ_{f,ι} : G_ℚ → GL₂(ℚ̄_ℓ)`, unramified outside `Nℓ`, with `tr ρ_{f,ι}(Frob_p) = ι⁻¹(a_p)`, and
  `ρ_{f,ι}|_{G_{ℚ_ℓ}}` is de Rham with Hodge–Tate weights `0, k − 1`") in survey statements that collect Deligne,
  Faltings, Saito and Kato, e.g. Taylor, *Galois representations*, Ann. Fac. Sci. Toulouse Math. (6) 13 (2004),
  and Gee, *Modularity lifting theorems*, Essent. Number Theory 1 (2022) §2. **These two locators, theorem numbers
  and wordings are recalled, not read: UNVERIFIED.** A reader should check one of them (or any refereed source
  printing the existence form at every level).
- *Never stronger than any reading of such a print.* Each clause is weaker than or equal to its printed
  counterpart under every reading: the normalization and the sign convention by or-introduction (§1); the trace
  clause is weaker than "char. poly." or "trace and determinant" (`trace_of_charpoly`) and asserts nothing when
  `a_p` is not in `ιC(ℚ̄)`; semisimplicity/irreducibility is not asserted; "de Rham with HT weights" gives the
  HT weights; a print with one isomorphism `ι : ℚ̄_ℓ ≅ ℂ` gives every pair `(ιC, ιL)` (extend `ιC ∘ ιL⁻¹` to an
  isomorphism `ℚ̄_ℓ ≅ ℂ`, STANDARD); a print over `K_{f,λ}` gives it by extension of scalars.
- *What remains for a reader (the `unread` flag):* that a refereed print states the existence form **at every
  level** (`ℓ ∣ N` included; Faltings and Scholl cover `ℓ ∤ N` only; the all-level input is Saito 1997 / Kato 2004,
  whose (9.2.2) the locator audit read).
- *The other reading.* If a rater holds that the only print is Kato's (or Saito's) statement about the
  étale-cohomological `V_{F_λ}(f)`, the leaf is that statement's consequence with witness `V_{F_λ}(f) ⊗ ℚ̄_ℓ`:
  kind `consequence`, GLUE, count-neutral (as ht-exists). The reading points that made ht-exists *pending
  reading* are gone either way.

**Proposed `locators.md` row** (not added: shared file outside this task's scratch):
`R13 (printed existence form, htnew-print) | Taylor 2004 (Ann. Fac. Sci. Toulouse) / Gee 2022 (ENT) §2; content
Deligne 1971, Faltings 1987, Saito 1997, Kato 2004 (9.2.2) pp. 187-188 | — | (9.2.2) read; surveys UNVERIFIED |
there is a continuous rho attached to a newform (either Frobenius normalization) with HT weights {0, k-1} at l,
every level; check one survey's statement covers l | N`.

## 4. Compile log, `#discharges`, dry-run fold (VERIFIED, 2026-11-16, Lean 4.35.0 / Mathlib v4.35.0)

One Lean process at a time; load ≤ 20 throughout.

| what | command | outcome |
|---|---|---|
| contribution (scratch copy) | `lake env lean scratch/htnew-print/EigenformHTPrinted.lean` | success, about 80 s, warnings only (deprecations, unused simp args) |
| axioms | `lake env lean scratch/htnew-print/Axioms.lean` | `eigenformHTNew_of_printed`, `printed_of_eigenformHTNew`, `exists_ss`, `trace_of_charpoly`: `[propext, Classical.choice, Quot.sound]` (`axioms.txt`) |
| discharge build | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.EigenformHTPrinted` | success, 14229 jobs, 15 min; `frozenTarget` standard axioms |
| `#discharges` | `lake env lean scratch/htnew-print/Discharges.lean` | output `Discharges-output.txt` (below) |
| fold | `python3 scripts/one_proof/autofold.py scratch/htnew-print/autofold.json --dry-run`, line 1 stripped → `FoldDryRun.lean`, `lake env lean` | `strict count: 11/18 on 29 -> 12/17 on 29; strictest 11/18 -> 12/17`; `sixContactMin_of_open49` compiles, standard axioms |

```
DISCHARGES [OpenResearchLeaves31.eigenformHTNew] by EigenformHTPrinted.eigenformHTNew_of_printed
  still assumes: [EigenformHTPrinted.ModularHTPrinted, DSCoeffExt.EigenformCoeffFieldFinite]
  axioms: [propext, Classical.choice, Quot.sound]
...
#discharges: 35 open hypotheses, 9933 theorems checked, 37 discharge one
```

`DSCoeffExt.EigenformCoeffFieldFinite` is an open LEAF field of `OpenResearchLeaves31` that stays in the new
bundle (the fold passes `{n}.eigenformCoeffFieldFinite`). The other 36 entries come from contributions already
in the tree.

**Autofold spec** (`scratch/htnew-print/autofold.json`): discharges `eigenformHTNew` with proof
`_root_.EigenformHTPrinted.eigenformHTNew_of_printed {n}.modularHTPrinted {n}.eigenformCoeffFieldFinite`; the new
leaf is `modularHTPrinted : _root_.EigenformHTPrinted.ModularHTPrinted`, kind `published`, with flag `unread: new
printed leaf (...); locator UNVERIFIED` and the source as in §3. The fold itself (integrator: autofold without
`--dry-run`, the build, the hash guard, OpenStatements, render_open) is not done here.

## 5. The single consumer

ht-bypass: the field is used once, at `ℓ = 5`, to exclude eigenforms of weight `k ≥ 3` (`G12Weight`). Autofold
needs a proof of the field's exact type, so the leaf is stated for all `ℓ` and `k ≥ 2` (the print's generality);
the instance the route uses (`ℓ = 5`, `k ≥ 3`) is a direct instance of it. A weaker-leaf bypass fold (ht-bypass
§5, `afterG7_of3Weak`) would not change the count and is not proposed.

## 6. Files

- `ZInQKernel/Contrib/OneProof/EigenformHTPrinted.lean`: the contribution (imports `NewformDict`, `DSCoeffExt`,
  `TateTwistInvariants`, `AxSenTate`; not `OneProof.Main`). No `#eval`, `run_cmd`, `initialize`, `syntax`,
  `notation`, macro, elaborator, `axiom` or `sorry` (VERIFIED by grep).
- `ZInQKernel/Contrib/OneProof/NewformDict.lean`: newform-dict's file, byte-identical (a later merge of
  `wip/newform-dict` adds the same file, so it merges cleanly).
- `scratch/htnew-print/`: `EigenformHTPrinted.lean` (copy), `Axioms.lean` + `axioms.txt`, `Discharges.lean` +
  output, `autofold.json`, dry-run module and output, `ht-exists-copy.lean` (reference copy of ht-exists's file),
  `log.md`.
