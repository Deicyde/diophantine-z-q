# ht-exists: `eigenformHTNew` from Kato's theorem in its existence form

Task ht-exists, branch `wip/ht-exists`, base 16db7d60 (wip/ht-bypass on leaf-fold22; `frozenTarget` over
`OpenResearchLeaves21`), 2026-11-15. Lean: `ZInQKernel/Contrib/OneProof/EigenformHTExists.lean` (same text in
`scratch/ht-exists/EigenformHTExists.lean`). Log: `scratch/ht-exists/log.md`. Nothing else under `ZInQKernel/` was
edited. This is model work with no human review.

Marks: **VERIFIED** = compiled, or read in a file on this host. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number, locator or printed wording recalled without a
source (there is no network on this host).

## 0. Verdict

**The field `eigenformHTNew` is discharged by a new leaf in existence form, autofold-compatible, and the leaf is
equivalent to the field over existing LEAF fields.** No statement was changed. The field is not false, vacuous or
inert (ht-bypass §4 and §5 below).

1. **New leaf `EigenformHTExists.KatoHTExists`** (§1): for each newform `f` of weight `k ≥ 2`, level `N`, every `ℓ`
   and embeddings `ιC`, `ιL`, **there is** a semisimple continuous `ρ : G_ℚ → GL₂(ℚ̄_ℓ)`, unramified outside `Nℓ`,
   whose **geometric** Frobenius at `p ∤ Nℓ` has trace `ιL ιC⁻¹ a_p(f)`, with Hodge–Tate weights `{0, k − 1}` at
   `ℓ`. This is how Kato (and Faltings, Scholl, Saito) state the result: for the representation `V_{F_λ}(f)` they
   construct, in the cohomological normalization. It is the statement c-to-printed2 called `KatoRealizationCohSS`
   (scratch only until now).
2. **Discharge (VERIFIED, compiled, standard axioms):**
   `eigenformHTNew_of_katoHTExists : KatoHTExists → TateTwistInvariants → AxSenTate → EigenformHTNew`.
   The last two are LEAF fields of `OpenAddedLeaves17` (Tate 1967 §3.3 Thms 1-2). Proof: dualize the witness
   (contragredient semisimple, attached in the trace form, weights `{0, 1 − k}` by `HTDual`, which is proved from
   Tate's two theorems), then transport to every semisimple attached `ρ`: Chebotarev + Brauer–Nesbitt (the kernel's
   `attachedConj_proof`, from T18 `ZInQ.Contrib.frobeniusDense` and T19) give a conjugating matrix, and the kernel's
   `htConj_proof` moves the Hodge–Tate weights across it. This is the same pattern as r17-bypass's
   `iso_of_attached` + `condExp_eq_of_intertwine`, with the kernel's already-proved conjugation lemmas in place of
   the new ones.
3. **Converse (VERIFIED):** `katoHTExists_of_eigenformHTNew : DSThm965 → DSThm966 → TateTwistInvariants →
   AxSenTate → EigenformHTNew → KatoHTExists`, and `katoHTExists_iff`. All four inputs are LEAF fields of the
   current bundles, so the new leaf is no stronger than the field it replaces.
4. **The instance the route uses (ht-bypass: `ℓ = 5`, `k ≥ 3`):** the restricted leaf `KatoHTExists5Ge3`,
   `eigenformHTNew5Ge3_of_katoHTExists5Ge3` (ht-bypass's weakest form `EigenformHTNew5Ge3`), its converse, the
   consumer input `eigenformHT5Ge3Chain_of_katoHTExists5Ge3`, and `HDec.HSyn.G0AssembleMod.afterG7_of3Kato5`
   (`AfterG7`, the input of `GluePieces.modularConstituent`, through ht-bypass's `afterG7_of3Weak`). All VERIFIED.
   The autofold discharge uses the unrestricted leaf, because autofold needs a proof of the field's exact type.
5. **Count: neutral now, −1 strict GLUE once a reading clears the flag.** The leaf goes in as kind `published` with
   flag `pending reading` (§3), so it counts GLUE: the dry run gives `46/10 on 56 -> 46/10 on 56; strictest 45/11 ->
   45/11` (VERIFIED). When a statement check confirms the three points of §3, the flag is removed and the strict
   GLUE count drops by one.

## 1. The statements

```lean
-- the field (TailS.lean l.1275), unchanged
def ZInQ.Contrib.HodgeSplit.EigenformHTNew : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k) (ρ : GaloisRep ℓ 2),
    0 < N → 2 ≤ k → IsNewform f χ → ρ.IsSemisimple → ρ.AttachedTo ιC ιL f →
    ρ.HasHTWeightsAtSelf ℓ {0, 1 - k}

-- the new leaf
def EigenformHTExists.KatoHTExists : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
    (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (f : CF N k),
    0 < N → 2 ≤ k → IsNewform f χ →
    ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N * ℓ → ρ.UnramifiedAt p ∧ ∃ α : Qbar, ιC α = coeff f p ∧
        ∀ (v : ValuationSubring Qbar) (σ : GQ), LiesOver v p → IsArithFrob σ v p →
          (ρ.mat σ⁻¹).trace = ιL α) ∧
      ρ.HasHTWeightsAtSelf ℓ {0, k - 1}

-- the route's instance
def EigenformHTExists.KatoHTExists5Ge3 : Prop := -- the same at ℓ = 5 and 3 ≤ k
```

All objects are the kernel's genuine definitions (pkg-I4 `GaloisRep`, `IsNewform`, `coeff`, `IsArithFrob`,
`UnramifiedAt`, and `HasHTWeightsAtSelf` over `htMult`, Tate's `dim (ℂ_ℓ(w) ⊗ V)^{G}`). No structure was invented.
The file sets `autoImplicit false`, so no identifier in any statement is auto-bound (VERIFIED by compiling).

**Convention check (VERIFIED from the definition, with STANDARD `gr^i B_dR = ℂ_ℓ(i)`).** `htMult ρ w =
dim (ℂ_ℓ(w) ⊗ V)^G` (LPrefix.lean l.1803; `htSpace` at `−w` on `V^∨`), so weight `w` occurs iff `gr^w D_dR(V) ≠ 0`
and `ℚ_ℓ(1)` has weight `−1`. `H¹` of an elliptic curve has filtration jumps `0, 1`, so weights `{0, 1}`; Kato's
`V_{F_λ}(f)` with jumps `0, k − 1` has weights `{0, k − 1}`, as in the leaf.

## 2. The Lean (all VERIFIED: compiled, `[propext, Classical.choice, Quot.sound]`)

| theorem | statement |
|---|---|
| `htDual_proof` | `TateTwistInvariants → AxSenTate → HTDual` (c-to-printed2, verbatim; `synthInstance.maxHeartbeats 400000` needed under this import) |
| `dualGR_isSemisimple` | contragredient of a semisimple `ρ` is semisimple (c-to-printed2, verbatim) |
| `dual_of_coh`, `coh_of_dual` | the duality step in both directions: cohomological witness ↔ trace-form `AttachedTo`, weights `{0, k−1}` ↔ `{0, 1−k}` |
| `ht_of_attached` | transport: one semisimple attached `ρ₀` with weights `S` ⇒ every semisimple attached `ρ` has weights `S` (`attachedConj_proof`, `htConj_proof`) |
| `eigenformHTNew_of_katoHTExists` | **the discharge** |
| `katoHTExists_of_eigenformHTNew`, `katoHTExists_iff` | converse, over `dsThm965`, `dsThm966`, `tateTwistInvariants`, `axSenTate` |
| `katoHTExists5Ge3_of_katoHTExists` | restriction |
| `eigenformHTNew5Ge3_of_katoHTExists5Ge3`, `katoHTExists5Ge3_of_eigenformHTNew5Ge3` | ht-bypass's weak form from / to the restricted leaf |
| `eigenformHT5Ge3Chain_of_katoHTExists5Ge3` | the `r13w` input of `afterG7_of3Weak` |
| `HDec.HSyn.G0AssembleMod.afterG7_of3Kato5` | `AfterG7` from the restricted leaf (consumer chain) |

The file imports `ZInQKernel.Contrib.OneProof.EigenformHTWeak` (ht-bypass, in this base; it imports
`OneProof.H.TailX`), not `OneProof.Main`. It has no `#eval`, `run_cmd`, `initialize`, `syntax`, `notation`, macro,
elaborator, `axiom` or `sorry` (VERIFIED by grep). Size 37 KB.

## 3. Rating of the new leaf

**Not printed form verbatim; a consequence of the print with one existential. Proposed kind `published`, flag
`pending reading`.** Reason: the printed theorem is about Kato's `V_{F_λ}(f)`, a Hecke quotient of the étale
cohomology of the modular curve with coefficients `Sym^{k−2}` of the universal elliptic curve's Tate module. Mathlib
has no such object (no étale cohomology with coefficients, no universal elliptic curve over `Y₁(N)`), so the leaf
replaces it by "there is a `ρ`" with the properties that pin `V_{F_λ}(f)` down up to isomorphism (Frobenius traces
and semisimplicity; the Brauer–Nesbitt transport is proved, §2). The witness is `V_{F_λ}(f) ⊗_{F_λ, ιL ιC⁻¹} ℚ̄_ℓ`.
The leaf is not stronger than the print: it asserts the conclusion for one representation, and asks for
semisimplicity where the print gives irreducibility. It is the r17-bypass rating, for the same reason.

**What a reading must settle (exact locators; the locator audit's row R13 in `docs/research/locators.md` read
(9.2.2) and lists the other pages):**

1. Kato, *p-adic Hodge theory and values of zeta functions of modular forms*, Astérisque 295 (2004), §§9.2-9.4,
   (9.2.2), pp. 187-188 (PDF pp. 72-73): `V_{F_λ}(f)` is de Rham at `ℓ` for every level, `ℓ ∣ N` included
   (read by the audit).
2. Same, §§11.3-11.4, pp. 205-207: the Hodge filtration of `D_dR(V_{F_λ}(f))` has jumps exactly `0` and `k − 1`
   (and not `1 − k, 0`, which would mean Kato's `V` is the Tate-normalized one; then the witness is `V^∨` and the
   leaf is still a consequence, with the proved `HTDual`). Content attribution UNVERIFIED.
3. Same, §6.3 and §8.3, pp. 161-162 and 181-182: the Frobenius normalization of `V_{F_λ}(f)`: geometric Frobenius at
   `p ∤ Nℓ` has trace `a_p(f)` (not `ā_p(f)`; if `ā_p`, the witness is `V_{F_λ}(f^*)` for the conjugate newform and
   the leaf is still a consequence). Content attribution UNVERIFIED.
4. Semisimplicity of the witness: Ribet, *Galois representations attached to eigenforms with Nebentypus* (LNM 601,
   1977) for `k = 2`, and Ribet, *On ℓ-adic representations attached to modular forms II* (Glasgow Math. J. 27,
   1985) in general (irreducibility; titles and locators UNVERIFIED).

Alternatives for 1-2 (UNVERIFIED): Faltings, Math. Ann. 278 (1987) and Scholl, Invent. Math. 100 (1990)
(`ℓ ∤ N`); Saito, Invent. Math. 129 (1997) (all levels). If a source prints the bundled statement "`ρ_{f,λ}` is
de Rham with Hodge–Tate weights `0, k − 1`" directly, the flag can be cleared on that source alone.

**Proposed `locators.md` row** (not added: another task's file):
`R13 (existence form, ht-exists) | Kato 2004 (9.2.2) pp. 187-188; §§11.3-11.4 pp. 205-207; §§6.3, 8.3 pp. 161-162,
181-182; Ribet 1977/1985 | — | (9.2.2) read; rest UNVERIFIED | there is a semisimple rho attached (geometric Frobenius
trace a_p) with HT weights {0, k-1}; check the filtration jumps and the Frobenius normalization of V_{F_lambda}(f)`.

## 4. Compile log and `#discharges` (VERIFIED, 2026-11-15, Lean 4.35.0 / Mathlib v4.35.0)

Build tree copied from `~/dzq-wt/ht-bypass` (same commit, clean worktree). One Lean process at a time; load ≤ 11.

| what | command | outcome |
|---|---|---|
| contribution | `lake build ZInQKernel.Contrib.OneProof.EigenformHTExists` | first run: synthInstance timeout in `htDual_proof` (instance drift, as c-to-printed2 noted); with the option: success, 18 s, warnings only (deprecated `if_neg`/`if_pos` in the verbatim copy) |
| discharge check | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.EigenformHTExists`, then `lake env lean scratch/ht-exists/Discharges.lean` | success (`scratch/ht-exists/Discharges-output.txt`); 8 `#print axioms` lines standard |
| fold | `python3 scripts/one_proof/autofold.py scratch/ht-exists/autofold.json --dry-run`, line 1 stripped → `scratch/ht-exists/FoldDryRun.lean`, `lake env lean` | `strict count: 46/10 on 56 -> 46/10 on 56; strictest 45/11 -> 45/11`; `sixContactMin_of_open29` compiles, standard axioms |

```
DISCHARGES [OpenResearchLeaves21.eigenformHTNew] by EigenformHTExists.eigenformHTNew_of_katoHTExists
  still assumes: [EigenformHTExists.KatoHTExists,
 ZInQ.Contrib.HodgeSplit.TateTwistInvariants,
 ZInQ.Contrib.HodgeSplit.AxSenTate]
  axioms: [propext, Classical.choice, Quot.sound]
...
#discharges: 63 open hypotheses, 1703 theorems checked, 6 discharge one
```

The other five entries are the contributions already folded, as in the kit's worked example. `TateTwistInvariants`
and `AxSenTate` are listed because `#discharges` lists every hypothesis; both are open LEAF fields of
`OpenAddedLeaves17`, which the fold passes as `{l}.tateTwistInvariants`, `{l}.axSenTate`.

**Autofold spec** (`scratch/ht-exists/autofold.json`): discharges `eigenformHTNew` with proof
`_root_.EigenformHTExists.eigenformHTNew_of_katoHTExists {n}.katoHTExists {l}.tateTwistInvariants {l}.axSenTate`,
new leaf `katoHTExists : _root_.EigenformHTExists.KatoHTExists`, kind `published`, flag `pending reading: …` (the
points of §3), source as in §3. The generated conversion takes the added-leaves bundle as an extra argument
(`openResearchLeaves21_of_OpenResearchLeaves22 (n) (l)`), and the dry-run module compiles.

## 5. Not false, vacuous or inert (SPECULATIVE judgement, from the definitions)

- The leaf's hypotheses are satisfiable (every newform of weight `≥ 2`, STANDARD), and the witness exists by the
  printed theorems (§3), so the existential is not vacuously hard. Its conclusion is the genuine Hodge–Tate
  statement over `htMult`.
- The converse (§2) shows the leaf says no more than the field over four LEAF fields, and the field is used at a
  non-vacuous instance (ht-bypass: `ℓ = 5`, Pan's eigenform, `k ≥ 3` excluded through it).

## 6. What remains

- The reading of §3 (points 2-4) to clear the flag: then `katoHTExists` counts LEAF and the strict GLUE count drops
  by one.
- The fold itself (integrator): `autofold.py scratch/ht-exists/autofold.json`, the build, the hash guard, OpenStatements
  and `render_open.py`. Not done here (this task edits nothing outside `ZInQKernel/Contrib/OneProof/`). The
  contribution depends on ht-bypass's `EigenformHTWeak.lean` (only for §8-§9); both are in this branch.
- Optional bypass fold to the restricted leaf `KatoHTExists5Ge3` via `afterG7_of3Kato5` (smaller open statement,
  same count; needs the G0 term of `TailK.lean` restated, as ht-bypass §5 explains). Not recommended unless a
  reader finds that only `ℓ = 5` or only `k ≥ 3` is printed.

## 7. Files

- `ZInQKernel/Contrib/OneProof/EigenformHTExists.lean`: the contribution.
- `scratch/ht-exists/EigenformHTExists.lean` (copy), `Discharges.lean` + `Discharges-output.txt`, `autofold.json`,
  `autofold-dryrun.txt`, `FoldDryRun.lean` + `FoldDryRun-output.txt`, `log.md`.
