# r16-det: a printed source for the determinant of `ρ_{f,λ}` on `A_f` (Diamond–Shurman Thm 9.6.5 at `k = 2`)

Task r16-det, branch `wip/r16-det`, base `origin/main` 222c98bf, with r16-close (d62e5b85) merged (no
conflicts). Date 2026-11-16/17. New Lean: `ZInQKernel/Contrib/OneProof/R16CoreYDS965.lean`. Scratch:
`scratch/r16-det/` (results log `log.md`). Nothing else under `ZInQKernel/` or `blueprint/` was edited. Model
work, no human review.

Marks: **VERIFIED** = compiled, or read in a source or a file of this tree. **STANDARD** = published, with a
reference. **SPECULATIVE** = a judgement. **UNVERIFIED** = recalled without a source.

## 0. Result

1. **The printed characteristic equation of the Section 9.5 realization is Diamond–Shurman Thm 9.6.5 at
   `k = 2`** (locator VERIFIED by a human reader's print copy: p. 404 of the corrected fourth printing,
   2016, issue #14 comment 7000317188).
   - Thm 9.6.5 covers a normalized eigenform `f ∈ S_k(N, χ)` and `λ ∣ ℓ`. It gives a 2-dimensional
     `ρ_{f,λ} : G_ℚ → GL₂(K_{f,λ})`, unramified at `p ∤ ℓN`, and prints that "the characteristic equation" of
     `ρ_{f,λ}(Frob_𝔭)` is `x² − a_p(f)x + χ(p)p^{k−1} = 0`.
   - **The identification.** In the paragraph after the theorem, DS say that Section 9.5 constructed
     `ρ_{f,λ}` for `k = 2` but did not prove that it is irreducible or that the equation is the characteristic
     equation (paraphrase; one line of print is the most we may quote). So at `k = 2` the theorem is DS's
     statement about **the Section 9.5 representation**, the `λ`-component `e_λ V_ℓ(A_f)` of Exercise
     9.5.2(a). That is exactly aftate-fix2's `V_λ = K_{f,λ} ⊗_{ℚ_ℓ ⊗ K_f} V_ℓ(A_f)`.
     The placement on p. 404 and the wording: HUMAN-READ, zachbaugher, issue #14 comment 7121091136.

   So r16-close's statement check needs one amendment. Thm 9.5.4 prints only "satisfies", but DS print the
   characteristic equation for the same representation two pages later. r16-close's objection that 9.6.5's
   `ρ_{f,λ}` is "an abstract representation, not the realization on `A_f`" is answered by DS's own sentence
   for `k = 2`.

2. **New leaf `AfTateLam.AfCharpolyDS965`** (printed form, LEAF). It is DS Thm 9.6.5 at `k = 2`, over
   `K_{f,λ}`, universally over DS's `A_f`. Its statement is aftate-fix2's `AfTateLam.AfTateDSLambda`
   verbatim (`afCharpolyDS965_iff : AfCharpolyDS965 ↔ AfTateDSLambda := Iff.rfl`). Only the source changes:
   9.6.5 with its `k = 2` identification, instead of 9.5.4.

3. **`AfDetLambda` is a direct consequence** (VERIFIED, compiled):
   `afDetLambda_of_ds965 : MumfordTorsionAlgClosed → AfCharpolyDS965 → AfDetLambda`. The determinant is the
   constant coefficient of a degree-2 characteristic polynomial. Mumford's theorem is used only to make
   `V_ℓ(A)` finite-dimensional, since `AfDetLambda` has no finiteness hypothesis and `LinearMap.det` is 1
   on infinite-dimensional spaces.

4. **Discharge** (VERIFIED, compiled, standard axioms):

   ```lean
   theorem AfTateLam.r16CoreY_of_ds965 (h1 : HeckeJ1DS) (h2 : AfShimura) (h3 : AfCharpolyDS965)
       (hI : X1Igusa.IgusaGL2DS) (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY
   ```

   This is aftate-fix2's `r16CoreY_of_printed` applied to the re-sourced leaf.

5. **Count.** `r16CoreY` (GLUE) leaves. `heckeJ1DS`, `afShimura`, `afCharpolyDS965` and `igusaGL2DS` (all
   published, LEAF) enter. **−1 GLUE**: 11/18 on 29 → 15/17 on 32 (LEAF/GLUE), against r16-close's 15/18 on
   33. Dry run (§3): `strict count: 11/18 on 29 -> 15/17 on 32; strictest 11/18 -> 15/17`, and the generated `sixContactMin_of_open49` compiles with standard axioms.

## 1. What each candidate prints

| candidate | read? | what it prints | usable? |
|---|---|---|---|
| DS Thm 9.5.4 (2016 pp. 401–402) | read (human: issue #14 comment 7121091136) | `ρ_{f,λ}(Frob_𝔭)` "satisfies" `x² − a_p x + χ(p)p = 0` | gives `AfTateDSLambdaSat` only |
| DS Thm 9.6.5 + the paragraph after it (2016 printing p. 404) | **read** (human, issue #14 comments 7000317188, 7121091136: the theorem and the paragraph after it) | "the characteristic equation" `x² − a_p x + χ(p)p^{k−1}`; for `k = 2` the representation is the §9.5 construction | **yes**: `AfCharpolyDS965`, which implies `AfDetLambda` |
| DS Exercise 9.6.3 | AI read only, unverified (issue #14 comment 7000317188 lists it under "Not read") | (a) derive det from the characteristic equation of 9.6.5's `ρ`; (b) the converse | supporting only |
| Shimura 1971, Thm 7.14 | not available on this host | (UNVERIFIED: recalled as the characteristic polynomial of Frobenius on `V_ℓ` of the Shimura quotient) | unread |
| Ribet, LNM 601 (1977) §§1–2 | not available on this host | (UNVERIFIED) | unread |
| Weil pairing route (`weilPairingMumford`, main) | tree checked | main has `T09Pic.WeilPairingMumford0` on abelian varieties and duals | not pursued: the print makes it unnecessary. It would also need the canonical polarization of `J₁(N)`, the adjointness `T_p* = ⟨p⟩⁻¹T_p` and glue down to `V_λ` |

## 2. Lean

`ZInQKernel/Contrib/OneProof/R16CoreYDS965.lean` (new) imports `ZInQKernel.Contrib.OneProof.R16Split` and
`ZInQKernel.Contrib.OneProof.AfTateLambda` (not `OneProof.Main`). It contains:
- `AfTateLam.AfCharpolyDS965 : Prop`: the leaf, with a docstring naming DS 9.6.5 and the identification.
- `afCharpolyDS965_iff`: `Iff.rfl` with `AfTateDSLambda`.
- `det_finrank_of_charpoly`: from `g.charpoly = X² − C t X + C d`, `det g = d` and `finrank = 2`.
- `afDetLambda_of_ds965`.
- `r16CoreY_of_ds965`.

No `sorry`, `axiom` or build-time code.

## 3. Checks (VERIFIED, one Lean process at a time)

| check | command | outcome |
|---|---|---|
| contribution | `lake build +ZInQKernel.Contrib.OneProof.R16CoreYDS965` | `Build completed successfully (11359 jobs)` |
| main chain | `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` | exit 0 |
| target copy | `lake env lean scratch/r16-det/Target.lean` | verbatim copy of `R16Split.R16CoreY` (diff against `R16Split.lean` empty), `copy_iff := Iff.rfl`, `'R16DetTarget.r16CoreY_copy' depends on axioms: [propext, Classical.choice, Quot.sound]` |
| `#discharges` | `lake env lean scratch/r16-det/Discharges.lean` (`Discharges-output.txt`) | below |
| fold dry run | `python3 scripts/one_proof/autofold.py scratch/r16-det/autofold.json --dry-run`, line 1 stripped, `lake env lean scratch/r16-det/FoldDryRun.lean` | `strict count: 11/18 on 29 -> 15/17 on 32; strictest 11/18 -> 15/17`; `'HDec.HSyn.sixContactMin_of_open49' depends on axioms: [propext, Classical.choice, Quot.sound]` (printed twice: one `#print axioms` line was appended to the generated file, which already has one) |

```
DISCHARGES [OpenResearchLeaves31.r16CoreY] by AfTateLam.r16CoreY_of_ds965
  still assumes: [AfTateLam.HeckeJ1DS,
 AfTateLam.AfShimura,
 AfTateLam.AfCharpolyDS965,
 X1Igusa.IgusaGL2DS,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 35 open hypotheses, 10345 theorems checked, 45 discharge one
'AfTateLam.afDetLambda_of_ds965' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The spec keeps `{t}.mumfordTorsionAlgClosed` (an open textbook LEAF on main). After fold34-pr has folded PR #54,
substitute `_root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`.

## 4. Leaf ratings

| leaf | Lean | printed form? | reason |
|---|---|---|---|
| `afCharpolyDS965` | `AfTateLam.AfCharpolyDS965` | **yes** (AI-read); a later human reading rates it a consequence, GLUE (end of row) | DS Thm 9.6.5 at `k = 2` prints the characteristic equation `x² − a_p x + χ(p)p` of `ρ_{f,λ}(Frob_𝔭)` over `K_{f,λ}`, and DS identify the weight-2 `ρ_{f,λ}` with the §9.5 construction `e_λ V_ℓ(A_f)` (Exercise 9.5.2(a)), aftate-fix2's `V_λ`. The weakenings are the same as for r16-close's `afTateDSLambdaSat`: newforms only, `N ≥ 2`, irreducibility and unramifiedness dropped. **Reading risk:** the identification is in DS's paragraph after the theorem on p. 404 (HUMAN-READ, zachbaugher, issue #14 comment 7121091136), not inside the theorem statement, and the theorem itself is phrased existentially ("there is … a representation"). A strict reviewer may want Shimura 1971 Thm 7.14 as a second locator (UNVERIFIED, unread). The Frobenius convention and the passage `e_λ V_ℓ(A_f) ↔ K_λ ⊗ V_ℓ(A_f)` are as in r16-close's rating of `afTateDSLambdaSat` (no new risk). **Human reading** (issue #14 comment 7121091136): CONSEQUENCE; GLUE. DS print the `k = 2` characteristic equation without proof or citation (§9.5 proves only that `ρ_{f,λ}(Frob_𝔭)` satisfies the quadratic), and the step from DS's transported Galois action to the Lean's algebraic `A_f` is a dictionary argument that is not in the print. |
| `heckeJ1DS`, `afShimura`, `igusaGL2DS` | unchanged | yes | as rated by r16-close (§4 there) |
| (dropped) `afTateDSLambdaSat`, `afDetLambda` | — | — | both follow from `afCharpolyDS965` (the second by `afDetLambda_of_ds965`; the first by Cayley–Hamilton), so they are not needed |

Proposed `locators.md` row (that file is not this task's to edit): `afCharpolyDS965`: DS GTM 228,
corrected fourth printing (2016), Thm 9.6.5 and the paragraph after it, p. 404; `ρ_{f,λ}` as in Lemma 9.5.3,
Thm 9.5.4 and Ex. 9.5.2(a) (§9.5, pp. 397–402); read by a human reader (issue #14 comment 7121091136).

## 5. Also done

The host path in r16-close's committed files (`docs/research/r16-close.md` l. 16–18 and
`scratch/r16-close/log.md`) is reworded so that no host path remains.

## 6. Files

- `ZInQKernel/Contrib/OneProof/R16CoreYDS965.lean`: the contribution.
- `scratch/r16-det/Target.lean`: verbatim copy of `R16Split.R16CoreY`, `copy_iff := Iff.rfl`, and the discharge
  at the copy.
- `scratch/r16-det/Discharges.lean` with `Discharges-output.txt`: `#discharges` and the axiom prints.
- `scratch/r16-det/autofold.json` (made by `make_spec.py`), `FoldDryRun.lean` and `FoldDryRun-output.txt`.
- `scratch/r16-det/log.md`.
