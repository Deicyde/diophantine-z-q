# leaf-audit: adversarial Lean audit of the leaves introduced on 2026-11-15

## Verdict

**One of the 16 leaves is false: `LinYangEx29All` (theta-fold).** The other 15 pass the three checks, within the
limits stated per leaf below. (VERIFIED: the refutation compiles; the numerics were computed.)

- **Why it is false.** `LinYangEx29All` quantifies over *every* `j₆ : ℍ → ℂ ∪ {∞}` that is:
  - continuous;
  - has the `Γ*`-orbits as fibres;
  - is surjective;
  - takes the values `0, ∞, −16/27` at the CM points.

  All of these clauses survive `j₆ ↦ conj ∘ j₆`, because complex conjugation fixes `0`, `∞` and `−16/27`. The
  conclusion `s₃² = z·s₂³` does not survive it. Applying the leaf to `j₆` and to `conj ∘ j₆` gives
  `(z − z̄)·s₂(Ω(τ))³ = 0`.
- **The Lean refutation** is `LeafAudit1115.not_linYangEx29All`, with standard axioms. Together with
  `IgusaThetaExpressions` and `QMHauptmodul`, the leaf would force `j_θ = jNum/jDen ∘ Ω` to be real wherever
  `jDen ≠ 0`.
- **The numerics contradict this.** The script `scratch/leaf-audit/py/jtheta_nonreal.py` evaluates the Lean
  definitions at 40 digits. It gives `j_θ(0.3 + 1.1i) = 4.27317158561753 − 0.683139858455891i`, with `|jDen| ≈ 3.1·10⁵`.
  - Two more points are also non-real.
  - The script reproduces pkg-I1's values `j_θ(√2 + i) = 0` and `j_θ(i√(9+6√2)) = −16/27`, and the pole at `i√3`.
- **Why it matters.** The leaf set `{IgusaThetaExpressions, LinYangEx29All}` plus the chain's `QMHauptmodul` is
  inconsistent. theta-fold's `frozenTarget` takes it as an open hypothesis, and theta-fold's OPEN.md lists it as an
  open LEAF (elliotglazer #86).
- **The fix is theta-fold's own existential `LinYangEx29`.** It feeds the consumer directly
  (`IgusaAlgFinal.thetaRatiosAtQM_of_printed`) and no longer needs `QMHauptmodul`.
  - The corrected chain top compiles: `scratch/leaf-audit/FoldFix.lean`, `sixContactMin_of_open29_fixed`, standard
    axioms.
  - With `j₆ = j_θ`, its three relations hold numerically to `2·10⁻³⁹` at three points
    (`scratch/leaf-audit/py/linyang_check.py`).
  - The spec for the change is `scratch/leaf-audit/autofold.json`. It is a by-hand change: the false field cannot be
    discharged, so the consumer is changed instead.

**Integration finding (VERIFIED).** With theta-fold merged onto leaf-fold25, `ZInQKernel/OneProof/H/TailZ35.lean`
no longer compiles (line 117: type mismatch). The reason is that theta-fold threads the extra argument `hθ` through
`sixContactMin_of_open28`, and TailZ35 does not pass it. theta-fold must therefore be re-folded on top of
leaf-fold25. This worktree's `Main.lean` keeps leaf-fold25's side of the merge.

## What compiles

All entries below are VERIFIED.

- **The audit module.** `ZInQKernel/Contrib/OneProof/LeafAudit1115.lean` builds with
  `lake build ZInQKernel.Contrib.OneProof.LeafAudit1115` (12964 jobs). Every new theorem uses
  `[propext, Classical.choice, Quot.sound]`; the output is in `scratch/leaf-audit/build-LeafAudit1115-output.txt`.
  - It imports only the contribution modules that define the leaves, never `Main`.
  - h29-ne3's leaves exist only in `scratch/h29-ne3/TYZLemma29Mod2.lean`. That file is copied verbatim to the helper
    `ZInQKernel/Contrib/OneProof/LeafAudit1115H29.lean`: same namespace, a drop-in for
    `Contrib/OneProof/TYZLemma29Mod2.lean`.
- **The corrected theta-fold top.** `scratch/leaf-audit/FoldFix.lean` compiles.
- **`#discharges`.** The run is `scratch/leaf-audit/Discharges.lean`, output in `discharges-output.txt`.
  - It runs against a temporary `Main`: theta-fold's `Main` plus leaf-fold25's `hFH` edit. This was a working-tree
    change only and has been restored, because leaf-fold25's `Main` cannot build with theta-fold.
  - Result: 64 open hypotheses, 3499 theorems checked, 17 discharge one.
  - The audit module adds no discharge, as expected. The 11-15 discharges of `r17`, `r11r12`,
    `elkiesX6StarPrinted`, `r9b`, `mumfordGroupLaw`, `h29`, `hL3` and `hX` are all listed.
  - `linYangEx29All` is among the open hypotheses.

## Table

| leaf (branch) | (1) non-vacuity | (2) sanity case | (3) old/new in Lean | verdict | printed form? |
|---|---|---|---|---|---|
| `LinYangEx29All` (theta-fold) | premises met by `QMHauptmodul`'s `f`, and also by `conj ∘ f` | **fails**: forces `j_θ` real; numerically `j_θ(0.3+1.1i) = 4.273 − 0.683i` | new ⇒ use form `ThetaRatiosAtQM` (with `QMHauptmodul`) | **FALSE** | no: drops the holomorphy of Lin–Yang's `j₆`. Fix: existential `LinYangEx29` (consequence of the print) |
| `IgusaThetaExpressions` (theta-fold) | `𝔥₂ ∋ Ω(τ)` (`omegaSiegel_proof`) | 76 exact Fourier coefficients (theta-fold, not re-run; script not in the repo); consistent with the corrected Lin–Yang relations to 1e-39 | together with the corrected leaf ⇒ `ThetaRatiosAtQM` | OK | printed (Igusa's classical identities; constants pinned) |
| `ElkiesX6StarFunctionField` (elkies-coord) | the inner premises (integral, `η ∈ t.U`) follow from the leaf's own charts (`ff_premises_of_charts`); the outer quantifier is existential | fibre fields `ℚ(i)` at `t = 1` (D = −4), `ℚ(√−3)` at `t = 0, ∞` (D = −24, −3); `[ℚ(X₆):ℚ(t)] = 4 = #W` | new ⇒ old `elkiesX6StarPrinted_of_functionField`; old ⇒ new not proved | OK | printed (modulo the standard `ℚ(X/W) = ℚ(X)^W`); orientation unread, but harmless (see §2) |
| `MumfordGroupLaw` (leaf-fold23) | **proved**: trivial family `Spec ℚ → Spec ℚ`, fibres = zero AV (`mumfordGroupLaw_premises_trivial`) | conclusion holds there (`mumfordGroupLaw_trivial_conclusion`) | old ⇒ new `mumfordGroupLaw_of_core`; new + `PushforwardStructureSheaf` ⇒ old | OK | consequence (GIT 6.14 per component) |
| `NewformRepConductor` (r17-bypass) | not provable in Lean today (no Lean newform with `IsNewform`); same premises as `r17`, minus `ρ` | 11a: `a_11 = 1 = v_11(11)` (STANDARD) | new ⇒ old `carayolR17'_of_newformRepConductor`; old (+ R14 existence) ⇒ new `newformRepConductor_of_R17'` | OK | consequence (Carayol Thm A + Casselman), pending reading |
| `TYZLemma29PrintedNe3` (h29-ne3) | **proved relative to sibling leaves** (Legendre, Jones–Pall, test vector, `h11`) at `n = 11` (`tyz_premises`) | brandt.py re-run: `Q(11), Q(19) = ±1 = ±𝓛` | `printed_iff : TYZLemma29Printed ↔ Ne3 ∧ Thm21At31` (both directions); ⇒ `h29` | OK | printed (restricted to odd `1 < n ≠ 3`) |
| `TYZThm21At31` (h29-ne3) | as above, at `n = 3` | brandt.py: `Q(3) = f₃(1) = ±3 = ±w_K 𝓛(3)𝓛(1)` (`w_K = 3`) | `printed_iff` | OK | consequence (one instance of Thm 2.1) |
| `MainTheoremCM` (qmrec-printed) | instantiated at the route (`E = K(√2)`, reflex datum, the QM surface) inside `qmReciprocityL3_of_printed`; no nonzero AV over `ℂ` exists in Lean, so there is no free-standing instance | (shape check only) `θ(Φx)^σ = θ'(Φy)` for `ty − x ∈ 𝔞̂` is Shimura's `ξ(u)^σ = ξ'(N(s)^{-1}u)` | new ⇒ `QMReciprocityL3`, `rayClassCMAb` | OK | printed, weakened (`ε` existential, dropped clauses) |
| `PanPrinted` (pb-bypass) | template premises as for `PanBerger`; `LocalIsPst` holds for the trivial representation | trivial rep is pst (`isPst_trivial`) | `PanPrinted → BergerPrinted → PanBerger` | OK, **conditional** | printed, over pb-bypass's `B_st` (see §8) |
| `BergerPrinted` (pb-bypass) | as above | as above | as above | OK, **conditional** | printed (same caveat) |
| `FaltingsTateSurj` (faltings-cm) | **proved**: `K = ℚ`, `A = B = 0` | conclusion holds at `A = B = 0` (`faltingsTateSurj_zero`) | both directions (`faltingsTateSurj_of_faltingsTate`, `faltingsTate_of_surj`) | OK | consequence (surjectivity half) |
| `ShimuraIntegralModelUsed` (sir-printed) | existential (no premises to meet) | — | old ⇒ new `shimuraIntegralModelUsed_of_rep`; new ⇒ consumer | OK | not printed (paper derivation from Lan + Lemma P over `ℚ̄`) |
| `X0ModuliGaloisMero` (gz-heegner) | **proved**: `N = 1`, `g = 1`, `σ = id`, `τ = τ' = i`, `μ = 1`, `j(i) = 1728` (`x0ModuliGaloisMero_premises`) | `N = 1`: `σ(g(τ)) = g(τ')` is the classical `j`-equivariance | new ⇒ `hX` (`x0ModuliGalois_of_mero`); with `ShimuraMainCM` ⇒ gz-hl3's `HeegnerPointRational` | OK | consequence (canonical model + q-expansion principle) |
| `GrossZagierFormulaCd` (gz-weil) | needs a Lean newform for `C_d` (only from further leaves): not proved | PARI: `C_5`, `D = −31`: `L'(E/K,1) = 7.5057 > 0`, Heegner point of height `1.8995 > 0` | general ⇒ Cd (`grossZagierFormulaCd_of`); with `HeegnerPointRationalCd`, `GrossConjugationCd` ⇒ `GrossZagierHeegnerCd` | OK | consequence (GZ V.2.1, constant forgotten) |
| `GrossConjugationCd` (gz-weil) | as above | `C_5`: `ε = −1`, Heegner point in `E(ℚ)` (σy − y torsion) | general ⇒ Cd (`grossConjugationCd_of`) | OK | consequence (Gross §5) |

"Proved" means a compiled Lean instance in `LeafAudit1115.lean`.

## Per-leaf notes

1. **`LinYangEx29All`.** The proof is in the verdict above.
   - The universal form is not Lin–Yang's statement. Their `j₆` is *the* Hauptmodul: holomorphic, and pinned by
     three values. The Lean clauses pin it only up to orientation-preserving or orientation-reversing
     homeomorphisms of `P¹` that fix three points.
   - There are two possible fixes:
     - the existential `LinYangEx29` (recommended; already defined and consumed);
     - the universal form with a holomorphy premise (`j₆` holomorphic where finite), which `QMHauptmodul`'s `f`
       satisfies off `jDen = 0`.
2. **`ElkiesX6StarFunctionField`.** The leaf is existential, so the only risks are falsity or a degenerate `W`.
   - **Degenerate `W`.** An empty `W` would make the clause say `ℚ(X₆) = ℚ(t)`, which is false (degree 4). The leaf
     therefore forces genuine Atkin–Lehner involutions. These exist over `ℚ` on the canonical model, so the clause
     holds with them.
   - **Orientation.** The chart cover `{s² = −t, r² = 3(t − 1)}` is invariant under `t′ = 1/t`, with `s′ = s/t` and
     `r′ = rs/t`, which give `s′² = −t′` and `r′² = 3(t′ − 1)`.
     - This swaps the `D = −24` and `D = −3` fibres and fixes `t = 1`.
     - So the unread `0/∞` orientation does not affect truth (algebra VERIFIED). The transfer of the second chart is
       by the same symmetry and is not compiled.
   - **CM fibres (by hand).** The Ogg fixed-point counts were done by hand and are UNVERIFIED as citations:
     - `w₂` fixes the 2 points of `D = −4`;
     - `w₃` fixes the 2 points of `D = −3`;
     - `w₆` fixes the 2 points of `D = −24`.

     These are exactly the three branch fibres of the charts.
3. **`MumfordGroupLaw`.** The fibre hypothesis is the only one that could be vacuous. The trivial family meets it,
   because every field fibre is `AbVar.zero`.
4. **`FaltingsTateSurj`.** `T_ℓ(0) = 0` (subsingleton), so the conclusion holds trivially at `A = B = 0`. It cannot be
   vacuous, since `AbVar K` is inhabited.
5. **`NewformRepConductor`.** `IsNewform` excludes oldforms: "not in `oldSpace`" plus strong multiplicity one. This
   matters, because an oldform would make the leaf false.
6. **TYZ leaves.** Non-vacuity here means: a test vector exists by `TYZTestVectorExists`, and `IsTestVector n τ 0`
   would hold only if `π_ℤ^{U_n} = 0`, in which case `TYZThm21At31` would be *false* rather than vacuous. h29-fix's
   brandt.py was re-run and reproduced. `w_K` is now handled exactly by the two prints.
7. **`MainTheoremCM`.** `IsUniformization` requires holomorphy, so the `conj` trick of §1 does not apply. The point
   conjugation `P^σ ≫ h = Spec σ ≫ P` matches `A^σ = A ×_{Spec ℂ, Spec σ} Spec ℂ`.
8. **`PanPrinted`, `BergerPrinted`.** Both leaves are faithful to the print, *provided* `B_st^{G_K}` is
   finite-dimensional and nonzero (Fontaine: `= K₀`), which is not proved.
   - `IsSemistableOver` is the finrank equation `dim D_st,K = dim B_st^{G_K} · dim V`. If `B_st = 0`, or if both
     spaces were infinite-dimensional (Mathlib's `finrank = 0`), then every representation would be "semistable".
   - In that case `PanPrinted` becomes Pan's theorem without the pst hypothesis, which is false: non-classical
     overconvergent eigenforms of integral weight give Hodge–Tate, non-de Rham representations (Kisin, STANDARD,
     UNVERIFIED locator).
   - pb-sanity is checking the definitions. Recommendation: add `FiniteDimensional ℚ_p (bstInv p K)` and
     `0 < finrank (bstInv p K)` to `IsSemistableOver`, or prove them.
9. **`ShimuraIntegralModelUsed`.** It is weaker than the field (proved), and every consumer needs only `p > 324`.
10. **`X0ModuliGaloisMero`.** The premise "`k/N` has order `N`" is forced by `σ`. Meromorphy is complex-analytic, so
    it is not open to the `conj` trick.
11. **GZ `C_d` leaves.** The leaves were consistent with the PARI sanity case. Their non-vacuity in Lean needs a
    `Newform` for `C_d`, which is available only from further leaves (`NewAt32`, `AtkinLiTwistNew`).

## What remains

- A human reading of the prints is still needed for every leaf: the locators are UNVERIFIED and there is no network.
- Theta-fold must be re-folded on top of leaf-fold25 with the corrected field.
- pb-sanity's verdict on `B_st` decides `PanPrinted` and `BergerPrinted`.
- The old ⇒ new direction is not proved for `ElkiesX6StarFunctionField`. It is not needed.
