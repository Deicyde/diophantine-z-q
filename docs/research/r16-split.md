# r16-split: the research field `r16` (`LeafModCurves.R16_EichlerShimuraJ1'`), re-examined

Task r16-split, 2026-11-15. Base `24f97774` (wip/w72, leaf-fold20). Lean:
`ZInQKernel/Contrib/OneProof/R16Split.lean` (new) and `scratch/r16-split/` (results log `log.md`). Nothing else
under `ZInQKernel/` or `blueprint/` was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a file of this tree. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number recalled without a source (no network on this
host). Unless `docs/research/locators.md` read it, a locator is UNVERIFIED.

## 1. Verdict and main result

**Verdict.** The two printed components named in kinds.tsv cannot yet be stated as Lean leaves over genuine
definitions. They are Shimura 1971 Thm 7.9 (the Eichler–Shimura congruence relation) and Shimura 1973 Thm 1
(the quotient `A_f`). Both are statements about the Hecke correspondences `T_p`, `⟨d⟩` on `X₁(N)` and about
Shimura's specific quotient `A_f = J₁(N)/I_f J₁(N)`, where `I_f = ker(𝕋 → K_f, T_p ↦ a_p(f))`. The tree still
has no Hecke correspondence on any model of `X₁(N)`. Above all, it has no comparison between Mathlib's analytic
cusp form `f : CF N 2` and the algebraic curve, and without that `I_f` cannot be written down. §4 lists exactly
what is missing, re-examined against the objects the kernel now has. Some of the earlier list (modular-split
§4.1) is now available:
- models of `X₁(N)` from function fields;
- morphisms from maps of function fields;
- `Pic` pull-back;
- images of homomorphisms as abelian varieties, which make the quotient unnecessary.

Two items are still missing:
- the quotient isogeny `E → E/C` (Vélu), which the second degeneracy map needs;
- the comparison `S₂(Γ₁(N)) ≅ H⁰(X₁(N)_ℂ, Ω¹)`.

**Main result: the smallest faithful split, proved in Lean (VERIFIED, standard axioms).** One of the four
conjuncts of r16 is a consequence of the others together with leaves already in the bundle. Of the three sources
cited by r16's docstring, this removes (ii): "`V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`" (Shimura 1971 §7.4,
Ribet 1977). The locator audit had marked exactly that item as not supplied (`locators.md`, row R16: "Individual-embedding
rank-two Tate realization … must still be supplied").

```lean
-- ZInQKernel/Contrib/OneProof/R16Split.lean, namespace R16Split
theorem r16_of_printed (hC : R16CoreY) (hM : AvSplit.MumfordTorsionAlgClosed)
    (hCP : ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed) : LeafModCurves.R16_EichlerShimuraJ1'
theorem r16_of_coreY (hC : R16CoreY) (hT : PkgI3.TateModuleFree) (hCP : PkgI3.CharPolyIndepOfEll) :
    LeafModCurves.R16_EichlerShimuraJ1'
theorem r16_of_coreX (hC : R16CoreX) (hT : PkgI3.TateModuleFree) : LeafModCurves.R16_EichlerShimuraJ1'
theorem coreY_of_r16 : LeafModCurves.R16_EichlerShimuraJ1' → R16CoreY      -- the cores are consequences
theorem coreX_of_r16 : LeafModCurves.R16_EichlerShimuraJ1' → R16CoreX
```

- `R16CoreY` is r16 verbatim with the **rank-two clause** deleted. That clause says
  `finrank (eigenFun ℓ A θ emb) = 2` for all `ℓ` and `ι`.
- `R16CoreX` is r16 verbatim with the **dimension clause** deleted. That clause says `A.dim = [K_f : ℚ]`.
- `mumfordTorsionAlgClosed` and `charPolyIndepOfEllAlgClosed` are already published LEAF fields of
  `OpenTextbookLeaves11`, so `r16_of_printed` adds only one new hypothesis, `R16CoreY`.

**The fold.** The recommended fold replaces `r16` by `R16CoreY`. The field is filled with
`r16_of_printed {n}.r16CoreY {t}.mumfordTorsionAlgClosed {t}.charPolyIndepOfEllAlgClosed`; the spec is in
`scratch/r16-split/autofold.json`. Running autofold with `--dry-run`:
- reports "strict count: 47/11 on 58 -> 47/11 on 58; strictest 46/12 -> 46/12";
- produces the module saved as `scratch/r16-split/FoldDryRun.lean`.

The kinds count does not change: a composite GLUE field is replaced by a strictly weaker composite GLUE field.
The literature content shrinks from three published inputs to two, and both are statements about the same
`A_f`.

## 2. The new leaf, rated

| leaf | Lean | printed form? | kind | reason |
|---|---|---|---|---|
| `r16CoreY` | `R16Split.R16CoreY` | **no** | composite (GLUE) | It is a consequence of two printed theorems at Shimura's `A_f`: (a) Shimura 1973 Thm 1, unconditional clauses, which give the `ℚ`-quotient `A_f`, `K_f ↪ End⁰(A_f)` and `dim A_f = [K_f:ℚ]` (audit row R16, read); (b) the characteristic polynomial `X² − a_p X + χ(p)p` of arithmetic Frobenius on `V_ℓ(A_f)` over `K_f ⊗ ℚ_ℓ`, `p ∤ Nℓ` (Diamond–Shurman Thm 9.5.4; Shimura 1971 Thm 7.11, which comes from Thm 7.9; numbers UNVERIFIED). It is not the printed form because it packages both as one existential over an unnamed `(A, π, θ)`: `A_f` has no Lean definition (§4). It is never stronger than the prints: it is r16 minus a conjunct, and r16's docstring already argues that r16 is a consequence. The model-of-`X₁(N)` and `θ ∘ c` convention remarks of r16's docstring apply unchanged. |
| (alternative) `R16CoreX` | `R16Split.R16CoreX` | no | composite (GLUE) | It is the same kind of consequence, but it keeps the rank-two clause, whose source is Diamond–Shurman Lemma 9.5.3 / Ribet 1977 (UNVERIFIED), and drops `dim A = [K_f:ℚ]`. It needs only `TateModuleFree`. It is not recommended: its remaining source (ii) is the one the audit could not locate. |

No new published leaf is introduced, so no locators row is needed. If `R16CoreY` is folded, its kinds row is
`composite`, GLUE, with the source text of the spec.

## 3. The proofs (all VERIFIED: compiled, `#print axioms` = `propext, Classical.choice, Quot.sound`)

Notation:
- `k = ℚ_ℓ`, `Ω = ℚ̄_ℓ = PadicAlgCl ℓ`, `V = V_ℓ(A)`, `F = K_f`;
- `ρ = rhoV : F → End_k(V)`, which is `endV ∘ θ`;
- `W = Hom_k(V, Ω)`;
- `P(a)φ = φ ∘ ρ(a)` (`precompHom`).

R16's `eigenFun ℓ A θ ι` is literally the joint eigenspace `{φ ∈ W | P(a)φ = ι(a)φ for all a}`
(`eigenFun_eq`, proved by `Iff.rfl`).

1. **`ρ` is a ring homomorphism** (`homT_mul`, `homT_one`, `endV_mul`, `endV_one`). Leaves.lean defines `endV`
   only as an additive map.
2. **Decomposition** (`isInternal_jointEig`, `sum_finrank_jointEig`). Let `F` be a field, finite over `ℚ`,
   acting on a finite-dimensional `Ω`-space `W` through a ring homomorphism `P`. Then `W` is the internal
   direct sum of the joint eigenspaces `E_ι`, one for each `ι : F →ₐ[ℚ] Ω`. The proof:
   - take a primitive element `α` (`Field.powerBasisOfFiniteOfSeparable`);
   - `P(α)` is annihilated by the separable `μ_α`, so it is semisimple
     (`isSemisimple_of_squarefree_aeval_eq_zero`);
   - its eigenvalues are roots of `μ_α`, which are the `ι(α)` (`PowerBasis.lift`);
   - `E_ι = ker(P(α) − ι(α))`, because `{a | P(a)φ = ι(a)φ}` is a subfield of `F` (`eqSubfield`) that
     contains `α`.
3. **Dimension clause from rank two** (`dim_eq_of_rank_two`, at `ℓ = 2`). The chain of equalities is
   `2·[F:ℚ] = Σ_ι dim E_ι = dim_Ω W = dim_k V = rank T_2(A) = 2 dim A`. The steps are:
   - `AlgHom.card` gives the number of `ι`;
   - `Module.finrank_linearMap_self` gives `dim_Ω W = dim_k V`;
   - `Module.finrank_baseChange` gives `dim_k V = rank T_2(A)`;
   - `TateModuleFree` gives `rank T_2(A) = 2 dim A`.

   Then cancel the 2 in `WithBot ℕ∞`.
4. **Rank two from the dimension clause** (`rank_two_of_dim`). Write `d_ι = dim E_ι`.
   - The trace of `P(a)` is `Σ_ι d_ι ι(a)` (`trace_eq_sum_jointEig`, `LinearMap.trace_eq_sum_trace_restrict`).
   - It equals the trace of `ρ(a)` (`trace_precompL`, computed in the basis `b.constr`).
   - That trace is rational by Mumford §19 Thm 4 (`trace_endV_rat`; `End⁰ = ℚ ⊗ End`, so it suffices to treat
     `q ⊗ e`).

   `weights_eq_of_rational` then shows that all `d_ι` are equal:
   - the functional `a ↦ Σ d_ι ι(a)` is `ℚ`-valued, so it is `a ↦ Tr_{F/ℚ}(ba)` for some `b ∈ F`
     (`traceForm_nondegenerate`);
   - by `trace_eq_sum_embeddings` and Dedekind's independence of characters (`linearIndependent_monoidHom`),
     `d_ι = ι(b)` for every `ι`;
   - so `b = d_ι ∈ ℕ` for every `ι`.

   Finally `Σ_ι d_ι = 2 dim A = 2[F:ℚ]` with `[F:ℚ]` summands, so `d_ι = 2`.
5. `r16_of_coreX`, `r16_of_coreY` and `r16_of_printed` assemble these steps. `r16_of_printed` uses the kernel
   bridges:
   - `AvSplit.torsionStructure_of_mumford` followed by `T5Torsion.TateFree.tateModuleFree_of_torsionStructure`
     gives `TateModuleFree`;
   - `ZInQ.Contrib.AVB1.charPolyIndepOfEll_of_algClosed` gives `CharPolyIndepOfEll`.

Compile record (`scratch/r16-split/log.md`):
- `lake env lean scratch/r16-split/Split.lean`: about 15 s, standard axioms. **VERIFIED.**
- `lake build +ZInQKernel.Contrib.OneProof.R16Split`: success, 9122 jobs. **VERIFIED.**
- The `#discharges` output is in §6.

## 4. What is missing for the printed split (re-examined)

The goal is two separate published-form leaves about one Lean object `A_f`, each in its printed form:
- `S73`: Shimura 1973 Thm 1, the unconditional clauses;
- `ES`: Diamond–Shurman Thm 9.5.4, or Shimura 1971 Thm 7.11 with Thm 7.9.

`R16CoreY` would then follow from them by glue. Here is each object the task names, and what it gives
(VERIFIED by reading the files cited; effort estimates are SPECULATIVE).

| needed object | status in the tree | what it gives / what is missing |
|---|---|---|
| a model `X` of `X₁(N)` | **available**. `IsX1Model`, with existence through cloud-w07's `NormalModel.lean` (`Xn F`, `functionFieldEquiv`: the normal model of any finite extension of `ℚ(T)`) | — |
| the curve `X₁(N) ∩ Γ₀(p)` | **definable**. Its function field is `K_N(x(C))` for a cyclic `C ⊂ E_j[p]`, an `IntermediateField` like `fieldX1`; the model again comes from `Xn` | not yet written |
| degeneracy map `α : X₁(N,p) → X₁(N)` (forget `C`) | **definable**. It comes from the field inclusion, using the vendored `exists_hom_of_valuationRing_stalk` (`Birational/ValuativeExtension.lean`): a generic-point map from a curve with valuation-ring stalks to a proper target extends to a morphism | not yet written |
| degeneracy map `β : (E, P, C) ↦ (E/C, P mod C)` | **missing: the quotient isogeny `E → E/C` (Vélu's formulas)** | Mathlib has Weierstrass curves and their point groups, but no isogeny with a prescribed finite kernel. `β^*` sends `j ↦ j(E/C)` and the Weber function `h(P) ↦ h(P mod C)`. The Weber function is needed because `E/C` is `E_{j(E/C)}` only up to a quadratic twist. |
| `⟨d⟩` | **definable**. `h(P) ↦ h(dP)` is a `ℚ(j)`-automorphism of `K_N`, and it extends to the model as above | not yet written |
| `T_p` and `⟨d⟩` on `J` | **definable given the two maps**. `T_p = Alb(α) ∘ Pic⁰(β)`, where `Alb(α)` comes from `IsJacobian.univ` and `Pic⁰(β)` from the vendored `Pic.map` pull-back through `J ≅ Pic⁰` (`exists_abelianVariety_picardDegreeZero`, `Curve.isAlbanese_abelJacobiMap`) | Pic pull-back as an abelian-variety homomorphism goes through Yoneda on the representing object; not yet written |
| the Hecke algebra `𝕋 ⊆ End(J)` | definable (`Subring.closure`) once `T_p` and `⟨d⟩` exist | — |
| **the eigencharacter `λ_f : 𝕋 → K_f`, `T_p ↦ a_p(f)`, and `I_f = ker λ_f`** | **missing: the comparison `S₂(Γ₁(N)) ≅ H⁰(X₁(N)_ℂ, Ω¹)`, `f ↦ f(τ)dτ`, Hecke-equivariant** | `f` is Mathlib's analytic cusp form; `X` is an algebraic curve over `ℚ`. Nothing links them: there is no complex-analytic structure on `X(ℂ)` and no `Γ₁(N)\ℍ* ≅ X₁(N)(ℂ)`. `uniformizationLeafAll` is for abelian varieties only (`A(ℂ) ≅ ℂ^g/Λ` in coordinates). dimjac-glue's `H⁰(X, Ω¹) =` holoDiff identifies the differentials with those of the function field, not with cusp forms. **This is the deepest missing definition.** Without it, `λ_f` cannot be defined. One could take `λ_f` existentially, but then it would be a structure invented for the purpose, which is exactly what the leaf rules forbid. |
| `A_f` | **definable without quotients** once `λ_f` is available | av-glue's image-as-abelian-variety recipe (`Hom.image` plus flat base change) gives `A_f' = (n·e_f)(J)`, where `e_f` is the idempotent of `𝕋 ⊗ ℚ` for the Galois orbit of `f`. `A_f'` is isogenous to `J/I_f J` (Shimura 1973 §1; STANDARD), it receives a surjection from `J`, and every clause of R16 is invariant under isogeny (SPECULATIVE: dimension, `V_ℓ`, and `θ` transported through `End⁰`). So the quotient that modular-split §4.1 listed is not needed. |
| Shimura 1971 Thm 7.9 **as printed** | **missing in addition**: an integral model of `X₁(N)` over `ℤ_(p)` with good reduction (Igusa), reduction of correspondences, and the Frobenius correspondence | Its Tate-module consequence `V_ℓ(T_p) = σ_p + p⟨p⟩σ_p⁻¹` on `V_ℓ(J)` for `p ∤ Nℓ` is statable as soon as `T_p` and `⟨d⟩` exist (SPECULATIVE), and it avoids the integral model. |
| route A's `QMAbScheme`; genus-fold's `dim J₁(N) ≤ N²`; `Contrib/HeckeAll/` | not relevant | `QMAbScheme` is about families of QM abelian surfaces. The genus bound concerns `dim J` only. `HeckeAll` is about `L(C_d, s)` and Hecke characters of `ℚ(i)`; it has no Hecke operators on modular curves or Jacobians (VERIFIED, `hecke-all.md`). The kernel's `IsNewform` encodes the Hecke-eigen condition through coefficient identities only. |

**Smallest faithful split today**: `r16 ⇐ R16CoreY ∧ mumfordTorsionAlgClosed ∧ charPolyIndepOfEllAlgClosed`
(§1). Two further splits would follow:
- with Vélu and the four definable rows written: `T_p`, `⟨d⟩` and `𝕋` as Lean objects;
- with the `S₂ ↔ H⁰(Ω¹)` comparison: `λ_f`, `A_f`, and then `S73` and `ES` as separate published-form leaves.

From those, `R16CoreY` follows. The ingredients are `θ` from the `𝕋`-action, and the specialization at `ι` of the
characteristic polynomial over `K_f ⊗ ℚ_ℓ`, using the rank-two freeness that §3 now proves. That composition
would be project glue.

## 5. Is r16 false, vacuous or inert? No

These are SPECULATIVE judgements, from reading the statement:
- **Not vacuous.** Newforms exist, for example at level 11. Models of `X₁(N)` exist (`X1ModelExists`, field `x1`
  of `ModCurveLeaves`), and so do Jacobians.
- **Model and convention.** If a model (the `ℤ/N` versus `μ_N` moduli problem) gives `ā_p` and `χ̄(p)`, replace
  `θ` by `θ ∘ c`. Then `eigenFun ℓ A (θ ∘ c) ι = eigenFun ℓ A θ (ι ∘ c)`, and the trace becomes
  `(ι∘c)(ā_p) = ι(a_p)`. This needs `ā_p = χ̄(p)a_p` for `p ∤ N`, and `K_f` stable under `c` (STANDARD; Ribet
  1977).
- **The rank-two and dimension clauses are not independent.** Given `TateModuleFree` and Mumford §19 Thm 4, each
  implies the other (§3). That is a redundancy in the statement, not an error.

## 6. `#discharges` and the fold check (VERIFIED)

- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`: success (12982 jobs; `frozenTarget`
  has standard axioms).
- `lake env lean scratch/r16-split/Discharges.lean`, which runs `#discharges`; the full output is in
  `scratch/r16-split/Discharges-output.txt`:

```
DISCHARGES [OpenResearchLeaves20.r16] by R16Split.r16_of_coreX
  still assumes: [R16Split.R16CoreX, PkgI3.TateModuleFree]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves20.r16] by R16Split.r16_of_coreY
  still assumes: [R16Split.R16CoreY, PkgI3.TateModuleFree, PkgI3.CharPolyIndepOfEll]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves20.r16] by R16Split.r16_of_printed
  still assumes: [R16Split.R16CoreY, AvSplit.MumfordTorsionAlgClosed, ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 65 open hypotheses, 1310 theorems checked, 8 discharge one
```

- `r16_of_printed` is the theorem to fold. Its other two hypotheses are existing LEAF fields of
  `OpenTextbookLeaves11`.
- The autofold `--dry-run` module (`scratch/r16-split/FoldDryRun.lean`) compiles:
  `HDec.HSyn.sixContactMin_of_open28` has standard axioms. It was not applied: `Main.lean`, `kinds.tsv` and
  `claims.tsv` are unchanged, because folding is the integrator's step.

## 7. Files

- `ZInQKernel/Contrib/OneProof/R16Split.lean`: the contribution. It imports `HDecomp.ModCurves.Leaves` (which
  declares r16), `OneProof.H.TailQ`, `OneProof.H.LF4T5` and `Contrib.AVB1.AlgClosed`, but not `OneProof.Main`.
- `scratch/r16-split/Split.lean`: the same mathematics in scratch form, with `#print axioms`.
- `scratch/r16-split/autofold.json`: the fold spec (field `r16`, leaf `r16CoreY`, kind composite).
- `scratch/r16-split/FoldDryRun.lean`: the autofold `--dry-run` module.
- `scratch/r16-split/Discharges.lean`: the `#discharges` check.
- `scratch/r16-split/log.md`: the results log.
