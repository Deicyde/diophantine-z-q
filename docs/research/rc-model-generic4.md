# Generic comparison on the pinned rational open: pair classes at every point

**Retired frozen fields: none yet.** No field of the frozen target and no count changes. The hRC GLUE row (`docs/one-proof/OPEN.md:460`) and its odd-side input `PreLeaves.odd_staged` (`ZInQKernel/Contrib/OneProof/RC/Wiring/Leaves.lean:305`) are unchanged.

**Scoped stop.** Items 1 and 2 are proved. Item 5 is partly done: the pair-class conjunct is proved with actual readings on both sides. Items 3 (Atkin–Lehner) and 4 (good Hecke) remain open; the smallest faithful statements are below. `GenericFibreComparison` is **not** instantiated, because the Atkin–Lehner and Hecke readings are not yet actual on both sides.

All 13 new modules are under `ZInQKernel/Contrib/OneProof/RC/ModelGeneric4/`. Each builds with `lake build`, with no `sorry` and no axiom declaration. Every `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`. No error verdict was reached, and no leaf was added or proposed.

## Main results

1. **Item 1 (pair class at every parameter).** `rationalPoints_rationalPointAtParameter` (`PairClass.lean`) says that for every `2 ≤ N` and every τ ∈ ℍ, `rationalPoints h₂ (rationalPointAtParameter h₂ τ) = analyticCyclicPair τ`. This covers parameters with algebraic j(τ) and coordinate collisions.
2. **Item 2 (surjectivity).** `exists_complexPoint_eq` (`Surjectivity.lean`) says every `x : RationalCurveComplexPoints (branchFiniteOverQ N)` has a τ with `x.left ≫ (X0Model3.finiteChart N).ι = X0Model.complexPoint N τ`. Equivalently (`exists_rationalPointAtParameter_eq`), every ℚ-point to ℂ of `Y0RationalAlgebra h₂` is `rationalPointAtParameter h₂ τ`.
3. **(b1) at every level.** `pairQuotientJ_analyticCyclicPair` (`LatticeQuotient.lean`): the actual vendored iterated Vélu quotient of `(ℂ/(ℤτ+ℤ), ⟨1/N⟩)` has invariant `j(Nτ)`. This was not in the tree. It needed a new order-two Vélu map of function fields, because the vendor has only the point map `veluPointMap2`.
4. **Pair-class conjunct (item 5, partial).** `pairClass_conjunct` (`Readings.lean`): `branchPairClass h₂ (x ≫ (rationalOpenIsoOverQ h₂).hom) = levelPairClass h₂ x`, with actual readings on both sides.

## New definitions and theorems (what each supplies)

| Declaration (module) | Statement and use |
| --- | --- |
| `gate`, `pointPlace`, `IsSeam` (QuotientFunctionField) | A fixed centred Abel gate on each elliptic equation (the vendored existence theorem, chosen once). `IsSeam ι hι f`: restricting places along ι is the point homomorphism f. |
| `exists_oddStep`, `StepSeam`, `exists_quotientSeam_of_steps` | Each odd prime step of `cyclicQuotientCurve` is induced by a function-field map with seam the actual Vélu point map. The kernel is in H, of order ℓ, and the image of H is `stepSubgroup`. The composite over the iteration has kernel exactly H. **ON THE SPOT (c)**, from the vendored odd Vélu function-field theorem. |
| `twoFFHom`, `twoFFHom_finiteAlong`, `twoFFHom_isIntegral`, `twoFFHom_seam`, `stepSeam_two`, `exists_quotientSeam` (OrderTwoStep) | The order-two Vélu formulas define an injective, finite, integral map of function fields. Its place restriction is `veluPointMap2`. Proved via the transcendence of `x + G/(x-x₀)`, poles at ∞ and at the abscissa `x₀`, and `eq_placeOfEquation_of_le_centre` elsewhere. The composite therefore exists at every level. **ON THE SPOT (c)**. |
| `j_eq_analyticJN_of_seam`, `pairQuotientJ_analyticCyclicPair` (LatticeQuotient) | A seam map onto the period curve of ℤτ+ℤ with kernel ⟨u(1/N)⟩ forces target invariant j(Nτ). The proof transports along a variable change and lifts by the vendored `exists_differentiable_toPoint…`. The lift is z ↦ αz+c (vendored Liouville lemma), the preimage of the kernel is ℤτ+ℤ/N, and that lattice is homothetic to ℤNτ+ℤ. This is (b1). **ON THE SPOT (c)**; background Silverman AEC VI.4.1 UNVERIFIED. |
| `dense_transcendental_analyticJ` (Density) | (b3): the parameters with transcendental j are dense. Fibres of j are discrete (j is analytic and nonconstant by j-surjectivity), hence countable; the algebraic numbers are countable. |
| `pairQuotientJ_rationalPoints_comp` (GenericSpecialization) | `pairQuotientJ ∘ rationalPoints` commutes with every ℚ-embedding of algebraically closed fields of characteristic 0. Uses the cover lift and the vendored base-change lemma. |
| `pairQuotientJ_rationalPoints_of_transcendental`, `rationalPoints_rationalPointAtParameter_of_transcendental` | (b2): at a complex point with transcendental j-value, the point factors through `Kbar` by an embedding j ↦ x(J). Then `Y0RationalGenericQuotientJ_eval` gives quotient invariant = regular coordinate = j(Nτ). Item 1 then follows at those τ by `complexPairClass_eq_of_transcendental_coordinates`. |
| `hasGlobalRep`, `continuous_finitePointEval`, `continuous_rationalPointAtParameter` (ChartContinuity) | Every element of `modularFunctionField N` is, at every τ, the germ of one global meromorphic function (closure under field operations; generators j, j(N·)). Hence τ ↦ (value of a regular chart section at the analytic point) is continuous. |
| `continuous_g₂/g₃/weierstrassP/derivWeierstrassP` (PeriodContinuity) | g₂, g₃, ℘(1/N), ℘′(1/N) of ℤτ+ℤ are continuous in τ. The first three come from `WeberField`; ℘′ uses the majorant ≪‖v‖⁻³. |
| `markedLift`, `rationalPoints_analyticPoint`, `continuous_markedLift` (PairClass) | The classifying point of `(E_τ, u(1/N))` on the pinned short cover. Its coordinates are −g₂/4, −g₃/4, ℘(1/N), ℘′(1/N)/2, Δ⁻¹, all continuous. Its restriction reads `analyticCyclicPair τ`. Item 1 then follows by `Continuous.ext_on` on the dense set. |
| `exists_isCoprime_lift` (CoprimeLift), `analyticCyclicPair_eq_of_scale` (Homothety), `isScale_smul`, `exists_analyticCyclicPair_eq` (AnalyticClasses) | A primitive residue pair lifts to a coprime pair, so every cyclic subgroup is ⟨u((cτ₀+d)/N)⟩ with (c,d) the bottom row of some γ ∈ SL₂(ℤ). The homothety by cτ₀+d is a Weierstrass variable change u = cτ₀+d. Combined with j-surjectivity (`CMField2.exists_analyticJ_eq`), every complex class is `analyticCyclicPair (γτ₀)`. |
| `levelPoint`, `levelPairClass`, `branchParameter`, `branchPairClass`, `branchPairClass_eq`, `pairClass_conjunct` (Readings) | Level reading: `rationalPoints h₂` of the coordinate map. Branch reading: `analyticCyclicPair` of a parameter of the point; `branchPairClass_eq` shows it does not depend on which parameter is chosen. |

## What remains

| Item | Smallest faithful open statement | Reduction / reference |
| --- | --- | --- |
| 3. W_Q (exact Q) | For `Q ∣ N`, `Nat.Coprime Q (N/Q)`: (a) a level-side moduli operator σ_Q on complex points of `Y0Rational h₂`, defined as `(rationalPoints h₂).symm` of the class of `(E/C_Q, ψ(E[Q]+C))`. Here ψ is a seam point map of the actual Vélu composite (`exists_quotientSeam` with `n = Q`); the class does not depend on ψ because two seam maps with the same kernel differ by an automorphism of the target. (b) `σ_Q x ≫ e.hom = (x ≫ e.hom) ≫ rationalAtkin hQ` restricted to the chart, for every x. | By items 1–2 every point is `rationalPointAtParameter h₂ τ`, and `rationalAtkin_rationalPointAtParameter` gives the matrix translate. What is missing is the lattice computation of the image subgroup under ψ. This needs: the lift identity `toPoint₂(αz+c) = ψ(toPoint z)` extracted from the proof of `j_eq_analyticJN_of_seam`; that the function-field isomorphism along a Weierstrass variable change acts on points by the variable change (only `Nonempty` iso in the vendor); and the Atkin–Lehner matrix lattice identity. Moduli form **ON THE SPOT (c)** (Ogg 1974 p. 450 analytic; Conrad 2007 only quotient maps; full data in the References note below, UNVERIFIED). Atkin–Lehner, *Hecke operators on Γ₀(m)*, Math. Ann. 185 (1970), for the matrix only, UNVERIFIED. Silverman AEC 2009 III.4.11–4.12 UNVERIFIED. |
| 4. Good Hecke | Branch: for p prime, `p ∤ N`, the multiset of chart points at `pτ` and `(τ+b)/p` (b = 0..p−1) for any parameter τ of y. This needs (i) lifting `complexPoint N σ` back to `RationalCurveComplexPoints (branchFiniteOverQ N)` (open immersion lift over ℚ); (ii) independence of τ via `X0Branch.complexPoint_eq_iff`, where Γ₀(N) permutes the p+1 representatives of Γ₀(N) diag(1,p) Γ₀(N). Level: the multiset of `(E/D, image C)` over the p+1 subgroups D of order p, with image under a seam map. Comparison: the p+1 lattices of index p (`ℤ(τ+b)/p + ℤ`, `ℤτ + ℤ/p`) via `j_eq_analyticJN_of_seam`-style lifts and `analyticCyclicPair_eq_of_scale`. | Diamond–Shurman, *A First Course in Modular Forms*, 2005, §5.2 UNVERIFIED. No correspondence object is introduced. |
| 5. Assembly | `GenericReadings` for `Y0Rational h₂` and `branchFiniteOverQ N` with actual `atkinLehner` and `hecke`, then the comparison for `e = rationalOpenIsoOverQ h₂`. | The j conjunct is `rationalOpen_pairJ`; the pair conjunct is `pairClass_conjunct`; the param conjunct is associativity (`rationalOpenIso_hom_comp`, `restrictParametrization_point`), not a comparison result. The W_Q and Hecke conjuncts wait on items 3–4. |

`GenericFibreComparison` (`ZInQKernel/Contrib/OneProof/RC/ModelLevels/GenericComparison.lean:36`, quantifier at `:45`) quantifies only over `Q ∣ N` with `Nat.Coprime Q (N / Q)`, so the non-exact case never enters the comparison and no identity filler is needed in a conjunct. `GoodRow.extension` (`RC/PMWire/Model.lean:59`) uses `q.Prime` with `0 < N.factorization q`, i.e. `W_{q^{v_q(N)}}`, an exact divisor. The manuscript uses `W_{p^e}` at tex 8487–8489. No consumer uses a non-exact Q.

## `PMWire.GoodRow` per-field table (`ZInQKernel/Contrib/OneProof/RC/PMWire/Model.lean:35`)

| Field | Status | Supplier / owner lane |
| --- | --- | --- |
| `closed`, `M`, `smoothM`, `reducedM`, `separatedM`, `denseGeneric` | supplied upstream | `Pinned.Y0Level` (rc-model-levels3) |
| `source` | supplied upstream | ModelNeron `source`, `chartField` (rc-model-neron) |
| `E`, `groupE`, `neron`, `jE`, `properGenericE`, `geomIntGenericE` | supplied upstream | rc-model-neron (local Néron target) |
| `readComplex`, `readComplex_eq` | open | target lane (rc-model-target) |
| `point` | open | same-place comparison (hCM lane v21g) |
| `extension` | open | detector Atkin–Lehner lane; generic input is item 3 here (open) |
| `point_W` | open | detector Atkin–Lehner lane |
| `read`, `read_frob` | open | target lane |
| `point_frob`, `frobenius_sq` | open | same-place comparison (hCM lane) |

None of these is supplied by this task.

## What this supports (no retirement)

- The generic identity needed by detector specialization for `ExtendsAtkin` (`RC/PMWire/Generic.lean:150`, `rationalW` at `:139`) is item 3. It sits behind `GoodRow.extension` (`Model.lean:59`) and `point_W` (`:61`); `W_generic` (`:98`) is a projection of `extension`. Items 1–2 give it its pointwise footing: every complex point of the open is an analytic point with the actual class, so the remaining W_Q work is purely the lattice image computation.
- The generic side of `Relations.hecke` and `eigen` (`RC/PMWire/Operators.lean:144–145`) is item 4. Items 1–2 give the branch operator a well-defined domain.

## Tiers for detector specialization

| Tier | Statement | Reference |
| --- | --- | --- |
| Small after item 3 | Generic σ_Q equals `rationalAtkin hQ` on the open, by separatedness and density (`AtkinRational.ext_model_of_chart`, `RC/AtkinRational/Model.lean:232`) once agreement holds at all complex points. | — |
| Medium | Specialization of σ_Q and the good Hecke neighbours over the strict henselian DVR at the detector. | Katz–Mazur, *Arithmetic Moduli of Elliptic Curves*, Ann. of Math. Studies 108, Princeton Univ. Press, 1985; the section locator §2.4 could not be checked (no access to the print) and is UNVERIFIED; background only. (For W_Q this tier is superseded: rc-model-generic5 constructs the integral operator on the pinned model, `ModelGeneric5.extendsAtkin_Wint`.) |
| Downstream | Same-place comparison (supersingular pair classes, Frobenius). | hCM lane; Cornut–Jetchev 2010 §§4.9–4.10 UNVERIFIED. |

## Known issues

- Inherited: the Milne locators at tex 1784–1788 do not state the normalized-newform and Hecke claims.
- Inherited: Jetchev–Kane (arXiv v1), cited at tex 8468–8474, refers the class correspondence to Ribet 1990 Prop. 3.3 and does not print the Hecke, Atkin–Lehner or Frobenius compatibilities. Ribet's Prop. 3.3 and Rem. 3.5 are reported with proofs deferred (to Milne 1979, Carayol 1986 and Vignéras); they are never sources. Every item of this chain is UNVERIFIED: K. A. Ribet, *On modular representations of Gal(Q̄/Q) arising from modular forms*, Invent. Math. 100 (1990) (UNVERIFIED); J. S. Milne, *Points on Shimura varieties mod p*, Proc. Sympos. Pure Math. 33, Part 2 (1979) (UNVERIFIED); H. Carayol, *Sur la mauvaise réduction des courbes de Shimura*, Compositio Math. 59 (1986) (UNVERIFIED); M.-F. Vignéras, *Arithmétique des algèbres de quaternions*, Lecture Notes in Math. 800, Springer, 1980 (UNVERIFIED). The level-N correspondence is being built in the hCM lane.
- `GenericFibreComparison` (`ZInQKernel/Contrib/OneProof/RC/ModelLevels/GenericComparison.lean:36`) has no consumer: `git grep` finds only its definition, its `#print axioms` and a docstring in `ModelGeneric4/Readings.lean`. Item 5 of this run (the pair-class conjunct) therefore feeds nothing downstream; the consumed targets are `GoodRow.extension`, `point_W` and the stage-prime hypotheses (re-aimed in rc-model-generic5).

## References note (added by rc-model-generic5; all UNVERIFIED)

- A. P. Ogg, *Hyperelliptic modular curves*, Bull. Soc. Math. France 102 (1974), 449–462 (UNVERIFIED; defines w_M analytically).
- B. Conrad, *Arithmetic moduli of generalized elliptic curves*, J. Inst. Math. Jussieu 6 (2007), no. 2, 209–278 (UNVERIFIED; quotient maps only, no moduli form of W_Q).
- The vendored order-two Vélu step has no function-field map; this task constructs one (`twoFFHom`).
- The vendored function-field isomorphism along a Weierstrass variable change is only `Nonempty`, with no point formula. The kernel computation here goes around this by cardinality (`isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj` plus one containment). Item 3 will need the point formula.
- `PeriodContinuity` imports `WeberField`, which pulls a large dependency chain (a long first build).

## Manuscript check

| TeX lines | Verdict | Step |
| --- | --- | --- |
| 8476–8479 | supporting (generic fibre) | "The modular curve has good reduction": every complex point of the pinned rational open is an analytic point with the actual class (items 1–2), so the generic fibre is the open of the fixed curve compatibly with j and the pair reading. |
| 8476–8479 | supporting (generic fibre) | The vendored Vélu quotient of the period curve by ⟨1/N⟩ has invariant j(Nτ) (b1), at every level including powers of two. |
| 8478–8479 | OK | The parametrization conjunct is associativity of the restriction (inherited `restrictParametrization_point`). |
| 8479–8487 | unverified | Good Hecke correspondences: the generic pointwise comparison is open (item 4). |
| 8487–8489 | unverified | W_{p^e}: only exact divisors are used; the generic moduli comparison is open (item 3). |
| 8489–8492 | unverified | Frobenius and the same-place comparisons are downstream. |
| 9101–9113 | unverified | The unaveraged weighted comparison uses the reduced parametrization values; not touched here. |
| 1784–1788 | unverified | Inherited citation scope. |
