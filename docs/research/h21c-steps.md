# h21c-steps: `h21C` reduced to TYZ Theorem 2.1 over `π^U = ⊕ ℂ f_δ` (Theorem 2.4(1)), dictionary proved

**Main result.** The hypothesis `h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC` of `frozenTarget` is proved
equivalent, in Lean, to a new statement `h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span`. `h21S` is Tian–Yuan–Zhang
Theorem 2.1 (arXiv:1411.4728v1, L554–559) with `π_ℤ^{U_n}` read through the printed description of `π^U` in
Theorem 2.4(1) (L615–623): `π^U = ⊕_δ ℂ f_δ`, with TYZ's six forms `f_δ` defined in Lean. Every step between the
two statements is a Lean proof:

* TYZ Lemma 2.5, both directions of the bijectivity: surjectivity (`exists_twoRepU`) and the injectivity that was
  open (`twoRep_mem_DCU_iff`);
* the forms `f_δ` (`fDelta`), with their invariance;
* the equivalence `InPiZ n τ f ↔ InPiSpan n τ f` (`inPiZ_iff_inPiSpan`). This is character orthogonality on the 8
  classes, checked by `decide`, and uses **no measure**.

The passages the review listed (L715–720 `π ⊂ 𝒜₀`, Lemma 2.5's measure, L722–727) are no longer used. The only
printed input besides Theorem 2.1 is Theorem 2.4(1), and it enters as the definition of `π^U`.

**What was not achieved.** The task asked for two hypotheses, Theorem 2.1 and Theorem 2.4(1), each stated
separately as a direct instance. That split is **blocked**. Both theorems are about `π`, the Jacquet–Langlands
transfer of the newform of `y² = x³ − x`, and `π` has no Lean definition. Theorem 2.4(1) can only enter as the
substitution `π^U = span{f_δ}` inside Theorem 2.1. So the fold gives one new hypothesis in place of `h21C`:
**0 fields added**, and **−1 GLUE** if a reviewer rates `h21S` LEAF. My proposed rating is LEAF, as a composite
of Theorem 2.1 and Theorem 2.4(1) at the level of definitions; this is unreviewed.

All claims below are VERIFIED (compiled), unless they are marked otherwise.

## 1. Files

| file | content | status |
| --- | --- | --- |
| `ZInQKernel/Contrib/OneProof/TYZThm21Span/FDelta.lean` | `U4`, `GU`, `DCU`; Lemma 2.5 surjectivity and injectivity; `deltaQ`, `xRepQ`, `psiDelta`, `fDelta`; character orthogonality | builds (`lake build`), no sorry |
| `ZInQKernel/Contrib/OneProof/TYZThm21Span.lean` | `InPiSpan`, `IsTestVectorSpan`, `TYZThm21Span`; dictionary; `tyzThm21PairsC_of_span` and converse; non-vacuity | builds, no sorry |
| `scratch/h21c-steps/FoldCheck.lean` | hand fold of `Main.lean` (`frozenTarget_h21S`, `frozenTarget_h21S'`) | see §5 |
| `scratch/h21c-steps/Discharges.lean` | `#discharges` and axioms | see §5 |
| `scratch/h21c-steps/autofold.json`, `kinds-rows.tsv` | fold spec (manual: `h21C` is top level), kinds row of `h21S` | written |

Namespace: `ZInQ.Contrib.H21CSteps`. Both files import only `HfxProof.Sg` and `TYZThm11Genus`, never `OneProof.Main`.

## 2. The double coset space (TYZ L602–661)

* TYZ's `U` is `∏ U_p`, with `U_p = O_{B,p}^×` for odd `p` and `U_2 = ℤ_2^×(1 + 4O_{B,2})`. Lean uses
  `U4 = (1 + 4Ô_B)^×`, the units `w` with `(w−1)/4` and `(w⁻¹−1)/4` in `Ô_B` at every place, and
  `GU = ⟨U4, ℚ̂^×⟩`. Since `ℤ_2^×` (at `2`, `1` elsewhere) lies in `ℚ̂^×`, we have `ℚ̂^× U = ℚ̂^× U4`. This is a
  one-line fact, not formalized: the docstring states it.
* **Surjectivity** (`exists_twoRepU`): every unit of `B̂` lies in `B^× (1 + 2x_t) ℚ̂^× U` for some `t`. This copies
  hfx-proof's `exists_twoRep_of_unit`, whose correcting unit `w` already lies in `U4`.
* **Injectivity** (`twoRep_mem_DCU_iff`): the 8 double cosets are distinct.
  * The proof is hfx-proof's local obstruction (`twoRep_not_mem_DC`), generalized to `GU`. The local condition at
    `2` is `C0 = ℚ_2^× (ℤ_2 + 4O_{B,2})^×`; `GU_le_SgC` shows `GU ⊂ SgC C0`.
  * The 2-adic step is hfx-proof's `two_adic_b1` with `ω = 0`.
  * The finite check is `mod4_sep`, by `decide +kernel`: `μ β_t ≡ X β_{t'} (mod 4)` with `μ` one of the 24
    Hurwitz units forces `t = t'`.
* `GU_le_HgrpN`: `ℚ̂^× U ⊂ ⟨U_n, ℚ̂^×⟩`. This gives `π^{U_n} ⊂ π^U`.

## 3. The forms `f_δ` (Theorem 2.4(1), L615–623)

* `deltaQ`: the six representatives of `Δ/{±1}`, namely `(i+j)/2, (i−j)/2, (j+k)/2, (j−k)/2, (k+i)/2, (k−i)/2`.
* `xRepQ t = a i + b j + c ζ`, and `twoRepQ t = 1 + 2 x_t` (`twoRepQ_eq_one_add`).
* `psiDelta δ t = (−1)^{tr(δ x_t)}`, with `tr` the reduced trace of `ℍ[ℚ]`. In closed form (`psiDelta_eq_tab`,
  48 cases by `norm_num`) the exponents are `a+b+c, a+b, b+c, b, a+c, a`.
  * Together with `1` and `χ₀ = (−1)^c` (`chi0Rep`), these are the 8 characters of `(ℤ/2)^3`.
  * Check against the print (VERIFIED by hand): TYZ Theorem 2.4(3), `χ₀ f_{(i+j)/2} = f_{(i−j)/2}` and the two
    similar identities, agrees with this table.
* `fDelta δ` is the function on `B^× \ B̂^× / ℚ̂^× U` whose value is `ψ_δ(t)` on the class of `1 + 2x_t`. By Lemma
  2.5's bijectivity, this function is TYZ's `f_δ`: TYZ define `f_δ` on this space through its values at `1 + 2x`.
  * Invariance: `fDelta_eq_of_mem`. Values at the representatives: `fDelta_twoRep`.
  * Not formalized: the formula `f_δ(1 + 2x)` for a general `x ∈ O_{B,2}`, outside the 8 representatives. The
    statements do not need it.

## 4. The dictionary and the new leaf

* `InPiSpan n τ f` holds when two conditions hold:
  * `f` is integer valued and equals `Σ_δ c_δ f_δ` on `B̂^×`, for some `c : Fin 6 → ℂ`;
  * `f` is right `U_n`-invariant.

  This is `π_ℤ^{U_n}` with `π^U` taken from Theorem 2.4(1). It uses `U ⊂ U_n ℚ̂^×` (`GU_le_HgrpN`) and the
  trivial central character of `π` (L538–540).
* `fourier8`: a function on the 8 classes that is orthogonal to `1` and `χ₀` equals
  `Σ_δ ((1/8) Σ_s F(s) ψ_δ(s)) ψ_δ`. The proof combines `psi_orth`, by `decide`, with linear algebra.
* `inPiZ_iff_inPiSpan`, and from it `isTestVector_iff_span`.
* `exists_testVectorSpan` (non-vacuity): a nonzero test vector exists for every admissible `τ`. It comes from
  hfx-proof's `tyzTestVectorExists` through the dictionary.
* `TYZThm21Span` is `TYZThm21PairsC` word for word, except that `IsTestVector` is replaced by `IsTestVectorSpan`.
  * Proved: `tyzThm21PairsC_of_span : TYZThm21Span → TYZThm21PairsC`, and its converse `tyzThm21Span_of_pairsC`.
  * The restrictions are kept: odd classes, `n > 1`, and the first assertion only for pairs with no factor
    `≡ 1 (mod 8)`.

**Rating of the new leaf `h21S` (proposed: LEAF; printed form: yes, with one definition-level reading).**

* Theorem 2.1 is stated as printed, in the complex-sign form of h21C that tyz-genus and lcal-one argued is the
  print.
* Its object `π_ℤ^{U_n}` is built from Theorem 2.4(1)'s printed basis `f_δ`, which is defined in Lean from
  L620–622.
* No measure, no `𝒜₀` and no orthogonality reading remains.
* The reading in question: `π^U = ⊕ ℂ f_δ` is taken as Theorem 2.4(1) prints it. It cannot be checked in Lean,
  because `π` is not defined there.

## 5. Fold and checks

* Hand fold for `Main.lean`:
  * replace the binder `(h21C : ZInQ.Contrib.TYZGenusFold.TYZThm21PairsC)` by
    `(h21S : ZInQ.Contrib.H21CSteps.TYZThm21Span)`;
  * replace the two uses of `h21C` by `(ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span h21S)`;
  * add the import `ZInQKernel.Contrib.OneProof.TYZThm21Span`.
* Kinds: remove the `frozenTarget h21C` row and add the `h21S` row (`scratch/h21c-steps/kinds-rows.tsv`).
* FoldCheck (VERIFIED, compiled against `ZInQKernel.OneProof.Main` at base e1b31749):
  * `frozenTarget_h21S` (the new body) and `frozenTarget_h21S'` (through the current `frozenTarget`) both compile.
  * Both depend only on `[propext, Classical.choice, Quot.sound]`.
  * Output: `scratch/h21c-steps/FoldCheck-output.txt`.
* `#discharges` (VERIFIED; `scratch/h21c-steps/Discharges-output.txt`):

  ```
  DISCHARGES [h21C] by ZInQ.Contrib.H21CSteps.tyzThm21PairsC_of_span
    still assumes: [ZInQ.Contrib.H21CSteps.TYZThm21Span]
    axioms: [propext, Classical.choice, Quot.sound]
  ```

  `tyzThm21Span_of_pairsC`, `inPiZ_iff_inPiSpan`, `twoRep_mem_DCU_iff` and `exists_testVectorSpan` also use only
  the standard axioms.
* Locator row for `docs/research/locators.md`, to be added by the integrator. It is not edited here, because it is
  another task's file. Row: TYZ arXiv:1411.4728v1, Theorem 2.1 at L554–559 and Theorem 2.4(1) at L615–623, with
  `f_δ(1+2x) = (−1)^{tr(δx)}` at L620–622. Read on this host from `~/tyz-src/Period7.tex` (VERIFIED).

## 6. What remains

* A reviewer's rating of `h21S`, in particular the definition-level reading `π^U = ⊕ ℂ f_δ`.
* Not formalized:
  * the formula `f_δ(1 + 2x)` for a general `x ∈ O_{B,2}`, beyond the 8 representatives;
  * the identity `ℚ̂^× U = ℚ̂^× U4`, a one-line fact stated in a docstring. Lean uses `U4` throughout.
* The integrator applies the Main fold by hand.
