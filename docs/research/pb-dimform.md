# pb-dimform: Pan's and Berger's leaves in Fontaine's dimension form; model independence of pst; the literal `B_cris^+`

Task pb-dimform, 2026-11-17. Base: `wip/lane74b` 6b404a20 (contains `wip/pb-p1` 0d4cf145 and its bypass fold
`ZInQKernel/OneProof/H/TailZ77.lean`, top module `TailZ79`). No other branch merged. Results log:
`scratch/pb-dimform/log.md`. Model work; no person has reviewed it.

Marks: **VERIFIED** (compiled here, or read in a print by the fleet's print reader, which counts as read under the
owner's 11-17 rule), **STANDARD** (published, exact reference), **UNVERIFIED** (from memory), **on-the-spot** (a
step in neither the manuscript nor a source it cites).

## 1. Result

**(a)+(d) Both leaves are restated in place in Fontaine's dimension form, and the folded chain recompiles.**
`PanPrintedF` (R12) and `BergerSurveyF` (R11) keep their names and their Lean text. Only the predicate under them,
`FontaineSt.IsPstF`, changed. It used to be the basis form `IsAdmissibleT` (a `B_st`-basis of `B_st ⊗ V` made of
`G_K`-invariant vectors). It is now bst-construct's `BergerBst.IsAdmissible`,
`dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`, over the same ring `BstFOf`. This is Brinon-Conrad's
definition (§5.2 pp. 67-68; potentially semistable: Thm 9.3.5 p. 148). Consequences:

* The leaves need no dimension-to-basis step, and so no `G_K`-regularity of `B_st`.
* `panBerger_of_F` compiles with no change to its proof. Berger's conclusion `IsPstF ρ_E`, on the de Rham model
  `ρ_E`, is Pan's hypothesis `LocalIsPstF` on that same model.
* VERIFIED: `lake build ZInQKernel.Contrib.OneProof.PstModel ZInQKernel.OneProof.Main` succeeds, so TailZ77-TailZ79
  and `ZInQ.OneProof.frozenTarget` recompile over the dimension form. Every new or changed theorem uses only
  `[propext, Classical.choice, Quot.sound]` (§6).

**(b) Model independence of pst is proved** (VERIFIED, new file `ZInQKernel/Contrib/OneProof/PstModel.lean`).

* For `E ⊆ L` and `ρ_L = ρ_E ⊗_E L`, `IsAdmissible B H ρ_E ↔ IsAdmissible B H ρ_L` for every subring
  `B ⊆ B_dR` and every subgroup `H` (`isAdmissible_iff_of_basis`, `isAdmissible_iff_of_le`).
* Hence pst on one finite model of a `ℚ̄_p`-valued `ρ` is pst on every finite model: `isPstF_model_iff`,
  `localIsPstF_iff_of_model`, `localIsPstF_iff_forall`.
* So the model clause of `PanPrintedF` ("pst on some finite `E`-model") is the print's model-free hypothesis
  "the restriction of ρ at p is potentially semi-stable".

**(c) The literal printed set of survey II.3.1 equals `BcrisPlusOf`** (VERIFIED, `bcrisPlusOf_eq_printed`). The set is
`{Σ x_n ω^n/n! : x_n ∈ B̃^+ = A_inf[1/p], x_n → 0}`, with `x_n → 0` read `p`-adically in `A_inf[1/p]`
(`A_inf` an open lattice), the topology Brinon-Conrad p. 129 fixes for `A_cris`.

**Docstrings re-cited** (the lead's two additions, done in the same commit as the restatement, 977d924d):

* The definitions `AcrisOf`, `BcrisPlusOf`, `BcrisOf`, `BstFOf`, `IsPstF` and the two leaves now cite Brinon-Conrad
  at the reader's locators.
* `BstFOf` cites Brinon-Conrad Def. 9.2.3 p. 138, p. 142 and Thm 9.2.10 p. 143 instead of the survey's misprinted
  II.3.3 series, and it notes the two misprints.

**Ratings this feeds (proposal; the final ratings are the lead's).**

* `bergerSurveyF`. The objection "dimension implies basis needs regularity" is gone, because the conclusion is now
  the dimension form. What remains is provenance (b): the survey is not in the bibliography. The statement is Berger
  2002 Thm 0.6 = Thm 5.19 (arXiv v3), with definitions from Brinon-Conrad. Two smaller residues stay on the record:
  * Berger's `B_st` versus Fontaine's: Known issue (ii).
  * The new conclusion is weaker than the old one (`bergerSurveyF_of_basis`), so the leaf is a consequence of the
    print in either reading of "admissible": the survey I.2.3 / Brinon-Conrad dimension form, or Berger 2002 p. 8's
    basis form.
  * Proposed: LEAF (consequence of Berger 2002 Thm 0.6 = Thm 5.19 (arXiv v3)), with flag (ii).
* `panPrintedF`. Both deciding points of the review are settled:
  1. The model clause: `localIsPstF_iff_forall`.
  2. "In the sense of Fontaine": Brinon-Conrad, inside the bibliography, at definition level, in the dimension form.
     That is now the Lean predicate itself, so no step of the form "basis is at least as strong" is needed.
  * Proposed: LEAF (published; direct instance of Pan arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, cited at L756).

## 2. Exact before and after of each restated statement

### 2.1 The predicate (`ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean`, `FontaineSt`)

Before (pb-p1, base 6b404a20, `PanBergerFontaine.lean:396`; copy in
`scratch/pb-dimform/PanBergerFontaine.before.lean.txt`):

```lean
def IsPstF {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsAdmissibleT p (BstFOf p h w hw) K.fixingSubgroup ρ
```

with `IsAdmissibleT B H ρ := ∃ (ι : Type) (b : Basis ι B (B ⊗[ℚ_[p]] (Fin n → E))), ∀ i, inclT p B (b i) ∈
tensorInv p (bdrLin p) H ρ` (`PanBergerPst.lean:524`).

After (pb-dimform, `PanBergerFontaine.lean:418`):

```lean
def IsPstF {ε₀ : PreTilt 𝓞_ℂ_[p] p} (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) (ρ : GQp p →* GL (Fin n) E) : Prop :=
  ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K ∧
    IsAdmissible p (BstFOf p h w hw) K.fixingSubgroup ρ
```

with `IsAdmissible B H ρ := finrank (fixedSub p B H) (dB p B H ρ) = finrank ℚ_[p] (Fin n → E)`
(`BergerBst.lean:347`). Here `fixedSub p B H = B^H` and `dB p B H ρ = (B ⊗_{ℚ_p} E^n)^H`, with the invariance
computed in `B_dR ⊗ E^n`.

The old predicate is kept as `IsPstFBasis` (and `LocalIsPstFBasis`). `isPstF_of_basis` proves `IsPstFBasis →
IsPstF` (via `isAdmissible_of_T`, `bstF_stable`, `bstFOf_eq_xi`). The converse needs the `G_K`-regularity of
`B_st` and is not proved.

`LocalIsPstF` is unchanged as text (`PanBergerFontaine.lean:433`): `∃ E finite ⊆ ℚ̄_p, ∃ ρ_E` with
`GL.map (algebraMap E ℚ̄_p) ∘ ρ_E = ρ` and `IsPstF ρ_E`. It now means the dimension form through `IsPstF`.

### 2.2 `BergerSurveyF` (R11, field `bergerSurveyF`)

The Lean text is unchanged, before and after (`PanBergerFontaine.lean:647` before, `:717` after):

```lean
def BergerSurveyF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (n : ℕ) (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
      (ρE : GQp p →* GL (Fin n) E),
      Continuous ρE → IsDeRhamU p ρE → IsPstF p h w hw ρE
```

* Before, the conclusion `IsPstF` unfolded to "for some finite `K`, `B_st ⊗ V ≃ B_st^d` as `B_st[G_K]`-modules"
  (basis form).
* After, it unfolds to "for some finite `K`, `dim_{B_st^{G_K}} (B_st ⊗_{ℚ_p} V)^{G_K} = dim_{ℚ_p} V`".
* The new statement is implied by the old one, kept as `BergerSurveyFBasis` (`bergerSurveyF_of_basis`). It is
  weaker.
* Docstring: Berger, Invent. Math. 148, cited at L739, Thm 0.6 = Thm 5.19 (arXiv v3), with the survey's IV.5.1 read
  as the same theorem. Definitions from Brinon-Conrad.

### 2.3 `PanPrintedF` (R12, field `panPrintedF`)

The Lean text is unchanged, before and after (`:674` before, `:763` after):

```lean
def PanPrintedF : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (ε₀ : PreTilt 𝓞_ℂ_[p] p) (h : IsGenEps p ε₀) (w : Ainf p)
    (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0),
    RingHom.ker (WittVector.fontaineTheta 𝓞_ℂ_[p] p) = Ideal.span {w} →
    ∀ (ιp : PadicAlgCl p ≃+* ℂ) (ρ : GaloisRep p 2),
    IsIrreducibleP ρ → ρ.FinitelyRamified → LocalIsPstF p h w hw 2 (ρ.restrictLocal p) → ρ.IsOdd →
    LocalDistinctHTP p (ρ.restrictLocal p) →
    ∃ (N : ℕ) (_ : NeZero N) (k : ℤ) (g : HeckeRing.GL2.EigenformAwayFromLevel N k)
      (ρg : GaloisRep p 2) (ψ : GaloisChar p),
      IsAttachedVia p ιp g ρg ∧ IsTwistOf p ρ ρg ψ
```

* Before, the hypothesis `LocalIsPstF` was "on some finite model, for some finite `K`, `B_st ⊗ V ≃ B_st^d`
  equivariantly" (basis form, stronger than the print's).
* After, it is "on some finite model, for some finite `K`, `dim_{B_st^{G_K}} D_st,K(V) = dim V`". This is the print
  with Brinon-Conrad's definitions. By `localIsPstF_iff_forall` it is the same as pst on every model.
* The new leaf implies the old one, kept as `PanPrintedFBasis` (`panPrintedFBasis_of_F`; weaker hypothesis).
* Docstring: Pan arXiv:1901.07166v2 Thm 1.0.4 with Conj. 1.0.1, cited at L756-757. "In the sense of Fontaine" is
  read in Brinon-Conrad Thm 9.3.5 p. 148 and §5.2 pp. 67-68.

### 2.4 `panBerger_of_F` (role kept)

Signature and proof are unchanged: `PanPrintedF → BergerSurveyF → DSThm965Printed → EigenformCoeffFieldFinite →
DSThm966Printed → PanBerger`. It passes the predicate through.

### 2.5 Other declarations in `PanBergerFontaine.lean`

* Renamed, because they read the basis form:
  * `isPstT_of_F` → `isPstT_of_FBasis`;
  * `bergerPrintedVT_of_survey` → `bergerPrintedVT_of_surveyBasis`;
  * `bergerPrintedV_of_survey` → `bergerPrintedV_of_surveyBasis`.
  * They now take `IsPstFBasis` / `BergerSurveyFBasis`. None is used by the fold. The old field `bergerPrintedV`
    (tree `B_st`, basis form) is not derivable from the dimension-form `BergerSurveyF` without the regularity of
    `B_st`.
* New:
  * `IsPstFBasis`, `LocalIsPstFBasis`, `BergerSurveyFBasis`, `PanPrintedFBasis` (pb-p1's forms);
  * `isPstF_of_basis`, `localIsPstF_of_basis`, `bergerSurveyF_of_basis`, `panPrintedFBasis_of_F`, `bstFOf_eq_xi`.
* `BmaxStToFontaine` and `panPrintedP_of_F` are unchanged as text. They now concern the dimension form, and neither
  is used by the fold. The docstring of `BmaxStToFontaine` no longer lists regularity as needed.

## 3. Model independence (item (b)), `PstModel.lean` §1-§5

The proof is on-the-spot: it is in neither the manuscript nor a cited source, and it is standard.

* `rank_fin_pi` / `finrank_fin_pi`: over a commutative domain `R`, `rank (M^d) = d · rank M` for every module `M`,
  with no freeness. Proof: rank-nullity (`IsDomain.hasRankNullity`) for `fst : M × M^d → M`.
  * `B^H = fixedSub p B H` is a domain, as a subring of the field `B_dR`. Lean does not know it is a field
    (Fontaine: `B_st^{G_K} = K_0`), so the rank is taken over a domain.
* `phiE b : (E^n)^d ≃ₗ[ℚ_p] L^n`, `(v_j) ↦ (Σ_j v_j(i) b_j)_i`, for an `E`-basis `b` of `L`. It is equivariant
  (`phiE_equivariant`) when `ρ_L = GL.map (algebraMap E L) ∘ ρ_E`.
* `psi`: `A ⊗ L^n ≃ (A ⊗ E^n)^d`, linear over any `S` acting on `A` (via `AlgebraTensorModule.congr` and
  `TensorProduct.piRight`). It commutes with `B ⊆ B_dR` (`psi_inclT`) and with the `G`-action (`psi_act`).
* `dBEquiv : D_{B,H}(L^n) ≃ₗ[B^H] D_{B,H}(E^n)^d`.
* `isAdmissible_iff_of_basis`: `IsAdmissible B H ρ_L ↔ IsAdmissible B H ρ_E`. Both sides of the dimension equality
  are multiplied by `d = [L:E] > 0`.
* `isAdmissible_iff_of_le` gives the same for intermediate fields `E ≤ L` of `ℚ̄_p`, with the two models agreeing
  in `GL_n(ℚ̄_p)`.
* `isPstF_iff_of_le`, then `isPstF_model_iff`: compare both models with the model over `E ⊔ E'`.
* `localIsPstF_iff_of_model`: for any model `ρ_E` of `ρ`, `LocalIsPstF ρ ↔ IsPstF ρ_E`.
* `localIsPstF_iff_forall`: `LocalIsPstF ρ ↔ (a model exists) ∧ (every model is pst)`.

The statement holds for every subring `B ⊆ B_dR` (in particular `B_dR` itself). It is the Lean form of the
manuscript's sentence at L10973-10974 ("Extension of the coefficient field is, on underlying `ℚ_ℓ`-representations,
a finite direct sum"), for admissibility in the dimension form.

## 4. The literal printed `B_cris^+` (item (c)), `PstModel.lean` §6

```lean
def PAdicNullLoc (c : ℕ → AinfP p) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∃ a : Ainf p, c n = algebraMap (Ainf p) (AinfP p) ((p : Ainf p) ^ k * a)

def BcrisPlusPrinted (w : Ainf p) (hw : WittVector.fontaineTheta 𝓞_ℂ_[p] p w = 0) : Set (BdR p) :=
  {x | ∃ c : ℕ → AinfP p, PAdicNullLoc p c ∧
    x = toBdR p (evalB p (algebraMap_mem_ith p hw)
      (PowerSeries.mk fun n => c n * qpToLoc p (((n.factorial : ℕ) : ℚ_[p]))⁻¹))}

theorem bcrisPlusPrinted_eq_set : BcrisPlusPrinted p w hw = BcrisPlusSet p w hw
theorem bcrisPlusOf_eq_printed : (BcrisPlusOf p w hw : Set (BdR p)) = BcrisPlusPrinted p w hw
```

* This is survey II.3.1 p. 13 verbatim in structure: `x_n ∈ B̃^+ = A_inf[1/p]` (`AinfP`), `x_n → 0`, and
  `Σ x_n ω^n/n!` evaluated `ker θ`-adically in `B_dR^+`, for any `w ∈ ker θ` in place of `ω`.
* Reading: `x_n → 0` `p`-adically in `A_inf[1/p]`, i.e. eventually in `p^k A_inf` for every `k`. The survey names no
  topology. Brinon-Conrad p. 129 uses the `p`-adic one for `A_cris`. Under this reading the on-the-spot
  weak-topology rearrangement of pb-p1.md §6.1 is not needed.
* Proof:
  * printed ⊆ `p^{−K} A_cris`: the null sequence is eventually in `A_inf`, and the finitely many earlier terms have
    bounded denominators, so `p^K x_n = a_n ∈ A_inf` with `a_n → 0`, using `A_inf → A_inf[1/p]` injective.
  * Conversely, `x_n = p^{−k} a_n`.
* With pb-p1's `bcrisPlusOf_eq_set` this gives `BcrisPlusOf`.

## 5. Known issues (sources)

(i) **Berger 2002, `log[π̄]`.**
  * §1.2 p. 11 of arXiv:math/0102179v3 prints `log[π̄]` as the series for `log(π̄^(0)) + log([π̄]/π̄^(0))`.
  * That divides by `π̄^(0) ∈ 𝓞_ℂ_p`, which is not in `B_dR^+`.
  * So the definition is literal for `p̃` (whose `p̃^(0) = p` is invertible in `ℚ_p`) but not for `π̄ = ε − 1`.
  * A faithful definition needs the `p`-adic logarithm of his Prop. 2.23 (pp. 23-24), which the tree lacks.
  * Not used here: our `B_st` is Fontaine's (Brinon-Conrad), built on `log[p̃]`. (VERIFIED by pb-p1's reading.)

(ii) **Berger's `B_st` versus Fontaine's.**
  * Berger 2002 p. 11 says his `B_st` is "légèrement différente de celle de Fontaine, mais le foncteur `D_st` est le
    même". This is asserted without proof.
  * Our Berger leaf is stated over Fontaine's `B_st` (Brinon-Conrad Def. 9.2.3, p. 142, Thm 9.2.10). Reading Berger's
    Thm 0.6 with Fontaine's pst relies on that assertion, or on the survey IV.5.1, which proves the theorem with
    Fontaine's ring. The survey is outside the bibliography.
  * Fontaine's sense itself is sourced inside the bibliography: Brinon-Conrad, cited at L10972-10974, with the
    locators read by the fleet's print reader (§5.2 pp. 67-68, Def. 9.1.4 p. 131, Def. 9.2.3 p. 138, p. 142,
    Thm 9.2.10 p. 143, Thm 9.3.5 p. 148, p. 129).

(iii) **Berger's survey (arXiv:math/0210184v1), II.3.3 pp. 14-15: two misprints** (fleet print reader, VERIFIED as a
reading):
  * the series for `log[p̃]` is printed with exponent `n − 1` where it must be `n`. The Lean has `n`, which agrees
    with Brinon-Conrad p. 142.
  * Frobenius is printed as `φ(Y) = Y^p`; the standard is `pY`. This has no effect on the Lean, which has no
    Frobenius.
  * `BstFOf`'s docstring no longer quotes the survey's series. It cites Brinon-Conrad and notes both misprints.

(iv) **Survey II.3.1** does not name the topology in which `x_n → 0`. Resolved by Brinon-Conrad p. 129 (`p`-adic)
and §4 above.

## 6. Checks (VERIFIED)

* `lake build ZInQKernel.Contrib.OneProof.PanBergerFontaine`: succeeds (`scratch/pb-dimform/build2.txt`).
* `lake build ZInQKernel.Contrib.OneProof.PstModel ZInQKernel.OneProof.Main`: Build completed successfully (15975 jobs)
  (summary in `scratch/pb-dimform/build3.summary.txt`; the 9 MB log was not kept). TailZ77, TailZ78, TailZ79 and
  `Main` were rebuilt; `ZInQ.OneProof.frozenTarget` depends on `[propext, Classical.choice, Quot.sound]`.
* `scratch/pb-dimform/Discharges.lean` (`#discharges` and `#print axioms` of every new or changed theorem, of
  `HDec.HSyn.sixContactMin_of_open72` and of `ZInQ.OneProof.frozenTarget`): all 40 `#print axioms` lines are
  `[propext, Classical.choice, Quot.sound]`, with no errors (`scratch/pb-dimform/discharges.txt`).
  * `#discharges` lists one new line touching this work:
    `DISCHARGES [OpenResearchLeaves53.bergerSurveyF] by HDec.PkgI4.PanDict.bergerSurveyF_of_basis`, still assuming
    `[HDec.PkgI4.PanDict.BergerSurveyFBasis]`.
  * This is not a discharge to fold. It reduces the field to pb-p1's stronger basis-form leaf, which is a step
    backwards.
  * Nothing for `panPrintedF`.
* The in-place route did not break, so no regenerated bypass fold is needed.
* No field is discharged: both fields stay, restated. So no autofold dry run was done (per the task).
* `scratch/pb-dimform/PstModelCore.lean` is the scratch copy of `PstModel.lean` (same body). It compiles with
  `lake env lean`.

**Not done / stale text outside my edit scope.** The field docstrings in `ZInQKernel/OneProof/H/TailZ77.lean`
(lines 40 and 68) still say "basis form" and cite the survey for the rings. The rows `panPrintedF` and
`bergerSurveyF` of `docs/one-proof/kinds.tsv` say the same. I was not allowed to edit them. Proposed replacement
wording, for integration:

* `panPrintedF`: "... printed form with 'potentially semi-stable in the sense of Fontaine' in Fontaine's dimension
  form (Brinon-Conrad §5.2 pp. 67-68, Thm 9.3.5 p. 148) over Fontaine's `B_st = B_cris[log p~]` inside `B_dR`
  (Brinon-Conrad Def. 9.2.3 p. 138, p. 142, Thm 9.2.10 p. 143), on a model `V = E^n` (model-independent:
  `PstModel.localIsPstF_iff_forall`)".
* `bergerSurveyF`: "... potentially semistable over Fontaine's `B_st` (Brinon-Conrad, as above), dimension form
  (Brinon-Conrad §5.2; survey I.2.3)".

## 7. Manuscript check

One line per step of `diophantine_zq.tex` that this work formalizes or relies on.

* **L738-741** ("Berger's p-adic monodromy theorem [berger2002] makes this de Rham representation potentially
  semistable, as required by Pan's theorem"): **gap filled**.
  * The step needs three things the manuscript does not give:
    1. a locator: Thm 0.6 = Thm 5.19 (arXiv v3);
    2. pst on the `E`-coefficient model, not only on a `ℚ_ℓ`-representation: supplied by `isPstF_model_iff` /
       `localIsPstF_iff_forall` (Lean, on-the-spot);
    3. that Berger's "potentially semistable" is Pan's "in the sense of Fontaine". Berger's `B_st` differs from
       Fontaine's, with `D_st` the same by his unproved remark (Known issue (ii)). We state Berger's theorem
       directly over Fontaine's ring (Brinon-Conrad); the survey IV.5.1 proves it so.
  * With the dimension form used on both sides, the predicate passes from Berger to Pan unchanged (`panBerger_of_F`).
* **L756-757** ("Apply [Theorem 1.0.4]{pan2022} at ℓ=5; there is no residual-image proviso at this prime"): **OK**.
  * Per the review's page read of arXiv:1901.07166v2 pp. 2, 5-7: the residual condition is at `p = 3` only, the leaf
    is stated for `p ≥ 5`, geometric Frobenius, `HT(ε) = −1`. Not re-read here.
  * Pan's hypothesis "potentially semi-stable in the sense of Fontaine" is now the Lean predicate, with
    Brinon-Conrad's definitions.
* **L10972-10974** ("De Rham representations are closed under duals and subquotients [brinon-conrad Thm 5.2.1,
  Prop. 6.3.3]. Extension of the coefficient field is, on underlying `ℚ_ℓ`-representations, a finite direct sum"):
  * The direct-sum sentence: **OK**. It is formalized for admissibility (dimension form) over every subring
    `B ⊆ B_dR`: `phiE`, `dBEquiv`, `isAdmissible_iff_of_basis`.
  * The closure under duals and subquotients: **unverified** (not part of this task; Brinon-Conrad's Thm 5.2.1 and
    Prop. 6.3.3 not read here).
* **L11019-11023** (bibitem brinon-conrad, preliminary version June 24, 2009): **OK**. It is the source of every
  period-ring definition used by the two leaves, at the reader's locators (§5 (ii)). Note: the bibitem lists only
  Thm 5.2.1 and Props. 6.3.3, 6.3.8. The definitions used here (pp. 67-68, 129-148) are additional locators, not
  claims of the manuscript.
* **L11037-11040** (bibitem berger2002, "p-adic monodromy theorem", no theorem number): **gap filled**. Locator
  supplied: Thm 0.6 = Thm 5.19 (arXiv:math/0102179v3); Thm 0.7 there is Sen's theorem.
* **L11041-11045** (bibitem pan2022, arXiv:1901.07166v2, Theorem 1.0.4, "the version used here"): **OK**.

## 8. Deliverables

* `ZInQKernel/Contrib/OneProof/PanBergerFontaine.lean` (edited in place).
* `ZInQKernel/Contrib/OneProof/PstModel.lean` (new; imports `PanBergerFontaine`; not imported by the chain).
* `scratch/pb-dimform/`:
  * `log.md`, `bc-reading.md` (the host's note on the Brinon-Conrad / survey readings);
  * `PanBergerFontaine.before.lean.txt`;
  * `PstModelCore.lean`, `Discharges.lean`, `discharges.txt`;
  * `build2.txt`, `build3.txt`.
* `.fleet/pb-dimform.md`.
