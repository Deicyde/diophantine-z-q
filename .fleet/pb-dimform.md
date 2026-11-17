# pb-dimform (fleet note)

**Result.** Pan's and Berger's leaves (`PanPrintedF`, `BergerSurveyF`) are restated in place in Fontaine's dimension
form. `FontaineSt.IsPstF` is now `∃ K finite, IsAdmissible (BstFOf) G_K ρ`, i.e.
`dim_{B_st^{G_K}} (B_st ⊗ V)^{G_K} = dim V`, as in Brinon-Conrad §5.2 / Thm 9.3.5 (in the bibliography). The old
predicate was the basis form.

* The leaf texts and names are unchanged, and so is `panBerger_of_F`, which passes the predicate from Berger's
  conclusion to Pan's hypothesis on the same model.
* No dimension-to-basis step (and so no `G_K`-regularity of `B_st`) is needed.
* The old basis forms are kept as `*Basis`. Comparison lemmas: the new Berger leaf is weaker than the old one, and
  the new Pan leaf implies the old one.
* Docstrings are re-cited to Brinon-Conrad. `BstFOf` no longer quotes the survey's misprinted II.3.3 series.

**Also proved** (new file `ZInQKernel/Contrib/OneProof/PstModel.lean`):

* (b) Model independence of pst: `isPstF_model_iff`, `localIsPstF_iff_forall`, from
  `D_B(L^n) ≅ D_B(E^n)^{[L:E]}` over `B^H`, for any `B ⊆ B_dR`.
* (c) The literal survey II.3.1 set `{Σ x_n ω^n/n! : x_n ∈ A_inf[1/p], x_n → 0 p-adically}` equals `BcrisPlusOf`
  (`bcrisPlusOf_eq_printed`).

**Compiles** (VERIFIED):

* `lake build ZInQKernel.Contrib.OneProof.PstModel ZInQKernel.OneProof.Main`: Build completed successfully (15975
  jobs). TailZ77-TailZ79 and `Main` recompiled over the dimension form.
* `#print axioms`: standard axioms only, for 40 declarations, including `frozenTarget` and `sixContactMin_of_open72`.
* `#discharges`: nothing new to fold. The only new line reduces `bergerSurveyF` to its stronger basis form.

**Ratings proposed** (report §1):

* `panPrintedF`: LEAF. Both of the review's deciding points are settled: model independence, and Fontaine's sense
  from Brinon-Conrad.
* `bergerSurveyF`: LEAF, a consequence of Berger 2002 Thm 0.6 = Thm 5.19 (arXiv v3). Flag: Berger's `B_st` versus
  Fontaine's, "same D_st" asserted without proof (Known issue (ii)).

**Remains.**

* The field docstrings in `OneProof/H/TailZ77.lean` (lines 40, 68) and the rows in `docs/one-proof/kinds.tsv` still
  say "basis form". They are outside my edit scope; replacement wording is proposed in report §6.
* No field was discharged, so no autofold was run.
* Manuscript check: report §7. L738-741 is "gap filled": locator, coefficient models, Berger versus Fontaine `B_st`.
  L756-757, L10973-74 (direct sum) and the bibitems are OK. Closure under duals and subquotients is unverified.

Report: `docs/research/pb-dimform.md`.

Commits: 977d924d (in-place restatement), 6201cf6b (report); this note is the last commit.
