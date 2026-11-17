# dprm-scout results log

Base: origin/wip/h10-compose 346db1d6, origin/main merged (07e9d9ee).

## Target
`hZ : ¬ ComputablePred ZInQ.Contrib.H10Reduction.IntCodeSolvable`, premise of
`ZInQ.OneProof.rationalH10` (ZInQKernel/OneProof/RationalH10.lean). It is a direct hypothesis of that
theorem, not a field of a `frozenTarget` bundle (VERIFIED, read).

## Mathlib inventory (VERIFIED, read in .lake/packages/mathlib)
- Dioph.lean: `IsPoly`, `Poly`, `Dioph S := ∃ β p, ∀ v, v ∈ S ↔ ∃ t, p (v ⊗ t) = 0` (β any type in the
  same universe), closure: `Dioph.inter`, `Dioph.union`, `Dioph.ex_dioph`, `Dioph.ex1_dioph`,
  `Dioph.reindex_dioph`, `Dioph.DiophList.forall`, `Dioph.dom_dioph`, `Dioph.diophFn_comp`,
  `Dioph.dioph_comp`, `eq_dioph`, `add_dioph`, `mul_dioph`, `le_dioph`, `lt_dioph`, `ne_dioph`,
  `sub_dioph`, `dvd_dioph`, `mod_dioph`, `modEq_dioph`, `div_dioph`, `pell_dioph`, `xn_dioph`,
  `pow_dioph` ("A version of Matiyasevic's theorem": exponentiation is Diophantine).
  No bounded universal quantifier, no binomial coefficient / factorial / prime, no r.e. ⇒ Dioph.
- PellMatiyasevic.lean: `Pell.matiyasevic`, `Pell.eq_pow_of_pell`, `Pell.xn/yn` and their lemmas.
- Computability: `Nat.Partrec.Code`, `Code.eval`, `Code.evaln`, `Code.exists_code`, `Code.primrec_evaln`,
  `Code.smn`, `Code.fixed_point`; RE.lean `REPred`, `ComputablePred`, `ComputablePred.to_re`,
  `computable_iff_re_compl_re`; Halting.lean `ComputablePred.halting_problem_re`,
  `ComputablePred.halting_problem`, `halting_problem_not_re`, `rice`, `rice₂`;
  Reduce.lean `ManyOneReducible`, `ComputablePred.computable_of_manyOneReducible`;
  TuringMachine/ToPartrec.lean (partial recursive → TM).
- NumberTheory/SumFourSquares.lean: `Nat.sum_four_squares`.
- MvPolynomial: `exists_fin_rename`, `eval₂Hom_bind₁`.

## Lean
- ZInQKernel/Contrib/OneProof/IntegerH10.lean (new): leaf `DPRMNat`; glue
  `haltSet_re`, `haltSet_not_computable`, `four_squares_iff`, `manyOne_of_poly`,
  `not_computable_intCodeSolvable_of_dprm`, `rational_not_computable_of_frozenTarget_dprm`.

## Compile outcomes (VERIFIED)
- `lake build ZInQKernel.Contrib.H10Reduction`: 9847 jobs, success (03:36).
- `lake env lean ZInQKernel/Contrib/OneProof/IntegerH10.lean`: errors fixed in 3 iterations
  (four-squares succ case: `finProdFinEquiv.symm` unfolded by simp; fixed by a separate `hz` lemma and
  `rw`); final run: no errors, no warnings.
- `lake build ZInQKernel.Contrib.OneProof.IntegerH10`: success (9848 jobs).
- Axioms (scratch/dprm-scout/axioms-output.txt): `not_computable_intCodeSolvable_of_dprm`,
  `not_computable_intCodeSolvable_of_dprmDioph`, `rational_not_computable_of_frozenTarget_dprm`,
  `dprmNat_of_dprmDioph`: [propext, Classical.choice, Quot.sound].

## Statements proved
- `not_computable_intCodeSolvable_of_dprm : DPRMNat → ¬ComputablePred IntCodeSolvable`
- `rational_not_computable_of_frozenTarget_dprm : FrozenTarget → DPRMNat → ¬ComputablePred RatCodeSolvable`
- `dprmNat_of_dprmDioph : DPRMDioph → DPRMNat`

## Findings
- No hypothesis on #150's coding is needed (only `code_complete`, public, is used).
- After merging origin/main, `frozenTarget` takes OpenResearchLeaves40/OpenTextbookLeaves17 but
  RationalH10.lean (wip/h10-compose) passes OpenResearchLeaves38/OpenTextbookLeaves16: needs a binder
  update at integration (not compiled here; outside write scope).
- hZ is not a frozenTarget hypothesis, so autofold.py does not apply; autofold.json records the intended
  replacement with a note.
