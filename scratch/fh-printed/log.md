# fh-printed results log

Base 43513d87 (leaf-fold25). Prebuilt tree copied from ~/dzq-check2 (bc90deac, same Lean files).

## Plan (statements)
- Printed leaf: FH 1995 Thm B with (a) local conditions chi_v = chi0,v as norm-residue (Hilbert symbol)
  characters of Q_p^x / R^x, (b) chi as the idele class character of Q(sqrt d) (d squarefree),
  its Dirichlet coefficients from local components at unramified p, (c) root number = sign of the
  FE of the completed L-function for some conductor q (no conductor theorem), (d) "infinitely many"
  as Set.Infinite. L-value read as G(1) (step iii, remains a reading).
- Dictionary steps proved in Lean: local chars equal => D/D0 square in Q_p and D D0 > 0, D = 1 mod 4;
  idelic chi_d(n) = jacobiSym n |d| for d odd fundamental; Set.Infinite => forall B exists |D| > B.

## Compile log
- 11-15 06:10 scratch/fh-printed/LocalNorm.lean: IsLocalNorm, Hensel (p odd, p = 2 mod 8),
  descent lemma, p not a norm (unramified nonsquare), nonsquare unit not a norm (ramified): COMPILES (VERIFIED).
- 11-15 06:40 LocalNorm.lean: + p=2 non-norms (2 for d=5 mod 8, -1 for d=3 mod 4, 5 for d=2 mod 4), unit norms (p odd, p=2), infinity, isSquare_div_of_localNorm_iff (odd p), isSquare_div_two_of_localNorm_iff: COMPILES (VERIFIED)
- 11-15 07:05 LocalNorm.lean: + charAtPrime, idelicChar (character of Q(sqrt d) from local components), charAtPrime_eq_jacobiSym, idelicChar_eq_jacobiSym (d = 1 mod 4 squarefree), charAtPrime_two_of_ramified: COMPILES (VERIFIED)
- 11-15 ~07:30 scratch/fh-printed/Statement.lean (imports FHNonvanishing.TwistFE and the new module
  ZInQKernel/Contrib/OneProof/FHPrinted/LocalNorm.lean): FriedbergHoffsteinB_Printed (leaf),
  friedbergHoffsteinB_FE_of_printed, rootNumberTwistEqOne_iff (RootNumberTwistEqOne f D0 <->
  chi_D0(-N) eps(f) = 1), friedbergHoffsteinB_printed_of_FE, friedbergHoffsteinB_printed_iff_FE:
  COMPILE, axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
- 11-15 06:27 (host clock) deliverable ZInQKernel/Contrib/OneProof/FriedbergHoffsteinBFE.lean + helper
  FHPrinted/LocalNorm.lean: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
  +ZInQKernel.Contrib.OneProof.FriedbergHoffsteinBFE` OK (12996 jobs). scratch/fh-printed/Discharges.lean:
  DISCHARGES [hFH] by ZInQ.FHPrinted.friedbergHoffsteinB_FE_of_printed, still assumes
  [ZInQ.FHPrinted.FriedbergHoffsteinB_Printed], axioms standard; fhprinted_frozenTarget (frozenTarget with hFH
  replaced) standard axioms. Output: scratch/fh-printed/Discharges-output.txt (VERIFIED).
- 11-15 ~06:40 rebuilt after docstring edits; #discharges rerun: same DISCHARGES [hFH] line, 1918 theorems checked
  (nonvacuity lemma exists_isEntireCont_printedTwistCoeff added). scratch/fh-printed/LocalNorm.lean = copy of the
  module; scratch/fh-printed/Statement.lean = development copy (superseded by FriedbergHoffsteinBFE.lean).
- Report docs/research/fh-printed.md written. Rating: new leaf printed except reading (iii) (classical L-function
  of pi_f x chi_d); equivalent in Lean to FriedbergHoffsteinB_FE.
