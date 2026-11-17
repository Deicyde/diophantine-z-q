# dprm-scout: integer H10 for #150's coding from one printed leaf (DPRM)

## Result

The integer-H10 premise of the rational Hilbert 10 theorem,

```lean
hZ : ¬ ComputablePred ZInQ.Contrib.H10Reduction.IntCodeSolvable
```

(premise of `ZInQ.OneProof.rationalH10`, `ZInQKernel/OneProof/RationalH10.lean`, for the raw-code coding of
upstream PR #150, `ZInQKernel/Contrib/H10Reduction.lean`), is **proved from one printed leaf**, the DPRM
theorem for subsets of `ℕ`, stated over Mathlib's own definitions; all glue is proved in Lean.
File: `ZInQKernel/Contrib/OneProof/IntegerH10.lean`, namespace `ZInQ.Contrib.IntegerH10`.

```lean
/-- DPRM (Matiyasevich 1970; Davis, Amer. Math. Monthly 80 (1973)) for subsets of ℕ. -/
def DPRMNat : Prop :=
  ∀ p : ℕ → Prop, REPred p →
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 1)) ℤ), ∀ x : ℕ,
      p x ↔ ∃ y : Fin n → ℕ, eval (fun i => ((Fin.cons x y : Fin (n + 1) → ℕ) i : ℤ)) Q = 0

theorem not_computable_intCodeSolvable_of_dprm (h : DPRMNat) :
    ¬ ComputablePred IntCodeSolvable

theorem rational_not_computable_of_frozenTarget_dprm (h : ZInQ.FrozenTarget) (hD : DPRMNat) :
    ¬ ComputablePred RatCodeSolvable
```

The same leaf in Mathlib's `Dioph` form (`DPRMDioph : ∀ p : ℕ → Prop, REPred p → Dioph {v : Fin2 1 → ℕ |
p (v Fin2.fz)}`) implies `DPRMNat` (`dprmNat_of_dprmDioph`, proved), so either may be the leaf
(`not_computable_intCodeSolvable_of_dprmDioph`).

No hypothesis on #150's coding is needed: the reduction only uses codes it builds itself, and
`code_complete` (public in #150) supplies a code for the fixed part. Malformed codes (decoding to `0`) are
irrelevant for undecidability, since only a many-one reduction *into* `IntCodeSolvable` is used.

Compile status: COMPILE_STATUS

## The leaf, rated

`DPRMNat` — **printed form** (a consequence of the printed theorem, never stronger), flag
"unread: new printed leaf, no reading recorded" (no copy of the print on this host; locators UNVERIFIED).

* Print: Yu. V. Matiyasevich, "Enumerable sets are Diophantine", Dokl. Akad. Nauk SSSR 191 (1970) 279–282
  (Soviet Math. Dokl. 11 (1970) 354–357), completing M. Davis, H. Putnam, J. Robinson, "The decision problem
  for exponential Diophantine equations", Ann. of Math. 74 (1961) 425–436; exposition M. Davis, "Hilbert's
  tenth problem is unsolvable", Amer. Math. Monthly 80 (1973) 233–269, main theorem: a set is Diophantine iff
  it is recursively enumerable. Also Matiyasevich, *Hilbert's Tenth Problem*, MIT Press 1993, Ch. 5
  (UNVERIFIED chapter). Volume/page numbers are STANDARD bibliographic data recalled, not read here: UNVERIFIED.
* Gaps between print and Lean statement, each harmless and in the weakening direction:
  1. *Arity.* The print is for sets of n-tuples; `DPRMNat` is the case n = 1 (a consequence).
  2. *Number convention.* Davis 1973 may work with positive integers (UNVERIFIED); Matiyasevich's book works
     with ℕ including 0 (UNVERIFIED). The ℕ form follows from the positive-integer form by the substitution
     `x ↦ x+1`, `yᵢ ↦ yᵢ+1` on the polynomial and the shift of the set (r.e. is preserved): routine glue, not
     done in Lean here since the leaf is stated in the ℕ convention.
  3. *"Recursively enumerable".* Mathlib's `REPred p` is "`p` is the domain of a partial recursive function"
     (`Partrec`, i.e. μ-recursive under Mathlib's `Primcodable ℕ` coding, the identity). The print's r.e. (Davis:
     the set is the range or domain of a partial recursive function, or Σ₁) is equivalent by the standard
     equivalence of these definitions (Kleene); this is definitional, not mathematical, content.
  4. *Polynomial.* The print's "polynomial with integer coefficients in finitely many unknowns" is
     `MvPolynomial (Fin (n+1)) ℤ`, unknowns ranging over ℕ: literal.
* `DPRMDioph` is the same theorem with Mathlib's `Dioph`, whose unknowns range over an arbitrary type `β`;
  it is weaker than (implied by) the printed finite-unknown form, and implies `DPRMNat` here, so it is also a
  printed-form leaf.

## The glue (all proved)

| node | content | status |
| --- | --- | --- |
| `haltSet`, `haltSet_re`, `haltSet_not_computable` | `{x | Code.eval (ofNat Code x) 0 halts}` is r.e. and not computable; from Mathlib's `ComputablePred.halting_problem_re 0`, `ComputablePred.halting_problem 0` via `Denumerable.ofNat`/`encode` | proved |
| `sq4`, `four_squares_iff` | natural unknowns ↦ four integer squares each (`Nat.sum_four_squares`), via `bind₁` | proved |
| `tailCode`, `eval_decode_tail`, `tailCode_primrec` | the parameter-dependent code `-2x·X₀ + x²` and its primitive recursiveness | proved |
| `manyOne_of_poly` | a ℕ-Diophantine predicate many-one reduces to `IntCodeSolvable`: `x ↦ (4n+1, encode (c₀ ++ tailCode x))` with `c₀` a code (by #150's `code_complete`) of `Q₄² + X₀²`, so the decoded polynomial is `Q₄² + (X₀ − x)²` | proved |
| `not_computable_intCodeSolvable_of_dprm` | `hZ` from `DPRMNat` | proved |
| `rational_not_computable_of_frozenTarget_dprm` | #150's `rational_not_computable_of_frozenTarget` with `hZ` discharged | proved |
| `isPoly_eq_eval`, `dprmNat_of_dprmDioph` | Mathlib `Poly` is an `MvPolynomial` evaluation; finitely many unknowns via `exists_fin_rename` and `Function.extend` | proved |

## Integration notes

* `hZ` is a plain premise of `ZInQ.OneProof.rationalH10`, not a field of a `frozenTarget` bundle, so
  `#discharges` (which matches bundle fields and `frozenTarget`'s arguments) and `autofold.py` (which folds
  bundle fields) do not apply to it. `scratch/dprm-scout/autofold.json` records the intended replacement in
  the spec format for the integrator, with that caveat. The composite for the integrator is a one-line change
  of `rationalH10`: replace `hZ` by `(hD : ZInQ.Contrib.IntegerH10.DPRMNat)` and pass
  `(ZInQ.Contrib.IntegerH10.not_computable_intCodeSolvable_of_dprm hD)`.
* After merging origin/main (07e9d9ee), `frozenTarget` takes `OpenResearchLeaves40`/`OpenTextbookLeaves17`,
  while `RationalH10.lean` (from wip/h10-compose) still passes `OpenResearchLeaves38`/`OpenTextbookLeaves16`:
  that file needs its two binder types updated when h10-compose is merged into main (not edited here:
  outside this task's write scope; not compiled here).
* The contribution imports only `ZInQKernel.Contrib.H10Reduction` and Mathlib (never `OneProof.Main`).

## Road map: proving DPRM itself in Lean over Mathlib (no deep attempt)

Dependency tree (status: **proved** = in Lean, sorry-free; **open** = not in Lean; Mathlib names VERIFIED by
reading; literature numbering UNVERIFIED).

```
hZ = ¬ ComputablePred IntCodeSolvable ............................ proved from DPRMNat (this task)
├─ halting set r.e., not computable ............................... proved (Mathlib halting_problem_re/halting_problem)
├─ ℕ-unknowns → ℤ-unknowns (four squares) ......................... proved (Nat.sum_four_squares)
├─ encoding into #150's raw codes ................................. proved (code_complete, tailCode)
└─ DPRMNat ........................................................ LEAF (printed form); open in Lean
   └─ DPRMDioph ⇒ DPRMNat ......................................... proved (dprmNat_of_dprmDioph)
      └─ DPRMDioph (Route A below)
         ├─ A0 exponentiation Diophantine ......................... proved (Mathlib Dioph.pow_dioph)
         ├─ A1 binomial coefficient Diophantine ................... open, glue (small)
         ├─ A2 factorial Diophantine .............................. open, glue (small–moderate)
         ├─ A3 bounded universal quantifier ....................... open; published (Davis–Putnam–Robinson 1961)
         ├─ A4 Nat.Primrec graphs Diophantine ..................... open, glue (moderate; needs A3)
         └─ A5 REPred ⇒ ∃k of a Primrec relation .................. open, glue (small; Mathlib Code.evaln API)
```

**Route A (recommended): Davis 1973 / Davis–Putnam–Robinson with Matiyasevich's lemma, over Mathlib's
`Nat.Primrec` and `Code.evaln`.**

* **A0. Exponentiation is Diophantine.** Mathlib `Dioph.pow_dioph` (from `Pell.matiyasevic`,
  `Pell.eq_pow_of_pell`). Proved. This is Matiyasevich's 1970 contribution, the deep step.
* **A1. Binomial coefficients.** `z = C(n,k)` iff, with `u = 2^n + 1`, `z = ⌊(u+1)^n / u^k⌋ mod u`
  (Davis 1973, lemma on `C(n,k)`, numbering UNVERIFIED; the identity is elementary). From `pow_dioph`,
  `div_dioph`, `mod_dioph`, `Nat.choose`, `add_pow`. Missing: the base-`u` digit argument (all coefficients
  `< u`). Small.
* **A2. Factorial.** `m = n!` via `n! = ⌊r^n / C(r,n)⌋` for `r > (2n)^{n+1}` (Davis 1973, UNVERIFIED
  numbering). From A1, `div_dioph`; missing: the inequality estimate. Small–moderate.
* **A3. Bounded universal quantifier** (Davis–Putnam–Robinson 1961; Davis 1973, theorem on bounded
  universal quantifiers, UNVERIFIED numbering; Matiyasevich 1993 Ch. 6 UNVERIFIED). Lean target:
  `Dioph S → Dioph {v | ∀ k < v i, k ::ₒ v ∈ S}` (shape to be fixed against Mathlib's `Option α → ℕ`
  conventions). Proof: bound the witnesses by a majorant polynomial, take `t = Q!`, use the pairwise coprime
  moduli `1 + (k+1)t` and the Chinese remainder theorem, and express `∏_k (1+(k+1)t)` through A1/A2.
  Mathlib supplies `Nat.chineseRemainderOfList`, `Nat.Coprime`, `Nat.factorial`, `Nat.choose`,
  `Finset.prod`, `Nat.ModEq`. The largest piece; it can be stated as its own published leaf if Route A is
  split among contributors.
* **A4. Primitive recursive graphs are Diophantine.** `Nat.Primrec f → Dioph {v : Fin2 2 → ℕ | f (v 0) = v 1}`
  by induction on Mathlib's `Nat.Primrec` (constructors `zero`, `succ`, `left`, `right`, `pair`, `comp`,
  `prec`). `Nat.pair`/`Nat.unpair` are Diophantine (polynomial plus `Nat.sqrt`, itself Diophantine by
  `s² ≤ n < (s+1)²`); `comp` by `Dioph.ex_dioph`; `prec` by coding the value sequence with Gödel's β-function
  (`c mod (1 + (i+1)d)`, `mod_dioph`) and A3. Moderate glue.
* **A5. r.e. predicates.** `REPred p` is `Partrec (fun a => Part.assert (p a) …)`; with
  `Nat.Partrec.Code.exists_code`, `Code.evaln_complete` ((∃ k, x ∈ evaln k c n) ↔ x ∈ eval c n) and
  `Code.primrec_evaln`, `p x ↔ ∃ k, (evaln k c x).isSome`, a Primrec relation, so `Dioph.ex_dioph` and A4
  give `DPRMDioph`. Small glue over existing API (`Partrec.nat_iff`, `Partrec.bind_decode₂_iff`).

**Route B: register machines** (Jones–Matiyasevich, "Register machine proof of the theorem on exponential
Diophantine representation of enumerable sets", J. Symbolic Logic 49 (1984), UNVERIFIED locator). The masking
relation `a ≼ b` (binary digitwise) is exponential Diophantine via Lucas (`C(b,a)` odd); a register machine run
is arithmetized as an exponential Diophantine system; A0 removes the exponentials. Mathlib supplies A0,
`Nat.choose`, Lucas' theorem (`Choose.lucas_theorem`, `Choose.choose_modEq_prod_range_choose`), Turing machines
`Turing.TM0/TM1/TM2` and `Turing.ToPartrec` (codes to a stack machine); missing: a register (Minsky) machine
model, the simulation of `Partrec`/`Code` by it, the arithmetization and masking lemmas. This is the route of
the existing complete formalizations (Isabelle AFP entry "DPRM_Theorem", Bayer–David–Pal–Stock–Schleicher 2022;
Coq, Larchey-Wendling–Forster, "Hilbert's Tenth Problem in Coq", FSCD 2019, via FRACTRAN; both UNVERIFIED
locators, recalled). Route A fits Mathlib better (it reuses `Nat.Primrec`, `Code.evaln` and the `Dioph`
closure lemmas, and needs no new machine model); Route B has a worked formal template to port.

Size estimates (SPECULATIVE): A1+A2 a few hundred lines; A3 1,500–3,000 lines; A4 500–1,000; A5 under 300.

## Mathlib inventory (VERIFIED: read in `.lake/packages/mathlib`, Mathlib v4.35.0)

* `Mathlib/NumberTheory/Dioph.lean`: `IsPoly`, `Poly` (a `CommRing`), `Poly.sumsq`, `Poly.map`,
  `Dioph S := ∃ (β : Type u) (p : Poly (α ⊕ β)), ∀ v, v ∈ S ↔ ∃ t, p (v ⊗ t) = 0` (unknowns over an arbitrary
  type), `DiophPFun`, `DiophFn`; closure: `Dioph.ext`, `of_no_dummies`, `inject_dummies`, `reindex_dioph`,
  `DiophList.forall`, `inter`, `union`, `ex_dioph`, `ex1_dioph`, `dom_dioph`, `diophFn_iff_pFun`,
  `abs_poly_dioph`, `proj_dioph`, `diophPFun_comp1`, `diophFn_comp1`, `diophFn_vec_comp1`, `vec_ex1_dioph`,
  `diophFn_vec`, `diophPFun_vec`, `diophFn_compn`, `dioph_comp`, `diophFn_comp`, `proj_dioph_of_nat`,
  `const_dioph`, `dioph_comp2`, `diophFn_comp2`, `eq_dioph`, `add_dioph`, `mul_dioph`, `le_dioph`, `lt_dioph`,
  `ne_dioph`, `sub_dioph`, `dvd_dioph`, `mod_dioph`, `modEq_dioph`, `div_dioph`, `pell_dioph`, `xn_dioph`,
  `pow_dioph` ("a version of Matiyasevic's theorem"). Absent: bounded ∀, binomial, factorial, primes,
  r.e. ⇒ Diophantine, any link to `Computability`.
* `Mathlib/NumberTheory/PellMatiyasevic.lean`: `Pell.pell`, `xn`, `yn`, … , `Pell.matiyasevic`,
  `Pell.eq_pow_of_pell`.
* `Mathlib/Computability/Primrec/Basic.lean`: `Nat.Primrec` (zero, succ, left, right, pair, comp, prec),
  `Primcodable`, `Primrec`, `Primrec.ofNat`, `Primrec.encode`, `Primrec.decode`; `Primrec/List.lean`:
  `Primrec.list_cons`, `list_append`, `list_map`, `list_flatMap`.
* `Mathlib/Computability/Partrec.lean`: `Nat.Partrec`, `Partrec`, `Computable`, `Computable.ofNat`,
  `Partrec.comp`, `Partrec.nat_iff`, `Partrec.bind_decode₂_iff`, `Nat.rfind`, `Nat.rfindOpt`.
* `Mathlib/Computability/PartrecCode.lean`: `Nat.Partrec.Code`, `Code.eval`, `Code.evaln`, `exists_code`,
  `evaln_sound`, `evaln_complete`, `evaln_mono`, `primrec_evaln`, `eval_eq_rfindOpt`, `smn`, `fixed_point`.
* `Mathlib/Computability/RE.lean`: `REPred`, `ComputablePred`, `REPred.of_eq`, `Partrec.dom_re`,
  `ComputablePred.to_re`, `ComputablePred.computable_iff_re_compl_re`.
* `Mathlib/Computability/Halting.lean`: `ComputablePred.halting_problem_re`, `halting_problem`,
  `halting_problem_not_re`, `rice`, `rice₂`.
* `Mathlib/Computability/Reduce.lean`: `ManyOneReducible` (`≤₀`), `ComputablePred.computable_of_manyOneReducible`.
* `Mathlib/Computability/TuringMachine/*`: `Turing.TM0/TM1/TM2`, `Turing.ToPartrec`; no register machines.
* Other used: `Nat.sum_four_squares` (`NumberTheory/SumFourSquares.lean`), `MvPolynomial.exists_fin_rename`,
  `MvPolynomial.eval₂Hom_bind₁`, `Function.Injective.extend_apply`, `Choose.lucas_theorem`,
  `Nat.chineseRemainderOfList`.
