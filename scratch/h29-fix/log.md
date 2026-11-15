# h29-fix results log

Base: origin/wip/h29-split 14503253. Contributor file under revision: copy of
`ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean` (not edited in place; revised copy in scratch/h29-fix/).

## Step 1. Computations (2026-11-15)

* `brandt.py` (output `brandt-output.txt`), exact arithmetic. Model X = O_B^x \ (O_B/4O_B)^x (derivation in
  report §2). VERIFIED:
  - #X = 8, every left O_B^x-orbit has 24 elements (TYZ Lemma 2.5, L646-651: 8 classes, uniform measure).
  - the 8 elements 1 + 2x, x = a i + b j + c zeta (a,b,c in {0,1}), represent the 8 classes (Lemma 2.5, first map).
  - chi_0 o nrd on 1+2x is (-1)^c = (-1)^{tr x}.
  - dim A_0^U (orthogonal to 1 and chi_0 o nrd) = 6 (TYZ Thm 2.4(1), L777).
  - Hecke: for every odd prime p < 40, T_p = a_p(E) on A_0^U (a_p by point count of y^2 = x^3 - x);
    T_p 1 = (p+1) 1, T_p chi_0 = chi_0(p)(p+1) chi_0. [the unprinted bridge, checked for p < 40]
  - n = 3, all 8 admissible tau (tau(sqrt -3) = +-i +-j +-k): pi^{U_3} one-dimensional (TYZ Thm 2.6),
    integral generator f_3 takes values {1, -3} or {-1, 3}; **Q(3) = f_3(1) = +-3** for every tau
    (Cl_3 = 1, so 2Cl_3 = {1}).
  - n = 11 (4 taus), n = 19 (3 taus): one-dimensional, Q(n) = +-1.
* `lcal_small.py` (PARI 40 digits, output `lcal-output.txt`): TYZ's L(n)^2 = 1 at n = 1, 3, 11, 19; 4 at 17;
  0 at 41. VERIFIED numerically (19 digits).
* Verdict at n = 3: Lemma 2.9 printed (L1062-1066) says eps L(3) L(1) = Q(3), i.e. +-1 = +-3: FALSE.
  Theorem 2.1 (L554-559) at (d1,d2) = (3,1): P(3,1) = Q(3) (Cl_3 = 1, chi trivial) = +-2^{1-1} w_K L(3) L(1) = +-3:
  TRUE. **Lemma 2.9 is misprinted** (the factor w_K of Theorem 2.1 is dropped in its statement; the proof
  L1068-1077 gives w_K * sum = Q(n)). At n = 11, 19 (w_K = 1) both agree (+-1).
* `regular_form.py` (output `regular-output.txt`): every n = 1 (mod 8), n <= 10^6, is x^2 + y^2 + 16 z^2; the
  integers <= 10^6 not represented are exactly n = 3 (4), 6 (8), 12 (16), 4^a(8k+7). VERIFIED (exhaustive).
* Mathlib 4.35 has no three-square theorem (grep for three_sq / sum_three / three squares in
  .lake/packages/mathlib/Mathlib: only Nat.sum_four_squares). VERIFIED.

## Step 2. Revised contribution (scratch/h29-fix/TYZLemma29Mod2.lean), compiled 2026-11-15

Changes against ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean (h29-split):
* `wK m := if m = 3 then 3 else 1`; `Lemma29Printed`/`Lemma29At`: `wK m * Σ ε ℓℓ = Q m` (disjunction removed).
* `Prop23Cong`, `Prop23Odd`, `TYZTestVectorExists`, `TYZProp23Printed`: `1 < n` added (weakening; n = 1 unused).
* `InPiZ`: Hecke pin (apE, hurwitzNorm, quatOf: removed) replaced by TYZ's printed description of pi^U = A_0^U:
  sums over the 8 Lemma-2.5 representatives `twoRep v t = ιAt v (1 + 2x)`, x = a i + b j + c ζ, of f and of
  (-1)^c f vanish (`twoRepQ`, `twoRep`, `chi0Rep`). New `exists_isPlaceTwo` (the place 2 exists).
* `TYZTestVectorExists`: `∃ f, IsTestVector n τ f ∧ ∃ x : ℍ[AQ]ˣ, f x ≠ 0`.
* New glue: `wK_cast`, `tv_eq_of_toClassGroup_eq` (f ∘ τ̂ constant on classes), `genusPeriodTV_eq_of_section`;
  `odd_on_sqClasses` reproved through it.
* `LegendreJonesPall` now proved (`legendreJonesPall_of`) from `LegendreThreeSquares` and `JonesPallX2Y2Z16`;
  new top theorem `tyzLemma29Mod2_of_printedLeaves_legendre`.

Compile: `lake env lean scratch/h29-fix/TYZLemma29Mod2.lean`: no errors (warnings: deprecated dif_pos, as before).
`check.sh` → `DischargesH29Fix-output.txt` (VERIFIED):
  DISCHARGES [h29] by ...tyzLemma29Mod2_of_printedLeaves_legendre
    still assumes: [LegendreThreeSquares, JonesPallX2Y2Z16, TYZTestVectorExists, TYZLemma29Printed, TYZProp23Printed]
    axioms: [propext, Classical.choice, Quot.sound]
  `h29fix_frozenTarget` (Theorem 1.1 with h29 replaced by the five): axioms [propext, Classical.choice, Quot.sound].
  #discharges: 66 open hypotheses, 1289 theorems checked, 6 discharge one.

## Step 3. Genus periods with class groups (brandt2.py, output brandt2-output.txt)

Extension of the model: right action of the uniformizer 1 + tau(sqrt -n) for n = 1 (mod 8) (via lambda = 1 + i);
an O_K-ideal a of odd norm N maps (as an idele, through tau-hat) to the class of conj(gamma), gamma in tau(a) O_B of
norm N (class number one of O_B); 2Cl_n from PARI bnfinit/bnfisprincipal. 19 values of n (2 embeddings tau each,
38 runs; n = 1 (8): 17, 33, 41, 57, 73, 89, 97, 105, 113; n = 3 (8): 3, 11, 19, 35, 43, 51, 59, 67, 83, 123),
L-values from PARI. VERIFIED (exact for Q(n), 8+ digits for L):
* pi^{U_n} is one-dimensional in every run (TYZ Thm 2.6 at chi = 1);
* f_n is odd at every class of 2Cl_n (TYZ Prop 2.3 restricted to K^-hat^x);
* Q(n) lies in { w_K * sum_{pairs} eps L(d1) L(d2) : eps = +-1 } in every run (the corrected Lemma 2.9 leaf),
  e.g. Q(17) = +-2 (L(17)^2 = 4), Q(41) = 0 (L(41) = 0), Q(113) = 4, Q(43) = +-3 (L(43)^2 = 9, w_K = 1),
  Q(51) = +-3 = +-(L(51) + 2 L(3)L(17)) form, Q(59) = +-1 with #2Cl = 3.
* With w_K = 1 at n = 3 it would fail (Q(3) = +-3, L(3) = +-1); n = 43 shows +-3 is a genuine value when L = +-3.

## Step 4. Second read (fresh model agent, given the code and the TYZ line ranges, not this report)

No errors. Ratings: all five LEAF. Notes recorded:
* InPiZ matches TYZ's pi_Z^{U_n} using printed facts only (representatives 1+2x, chi_0 = (-1)^c, nrd(U) gives only
  chi = 1, chi_0); Un = U K_{n,2}^x (L924) checked; RnHat = prod_p R_{n,p}.
* w_K form re-derived from (PQ), genus theory (h_2 = k resp. k-1), Lemma 2.8 and Thm 2.1: w_K sum eps L L = Q(n).
* Independent of brandt.py: with tau(omega) = zeta, f_3 = f_0 of Thm 2.6, f_0(1) = 3, so Q(3) = +-3; TYZ's printed
  Thm 2.1 and Lemma 2.9 are inconsistent at n = 3 by their own statements.
* Weakness (harmless): Thm 2.4(2)'s lattice "pi_Z^U" has index 16 in the integer-valued elements of pi^U; the leaf
  uses integer-valued elements (TYZ's definition of pi_Z, L540), and on the line pi^{U_n} the generator pi(g) f_0 is
  primitive, so "free of rank 1" holds for it.
* Not verified by the reader: Tau Ceti API orientation, lValOne/omegaTYZ, wording of Jones-Pall Thm 5.
