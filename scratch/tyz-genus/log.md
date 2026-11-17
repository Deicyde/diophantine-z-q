# tyz-genus results log

Task tyz-genus (2026-11-16). Base wip/leaf-fold33b 4da8d4f3; merged origin/main (up to date),
origin/wip/h29-proof, origin/wip/h11-reduce (clean merges). Build tree reflink-copied from ~/dzq-wt/leaf-fold33b
(identical Main.lean); `lake build TYZLemma29Genus TYZThm11Integral TYZProp23Printed` OK.

TYZ source ~/tyz-src/Period7.tex: NOT on this host (ls fails). TYZ line numbers below are quoted from earlier notes.

## Step 0: findings before Lean (VERIFIED by reading the files)

* F0.1 `TYZThm21Pairs` (TYZLemma29Genus.lean:91) quantifies over integer sign choices `ℓ : ℕ → ℤ` with
  `IsLcalSign ℓ` (`(ℓ m)^2 = lcalSq m` for every squarefree m ≡ 1,3 mod 8). As h11-reduce §1 found for
  `TYZLemma29PrintedNe3`, such a leaf is vacuous unless TYZ Thm 1.1 (= h11) holds, so h11 cannot be derived from
  `TYZThm21Pairs` (item (3) of the task is impossible in that form).
* F0.2 `TYZThm21Pairs` requires `1 < n`; the values L(1)^2 needs an instance with d1 d2 = 1, i.e. n = 1, which
  the leaf excludes; at n = 3, pair (3,1) only gives 𝓛(3)^2 𝓛(1)^2 = (Q(3)/3)^2 (product, not each factor).

## Step 1: TYZ Lemma 2.8 proved in Lean (no new leaf) — VERIFIED (compiled, standard axioms)

Files (helpers under ZInQKernel/Contrib/OneProof/TYZGenusFold/, development copies in scratch/tyz-genus/):
* Jacobi.lean: `jacobiSym_neg_absNorm` ((−n / N I) = 1 for N I prime to 2n, prime-ideal induction with
  `RouteK.Redei.prime_trichotomy`), `gchar_univ_mk0` (Π_{q|n} χ_q([I]) = χ₄(N I) for n ≡ 1 mod 4, Jacobi reciprocity).
* Local.lean: `dc_norm` (reduced norms on B^× twoRep(t) H), `chi0_eq_of_mem_DC`, `F_zero` (hp23's explicit
  generator F vanishes where χ₀ = −1: twist by chi0Rep + rank one + F odd at the class of 1).
* Ideles.lean: idele `aK = E·α + (1 − E)` (E = image of the idempotent of 𝔸ᶠ_ℚ at the primes of m), `τ̂(aK)`
  componentwise, `toClassGroup_aKU` (class [I] when (α) = I M, M + (N I) = O; by counts, Tau Ceti
  `finprod_unitOfPrime_zpow_count`, `count_toPrincipalIdeal_eq_neg_log_valuation`).
* Class.lean: `exists_mk0_coprime_nat`, `exists_alpha`, `normSq_tau`, `tv_zero_of_gchar` (f_n(τ̂ t) = 0 when
  Π_q χ_q(t) = −1, n ≡ 1 mod 8), `tyzLemma28Sym : TYZLemma28Sym`,
  `tyzLemma29PrintedNe3_of_thm21Pairs : TYZThm21Pairs → TYZLemma29PrintedNe3`.
* `#print axioms` for both: [propext, Classical.choice, Quot.sound].

Proof idea (differs from h29-proof §4's twist sketch only in organisation): for a class t pick I ∈ t integral
with N I prime to 2n and α ∈ I with (α) = I M, M + (N I) = O; the idele aK (N I) α lies in t. If
τ̂(aK) ∈ B^× twoRep(t') H, reduced norms give: v_r(g · N I) even at odd r (g = nrd γ), and g·nrd(twoRep t') ∈
2^ℤ(1+4ℤ₂) at 2; so N I · nrd(twoRep t') ≢ 3 (mod 4). With χ_U(t) = χ₄(N I): χ_U(t) = −1 ⇒ t'.2.2 ≠ 0 ⇒ F(t') = 0
⇒ f_n(τ̂ t) = 0. Hence χ_{T^c} f_n = χ_T f_n termwise.

## Step 2: contribution file, #discharges, manual fold — VERIFIED (compiled)

* Helpers moved to ZInQKernel/Contrib/OneProof/TYZGenusFold/{Jacobi,Local,Ideles,Class}.lean (scratch copies
  removed); final file ZInQKernel/Contrib/OneProof/TYZLemma28Sym.lean (imports TYZLemma29Genus, which defines
  TYZThm21Pairs / TYZLemma28Sym, and TYZGenusFold.Class); `lake build ZInQKernel.Contrib.OneProof.TYZLemma28Sym` OK.
* scratch/tyz-genus/Discharges.lean → Discharges-output.txt:
  `DISCHARGES [hL29] by ZInQ.Contrib.TYZGenusFold.tyzLemma29PrintedNe3_of_thm21Pairs`
  `still assumes: [ZInQ.Contrib.TYZDecomp.H29Genus.TYZThm21Pairs]`, axioms [propext, Classical.choice, Quot.sound]
  (39 open hypotheses, 9305 theorems checked).
* scratch/tyz-genus/FoldCheck.lean → FoldCheck-output.txt: `frozenTarget_thm21` (frozenTarget with hL29 replaced by
  h21 : TYZThm21Pairs) and `frozenTarget_thm21'` (as an instance of the current frozenTarget): standard axioms.
  Count: TYZ hypotheses h11, hL29 → h11, h21 (2 → 2, neutral).

## Step 3: h11 — analysis and the best combination — VERIFIED (compiled)

* F3.1 (VERIFIED, reading): every relation of TYZ Thm 2.1 / Lemma 2.9 at n > 1 is a product ℓ(d1)ℓ(d2) with
  d1 d2 = n > 1, so ℓ(1)^2 is never isolated; the n = 1 instance (pair (1,1)) is excluded by `TYZThm21Pairs` (1 < n).
  TYZ's own proof of Thm 1.1 asserts 𝓛(1) = 1 separately (L1082, as quoted in rv-pn-encoding/tyz-decomp) and the
  halving step fails at m = 1 (rv-pn-encoding). The project has only bounds 0 < ‖lcalSq 1‖ < 4 (t21-proof).
  So h11 needs an exact input at m = 1 (TYZLcalOne or Tunnell), besides a non-integer form of Thm 2.1.
* F3.2 (VERIFIED, compiled) ZInQKernel/Contrib/OneProof/TYZThm11Genus.lean:
  - `TYZThm21PairsC` (Thm 2.1 for every pair with complex sign choices ℓ : ℕ → ℂ, ℓ(m)^2 = lcalSq m; not vacuous:
    complex square roots exist), `tyzThm21Pairs_of_C : TYZThm21PairsC → TYZThm21Pairs`;
  - `lemma29_coreC` (TYZ's proof of Lemma 2.9 over ℂ, with the proved Lemma 2.8);
  - `tyzThm11Integral_of_thm21C : TYZThm21PairsC → TYZLcalOne → TYZThm11Integral` (TYZ's induction; n = 3 from
    Thm 2.1 at (3,1) with t21-proof's f_3(1) = ±3 and #μ = 6, no Tunnell);
  - `tyzLemma29PrintedNe3_of_thm21C`.
* #discharges (Discharges-output.txt): `DISCHARGES [h11] by ...tyzThm11Integral_of_thm21C still assumes:
  [TYZThm21PairsC, TYZLcalOne]`; `DISCHARGES [hL29] by ...tyzLemma29PrintedNe3_of_thm21C still assumes:
  [TYZThm21PairsC]`; all standard axioms.
* FoldCheck variant B `frozenTarget_thm21C` (h11, hL29 → h21C, hL1): standard axioms. Count 2 → 2 (neutral).

## Step 4: variant C (−1, pending reading of TYZ Thm 2.1 at n = 1) — VERIFIED (compiled)

* ZInQKernel/Contrib/OneProof/TYZGenusFold/QI.lean: `isCyclotomicExtension_four` (QNeg 1 is the 4th cyclotomic
  field), `torsionOrder_one` (#μ(ℚ(i)) = 4), `pid_one` (Minkowski, |d| = 4 < π²), `classGroup_one_subsingleton`.
* ZInQKernel/Contrib/OneProof/TYZThm21PairsOne.lean: `TYZThm21PairsC1` (Thm 2.1, complex ℓ, every squarefree
  n ≥ 1 in the odd classes, formula as 2^a P = ±2^k w_K ℓℓ, a = 1), `tyzThm21PairsC_of_C1`, `tyzLcalOne_of_C1`
  (n = 1: P(1,1) = f_1(1) = ±F(0) odd, so 𝓛(1)^2 is an odd integer; t21-proof's bounds Re L(C_1,1) ≥ 0.09,
  ‖L(C_1,1)‖ ≤ 1.26, ∫ ≥ 2 give 0 < 𝓛(1)^2 < 3, so = 1), `tyzThm11Integral_of_C1`, `tyzLemma29PrintedNe3_of_C1`.
* #discharges: `DISCHARGES [h11] by ...tyzThm11Integral_of_C1 still assumes: [TYZThm21PairsC1]`,
  `DISCHARGES [hL29] by ...tyzLemma29PrintedNe3_of_C1 still assumes: [TYZThm21PairsC1]`; standard axioms.
* FoldCheck `frozenTarget_thm21One` (h11, hL29 → h21 : TYZThm21PairsC1): standard axioms. Count 2 → 1 (−1), but
  the n = 1 instance of the leaf is not verified against the print (source absent; TYZ assert 𝓛(1) = 1 separately
  at L1082). Under CONTRIBUTING's rule a leaf pending reading counts as glue until a check clears it.
