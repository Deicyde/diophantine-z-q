# rv-jac-ext results log

## Sources read (VERIFIED by reading)
- axiom-bridge.md §1 (Faltings.Jacobian needs `CurveWithDegreeOneDivisor`: a divisor of closed
  points with `∑ n_x [κ(x):k] = 1`), §4 (open question).
- h-trust A1-A10, B1-B3, E1-E4, F1-F4; h-decomposition G1-G18 rows; h-b1 M3.
- N5 (diophantine_zq.tex) L377-441 (constants F₀ = 324!, D = F₀·3^{256F₀⁴}, deg(Y₃→P¹_j) ≤ 324),
  L524-578 (K, W₀ = Res_{K/ℚ}A, r ≤ 16F₀², L = EK, [L:ℚ] ≤ F₀·3^{r²} ≤ D, unramified outside T),
  L632-716 (B1-B3, [L':ℚ] ≤ 2md ≤ QM), L796-905 (conductor and transfer).
- Every use of the field after L563 goes through d = [L:ℚ] ≤ D, T, L Galois, L ⊇ K, and
  "L defines every geometric Hom between conjugates" (N5 L560-563, L638-640, L716, L833-867).
  No step uses [K:ℚ] directly after A8.

## Computations
- `weier2.py` (output `weier2.output.txt`), exact: (𝒪/2𝒪)^* has 12 elements (A₄: 3 involutions,
  8 elements of order 3); right multiplication preserves e₂ = Trd(μ⁻¹xȳ) mod 2; 6 odd and 10 even
  quadratic forms refine e₂; orbits on the 6 odd forms (= Weierstrass points, Mumford):
  trivial [1⁶], C₂ [1,1,2,2], C₃ [3,3], V₄ [2,2,2], A₄ [6]. VERIFIED.
- `autcheck.py`: Aut(A,λ) ∩ 𝒪 = {±1} (box search; exact argument: nrd −1 case needs
  2a²+3b² = 1 with b ∈ ½ℤ, a ∈ b+ℤ, impossible). VERIFIED. So Aut(C_ℚ̄) = C₂.
- `bounds.py`: 324! has 675 digits; largest k with k·12^k ≤ 324! is 622; with k·720^k ≤ 324! is 235;
  route L inequalities hold for k ≤ 324. VERIFIED.

## Lean (`JacExt.lean`, Mathlib only; compiled with `lean` + LEAN_PATH, since `lake env` tries to
## fetch Mordell on this branch)
- `perm_eq_one_of_fixes_pairs`, `finrank_finset_sup_le`, `routeW_degree`, `routeW_finrank`,
  `routeL_degree`, `routeL_degree_noCM`, `twelve_pow_bound` (324·12^324 ≤ 324!, `decide +kernel`).
  Compiled, no errors; axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## Findings
1. The curve C with (Jac C, θ) ≅ (A, λ) exists over K itself (Weil 1957 + Torelli + Weil descent;
   Serre's appendix to Lauter 2001 for the hyperelliptic case). STANDARD, locators UNVERIFIED.
   Mestre's obstruction (axiom-bridge §4(a)) concerns the field of moduli ℚ and does not arise.
2. A degree-one divisor over K is not forced: when the image of G_K in (𝒪/2𝒪)^* is V₄ or A₄ no
   Weierstrass point has odd degree. It is forced in the other three cases.
3. Over K(A[2]) ([K(A[2]):K] | 12) all six Weierstrass points are rational.
4. Route W′: K̃ = K(σA[2] : σ) is Galois over ℚ, unramified outside T, [K̃:ℚ] ≤ k·12^k ≤ 324! for
   k = [K:ℚ] ≤ 324 (A3 + torsor argument, or h-b1 M3's 144). A5-A6 conclusions hold for A_K̃
   with the same constants, so A8 gives the same D and B3 the same QM. ABSORBED.
5. Route L: L₂ = L(A[2]), [L₂:L] ≤ 12; needs 12·[L:ℚ] ≤ D, true by A8's own bound if k ≤ 324,
   or for all k ≤ F₀ with A10's rank r = 4k². ABSORBED.
6. J₁(N): X₁(N)/ℚ has a ℚ-rational cusp (0 in the (E,P) model, ∞ in the μ_N model); no extension.
