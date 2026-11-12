# glue-repo results log

Task: steps A1, A3, A5-A8, A10 of docs/research/h-trust.md. Marks: VERIFIED (read, computed or
compiled), STANDARD (published, reference), SPECULATIVE. Locators from memory are UNVERIFIED.

## Computations (scratch/glue-repo/compute.py, ~/pyenv/bin/python -I)
- VERIFIED: Trd(a μ⁻¹ ā μ) = 2x0²+4x1²+18x2²−48x2x3+36x3² (a = x0+x1 i+x2 j+x3 ij); leading
  minors 2, 8, 144, 576: positive definite (Rosati involution positive).
- VERIFIED: Res(F,G), Res(F,H), Res(G,H) supported on {2,3,5}; Bezout denominators on {2,3,5}.
- VERIFIED: structure constants of 𝒪 in the basis (1,i,(1+j)/2,(i+ij)/2) are integer
  polynomials (§4); Rosati involution in 𝒪-coordinates is integral (§5).
- VERIFIED (box |coord| ≤ 12, and proved by parity in general, see PRArith): every x ∈ 𝒪 with
  trd 0, nrd 3 has (1+x)/2 ∈ 𝒪.

## A1Quaternion.lean — COMPILED (lake env lean, no errors, no sorry)
B = ℍ[ℚ,2,0,-3] (Mathlib QuaternionAlgebra); 𝒪 = Set.range comb as a genuine `Subring B`.
Theorems: μ_mul_μ (μ²=-6), μ_mul_μinv, comb_mul (integral structure constants), O (subring),
e_mem, star_mem, ros_mem (𝒪 stable under †), trace_form / det_trace_form (det Trd(eₐe_b) = -36,
reduced disc 6), gram_E (N5 L414-416 matrix), det_gram_E (= 1), E_comb (E integral on 𝒪),
E_self, E_antisymm (alternating), E_ros (E(ax,y)=E(x,a†y)), ros_ros, ros_mul, ros_add
(anti-involution), trd_mul_ros, trd_mul_ros_pos (Trd(a a†) > 0 for a ≠ 0: † positive).

## TorsionFree.lean — COMPILED (no errors, no sorry)
- CommCore.eq_one_of_pow_eq_one: commutative ring, 3 regular, ⋂ 3ⁿC = 0, A ≡ 1 mod 3, Aᵐ = 1
  (m > 0) ⇒ A = 1 (steps 3∤m and m=3, induction on v₃(m)).
- eq_one_of_pow_eq_one: same in any ring (via the commutative subalgebra ℤ[y]).
- matrix_eq_one (R Noetherian domain, 3 nonzero nonunit; Krull intersection
  Ideal.iInf_pow_eq_bot_of_isDomain), matrix_int_eq_one, matrix_padic_eq_one (N5 L468-470).
- padic_subgroup_trivial: finite H ≤ GL_r(ℤ₃) with all elements ≡ 1 mod 3 is ⊥ (PR(ii) step 3).
- injective_mod_three, card_le_three_pow: finite G ≤ GL_r(ℤ) injects into GL_r(𝔽₃);
  Nat.card G ≤ 3^(r²) (A8).

## PRArith.lean — COMPILED (no errors, no sorry; #print axioms: propext, Classical.choice, Quot.sound)
Imports ZInQKernel.Hypotheses.Height (contactSet, contactSupport, prime_dvd_contactSupport_iff);
Jmap copied verbatim from JHeight.lean (not importable in worktrees).
- G6_sub_F2 (G⁶−97200F²=H²), J_add (J+16/27 = 16H²/(27G⁶)), t_eq (t = 1+27J/16 = H²/G⁶),
  t_sub_one (t−1 = −3(180F/G³)²).
- Hq_ne_zero (quadratic factors: discriminants 10800, 43200, 43200 have v₃ = 3, odd),
  Fq_ne_zero, J_ne_zero (A7), J_ne_branch (J(u) ≠ −16/27, h-b1 M7).
- bez_FG, bez_FH, bez_GH: homogeneous Bezout certificates, N = 2¹⁰3⁸5⁶, 2¹⁷3¹²5¹⁰, 2¹¹3⁹5⁶
  (scratch/glue-repo/bezout.py, output bezout.output.txt), checked by `ring`.
- inertia_trivial_iff: prime p ≥ 17, u ∉ 𝒞: (4 ∣ v_p(J)⁺ ∧ 6 ∣ (−v_p(J))⁺ ∧ 2 ∣ v_p(J+16/27)⁺)
  ↔ ¬∃ c ∈ 𝒞, v_p(u−c) > 0 odd. (= Prop. TS's inertia orders e/gcd(e,m) all 1, (e)=(4,6,2).)
- inertia_trivial_iff_not_dvd: same with ¬ p ∣ contactSupport S u, for p ∉ S ⊇ primes ≤ 324.

## A1Quaternion.lean, elliptic elements (h-b1 M9 / Lemma NV step 2; rv-h-cm (Emb)) — COMPILED
- nrd, nrd_eq, mul_star_eq (x x̄ = nrd x), nrd_mul.
- half_one_add_mem: x ∈ 𝒪, Trd x = 0, nrd x = 3 ⇒ ½(1+x) ∈ 𝒪 (type (0,3): CM order of disc −3,
  maximal; proof by residues mod 4, `decide` over (ZMod 4)³).
- descent / no_trd_zero_nrd_two: no x ∈ B with Trd x = 0, nrd x = 2 (ℚ(√−2) does not embed in
  B; 3-adic infinite descent on 3C² = 2E²+2B²+6D², `decide` over ZMod 3).
- #print axioms: propext, Classical.choice, Quot.sound.
