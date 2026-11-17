# mcheck-rc-deep2: detailed Manuscript check of the paired functional and of the residual bound (5.1)

Scope: two results in `diophantine_zq.tex` that the uniform bound (5.5) depends on. The previous check
(docs/research/mcheck-rc-deep.md, item D4) left both unchecked.

- **(1) ex:arith-paired-functional**: statement L3704-3726, proof L3727-3875. (L3877-3892 is the next
  definition, ex:arith-coordinate.) For context I read the setup L2718-2833 (coefficients, Definition
  ex:arith-data, conjugate duality), ex:arith-local-kummer and (4.3) at L3413-3470, the (4.4) model and
  support comparison at L3471-3500, and ex:arith-moving-character at L3502-3702.
- **(2) ex:limits-residual-bound, (5.1)**: statement L4453-4464, proof L4465-4648. For context I read
  ex:limits-inner-limit (L4391-4451).

There was no network, so print locators are quoted as the manuscript gives them and are UNVERIFIED. There
is no Gross-Zagier or TYZ argument here, and neither result uses CST Theorem 1.1 or Kolyvagin Theorem 1.

Scripts and outputs are in `scratch/mcheck-rc-deep2/`. Every check has a negative control: the same test
is run on a deliberately wrong input, and that run must fail.

| script | output | content |
|---|---|---|
| `p1_checks.py` | `p1_checks.out` | 28/28 PASS: the Frobenius and inertia contractions; DC = CA; active units over 𝒪[G]; the moving prime at a finite stage; the central determinants at (t); units at (t) and (t+2); the homotopy inverse from a cone contraction; the group-ring pairing; old-place bookkeeping; splitting of acyclic free complexes |
| `r_checks.py` | `r_checks.out` | 18/18 PASS: (5.1a); the Kummer count and (5.1b); the genus bound on 1217 fields by composition of forms; Hilbert 90; the Euler-characteristic and Schreier routes; the local table and per-prime costs; the (5.1) chain; contractibility at active primes after inverting t; minimal ranks over F_2[G] |

## Conclusion

**(1) ex:arith-paired-functional holds as written.** I found no false step.

- **Is the exponent a uniform in K? Yes.** The proof in fact gives a = 0. Every map in
  λ_z = PD(−, j⁻¹c(z)) is integral over S = 𝒪[G], and K enters only at the places above 2N. Every
  allowed K splits there, so K_w = Q_p, and the local diagram is one of a fixed finite list: one for each
  p | 2N and each local squareclass type, of which there are 4 for odd p and 8 for p = 2. At active and
  moving places the full local complexes have explicit contractions over 𝒪[G]: A and D are units at
  active places, C = t·I at the moving place, and t is a unit in 𝒪. These contractions have no
  2-power denominators. The group-ring pairing is a permutation matrix. Hence the cone of
  j : C_{U^⊥} → τ*C_U is integrally contractible, and j⁻¹ is integral (P1-P3, P8-P11).
- **Does integrality hold at (t) and (t+2)? Yes**, for the scalar primitive constituent, as stated.
  - At active primes C = −2, a unit at every height-one 𝔭 ≠ (2).
  - At (t+2) the moving inertia gives C = t ≡ −2, again a unit.
  - At (t) the inertia contraction is not available. Instead the Frobenius contraction works, because
    in the limit det(1 − Φ_0) = 2 − lim χ_h(r_i)a_{r_i} is nonzero. This uses the uniform bound
    v_2(2 ± a_r) ≤ c_E of ex:arith-moving-character together with r_i → 1 2-adically. The determinant
    keeps v_2 ≤ c_E in the ultrafilter limit, because that condition is clopen (P6-P7).

**(2) ex:limits-residual-bound holds as written.** I found no false step. I re-derived every count:

- the global Kummer and genus count;
- the Euler-characteristic route and the Schreier route;
- every row of the local table;
- the per-prime costs 30/24/32/14;
- the inequality chain.

The chain (5.1) holds with slack 8 at the largest s. The transfer to the original support is correct:
after reduction mod 2 and inversion of t, A = D = ((1+t)^{±e} − 1)I = t·unit and C = 0, so every
active comparison block is acyclic. The binary statement (ranks over F_2((t))[G] equal the dimensions
after augmentation) is correct, since F_2((t))[G] is a local ring.

**Errors: none.** No `.fleet/mcheck-rc-deep2-verdict.md` was written.

**Gaps filled (all small):**

- **P-a** (L3471-3477, L3756-3764, moving prime). The norm N_q(g) = (q+1)/2 + (q−1)/2·g in (4.4) is the
  Fox norm only when g² = 1. At the moving prime g acts as 1+t.
  - *Sketch:* DC − CA = −(N−1)(g−1) = −((r−1)/2)·(2t + t²). This vanishes in A_i because
    r ≡ 1 mod 2^{B'} with B' ≥ max(B,n) (L3669) and n_i ≥ 2i (L3695-3697). The Fox norm Σ_{k<r} g^k has the same limit, 1.
    So (4.4) is valid at the moving prime at every stage, and D → A in the limit (P5, P5b).
- **P-b** (L3712-3714, statement). The statement says that a is "independent of the active list and G".
  It does not mention K, yet (5.5) needs uniformity in K.
  - *Sketch:* the proof supplies it at L3808-3819 and L3866-3869 (old places are K-independent; a = 0).
    The statement should add "and of the allowed K".

**Not checked (unverified):**

- ex:arith-local-kummer: the integral statement Cone(U → L) ≃ RHom(U, Z_2)[−2] at the old places. I
  checked only that its cohomology is consistent (P10), not its proof.
- ex:arith-moving-character: I checked only how c_E is used, not the construction of the moving primes.
- ex:limits-inner-limit: I did not re-check that retained homotopy inverses survive the ultrafilter
  limit.
- That the local data satisfy the hypotheses of Nekovář 6.2.5-6.2.8 / 6.3.4 and 7.8.8(ii).
- All print locators (Known issues, item K4).

## Table 1: ex:arith-paired-functional (L3704-3875)

| tex | step | verdict | reason |
|---|---|---|---|
| 3704-3714 | statement: λ_z defined by transport, orthogonal lift and duality; integral after 2^a over 𝒪[G]; a independent of the active list and G | OK, gap filled (P-b) | proved below with a = 0. K-uniformity is proved (L3808-3819, L3866-3869) but missing from the statement |
| 3715-3724 | statement: the scalar primitive functional is integral at every height-one 𝔭 ≠ (2), including (t) and (t+2), with the same generic value; scope limits for the universal relaxed functional | OK | rows 3756-3779 below. The scope limits are honest: no claim is made for the relaxed family at height one |
| 3727-3730 | 𝒪 = (Λ_(2))^∧; the residual active Frobenius is (1+t)^{e}I with e odd; A, D invertible over 𝒪[G] | OK | 𝒪[G] is local with residue field F_2((t)). Residually A = D = ((1+t)^e − 1)I ≠ 0 (g ↦ 1, q ≡ 1). Checked in P4. The symbol "a" here clashes with the exponent a (K3) |
| 3731-3735 | Frobenius contraction h¹ = A⁻¹v, h² = (0, D⁻¹u) using DC = CA | OK | all three degree identities checked on 137 random models; the control D + I fails (P1). DC = CA holds because g² = 1 and g commutes with Φ (P3) |
| 3736-3755 | z^⊥ := (comparison)⁻¹ of the transported class; λ_z = PD(−, z^⊥) is closed; the generic value does not depend on the localization | OK | PD is a chain map, so λ_z∘d = ±PD(−, dz^⊥) = 0. On cycles, PD(w, −) depends only on the class of z^⊥, which is unique in the derived category. The text rightly says that integrality needs more |
| 3756-3758 | over 𝒪[G]: A, D are units, moving inertia − 1 = t·unit; the homotopies are integral | OK | at r, g acts as 1+t (orientation, L3698-3699), so C = tI, and t ∉ (2) is a unit of 𝒪. Units of 𝒪 have v_2 = 0, so there are no 2-power denominators |
| 3759-3762 | scalar primitive at height-one 𝔭 ≠ (2): active inertia − 1 = −2, a unit | OK | χ_h(g) = −1, Ψ and ρ are unramified at active primes, so C = −2I. Contraction denominators are powers of 2 only (P2). 2 ∉ 𝔭 because (2) is a height-one prime |
| 3762-3764 | moving prime: inertia contraction unless 𝔭 = (t); at (t), Frobenius contraction with nonzero central determinants | OK, gap filled (P-a) | t ∈ 𝔭 forces 𝔭 = (t). At (t) the residue field is Q_2 and det(1 − Φ_0) = 2 − lim χa_{r_i}, since det = lim r_i = 1. v_2 ≤ c_E survives the limit (P6). D → A by P-a (P5, P5b) |
| 3764-3765 | (t+2) is handled by the inertia contraction | OK | t ≡ −2 mod (t+2) is a unit in Λ_(t+2) (P7) |
| 3765-3775 | unused primes keep the unramified condition (self-orthogonal); the relaxed family is not covered at height one | OK | Ψ(Fr_q) is prescribed and ρ, χ_h are unramified at q, so U_ur^⊥ = U_ur for q ∤ 2 (standard). The scope limit is stated correctly |
| 3776-3779 | inertia contraction h¹ = C⁻¹w, h² = (−C⁻¹u, 0) | OK | checked on 150 random models; the control fails (P2) |
| 3780-3807 | fixed old-support lattice: Cone(U_{p,δ} → L_{p,δ}) ≃ RHom(U_{p,δ}, Z_2)[−2] integrally, with torsion kept; a quasi-isomorphism of bounded free models has an integral homotopy inverse | OK; the integral comparison rests on ex:arith-local-kummer (**unverified** here) | cohomology on both sides agrees: T_0^∨ in degree 2, and rank 1 in degree 1 only at p = 2 (P10). A bounded acyclic free complex over a local ring splits from the top, with 2-integral homotopies (P11; the control [Z −2→ Z] has no contraction) |
| 3808-3819 | K splits at 2N: two copies of the same Q_p-diagram, swapped by τ; Ψ and ε are trivial there; old diagrams are scalar extensions of a fixed finite list; derivative conditions use their orthogonal planes | OK | this is the K-uniformity. The local types are squareclasses: 4 for odd p, 8 for p = 2 (P10). Ψ is trivial at 2N (L3505, L3431); ε is trivial at 2N by common squareclasses (L3433-3437). F and S are self-orthogonal (block 2, mcheck-rc-deep) |
| 3820-3835 | no group-order denominator: [1](gh) is a permutation matrix; the duality hypotheses come from Nekovář 6.2.5-6.2.8 and 6.3.4; no real place | OK; locator UNVERIFIED | permutation matrix with integral inverse for G = (Z/2)^k, k ≤ 4. In the control, the regular trace |G|·[1] is not unimodular (P9) |
| 3837-3852 | over S the transported and orthogonal conditions differ only at active and moving places (full vs 0); a direct sum of contractions is a contraction; j is an integral homotopy equivalence; z^⊥ = j⁻¹c(z) and λ_z are integral | OK | Cone(j) ≃ ⊕_v Cone(U^⊥_v → τ*U_v). At old places this cone is acyclic, bounded and free, so contractible. At active and moving places it is the full complex, contracted above. Derivative and unramified places contribute the identity |
| 3853-3862 | cone contraction ⇒ chain map j⁻¹ with jj⁻¹ ≃ 1 and j⁻¹j ≃ 1; d(j⁻¹c(z)) = 0; closed integral functional | OK | from H(x,y) = (gx', ky) on Cone(j): g is a chain map, jg − 1 = −(dk + kd) and gj − 1 = da + ad. Verified on 25 hidden examples with Y = X ⊕ (4.4) full complex; the control 2·k fails (P8) |
| 3864-3875 | a = 0 is allowed; a is independent of G, the active graph and K | OK | a = 0 follows because every map is integral. The remark that "z already contains L" is not the reason, but it is harmless (K3). No numerical denominator arises, and none is needed |

## Table 2: ex:limits-residual-bound (L4453-4648)

| tex | step | verdict | reason |
|---|---|---|---|
| 4453-4464 | statement: N(E,A,j) ≤ 56ω(2N) + 8A + 56j + 70 for the reduced generic model; independent of the active primes and of v_2(r_i − 1) | OK | proved below. The scope (the reduced generic model, not the whole tuple) is stated correctly |
| 4466-4477 | v = ω(2N), m = v+1+j; T = primes below S_0 plus primes ramified in K; (5.1a) s ≤ v+A+1+j | OK | 2N primes and r split, derivative primes are inert, and 2 is unramified (K split at 2N), so the sets are disjoint. Ramified primes divide the squarefree part of k, so there are at most A of them (R1) |
| 4478-4491 | residual module W = E[2] = F_2² trivial; Kummer sequence for H¹(G_{K,S_T}, F_2); unit term 1 + |S_T| | OK | E[2] is rational (L7369), χ_h ≡ 1 mod 2, Ψ ≡ 1 mod t. Unit rank r_1 + r_2 − 1 + |S_T| = |S_T|; μ_K/2 has dimension 1. 2 ∈ T is needed and holds |
| 4492-4497 | (5.1b): |S_T| ≤ 2s − r, dim Cl(O_{K,S_T})[2] ≤ r − 1 | OK | h¹ ≤ 1 + (2s − r) + (r − 1) = 2s (R2). The genus bound is checked by form composition on all 1217 imaginary quadratic fields with |D| ≤ 4000: 2-rank = r − 1 exactly (R3) |
| 4498-4518 | genus argument: N α = 1; Hilbert 90 via β = 1+α or √k; invariant ideals are generated by ramified primes; (√d) is a nonempty relation; S-class group is a quotient | OK | the β recipe is checked in R3 (its control at α = −1 fails, as it must). |d| > 1 makes the relation nonempty; Q(i) is treated separately. A quotient does not raise the 2-rank |
| 4519-4524 | inflation G_{K,S_0} → G_{K,S_T} is injective on H¹; h⁰ = 2, h¹ ≤ 4s | OK | standard (S_0 ⊂ S_T, trivial coefficients). W has dimension 2 |
| 4525-4533 | Euler characteristic −2, H^{>2} = 0, h² = h¹ − 4; total ≤ 8s − 2 ≤ 8s + 2 | OK; Milne I.4.10, I.5.1 UNVERIFIED | one complex place: χ = 2 − [K:Q]·2 = −2. cd_2 = 2 for totally imaginary K. Arithmetic in R4 |
| 4534-4543 | alternative route: G_{Q,T}(2) has s+1 generators; Schreier gives 2s+1 for K; h¹ ≤ 4s+2; total ≤ 8s+2 | OK | K_{S_T}(2) = Q_T(2), because the Galois closure of a 2-extension of K is a 2-extension of Q unramified outside T. Schreier: 1 + 2s. Total: 2 + (4s+2) + (4s−2) = 8s+2 (R4) |
| 4544-4550 | local: (h⁰, h¹, h²)(K_w, W) = (2, 4 + 2d_w, 2) | OK; Milne I.2.3, I.2.8 UNVERIFIED | local duality (W^∨(1) ≅ W) and the local Euler characteristic −d_w·dim W (R5) |
| 4551-4557 | old Kummer residual dims (2, 2 + d_w) | OK | E^{(h)}(K_w)^∧_2 = Z_2^{d_w} ⊕ T_0, where T_0 has 2 cyclic factors because E^{(h)}[2] = E[2] is rational. Derived reduction gives T_0[2] in degree 0 and (Z_2^{d_w} ⊕ T_0)/2 in degree 1 |
| 4558-4573 | table: old Kummer 4+d_w / 12+3d_w; unramified 4/12; 0: 0/8; full 8/16; derivative strict 2/10, finite or singular 4/12, relaxed 6/14 | OK | each row recomputed (R5): [Φ − 1] = 0 on trivial W; D⁰ has dimension 2; F and S have dimension 2 each. In the control, dropping the degree-0 torsion breaks the old-Kummer row |
| 4574-4583 | per-prime costs: 2 → 30, other old → 24, moving → 32, derivative → 28 (14 inert); each ≤ 48; total ≤ 48m | OK | two places over 2 with K_w = Q_2 (Σd_w = 2): 2·15 = 30. Old: 2·12. Moving (full, split): 2·16. Inert derivative: one place, 14 (R5) |
| 4584-4592 | archimedean allowance ≤ 4; τ is not a real local condition | OK | K has no real place. The allowance is generous |
| 4593-4600 | stagewise finite free models of the global and local complexes; cone rank ≤ sum; uniform in r_i and in the order of Ψ_i (killed mod t) | OK (structural) | for a perfect complex over the Artin ring B_i, the minimal free rank equals the residual dimension (Nakayama). A cone has rank at most the sum of the ranks. Uses ex:limits-inner-limit (not re-checked) |
| 4601-4610 | (5.1): (8s+2) + 48m + 4 ≤ 8(s+1) + 6 + 48(v+1+j) ≤ 56v + 8A + 56j + 70 | OK | checked for all v ≤ 12, A, j ≤ 40, s ≤ v+A+1+j. Slack is 8 at the largest s. The control with constant 61 fails (R6) |
| 4612-4620 | scalar transfer: mod 2, χ_h is unramified at active primes; Nekovář 7.8.8(ii) identifies the S_0 complex with unramified conditions there | OK; locator UNVERIFIED | the use matches the stated hypothesis "coefficient representation unramified at the removed place" (L3484-3487) |
| 4620-4632 | at active places C = 0 and A = D = ((1+t)^{±e} − 1)I; ((1+t)^{±e} − 1)/t is a unit; full, unramified and singular blocks are contractible after inverting t; the inner limit is taken before inverting t | OK | t-adic valuation exactly 1 for every odd e < 40, both signs. The control e = 0 fails (R7). Active conditions are full or 0 (L3837-3840), and both differ from unramified by a contractible cone. The order "inner limit, then invert t" is necessary, because t is nilpotent in B_i, and the text follows it |
| 4633-4647 | binary: augmentation; F_2((t))[G] is local with nilpotent augmentation ideal; minimal ranks equal the augmented dimensions, which obey (5.1); 𝒪-minimal ranks equal the F_2((t))-dimensions | OK | I^{k+1} = 0 for G = (Z/2)^k (R8). Minimal model by unit cancellation matches the augmented dimensions on 47 random complexes over F_2[x]/x² (R8; the control fails). For the DVR 𝒪, minimal rank = dim of C ⊗^L residue field |

## Known issues

- **K1 (P-a, presentation).** The norm N_q(g) in (4.4) (L3477) is the g² = 1 form of the Fox norm, yet the
  model is also used at the moving prime, where g acts as 1+t (L3756-3764). It is still valid there:
  r ≡ 1 mod 2^{B'} with B' ≥ n_i ≥ 2i gives DC = CA exactly in A_i, and N → 1 in the limit (P5b). The
  text should say so.
- **K2 (P-b, statement).** In ex:arith-paired-functional the statement (L3712-3714) gives independence
  of a "from the active list and G" and does not mention K. K-uniformity is what (5.5) uses (L4957-4964),
  and the proof does prove it (L3808-3819, L3866-3869). The statement should include it.
- **K3 (notation and wording).**
  - At L3728 "(1+t)^aI with a odd" reuses the letter a, which elsewhere is the old-support exponent.
  - At L3864-3866 the step "z already contains L, thus a = 0" gives the wrong reason: a = 0 holds
    because every map in λ_z = PD(−, j⁻¹c(z)) is integral, whatever L is. The conclusion is right.
  - In the genus paragraph (L4509) the radicand is called d, whereas the rest of the section uses k.
- **K4 (inputs and citations, unverified).**
  - Proofs taken as inputs, not re-checked: ex:arith-local-kummer (the integral old-place comparison);
    ex:arith-moving-character (c_E uniform); ex:limits-inner-limit.
  - Locators quoted as printed and unchecked: Nekovář §§6.2.5-6.2.8, Thm 6.3.4 and Prop. 7.8.8(ii);
    Milne I.2.3, I.2.8, I.4.10 and I.5.1.
  - The content used is standard, but whether the local data meet Nekovář's exact hypotheses is
    unverified.
- **K5 (consequence for (5.5)).** Item D4 of mcheck-rc-deep listed four outside inputs. Two of them are
  now checked: (5.1), and the uniform exponent a with integrality at (t), (t+2) and the active primes.
  Still unchecked: the inner and outer limit lemmas, ex:arith-local-kummer, ex:arith-moving-character,
  and "central dimension one" via lem:forward-rank.
