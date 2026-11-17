# mcheck-rc-deep: detailed Manuscript check of the finite Heegner descent and of the uniform bound (5.5)

Scope: two blocks of `diophantine_zq.tex` that are Elliot's own work inside the proof of Theorem 5.3 (hyp:RC).

- **Block 1**: ex:arith-finite-heegner, tex L2834-3410. The map gave L2834-3393, but the proof runs to
  L3410. Setup read: L2718-2833.
- **Block 2**: ex:limits-uniform-lower-bound, tex L4909-5205, with ex:limits-kernel-detection
  (L4747-4831) and ex:limits-derivative-switch (L4833-4907). For context I also read
  ex:limits-outer-evaluation (L4650-4745), the statement of ex:arith-paired-functional (L3704-3726) and the
  end of its proof (L3860-3880), ex:arith-coordinate (L3882-3892), (3.5) at L2446 and (4.6) at L4045.

No network was available. Print locators are quoted as the manuscript gives them. Any locator I comment
on from memory is marked UNVERIFIED. There is no Gross-Zagier or TYZ argument of our own anywhere below.
Neither block uses CST Theorem 1.1 or Kolyvagin Theorem 1. Block 2 reaches lem:forward-rank only
indirectly, through the hypotheses of (4.6) ("central dimension one").

Scripts and outputs are in `scratch/mcheck-rc-deep/`:

| script | output | content |
|---|---|---|
| `b1_checks.py` | `b1_checks.out` | 17/17 PASS: (H1), matrix span, (H5), (H6), (H12), (H14)-(H18), self-cup, local res/cor, (H11) |
| `b1_transfer.py` | `b1_transfer.out` | 6/6 PASS: the transfer (H21) and its degree-n form on a GL2(Z/8) model (a negative control fails, as it should) |
| `b1_homotopy.py` | `b1_homotopy.out` | 5/5 PASS: transferred homotopies, the 3-arrow identity at L3354, witness transport (negative control fails) |
| `b2_checks.py` | `b2_checks.out` | 18/18 PASS: switch pairing and determinant symmetry, the Schur formula behind (5.5), the quadratic case, (5.5a)/(5.5b), (3.5) |

## Conclusion

**Block 1 (finite Heegner descent) holds as written.** I found no false step. Every computation checks:
the torsion annihilator e = n+2, the matrix span, (H5), (H6), the precision rule (H12), the Frobenius
algebra (H13)-(H18), the twisted transfer (H21) and the homotopy identities. The argument is the standard
Kolyvagin derivative computation, carried out at p = 2. It keeps track of the 2-power losses (one
uniform 2^e from (H2), and one extra bit in (H12) that pays for the division by two in (H18)), and as far
as I can check, it keeps track of them correctly. I filled two small gaps in the statement (B1-a, B1-b
below). The steps that rest only on a cited print are OK in content, but their locators are UNVERIFIED.

**Block 2 (switches and (5.5)) holds as written, relative to inputs proved elsewhere.** I found no false
step. I checked the following: the switch lemma, including the claim that the two valuations are equal,
which I filled in detail (B2-a); the outer-DVR compactness argument for (5.5), including the Schur formula
u = ±αβ/Δ, which holds for every nonzero maximal minor (S2); the quadratic-specialization case at (t) and
(t+2) (hyperbolic sign planes, the bookkeeping of (5.5a), the polarization behind (5.5b)); the comparison
of orthogonal conditions at derivative primes; and the step (5.5) + (4.6) ⇒ (3.5). The proof by
contradiction uses five inputs from outside the block. I checked their use, not their proofs:

- (5.1), the residual rank bound (ex:limits-residual-bound);
- (5.3)/(5.4), the outer DVR and Chebotarev realization;
- the fixed functional exponent a, uniform in K, from ex:arith-paired-functional;
- "central dimension one" at known simple zeros, from the (4.6) hypotheses and lem:forward-rank;
- (4.2) from block 1.

**Errors: none.** No `.fleet/mcheck-rc-deep-verdict.md` was written.

**Gaps filled (all small, at the level of presentation):**

- **B1-a**: the classes P_{I,m} need 2^a | a_ℓ and 2^a | ℓ+1 for every ℓ in I, not only for the new prime.
- **B1-b**: after twisting, the split norm relation needs θ to factor through Δ_{f/q}.
- **B2-a**: the switch lemma's equal-valuation claim, written out.
- **B2-b**: in the (5.5) argument, the bound β ≥ -a must also hold after the switches. The argument is
  given only in the height-one paragraph (L5162-5189).

**Not checked (unverified):**

- the print locators;
- the claim that the local data satisfy Nekovář 8.6.2.1-8.6.2.4;
- the proofs of the outside inputs listed above.

## Table 1: Block 1, ex:arith-finite-heegner (L2834-3410)

| tex | step | verdict | reason |
|---|---|---|---|
| 2836-2856 | setup: K split at 2N, K ≠ Q(i), Q(√-3); f prime to 2ND_K; I inert, outside 6fND_K; θ = χ_hΨ with Ψ trivial at 2N | OK | hypotheses; they match sec 8 setup L2720-2741 |
| 2858-2878 | statement: e, L depend only on E, π, old types, m_0; (4.1); (4.2) if a ≥ m+e and (H12) | OK, gap filled (B1-a) | as stated, P_{I,m} is claimed for any finite inert I. But (H7) needs 2^a \| a_ℓ and 2^a \| ℓ+1 for every ℓ in I, which holds when every prime of I satisfies (H12) (L3093 "every retained derivative prime"). Sketch: add "each ℓ in I satisfies (H12)" to the hypotheses |
| 2881-2886 | (H1): n ≥ 2 with 1+2^n M_2(Z_2) ⊂ ρ(G_Q), ρ(g) = uI, z = g²τg²τ⁻¹, e = v2(u⁴-1) = n+2 | OK | Serre open image (cited). ρ(z) = u⁴I and e = n+2 for n ≥ 2 checked (b1_checks; n = 1 would fail) |
| 2887-2897 | g² fixes every quadratic field; τ inverts Gal(H_d/K); z fixes every H_d; (H2): 2^e kills E(H_d)[2^∞] | OK | χ(g²) = χ(g)² = 1; H_d/Q is generalized dihedral; z acts on E(H_d)[2^∞] as u⁴, and u⁴-1 = 2^e·(odd) |
| 2899-2911 | matrix span: squares of preimages of I+2^nE_ij span ⊇ 2^{n+1}M_2(Z_2) | OK | squares and span checked for n = 2..11 (b1_checks). This is a Z_(2)-span, not a Z-span: it uses that 1+2^{n-1} is odd, as the text says |
| 2913-2931 | (4.1) from CCL Thm 2.15 on X_0(N): inert Tr y_{dℓ} = a_ℓ y_d; split Tr y_{dq} = (a_q-σ_q-σ_q⁻¹)y_d; u_m = 1; no cusp correction | OK; locator UNVERIFIED | these are the standard Heegner norm relations. In the split case, σ_𝔮σ_𝔮̄ = [(q)] = 1 in Pic(O_d). T_q[∞] = (q+1)[∞], so π(x) = φ([x]-[∞]) gives no correction. O_K^× = ±1 |
| 2932-2943 | cuspidal group finite (Manin-Drinfeld, Elkik p.59); C_π; π(Wx) = [w]π(x)+π(W∞) | OK; locator UNVERIFIED | W commutes with T_q for q ∤ N, so it acts on the non-CM A_f as ±1. Used only "for other changes of CM convention" |
| 2945-2962 | (H4): ȳ_{dℓ} = F_ℓ ȳ_d at a compatible place, with the supersingular specialization argument | OK | standard CM congruence (Gross; Howard is cross-referenced). The only order-ℓ subgroup scheme of a supersingular curve is ker F. It holds for class translates with transported places |
| 2964-2979 | (H5): ker(Pic O_{fn_I} → Pic O_f) ≅ ∏ (O_K/ℓ)^×/(Z/ℓ)^× ≅ ∏ C_{ℓ+1}, with no unit quotient | OK | O_f^× = O_{fn_I}^× = {±1}. Cyclicity of order ℓ+1 checked for 20 primes (b1_checks) |
| 2980-2986 | (H6): (σ_ℓ-1)D_ℓ = (ℓ+1) - Tr_ℓ | OK | identity in Z[C_{ℓ+1}] checked for 30 primes |
| 2987-3002 | (H7): c_{I,a} = δ_a(C_π D_I y_{fn_I}) is Gal(M_I/H_f)-invariant when 2^a divides a_ℓ and ℓ+1 | OK | (σ_ℓ-1)C_πD_I y = C_πD_{I∖ℓ}((ℓ+1)y - a_ℓ y_{fn_I/ℓ}) by (4.1)+(H6). This is a 2^a-multiple, so its Kummer class vanishes |
| 3004-3017 | (H8): inflation-restriction sequence [Nekovář (4.1.4.1), p.96] | OK; locator UNVERIFIED | standard Hochschild-Serre low-degree sequence |
| 3018-3036 | (H9): d_a(c) = 2^e b with res b = 2^e c; well defined; res d_a(c) = 2^{2e}c; I = ∅ gives 2^{2e}c | OK | V_a^{G_M} = E(M)[2^a] is killed by 2^e by (H2), so H^1 and H^2 of Γ are killed by 2^e. Two lifts differ by a class killed by 2^e |
| 3038-3061 | (H10): H^1(Gal(F'/F), B_0(F')) = 0 for unramified F'/F; c_B kills H^1(Gal, B(F')) | OK; locators (Lang 1956; Silverman IV.3.2(a)) UNVERIFIED | the Lang + formal-group filtration argument is standard. Each quotient is k' with a normal basis, hence an induced module. Φ(k') ⊂ Φ(k̄) gives exponent dividing c_B. The argument also works at p = 2 |
| 3063-3067 | if v is Kummer over F', then c_B v is Kummer over F | OK | the image in H^1(F,B) lies in ker(res) = H^1(Gal(F'/F), B(F')), which c_B kills |
| 3069-3091 | (H11): L = m_0C_πC_bad2^{2e}; b_{I,a} is Kummer at 2N, unramified at good places away from 2fn_I, full at active and moving primes; L is independent of K, f, I, m, b, G | OK | completions at 2N are unramified over Q_p because K is split there and the conductor is prime to 2N; geometric component groups do not change. At good v ∤ 2 the Kummer image equals H^1_ur. The multiplier identity is checked (b1_checks) |
| 3093-3100 | (H12): ρ(Fr_ℓ) ≡ J mod 2^{a+1} ⇒ 2^{a+1} divides a_ℓ and ℓ+1 | OK | tr J = 0 and det J = -1. 2200 random matrices checked, together with "F - a_ℓ ≡ J mod 2^a" and "Fr² ≡ I mod 2^{a+1}" (b1_checks) |
| 3101-3113 | (ℓ) splits completely in H_{fn_I}; residue field F_{ℓ²}; (H13) | OK | Artin symbol of ℓO_c is trivial; Tr Y = a_ℓX by (4.1) with d = fn_I; Ȳ = FX̄ by (H4) applied to class translates; F² - a_ℓF + ℓ = 0 |
| 3114-3121 | b_{I,a} at the place equals δ(LX) exactly; (H14): f_old = (F²-1)Q̄ = (a_ℓF-(ℓ+1))Q̄ | OK | the local fields of M_I and H_f coincide (split). The Frobenius of Q_{ℓ²} is F². Identity checked |
| 3123-3140 | adjusted representative b with b\|G_{H_{fn_Iℓ}} = (g-1)Z exactly; U = (σ_ℓ-1)Z - b(σ_ℓ) is fixed by G_{H_{fn_Iℓ}}; 2^aU = L((ℓ+1)Y - a_ℓX) | OK | I redid the cocycle computation: from b(gσ) = b(σ·σ⁻¹gσ) one gets g(-U) = -U. Then (H6) and Tr Y = a_ℓX |
| 3141-3149 | (H15): U_0 has integer coefficients; U - U_0 is killed by 2^e | OK | 2^{a+1} divides both coefficients; U - U_0 ∈ E(H_{fn_Iℓ})[2^∞]; (H2) |
| 3151-3159 | (H16): s_new = b(σ_ℓ) has reduction (a_ℓ-(ℓ+1)F)Q̄ + ε = (F-a_ℓ)f_old + ε, with 2^eε = 0 | OK | inertia acts trivially on reductions, and reduction is injective on 2-primary torsion. Checked in a matrix model (b1_checks) |
| 3160-3166 | (H17) (F-a)(aF-(ℓ+1)) = a-(ℓ+1)F; push to precision m kills ε; s_new = Jf_old | OK | polynomial identity mod F²-aF+ℓ checked. a-m ≥ e. F - a_ℓ ≡ J on E[2^a] |
| 3168-3172 | (H18): reduction of LD_ℓY = Lℓ(ℓ+1)/2·FX̄ = 2^a·(an F²-fixed point) | OK | all inertia translates reduce to Ȳ; Σj = ℓ(ℓ+1)/2; 2^a \| ℓ(ℓ+1)/2 (checked) |
| 3173-3186 | local 2^a-division point of LD_ℓY in the totally ramified upper field; restricted class 0; Frobenius lift in the upper group gives f_new = 0 (H19) | OK | Hensel lift from F_{ℓ²}, then [2^a] is invertible on the formal group (ℓ odd). The upper Frobenius acts as F² ≡ I on E[2^a], so the coboundary adjustment contributes 0. Silverman locators UNVERIFIED |
| 3187-3199 | orientation; extra bit pays for the halving; repeat with each prime singled out; one exponent suffices | OK | each other conductor prime splits completely in the lower ring-class field by the same principal-ideal argument. The precision is the maximum over a finite set |
| 3202-3218 | (H20): Shapiro, then v⊗[δ] ↦ θ(δ)v, G_K-equivariant, also over A[G] | OK | g(v⊗[δ]) = gv⊗[gδ] ↦ θ(g)θ(δ)gv |
| 3219-3250 | (H21) and the degree-n formula; h(gk,δ) = h(g,kδ)h(k,δ); dT = Td; no averaging factor | OK | checked on GL2(Z/8) ⊃ SL2(Z/8) with θ = det, degrees 0, 1, 2 (b1_transfer); a perturbed formula fails. Nekovář 8.1.1-8.1.6 locator UNVERIFIED |
| 3251-3267 | at 2N: local Mackey sum of corestrictions; Ψ is locally trivial; Kummer of Σχ(δ)δQ equals the transfer; old Kummer conditions survive | OK | standard: the double-coset formula and the naturality of Kummer maps under corestriction. Locally θ is an unramified quadratic character times 1 |
| 3268-3280 | derivative prime: θ is locally trivial; transported places and Frobenii; (4.2) f(P_{I∪ℓ}) = 0, s(P_{I∪ℓ}) = Jf(P_I) | OK | at the place r_δ⁻¹λ the relation reads s' = ρ(r_δ)⁻¹Jρ(r_δ)f'. The weight ρ(r_δ) in (H21) turns this into s = Jf in common coordinates |
| 3281-3295 | the split norm relation survives the twist: a_q - θ(σ_q) - θ(σ_q)⁻¹; d_a is compatible with corestriction (Cartesian squares) | OK, gap filled (B1-b) | compatibility: res∘cor = cor∘res in the linearly disjoint square, so cor b lifts 2^e cor c. **Gap:** collapsing Σ_{Δ_f} θ(δ)δ through Tr_{H_f/H_{f/q}} needs θ trivial on Gal(H_f/H_{f/q}). Otherwise the twisted sum is 0, not the displayed relation. Sketch: state "θ of conductor prime to q". Its use at (4.5), L3912-3915 (moving prime r_i at t = 0, θ = χ_h unramified at r_i), satisfies this |
| 3297-3317 | tame two-generator resolution; zero differential at m ≤ a; q ≡ 1 mod 2^{a+2}; self-cup of the adjusted uniformizer is 0 | OK | Fox derivatives with τ acting trivially give d¹(x,y) = (Φ-q)y. Φ = ρ(Fr)² ≡ I. -1 is a 2^m-th power in F_{ℓ²} (brute force, 34 cases), and (π,π) = (π,-1) |
| 3318-3336 | res = diag(1,f,e,ef), cor = diag(ef,e,f,1); the shear is divisible by (q-1)/2; the four conditions are preserved; cup adjunctions hold | OK | adjunction cor(res x ∪ y) = x ∪ cor y holds entry by entry (b1_checks); 2^{a+1} \| (q-1)/2 |
| 3337-3358 | contraction transfer: F_L = pFi, homotopies, 3-arrow identity K(H,GF)-K(HG,F)+H_LK(G,F)-K(H,G)F_L = Ld - dL | OK | verified symbolically by hand and numerically in 25 random models with the printed sign (b1_homotopy) |
| 3359-3371 | U⊗U' is free in degrees 0-2, so negative Hom into A[-2] vanishes; local data for Nekovář 8.6.2.1-8.6.2.4 | OK (degree count); citation use **unverified** | the degree count is immediate. I did not check that these data are exactly what 8.6.2.x requires (no print) |
| 3372-3406 | (H22) Selmer-cone witnesses; pushing witnesses through contractions: pz - pz' = d(pq), p'Fz - p'Fipz = d(p'Fhz) | OK | definitional; the identity is checked (b1_homotopy (c)) |
| 3407-3410 | the final multiplier is uniform: no factor in [H_f:K], \|G\|, \|I\| | OK | L comes from (H11), e from (H1). Nothing in paragraphs 6-8 adds a multiplier |

## Table 2: Block 2, switches and the uniform bound (L4747-5205)

| tex | step | verdict | reason |
|---|---|---|---|
| 4766-4775 | kernel lemma: a cocycle zero on the exact kernel is a coboundary in char 0, via (u⁴-1)b(g) = (g-1)b(z) | OK | z is central modulo the kernel and ρ(z) = u⁴I; dividing by u⁴-1 ≠ 0 in char 0 |
| 4778-4799 | rank-two localization at one kernel element (nonquadratic scalar character): the induced rank-4 representation is absolutely irreducible; Goursat; polarization | OK | matrix span (block 1) plus distinct moving-inertia characters (1+t)^{±1}. Polarization is checked in S3 |
| 4813-4830 | finite Chebotarev in one compositum; exact matrix identity (5.4) via the inner ultrafilter | OK (structural) | this is the use of (5.4). Precision n(i) → ∞ is applied before the 𝒪-denominators. I did not re-prove ex:limits-inner-limit |
| 4833-4880 | derivative local conditions: U_str = D^0, U_rel = D^0⊕(F⊕S)[-1], U_F, U_S; U_str^⊥ = U_rel; planes self-orthogonal; cone triangles | OK | linear algebra with D^0↔D^2 and F↔S. The triangles have no H^0 term because D^0 is kept |
| 4881-4895 | switch: strict H^1 = 0; relaxed image = its annihilator ⊇ {(v,0),(0,Jv)}, so equal; new H^1 = ⟨B⟩ | OK | the image is Lagrangian of dimension 2 in F⊕S (dim 4). (v,0) ⊥ (0,Jv) since β(v,Jv) = ε⟨v,v⟩ = 0 (S1). Nekovář 6.3.3-6.3.4 locator UNVERIFIED |
| 4897-4906 | the two class-functional coordinates have equal valuations even when v is divisible | OK, gap filled (B2-a) | the text gives this in two sentences. **Filled:** H²(C_str) ≅ ⟨A,B⟩^∨ has basis A*, B*. F_v → H²(C_str) sends x ↦ ε⟨x,v⟩B*. S_v → H²(C_str) sends y ↦ ε⟨v,Jy⟩A*. With unit volumes v∧x and Jv∧y, both pairings are units. λ_A ≡ A* and λ_B ≡ B*. So u_F and u_S are both unit/vol(A*∧B*). The symmetry needs s(B) = Jf(A) exactly, which (4.2) gives. Toy model in S1, where the control s(B) = 2Jv shifts the valuation by 1 |
| 4909-4925 | statement: v2 u_prim ≥ -C(E,A) uniformly at known simple zeros with ω(k) ≤ A; u_prim ∈ Λ[1/2], also at the unknown base | OK (see rows below) | C(E,A) is ineffective (proof by contradiction via an ultrafilter); RC is qualitative, so that is enough |
| 4927-4933 | rank-one start: the central class is nonzero by (4.5); the generic kernel is ≠ 0; semicontinuity gives generic kernel ≤ central dimension 1 | OK relative to (4.6) hypotheses | the rank of a matrix over the DVR Λ_(t) can only drop on specialization. "Central dimension one" is the Selmer rank at t = 0. It comes from the simple-zero hypotheses through lem:forward-rank, which I did not re-check here |
| 4935-4940 | contradiction setup: v2u_j → -∞; bounded-size minimal models over 𝒪_j; primitive v_j; outer kernel dimension s ≥ 1 | OK relative to (5.1), (5.3) | a primitive vector has a unit coordinate, so its outer image is ≠ 0 |
| 4940-4945 | s > 1: one derivative prime gives a rank-two localization including v; relaxed image = F; new outer dimension s-2 | OK | Lagrangian of dimension 2 containing F is F, so U∩S = 0 (S5). The outer fraction field is a nonquadratic test because t and t+2 are units of 𝒪 |
| 4947-4955 | the actual class is a scalar multiple of v_j with nonzero generic localization on an outer-large set; switch keeps inner valuations; new outer dimension ≥ 1; finitely many drops; (5.1) for a fixed number of switches | OK | the number of switches is ≤ (n-1)/2 with n bounded, and the same for all j on the ultrafilter set. A drop to 0 is excluded (consistent with odd fibre parity) |
| 4957-4964 | terminal: nonzero maximal minor Δ, inner valuation b; u = ±αβ/Δ; v2u_j ≥ -a-b: contradiction; (5.5) | OK, gap filled (B2-b) | the Cramer formula u = ±z_{j0}λ(f_{k0})/M_{k0j0} is checked for every nonzero minor; the coordinate does not depend on the complement (S2, 3694 evaluations). **Gap:** β ≥ -a after the switches needs the paired functional to stay 2^a-integral with the added derivative conditions. The text proves this only in the regularity paragraph (L5162-5189: the orthogonal comparison at a derivative prime is the identity). Sketch: quote that argument here. The uniformity of a in K comes from ex:arith-paired-functional (L3712-3714, L3866-3874), not checked here |
| 4965-4972 | (5.5) only at known simple zeros; remark on [2^j] | OK | correct scope. [2^j] shows that bounded size alone gives no bound (S2) |
| 4975 | tex comment "Replace baseline lines 4112--4138" | n/a | editorial leftover (map K6) |
| 4976-4997 | height-one p ≠ (2): R = Λ_p is a DVR, k has char 0; derivative conditions keep D^0; evaluation injection; C = [R^s → R^s] with d⊗k = 0; primitive v in the saturated kernel; switches chosen with loc(v̄) ≠ 0 | OK | the kernel of an R-linear map is saturated. Nonzero mod p implies nonzero generically |
| 4997-5003 | nonquadratic specialization: rank-two detection, U = F, s drops by 2 | OK | as at L4940 |
| 5004-5009 | quadratic ⇔ t(t+2) = 0 in k, so p = (t) or (t+2) | OK | (1+t)² - 1 = t(t+2) (S3); both are height-one primes ≠ (2) |
| 5009-5019 | c^τ(g) = Jc(τ⁻¹gτ) is a k-linear involution; Ind = W_+⊕W_- with α(τ) = ±1 | OK | I redid the cocycle check using α^τ = α. τ² = 1 allows the extension α̃(gτ^ε) = α(g)(±1)^ε |
| 5019-5026 | W_± are absolutely irreducible on G_K and nonisomorphic (τ acts as J vs -J) | OK | squares g² ∈ G_K have α(g²) = 1, so the span is that of block 1. A scalar c with cJ = -Jc is 0 since 2 is invertible |
| 5024-5034 | at a new derivative prime τ acts on F as J and on S as -J (ℓ = -1 in the limit) | OK | c^φ(ϕ) = Jc(ϕ); φ⁻¹τ_vφ = τ_v^{ℓ⁻¹}, so S picks up ℓ⁻¹ = -1. Conjugating τ to φ costs α(φτ⁻¹) = 1 on the exact kernel |
| 5035-5054 | β(x,y) = εe_2(x,Jy) is symmetric; H_+ = F(e_+)⊕S(e_-), H_- = F(e_-)⊕S(e_+) are orthogonal hyperbolic planes; isotropic lines are the axes | OK | S3: symmetry from det J = -1, J² = 1; Q(aF+bS) = 2ab·c. With 2 invertible, the axes are the only isotropic lines |
| 5055-5059 | old conditions are stable under the involution | OK (structural) | conjugate places are swapped; F and S at earlier derivative primes are stable by the row above |
| 5059-5086 | U = U^⊥ (from the duality, not isotropy alone); (5.5a) exact sequences; U = U_+⊕U_-, each an axis | OK | the sequences come from the triangles with D^0 kept (no H^0 term). The axis claim follows from the row above |
| 5087-5115 | detection of opposite signs: joint span = W_+⊕W_-; (5.5b) c_δ((τh)²) = (1+δJ)c_δ(h); one actual h with both finite coordinates ≠ 0; Chebotarev realization | OK | Goursat plus nonisomorphism. (τh)² = (τhτ⁻¹)h ∈ H, and coboundaries vanish on H. (1+δJ) maps onto the δ-axis (S3). The polarization identity is checked |
| 5116-5122 | both signs present: U = F, dim V' = s-2; loc(v̄) ≠ 0 | OK | S3 bookkeeping. The sign components of loc(v̄) lie on different axes, so they cannot cancel |
| 5123-5136 | one sign only (V = V_+): U_+ = F(e_+), U_- = S(e_+); K_0 has dims (s-1,0) and V' has (s-1,1); the next switch is mixed and drops by 2 | OK | enumerated in S3: U_- = F(e_-) would put a minus vector in V. The new primitive vector is used at the second detection |
| 5137-5153 | new class = actual derivative P_{I∪ℓ} with the same L; (4.2); the switch keeps the valuation; the actual class is never replaced by the primitive vector | OK | uses block 1 (4.2) and B2-a |
| 5154-5162 | finitely many switches give fibre dimension 1; terminal [R →0 R]; the actual class is integral | OK | a generic kernel of rank 1 on R → R forces d = 0 |
| 5162-5189 | at derivative primes (D^0⊕S[-1])^⊥ = D^0⊕S[-1]; the orthogonal comparison is the identity; the paired functional stays integral; unit -2 at active primes; at the moving prime t, except at (t) (central Frobenius determinants) | OK (local orthogonality); inputs from ex:arith-paired-functional **unverified** here | the annihilator computation is immediate. The active/moving-prime inputs belong to the paired-functional proof (L3704-3880), outside this block |
| 5189-5195 | terminal coordinate in R; valuation preserved through the switches; Λ[1/2] = ∩_{p≠(2)} Λ_p | OK | Λ = Z_2[[t]] is a normal noetherian domain (a UFD), so it is the intersection of its height-one localizations |
| 5196-5200 | the same proof at the unknown corank-one base (zero class gives u = 0; otherwise rank-one start) | OK relative to "central dimension one" there | that comes from s_2(E/K) = 1 (L2627-2647, checked by the map). No uniform bound is claimed there, correctly |
| 5200-5202 | (5.5) + (4.6) + Σt_p ≤ 2A ⇒ (3.5) | OK | S4. Only Σt_p ≥ 0 is needed (map K5); v2u(0) ≥ the Gauss valuation |

## Known issues

- **D1 (statement, B1-a).** In ex:arith-finite-heegner (L2858-2869) P_{I,m} is asserted for any finite set of
  good inert primes I. The construction ((H7), (H12)) needs every ℓ in I to satisfy 2^a | a_ℓ and
  2^a | ℓ+1, which (H12) for every retained prime gives. This is harmless: every use chooses I by
  Chebotarev with (H12). Still, the hypothesis should be stated.
- **D2 (statement, B1-b).** The twisted split norm relation a_q - θ(σ_q) - θ(σ_q)⁻¹ (L3290-3295) needs θ to
  factor through Δ_{f/q}. Its use at (4.5) satisfies this.
- **D3 (presentation, B2-a/B2-b).** The equal-valuation claim of the switch lemma (L4897-4906) and the
  bound β ≥ -a after switches in the (5.5) argument (L4960) are stated tersely. Both are filled above.
- **D4 (outside inputs, unverified here).** Block 2 relies on several results outside it: (5.1)
  (ex:limits-residual-bound); the inner and outer limit lemmas; ex:arith-paired-functional, which
  supplies the exponent a uniform in K and the integrality at (t), (t+2) and at active primes; and the
  (4.6) hypotheses ("central dimension one" through lem:forward-rank, a Kolyvagin print). I checked how
  they are used, not their proofs. ex:limits-residual-bound and ex:arith-paired-functional are the next
  checks of most value.
- **D5 (citations, UNVERIFIED).** These locators are all quoted as printed and unchecked (no network):
  - CCL Thm 2.15;
  - Elkik p.59;
  - Nekovář (4.1.4.1) p.96, 8.1.1-8.1.6, 8.6.2.1-8.6.2.4 and 6.3.3-6.3.4;
  - Lang 1956 Thm 1;
  - Silverman IV.2.3 and IV.3.2(a), pp.122-124;
  - Howard 2012 §1.7 (13);
  - Serre (open image).

  The mathematical content used is standard. Whether the local data meet the exact hypotheses of
  Nekovář 8.6.2.x is unverified.
- **D6 (ineffective constant).** C(E,A) in (5.5) comes from an ultrafilter contradiction and is not
  computable. This is fine for RC but worth knowing.
- **D7 (text artefacts).** The tex comment at L2832-2833 ("This is a proof fragment, not an assertion
  about completion of RC") sits directly before block 1, and L4975 ("Replace baseline lines 4112--4138")
  is inside block 2. Both are editorial, as noted in map K6. Block 1 itself is a complete proof of its
  proposition, so the first comment should not be read as a disclaimer on its content.
- **D8 (range).** The proof of ex:arith-finite-heegner ends at L3410, not L3393 as given in the map.
