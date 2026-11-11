# el-qfree log

## S1. Quantifier structure of the two consumers (VERIFIED, reading Lean)
- `Test n κ t` (Assembly/Local/SixLocalTests.lean:66): `∃ h s₀ : ℤ, ∃ η q : ℚ`, with only
  `h ≠ 0, h ≠ κ, η² = 1, a₀ ≠ 0, W ≠ 0, Θ ≠ 0, Φ(R/Θ²)`. No real or p-adic condition on q; η is a
  free sign (η = −sign F gives R₀ < 0, B < 0).
- `SlopePred t ℓ c` (Multiplication/Certificate/SlopePredicate.lean:52): `∃ η q h z` with
  `h g ≠ 0, h g ≠ c 0`, nonvanishing, `Φ(R/Θ²)`. q, η, the six shifts h_g and the 18 integers z_g free.
- The open sets U_test, U_slope of cr3-map-needs are imposed only by PC's hypotheses
  (test_complete takes q from poleInput_real). Completeness without PC needs:
  ∃ (η, q, h, s₀) with Φ(B) (test), ∃ (η, q, h_g, z_g) with Φ(B) (slope).
- Test(n, κ, n) itself accepts any κ ≠ 0 (κ deep is used only to verify PC's S₀-valuations).

## S2. Multiplier valuation window (VERIFIED by derivation; extends cr3-map-needs L7)
Pole system with multiplier m: A = mB, H = A(A − B²), e, z as in L7. Fix odd p, b = v_p(B), μ = v_p(m).
- Soundness lemma (L7's proof, hypothesis weakened): if b < 0 odd, μ even and μ > b, there is no
  solution. (Proof of L7 uses only a = b + μ odd and a − 2b = μ − b > 0.)
- Completeness constraint at a consumed prime of a genuine instance (b ≥ 1 odd; b = 1 at the slope
  site's P(t)): if μ > b then v_p(θ) = v_p(m(m − B)) = μ + b is odd, p | β, and Loc N β ∧ Loc Nθ β
  fails locally at p (C_{Nθ} has good reduction at p after scaling, a good-reduction point has
  abscissa of even valuation, β has odd valuation). So the prover needs μ < b, i.e. μ ≤ 0 when b = 1.
- Hence any multiplier set M usable at both kinds of input needs v_p(m) ∈ (−1, 1) ∩ 2ℤ = {0} at
  p ∈ P(t) for the chosen m, and v_p(m) ≥ 0 even for all m ∈ M at all p > 324 (soundness for
  b = −1). An input-dependent multiplier m = μ·R₀·B (designed so that v_p(m) > v_p(B) whenever
  v_p(R₀) odd) makes θ = sqf(μR₀(μR₀ − 1)) independent of q but violates the completeness
  constraint at every consumed prime: Φ fails at every genuine instance. Excluded.
- Unbounded k: m = m₀k² needs k ∈ ℤ[1/S] (S = primes ≤ 324) certified by the polynomial. With
  bit encodings k is bounded (each bit is one witness per pole call, ~8.3M variables). An
  existential definition of ℤ[1/S] in ℚ is as hard as the target (ℤ = ℤ[1/S] ∩ ⋂_{p∈S} ℤ_(p), each
  ℤ_(p) diophantine). Quaternion sets T_{a,b} (Poonen 2009, Lemma 2.5: traces of norm-1 elements =
  ⋂_{p∈Δ_{a,b}} ℤ_(p) ∩ real condition) give integrality only at the ramified primes; soundness
  would need Δ_{a,b} ⊇ consumed primes for every witness (a, b), which no fixed choice of b forces
  (primes splitting in ℚ(√b) escape; Chebotarev). STANDARD (Poonen) + derivation.
- Conclusion: M is a finite set {m₀k² : m₀ | ±Π_{p≤324} p, k < 2^K}.

## S3. Exact θ = ±1 criterion (VERIFIED by derivation)
B = N/D reduced, m = m₀k², ε = ±1. θ ≡ ε·1 ⇔ X := ε m₀ D (m₀k²D − N) ∈ ℚ*².
Torsion witness then gives Φ (rs-pole §2.2(2), N = β; Loc depends on d only through d²).
(a) Bounded integer k: m₀ squarefree, so m₀ ⊆ S ∩ (supp N ∪ odd-supp D); finite check (E2).
(b) k ∈ ℤ[1/S] arbitrary: let D' be the prime-to-S part of D. For ℓ | D', v_ℓ(m₀k²D − N) = 0, so
    v_ℓ(X) = v_ℓ(D): D' must be a square, and −ε m₀ N (D/ℓ^{v_ℓ D}) must be a QR mod ℓ.
    Global form: with D' = E², X ∈ □ ⇔ (m₀kE)² − ε'·W² = m₀N·(S-unit square) splits as
    g·g' = m₀N, g + g' = 2m₀kE: k = (g + m₀N/g)/(2m₀E) with g ∈ (divisors of N')·(S-units).
    So k exists iff some g = u·g₁ (u S-unit, g₁ | N') has g² ≡ −m₀N (mod E·2m₀). The S-unit u
    ranges over ⟨S⟩ ⊂ (ℤ/E)*; when ⟨S⟩ ⊇ squares of (ℤ/E)* the condition is a Legendre condition
    only, but u (hence k) has exponents ~ ord(⟨S⟩ mod E) ~ E: k is doubly exponential in the
    size of B. Not encodable with bounded bits.
(c) For fixed k, X ∈ □ is a curve in q: w² = ε m₀(m₀k²T(R)² − R N_W(R)²), R = R₀(1 − R₀q²)²,
    T = Tr W, N_W = Nm W (Θ = T/N_W). deg_R(R N_W²) = 1 + 2·2·#{j: C_j ≠ 0}; with 6 nonzero
    tests deg_R = 25, deg_q = 100: hyperelliptic genus 49 (if squarefree). Finitely many q (Faltings).

## S4. q-uniform (rational-curve) routes: structure (derivation; dimension count SPECULATIVE)
Notation: σ(q) = a₀/Θ (test) so B = R₀σ², θ(q) ≡ m(m − R₀σ²) ≡ m(m T(R)² − R N_W(R)²), R = R₀a₀².
- Over ℚ(q): C_N(ℚ̄(q)) ⊗ ℚ ≅ Hom(Jac(Y_N), C₁) ⊗ ℚ, Y_N : y² = N(q) (hyperelliptic involution
  acts as −1 on Jac, so every map is odd). STANDARD (twists of constant curves).
- Torsion classes over ℚ(q): x ∈ {0, ±N}; both points torsion ⇔ θ(q) ∈ ±ℚ(q)*², false since
  m − B(q) has simple zeros. So a q-uniform Φ needs Jac(Y_N) or Jac(Y_{Nθ}) ⊇ C₁ (over ℚ̄).
- N constant (e.g. N = β): need Jac(Y_θ) ⊇ C₁, Y_θ : w² = m(mT² − RN_W²), genus 49 (6 nonzero
  tests) or 33 (n = 1, h = 2κ, s₀ = 2κn: tests D₄ = D₅ = 0). Tested in E3.
- General q = φ(x), N = G(ψ(x)): a rational curve on the 3-fold
  V' : w² = m(m − R₀σ(q)²)(β² − τ₁⁴)(β² − τ₂⁴) (double cover of ℙ¹_q×ℙ¹×ℙ¹ branched in tridegree
  (100, 4, 4)), K_{V'} = π*O(48, 0, 0): Kodaira dimension 1, canonical fibration = projection to
  the q-line. On the surface S : w² = θ(q)Q(ρ) (Q a quartic, bidegree (100, 4)), K_S = π*O(48, 0) and
  a rational curve Z with deg(q|Z) = e has −K_S·Z − 1 = −48e − 1 < 0 (expected dimension of
  rational curves). Parameter count for (φ, ψ) of degrees (e, d): conditions 50e + 2d, parameters
  2e + 2d − 1. Overdetermined by 48e + 1 for every e, d. So rational curves of q-values exist only
  for special (non-generic) θ. (count: derivation; conclusion SPECULATIVE)
- Note: S(ℚ) is expected Zariski dense (fibres over q are 2-coverings of C_{βθ(q)}, about half with
  positive rank), so the obstruction is to explicit/uniform witnesses, not to existence; proving
  existence for one q is again a positive-rank statement for C_{βθ(q)} (= CR₃ shape).

## E2. θ = ±1 with bounded multipliers on real test-site inputs (VERIFIED, `e2_theta1.py`, `e2_out.txt`)
Inputs: n ∈ {1,2,3}, κ = 1, (h, s₀) ∈ {(2,2n), (3,2n), (−1,n)}, η = ±1, q ∈ {0, 1/2}: 30 inputs.
B = N/D built from the Lean formulas (k0.py). Checked exactly: ε m₀ D (m₀k²D − N) ∈ □ for all
signed m₀ ⊆ S ∩ (supp N ∪ odd-supp D) (S = primes ≤ 324), 1 ≤ k ≤ 256, ε = ±1.
Outcome: 0 hits on 30/30 inputs. N has 356-4000+ digits, D 210-2000+ digits; reduced D is never a
square (for free q the admissibility condition IsSquare(B.den) is not automatic), so by S3(b) even
unbounded S-integral k fails unless the prime-to-S part of D is a square. D has prime factors
> 324 (e.g. 593, 8273, 81611), none in S. Runtime ≈ 50 min.

## E3. No CM factor in Jac(Y_θ) (VERIFIED, `e3_cmfactor.py`, `e3b.py`, outputs `e3_out.txt`, `e3b_out.txt`)
Y_θ : w² = m(m T(R)² − R N_W(R)²), R = R₀(1 − R₀q²)² (q-uniform route with N constant, S4).
Test: if Jac(Y_θ) had a factor ℚ̄-isogenous to C₁ (CM by ℤ[i]), then at every good p ≡ 3 (mod 4)
(inert in ℚ(i)) that factor is supersingular, so some Frobenius root α has α²/p a root of unity.
Computed hyperellcharpoly mod p, resultant to roots α²/p, polcyclofactors.
- (n,h,s₀,η,m) = (1,2,2,1,1): genus 33, p = 19: no cyclotomic factor.
- (1,2,2,1,−1): genus 33, p = 19: none.   (1,2,2,−1,3): genus 33, p = 67: none.
- (2,2,4,1,1): deg 100 but f not squarefree over ℚ (deg gcd(f,f′) = 8): singular mod every p tried;
  not tested.
Conclusion (for these instances): Hom(Jac Y_θ, C₁) = 0 over ℚ̄, so C_{Nθ(q)}(ℚ(q)) is torsion for
every constant N, and no q-uniform Φ-witness with a constant twist exists. Turns cr3-map-literature
R6's SPECULATIVE assessment into an exact statement on three real instances.
