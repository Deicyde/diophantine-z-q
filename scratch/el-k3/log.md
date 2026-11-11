# el-k3 log

Angle: special structure of X_{β,θ}: w² = θ f(s) f(t), f(s) = β²s⁴ − 1 (congruent-curve form of
rs-pole §2.2, cr3-map-literature R3). Φ(B) with multiplier m ⇔ X_{β_m,θ_m}(ℚ) ≠ ∅ (L5/R1/R3).

## Definitions
- r_1..r_4 = 1/√β, −1/√β, i/√β, −i/√β (roots of f); K = ℚ(i, √β, √θ).
- Y = Bl_{16}(ℙ¹×ℙ¹) at (r_a, r_b); X → Y double cover branched on the 8 strict transforms
  L_a (s = r_a), M_b (t = r_b), which are disjoint in Y. Nodes N_ab = π⁻¹E_ab, tropes T_a, T'_b.
- D4 = Möbius maps preserving {r_a}: s ↦ λs, s ↦ λ/(βs), λ⁴ = 1. Graph Γ_φ = {t = φ(s)}
  has f(φ(s)) = k_φ f(s)·□ (k = 1, resp. −β²), so π⁻¹Γ_φ = G_φ⁺ ∪ G_φ⁻ with
  w = ±√θ f(s), resp. w = ±iβ√θ f(s)/(βs)²; fields ℚ(λ, √θ), resp. ℚ(λ, √−θ).

## Steps

### S1. NS(X̄) with Galois action (`ns_lattice.py`, `ns_invariants.py`; VERIFIED, exact)
- Inputs: 40 curves (16 N_ab, 8 tropes, 16 graph components G_φ^±); intersection numbers from
  the configuration; G·G by solving φ(s) = ψ(s) (numeric β = 7, w-sign matching, no tangency
  at blown-up points since D4 is finite). Gram matrix symmetric.
- Rank 20; span has discriminant −16 = −disc T(Km(E×E)), T = ⟨4⟩⊕⟨4⟩ (E: j = 1728). So the
  40 curves generate NS(X̄) (index 1). Galois (σ_β, σ_i, σ_θ) acts isometrically.
- Invariant lattice NS(X̄)^G:
  - θ ∉ ⟨−1, β⟩ℚ*² (all admissible θ ≠ 1): rank 8, disc −1024, **the form is ≡ 0 mod 4 on the
    diagonal and even off it**: D² ≡ 0 (mod 4) and D·D′ ∈ 2ℤ for all D, D′ ∈ NS^G.
  - θ = 1 or −1: rank 9, odd values (graph components over ℚ).  θ = β: rank 8, also ≡ 0 mod 4.
- Consequences (Pic X ⊆ NS(X̄)^G):
  1. No (−2)-class over ℚ ⇒ no smooth rational curve defined over ℚ on X_{β,θ}; no genus-one
     fibration over ℚ with a section.
  2. D·F even for every ℚ-divisor D and ℚ-fibre class F ⇒ the generic fibre of every
     ℚ-rational genus-one fibration has even index (closure of a degree-1 divisor would be a
     ℚ-divisor with D·F = 1).
  3. Every curve defined over ℚ has odd arithmetic genus (C² ≡ 0 mod 4).
  4. Pic is independent of θ (σ_θ has no fixed anti-invariant class): any construction read off
     the Picard lattice is uniform in θ.

### S2. Algebraic Brauer group (`ns_h1.py`; VERIFIED, exact)
- H¹(Gal(K/ℚ), NS(X̄)) via cocycles on the generators of (ℤ/2)³ and SNF (PARI matkerint,
  matinverseimage, matsnf); Z¹ rank checked equal to B¹ rank.
- θ generic (every admissible θ ≠ 1): H¹ = 0. θ = 1, −1, β: H¹ = ℤ/2.
- So Br₁(X)/Br₀ = 0: no algebraic Brauer–Manin obstruction on X_{β,θ}. With descent-alt
  §4.2(i) (one-curve quartic, hence X, everywhere locally soluble) only transcendental BM or
  no obstruction remains; Skorobogatov's conjecture (BM is the only obstruction on K3s,
  SPECULATIVE/open) would give X(ℚ) ≠ ∅ up to transcendental classes. Not a proof route.

### S3. E1 toy pairs, naive search (`e1_points.py 1 3 10 100000`; VERIFIED computation)
- Toy (β, θ) with (θ1)-(θ4); search s₀ ∈ {∞} ∪ {height ≤ 10}, t of height ≤ 10⁵
  (hyperellratpoints on w² = c(β²t⁴ − 1), c = sqf(θ f(s₀))). Sanity: planted point found.
- (199, 257): smallest point H = 74 (s = −7, t = −11/74). (3791, 1889), (−260287, 11953): none.
- Even 3-4 digit θ need points of height ≳ 10²; naive search is useless beyond toys.

### S4. E2 realistic inputs (`e2_realistic.py 7 12 3 1000`, output `out_e2.txt`; VERIFIED computation)
- 12 admissible B from the rs-pole §4.1 sampler; first DL multiplier m ∈ {1,3,5,7,2,6,10,14}
  with |β| ≡ 7 (8). θ has 22-25 digits (prime factors up to 25 digits).
- One-curve fibre (s = ∞), curve C_{βθ}: PARI ellrank = [1,1] (Selmer rank 1) in 12/12, **no
  point found** in 12/12. Caveat: PARI's lower bound 1 is the parity/Selmer value, not a proven
  point (it also prints [1,1,0,[]] for d = 157, whose generator is huge).
- Exact Selmer certificate (sel2cong) for the one-curve case: 0/12 at the first m (seed 5 run: 1/1).
- Naive search on X (s₀ height ≤ 3, t height ≤ 10³): no point, 12/12.
- BSD heuristic (L′(1) := 1, |tors|² = 16, Ω = 2ω₁, Tamagawa from ellglobalred): ĥ(generator)
  ≈ 10^7.2 … 10^11.7. Any point of X_{β,θ} gives an explicit point (log-height O(log H)) on a
  rank-one curve C_{nθ} with nθ ≥ θ, so heuristically log H(point of X) ≳ 10^7 for these inputs
  (SPECULATIVE: BSD + typical L′). Points exist only as existence statements; no construction
  with coefficients of size poly(θ) (e.g. a ℚ-conic on X with coefficients poly(β, θ), whose least
  point has log-height O(log θ) by Legendre/Holzer) can produce them.

### S5. Consequences recorded
- Special θ for the Picard lattice: only θ ∈ ⟨−1, β⟩ℚ*²; admissible ⇒ θ = 1, the trivial witness,
  which L7/L8 restrict to finitely many (q, m) per B (genus / integral points). With k bounded
  by bit-encoding, m = m₀k² gives finitely many tries.
- (θ3) is exactly the local condition at ℓ | θ, ℓ ≡ 1 (4): if (β/ℓ) = −1 then v_ℓ(f(s)) is even
  for all s ∈ ℚ_ℓ and X_{β,θ}(ℚ_ℓ) = ∅ (VERIFIED by the valuation argument).
