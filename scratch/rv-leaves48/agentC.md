# rv-leaves48, agent C: adversarial review of T14-T16, T20-T22, T29-T31

Read-only review. No Lean process was run. Line numbers refer to `scratch/h-decomposition/Leaves.lean`.
Bundle check (VERIFIED, L19149-19185): `TextbookLeaves` uses the cochain forms `PkgI6.BrauerHasse2C`,
`BrauerReciprocity2C`, `LocalH2CardC` (rv-leaves-b repair 3 has been applied), and the **GlueConductor**
(global number-field) forms of T20/T21, not `PkgI6.HilbertDifferentFormula` (L5092) or `PkgI6.DifferentBound`.

## Verdict table

No leaf in this cluster is OVER-STRONG, VACUOUS or MISSTATED. All 13 are OK. There are two minor
documentation errors: one in rv-leaves-b and one in a docstring (§2).

| leaf | verdict | reason |
|---|---|---|
| t16b `PkgI6.LocalReciprocityUpper` (L5150) | OK (watch item: normalization) | ∃θ with: surjective; kernel = `N(L^×)`; every uniformizer ↦ an element acting as `x ↦ x^q` on `k_B`; `θ(U^{(⌈v⌉₊)}) = G^v` for real `v ≥ 0`. The arithmetic-normalized reciprocity map (Serre's convention) satisfies all four clauses. Clause 4 uses upper-numbering XV §2 together with Hasse–Arf for non-integer `v` (G^v is left-continuous, `G_u = G_{⌈u⌉}`, L5047). Holds in char p too (local CFT for finite residue fields). The normalization matters for clause 3 (§2.1) |
| t22a `PkgI6.HerbrandQuotient` (L5105) | OK | `(G/H)^v = r(G^v)` for every real `v`. For `v < −1` both sides are `⊤` (the sInf in `upperRam` is `−1`, L5059, and `r` is onto). `r` is forced by `hr` (`C → B` is injective: domain, torsion-free). Perfect residue field ⇒ separable residue extensions (Serre's standing hypothesis) |
| t22b `PkgI6.HerbrandTransitivity` (L5122) | OK | `φ_{B/A} = φ_{C/A} ∘ φ_{B/C}` on `u ≥ −1`. `C/A` Galois is included. `lowerRam C B` uses `B ≃ₐ[C] B = H` and agrees with `G_i ∩ H` (`lowerRam_tower`, L5066) |
| t14a `PkgI6.BrauerHasse2C` (L4893) | OK | The cocycle/coboundary formulas for trivial action are correct (L4875-4880). `ZMod N` is discrete (VERIFIED, Mathlib `Topology/Instances/ZMod.lean`). The places include `∞`. Kummer theory gives `H²(μ₂) ≅ Br[2]`, then ABHN |
| t14b `PkgI6.BrauerReciprocity2C` (L4899) | OK | The local invariants of a 2-torsion class lie in `{0, 1/2}` and are injective, and they sum to 0. So the support is finite and even, with `∞` included |
| t15 `PkgI6.LocalH2CardC` (L4915) | OK | `H²(G_{ℚ_p}, ℤ/2) ≅ Br(ℚ_p)[2] ≅ ℤ/2`. `H²(Gal(ℂ/ℝ), ℤ/2) = Ĥ⁰ = ℤ/2`. `H2TwoClasses` is exactly "two elements" |
| t16a `PkgI6.LocalKroneckerWeber p` (L4981) | OK | Finite abelian `L ⊆ ℚ̄_p` lies in some `ℚ_p(μ_n)` with `n > 0`. `PadicAlgCl p = AlgebraicClosure ℚ_[p]` (VERIFIED). `IsAbelianGalois` = Galois with commutative group |
| t20 `GlueConductor.HilbertDifferentFormula` (L5732) | OK | Global `G_i = (P^{i+1}).inertia Gal(L/ℚ)` (L5717). The condition forces `σP ⊆ P`, so `G_0 ⊆ D_P`. Density makes it the local `G_i`. Exact power of `P` in `differentIdeal ℤ (𝓞 L)`; the Nat subtraction is safe because `|G_i| ≥ 1`. The transport citation (rv-leaves-b repair 4) is present in the docstring, L5700-5706 (VERIFIED) |
| t21 `GlueConductor.SerreDifferentBound` (L5741) | OK | `v_P(𝔇) ≤ e − 1 + e·v_p(e)`, from `v_{L_P}(e) = e·v_p(e)`. Holds for any number field (separable, finite residue field). `Ideal.ramificationIdx` is the length of `S_P/pS_P` (VERIFIED, `RingTheory/RamificationInertia/Ramification.lean:53`). That is `e` for a nonzero prime; the junk value 0 occurs only for non-primes, which are excluded |
| t30 `GlueDescent.B2Q.LeafSqrtCrit` (L8779) | OK | A locally constant `φ` has finite image, so it is a finite-order character of `ℚ_p^×`. `ψ'` is a square iff `ψ'(−1) = 1`, using `ℚ_p^× = p^ℤ × μ × U¹`, with `U¹` 2-divisible for odd `p`, and for `p = 2`: `{±1} × (1+4ℤ₂)`, where `Hom(ℤ₂, ℚ/ℤ)` is divisible. `rec(−1)` acts on `μ_{p^k}` by `ζ⁻¹` under either normalization and trivially on `μ_{N'}`, so `cyc_N(rec(−1)) = u`. Edge cases: `k = 0` gives `u = 1` and the claim "unramified χ has a square root" is true. `p = 2, k = 1` gives `u = 1` and is true too (χ factors mod `N'`). `ZMod.cast` is reduction because the moduli divide `N` |
| t31 `GlueDescent.B2Q.LeafUnramified` (L8802) | OK | The pullback is inflated from `D_P ≅ Gal(L_P/ℚ_p)`, which is cyclic unramified. `H²(C_f, ℤ/2)` can be nonzero (f even), but it dies under inflation to `C_{2f}`, hence in `G_{ℚ_p}`. The trivializing cochain lives on a finite quotient, so it is locally constant. `UnramifiedAt` covers every prime containing `p`, with `e = 1`; residue fields are finite, so this means unramified |
| t29a `LeafPush.T29a_DivisionNormalizer p` (L11889) | OK | Anisotropic `x x̄` forces `a, b ≠ 0` and a division algebra. `ℍ[R,a,b] = QuaternionAlgebra R a 0 b` (`i² = a`, `j² = b`; VERIFIED). The integral elements form the maximal order. Any `π` with `v(nrd π) = 1` is not `c·u`, since `v(nrd(cu))` is even. The `c·u` / `c·π·u` decomposition follows from the parity of `v(nrd x)` |
| t29b `LeafPush.T29b_SplitNormalizer p` (L11907) | OK | `N_{GL₂(ℚ_p)}(M₂(ℤ_p)) = ℚ_p^× GL₂(ℤ_p)`: `End(gΛ) = End(Λ)` forces `gΛ = cΛ`. The hypothesis is set equality, and `g⁻¹` is the genuine inverse because `det g` is a unit |

## Checks on the definitions (all VERIFIED by reading the source)

- `Field.absoluteGaloisGroup K` = `AlgebraicClosure K ≃ₐ[K] _`, with `deriving Group, TopologicalSpace`
  (the Krull topology). `absoluteGaloisGroup.map f` is a `→ₜ*` built from an arbitrary
  `IsAlgClosed.lift`. Whether a class vanishes does not depend on that choice (conjugation acts trivially
  on cohomology).
- `AddSubgroup.inertia I G = {σ | ∀ x, σ•x − x ∈ I}` (`Algebra/Group/Subgroup/Basic.lean:1183`).
  `lowerRam` is therefore Serre's `G_i`, defined by `v_B(σb − b) ≥ i+1` for all `b`. This agrees with
  Serre's `i_G` because residue extensions are separable under every leaf's hypotheses.
- `lowerRamR`: `⊤` for `u ≤ −1`, else `G_{⌈u⌉}`. `herbrandPhi` = `∫₀ᵘ |G_t|/|G_0|`, so `φ(u) = u` on `[−1,0]`.
  `upperRam` = `G_{sInf{u ≥ −1 | v ≤ φ u}}`. These match Serre IV §3. Under the leaves' hypotheses
  `B ≃ₐ[A] B = Gal(L/K)` is finite, so no `Nat.card = 0` or `/0` trap arises: `B` is a DVR, finite and
  hence integral over `A`, so `B` is the integral closure of `A` in `L`.
- `FractionRing.liftAlgebra` (local instance, L5084) is the canonical `Frac A → Frac B`. No algebra
  or topology instance is quantified freely in this cluster.
- `𝓞 L` carries the action of `Gal(L/ℚ)` restricted from `L` (`NumberField/Basic.lean:125`).

## 2. Minor findings (documentation, not Lean text)

1. **rv-leaves-b L141 is wrong in one detail.** It says that replacing `θ` by `θ⁻¹` "preserves every
   clause" of I6.10. That is false for clause 3 (L5158-5159): `θ⁻¹(π)` acts on `k_B` by `x ↦ x^{1/q}`,
   which differs from `x^q` once `f(L/K) > 2`. The leaf is still true, because the arithmetic
   normalization (Serre, *Local fields* XIII §4; Cassels–Fröhlich, Serre §2.8, UNVERIFIED locators) gives
   `θ(π)|_{K^{ur}} = Frob` and satisfies clause 3. Clauses 1, 2 and 4 are indeed invariant under `θ⁻¹`.
   STANDARD.
2. **Docstring L5147-5148** says "The canonical reciprocity map is one such θ". That is true only in the
   arithmetic normalization. With Deligne's geometric normalization the canonical map is `θ⁻¹` and fails
   clause 3. Suggested wording: "The reciprocity map normalized so that uniformizers act as the arithmetic
   Frobenius (Serre's convention) is one such θ."
3. Locator inconsistency for T31, `cd ℤ̂ = 1`: h-decomposition.md L854 cites "Serre, *Galois cohomology*
   II §3", while glue-descent.md L239 cites "I §3". Both are UNVERIFIED; the right one is I §3–§4
   (SPECULATIVE).

The other rv-leaves-b repairs are applied. Repair 3 (cochain forms in the bundle) is at L19159-19161.
Repair 4 (transport citation for T20/T21) is in the docstring at L5700-5706.

## 3. Instantiation attempts (none breaks a leaf)

- t16b on non-complete fields: excluded by `IsAdicComplete (maximalIdeal A) A`. On infinite extensions:
  excluded by `Module.Finite A B`. In characteristic p (`𝔽_q[[t]]`): local CFT, the upper numbering
  theorem and Hasse–Arf all hold, and separability is a hypothesis. Trivial extension `B = A`: `θ = 1`,
  every `x` is its own norm, and `b^q ≡ b` holds on `𝔽_q`. The leaf is true in all these cases.
- t16a: stated only for `ℚ_p`, and only for finite abelian `L`. True.
- t22a/b with `C = A` or `C = B`: degenerate, and true.
- t30 with `N = 1`, `k = 0` and `p = 2, k ≤ 1`: true (checked above).
- t31 with an even residue degree `f`: the finite-level class may be nonzero, but the leaf asks about
  `G_{ℚ_p}`, where it dies. True.
- t29a with `a = 0` or `b = 0`: the hypothesis fails (`i·ī = −a = 0`), so it is vacuous only on
  degenerate algebras. That is intended.

## 4. Optional Lean sanity probes (append to a copy of Leaves.lean; none settles a doubt, since there is none)

```lean
-- P1: G^0 = G_0, which clause 4 of t16b uses at v = 0.
example (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]
    [Finite (B ≃ₐ[A] B)] : PkgI6.upperRam A B 0 = PkgI6.lowerRam A B 0 := by
  have h := PkgI6.upperRam_phi_nat A B 0
  simpa [PkgI6.phi_zero] using h

-- P2: t30 at p ∤ N (k = 0): the hypotheses force u = 1, so the leaf says "χ unramified at p
-- has a local square root" (true).
example (p : Nat.Primes) (N : ℕ) [NeZero N] (hp : ¬ (p : ℕ) ∣ N) (u : (ZMod N)ˣ)
    (h1 : ((u : ZMod N).cast : ZMod (N / (p : ℕ) ^ N.factorization p)) = 1) : u = 1 := by
  have h0 : N.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hp
  rw [h0, pow_zero, Nat.div_one] at h1
  ext
  simpa [ZMod.cast_id] using h1
```

(P2's `rw` rewrites a type index. If it hits a motive error, use `simp only [h0, pow_zero, Nat.div_one] at h1`
or `obtain` with `subst`. These probes are cosmetic.)
