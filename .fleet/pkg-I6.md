# pkg-I6 (2026-11-11): fleet report

Full note: `docs/research/pkg-I6.md`. Lean: `scratch/pkg-I6/I6.lean` (Mathlib only) and
`Check.lean`. Log: `scratch/pkg-I6/log.md`.

**Main result.** Every input of package I6 (h-trust B1, B2, C10, D1, D3, D4) can be stated
today as a concrete Lean Prop over genuine Mathlib objects. All of them compile. This corrects
wk-h §3.2, and it fills the three I6 holes (`L15b`, `L16`, `L20`) that hdec-faithful leaves as
`sorry`. Mathlib v4.35 already has continuous Galois cohomology: `absoluteGaloisGroup.map`,
`continuousCohomology`, and a Tate–Shafarevich subgroup. So the Brauer leaves are stated
directly on `H²(G_ℚ, ℤ/2)`, which avoids the `H² = Br[2]` bridge that no library has. The
**Brauer step of B2 is proved in Lean** from three leaves, both on Mathlib's `H²` and on continuous
cochains (`eq_of_same_finite_support`, `cob_of_same_finite_support`; axioms `propext`,
`Classical.choice`, `Quot.sound`).

**Leaves (10).** Theorem numbers are from memory and marked UNVERIFIED.
- I6.1 Skolem–Noether.
- I6.2a-c: ABHN injectivity, even support, and local `H²` of order 2. Each is stated on
  `H²(G_ℚ, ℤ/2)` and on cochains.
- I6.3 local Kronecker–Weber for `ℚ_p`. It replaces "local reciprocity" in B2's square-root
  criterion.
- I6.4 Chebotarev, existence form, with Mathlib's `IsArithFrobAt`.
- I6.5 Brauer–Nesbitt in characteristic 0.
- I6.6 Serre's bound on the different, `𝔇 ∣ 𝔪^{e−1}(e)`. Mathlib has only the lower bound.
- I6.7 Hilbert's formula for the different.
- I6.8 Herbrand's theorem.
- I6.9 transitivity of `φ`.
- I6.10 local CFT at the finite abelian level, with the upper numbering theorem.

The ramification groups `G_i` (via Mathlib's `AddSubgroup.inertia`), `G^v`, `φ` and Serre's Artin
conductor are given concrete definitions. Tau Ceti proves I6.1, the Br forms of I6.2, I6.4, I6.7
and I6.8 (per prereq-survey, not re-checked). Serre's different bound, Brauer–Nesbitt and local
Kronecker–Weber were not located in any library.

**Glue.**
- Proved here: `skolemNoether_aut`, both Brauer steps, `lowerRam_tower`.
- `sorry` here: `artinConductor_le_of_upper` (D4) and `sq_principalUnits` (D3). glue-conductor
  has already proved the second in `Dyadic.lean`.
- Still to be written: the square-root criterion from I6.3 (500-1000 lines), the vanishing of
  `[ε]_p` at unramified `p` (cyclic inflation), and Frobenius density.
- Finding (SPECULATIVE, not reviewed): D3 does not need the norm functoriality of reciprocity.
  `β⁴ = χ²` is unramified at 2, so I6.10 for `F` alone suffices.

**Biggest obstacle.** The leaves can be stated. What they are applied to cannot be, yet:
- `End⁰(A_{\bar ℚ})` in B1;
- the cocycle `ε` built from the `μ_σ`;
- the ℓ-adic `r_ℓ` and its conductor in C10 and D1-D4, which meet Carayol (I4).

So I6 can be crowdsourced now, but gluing it to H waits on I1-I4.
