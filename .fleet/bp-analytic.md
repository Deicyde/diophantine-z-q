# bp-analytic: fleet report

**Verdict.** The analytic uniformization (AN3 of bp-faltings, N14/R1an of bp-qmmoduli, used by
R22, T11, T12) does not block any consumer. It is now stated as one leaf over genuine objects,
with no analytification:
- `UniformizationLeaf A` (`IsUniformization A Λ φ`) is about the project's `AbVar`, Mathlib's
  `ℂ`-points and regular functions `Γ(U, 𝒪_A)`.
- It asserts a full lattice `Λ ⊂ ℂ^g` and a group isomorphism `φ : ℂ^g/Λ ≃ A(ℂ)` such that
  (i) regular functions are holomorphic, (ii) `g` regular functions give local holomorphic
  coordinates, and (iii) `φ⁻¹` is continuous for the topology of regular functions.
- It is a consequence of Mumford §1 together with the construction of `A^an` (locators
  UNVERIFIED).

The glue the consumers need over the leaf is proved:
- the period lattice and `g` are well defined up to `ℂ`-linear isomorphism;
- `End(A)` acts on `(ℂ^g, Λ)` by a unital ring homomorphism into `ℂ`-linear maps;
- `A(ℂ)[n] = φ((1/n)Λ/Λ)`.

The leaf's *proof* is the XL package (analytic topology and manifold structure on `X(ℂ)`,
compactness for proper `X`, Lie theory). It is about 15-30k lines (SPECULATIVE) and can be
scheduled last.

**What compiles** (`scratch/bp-analytic/Torus.lean`, about 1 660 lines, Mathlib only, no
`sorry`, no warnings, axioms `propext`/`Classical.choice`/`Quot.sound`):
- `E/Λ` as an analytic manifold, complex Lie group, compact and connected. This fills the
  `IsManifold` TODO of Mathlib's `Instances/Quotient.lean` for lattices.
- The exponential, surjective with kernel `Λ`.
- Liouville; biholomorphic changes of coordinates (`torusDiffeo`).
- Continuous or holomorphic homomorphisms of tori are `ℝ`- or `ℂ`-linear (covering lifts).
- The Siegel period lattice `Ωℤ^g + ℤ^g` is full iff `det Im Ω ≠ 0`.
- `covol(Ωℤ^g + ℤ^g) = |det Im Ω|`: the Faltings archimedean term through the period matrix
  alone.
- Riemann theta quasi-periodicity, and pkg-I1's theta constants as `θ` at 2-torsion points (no
  convergence hypotheses).
- **pkg-I1's `Ω(τ)` is a period matrix of the QM torus `ℂ²/ι(𝒪)(τ,1)ᵀ`.** The lattice is full,
  `F'(τ)` maps `Ω(τ)ℤ²+ℤ²` onto it (biholomorphic group isomorphism), `Ω(τ)` is symmetric, and
  `Ω(τ) ∈ 𝔥₂` for `Im τ > 0`. pkg-I1 had only numerical evidence for this.
- §10: the leaf and its glue (`exists_equiv`, `dim_eq`, `analyticRep` with
  `_id/_comp/_mul`, `torsion_iff`).

**What remains** (docs/research/bp-analytic.md §2-§3, §6):
- Proof of the leaf: A1-A5. A4 (proper ⇒ compact) is the most expensive node.
- Consumer glue: A6 (identifying `η` with `c·dz` via bp-faltings' cotangent model), and complex
  conjugation as an antilinear involution (T12).
- P4 (polarization ⇒ `𝔥_g`) for a general principally polarized `A`.
- A separate GAGA leaf for T11's surjectivity.
- Flagged for bp-qmmoduli: the F1 glue "two Hauptmoduln coincide" needs the analytic
  uniformization of the Shimura curve *in families*. That is not part of AN3 and should be
  recorded in R1an or R1.
- The faithfulness review of the leaf is the author's own, plus one model read-through; no
  human has reviewed it.
