# rv-a6-route: adversarial review of pkg-I2's Raynaud route for step A6 (Lemma PR(ii))

Status: research note (task rv-a6-route, 2026-11-11). Subject: `docs/research/pkg-I2.md` §4.2 and
the `sorry` in `scratch/pkg-I2/I2.lean` (`goodReduction_of_QM_rational3`). Files:
`scratch/rv-a6-route/A6.lean` (compiles), `scratch/rv-a6-route/quat_check.py` (PARI/Python
checks), `scratch/rv-a6-route/log.md`. No file under `ZInQKernel/`, `blueprint/`, or another
task's notes or scratch was edited.

Marks: **VERIFIED** (read in a source, computed, or compiled), **STANDARD** (published, reference
given), **SPECULATIVE**. There was no network, so every theorem number is from memory or from
h-b1/h-trust/pkg-I2 and is **UNVERIFIED**.

## Verdict: SOUND AFTER REPAIRS

The Raynaud route proves Lemma PR(ii) as h-b1 §4 states it and as h-trust A6 uses it: good
reduction of `A` and of every conjugate `σA` at every finite place `v ∤ 3` of `K`, including
`v | 2`. It uses three published inputs:

- Raynaud's criterion at `m = 3` (SGA 7 I, Exp. IX, Prop. 4.7), combined with SGA 7 IX 3.5 (⇒);
- Néron–Ogg–Shafarevich (Serre–Tate 1968, Thm 1, (c) ⇒ (a));
- `A(K̄)[n] ≅ (ℤ/n)^{2g}` (Mumford, *Abelian varieties*, §4 / §6).

Everything else is elementary algebra. The route needs none of SGA 7 IX 3.6, the toric-part
argument with the general Néron mapping property, Serre–Tate Thm 2, or the torsion-freeness of
`1 + 3M₄(ℤ₃)`.

Two repairs are needed. Both fix the wording of step 2–3 of pkg-I2 §4.2; neither changes the
route.

- **R1 (step 2: freeness of `A[3ⁿ]`).** pkg-I2 says "the cardinality `3^{4n}` with exponent `3ⁿ`
  forces `A[3ⁿ] ≅ Λ/3ⁿ`". **This is false for every `n ≥ 1` (VERIFIED).**
  - Counterexample: `Λ/Π^{2n−1} ⊕ Λ/Π` has order `3^{4n}` and exponent `3ⁿ`, but as a group it is
    `(ℤ/3ⁿ)² ⊕ (ℤ/3^{n−1})² ⊕ (ℤ/3)²`. The Smith normal forms are computed in `quat_check.py`:
    `Λ/Π^a` has elementary divisors `(3,3)`, `(3,3,3,3)`, `(9,9,3,3)`, `(9,9,9,9)` and
    `(27,27,9,9)` for `a = 1, …, 5`.
  - At `n = 1` even the full group structure does not force freeness: `Λ/Π ⊕ Λ/Π = 𝔽₉²` is
    group-isomorphic to `(ℤ/3)⁴`.
  - Repair: use the full group structure `(ℤ/3ⁿ)⁴`, which I2-Tors supplies, and only `n = 2k ≥ 2`,
    which is all the route uses. The proof is §3 step 2 below. It replaces the appeal to the
    classification of finite `Λ₃`-modules with a five-line Nakayama argument.
- **R2 (step 3: why `c² ≡ 0` forces `c ∈ 3ᵏΛ`).** pkg-I2 cites "`nrd = x² − 2y² + 3z² − 6w²` is
  anisotropic mod 3". **That is false for the quaternary form: `(0,0,1,0)` is a zero mod 3.**
  - The correct input is that `B ⊗ ℚ₃` is a division algebra, so `v_Π` is a valuation on
    `Λ₃ = Λ ⊗ ℤ₃` (equivalently, `nrd` is anisotropic over `ℚ₃`, not mod 3).
  - A finite substitute is also available: `c² ≡ 0 (mod 9)` implies `c ≡ 0 (mod 3)` in `Λ/9`,
    and then induction on `k`. This was VERIFIED exhaustively over the `3⁸` elements of `Λ/9`;
    the analogous step mod 81 on `3Λ/81` was also checked exhaustively.

**Lean (VERIFIED: compiles; `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound`):**

- `RvA6.goodReduction_of_QM_rational3` in `scratch/rv-a6-route/A6.lean` has the statement of
  pkg-I2's `goodReduction_of_QM_rational3`. It is **proved** from four inputs:
  - the leaves `NeronOggShafarevich`, `RaynaudCriterion` and `TorsionStructure` (copied verbatim
    from `scratch/pkg-I2/I2.lean`);
  - one new pure-algebra glue statement, `QuatUnipotentTrivial`. Its valuation step (§3 step 4)
    is proved separately in `scratch/rv-a6-route/QuatVal.lean` (`RvA6.quat_sq_dvd`, every `k`).
- `QuatUnipotentTrivial` is a statement about a commutative group with three endomorphisms. It
  mentions no schemes and no Galois groups, and is **not yet proved in Lean**. Its proof (§3)
  is complete on paper. It is elementary and finite-level, and needs nothing beyond Mathlib's
  `ZMod`, linear maps and cardinalities.
- So the A6 `sorry` of pkg-I2 is reduced to a self-contained algebra lemma: a good,
  crowdsourceable glue item, estimated at a few hundred lines (SPECULATIVE).

## 1. What is being proved, and what the Lean statement says

**Lemma PR(ii)** (h-b1 §4) states: `A/K` is the abelian surface of a point `x ∈ Y₃(K)`, and it
has good reduction at every finite place `v ∤ 3` of `K`. h-trust A6 also needs every conjugate
`σA = A_{σx}`. Its consumers are N5 L529-530, L557-558, L752-753, L778-781 and L847-850 (the
h-b1 §4 table, VERIFIED by reading h-b1). Every consumer is at a place `v ∤ 3`.

**Inputs from step 1 of h-b1's proof (A4).** These are unchanged by the route:

- `ι: 𝒪 → End_K(A)` is defined over `K`;
- `A[3] ⊂ A(K)`, from the level structure `η`.

Manuscript L411 fixes `B = (2, −3)` and `𝒪 = ℤ[i, (1+j)/2]` (VERIFIED by reading), so
`Λ = ℤ⟨i, j⟩ ⊂ 𝒪`.

**Lean statement (pkg-I2, unchanged).** Hypotheses:

- `A : Grp (Over (Spec K))` is an abelian variety with `topologicalKrullDim = 2`;
- `I, J : A ⟶ A` are homomorphisms of group objects over `K`, with `I² = 2`, `J² = −3` and
  `IJ = −JI` on `K̄`-points;
- every `σ ∈ Aut(K̄/K)` fixes `A(K̄)[3]`;
- `O ⊂ K` is a DVR valuation subring with `3 ∈ Oˣ`, and `w ⊂ K̄` lies over `O`.

Conclusion: `HasGoodReduction A O`.

Faithfulness to PR(ii):

- Each hypothesis is implied by A4.
- The conclusion at an arbitrary DVR `O ∌ 3⁻¹` covers every finite place `v ∤ 3`.
- The conjugates satisfy the same hypotheses (`σA = A_{σx}` with `σx ∈ Y₃(K)`), so the same
  theorem applies to them.
- What is not formalized: the existence of `w` over a given `O`, which follows from the
  extension of valuations (STANDARD, glue).

Everything is VERIFIED by reading `I2.lean` and h-b1.

## 2. The route, step by step, with the burden of proof on it

Notation: `σ` is an element of the inertia group of `w`, `N = σ − 1` on points, and `k ≥ 1`.

1. **Raynaud.** By A4, `A[3]` is rational over `K`, and `3 ≥ 3` is prime to `p`. So `A` has
   semistable reduction (SGA 7 IX 4.7), and inertia acts on `T_ℓ` with `(σ−1)² = 0` for every
   `ℓ ≠ p` (SGA 7 IX 3.5 ⇒). The leaf `RaynaudCriterion` states the finite-level consequence.
   Apply it with `ℓ = 3` at level `3^{2k}`: `N² = 0` on `T := A[3^{2k}]`.
   - Checked: the leaf's hypothesis is exactly "`A[m]` is `K`-rational" with `m = 3`, invertible
     in `O`.
   - Checked: `ℓ = 3` is allowed whenever `p ≠ 3`, in particular at `p = 2`.
   - Semistability does not depend on `ℓ` (SGA 7 IX 3.5, STANDARD).
2. **Torsion.** I2-Tors with `g = 2` gives `T ≅ (ℤ/3^{2k})⁴` as groups. `3` is invertible in `K`,
   since it is a unit of `O ⊂ K`.
3. **`N` is `Λ`-linear.** `I` and `J` are defined over `K`, so they commute with `σ`. In Lean this
   is associativity of composition: `σ·(x ≫ I) = (σ·x) ≫ I`. Hence `N` commutes with `I` and `J`.
4. **Algebra (`QuatUnipotentTrivial`, §3).** From steps 1-3, `N` vanishes on `A[3ᵏ]`.
   - This step uses that `B ⊗ ℚ₃` is a division algebra.
   - VERIFIED: `hilbert(2,−3,3) = −1`, `hilbert(2,−3,2) = −1` and `hilbert(2,−3,∞) = +1`, so `B`
     ramifies exactly at `{2,3}` (disc 6, consistent with `μ² = −6`).
   - VERIFIED: the trace form of `Λ` on `1, i, j, ij` has determinant `−576 = −24²`. So the
     reduced discriminant is 24, its 3-part is 3, and `Λ₃` is the maximal order.
   - The split case shows the input is necessary: in `M₂(ℤ/9)`, `[[0,1],[0,0]]` squares to 0 and is
     not divisible by 3.
5. **NOS.** Inertia is trivial on `A[3ᵏ]` for every `k ≥ 1`, which is infinitely many `m` prime
   to `p`. Serre–Tate Thm 1, (c) ⇒ (a), gives good reduction at `O`.

**Adversarial checks of the leaves as used here** (no new defect found beyond those that
pkg-I2 already lists generally):

- `RaynaudCriterion` is a consequence of the published statements (4.7 with 3.5 ⇒). Its
  hypothesis (all of `Aut(K̄/K)` fixes `A[m]`) is at least as strong as the published one.
- SGA 7 is written over a henselian (or strictly henselian) base, while the leaf is stated over
  a global `K` with a DVR `O`. The bridge is the identification of the decomposition and inertia
  groups at `w` with those of the henselization, together with compatibility of semistability and
  of the Néron model with étale base change (BLR 7.2/1, UNVERIFIED locator). This is STANDARD,
  and the same issue applies to the NOS and D2 uses that pkg-I2 already has. It is a citation
  task for the leaf, not a gap in the route.
- `K̄ = AlgebraicClosure K`, not `K_s`. In characteristic 0 (the use case) they coincide. In
  general `Aut(K̄/K) = Gal(K_s/K)`, and `A(K̄)[m] = A(K_s)[m]` for `m` invertible.
- `TorsionStructure` measures the dimension as `topologicalKrullDim` of the underlying space. For
  a `K`-variety this is the usual dimension (STANDARD).
- No hypothesis of the A6 statement is used vacuously. All of `hI`, `hJ`, `hIJ`, `hrat`, `h3`
  and `hdim` are consumed in the Lean proof.

## 3. Proof of `QuatUnipotentTrivial` (the remaining glue; paper proof complete)

**Statement.** Let `G` be a commutative group (written additively here) and `k ≥ 1`. Let
`T = G[q]` with `q = 3^{2k}`, and suppose `T ≅ (ℤ/q)⁴`. Let `I, J, S ∈ End(G)` satisfy
`I² = 2`, `J² = −3`, `IJ = −JI`, `SI = IS` and `SJ = JS`, and suppose `N := S − 1` has `N² = 0`
on `T`. Then `N = 0` on `G[3ᵏ]`.

`Λ = ℤ⟨i,j⟩/(i² − 2, j² + 3, ij + ji)` is free over `ℤ` on `1, i, j, ij`. The ring map `Λ → End(T)`
(`i ↦ I`, `j ↦ J`) makes `T` a `Λ/q`-module, and `N` is `Λ`-linear.

1. **`|T/JT| = 9`.**
   - `3T = J²T ⊂ JT`.
   - `I` preserves `JT`, since `IJ = −JI`.
   - So `T/JT` is a module over `𝔽₃[x]/(x² − 2) = 𝔽₉` (2 is not a square mod 3), and
     `|T/JT| = 9^d` with `d ≤ 2`, because `T/3T ≅ 𝔽₃⁴`.
   - `d = 0` is impossible: `T = JT` would give `T = J^{2·2k}T = 3^{2k}T = 0`.
   - `d = 2` is impossible: then `JT = 3T`, so `J = 3J'` for some `J'`, since `T` is a free
     `ℤ/q`-module. Then `−3 = 9J'²`, so `3(1 + 3J'²) = 0`. As `3J'²` is nilpotent, `3 = 0` on `T`,
     contradicting `q ≥ 9`.
2. **`T` is free of rank one over `Λ/q`.**
   - Pick `x ∉ JT`. Then `ℤ[I]·x + JT = T`, since `T/JT` is a 1-dimensional `𝔽₉`-space.
   - So `T = Λx + JT = Λx + J²T = … = Λx + J^{4k}T = Λx`.
   - The map `Λ/q → T, λ ↦ λx` is onto, and both sides have `q⁴` elements, so it is bijective.
3. **`N` is right multiplication.** Write `N x = c x` with `c ∈ Λ/q`. Then
   `N(λx) = λNx = λcx`, and `N²x = N(cx) = cNx = c²x`. So `c² = 0` in `Λ/q`.
4. **`c ∈ 3ᵏΛ`.**
   - `Λ₃` is the maximal order of the division algebra `B ⊗ ℚ₃` (§2 step 4), and `v_Π` is a
     valuation with `v_Π(3) = 2`.
   - Lift `c` to `Λ₃`. Then `2v_Π(c) = v_Π(c²) ≥ 4k`, so `c ∈ Π^{2k}Λ₃ = 3ᵏΛ₃`.
   - Elementary alternative: `c² ≡ 0 (mod 9)` gives `c ≡ 0 (mod 3)`, which was checked
     exhaustively (VERIFIED). Then induct on `k` with `c = 3c'`.
5. **Conclusion.**
   - `G[3ᵏ] ⊂ T`, and `G[3ᵏ] = T[3ᵏ] = 3ᵏT`, since `T ≅ (ℤ/3^{2k})⁴`.
   - For `y ∈ T`, `N(3ᵏy) = 3ᵏ·(λcx) ∈ 3^{2k}T = 0`, where `y = λx`. ∎

## 4. Lean

`scratch/rv-a6-route/A6.lean` (VERIFIED: compiles with `lake env lean`; no `sorry`, no `axiom`):

- §§1-9 are a verbatim copy of `scratch/pkg-I2/I2.lean` lines 1-443, with the namespace
  `PkgI2` renamed to `RvA6`.
- `QuatUnipotentTrivial : Prop` is the statement of §3 over `[CommGroup G]`, written
  multiplicatively, with the torsion iso in the format of `TorsionStructure`.
- `galHomPts A σ` and `endPts A f` are the Galois action and an endomorphism, as `MonoidHom`s
  on `A(L)`. They use `MonObj.one_comp` and `MonObj.mul_comp`.
- `RvA6.goodReduction_of_QM_rational3 (hNOS hRay hTors hAlg …) : HasGoodReduction A O` is proved
  in about 35 lines. It follows §2:
  - for each `k ≥ 1`, Raynaud at level `3^{2k}`, Tors at `n = 3^{2k}` and `hAlg` give
    `InertiaTrivialOn A w (3ᵏ)`;
  - then NOS (c), with the injective family `k ↦ 3^{k+1}`.

  `#print axioms`: `[propext, Classical.choice, Quot.sound]`.

`scratch/rv-a6-route/QuatVal.lean` (VERIFIED: compiles; no `sorry`; standard axioms) proves
§3 step 4 (repair R2) for every `k`, in coordinates. `x² = (a² + 2b² − 3c² + 6d²) +
2a(bi + cj + d·ij)` for `x = a + bi + cj + d·ij ∈ Λ`, and `RvA6.quat_sq_dvd k` says: if `3^{2k}`
divides the four coordinates of `x²`, then `3ᵏ` divides `a, b, c, d`. The base case
`quat_base` is a hand proof (with `decide` only over `ZMod 3`), so no exhaustive kernel
computation is needed.

**Still open in Lean:** steps 1-3 and 5 of the proof of `QuatUnipotentTrivial` (§3): `T` is free
of rank one over `Λ/3^{2k}`, and `N` is right multiplication by some `c` with `c² = 0`. It is pure algebra on a finite
abelian group of order `3^{8k}`. Mathlib has the ingredients: `ZMod`, `Module.End`,
`Nat.card`, `Fintype.card` of a free module, and bijectivity from injectivity on equal finite
cardinalities. One way to discharge §3 step 4 without valuation theory is the computation mod 9
plus induction on `k`. The kernel cost of a `decide` over `3⁸` quaternions mod 9 is untested.

## 5. Effect on the decomposition

For A6, the leaf list is **I2-Ray, I2-NOS, I2-Tors**. The glue is
`goodReduction_of_QM_rational3`, proved, plus `QuatUnipotentTrivial`, paper proof §3. With the
Raynaud route:

- Leaves dropped from A6: I2-SS (SGA 7 IX 3.6 + 3.5), I2-ST2 (Serre–Tate Thm 2), and the
  Néron-model toric-part functoriality and general Néron mapping property, which cannot be stated
  (pkg-I2 §2).
- I2-Ray is needed anyway for D2.
- h-trust A6 and its suppliers line should be updated by the integration task, not here:
  - "Suppliers: A4; Raynaud (SGA 7 IX 4.7 + 3.5); Serre–Tate Thm 1; Mumford §4 (structure of
    `A[n]`); `B ⊗ ℚ₃` division (computed)";
  - h-b1's step 2-3 argument stays as a second route.

## Changelog

- 2026-11-11, task rv-a6-route: first version.
