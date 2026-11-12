# glue-I6-rest: the remaining glue of package I6 and of the conductor cluster

Status: research note (task glue-I6-rest, 2026-11-11). Lean files: `scratch/glue-I6-rest/I6Base.lean`
(pkg-I6's `I6.lean` copied, plus glue), `scratch/glue-I6-rest/Conductor.lean` (D4) and
`scratch/glue-I6-rest/SqrtChar.lean`. Results log:
`scratch/glue-I6-rest/log.md`. No file under `ZInQKernel/`, `blueprint/`, or another task's
notes or scratch directory was edited.

Marks: **VERIFIED** means compiled or read in a source. **STANDARD** means a published theorem.
**SPECULATIVE** means an assessment. Locators from memory are UNVERIFIED.

## Verdict

**Three of the six glue items are proved in Lean: D3, D4 and the Galois theory for `e ≤ a!`.
A fourth, the square-root criterion, is proved in its group-theoretic core.** The proofs have no
`sorry`, and `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` (VERIFIED:
`lake env lean` on the three files, 22:28, 22:31 and 22:34 PST, no errors). Two items remain
open: cyclic inflation and Frobenius density. So does the local-field part of the square-root
criterion.

| Item | Status | Lean |
| --- | --- | --- |
| D3 `sq_principalUnits` | **proved** (adopted glue-conductor's Hensel argument) | `PkgI6.sq_principalUnits` |
| D1 (a), Galois theory for `e ≤ a!` | **proved**, global form (see caveat 2) | `PkgI6.finrank_splittingField_le_factorial`, `finrank_isSplittingField_le_factorial`, `ramificationIdx_le_finrank_of_numberField`, `ramificationIdx_le_factorial` |
| B2 square-root criterion from I6.3 | **group-theoretic core proved**; the local-field part is open | `GlueI6Rest.exists_half_iff` |
| D4 `artinConductor_le_of_upper` | **proved**, pkg-I6's statement with fewer hypotheses | `PkgI6.artinConductor_le_of_upper` (`Conductor.lean`) |
| B2 `[ε]_p = 0` at unramified `p` (cyclic inflation) | open | — |
| C10 Frobenius density in `G_ℚ` from I6.4 | open | — |

## 1. What is proved

All statements are over pkg-I6's definitions or over Mathlib objects. The leaf hypotheses
(`def … : Prop`) are copied unchanged from `scratch/pkg-I6/I6.lean`.

1. **`sq_principalUnits` (D3).** Let `B` be a complete DVR with `(2) = 𝔪^e`, `e ≥ 1`, and let
   `r > e`. Then every `y ∈ 𝔪^{r+e}` has some `x ∈ 𝔪^r` with `(1+x)² = 1+y`. This is pkg-I6's
   statement, unchanged. The proof takes glue-conductor's `exists_sq_eq_one_add` verbatim
   (Dyadic.lean: `u² + u = z/4`, Hensel via `IsAdicComplete.henselianRing`) and sets
   `s = r − e`. Applied twice, it gives `U^{3e+1} ⊆ (U^{e+1})⁴`. So Silverman AEC IV.6.4 is not
   a leaf. (VERIFIED)
2. **`finrank_splittingField_le_factorial`.** If `f ∈ K[X]` is separable, then
   `[SplittingField f : K] ≤ (deg f)!`. The proof uses `Gal f ↪ Perm(rootSet f)`
   (`galActionHom_injective`), `#rootSet ≤ deg f`, and `|Gal f| = [SplittingField f : K]`.
   `finrank_isSplittingField_le_factorial` gives the same bound for any splitting field.
   (VERIFIED)
3. **`ramificationIdx_le_finrank_of_numberField`.** For a number field `L` and a prime `P` of
   `𝓞 L`, `P.ramificationIdx ℤ ≤ [L:ℚ]`. The proof uses Mathlib's
   `sum_ramification_inertia_eq_finrank` and `inertiaDeg_pos`; `P = ⊥` is treated separately.
   (VERIFIED)
4. **`ramificationIdx_le_factorial`.** If `L` is a splitting field over `ℚ` of a separable `f`,
   then every prime `P` of `𝓞 L` has `e(P) ≤ (deg f)!`. That is the hypothesis `hea` of
   glue-conductor's `D1_genuine`, which uses the same `P.ramificationIdx ℤ`. Since
   `D1_genuine` is in another task's scratch file, the two were not composed in one file.
   (VERIFIED)
5. **`exists_half_iff` (B2, the core of the square-root criterion).** Let `Γ` be any abelian
   group and `χ : Γ →+ ℚ/ℤ`. Then `χ = 2ψ` for some character `ψ` iff `χ` vanishes on
   `Γ[2] = {g | 2g = 0}`. The proof factors `χ` through `Γ/Γ[2] ≅ 2Γ` and extends it to `Γ`
   with Mathlib's `CharacterModule.dual_surjective_of_injective` (`ℚ/ℤ` is injective by Baer).
   Finite-order characters take values in `μ_∞ ≅ ℚ/ℤ`, so this is pkg-I6's "a character of an
   abelian group is a square iff it kills `Γ[2]`". (VERIFIED)
6. **`artinConductor_le_of_upper` (D4), in `Conductor.lean`.** pkg-I6's definitions
   (`lowerRam`, `lowerRamR`, `herbrandPhi`, `upperRam`, `codimInv`, `artinConductor`) are copied
   verbatim. Statement: if `ρ σ = 1` for every `σ ∈ G^v` and every `v > U ≥ 0`, then
   `f(V) ≤ dim V·(1+U)`. The hypotheses are only `[IsLocalRing B]`, `[Finite (B ≃ₐ[A] B)]` and
   `[FiniteDimensional k V]`; pkg-I6 also had `IsDomain B` and `IsDiscreteValuationRing B`.
   So the theorem implies pkg-I6's statement. The proof:
   - The integrand `h(t) = |G_t|/|G_0|` of `φ` is antitone, hence interval-integrable, and
     `h ≥ 1/|G_0|`.
   - `phi_sub_ge`: `(u'−u)·h(u') ≤ φ(u') − φ(u)`. Hence `φ` is strictly increasing
     (`phi_strictMono`), and `G^{φ(b)} = G_b` (`upperRam_phi_nat`, via `IsLeast.csInf_eq`).
   - `sum_hInt_le`: `Σ_{i≤b} |G_i|/|G_0| ≤ 1 + φ(b)`.
   - `phi_nat_ge`: `φ(i) ≥ i/|G_0|`. So only finitely many `i` have `φ(i) ≤ U`, and no Krull
     intersection argument is needed.
   - If `codim V^{G_i} ≠ 0`, then `G^{φ(i)} = G_i` acts nontrivially, so `φ(i) ≤ U`.
   - The sum over those `i` is at most `dim V·Σ_{i≤M} |G_i|/|G_0| ≤ dim V·(1 + φ(M)) ≤ dim V·(1+U)`.

   (VERIFIED)

## 2. Caveats

1. In `I6Base.lean`, `artinConductor_le_of_upper` (a `theorem … := sorry` in pkg-I6) appears as
   the statement `def ArtinConductorLeOfUpper : Prop`. Its proof is in `Conductor.lean`, which
   cannot be imported (scratch files cannot import each other); the integration should merge
   the two files.
2. **Global versus local `e ≤ a!`.** Glazer's D1 is local: `F/ℚ_p` has degree `≤ a`, and `F̃` is
   its Galois closure. Item 4 gives `e ≤ a!` when the global field `L` of `D1_genuine` is the
   Galois closure of a global field of degree `≤ a`. In the application (`F = L_v(A[n])`,
   `a = D·G₀`), only the local degree is bounded. The global degree `[L:ℚ]` may be larger.
   Two ways to close this, both SPECULATIVE:
   - (i) Choose a global `K` of degree `[F:ℚ_p]` with `K_v = F` (Krasner), so that `L` is the
     Galois closure of `K`. Then `e(P) ≤ |D_P| ≤ [F̃:ℚ_p] ≤ a!`. This needs the bound on the
     decomposition group, which is the same Galois theory applied to the local minimal
     polynomial.
   - (ii) Bound `e(P) = |I_P| ≤ |D_P|` (Mathlib's `card_inertia_eq_ramificationIdxIn`), and
     `|D_P| = [L_P:ℚ_p]`, where `L_P` is the splitting field over `ℚ_p` of a degree-`a`
     polynomial, so item 2 applies over `ℚ_p`. This needs `D_P ≅ Gal(L_P/ℚ_p)` (completion;
     Serre II §3, UNVERIFIED). It is not in Mathlib.
3. Separability of `f` is a hypothesis of item 4. A minimal polynomial over `ℚ` is separable.

## 3. What remains, with the reason

1. D4: done (§1, item 6).
2. **`[ε]_p = 0` at `p ∉ T` (cyclic inflation). About 200-400 lines (SPECULATIVE). Not done.**
   On cochains (pkg-I6's `IsCocycle2`), the statement is that a 2-cocycle on the procyclic
   quotient `G_{ℚ_p} → Gal(L_v/ℚ_p) ≅ ℤ/f` with values in `ℤ/2` becomes a coboundary on
   `ℤ/2f`. This needs:
   - (a) Every 2-cocycle of `ℤ/f` with trivial coefficients `ℤ/2` is cohomologous to
     `x·carry_f(a,b)`. That is the finite-cyclic `H²`, available abstractly in Mathlib's
     `GroupCohomology/FiniteCyclic.lean` but not on explicit inhomogeneous cochains.
   - (b) `carry_f(a mod f, b mod f)` is a coboundary on `ℤ/2f`. Take representatives
     `a, b ∈ [0, 2f)` and `h(a) = ⌊a/f⌋`. From `a = f·h(a) + ā` and
     `(a+b mod 2f) = a + b − 2f·carry_{2f}(a,b)`, one gets
     `carry_f(ā,b̄) ≡ h(a) + h(b) − h(a+b mod 2f) (mod 2)`. (VERIFIED by brute force for f = 1..12, all a, b; log.md.)
   - (c) Continuity: the cocycle factors through a finite quotient.

   Part (a) is the cost. The comparison between Mathlib's homogeneous `H²` and inhomogeneous
   cochains is not in Mathlib (pkg-I6 §2, B2, item 4).
3. **The square-root criterion beyond its core.** Two inputs remain, and both are about local
   fields. Size per pkg-I6: 500-1000 lines (SPECULATIVE).
   - (i) From I6.3: a finite-order character of `G_{ℚ_p}` factors through
     `Gal(ℚ_p(μ_{p^k m})/ℚ_p) ≅ (ℤ/p^k)^× × ℤ/f`. This needs the irreducibility of the `p^k`-th
     cyclotomic polynomial over `ℚ_p`, which Mathlib proves only over `ℚ`
     (`cyclotomic.irreducible_rat`). Over `ℚ_p` it is Eisenstein at `p`. It also needs the
     disjointness of the totally ramified and unramified parts.
   - (ii) The 2-torsion of the profinite group `ℤ_p^× × ℤ̂` is `{±1} × {0}` for odd `p`. At
     `p = 2` it is `{±1} × {0}` too: `ℤ_2^× = {±1} × (1+4ℤ_2)`, and `(1+4ℤ_2)` and `ℤ̂` are
     torsion-free. So it is `{1, τ₋₁}`.

   Then `exists_half_iff`, applied to a large enough finite quotient (one whose 2-torsion
   image is generated by `τ₋₁`), gives the criterion. Choosing that quotient is a Galois-theory
   step on `μ_{2^{k+1}}`.
4. **Frobenius density in `G_ℚ` (C10). Not done; SPECULATIVE 200-400 lines.**
   - Its finite-level content, that Frobenius classes meet every coset of every open normal
     subgroup, is exactly the leaf `ChebotarevExists` applied to the fixed field `M`, together
     with surjectivity of restriction `G_ℚ → Gal(M/ℚ)` (Mathlib:
     `AlgEquiv.restrictNormalHom_surjective`).
   - The real glue is to lift a Frobenius at `Q ⊂ 𝓞_M` to an element of `G_ℚ` that is a
     Frobenius at a prime of `\bar ℤ`. That needs decomposition groups in the infinite
     extension `\bar ℚ/ℚ`, as an inverse limit of the finite ones. Mathlib has `IsArithFrobAt`
     and `exists_isArithFrobAt` only for finite group actions (SPECULATIVE; not grepped in
     full).
   - Alternative that avoids the lift (SPECULATIVE): state C10's trace comparison on finite
     quotients. The ℓ-adic representations factor modulo `ℓ^k` through finite Galois groups
     `Gal(M_k/ℚ)`, and finite-level `ChebotarevExists` suffices there, with no density in
     `G_ℚ`. This is the recommended route for the integration.

## 4. Files

| File | Imports | Content | `sorry` |
| --- | --- | --- | --- |
| `scratch/glue-I6-rest/I6Base.lean` | Mathlib | pkg-I6 `I6.lean` (leaves, definitions, its proved glue), `exists_sq_eq_one_add` (from glue-conductor), `sq_principalUnits`, the `e ≤ a!` chain, `ArtinConductorLeOfUpper` as a Prop | none |
| `scratch/glue-I6-rest/Conductor.lean` | Mathlib | pkg-I6 Part II definitions (copied), `artinConductor_le_of_upper` and its lemmas | none |
| `scratch/glue-I6-rest/SqrtChar.lean` | Mathlib | `exists_half_iff` | none |

`#print axioms` (VERIFIED) for the following: `eq_of_same_finite_support`, `skolemNoether_aut`,
`lowerRam_tower`, `cob_of_same_finite_support`, `sq_principalUnits`,
`finrank_splittingField_le_factorial`, `ramificationIdx_le_factorial`, `exists_half_iff`,
`upperRam_phi_nat`, `sum_hInt_le` and `artinConductor_le_of_upper`.
Each prints `[propext, Classical.choice, Quot.sound]`.
