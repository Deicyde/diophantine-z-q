# glue-descent: Glazer's scalar descent (h-trust B1-B3, C1) as lemmas, leaves and Lean

Status: research note (task glue-descent, 2026-11-11). Scope: steps B1, B2, B3 and C1 of
`docs/research/h-trust.md` (manuscript N5 = `diophantine_zq.tex`, L632-731). Lean drafts:
`scratch/glue-descent/` (1713 lines; build with `scratch/glue-descent/build.sh`); log:
`scratch/glue-descent/log.md`. No file under `ZInQKernel/`, `blueprint/` or other notes was
edited.

Marks: **VERIFIED** = read in a source, computed, or compiled by Lean; **STANDARD** = a published
theorem with a reference (theorem numbers from memory are marked UNVERIFIED: there is no network);
**SPECULATIVE** = an assessment.

## Summary

1. **B2 and B3 are now Lean theorems over genuine Mathlib objects, proved from four stated
   leaves (VERIFIED, compiled; axioms `propext`, `Classical.choice`, `Quot.sound`).** The objects
   are `G_ℚ = Field.absoluteGaloisGroup ℚ` with its Krull topology, `G_{ℚ_p}` with Mathlib's
   continuous map `absoluteGaloisGroup.map : G_{ℚ_p} → G_ℚ`, `ℚ̄ = AlgebraicClosure ℚ`,
   Mathlib's `modularCyclotomicCharacter`, `DirichletCharacter`, `IntermediateField` and `𝓞 L`.
   - `GlueDescent.B2Q.b2_of_leaves` takes:
     - a finite Galois `L ⊂ ℚ̄` unramified outside a finite set `T` of primes;
     - a continuous sign 2-cocycle `ε` of `G_ℚ`, inflated from `Gal(L/ℚ)`.

     It produces:
     - a Dirichlet character `χ`, its level supported in `T`, with
       `ord χ ≤ 2 ∏_{p∈T, p≠2}(p−1)`;
     - a continuous `β : G_ℚ → ℂ^×` with `β² = χ` and `β(σ)β(τ) = ε(σ,τ)β(στ)`.
   - `GlueDescent.B3Q.b3_of_leaves` adds an arbitrary continuous quadratic twist `η` and
     produces the kernel field `L' ⊇ L` of `(βη)|_{G_L}`:
     - `L'` is Galois over `ℚ`;
     - `G_{L'} = {σ ∈ G_L : β(σ) = 1}`;
     - `β` is constant on the cosets of `G_{L'}`;
     - `[L':ℚ] ≤ 2·ord(χ)·[L:ℚ]`.
   - `b3_degree_le_QM` gives N5's `[L':ℚ] ≤ Q·M` against the repository's own
     `heightQ R * contactSupport S u`. The astronomically large `D` is never evaluated: only
     `1 ≤ D ≤ R`, `10¹² ≤ R` and `10 ≤ E₀` are used.
2. **B1 and C1: all the algebra is proved; only the instantiation waits.** The following are
   theorems over arbitrary groups, fields and vector spaces (VERIFIED):
   - the cocycle identity of the discrepancy `c`;
   - the sign normalization `a_σ a_τ c = sign(c) a_στ` with `a = deg^{−1/4}`;
   - `ρ(σ) = β(σ)^{−1} a_σ T_σ` is a representation;
   - `ρ` commutes with `B ⊗ E` and is the Tate action on `G_{L'}`;
   - matrix units give `ρ ≅ r ⊕ r` with `dim r = 2`.

   N5's algebra `B = (2,−3)` is shown central and simple in Lean (its norm form is anisotropic
   over `ℚ`), so the Skolem–Noether leaf applies to it, and the centralizer step `c ∈ ℚ^×` is
   proved. The instantiation needs an abelian-variety layer with Tate modules, Galois conjugates
   and degrees. pkg-I3's `PkgI3.AbVar` supplies most of it (§4).
3. **Leaves of this cluster: 7.** Two of them, L-B3a and L-B3b, are needed only for the
   unramifiedness of `L'`.

   | Leaf | Statement |
   | --- | --- |
   | L-B1 | Skolem–Noether |
   | L-B2a | Hasse principle for `H²(G_ℚ, ±1)` at the finite places |
   | L-B2b | `|H²(G_{ℚ_p}, ±1)| ≤ 2` |
   | L-B2c | explicit local square-root criterion for Dirichlet characters |
   | L-B2d | unramified classes vanish locally |
   | L-B3a | unique quadratic character of tame inertia |
   | L-B3b | where a quadratic Dirichlet character ramifies |

   L-B1, L-B2a, L-B2b, L-B2c and L-B2d are stated in Lean as `def … : Prop` over Mathlib objects
   (they elaborate). L-B3a and L-B3b need inertia subgroups of `G_ℚ`, which Mathlib lacks.
4. **What is not formalized** (all SPECULATIVE as cost estimates):
   - the unramifiedness of `L'` outside `T`. Its group-theoretic core is proved
     (`twist_kills_inertia`, `inertia_le_kernel`); the rest needs inertia subgroups of
     `G_ℚ` and L-B3a, L-B3b;
   - the abelian-variety instantiation of B1 and C1;
   - continuity of `ρ_ℓ` in the ℓ-adic topology. No B or C step uses it beyond what Pan's
     theorem (C7) needs.

## 1. The four steps as lemmas

Notation, from N5 L520-580 (VERIFIED by reading):
- `u ∉ 𝒞` is rational and `T = S ∪ supp M_S(u)` (N5 L528).
- `K` is normal with `[K:ℚ] ≤ F₀`, and `A/K` is the QM surface.
- `L = EK` is normal and unramified outside `T`, with `d = [L:ℚ] ≤ D`. It defines every
  geometric endomorphism of `A` and every homomorphism between conjugates of `A` (N5 L555-570).
- B1-C1 assume `End⁰(A_ℚ̄) = B`, the NoCM case (A10).
- `Q = Q_R = R^{R E₀}` and `M = M_S(u)`.

### B1. The sign cocycle (N5 L632-664)

**Lemma B1.** There are `B`-linear isogenies `μ_σ : ^σA → A`, defined over `L`, for
`σ ∈ Gal(L/ℚ)`, with `μ_1 = 1` (inflated to `G_ℚ`), such that the following hold.
- (i) `c(σ,τ) = μ_σ ∘ ^σμ_τ ∘ μ_{στ}^{−1} ∈ End⁰(A)` lies in `ℚ^×`.
- (ii) `c` is a normalized 2-cocycle for the trivial action.
- (iii) With `a_σ = (deg μ_σ)^{−1/4} > 0` and `ε = sign ∘ c`, one has
  `a_σ a_τ c(σ,τ) = ε(σ,τ) a_στ`, and `ε : Gal(L/ℚ)² → {±1}` is a normalized 2-cocycle.

*Proof skeleton and suppliers.*
1. A geometric isomorphism `ψ_σ : ^σA → A` exists. This is A7: the conjugates have the same
   geometric polarized moduli point.
2. The map `b ↦ ψ_σ ^σb ψ_σ^{−1}` is a `ℚ`-automorphism of `B`. It is inner by **L-B1**, and
   correcting by the inner element and clearing denominators gives `μ_σ`. It is defined over
   `L` because `L` defines every relevant Hom group.
3. `c` commutes with `B`, so `c ∈ Z(B) = ℚ` (`B6_commute_i_j`).
4. Degrees: `deg` is multiplicative, `deg ^σf = deg f`, and `deg [c] = c⁴` on a surface. So
   `deg μ_σ · deg μ_τ = c⁴ · deg μ_στ`, and then (iii) holds (`sign_normalization`).
5. The cocycle identities (`cocycle_of_projective`, `sign_cocycle`).

The `a_σ` are real algebraic numbers. The identity in (iii) holds in any field containing them,
so it survives every embedding `C → ℚ̄_ℓ` (rv-h-novel S1.2).

*Inputs.* L-B1 (package I6). Abelian-variety facts (package I3, foundational API):
- the degree of isogenies, and its multiplicativity;
- `deg [n] = n^{2g}`;
- Galois conjugation preserves degree;
- `End⁰(A_ℚ̄) = B` (A9/A10).

*Lean.*
- The algebra is proved in `ProjRep.lean` and `B1Quat.lean`.
- `B6 = ℍ[ℚ,2,−3]` is shown to satisfy `Algebra.IsCentral ℚ B6` and `IsSimpleRing B6`
  (`aniso_int`: descent mod 3 on `a² − 2b² + 3c² − 6d²`).
- `B6_inner`: from `LeafSkolemNoether`, every `ℚ`-automorphism of `B6` is inner.
- Still missing: the abelian surface itself, `ψ_σ`, `μ_σ` and the degree.

### B2. The Brauer step (N5 L665-700)

**Lemma B2** (`b2_of_leaves`, VERIFIED compiled). *Hypotheses:*
- `L ⊂ ℚ̄` is finite Galois over `ℚ`;
- `T` is a finite set of primes, and every prime of `𝓞 L` over `p ∉ T` has ramification index
  1;
- `ε : G_ℚ × G_ℚ → ℂ^×` is locally constant and sign-valued, satisfies the 2-cocycle identity,
  and depends only on the restrictions to `L`.

*Conclusion:* there are `N ≥ 1`, a Dirichlet character `χ` mod `N` and a locally constant
`β : G_ℚ → ℂ^×` such that:
- every prime factor of `N` lies in `T`;
- `ord χ ≤ 2 ∏_{p∈T, p≠2}(p−1)`;
- `β² = χ ∘ cyc_N`;
- `β(σ)β(τ) = ε(σ,τ)β(στ)`.

*Proof (formalized).*
1. `T₋ = {p : [ε]_p ≠ 0}`. It lies in `T` by L-B2d.
2. `χ = ∏_{p∈T₋} χ_p`, with `χ_p` odd of level `p` (or level `4` at `p = 2`)
   (`Chi.exists_chi`). Its order bound is proved, and `prod_odd_le` turns it into
   `≤ 2 R^R M`.
3. `β₀ = √(χ∘cyc)` is a pointwise square root. It is locally constant because the cyclotomic
   character is (`cyc_isLocallyConstant`, proved: invariance under the open subgroup fixing
   `ℚ(μ_N)`).
4. At each `p`: `δχ_p = 0` iff `χ|_{G_{ℚ_p}}` has a square-root character
   (`signCob_dB_iff`, proved). By L-B2c that holds iff `χ(u_p) = 1`, where `u_p` is the CRT
   unit, `≡ −1 mod p^{v_p N}` and `≡ 1` away from `p` (`exists_crt_unit`). And
   `χ(u_p) = −1` exactly for `p ∈ T₋` (`chi_toUnitHom_crt`). So `[ε]_p` and `δχ_p` are both
   zero or both nonzero.
5. L-B2b makes them equal at every `p`, and L-B2a makes `ε·(dβ₀)^{−1}` a coboundary `dγ`. Then
   `β = β₀γ` (`B2.exists_beta`).

N5's real place is absorbed into L-B2a, which is stated at the finite places only.

*Inputs.* L-B2a, L-B2b, L-B2c, L-B2d (package I6).

*Remarks.*
- *(VERIFIED by argument.)* `u_p² = 1`, so the sign convention of the reciprocity map
  (`rec(−1)` acting by `u_p` or `u_p^{−1}`) is irrelevant.
- *(VERIFIED by argument.)* N5 states that the global boundary `δχ` and `[ε]` agree at every
  finite place. In the formal proof this is the hypothesis `agree` of `exists_beta`.
- rv-h-novel R1 (`ω_p(−1) = χ_p(−1)`) is exactly `chi_toUnitHom_crt` combined with L-B2c.

### B3. The cochain `β` and `[L':ℚ] ≤ QM` (N5 L701-716)

**Lemma B3.** Take the data of B2, with `ε(1,1) = 1`, and any continuous quadratic character `η`
of `G_ℚ`. Put `β' = βη` and `L' = (ℚ̄)^{ker(β'|_{G_L})}`. Then:
- (i) `β'² = χ` and `dβ' = ε` (`twist`, `twist_sq`);
- (ii) `β'|_{G_L}` is a `G_ℚ`-invariant character (`restrictHom`, `cochain_conj`);
- (iii) `L'/ℚ` is finite Galois, `L ⊆ L'`, `G_{L'} = {σ ∈ G_L : β'(σ) = 1}`, and `β'` factors
  through `Gal(L'/ℚ)`;
- (iv) `[L':ℚ] ≤ 2·ord(χ)·[L:ℚ]`, and hence, for `T = S ∪ supp M_S(u)` with `(S,R)`
  admissible and `[L:ℚ] ≤ D`, `[L':ℚ] ≤ Q_R·M_S(u)`;
- (v) for N5's `η` (the quadratic character of the product `P` of the odd primes `p ∉ T` where
  `β|_{I_p} ≠ 1`), `L'` is unramified outside `T`.

*Lean.* (i)-(iv) are `b3_of_leaves` and `b3_degree_le_QM`, compiled and using only the leaves of
B2. The field-theoretic steps use Mathlib's infinite Galois theory:
- `IntermediateField.finrank_eq_fixingSubgroup_index` for `ℚ̄/ℚ`;
- `InfiniteGalois.fixingSubgroup_fixedField` for the closed subgroup `ker β'|_{G_L}`, which is
  open because `β'` is locally constant;
- `isOpen_iff_finite`;
- `normal_iff_isGalois`.

(v) is not formalized. Its group theory is proved over abstract groups:
- `twist_kills_inertia`: if `β|_{I_v}` is quadratic, the nontrivial quadratic character of
  `I_v` is unique, and `η` is ramified exactly where `β` is, then `βη = 1` on every `I_v`;
- `inertia_le_kernel`: then `I_v ≤ G_{L'}`.

*Inputs for (v).*
- L-B3a: at an odd prime, the inertia group has a unique nontrivial continuous quadratic
  character. Tame inertia is procyclic, `∏_{ℓ≠p} ℤ_ℓ(1)` (Serre, *Corps locaux* IV §2,
  UNVERIFIED locator).
- L-B3b: the quadratic Dirichlet character of odd squarefree conductor `P` is ramified exactly
  at `p | P` (classical; STANDARD).
- The finiteness of `P`: `β'` factors through a number field, which is ramified at finitely
  many primes (STANDARD).
- API: inertia subgroups `I_p ⊂ G_ℚ`. Mathlib has inertia only for finite Galois extensions of
  Dedekind domains.

### C1. `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` on `G_{L'}` (N5 L719-731)

**Lemma C1.** *Data:*
- `C` is a number field containing the `a_σ`, the values of `β` and a splitting field of `B`;
- `ℓ` is a prime, and `E/ℚ_ℓ` is finite and contains an image of `C`;
- `V = V_ℓ(A_ℚ̄) ⊗_{ℚ_ℓ} E`, and `T_σ = μ_σ ∘ σ_* ∈ GL(V)`, where
  `σ_* : V_ℓ(A) → V_ℓ(^σA)` is the transport of structure.

*Conclusion:*
- (i) `T_σ T_τ = c(σ,τ) T_στ`, and `T_σ` commutes with `B`;
- (ii) `ρ(σ) = β(σ)^{−1} a_σ T_σ` is a representation of `G_ℚ`;
- (iii) `ρ` commutes with `B ⊗ E ≅ M₂(E)`, so `V ≅ W ⊕ W` as `G_ℚ`-modules, with
  `W = e₁₁V` and `dim W = 2` (`dim V = 4`);
- (iv) on `G_{L'}`: `μ_σ = 1`, `a_σ = 1` and `β(σ) = 1`, so `ρ` is the Tate action of
  `A_{L'}`.

*Lean.* (ii)-(iv) are proved for any group, field and `E`-vector space:
- `rho_map_mul`, `rhoRep`, `rho_commute`, `commute_adjoin` (commuting with `B` implies
  commuting with the `E`-algebra it generates);
- `MatrixUnits2.splitEquiv`, `splitEquiv_intertwines`, `finrank_W`;
- `rho_eq_act`.

(i) is the instantiation.

*Inputs* (package I3; foundational API, not literature leaves):
- `V_ℓ(A)` is free of rank `2g = 4` (pkg-I3's `TateModuleFree`);
- the faithful Tate realization `End⁰(A) → End(V_ℓ A)` (pkg-I3's `tateHom`);
- the transport `σ_*` and its compatibility with `^σf`: `σ_* ∘ ^σb = b ∘ σ_*` after
  identification;
- `B ⊗ E ≅ M₂(E)` for `E ⊇` a splitting field (algebra; only the matrix units are used).

Continuity of `ρ_ℓ` is not addressed.

## 2. The leaves

| Leaf | Lean (`scratch/glue-descent/`) | Statement | Published source | In a library |
| --- | --- | --- | --- | --- |
| L-B1 | `B1Quat.lean`: `LeafSkolemNoether` | every `K`-automorphism of a finite-dimensional central simple `K`-algebra is inner | Reiner, *Maximal orders* (1975), Thm 7.21 (UNVERIFIED locator); special case automorphism | Tau Ceti `skolemNoether` (per prereq-survey); pkg-I6 `SkolemNoether` |
| L-B2a | `B2Glue.lean`: `B2Q.LeafHasse` | a continuous sign 2-cocycle of `G_ℚ` that is a coboundary on every `G_{ℚ_p}` (`p < ∞`) is a coboundary | consequence of `H²(G_K, μ₂) = Br(K)[2]` (Kummer, Hilbert 90), Albert–Brauer–Hasse–Noether with `∑ inv_v = 0`, `Br ℝ = ℤ/2` (Milne, ADT Ch. I; Tate in Cassels–Fröhlich Ch. VII; UNVERIFIED locators) | Tau Ceti has the Br forms (prereq-survey); pkg-I6 states `BrauerHasse2` + `BrauerReciprocity2` on Mathlib's `H²` |
| L-B2b | `B2Q.LeafLocalTwo` | `H²(G_{ℚ_p}, ±1)` has at most two classes | `Br(ℚ_p)[2] ≅ ℤ/2` (Serre, *Corps locaux* XIII; UNVERIFIED locator) | pkg-I6 `LocalH2Card` (= 2) |
| L-B2c | `B2Q.LeafSqrtCrit` | for `χ` mod `N = p^k N'` and `u ≡ −1 (p^k)`, `≡ 1 (N')`: `χ|_{G_{ℚ_p}}` has a continuous square-root character iff `χ(u) = 1` | consequence of local CFT for `ℚ_p` with explicit (Lubin–Tate/cyclotomic) reciprocity and `ℚ_p^× ≅ ℤ × μ × U¹` (N5 L683-689); unit part checked numerically by `c2_sqrt_criterion.py` (135 characters) | no; pkg-I6 proposes local Kronecker–Weber (`LocalKroneckerWeber`) plus 500-1000 lines of glue |
| L-B2d | `B2Q.LeafUnramified` | `ε` inflated from `Gal(L/ℚ)`, `L` unramified at `p` ⇒ `ε|_{G_{ℚ_p}}` is a coboundary | consequence of `Gal(ℚ_p^{ur}/ℚ_p) ≅ ℤ̂` and `cd ℤ̂ = 1` (Serre, *Galois cohomology* I §3, UNVERIFIED) | no (pkg-I6 lists it as glue to write) |
| L-B3a | not stated (needs `I_p ⊂ G_ℚ`) | unique nontrivial quadratic character of inertia at odd `p` | Serre, *Corps locaux* IV §2 (UNVERIFIED) | no |
| L-B3b | not stated | the quadratic Dirichlet character of odd squarefree conductor `P` ramifies exactly at `p ∣ P` | classical | no |

*Faithfulness checks* (VERIFIED by reading the Lean statements):
- Signs are `ℂ^×`-valued with square 1, and locally constant equals continuous into a discrete
  group, so `IsSignCocycle` and `SignCob` are continuous `ℤ/2`-cocycles and coboundaries.
- `resp p` depends on Mathlib's arbitrary embedding `ℚ̄ → ℚ̄_p`. Vanishing of a restricted
  class does not depend on the embedding, so L-B2a, L-B2c and L-B2d are true for the chosen one.
- L-B2c at `k = 0` gives `u = 1`: an unramified `χ` has a local square root. This is true.
- `UnramifiedAt` uses `Ideal.ramificationIdx ℤ = 1` at every prime of `𝓞 L` containing `p`.

*Packaging warning (SPECULATIVE recommendation).* L-B2c and L-B2d are consequences of published
theorems, and neither is stronger. Each still packages some glue:
- L-B2c: the structure of `ℚ_p^×` and the passage between characters of `G_{ℚ_p}` and of
  `ℚ_p^×`;
- L-B2d: decomposition groups and inflation.

The synthesis can accept them as leaves, or split them into pkg-I6's `LocalKroneckerWeber` and
local CFT plus glue.

L-B2a versus pkg-I6: L-B2a should follow from pkg-I6's `BrauerHasse2`, `BrauerReciprocity2`
and `LocalH2Card` at `∞` (a class trivial at every finite place has an even number of nonzero
local invariants, at most one, so none). This is SPECULATIVE: it was not checked in Lean against
pkg-I6's `H²`-based statements.

## 3. Glue proved in Lean (all compiled, no `sorry`, standard axioms; VERIFIED)

| File | Theorems | Step |
| --- | --- | --- |
| `ProjRep.lean` | `cocycle_of_projective`, `sign_normalization`, `sign_sq_eq_one`, `sign_cocycle`, `rho_map_mul`, `rhoRep`, `rho_commute`, `rho_eq_act`, `MatrixUnits2.splitEquiv`, `splitEquiv_intertwines`, `finrank_W`, `commute_adjoin` | B1, C1 |
| `B1Quat.lean` | `B6_commute_i_j`, `B6_isCentral`, `aniso_int`, `aniso_rat`, `B6_star_mul`, `B6_isSimpleRing`, `B6_inner` | B1 |
| `Cochain.lean` | `restrictHom`, `cochain_conj`, `kernelSubgroup_normal`, `cochain_mul_kernel`, `twist`, `twist_sq`, `cochain_of_boundary_eq`, `boundary_sq`, `relindex_kernel_le`, `index_kernel_le`, `twist_kills_inertia`, `inertia_le_kernel` | B2, B3 |
| `Constants.lean` | `prod_S_le`, `prod_odd_le`, `degree_le_QM` (repository definitions `heightD`, `heightE0`, `heightQ`, `contactSupport`) | B2, B3 |
| `Chi.lean` | `exists_odd_char`, `orderOf_dvd_totient`, `orderOf_prod_dvd`, `exists_chi` | B2 |
| `B2Glue.lean` | `B2.exists_beta` (abstract deduction), `signCob_dB_iff`; the leaves; `cyc_isLocallyConstant`, `galChar_isLocallyConstant` | B2 |
| `B2Assembly.lean` | `exists_crt_unit`, `chi_toUnitHom_crt`, `b2_of_leaves` | B2 |
| `B3Assembly.lean` | `inflatedNormalized_of`, `b3_of_leaves`, `b3_degree_le_QM` | B3 |

Build: `scratch/glue-descent/build.sh` compiles the eight files in order, one Lean process at a
time. Later files import earlier ones through oleans in `scratch/glue-descent/.lake/out`
(gitignored). A full rebuild takes about 45 s.

## 4. API needed for the rest (SPECULATIVE estimates)

- **Abelian surfaces with Tate modules (B1, C1).** pkg-I3 defines on Mathlib group schemes:
  `PkgI3.AbVar K`, `Hom`, `End⁰`, `T_ℓ`, `V_ℓ`, the `G_K`-representation `galRep`, `tateHom` and
  `baseChange`. Still missing:
  - the Galois conjugate `^σA` (base change along `σ : L → L`) and the semilinear transport
    `σ_* : V_ℓ(A) → V_ℓ(^σA)`;
  - degrees of isogenies, with multiplicativity, `deg[n] = n^{2g}` and conjugation invariance.

  With these, B1(i)-(iii) and C1(i) are short. All the algebra after them is already proved
  here. The real obstacle is upstream: Mathlib cannot yet construct a nonzero abelian variety,
  so the QM surface `A` must come from the I1 leaves (pkg-I3's report).
- **Inertia subgroups of `G_ℚ` (B3 (v)).** Use `I_p = r_p(I(ℚ̄_p/ℚ_p))`, where the inertia
  group is the kernel of the action on the residue field of `ℚ̄_p`. Alternatively, work at a
  finite level `Gal(L''/ℚ)` with Mathlib's inertia groups of Dedekind extensions. Either way,
  roughly 300-600 lines plus L-B3a and L-B3b.
- **Continuity of `ρ_ℓ`.** This needs the ℓ-adic topology on `GL(V)`. It is not used in B1-C1.

## 5. Findings

1. **(VERIFIED, Lean.)** N5's chain `[L':ℚ] ≤ 2md ≤ 4DR^RM ≤ QM` holds exactly as stated. It
   uses only `1 ≤ D ≤ R`, `10¹² ≤ R`, `E₀ ≥ 10`, and the facts that the primes of `S` are
   `≤ R` and that `M_S(u)` is the product of the primes of `T` outside `S`.
2. **(VERIFIED, Lean.)** The deduction of B2 from its cohomological inputs is correct (rv-h-novel
   S1.3-S1.6 reach the same conclusion by reading). N5's "Brauer reciprocity at the real place"
   is used only through L-B2a stated at the finite places.
3. **(VERIFIED, Lean.)** B3's twist changes neither `β² = χ`, nor `dβ = ε`, nor the degree bound.
   `b3_of_leaves` holds for every continuous quadratic `η`.
4. **(VERIFIED, Lean.)** B1's algebra `B = (2,−3)` is central simple over `ℚ`, its norm form
   `a² − 2b² + 3c² − 6d²` is anisotropic (descent mod 3), and its centralizer is `ℚ`. So N5's
   "`c` commutes with `B`, hence belongs to `ℚ^×`" is a Lean lemma.
5. **(VERIFIED by reading, rv-h-novel S1.8.)** N5's "possibly at 2" (L708) is vacuous, because
   `2 ∈ S ⊆ T`.
6. **Correction to wk-h §1** (agreeing with pkg-I6): the statements of B1-B3 are not all about
   Galois representations. B2 and B3 are statements about continuous cochains of `G_ℚ` and
   number fields, and they are stated and proved in Lean today. Only B1 and C1 need the
   abelian-variety layer.

## 6. Verdict per step

| Step | Glue provable over genuine definitions? | Status in Lean | Leaves |
| --- | --- | --- | --- |
| B1 | yes | algebra proved; instantiation needs AbVar + conjugates + degree | L-B1 (+ A7, A9/A10, I3 API) |
| B2 | yes | **proved over `G_ℚ` from the leaves** | L-B2a, b, c, d |
| B3 | yes | (i)-(iv) **proved over `G_ℚ`**, including `[L':ℚ] ≤ QM`; (v) group core proved, needs inertia API | the B2 leaves; L-B3a, L-B3b for (v) |
| C1 | yes | algebra proved; instantiation needs AbVar + transport `σ_*` | none beyond I3 API |
