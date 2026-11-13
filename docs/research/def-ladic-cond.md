# def-ladic-cond: the conductor exponent of an ℓ-adic representation of `G_{ℚ_p}`, `ℓ ≠ p`

Status: research note (task def-ladic-cond, 2026-11-11). Lean: `scratch/def-ladic-cond/LadicCond.lean`
(imports Mathlib only; check with `lake env lean scratch/def-ladic-cond/LadicCond.lean`). Results
log: `scratch/def-ladic-cond/log.md`. Nothing under `ZInQKernel/`, `blueprint/` or other tasks'
files was edited.

Marks: VERIFIED = compiled or read in a source in the repository; STANDARD = published, with
reference; SPECULATIVE = assessment. No network: theorem numbers from memory are UNVERIFIED.

## Main result

**The definition that blocked R17 (Carayol, Théorème (A)) and glue-conductor's L8 now exists in
Lean over genuine objects, and both leaves are stated over it (VERIFIED: `LadicCond.lean` compiles,
no `sorry`; every proved theorem uses only `propext`, `Classical.choice`, `Quot.sound`).**

- **Definition.** For `ρ : G_{ℚ_p} →* GL_n(k)` (`G_{ℚ_p} = PkgI4.GQp p = Gal(ℚ̄_p/ℚ_p)`, Mathlib's
  `PadicAlgCl p` with its spectral norm), the conductor exponent is Serre–Tate's
  `a(ρ) = codim V^{I_p} + Sw(ρ)`, with
  `Sw(ρ) = Sw_L(ρ) = ∑_{i≥1} (g_i/g_0) · codim V^{G_i(L) ∩ P_p}` at a finite Galois `L/ℚ_p` that is
  **adapted** to `ρ`, meaning `ρ` is trivial on `P_p ∩ G_L`, so that wild inertia acts through
  `Gal(L/ℚ_p)`. Serre–Tate 1968 §2 is the source (STANDARD; section number UNVERIFIED). The
  definition uses the finite image of wild inertia, through a finite level, not lattices. The task
  offered lattices mod ℓ as one option; a level `L` does the same job and avoids lattices and
  reduction mod `λ`. Grothendieck's monodromy theorem is not needed for the definition.
- **Sanity facts, proved:**
  - unramified ⇒ `a = 0`: `condExp_eq_zero_of_unramified`, `condAt_eq_zero_of_unramified`;
  - agreement with Serre's finite-level Artin conductor `∑_{i≥0}(g_i/g_0) codim V^{G_i}` (the formula
    of pkg-I6's `artinConductor`) when `ρ` factors through `Gal(L/ℚ_p)`: `condAt_eq_artinAt_of_surj`. It
    holds for every finite Galois `L`, and assumes only the two standard surjectivity
    facts (restriction of `I_p` onto `G_0(L)`, and of `P_p ∩ G_i` onto `G_i(L)`);
  - independence of the level reduces to one Prop, `SwanIndependent`: `condExp_eq_condAt`.
- **Leaves stated:**
  - `CarayolR17` (at every adapted level) and `CarayolR17'` (canonical `condExp`). Both are proved
    equivalent given the glue Props `SwanIndependent` and `AdaptedExists` (`carayolR17_of_R17'`,
    `carayolR17'_of_R17`);
  - `SwanIntegral` = L8, `Sw_L(ρ) = ∫₀^∞ codim V^{G^u} du`, over the absolute upper filtration
    `upperAbs`, which is defined from Herbrand's `φ` at every finite level.
- **Consumer, proved:** glue-conductor's D4(i) bound follows from L8: `condAt_le_of_upper`.
  If `ρ` is trivial on `G^u` for `u > U ≥ 0`, then `a(ρ) ≤ n(1+U)`. The integral estimate
  `integral_codim_le` is proved over Mathlib's Bochner integral.

## 1. Definitions (Part B of `LadicCond.lean`)

| Lean | Mathematics | Source |
| --- | --- | --- |
| `inertiaSet` | `I_p = {σ : ‖σx−x‖ < 1 for ‖x‖ ≤ 1}` | Serre, *Corps locaux* I §7 (UNVERIFIED §) |
| `wildSet` | `P_p = {σ : ‖σx−x‖ < ‖x‖ for x ≠ 0}`, i.e. `σx/x ≡ 1 mod 𝔪` | Serre CL IV §2 (UNVERIFIED §) |
| `fixSet L` | `G_L` | — |
| `IsUnif L ϖ` | `ϖ ∈ L` of maximal norm `< 1` (a uniformizer) | — |
| `ramSet L i` | preimage in `G_{ℚ_p}` of `G_i(L/ℚ_p)`, `v_L(σx−x) ≥ i+1` on `𝓞_L` | Serre CL IV §1 |
| `ramCard L i` | `g_i = |G_i(L/ℚ_p)|` (`Nat.card` of the restrictions to `L`) | — |
| `invariants ρ S`, `codimInv ρ S` | `V^S ⊆ kⁿ`, `n − dim V^S` | — |
| `IsAdapted L ρ` | `L/ℚ_p` finite Galois, `ρ = 1` on `P_p ∩ G_L` | — |
| `swanAt L ρ`, `swan ρ` | `Sw_L`, and `Sw` at a chosen adapted `L` | Serre–Tate 1968 §2 |
| `condAt L ρ`, `condExp ρ` | `codim V^{I} + Sw` | Serre–Tate 1968 §2 |
| `artinAt L ρ` | `∑_{i≥0} (g_i/g_0) codim V^{G_i}` | Serre CL VI §2 (= `PkgI6.artinConductor`) |
| `ramSetR`, `phiAt`, `upperSet`, `upperAbs` | `G_t = G_{⌈t⌉}`, Herbrand's `φ`, `G^v(L) = G_{ψ(v)}`, `G^v` on `G_{ℚ_p}` | Serre CL IV §3 |

The definitions copy pkg-I6's ring-level definitions (`lowerRam`, `herbrandPhi`, `upperRam`,
`artinConductor`), transcribed to subsets of `G_{ℚ_p}` through the norm of `ℚ̄_p`. Working on
subsets avoids a Lean bridge between `Gal(L/ℚ_p)` and `𝓞_L ≃ₐ[ℤ_p] 𝓞_L`. Invariants under a
subset are the invariants under the subgroup it generates.

**Agreement with Weil–Deligne / Carayol's normalization (STANDARD).** For an ℓ-adic `ρ`, take
Grothendieck's form `ρ(σ) = ρ'(σ) exp(t_ℓ(σ)N)` on `I_p`, with `ρ'|_{I_p}` of finite image. Then
`V^{ρ(I_p)} = (ker N)^{ρ'(I_p)}`: on the open subgroup where `ρ'` is trivial and `t_ℓ ≠ 0`, an
invariant `v` has `exp(tN)v = v`, so `Nv = 0`. Hence `condExp` is the conductor of the
Weil–Deligne representation, `codim (ker N)^{I} + Sw`. The Swan parts agree because `ρ` and `ρ'`
agree on `P_p` (`t_ℓ` vanishes on `P_p`). This comparison is not formalized; it needs WD
representations.

## 2. Sanity facts (Part C)

- **(a) Unramified ⇒ 0.** `condExp_eq_zero_of_unramified`: if `ρ = 1` on `I_p` then `condExp ρ = 0`,
  for whichever level the choice picks. Uses `wildSet_subset_inertiaSet` (proved). VERIFIED.
- **(b) Finite image.** `condAt_eq_artinAt`: if `ρ = 1` on `G_L`, then
  `codim V^I + Sw_L = ∑_{i≥0}(g_i/g_0) codim V^{G_i}`. The proof uses `invariants_eq_of_cover`
  (`V^S = V^T` when `T ⊆ S·G_L` and `ρ(G_L) = 1`), the split of the `i = 0` term and `g_0/g_0 = 1`.
  The reduced form `condAt_eq_artinAt'` (for `L` finite Galois with a uniformizer) assumes only:
  - restriction of `I_p` onto `G_0(L)`;
  - restriction of `P_p ∩ ramSet L i` onto `G_i(L)` for `i ≥ 1`;
  - `G_i(L) = 1` for `i ≥ N`. This one is now proved too, see below.

  STANDARD: Serre CL I §7 Prop. 21, IV §1–2 (UNVERIFIED); not proved here. The other hypotheses
  are proved:
  - `I_p ⊆ ramSet L 0`: `inertiaSet_subset_ramSet_zero`, via `apply_mem`, conjugates stay in a
    normal `L`;
  - `g_i ≠ 0`: `ramCard_ne_zero`, via `finite_restr`: the restrictions inject into
    `L →ₐ[ℚ_p] ℚ̄_p`, which is finite;
  - `G_i(L) = 1` for large `i`: `eventuallyTrivial`. If `σ` moves `y ∈ L`, then `x = p^k y ∈ 𝓞_L`
    has `‖σx − x‖ > 0`, which exceeds `‖ϖ‖^{i+1}` for large `i`. Induction over the finitely
    many restrictions then gives one bound for all of them.

  - existence of a uniformizer of every finite `L ⊆ ℚ̄_p`: `exists_isUnif`. By
    `norm_pow_factorial`, `‖y‖^{[L:ℚ_p]!} ∈ p^ℤ`; this uses Mathlib's
    `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow`, which gives `‖y‖ = ‖a_0‖^{1/deg}` for the
    minimal polynomial. `Nat.find` then picks the largest value below 1.

  The final form is `condAt_eq_artinAt_of_surj`, for every finite Galois `L`. Its only hypotheses
  are the two surjectivity facts.

  The agreement is with `artinAt`, which is pkg-I6's `artinConductor` formula on `G_{ℚ_p}`. A Lean
  identification with `PkgI6.artinConductor` on `𝓞_L ≃ₐ[ℤ_p] 𝓞_L` is not done.
- **(c) Independence.** There is no choice of lattice. The choice of level is reduced to
  `SwanIndependent` (Serre–Tate §2, from Herbrand's theorem, pkg-I6 leaves I6.8/I6.9; GLUE, not
  proved). `condExp_eq_condAt` proves `condExp = condAt L` for every adapted `L` given it. VERIFIED.
- **Non-degeneracy checks:** `fixSet_subset_ramSet`, `isAdapted_one`, `condExp_one`,
  `one_mem_wildSet`, `isUnif_bot`. The last one shows that `p` is a uniformizer of `L = ℚ_p`, so
  the existential in `ramSet` is satisfiable. It uses Mathlib's `PadicAlgCl.norm_extends` and
  `Padic.norm_le_pow_iff_norm_lt_pow_add_one`. VERIFIED.

## 3. The leaves (Part D)

**R17 (glue-conductor L10; h-decomposition R17).** `CarayolR17`: let `f` be a weight-2 newform of
level `N`, `ρ : G_ℚ → GL₂(ℚ̄_ℓ)` semisimple and attached to `f` (pkg-I4's `AttachedTo`), and
`p ≠ ℓ`. Then for every `L` adapted to `ρ|_{G_{ℚ_p}}`, `condAt L (ρ|_{G_{ℚ_p}}) = v_p(N)`.
`CarayolR17'` is the same statement with `condExp`.
- Source: Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A). The letter is VERIFIED from N5's locator
  according to pkg-I4; the content and the coverage of `p | N` for `F = ℚ` are UNVERIFIED.
- Faithfulness: Carayol's statement is local–global compatibility with `π_p`. The form
  "`a(ρ|_{G_{ℚ_p}}) = v_p(N)`" also needs:
  - `a(π_p) = v_p(N)` (Casselman 1973, newform theory; STANDARD);
  - `a(WD) = a(π_p)` under local Langlands for `GL₂`;
  - the WD/Serre–Tate comparison of §1.

  This is the form that pkg-I4's template `CarayolFor` and the literature use (SPECULATIVE that
  Carayol prints it in exactly this form).
- `ρ` with `ℚ̄_ℓ` coefficients agrees with Carayol's `ρ_{f,λ}` up to isomorphism after extending
  scalars: Chebotarev and Brauer–Nesbitt, as in pkg-I4. The conductor is invariant under both.
- R17 replaces pkg-I4's template `CarayolFor a`. It is a genuine statement: `a` is now defined.

**L8 (glue-conductor).** `SwanIntegral`: for continuous `ρ : G_{ℚ_p} → GL_n(ℚ̄_ℓ)`, `ℓ ≠ p`, and
adapted `L`, `Sw_L(ρ) = ∫_{u>0} codim V^{G^u} du`, with `G^u = upperAbs p u`.
- Source: Serre CL VI §2 (finite image) and Serre–Tate 1968 §2; UNVERIFIED numbering.
- With `condAt = codim V^I + Sw_L`, this is glue-conductor's L8, `a = codim V^I + ∫₀^∞ codim V^{G^u}`.
- SPECULATIVE assessment: L8 is glue rather than a research leaf. It follows from a change of
  variables in `φ` (`φ' = g_t/g_0`) and Herbrand's theorem (I6.8), which gives that `G^u` restricts
  onto `G^u(L)`. So it can leave the leaf list once `SwanIndependent` and the change of variables
  are proved.

**Consumer (glue-conductor D4(i)).** `condAt_le_of_upper` (from `SwanIntegral`): if `ρ` is trivial
on `G^u` for `u > U ≥ 0`, then `a ≤ n(1+U)`. With `n = 2` and `U = U₀` this is the bound
`a ≤ 2 + 2U₀` of D4(i). VERIFIED (compiled).

## 4. What remains (glue, not proved)

1. `SwanIndependent`: Herbrand plus transitivity of `φ`; medium.
2. `AdaptedExists`: `ρ(P_p)` is finite for `ℓ ≠ p` (pro-`p` against pro-`ℓ`), and `ρ` takes values
   in a finite `E/ℚ_ℓ` (Baire); medium.
3. The two surjectivity clauses of `InertiaRestriction L`: `I_p` restricts onto `G_0(L)`, and
   `P_p ∩ G_i` onto `G_i(L)`. They need unramified extensions (`G_L → Gal(\bar 𝔽_p/k_L)` is onto)
   and tame theory. Medium. Already proved: `I_p ⊆ ramSet L 0`, `g_i ≠ 0`, `G_i(L) = 1` for
   large `i`, and existence of uniformizers. The surjectivity facts may need `𝓞_L` as a complete
   DVR; Mathlib has `IsDiscreteValuationRing` and `Valued`, but no packaged `𝓞_L` for `L ⊆ ℚ̄_p`.
4. L8 itself (`SwanIntegral`), if it is to become glue.
5. The bridge from `artinAt` to `PkgI6.artinConductor`:
   `Gal(L/ℚ_p) ≅ (𝓞_L ≃ₐ[ℤ_p] 𝓞_L)` and the transport of `lowerRam`.
6. Out of scope: Weil–Deligne representations and Grothendieck's monodromy theorem. They are
   needed only to compare with the WD normalization, not to state R17.
