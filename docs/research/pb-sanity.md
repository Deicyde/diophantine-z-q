# pb-sanity: are pb-bypass's `B_cris`, `B_st` and `LocalIsPst` genuine?

Task pb-sanity, 2026-11-15. Base 43513d87 (leaf-fold25) with origin/wip/pb-bypass c1636db9 merged
(73447464). Lean: `ZInQKernel/Contrib/OneProof/PanBergerSanity.lean` (the contribution, generated from
`scratch/pb-sanity/Sanity1.lean` by `scratch/pb-sanity/tools/mkcontrib.py`, which only expands two local
notations). Results log: `scratch/pb-sanity/log.md`. Model work, no human review.

Marks: **VERIFIED** (compiled here, or read in a named file), **STANDARD** (published, exact reference),
**UNVERIFIED** (a theorem number or locator from memory; this host has no network).

## 1. Verdict

**The two leaves `panPrinted` and `bergerPrinted` can be rated printed form.** Every degeneracy that would
make them vacuous or false and that can be decided in Lean today is ruled out by a Lean proof (§2), and both
statements are consequences of the prints, not stronger (§4). Proved: `B_cris^+`, `B_cris`, `B_st` are not
zero and `t` is not nilpotent; `G_{ℚ_p}` acts on `B_cris` and on `B_st` by ring automorphisms (including the
additivity of `log` on `{ε : ε^♯ = 1}`); the monodromy variable `u` is not fixed by any `G_K`, `K` finite;
`K_0 ⊆ B_st^{G_K}` in
dimension form; potentially trivial representations are pst; and a nontrivial character (the quadratic
character of a prime-to-`p` root of unity, e.g. the unramified one) is semistable over `ℚ_p` itself. What
remains unproved in Lean is not a choice in the definitions but one standard theorem about exactly these
objects, the half `B_st^{G_K} ⊆ K_0` of Fontaine's `B_st^{G_K} = K_0` (in particular finite-dimensionality),
and with it any example of a representation that is not pst. I recommend changing the flag of both rows
from "no statement check yet" to "definitions checked by pb-sanity (non-degenerate; only `B_st^{G_K} ⊆ K_0`
not in Lean)", and keeping "unread" for the JAMS/Springer locators (`scratch/pb-sanity/autofold.json`).

One caveat for readers of the statement, not a defect: `IsSemistableOver` compares `finrank_{ℚ_p} D_st,K`
with `finrank_{ℚ_p} B_st^{G_K} · dim V`. Lean's `finrank` is 0 on infinite-dimensional spaces, so the
predicate means Fontaine's only because `B_st^{G_K}` is finite-dimensional (Fontaine's theorem). If it were
infinite-dimensional, `IsSemistableOver` would reduce to `finrank D_st,K = 0`, which every non-pst
representation satisfies. This is why `B_st^{G_K} ⊆ K_0` is the one definitional fact the leaves rest on.

## 2. What is proved (VERIFIED: `lake build +ZInQKernel.Contrib.OneProof.PanBergerSanity` succeeds, no
warning in the file; `#print axioms` gives `propext`, `Classical.choice`, `Quot.sound` for every listed
theorem, `scratch/pb-sanity/axioms-output.txt`)

All in namespace `HDec.PkgI4.PanBergerSplit`, over pb-bypass's definitions unchanged, using
`ZInQKernel/Contrib/G9/KerTheta.lean` (`ker θ = (ξ)`, `ξ = p − [p♭]`, `𝓞_ℂ_p♭` a domain) and pkg-I4's layer.

| property | Lean | how |
| --- | --- | --- |
| `p^m · ∏ log [ε_i] · y ≠ 0` in `A_cris` for `ε_i^♯ = 1`, `ε_i ≠ 1`, `0 ≠ y ∈ A_inf` | `pow_mul_prod_logOf_mul_ne_zero`, `pow_mul_prod_logOf_ne_zero` | below |
| no product of `log [ε]` is zero in `B_cris^+`; `0 ∉ tMonoid` | `zero_notMem_tMonoid` | from the above |
| **`B_cris^+ ≠ 0`, `B_cris ≠ 0`, `B_st ≠ 0`** | instances `nontrivial_bcrisPlus`, `nontrivial_bcris`, `nontrivial_bst` | |
| **`t` is not nilpotent**: `log [ε]` is not nilpotent in `B_cris^+`, is `≠ 0` in `A_cris`, is a unit `≠ 0` in `B_cris` | `logOf_not_isNilpotent`, `logOf_ne_zero`, `isUnit_logOf_bcris`, `logOf_bcris_ne_zero` | |
| some `ε` has `ε^♯ = 1`, `ε ≠ 1` (`ε = (1, ζ_p, ζ_{p²}, …)`), so `t` exists | `nonempty_tEps`, `exists_t` | `untilt_eq_of_coeff`, `root_eq_of_coeff` |
| `ℚ_p → B_st` injective | `algebraMap_qp_bst_injective` | |
| `A_inf → B_st` injective and `G_{ℚ_p}`-equivariant | `embW_injective`, `stAct_embW` | main lemma with `y` |
| **`G_{ℚ_p}` acts on `B_cris` by ring automorphisms** (a group homomorphism) | `bcrisAut : GQp p →* (Bcris p ≃+* Bcris p)`, `bcrisAct_mul`, `bcrisAct_one` | functoriality of `oAct`, `σ♭`, `W(·)`, `A_inf[1/p]`, adic completion, localizations |
| **each `σ` acts on `B_st` by a ring automorphism**; `1` acts trivially | `stEquiv`, `stAct_bijective`, `stAct_one` | explicit inverse; `u_1 = 1`, `log [1] = 0` |
| `u_σ` exists, `u_σ^♯ = 1` (so the `else 0` branch of `logU` never occurs), `u_{στ} = σ♭(u_τ)·u_σ` | `uSigma_spec`, `untilt_uSigma`, `logU_eq`, `uSigma_mul` | KerTheta `dvd_of_coeff_zero` |
| the group law on `B_st` ⇔ the cocycle identity for `σ ↦ log [u_σ]` | `stAct_mul_iff`, `stAct_mul (hL : LogAdditive p)` | |
| **`log [xy] = log [x] + log [y]` in `A_cris`** (`x^♯ = y^♯ = 1`) | `logAdditive : LogAdditive p` | below (second argument) |
| **`G_{ℚ_p}` acts on `B_st` by ring automorphisms** | `stAut : GQp p →* (Bst p ≃+* Bst p)` | `stAct_mul`, `logAdditive` |
| **`u` is not invariant under any open subgroup**: for every finite `K` some `σ ∈ G_K` moves `p♭`, so `σ(u) = u + log [u_σ] ≠ u` and `u ∉ B_st^{G_K}` (with a trivial action on `u`, `B_st^{G_K}` would contain `B_cris^{G_K}[u]`, infinite-dimensional, and `IsSemistableOver` would degenerate) | `exists_mem_fixingSubgroup_uSigma_ne_one`, `X_not_mem_bstInv`, (`K = ℚ_p`: `exists_stAct_X_ne`, `X_not_mem_bstInv_bot`) | a `p^n`-th root of `p` has degree divisible by `p^n` (`pow_dvd_natDegree_minpoly`, spectral norm and valuations), so it is not in `K` for `p^n > [K:ℚ_p]`; infinite Galois theory (`InfiniteGalois.fixedField_fixingSubgroup`); `root_preTiltMap` |
| **`K_0 ⊆ B_st^{G_K}`** (dimension form): for a root of unity `μ ∈ K` of order prime to `p`, `[μ♭]^i ∈ B_st^{G_K}` and `1, [μ♭], …, [μ♭]^{d−1}` (`d = [ℚ_p(μ):ℚ_p]`) are `ℚ_p`-independent; so a finite-dimensional `B_st^{G_K}` has dimension `≥ [ℚ_p(μ):ℚ_p]` | `teichB_pow_mem_bstInv`, `linearIndependent_teichB`, `natDegree_minpoly_le_finrank_bstInv` | `muFlat`, `coe_theta_zpToW`, `embW_injective`, `linearIndependent_pow` |
| a representation trivial on `G_K` is semistable over `K` (any `K`; no finiteness of `B_st^{G_K}` needed) | `isSemistableOver_of_trivial`, `isPst_of_trivial_on` | `D_st,K ≅ Hom(V, B_st^{G_K})` |
| trivial `n`-dimensional `ℚ̄_p`-representation satisfies `LocalIsPst` | `localIsPst_one` | |
| quadratic characters `σ ↦ σ(α)/α` (`α² ∈ ℚ_p`, e.g. the unramified one) are pst | `quadChar`, `isPst_quadChar` | trivial on `G_{ℚ_p(α)}` |
| a 1-dimensional representation with a unit period `b ∈ B_st` (`σ b = χ(σ) b` on `G_K`) is semistable over `K` | `isSemistableOver_of_period` | `D_st,K ≅ B_st^{G_K}`, `φ ↦ φ(1) b⁻¹` |
| **the quadratic character of a root of unity `β` of order prime to `p` with `β² ∈ ℚ_p` is semistable over `ℚ_p`**, and nontrivial if `β ∉ ℚ_p` (for `p` odd, `β` of order `2(p − 1)`: the unramified quadratic character, STANDARD) | `isSemistableOver_quadChar_teich`, `quadChar_ne_one` | period `[β♭]`; Teichmüller uniqueness `eq_of_pow_eq_one_of_untilt`; `A_inf` a domain |
| summary | `panBerger_definitions_nondegenerate` | |

**The main argument (all in `A_inf`, no `B_dR`).** Write `[ε_i] − 1 = ξ^{s_i} w_i` with `θ(w_i) ≠ 0`
(`eq_xi_pow_mul`: `A_inf` is `ξ`-adically separated on non-zero elements, proved from
`WittVector.exists_eq_pow_p_mul`, `p`-regularity modulo `ξ^n`, and "an element of `𝓞_ℂ_p♭` divisible by
every power of `p♭` is 0"); likewise `y = ξ^{s_0} w_0`. Put `S = Σ s_i`, `N = S + 1`. If the product were 0
in `A_cris = lim A_cris^0 / p^n`, then for every `n` the `p^n`-th partial log sums would satisfy
`p^m y ∏ L_i = p^n z` with `z ∈ A_cris^0`. The lattice bound `N! · A_cris^0 ⊆ A_inf + ξ^N A_inf[1/p]`
(`latG_bound`, `acris0_le_latSub`: the `A_inf`-span of the classes of `ξ^i/i!` in `A_inf[1/p]/ξ^N` is a
subring containing the generators) gives `N! z = a + ξ^N w`; then `a ∈ ξ^S A_inf`, and after cancelling `ξ^S`
and applying `θ[1/p]` (each `L_i / ([ε_i] − 1)` has `θ = 1`), `c := N! p^m θ(w_0) ∏ θ(w_i) ∈ p^n 𝓞_ℂ_p` for
all `n`; so `c = 0`, a contradiction since `𝓞_ℂ_p` is a domain of characteristic 0.

## 3. What is not proved, and why

* **`B_st^{G_K} ⊆ K_0`** (hence finite-dimensional). Fontaine's proof (Astérisque 223, Exp. II–III;
  Brinon–Conrad, CMI notes, §§9.1–9.2; numbers UNVERIFIED) embeds `B_st` into `B_dR` (injectivity of
  `A_cris → B_dR^+` and transcendence of `log [p♭]` over `B_cris`) and uses `B_dR^{G_K} = K`, which rests on
  Ax–Sen–Tate (`ℂ_p^{G_K} = K`) and Tate's `ℂ_p(i)^{G_K} = 0` for `i ≠ 0`. None of these is in Mathlib or in
  the tree (pkg-I4's own sanity check of `IsDeRham` takes `B_dR^{G_{ℚ_p}} = ℚ_p` as a hypothesis).
* **A representation failing `LocalIsPst`: out of reach.** To show `¬ IsSemistableOver K ρ` one must know
  `finrank B_st^{G_K} ≠ 0` (needs finite-dimensionality, first bullet) and bound `D_st,K(ρ)` from above, e.g.
  `D_st,K = 0` for a character of non-integral Sen weight or for `ℚ_p(χ)` with `χ` non-de Rham. Both need the
  embedding `B_st ⊆ B_dR` and Sen theory / Tate's theorem. So "LocalIsPst is not always true" is not proved.
  The results of §2 exclude the two concrete ways the definitions could have made every representation pst:
  a zero `B_cris` (pb-bypass's worry), and a monodromy variable fixed by some `G_K` (which would make
  `B_st^{G_K}` infinite-dimensional and `IsSemistableOver` trivially true for representations with
  `D_st,K = 0`).
* **Unramified characters of infinite order** (Frobenius ↦ a unit of `ℤ_p` that is not a root of unity):
  their periods are solutions of `φ(b) = u b` in `W(k̄)`, which needs Lang's theorem / Hilbert 90 over
  `W(k̄)`. The finite-order ones are covered: all are pst (`isPst_of_trivial_on`), and the quadratic ones
  attached to prime-to-`p` roots of unity are semistable over `ℚ_p` (`isSemistableOver_quadChar_teich`);
  such a character is nontrivial as soon as `β ∉ ℚ_p` (`quadChar_ne_one`); the existence of
  `β = ζ_{2(p−1)}` with `β² ∈ ℚ_p`, `β ∉ ℚ_p` for odd `p` is standard and not formalized.

## 4. Statement check of the two leaves against the prints

Sources: `docs/research/locators.md` rows R11 and R12, `docs/research/h-a011.md` §1.1 and §3.4 (both read
here; quoted at most a line).

**`BergerPrinted := BergerDR LocalIsPst`**: for every `p`, `n` and continuous `ρ : G_{ℚ_p} → GL_n(ℚ̄_p)`,
`LocalIsDeRham ρ → LocalIsPst ρ`. The print (Berger, Invent. Math. 148 (2002), Thm 0.7 of the published
version = arXiv v3 Thm 0.6 = Thm 5.19; locators R11: no dimension, oddness, residual or odd-`p` hypothesis):
every de Rham `p`-adic representation of `G_K` is potentially semistable. Translation: `LocalIsDeRham` gives a
finite `E ⊆ ℚ̄_p` and `ρ_E` with `IsDeRham ρ_E`, i.e. `V' := (E^n)^∨` (the space `Hom_G(E^n, B)` computes) is
de Rham; `ρ_E` is continuous (the topology of the finite-dimensional `E` is the subspace topology of `ℚ̄_p`),
so Berger applies to `V'` (restriction of scalars to `ℚ_p`, as R11 asks); "pst" gives a finite `K` with
`dim_{K_0} D_st,K(V') = dim V'`, which is `IsSemistableOver K ρ_E` once `B_st^{G_K} = K_0`. Same `E`, so
`LocalIsPst ρ`. **Not stronger than the print** (given Fontaine's `B_st^{G_K} = K_0` for these objects).

**`PanPrinted := PanFor LocalIsPst`**: for `p ≥ 5` and `ρ : GaloisRep p 2` (continuous `G_ℚ → GL₂(ℚ̄_p)`),
absolutely irreducible (Burnside form), finitely ramified, `LocalIsPst` at `p`, odd (`det ρ(c) = −1` for
every complex conjugation), with distinct Hodge–Tate weights ⇒ modular up to twist in trace form. The print
(Pan, JAMS 35 (2022), Thm 1.0.4 = arXiv:1901.07166v2 Thm 1.0.4, statement read in h-a011 §1.1; JAMS
numbering UNVERIFIED): `p` odd, the same five hypotheses (irreducible, finitely ramified, pst at `p`, odd,
distinct HT weights), with an extra residual proviso only at `p = 3`. The template restricts to `p ≥ 5`
(weaker). `LocalIsPst ρ` says `V^∨` is pst, so the leaf is Pan's theorem applied to `ρ^∨`, which is
irreducible, finitely ramified and odd (`det ρ^∨(c) = det ρ(c)^{−1} = −1`) with the negated, still distinct,
HT weights; Pan gives `ρ^∨ ≅ ρ_g ⊗ χ`, so `ρ ≅ ρ^∨ ⊗ det ρ ≅ ρ_g ⊗ χ det ρ`, and the trace-form conclusion
of `PanFor` follows as in pkg-I4 note §2.1 / h-a011 §4 (that part of the template is unchanged by pb-bypass
and was checked there; not re-checked here). **Not stronger than the print**, with the same proviso on
`B_st^{G_K} = K_0`.

**Ratings.** `panPrinted`: printed form (consequence of Pan Thm 1.0.4 applied to `ρ^∨`, `p ≥ 5`). `bergerPrinted`:
printed form (Berger Thm 0.7 applied to `V^∨`). Both over definitions that are Fontaine's (§2 shows they are
not degenerate; §3 names the one standard fact about them, `B_st^{G_K} ⊆ K_0`, that Lean does not yet
have).

## 5. Deliverables

* `ZInQKernel/Contrib/OneProof/PanBergerSanity.lean` (imports `ZInQKernel.Contrib.OneProof.PanBerger` and
  `ZInQKernel.Contrib.G9.KerTheta`; no `notation`, `#` command or other build-time code).
* `#discharges` (VERIFIED, `scratch/pb-sanity/discharges-output.txt`, after building `Main`, `Discharges`,
  `PanBerger` and `PanBergerSanity`): the sanity file discharges no new field (it proves no open hypothesis);
  `r11r12` is still discharged by pb-bypass's `panBerger_of_printed`, assuming `PanPrinted` and
  `BergerPrinted`; total `63 open hypotheses, 2166 theorems checked, 8 discharge one`.
* `scratch/pb-sanity/autofold.json`: pb-bypass's spec for `r11r12` with the two leaves' flags updated to
  record this check (same imports: the fold does not need the sanity file, and importing `KerTheta` into the
  fold chain is avoided).

## 6. Reproduce

```
lake build +ZInQKernel.Contrib.OneProof.PanBergerSanity
lake env lean scratch/pb-sanity/Axioms.lean
lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
lake env lean scratch/pb-sanity/Discharges.lean
```
