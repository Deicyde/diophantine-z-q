# hodge-split: the p-adic Hodge theory rows of the frontier, split into published forms

Task hodge-split, 2026-11-14. Base: cba8157f (frontier r3). Lean: `scratch/hodge-split/HodgeSplit.lean`
(main file) and `scratch/hodge-split/Companion.lean` (the parts that need the kernel's Chebotarev and
Brauer–Nesbitt modules; separate because importing `ZInQKernel.HDecomp` makes the opened `PkgI4` names
of the main file ambiguous). Results log: `scratch/hodge-split/log.md`. Model work, no human review.

Marks: **VERIFIED** (compiled here, or read in a named file), **UNVERIFIED** (a theorem number or locator
from memory or from earlier reports; this host has no network and no copy of the papers).

## 1. Main result

Of the seven rows, **three are now theorems from published-form leaves only** (H-52, H-32, H-8), **one is
a theorem from two published-form leaves plus one named glue Prop** (H-22), **one is a theorem from the
two Tate leaves plus two named glue Props** (H-51), **one is reduced to its newform case** (H-10; the
newform case is Kato's theorem, whose object is not definable in Mathlib), and **one cannot be split
today** (H-9: Pan's and Berger's theorems are about potentially semistable representations, and
Mathlib has no `B_cris`/`B_st`). Every Lean statement below compiles with the axioms `propext`,
`Classical.choice`, `Quot.sound` only (VERIFIED, 11-14). No row statement was changed; none was found
false.

New published-form leaves (all over genuine definitions: Mathlib's `ℂ_[p]`, `BDeRham`, `cyclotomicCharacter`,
pkg-I3/I4's abelian varieties, Tate modules and Hodge–Tate/de Rham spaces):

| leaf | statement (Lean form) | source (locators UNVERIFIED) |
|---|---|---|
| `TateTwistInvariants` | `ℂ_p(i)^{G_K} = 0` for `i ≠ 0`, `K ⊆ ℚ̄_p` finite over `ℚ_p` | Tate, *p-divisible groups* (1967), §3.3, Thm 2 |
| `AxSenTate` | `ℂ_p^{G_K} ⊆ K`, same `K` | Tate 1967 §3.3 Thm 1; Sen 1969; Ax 1970 |
| `HodgeTateDecompAbVar` | `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^g ⊕ ℂ_p^g`, `G_F`-equivariant, `g = dim A`, `F/ℚ_p` finite | Fontaine, Invent. Math. 65 (1982); Tate 1967 §4 (good reduction); Faltings, JAMS 1 (1988) |
| `DeRhamH1AbVar` | `V_p(A)^∨` is de Rham over `F` (pkg-I4's `IsDeRhamOver`) | Faltings 1989; Tsuji 1999; Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 (wording VERIFIED by h-leaves) |
| `FontaineDRTannakian p` | de Rham reps (printed definition `dim (B_dR ⊗ V)^G = dim V`) stable under duals, sub/quotients, `⊕`, `⊗` (matrix form) | Fontaine, Astérisque 223 (1994), Exp. II–III (§1.5 of Exp. III); Brinon–Conrad, CMI notes, Thm 5.2.1, §6.3 |
| `DSThm965` | `k ≥ 2`: `ρ` unramified outside `ℓN`, charpoly of arithmetic Frobenius `X² − a_p X + χ(p)p^{k−1}` | Diamond–Shurman, GTM 228, Thm 9.6.5 (Deligne 1971; Shimura 1971 Thm 7.14 for `k = 2`) |
| `DSThm966` | `k = 1`: continuous `ρ : G_ℚ → GL₂(ℂ)`, finite image, unramified outside `N`, `tr = a_p`, `det = χ(p)` at Frobenius | Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1; Diamond–Shurman Thm 9.6.6 |

## 2. The table

| row | old form (frontier r3) | new leaves (published form, source) | new glue | Lean name of the proof |
|---|---|---|---|---|
| H-52 `G0Galois.FiniteImageHT` | composite (Tate 1967, Ax–Sen–Tate, Hilbert 90) | `TateTwistInvariants`, `AxSenTate` | none open (proved: open kernel, finite coefficient field, Speiser descent replacing Hilbert 90) | `finiteImageHT_of_tate` |
| H-32 `∀ p, PkgI4.T23_FontaineClosure p` | consequence (form on `V^∨`) | `FontaineDRTannakian p` (on `V`, printed `D_dR`) | none open (proved: `isDeRham_iff_std : IsDeRham ρ ↔ IsDeRhamStd ρ^∨`, clause (i) outright) | `t23_all_of_fontaine` |
| H-8 `ZInQ.Contrib.R10.DeRhamComparisonHT` | composite (Faltings, Tate, T10, HT clause) | `HodgeTateDecompAbVar`, `TateTwistInvariants`, `AxSenTate`, `DeRhamH1AbVar` | none open (proved: `Hom_{G_F}(V, ℂ_p(j)) ≅ (ℂ_p(j−1)^{G_F})^g × (ℂ_p(j)^{G_F})^g`, image of `G_F` for any finite `F`, `dim A ∈ ℕ`) | `deRhamComparisonHT_of_leaves` |
| H-22 `G0Galois.R14Det` | composite (Shimura, Deligne, Deligne–Serre) | `DSThm965`, `DSThm966` | `ArtinTransport` (open); `Semisimplification2`, `DetFromFrobenius` (proved) | `r14Det_of_ds`; glue proofs `semisimplification2_proof` (main), `detFromFrobenius_proof` (companion) |
| H-51 `G0Galois.SenTwist` | consequence (Sen 1980) | `TateTwistInvariants`, `AxSenTate` (used by the open glue) | `HTCharOfTwist`, `HTTwistShift` (open); `HTWeightsUnique` (proved) | `senTwist_of_glue`; `htWeightsUnique_proof` |
| H-10 `PkgI4.EigenformHT` | consequence (Kato, after dualization) | none statable (Kato's `V_{F_λ}(f)` is étale cohomology); uses the kernel's leaves `NewformOfEigenform`, `EigenformRepExists` | `EigenformHTNew` (open: Kato for newforms, transported and dualized); `AttachedConj`, `HTConj` (proved) | `eigenformHT_of_new`; `attachedConj_proof` (companion), `htConj_proof` |
| H-9 `PkgI4.PanBerger` | composite (Pan + Berger) | none statable (both need `B_st`) | — | `panBerger_of_templates` (composition for every predicate `IsPst`) |

All names are in namespace `ZInQ.Contrib.HodgeSplit`.

## 3. Row by row

### H-52 `FiniteImageHT` — done

`finiteImageHT_of_tate : TateTwistInvariants → AxSenTate → G0Galois.FiniteImageHT` (VERIFIED). The
row is copied verbatim (`scratch/leaf-fold5/Leaves5.lean` l. 50965). Steps: `ρ|_{G_{ℚ_p}}` is continuous
(Mathlib's `Field.absoluteGaloisGroup.map` is a continuous homomorphism), so its kernel is closed of
finite index, hence open, hence contains `G_M` for a finite Galois `M ⊆ ℚ̄_p`
(`krullTopology_mem_nhds_one_iff_of_normal`); the finitely many entries generate a finite coefficient
field `E` (g9-derham's `liftGL`); then g9-derham's `descent_finrank` (Speiser's lemma) gives
`[M:ℚ_p]·dim H_i(ρ_E) = dim Hom(E^n, ℂ_p(i)^{G_M})`, which is `n[E:ℚ_p][M:ℚ_p]` for `i = 0` (Ax–Sen–Tate)
and `0` otherwise (Tate). Hilbert 90 in the row's citation is replaced by Speiser's lemma, already a
kernel theorem.

### H-32 `T23_FontaineClosure` — done

The flagged issue was that pkg-I4's `IsDeRham ρ` computes `D_dR` on `V^∨` (as `Hom_G(V, B_dR)`). New
genuine definitions: `ddrStd ρ = (B_dR ⊗ ℚ_pⁿ)^{G_{ℚ_p}}` in coordinates and `IsDeRhamStd ρ`
(`dim = n`), the printed definition. The leaf `FontaineDRTannakian p` is Fontaine's theorem for them, in
matrix form: (a) duals; (b) sub on the last `b` coordinates and quotient on the first `a` of a block lower
triangular `ρ`; (c) block-diagonal sums; (d) Kronecker products; continuity of the inputs assumed. Proved
glue: `isDeRham_iff_std : IsDeRham ρ ↔ IsDeRhamStd (dualRep ρ)` (`ρ^∨(σ) = ρ(σ⁻¹)ᵀ`, through
coordinates of `φ : ℚ_pⁿ → B_dR`), clause (i) of T23 outright (`isDeRham_conj`), and the transposes of the
block and Kronecker shapes. `t23_all_of_fontaine : (∀ p, FontaineDRTannakian p) → ∀ p, T23_FontaineClosure p`
(VERIFIED). Caveat: the leaf combines Fontaine's abstract theorem (admissible representations of a regular
ring form a Tannakian subcategory) with "`B_dR` is regular"; Brinon–Conrad state the de Rham case as one
result (UNVERIFIED numbering).

### H-8 R10 amended — done (one leaf in the closest statable form)

`deRhamComparisonHT_of_leaves : HodgeTateDecompAbVar → TateTwistInvariants → AxSenTate → DeRhamH1AbVar →
ZInQ.Contrib.R10.DeRhamComparisonHT` (VERIFIED). The Hodge–Tate part is a real derivation:
`htSpaceOver_eq_map` identifies `Hom_{G_F}(V, ℂ_p(j))` with `(ℂ_p(j−1)^{G_F})^g × (ℂ_p(j)^{G_F})^g` through
the decomposition (extend `φ` to `ℂ_p ⊗ V`, compose with `e⁻¹`, read off coordinates); with
`range_gfToGqp_eq` (the image of `G_F` is `G_{F'}` for every finite `F`, not only Galois) and Tate's two
theorems, `htMultOver w = g·([w = 0] + [w = −1])`. The weight clause without a dimension hypothesis uses
abvar-bc's `dim_finite` (kernel), transported to pkg-I4's copy of `AbVar` by `rfl`.

Caveat on `DeRhamH1AbVar`: the published comparison theorems are about `H¹_ét(A_{F̄}, ℚ_p)`; étale
cohomology is not in Mathlib, so the leaf states "`V_p(A)^∨` is de Rham" with pkg-I4's Hom form of
`D_dR(V^∨)`. Under the strict rule this is the published statement transported through the standard
identification `H¹_ét = Hom(T_p A, ℤ_p) ⊗ ℚ_p` (Milne, *Abelian varieties*, Thm 15.1(a), UNVERIFIED); it
is the de Rham clause of the old R10 with the Hodge–Tate counts removed. `HodgeTateDecompAbVar` is printed
for the Tate module (Fontaine 1982; Tate 1967 for good reduction) with bases of the two `g`-dimensional
`F`-spaces chosen.

### H-22 `R14Det` — two printed leaves, one open glue

`r14Det_of_ds : DSThm965 → DSThm966 → Semisimplification2 → DetFromFrobenius → ArtinTransport → R14Det`
(VERIFIED), through the weight split `r14Det_of_wt` (Shimura's `k = 2` case is not needed: Deligne covers
`k ≥ 2`). The leaves are Diamond–Shurman's statements with the coefficients extended along
`K_{f,λ} → ℚ̄_ℓ` (given by `ιL ∘ ιC⁻¹`); they contain no semisimplicity and no global determinant.
Proved glue:
- `semisimplification2_proof` (main file): a non-semisimple 2-dimensional `ρ` has an invariant line; in a
  basis through it `ρ = (a ∗; 0 d)`, and `diag(a, d)` is continuous, semisimple, with the same
  characteristic polynomials and unramified wherever `ρ` is.
- `detFromFrobenius_proof` (companion): `ε := det ρ · χ_ℓ^{1−k}` agrees with the nebentypus character
  `ε₀ = ιL ∘ ιC⁻¹ ∘ χ ∘ (G_ℚ → (ℤ/N)^×)` at all arithmetic Frobenius elements outside `Nℓ`, both are
  continuous, so they are equal by the kernel's T18 (`C9Rhof.eq_of_eq_on_arithFrob`). Ingredients proved
  here: an arithmetic Frobenius at `v ∣ p` raises roots of unity of order prime to `p` to the `p`-th power
  (`arithFrob_pow_of_rootOfUnity`, a valuation argument), hence `χ_ℓ(Frob_p) = p` and the mod-`N`
  cyclotomic character of `Frob_p` is `p`; `ιC` is a bijection on roots of unity; continuity of `ε₀`
  (trivial on `Gal(ℚ̄/ℚ(μ_N))`) and of `χ_ℓ` (Mathlib's `cyclotomicCharacter.continuous`).
Open glue: `ArtinTransport : DSThm966 → R14DetWt1` (realize Deligne–Serre's complex representation
over `ℚ̄`, then `ιL`; semisimple by Maschke; `ε = det ρ`).

### H-51 `SenTwist` — reduced to Tate's theorems plus two glue Props

Sen's operator is not in Mathlib, so Sen 1980 cannot be a leaf. `senTwist_of_glue : HTCharOfTwist →
HTTwistShift → HTWeightsUnique → G0Galois.SenTwist` (VERIFIED), with `HTWeightsUnique` proved
(`htWeightsUnique_proof`: `htMult` does not depend on the finite coefficient field; core
`dsp_finrank_extend`, `E'ⁿ ≅ (Eⁿ)^{[E':E]}` equivariantly). The two open Props are the content of the
argument through Tate's theorems: `HTCharOfTwist` (if `ρ` and `ψ ⊗ ρ` are Hodge–Tate with full weight
multisets, `ψ|_{G_{ℚ_p}} ≅ ℂ_p(s)` with `s ∈ ℤ`; needs the Hodge–Tate decomposition criterion, built on
`TateTwistInvariants` and `AxSenTate`, applied embedding by embedding of the coefficient field) and
`HTTwistShift` (twisting by `ℂ_p(s)` shifts all weights by `−s`). Both are project glue: no literature
beyond Tate 1967 is needed.

### H-10 `EigenformHT` — reduced to newforms; the newform case is not statable

Kato's theorem (Astérisque 295, §§9.2–9.4) is about Kato's `V_{F_λ}(f)`, built from étale cohomology of
modular curves; it cannot be a leaf over Mathlib today. Proved: `eigenformHT_of_new : EigenformHTNew →
NewformOfEigenform → EigenformRepExists → AttachedConj → HTConj → EigenformHT` (VERIFIED), and both glue
Props `AttachedConj` (companion: semisimple reps with equal Frobenius traces outside a finite set are
conjugate, from the kernel's T18 and T19 via `C9Rhof.iso_of_arithFrob`) and `HTConj` (g12-det's glue:
Hodge–Tate weights are invariant under conjugation by `GL_n(ℚ̄_p)`). So `EigenformHT` follows from the
kernel's leaves `NewformOfEigenform` (I4-L5) and `EigenformRepExists` (implied by `R14Det`) and the open
`EigenformHTNew` (Kato for newforms, transported to any semisimple attached `ρ` and dualized).

### H-9 `PanBerger` — cannot be split today

Pan's Theorem 1.0.4 and Berger's Théorème 0.7 both use "potentially semistable", i.e. `B_st`-admissible;
Mathlib 4.35 has `BDeRhamPlus`/`BDeRham` but no `B_cris`, `B_st` (VERIFIED by search of
`.lake/packages/mathlib`). `panBerger_of_templates (IsPst) : PanFor IsPst → BergerDR IsPst → PanBerger`
(VERIFIED) shows the row is exactly their composite for every predicate `IsPst`; it becomes a theorem from
two published-form leaves once a genuine potentially-semistable predicate exists. A second, independent gap
is normalization: Pan's printed conclusion is `ρ ≅ ρ_f ⊗ ψ` with geometric Frobenius, while `PanFor` is an
arithmetic-Frobenius trace form; the conversion needs `det ρ_f(Frob_q) = χ(q)q^{k−1}` and
`ā_q = χ̄(q) a_q` (not formalized here).

## 4. Remarks

- `htMult` (pkg-I4) divides a `ℚ_p`-dimension by `[E:ℚ_p]`. For `K = ℚ_p` this is the common Hodge–Tate
  multiplicity at every embedding of `E` (the Sen operator's characteristic polynomial has coefficients in
  `E ⊗ ℚ_p = E`, and integral roots are fixed by every embedding), so the definition is sound; this task
  proved that it does not depend on `E` (`htMult_eq_of_lifts`).
- The same Tate leaves serve H-52, H-8 and (through the open glue) H-51.
- `DSThm966` was first written without continuity of `ρ`; continuity is part of Deligne–Serre's statement
  and is needed to make the `ℓ`-adic transport continuous, so the leaf states it.

## 5. How to check

```
lake build ZInQKernel.Contrib.R10.Amend ZInQKernel.Contrib.AbVarBC.Dim \
  ZInQKernel.HDecomp.ModCurves.C9 ZInQKernel.HDecomp.Textbook.C10Closed \
  ZInQKernel.Contrib.Chebotarev.FrobeniusDense
lake env lean scratch/hodge-split/HodgeSplit.lean     # ~25 s
lake env lean scratch/hodge-split/Companion.lean      # ~30 s
```
Each file ends with `#print axioms` for its main theorems.

## 6. What remains

- Open glue: `ArtinTransport` (H-22), `HTCharOfTwist` and `HTTwistShift` (H-51).
- Not statable today: Kato's theorem (H-10, `EigenformHTNew`), Pan's and Berger's theorems (H-9).
- Locators: every theorem number above is UNVERIFIED except where marked.
