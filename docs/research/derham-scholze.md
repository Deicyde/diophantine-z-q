# derham-scholze: the de Rham and Hodge–Tate rows re-routed to the manuscript's `lem:de-rham-descent`

Task derham-scholze, 2026-11-17. Base `wip/derham-scholze` = `origin/wip/leaf-fold33b` (d67ea55f6; `origin/main` is
an ancestor). Log `scratch/derham-scholze/log.md`. Lean: `ZInQKernel/Contrib/OneProof/DeRhamScholze.lean` (scratch
copy `scratch/derham-scholze/DeRhamScholze.lean`).

## 1. Result

**Both research fields are re-routed to the manuscript's own proof (`lem:de-rham-descent`, step C3) and proved in
Lean from two leaves: Scholze's comparison as the manuscript applies it, and Milne's identification
`V_ℓ(A) ≅ H¹_ét(A_{F̄}, ℚ_ℓ)^∨`.** Everything else in the route is proved in Lean: duality, the Hodge–Tate
weights read off the de Rham filtration, which is the manuscript's "consequently" and covers Fontaine's
"de Rham ⇒ Hodge–Tate" in this case, and Fontaine's `t`.

```
DeRhamScholze.deRhamVpAbVarDirect_of_leaves (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality) :
    DeRhamPrint.Direct.DeRhamVpAbVarDirect
DeRhamScholze.TT.hodgeTateDecompOr_of_scholzeMilne (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality) :
    ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr
```

Both theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). `#discharges` shows that
each one discharges its field and still assumes exactly `[DeRhamScholze.ScholzeDeRhamAlg, T10Etale.T10_TateDuality]`
(VERIFIED, §6).

* **`ScholzeDeRhamAlg`** (new leaf). For a finite `F/ℚ_p`, a proper smooth `F`-scheme `X` and every `i`,
  `Hⁱ_ét(X_{F̄}, ℚ_p)` is de Rham and the Hodge filtration of its `D_dR` has its jumps in `[0, i]`. The statement uses
  **Mathlib's own `ℓ`-adic cohomology** (`Scheme.EllAdicCohomology`, pro-étale, Bhatt–Scholze) with the Galois action
  by transport of structure. It is rated a **consequence** of Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 with Thms 9.1
  and 9.3, **not printed form**: the print is about rigid-analytic varieties, which Mathlib does not have (§3.1,
  Known issue 1).
* **`T10_TateDuality`** (t10-etale's existing Milne leaf, reused unchanged). It is not an open field at this base,
  so the fold adds it back. Rated printed form with dictionary, flagged unread.
* **Proved glue:** the duality and transport of the de Rham property along Milne's identification
  (`DeRhamScholze.lean`); `DeRhamHodgeTate01`, "de Rham with Hodge jumps in `[0, 1]` ⇒ Hodge–Tate with weights
  `{0, 1}`" (`DeRhamScholzeHT.lean`, from Tate's two theorems via a twisted Tate–Sen lemma); and `FontaineTwistT`:
  `t = log [ε₀]` is a uniformizer of `B_dR^+` with `σ(t) = χ(σ) t` (`DeRhamScholzeT.lean`). These are all new Lean
  proofs, with no new hypotheses.
* **Fold:** the autofold spec discharges both fields with the two leaves above. The dry run gives
  `strict count: 4/27 on 31 -> 4/27 on 31` (two GLUE fields become two GLUE leaves). The fold module compiles with
  standard axioms (VERIFIED, §6). The count drops by 1 when `T10_TateDuality` is rated LEAF after a reading of
  Milne. `ScholzeDeRhamAlg` stays GLUE/GLUE (consequence) under the strict leaf review (queue25, 2026-11-17; §3.2):
  the print states de Rham only for rigid-analytic varieties.
* **Coordination with derham-range:** the new route does not need `range_iotaF_eq_bdrFix`. It reaches derham-direct's
  print form through `isDeRhamTensorOver_iff` (the tower law), so derham-range's lemma is neither duplicated nor
  required.

## 2. The manuscript's lemma and what each row needs

`lem:de-rham-descent` (diophantine_zq.tex L10939-11004, step C3; read in full, VERIFIED) has four parts:

1. (L10953-10965) `A/F` is smooth proper, its analytification is smooth proper rigid; Scholze's Cor. 1.8 (with the
   corrigendum) makes `H^i` of the analytification de Rham; Thms 9.1 (coherent, hence filtered de Rham cohomology)
   and 9.3 (`ℤ/ℓⁿ`-cohomology, `ℓⁿ` invertible since `char F = 0`) identify it with the algebraic cohomology,
   compatibly with `G_F`; so `H¹_ét(A_{F̄}, ℚ_ℓ)` is de Rham.
2. (L10966-10974) Milne's canonical Galois-equivariant `V_ℓ(A) ≅ H¹_ét(A_{F̄}, ℚ_ℓ)^∨` (Milne v2.00 Part I Thm
   12.1(a)), closure under duals and subquotients (Brinon–Conrad 5.2.1, 6.3.3), coefficients: `r|_{G_F}` de Rham.
3. (L10976-10991) finite descent from `F'` to `K` (Brinon–Conrad 6.3.8, finite case, written out).
4. (L10993-10998) Hodge numbers of `H¹_dR(A/F)` are `2, 2`, so the Tate module has weights `0,0,−1,−1`, hence each
   summand `0, −1`; descent preserves them. L11001-11004: the Hodge–Tate comparison alone would not give de Rham.

The two research fields concern `V_p(A)` for an abelian variety `A` over a finite `F/ℚ_p` (no `r`, no coefficient
field, no descent):

* `deRhamVpAbVarDirect` (`DeRhamPrint.Direct.DeRhamVpAbVarDirect`, `DeRhamPrintDirect.lean` L187): `dim_{F'} D_dR(V_p A)
  = dim V_p A`. Parts 1-2 of the lemma.
* `hodgeTateDecompOr` (`ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr`): `ℂ_p ⊗ V_p(A) ≅ ℂ_p(1)^a ⊕ ℂ_p^b` (or the Hom
  form), some `a, b`; its consumer (hodgetate-from-dr) proves `a = b = g` from the Weil pairing. Part 4 of the lemma
  (weights in `{0, −1}`), without the multiplicities.

Parts 3 and the coefficient step of part 2 are not used by these two fields and are not formalized here.

## 3. The new leaves and their ratings

### 3.1 `ScholzeDeRhamAlg` (Scholze 2013, Cor. 1.8 with Thms 9.1, 9.3, as the manuscript applies it)

```lean
def ScholzeDeRhamAlg : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (X : Over (Spec (CommRingCat.of F))) [IsProper X.hom] [Smooth X.hom] (i : ℕ),
    IsDeRhamFam p (F := F) (rhoH X p i) ∧ HodgeRange p (F := F) (rhoH X p i) i
```

Objects (all genuine definitions; none introduced for the purpose):

* `Hⁱ(X_{F̄}, ℚ_p) = ℚ_p ⊗_{ℤ_p} Hⁱ(X_{F̄}, ℤ_p)` (`HQ`), where `Hⁱ(X_{F̄}, ℤ_p)` is **Mathlib's**
  `Scheme.EllAdicCohomology (X ×_F Spec F̄) p i` (pro-étale cohomology of the sheaf `U ↦ C(U, ℤ_p)`, Bhatt–Scholze
  2015 Def. 6.8.1; `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean`), with t10-etale's `ℤ_p`-module structure
  (`T10Etale.lean`: multiplication on the coefficient sheaf through `Sheaf.H.map`, checked in degree 0).
* the action of `σ ∈ G_F`: transport along the scheme automorphism `1 × Spec(σ⁻¹)` of `X_{F̄}` (`galHX`; t10-etale's
  `transportₗ`, proved bijective and checked in degree 0). For an abelian variety and `i = 1` it is t10-etale's
  `galH` by `rfl` (`galHX_abVar`).
* `D_dR(W) = (B_dR ⊗_{ℚ_p} W)^{G_F}` (`ddrFam`, the carrier of the kernel's `ddrTensorOver`, `ddrFam_rep`); de Rham
  = finite-dimensional with `dim_{ℚ_p} D_dR = [F:ℚ_p] dim W` (`IsDeRhamFam`, the kernel's `IsDeRhamTensorOver` plus
  finite dimension).
* `Fil^j B_dR = 𝔪^j` (`filB`; `= t^j B_dR^+ = ξ^j B_dR^+`, `B_dR^+` a DVR, `TDict.tt_eq_varpi_mul_unit`), and
  `Fil^j D_dR = D_dR ∩ (Fil^j B_dR ⊗ W)` (`filD`); `HodgeRange … i` says `Fil⁰ D_dR = D_dR` and
  `Fil^{i+1} D_dR = 0`.

**Rating: consequence of the print, not printed form.** The print (Cor. 1.8, wording quoted from arXiv:1205.3463 by
h-leaves §3.1 and read again by the locator audit, `locators.md` row R10): for a proper smooth *rigid-analytic*
variety `X` over a complete discretely valued `k/ℚ_p` with perfect residue field, `Hⁱ(X_ét, ℚ_p)` is de Rham, with
associated filtered `k`-vector space `Hⁱ_dR(X)`. Mathlib has no rigid-analytic spaces and no algebraic de Rham
cohomology, so the print cannot be stated. The leaf is the algebraic statement the manuscript derives from it
(L10953-10965), through these steps:

1. the analytification of a proper smooth `F`-scheme is a proper smooth rigid space (manuscript L10953-10954);
2. Thm 9.1 (coherent, hence filtered de Rham cohomology) and Thm 9.3 (`ℤ/pⁿ`-cohomology, `p` invertible since
   `char F = 0`), compatibly in `n` and with `G_F` (manuscript L10955-10964);
3. (part of step 2, not a separate step) the journal's Cor. 1.8 is stated over `k̄`, so the passage to `F̄` is part
   of the cited comparison: provenance (b), not on-the-spot (strict leaf review queue25, 2026-11-17, folding its G3 into G2);
4. *on-the-spot (dictionary)*: Mathlib's `ℓ`-adic cohomology is pro-étale; the manuscript's (and Scholze's)
   `H¹_ét(·, ℤ_p)` is `lim_n H¹_ét(·, ℤ/pⁿ)`. Sketch: Bhatt–Scholze 2015 §5.6 (continuous cohomology equals
   pro-étale cohomology of `ℤ̂_p`; UNVERIFIED number); for `X_{F̄}` proper the groups `Hⁱ_ét(X_{F̄}, ℤ/pⁿ)` are finite,
   so `lim¹ = 0` and both sides are `lim_n Hⁱ_ét(X_{F̄}, ℤ/pⁿ)`;
5. the jump clause: the filtered isomorphism `D_dR(Hⁱ) ≅ Hⁱ_dR(X)` (part of Cor. 1.8) carries `Fil^j D_dR` to the
   Hodge filtration `Fil^j Hⁱ_dR = im Hⁱ(Ω^{≥j})`, which is everything for `j ≤ 0` and zero for `j ≥ i + 1`
   (`Ω^{≥j}` sits in degrees `≥ j`). This is the standard description of `Fil` on `D_dR` (`(Fil^j B_dR ⊗ V)^{G_F}`,
   `V` trivially filtered). A definition-level reading of Cor. 1.8: provenance (b), not on-the-spot (queue25).

### 3.2 Strict leaf review (queue25, 2026-11-17)

Verdict on `ScholzeDeRhamAlg`: GLUE/GLUE, kind consequence (crowd-kit leaf review, queue25). Scholze's journal Cor. 1.8
covers rigid-analytic varieties only; the algebraic case is only pointed to ("by suitable GAGA results") or credited to
Faltings in the journal's Overview, which does not state it. The jump range `[0, i]` and the coefficients are correct.
Deciding step: the algebraic-to-rigid comparison (analytification plus Thms 9.1/9.3). A second step: Mathlib's pro-étale
`Hⁱ` against classical étale cohomology (Bhatt–Scholze 2015 §5.6; not cited by the manuscript; on-the-spot, step 4).

Provenance: (a) manuscript, diophantine_zq.tex L10953-10964 (lem:de-rham-descent); (b) Scholze 2013 Cor. 1.8 and
Thms 9.1/9.3 with the corrigendum (steps 1-3 and 5); (c) on-the-spot: the pro-étale comparison (step 4).

Manuscript check: lem:de-rham-descent is correct at the level of its citations, through the GAGA route the print names.
On our side, not the manuscript's: Mathlib's `EllAdicCohomology` is pro-étale, and its comparison with
`lim_n Hⁱ_ét(·, ℤ/pⁿ)` is not proved in Mathlib (an unstated dictionary step of the Lean statement).

The leaf asserts nothing beyond the print plus these dictionary steps, and it does not mention the Hodge numbers
(not statable without `H_dR`).

### 3.2 `T10_TateDuality` (Milne, reused from t10-etale)

`T10Etale.T10_TateDuality` (t10-etale; `ZInQKernel/HDecomp/Textbook/T10Etale.lean`), unchanged: for `A/K` and
`ℓ ≠ char K`, a `ℤ_ℓ`-linear `φ : H¹(A_{K̄}, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)` with `φ ∘ galH σ = (galT σ⁻¹)^∨ ∘ φ`, over
Mathlib's pro-étale cohomology. It is the manuscript's citation (Milne, *Abelian varieties* v2.00, Part I, Thm
12.1(a), L10966-10970) with the equivariance the manuscript states ("canonical, Galois-equivariant"); t10-etale's
docstring cites the refereed version (Milne 1986, Thm 15.1(a)). It was a textbook leaf `t10` of earlier bundle
generations (av-b2 §2.6: "leaf, confirmed") and is no longer open at this base (pruned as unused), so the fold adds
it back as a leaf. **Rating: printed form with dictionary** (the pro-étale/étale comparison of §3.1 step 4, and
equivariance from canonicity), flagged unread (Milne not read here).

### 3.3 `DeRhamHodgeTate01` (glue; the manuscript's "consequently", L10995) and `FontaineTwistT`

```lean
def DeRhamHodgeTate01 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (V : Type) [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V),
    IsDeRhamFam p (fun σ => ρ.dual σ) → HodgeRange p (fun σ => ρ.dual σ) 1 →
    ∃ (a b : ℕ) (e : (V →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ σ f, e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ ρ σ⁻¹) =
        ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
          (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k)))
```

A de Rham representation `V^∨` whose Hodge filtration has its jumps in `[0, 1]` is Hodge–Tate with weights in
`{0, 1}`, in the Hom form of htdecomp-or (`Hom(V, ℂ_p) = ℂ_p ⊗ V^∨`). This is the step behind the manuscript's
"Consequently the Tate module has weights 0,0,−1,−1": Fontaine's "de Rham ⇒ Hodge–Tate, `gr D_dR ≅ D_HT`", which
the lemma uses without a citation. It is **on-the-spot glue** and is **proved in Lean** (§4) from

* Tate's two theorems (`ℂ_p(i)^{G_K} = 0` for `i ≠ 0`, `ℂ_p^{G_K} = K`), proved in the tree
  (`tateTwistInvariants_proof`, `axSenTate_proof`), and
* `FontaineTwistT`: `B_dR^+` has a uniformizer `t` with `σ(t) = χ(σ) t` (Fontaine's `t = log [ε]`), see §4.3.

## 5. Known issues

1. **Scholze's Cor. 1.8 is not statable in Lean as printed.** It is a theorem about proper smooth rigid-analytic
   varieties, with the filtered `k`-vector space `Hⁱ_dR(X)`; Mathlib v4.35 has neither rigid-analytic spaces nor
   algebraic de Rham cohomology. The leaf `ScholzeDeRhamAlg` is the algebraic form the manuscript itself derives
   (L10955-10965), so it is a *consequence* of the cited print through Thms 9.1/9.3 and two on-the-spot dictionary
   steps (§3.1 steps 3-4), not printed form. This is a limitation of the library, not a gap in the manuscript.
2. **Mathlib's `ℓ`-adic cohomology is pro-étale.** The manuscript, Scholze and Milne use étale cohomology
   (`lim H¹_ét(·, ℤ/ℓⁿ)`). The identification (Bhatt–Scholze 2015 §5.6) is not cited by the manuscript; it is an
   on-the-spot dictionary step (§3.1 step 4) shared with t10-etale's leaf.
3. **Milne's notes are unrefereed** (h-trust C3 classifies the manuscript's citation, Milne v2.00 Part I Thm 12.1(a),
   as [P]). The reused leaf `T10_TateDuality` cites the refereed Milne 1986 Thm 15.1(a) (UNVERIFIED number). Neither
   was read here. Milne states the identification over a separably closed field; the Galois equivariance the
   manuscript asserts ("canonical, Galois-equivariant") follows from canonicity, and the leaf states it.
4. **The weights are not read off Hodge numbers in Lean.** The manuscript's weight claim uses the Hodge numbers
   `2, 2` of `H¹_dR(A/F)` (L10993); `H_dR` is not in Mathlib. The Lean route keeps only what the filtered comparison
   gives without `H_dR` (Hodge jumps in `[0, 1]`), and the consumer of `hodgeTateDecompOr` already proves
   `a = b = g` from the Weil pairing (hodgetate-from-dr), so no Hodge number is needed downstream.
5. **"Consequently" (L10995) is Fontaine's de Rham ⇒ Hodge–Tate**, which the lemma does not cite. It is stated as
   the glue Prop `DeRhamHodgeTate01` and proved in Lean (§4.2) from Tate's theorems and Fontaine's `t`
   (`FontaineTwistT`, itself proved, §4.3), so it adds no hypothesis. Labelled on-the-spot: the proof is Fontaine's
   standard argument (gr maps plus Tate–Sen), and every step of it is in Lean.
6. L11001-11004 (Hodge–Tate comparison alone would not give de Rham): respected. Neither row uses a Hodge–Tate
   decomposition as an input; the de Rham row uses only Scholze + Milne + duality, and the Hodge–Tate row derives the
   decomposition from the de Rham comparison.
7. The corrigendum (Forum Math. Pi 4 (2016) e6): per the locator audit (`locators.md` R10), it repairs the
   definitions of the period sheaves and keeps the comparison results; no issue for this use. Not re-read here.

## 4. The glue proved in Lean

### 4.1 The de Rham row (`DeRhamScholze.lean`)

| declaration | statement | from |
|---|---|---|
| `galHX`, `galHX_abVar`, `galHX_bijective`, `rhoH` | `σ` on `Hⁱ(X_{F̄}, ℤ_p)` and `Hⁱ(X_{F̄}, ℚ_p)`; equals t10-etale's `galH` | t10-etale's `transportₗ` |
| `ddrFam`, `ddrFam_rep`, `IsDeRhamFam`, `filB`, `filD`, `HodgeRange` | `D_dR`, de Rham, `Fil^j` | definitions |
| `map_ddrFam`, `map_filD`, `isDeRhamFam_of_equiv`, `hodgeRange_of_equiv` | an equivariant isomorphism `W ≅ W'` carries `D_dR` and `Fil^j D_dR` across | linear algebra |
| `dualBC`, `dualBC_comm` | `ℚ_p ⊗ Hom_{ℤ_p}(T, ℤ_p) ≅ Hom_{ℚ_p}(ℚ_p ⊗ T, ℚ_p)` (`T` finite free), equivariant | Mathlib's `IsBaseChange.toDualBaseChange` |
| `milneE`, `milneE_comm` | `H¹(A_{F̄}, ℚ_p) ≅ V_p(A)^∨`, `G_F`-equivariant | `T10_TateDuality`, T26 (from `mumfordTorsionAlgClosed_proof`) |
| `dual_deRham_of_scholze` | `V_p(A)^∨` de Rham with Hodge jumps in `[0, 1]` | the two leaves |
| `isDeRhamTensorOver_of_scholze` | `V_p(A)` de Rham | + duality `DeRhamPrint.isDeRhamTensorOver_dual` (`B_dR` a field, `bdRInvariantsPrinted_proof`), `Module.evalEquiv` |
| `deRhamVpAbVarDirect_of_leaves` | **the field `deRhamVpAbVarDirect`** | + derham-direct's `isDeRhamTensorOver_iff` |
| `lemDeRhamDescent_tate` | the manuscript's lemma for `V_p(A)` (parts 1-2, jump clause) | |
| `hodgeTateDecompOr_of_leaves` | **the field `hodgeTateDecompOr`** from the leaves and `DeRhamHodgeTate01` | htdecomp-or's `or_of_hom` |

### 4.2 `DeRhamHodgeTate01` (`DeRhamScholzeHT.lean`)

File `ZInQKernel/Contrib/OneProof/DeRhamScholzeHT.lean` (scratch copy `scratch/derham-scholze/HTFromDR.lean`).
`DeRhamScholze.HT.deRhamHodgeTate01_of_fontaineT : FontaineTwistT → DeRhamHodgeTate01`, with standard axioms
(VERIFIED). The proof is Fontaine's argument, written out:

1. `θ₀ : Fil⁰ B_dR → ℂ_p` (`ι(b) ↦ θ(b)`) and `θ₁ : Fil¹ B_dR → ℂ_p` (`ι(t c) ↦ θ(c)`) are `ℚ_p`-linear (`theta0`,
   `theta1`).
2. In Hom form (`D_dR(V^∨) = Hom_{G_F}(V, B_dR)`, `map_ddrFam_dual`; `Fil^j = Hom(V, Fil^j B_dR)`,
   `map_filRange_dual`), `gr⁰ φ = θ₀ ∘ φ` lands in `Hom_{G_F}(V, ℂ_p)` (`gr0_mem`, by θ-equivariance) and
   `gr¹ φ = θ₁ ∘ φ` lands in `Hom_{G_F}(V, ℂ_p(1))` (`gr1_mem`, by `σ(t) = χ(σ) t`). The kernel of `gr⁰` is `Fil¹`
   (`ker θ = 𝔪 = (t)`) and the kernel of `gr¹` is `Fil² = 0`. Rank–nullity then gives
   `[F:ℚ_p] dim V = dim D_dR ≤ dim Hom_{G_F}(V, ℂ_p) + dim Hom_{G_F}(V, ℂ_p(1))` (`finrank_ddr_le`).
3. **Tate–Sen, twisted and relative** (`linIndep_two`): `F'`-linearly independent families in
   `Hom_{G_F}(V, ℂ_p)` and in `Hom_{G_F}(V, ℂ_p(1))` are together `ℂ_p`-linearly independent in
   `Hom_{ℚ_p}(V, ℂ_p)`. The proof is a minimal relation, twisted by `χ^{wt j − wt k}`: by Tate's `ℂ_p(±1)^{G_F} = 0`
   the cross terms vanish, and by Ax–Sen–Tate `ℂ_p^{G_F} = F'` the remaining coefficients lie in `F'`. Both of
   Tate's theorems are proved in the tree.
4. Writing `a, b` for the `F'`-dimensions, step 3 gives `a + b ≤ dim V` and step 2 gives `a + b ≥ dim V`. So the
   two bases together form a `ℂ_p`-basis of `Hom(V, ℂ_p)`, and the coordinate isomorphism is
   `Hom(V, ℂ_p) ≅ ℂ_p^a ⊕ ℂ_p(−1)^b`, `G_F`-equivariant in the exact shape of htdecomp-or's `HodgeTateDecompHom`.

### 4.3 `FontaineTwistT` (`DeRhamScholzeT.lean`)

File `ZInQKernel/Contrib/OneProof/DeRhamScholzeT.lean` (scratch copy `scratch/derham-scholze/FontaineT.lean`).
`DeRhamScholze.TT.fontaineTwistT : DeRhamScholze.HT.FontaineTwistT`, with standard axioms (VERIFIED). Take `ε₀`
derham-print's generator (`TDict.eps rootSystem`) and `t = log [ε₀]` (bst-construct's `logTeich`).

* **Uniformizer** (`maximalIdeal_eq_logTeich`): `log(1 + X) = X + X² g` (`logSeries_eq`), and `psEval X` is
  `[ε₀] − 1` (`psEval_X`). So `t ≡ [ε₀] − 1 = TDict.xe mod 𝔪²`, which lies in `𝔪 ∖ 𝔪²` (TDict's `xe_mem`,
  `xe_not_mem_sq`). Hence `t = ξ · unit` (`eq_xi_pow_mul_unit`) and `𝔪 = (t)`.
* **`σ(t) = χ(σ) t`** (`logTeich_flatAct`): `σ(log [ε]) = log [σ ε]` (bst-construct's `bdrAct_logTeich`).
  Coordinatewise, `σ(ε₀^{(k)}) = (ε₀^{(k)})^{χ(σ) mod pᵏ}` (`root_flatAct`, from Mathlib's
  `cyclotomicCharacter.spec`, after lifting the `pᵏ`-th roots of unity of `ℂ_p` to `ℚ̄_p`). pb-pst's `log_decomp`
  with these exponents, together with the `p`-adic separatedness of `A_max` (`amax_sep`), gives
  `log [σ ε₀] − χ(σ) log [ε₀] ∈ ⋂_k pᵏ A_max = 0`. This is pb-pst's `logTeich_eq_mul` with the exponent
  identified as `χ(σ)`.

`deRhamHodgeTate01_proof := deRhamHodgeTate01_of_fontaineT fontaineTwistT` and
`hodgeTateDecompOr_of_scholzeMilne := hodgeTateDecompOr_of_leaves hS hT deRhamHodgeTate01_proof`.

## 6. Compile log, `#discharges`, fold dry run (all VERIFIED, 11-17, Lean 4.35.0 / Mathlib v4.35.0)

| check | outcome |
|---|---|
| `lake env lean scratch/derham-scholze/DeRhamScholze.lean` | no errors (`milneE_comm` needs `maxHeartbeats 4000000`: transport between pkg-I4's and the kernel's copies of the abelian variety) |
| `lake env lean scratch/derham-scholze/HTFromDR.lean` | no errors; `deRhamHodgeTate01_of_fontaineT`: `[propext, Classical.choice, Quot.sound]` |
| `lake env lean scratch/derham-scholze/FontaineT.lean` | no errors; `fontaineTwistT_proof`: `[propext, Classical.choice, Quot.sound]` |
| `lake build ZInQKernel.Contrib.OneProof.DeRhamScholze ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` | built (16218 jobs) |
| `lake build ZInQKernel.Contrib.OneProof.DeRhamScholzeT` (with `DeRhamScholzeHT`) | built |
| `scratch/derham-scholze/Discharges.lean` (full output `Discharges-output.txt`) | see below |
| `python3 scripts/one_proof/autofold.py scratch/derham-scholze/autofold.json --dry-run` (`autofold-dryrun.txt`) | `strict count: 4/27 on 31 -> 4/27 on 31; strictest 4/27 -> 4/27`; nothing written to the tree |
| the dry-run module with line 1 stripped (`FoldDryRun.lean.txt`), `lake env lean` | compiles; `HDec.HSyn.sixContactMin_of_open68`: `[propext, Classical.choice, Quot.sound]` |

```
DISCHARGES [OpenResearchLeaves48.hodgeTateDecompOr] by DeRhamScholze.TT.hodgeTateDecompOr_of_scholzeMilne
  still assumes: [DeRhamScholze.ScholzeDeRhamAlg, T10Etale.T10_TateDuality]
DISCHARGES [OpenResearchLeaves48.deRhamVpAbVarDirect] by DeRhamScholze.deRhamVpAbVarDirect_of_leaves
  still assumes: [DeRhamScholze.ScholzeDeRhamAlg, T10Etale.T10_TateDuality]
'DeRhamScholze.deRhamVpAbVarDirect_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamScholze.TT.hodgeTateDecompOr_of_scholzeMilne' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamScholze.TT.deRhamHodgeTate01_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamScholze.TT.fontaineTwistT' depends on axioms: [propext, Classical.choice, Quot.sound]
'DeRhamScholze.lemDeRhamDescent_tate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(`#discharges` also lists the older discharges of these fields, e.g. through `DeRhamVpAbVarAdm` or
`HodgeTateDecompH1`.)

Files (no `sorry`, no `#eval`/`run_cmd`/notation/macros; none imports `ZInQKernel.OneProof.Main`):

| file | size | imports | content |
|---|---|---|---|
| `ZInQKernel/Contrib/OneProof/DeRhamScholze.lean` | 25 KB | `T10Etale`, `DeRhamRange`, `HodgeTateDecompOrH1`, `MumfordTorsionAlgClosed` | the leaf `ScholzeDeRhamAlg`, the glue Prop `DeRhamHodgeTate01`, §4.1 |
| `ZInQKernel/Contrib/OneProof/DeRhamScholzeHT.lean` | 35 KB | `DeRhamScholze` | `FontaineTwistT` (statement), §4.2 |
| `ZInQKernel/Contrib/OneProof/DeRhamScholzeT.lean` | 13 KB | `DeRhamScholzeHT`, `PanBergerPst`, `PanBergerSanity`, `DeRhamPrintTDict`, `BdRInvariants` | §4.3 and the final theorems |

The scratch copies (`scratch/derham-scholze/{DeRhamScholze,HTFromDR,FontaineT}.lean`) are the development versions.
`Statement.lean` copies the two fields verbatim and checks them `Iff.rfl` against the tree.

## 7. Autofold spec, kinds rows, locators

`scratch/derham-scholze/autofold.json` imports `ZInQKernel.Contrib.OneProof.DeRhamScholzeT` and does the following:

* `deRhamVpAbVarDirect` ← `DeRhamScholze.deRhamVpAbVarDirect_of_leaves {n}.scholzeDeRhamAlg {n}.t10TateDuality`, with
  new leaves `scholzeDeRhamAlg : DeRhamScholze.ScholzeDeRhamAlg` (kind `consequence`, flag "pending review: …") and
  `t10TateDuality : T10Etale.T10_TateDuality` (kind `published`, flag "unread: …; locator UNVERIFIED");
* `hodgeTateDecompOr` ← `DeRhamScholze.TT.hodgeTateDecompOr_of_scholzeMilne {n}.scholzeDeRhamAlg {n}.t10TateDuality`,
  with no new leaf.

Both new rows count GLUE (a consequence; an unread print), so the count is unchanged (two GLUE fields become two GLUE
leaves). **Recommendation:** fold. The content gains: (i) the H rows now follow the manuscript's C3 exactly as
cited (Scholze + Milne), with no Fontaine 1982/Tate 1967/Berger/Faltings HT-comparison input, as
L11001-11004 require; (ii) both leaves are stated over Mathlib's genuine étale (pro-étale) cohomology, a target the
community can formalize; (iii) one leaf feeds both rows. One reading could turn a row into LEAF: Milne's
Thm 12.1(a) (or Milne 1986 Thm 15.1(a)) for `t10TateDuality`. `scholzeDeRhamAlg` stays a consequence (strict leaf
review queue25, §3.2).

Proposed `locators.md` rows (not added, since `locators.md` is not this task's file):

* *Scholze 2013 Cor. 1.8 + Thms 9.1, 9.3 (+ corrigendum), algebraic form over Mathlib's `EllAdicCohomology`
  (`DeRhamScholze.ScholzeDeRhamAlg`): consequence (rigid → algebraic via 9.1/9.3; `F̄` vs `ℂ_p`; pro-étale vs étale).
  Locators as in row R10.*
* *Milne, AV v2.00 Part I Thm 12.1(a) (manuscript) / Milne 1986 Thm 15.1(a) (`T10Etale.T10_TateDuality`):
  equivariant `H¹(A_{K̄}, ℤ_ℓ) ≅ Hom(T_ℓ A, ℤ_ℓ)`; numbers UNVERIFIED.*

## 8. What remains

* Readings: Milne's theorem (unread here), and the integrator's ruling on `scholzeDeRhamAlg`'s rating.
* The fold itself (integrator): autofold without `--dry-run`, build, hash guard, OpenStatements, render_open.
* Not done, and not needed by the two fields: the manuscript's descent from `F` to `K` and the coefficient-field step
  (parts 2-3 of the lemma for `r`), and the Hodge numbers `2, 2` (they need `H_dR`, which is not in Mathlib; the
  consumer gets `a = b = g` from the Weil pairing).
* Optional infrastructure, not used by any proof: functoriality of t10-etale's transport (`galHX` is a group action;
  §3.1 states the leaf over the operators, which needs no group law).
