# pkg-I3: Faltings 1983 and Mumford's structure theorems as Lean leaves (steps A9, C2, C10, E1)

Status: research note (task pkg-I3, 2026-11-11). Drafts: `scratch/pkg-I3/I3.lean` (694 lines,
compiles with `lake env lean`; no `sorry`); log:
`scratch/pkg-I3/log.md`. No file under `ZInQKernel/`, `blueprint/` or other notes was edited.

Marks: **VERIFIED** = read in a source in this repository, computed, or compiled. **STANDARD** =
published, reference given. **AUDIT-READ** / **ASTRA-READ** = a model reported reading the page
(the repository's audit records), not read here. **UNVERIFIED** = theorem number from memory (no
network). **SPECULATIVE** = assessment.

## Summary

1. **Package I3 can be stated faithfully in Lean today (VERIFIED, compiled), contrary to
   wk-h §3.** wk-h said "ℓ-adic Tate modules: no" and concluded that I3 cannot be stated. That
   was true of Mathlib as a library, but the missing objects are small and can be *defined* on
   Mathlib's genuine scheme theory. Mathlib v4.35.0 has group objects in `Over (Spec K)`, the
   theorem that proper geometrically integral group schemes are commutative
   (`isCommMonObj_of_isProper_of_geometricallyIntegral`, Stacks 0BFD), the group structure on
   morphisms into a commutative group object (`Hom.commGroup`), `Field.absoluteGaloisGroup`,
   `ℤ_[ℓ]`, `ℚ_[ℓ]` and `Representation.IsSemisimpleRepresentation`. On top of these the
   draft defines, with every structural fact *proved*:
   - abelian varieties;
   - `Hom_K(A, B)` and the ring `End_K(A)`, and `End⁰`;
   - `A(K̄)` with its `G_K`-action (left action proved);
   - `T_ℓ(A)` as a `ℤ_ℓ`-module and `V_ℓ(A) = ℚ_ℓ ⊗ T_ℓ(A)`;
   - `ρ_ℓ : G_K → GL(V_ℓ A)` as a Mathlib `Representation`;
   - the map `ℤ_ℓ ⊗ Hom(A, B) → Hom(T_ℓ A, T_ℓ B)`;
   - base change.
2. **Seven leaves** (§3), bundled as `structure I3Leaves : Prop`:
   - Faltings' Satz 3 and Satz 4 / Korollar 1;
   - from Mumford: the rank of `T_ℓ`, §19 Thms 1, 3 and 4;
   - the QM dichotomy for A9.

   Each is a `def … : Prop` quantified over all (number) fields and all abelian varieties.
3. **Glue checked in Lean (VERIFIED; no `sorry`; axioms `propext`, `Classical.choice`,
   `Quot.sound`).**
   - `range_tateHomZl_subset`: the easy inclusion of Faltings' statement holds outright, so the
     leaf asserts exactly the published content (injectivity and the hard inclusion).
   - `exists_hom_ne_zero_of_equivariant`: the Faltings part of E1. From `FaltingsTate` and
     `TateModuleFree`, a nonzero `G_K`-equivariant `ℚ_ℓ`-linear map `V_ℓ A → V_ℓ B` gives a
     nonzero homomorphism `A → B`.
   - `finrank_equivEnd`: the Faltings part of C2. From `FaltingsTate`, `TateModuleFree` and
     `HomFreeFinite`, `dim_{ℚ_ℓ} End_{G_K}(V_ℓ A) = rank_ℤ End_K(A)`.

   These show that the leaves can actually be used through these definitions.
4. **Biggest obstacle (VERIFIED by grep):** Mathlib v4.35.0 cannot construct any *nonzero*
   abelian variety. There is no projective group scheme: Weierstrass curves exist only as point
   sets, and `GrpObj` occurs in `AlgebraicGeometry/` only in `Group/` and `Pullbacks`. The
   leaves are faithful statements about genuine objects, but to *apply* them to Glazer's `A`,
   `J₁(N)` and `A_f`, those varieties must be constructed, or supplied by other packages' leaves
   (I1 moduli, I4 modular Jacobians) as `AbVar` objects with stated properties. So the
   interface between I3 and I1/I4 is the type `PkgI3.AbVar`. Wherever the varieties are
   produced, the synthesis should require them to be produced in this type.

## 1. Where I3 is used (N5 = `diophantine_zq.tex`, read for this note, VERIFIED)

| Step | N5 lines | What the argument needs from I3 |
| --- | --- | --- |
| A9 | L564-575 | `End⁰(A_ℚ̄) ∈ {B, M₂(k)}`. N5 argues complex-analytically: polarizable tori are abelian varieties, analytic maps are algebraic (Milne's notes Thms 2.8-2.9, i.e. Mumford §§1-3 with GAGA), and the commutant of `J` in `B ⊗ B^op`. |
| C2 | L731-734 | "Faltings' semisimplicity and endomorphism theorems": `V_ℓ(A)|G_{L'}` is semisimple and `End_{G_{L'}}(V_ℓ A) = End_{L'}(A) ⊗ ℚ_ℓ = B ⊗ ℚ_ℓ`. After splitting `B` the commutant of `r_ℓ` is scalar, so `r_ℓ` is absolutely irreducible. |
| C9, C10 | L768-795; h-trust C9, C10 | Semisimplicity of `V₅(A_f)` over `G_ℚ` (Satz 3 for `A_f/ℚ`), for Brauer–Nesbitt. "The characteristic polynomial of an abelian-variety endomorphism on rational Tate modules is independent of the coefficient prime" (L786-787): Mumford §19 Thm 4, applied to an endomorphism of the reduction `Ā_v` over a finite field. |
| E1 | L861-867 | "Faltings' Hom theorem": a common constituent of `V_ℓ A` and `V_ℓ J` over `L'` gives a nonzero `L'`-homomorphism `A → J`. Then absolute simplicity and Poincaré reducibility give an isogeny `A × Z → J`. |
| A8 (I2 per wk-h, but a Mumford input) | L545-548 | `rank Hom(A, A') ≤ 4 dim A dim A'` (Mumford §19 Thm 3). |

## 2. The published statements

- **Faltings 1983.** G. Faltings, *Endlichkeitssätze für abelsche Varietäten über
  Zahlkörpern*, Invent. Math. 73 (1983), 349-366; erratum 75 (1984), 381 (bibliography N5
  L11084-11086, VERIFIED). §5:
  - **Satz 3.** For an abelian variety `A` over a number field `K`, the representation of
    `G_K` on `V_ℓ(A)` is semisimple.
  - **Satz 4.** `End_K(A) ⊗ ℤ_ℓ → End_{G_K}(T_ℓ A)` is an isomorphism.

  Both are printed on p. 360 (AUDIT-READ: `docs/theorem-application-audit/INVENTORY.md`
  A008, "page images checked" 2026-11-05). The erratum replaces the constant-height claim of
  Satz 2 by eventual stationarity and does not withdraw Satz 3 or Satz 4 (same record).
  - **Korollar 1.** `Hom_K(A, B) ⊗ ℤ_ℓ → Hom_{G_K}(T_ℓ A, T_ℓ B)` is an isomorphism, pp.
    360-361 (ASTRA-READ: `docs/reviews/height-replacement/descent/AUDIT.md`).

  The exact German wording is UNVERIFIED here. The content is STANDARD (also Cornell–Silverman
  (eds.), *Arithmetic Geometry* (1986), Ch. II, Faltings' paper in translation, Thms 3-4 and
  Cor. 1; UNVERIFIED locator).
- **Mumford 1970.** D. Mumford, *Abelian varieties*, Oxford University Press / TIFR (1970; 2nd
  ed. 1974). The ground field is algebraically closed throughout. All locators UNVERIFIED:
  - §19, Thm 1 (Poincaré complete reducibility) and its corollaries: `End⁰` is semisimple, and
    a division algebra when `A` is simple.
  - §19, Thm 3: `Hom(X, Y)` is free of rank `≤ 4 dim X dim Y`, and
    `Hom(X, Y) ⊗ ℤ_ℓ → Hom(T_ℓ X, T_ℓ Y)` is injective for `ℓ ≠ char k`.
  - §19, Thm 4: `P_φ ∈ ℤ[X]`, monic of degree `2g`, is the characteristic polynomial of
    `T_ℓ(φ)` for every `ℓ ≠ char k`.
  - §21: Albert's classification, with the restrictions in characteristic 0 (`[D:ℚ] ∣ 2g` for
    simple `A`).
  - §6, Application 2 and its corollary (§4 in some citations): `A[n] ≅ (ℤ/n)^{2g}` for
    `char k ∤ n`.
- **Over a general ground field** (needed because the leaves are over `L'`, `ℚ`, `𝔽_q`):
  J. S. Milne, *Abelian varieties*, in Cornell–Silverman (1986), §§8, 12 (Poincaré
  reducibility over any field, Prop. 12.1; injectivity and rank, Thm 12.5 and Cor. 12.?).
  UNVERIFIED locators. Alternatively, Mumford's statements over `k̄` imply those over `k` by
  base change (`Hom_k ⊆ Hom_{k̄}`, `ℤ_ℓ` flat over `ℤ`, and `T_ℓ(A) = T_ℓ(A_{k̄})`); see §5.
- **QM dichotomy.** For an abelian surface over an algebraically closed field of
  characteristic 0 with an embedding of a quaternion division algebra `B` into `End⁰`,
  `End⁰ ≅ B` or `M₂(k)` with `k` imaginary quadratic. It is classical in the QM literature
  (e.g. Rotger 2003/2004, Dieulefait–Rotger 2004; UNVERIFIED, no locator read). It follows from
  Mumford §19 Thm 1 and Cor. 2, `[D:ℚ] ∣ 2g` in characteristic 0 (§21), and `End⁰(E) ∈ {ℚ,
  imaginary quadratic}` for elliptic curves in characteristic 0 (Silverman, AEC III.9.4,
  UNVERIFIED). Argument (VERIFIED as an argument):
  - If `A` is simple, `D = End⁰(A)` is a division algebra containing `B`, with `[D:ℚ] ∣ 4`,
    so `D = B`.
  - Otherwise `A ~ E₁ × E₂`. If `E₁ ≁ E₂` then `End⁰` is commutative and cannot contain `B`.
    If `E₁ ~ E₂ = E` then `End⁰ = M₂(End⁰ E)`, and `M₂(ℚ)` cannot contain the division algebra
    `B` (same dimension 4), so `End⁰ E = k` is imaginary quadratic.

## 3. The leaves (all in `scratch/pkg-I3/I3.lean` §3, compiled, VERIFIED)

Common definitions (§2 of the file; namespace `PkgI3`):

- `AbVar K`: a structure with `X : Over (Spec K)`, `[GrpObj X]`, `[IsProper X.hom]`,
  `[Smooth X.hom]`, `[GeometricallyIntegral X.hom]`. This is the standard definition (Milne
  1986 §1). Commutativity is derived from Mathlib's theorem; it is not assumed.
- `Hom A B`: the additive group of `K`-morphisms `A → B` that are group homomorphisms
  (`IsMonHom`), with the pointwise group law of `Hom.commGroup`. `End A` carries a `Ring`
  instance (product = composition; axioms proved), and `End0 A := ℚ ⊗[ℤ] End A`.
- `A.Pt L`: the `K`-morphisms `Spec L → A`. `galAct σ` is precomposition with `Spec σ`; this
  is σ applied to coordinates, and `galHom_mul` proves that it is a left action.
- `Tate.T ℓ M`: the sequences `(xₙ)` in `M` with `x₀ = 0` and `ℓ xₙ₊₁ = xₙ`, i.e.
  `lim M[ℓⁿ]`. The `ℤ_ℓ`-action is `(a·x)ₙ = (a mod ℓⁿ)·xₙ`, and all module axioms are proved.
  `A.T ℓ = Tate.T ℓ A(K̄)` with `K̄ = AlgebraicClosure K`, and `A.V ℓ = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ A`.
- `galRep ℓ A : Representation ℚ_[ℓ] (Field.absoluteGaloisGroup K) (A.V ℓ)` is the base change
  of the action on `T_ℓ`.
- `tateHomZl ℓ A B : ℤ_ℓ ⊗[ℤ] Hom A B → (T_ℓ A →ₗ[ℤ_ℓ] T_ℓ B)`, `a ⊗ f ↦ a·T_ℓ(f)`.
- `IsGalEquivariant`, `IsIsogenyMor` (finite and surjective), `dim` (Krull dimension of the
  underlying space), `baseChange`, and `zero` (`Spec K`, a sanity inhabitant; it needed a new
  instance, `GeometricallyIntegral (𝟙 (Spec K))`).

| Leaf (Lean name) | Statement | Source | Relation to the source | Used at |
| --- | --- | --- | --- | --- |
| `FaltingsSemisimple` | `∀ K` number field, `∀ A ℓ`, `(A.galRep ℓ).IsSemisimpleRepresentation` | Faltings 1983 Satz 3 | the published statement | C2; C9-C10 (`A_f/ℚ`); E1 (`V(J)`, to turn a common constituent into a Hom) |
| `FaltingsTate` | `∀ K A B ℓ`, `tateHomZl ℓ A B` injective and `range = {φ | IsGalEquivariant φ}` | Faltings 1983 Kor. 1 (Satz 4 = case `A = B`) | the published statement (integral form) | C2, E1 |
| `TateModuleFree` | `∀ k A ℓ, (ℓ:k) ≠ 0 →` `T_ℓ A` free and finite over `ℤ_ℓ` of rank `2·dim A` | Mumford §6 (`A[n] ≅ (ℤ/n)^{2g}`) | consequence (pass to the limit) | glue for C2 and E1 |
| `HomFreeFinite` | `Hom A B` free and finite over `ℤ`, `rank ≤ 4 dim A dim B`, and `tateHomZl` injective for `ℓ ≠ char k` | Mumford §19 Thm 3 | the statement (over `k`: via base change, or Milne 1986 §12) | A8; glue for C2 |
| `CharPolyIndepOfEll` | `∀ φ : End A, ∃ P ∈ ℤ[X]` monic such that, for every prime `ℓ ≠ char k` and every finite basis of `V_ℓ A`, `charpoly(V_ℓ φ) = P` | Mumford §19 Thm 4 | consequence (drops `deg P = 2g` and `P(n) = deg(n − φ)`) | C10 (over the residue field `𝔽_q`) |
| `PoincareReducibility` | `char k = 0`; if every nonzero `f ∈ End A` is finite and surjective, then every nonzero `f : A → J` has `Z`, `g : Z → J` with `(f, g) : A × Z → J` finite and surjective | Mumford §19 Thm 1 (+ images of homomorphisms, §§4-8) | consequence | E1 |
| `QMDichotomy` | `k` algebraically closed of characteristic 0, `dim A = 2`, `(a,b)_ℚ` division and `(a,b)_ℚ →ₐ End⁰ A` ⇒ `End⁰ A ≃ₐ (a,b)_ℚ` or `≃ₐ M₂(ℚ(√d))` with `d < 0` | QM literature (UNVERIFIED); derivation in §2 | consequence of several theorems; **needs a single refereed locator** to count as a leaf, or else it should be split | A9 (its output feeds A10) |

Faithfulness notes (SPECULATIVE where it is a judgment, otherwise VERIFIED by reading the Lean):

- **No abstract structure is introduced.** Every field of `AbVar` is a Mathlib predicate on a
  Mathlib scheme. `T_ℓ`, `V_ℓ`, `ρ_ℓ` and `Hom` are *defined*, not posited, and their
  algebraic laws are proved. So none of the leaves can be satisfied by a model that has nothing
  to do with abelian varieties. This is the decisive difference from wk-h's Tier 2 signature
  (wk-h §4.3).
- **The Galois-equivariant maps are `ℤ_ℓ`-linear by definition.** Additive equivariant maps
  `T_ℓ A → T_ℓ B` would give the same set (they are `ℓ`-adically continuous, hence
  `ℤ_ℓ`-linear), but the leaf uses `→ₗ[ℤ_ℓ]`, as Faltings does.
- **Galois acts through `AlgebraicClosure K`.** In characteristic 0 this is the separable
  closure. In characteristic `p` with `ℓ ≠ p`, `A[ℓⁿ](K̄) = A[ℓⁿ](K^sep)`, so `TateModuleFree`
  and `CharPolyIndepOfEll` are unaffected.
- **Universe.** The leaves quantify over `K : Type` (universe 0). That suffices for every
  field in the proof.
- **No leaf is stronger than its source.** `CharPolyIndepOfEll` quantifies over all finite
  bases, so it needs no `Module.Finite` instance; the finiteness is `TateModuleFree`.
  `PoincareReducibility` is restricted to characteristic 0 to stay safely inside the published
  range.

## 4. What exists in Lean libraries (VERIFIED for Mathlib by grep; others from prereq-survey)

| Object | Mathlib v4.35.0 | Elsewhere (prereq-survey) |
| --- | --- | --- |
| group schemes over a field; commutativity of proper geometrically integral ones | yes (`AlgebraicGeometry/Group/Abelian.lean`) | Tau Ceti `AbelianVariety` (definitions, `Hom`, `IsIsogeny`, 4-declaration `Hom.Rigidity`) |
| group of points `X ⟶ G` | yes (`Hom.commGroup`, `IsMonHom.monoidHom`) | — |
| ℓ-adic Tate module of an abelian variety | **no** (built here, `Tate.T`) | Anthropic FLT: Jacobian Tate modules (rank `2g`); Tau Ceti: elliptic curves |
| Galois representation on `V_ℓ`; semisimplicity | `Representation`, `IsSemisimpleRepresentation` yes; `V_ℓ` built here | — |
| any nonzero abelian variety (elliptic curve as a scheme, Jacobian) | **no** | Anthropic FLT: Jacobians and QM abelian surfaces (special case); Tau Ceti: none as schemes with `Hom` content |
| Faltings 1983, Mumford §19 | no | no (ATLAS "Faltings" is Mordell, `theorem_wanted`) |

Recommendation (SPECULATIVE): if the crowdsourced formalization uses Tau Ceti's
`AbelianVariety`, the leaves should be restated over it, keeping `T_ℓ`, `ρ_ℓ` and `tateHomZl`
as above. The definitions here are deliberately minimal, so the translation is direct.

## 5. Glue (the project's work), by step

Proved in Lean (`I3.lean` §4, VERIFIED):

- `range_tateHomZl_subset` (image ⊆ equivariant maps).
- `exists_hom_ne_zero_of_equivariant` (E1, the Faltings part). It clears denominators with
  Mathlib's `Module.FinitePresentation.exists_lift_of_isLocalizedModule`; `ℤ_ℓ` is Noetherian
  and `T_ℓ A` is finite by `TateModuleFree`.

- `finrank_equivEnd` (C2): `dim_{ℚ_ℓ} End_{G_K}(V_ℓ A) = rank_ℤ End_K(A)`, from
  `FaltingsTate`, `TateModuleFree` and `HomFreeFinite`. `End_G(T_ℓ A) ≅ ℤ_ℓ ⊗ End A` by
  Faltings, then `End_G(V_ℓ A)` is shown to be the localization of `End_G(T_ℓ A)`
  (`IsLocalizedModule`), and Mathlib's `IsLocalizedModule.finrank_eq`,
  `IsLocalization.finrank_eq` and `Module.finrank_baseChange` finish.

Prose only (to be written):

- **C2, the commutant argument.** After extension of scalars to `E ⊇ ℚ_ℓ` splitting `B`, write
  `V_ℓ A ⊗ E = r ⊕ r`. Then `End_G(r ⊕ r) = M₂(End_G r)` has dimension 4, so `End_G r = E`.
  A semisimple representation with scalar endomorphisms is absolutely irreducible. Two inputs
  are linear algebra:
  - invariants commute with extension of the coefficient field (kernel of a finite family of
    commutator maps);
  - semisimplicity survives scalar extension in characteristic 0 (separability of the
    semisimple algebra generated by the image).

  Neither is a literature leaf. Input from other steps: `End⁰_{L'}(A) = B` (A9 + A10 + "`L'`
  defines every geometric endomorphism", A8/B3), as an isomorphism `End0 (A.baseChange L') ≃ₐ
  B`.
- **E1, the rest.**
  - From "common constituent over `E`" to a nonzero `ℚ_ℓ`-linear equivariant map: semisimplicity
    of `V(J)` (`FaltingsSemisimple`, applied to `J₁(N)/L'`) makes the constituent a summand;
    then invariants commute with coefficient extension.
  - Then `exists_hom_ne_zero_of_equivariant`.
  - Then `PoincareReducibility`, with `EndDivision A` obtained from `End⁰(A_{ℚ̄}) = B` (a
    division algebra), using faithfulness of base change on `Hom` and descent of finiteness and
    surjectivity along `L'/ℚ̄`.
- **C10.**
  - `CharPolyIndepOfEll` for `Frob ∘ μ̄_σ` on `Ā_v/𝔽_q`.
  - The specialization `V_ℓ(A) ≅ V_ℓ(Ā_v)` at good reduction, and the reduction of `μ_σ`
    through the Néron property (I2).
  - Chebotarev and Brauer–Nesbitt (I6; Chebotarev is proved in Tau Ceti).
  - `FaltingsSemisimple` for `A_f/ℚ`.
- **Base change of `T_ℓ`** (used by every application over `L' ⊋ K`). A `K`-embedding
  `AlgebraicClosure K → AlgebraicClosure L` identifies `A(K̄)` with `A_L(L̄)`, by the universal
  property of the pullback, compatibly with `G_L → G_K` (Mathlib has
  `Field.absoluteGaloisGroup.map`). Technical but finite.
- **Mumford over `k` from Mumford over `k̄`**, if Milne 1986 is not used: the same base-change
  identification, `ℤ_ℓ` flat over `ℤ`, and faithfulness of base change on `Hom`.

## 6. "Jacobians of explicit curves" instead of general abelian varieties? (SPECULATIVE)

No. Of the four varieties I3 is applied to, only the QM surface `A` is (for `u ∉ 𝒞`) the
Jacobian of an explicit genus-2 curve (Baba–Granath; I1). `J₁(N)` and `A_f` have no usable
equations, and the theorem is applied to `A × J₁(N)` and `A_f`.

A Jacobian-only formulation would also need more infrastructure, not less: the Picard scheme or
Mumford coordinates, and the group law. The only nonzero varieties for which Mathlib has a
group law are elliptic curves (`W.Point`, point sets), where Faltings' isogeny theorem could be
stated cheaply, but the proof uses no elliptic curve except in the CM branch, which does not
touch I3.

The general `AbVar` statement over Mathlib's group schemes is the most concrete faithful form.

## 7. Obstacles and open items

1. **No nonzero `AbVar` is constructible in Mathlib (VERIFIED).** Applying the leaves to `A`,
   `J₁(N)` and `A_f` needs these objects. Either they are built (large: projective group
   schemes, modular curves), or the leaves of I1/I4 supply them as `AbVar` with properties
   (the moduli interpretation gives `A/L'` with `B ↪ End⁰`; Shimura's construction gives
   `A_f/ℚ` as a quotient of `J₁(N)`). In the latter case the faithfulness of those leaves
   carries the weight, and I3's leaves remain faithful.
2. **QMDichotomy needs one refereed locator** (Rotger, or Shimura 1963/1967, or Albert's
   classification as printed in Mumford §21), or it should be split into Mumford §19 + §21 +
   Silverman III.9.4 with the isogeny-category glue (heavy: kernels, images and products of
   abelian varieties, none in Mathlib).
3. **Locators.**
   - Faltings Satz 3/4: AUDIT-READ, p. 360; Kor. 1: ASTRA-READ, pp. 360-361.
   - The Mumford and Milne numbers: UNVERIFIED.
   - The 1984 erratum's scope: AUDIT-READ.
4. **An alternative route for Satz 3/4 exists but is not statable** (h-leaves §2.3): Claims 2-3
   from Gaudron–Rémond 2014 Thm 1.4 with Tate's argument. GR14 is an I5 statement, about
   Faltings heights, which are not definable in Mathlib. So it does not reduce the I3 leaves to
   a statable one; it would only merge I3 into I5.
