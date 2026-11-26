# Adversarial AI readings: `colmez1992DeRhamAbVar` and `fontaine1982HTAbVar` (2026-11-26)

**Result.** Both rows match their printed sources, and every lens passed both. R1
(`DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar`) is Colmez's Théorème 5.2 (i)-(ii) at the print's own generality,
weakened only: `H¹_dR(X)` becomes an existential type, and three printed clauses are dropped. R2
(`DeRhamScholze.TatePrints.Fontaine1982HTAbVar`) is a direct instance of Fontaine's Théorème 2, at `K` a finite
extension of `ℚ_p`, in dimension form. No reader found a clause stronger than the print, a missing hypothesis, a sign
or variance error, or a definition that differs from the printed notion beyond the standard identifications recorded
below.

No person has read these pages. Under the maintainer's ruling of 2026-11-26 (STATEMENT-CHECKS.md, "Adversarial AI
readings"), with no human reader available, this adversarial AI reading stands in for the human reading. The
evidence stays AI-READ.

The rows were read at `69b78009a` (#213). Their statements are unchanged on main at `8a1c23f81`. The only later edit
to `TatePrints/Rows.lean` is a docstring locator, which two readers raised: Colmez §2 starts on p. 632, not p. 631.

## 1. Method

Three independent AI readings of both rows. Each worked from page images rendered from the PDFs at 150 dpi, not from
a text layer (Fontaine's scan has none). Each gives verbatim quotes and printed page numbers. The three readers ran on
three different model families (Claude, GPT, Gemini), so that they would not share blind spots. Each wrote its
report independently.

| Lens | Task |
| --- | --- |
| Fidelity | Unfold the Lean statement and every definition it uses into atomic clauses, and map each clause to the printed text: MATCH, MATCH AFTER A PROVED IDENTIFICATION (naming the Lean theorem), DIRECT INSTANCE, WEAKER or STRONGER THAN THE PRINT, MISMATCH. |
| Skeptic | Try to break the match: hidden standing hypotheses, conventions (Galois action on points, cyclotomic sign, twists), whether each Lean definition means the printed notion, vacuity, quantifiers, and what the relied-on identifications actually state. |
| Red team | Read both sources cold, before any Lean, and state what they assert in plain words. Then list every difference with the Lean and classify it. |

Sources (legal copies; SHA-256):

| Source | Copy | SHA-256 |
| --- | --- | --- |
| Colmez, *Périodes p-adiques des variétés abéliennes*, Math. Ann. 292 (1992), 629-644 | Springer journal PDF hosted on the author's page | `8e6bbf9904f4afb21ab5b7ba28f7a914362c491a0984f389802798532e33f2e3` |
| the same article, GDZ (PPN235181684_0292, LOG_0042) | downloaded for its hash only, not read | `f64fbacd511b3458f2be96485686b75181e9e6e12395e06526d57ba5782fb978` |
| Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur les corps locaux*, Invent. Math. 65 (1982), 379-409 | GDZ scan PPN356556735_0065, LOG_0028 | `70da79c47194065c92af5c1283e32a91fedf44146083325988998dc52de532af` |

Pages read: Colmez pp. 629, 632, 638-640 by every lens; the red team read all 16 pages (pp. 629-644), the fidelity
lens also pp. 631, 633, 637, and the skeptic also pp. 634, 642-643. Fontaine pp. 379, 381, 387-388 by every lens. The fidelity lens also
read pp. 380 and 389. The skeptic read §§0-3 through p. 394. The red team read pp. 379-397 and the bibliography.

Both journals are refereed (Colmez p. 629: "Reçu le 8 février 1991; version révisée reçue le 8 novembre 1991";
Fontaine p. 409: "Received December 19, 1980").

The shared Lean dictionary was checked by every lens. `AbVar F` is a group object over `Spec F` that is proper,
smooth and geometrically integral (commutative by a theorem). `A.dim` is the Krull dimension. `A.T p` is the inverse
limit of the `p^n`-torsion of the `F̄`-points, and `A.V p = ℚ_p ⊗ A.T p`. `galRep` applies `σ` to coordinates: a
left action, `(στ)·P = σ·(τ·P)`. `G_F` acts on `ℂ_p` and `B_dR` through `gfToGqp`, conjugation across the
isomorphism `ℚ̄_p ≅ F̄`. The proved identifications here are `G9.embF_gfToGqp`, `G9.embF_bijective` and
`range_gfToGqp_eq`; the last has no normality hypothesis on `F/ℚ_p`. `F' = fieldF p F ⊆ ℚ̄_p` is the image of `F`
under the same isomorphism. `BdR p` is Mathlib's `BDeRham`: the fraction field of the complete discrete valuation
ring `BDeRhamPlus` (`isFractionRing_BDeRham`). `filB p 0` is the image of `BDeRhamPlus`
(`DeRhamScholze.HT.mem_filB_zero`).

## 2. R1 `colmez1992DeRhamAbVar` (Colmez 1992, Théorème 5.2)

| Lens | Verdict |
| --- | --- |
| Fidelity | PASS: every kept clause matches the print, matches it after a proved identification, or is weaker than it and implied by it; nothing stronger. |
| Skeptic | PASS: a weakening of 5.2 (i)-(ii); no mathematical blocker. |
| Red team | PASS: every clause implied by 5.2 (i)-(ii); no missing hypothesis, no added strength, no sign or variance error, no unbridged definition. |

The print, p. 639:

> Théorème 5.2. (i) Si F_ω est une des primitives de ω définie à la proposition 4.1, alors la suite
> pⁿ(F_ω(a_n) − F_ω(a_n⊕û_n)) tend vers une limite dans B⁺_DR qui ne dépend que de u et de la classe de ω dans
> H¹_DR(X).
> (ii) L'application périodes p-adique (ω,u) → ∫_u ω de H¹_DR(X) × T_p(X) dans B⁺_DR ainsi définie est
> bilinéaire, commute à l'action de Galois [i.e. g(∫_u ω) = ∫_{g(u)} ω si g ∈ Gal(K̄/K)], respecte les
> filtrations (i.e. ∫_u ω ∈ Fil¹(B⁺_DR) si ω ∈ H⁰(X, Ω¹_X)) et est non-dégénérée quand on étend les scalaires à
> B_DR.

The clauses, as the readers mapped them:

* **Prime and base field.** p. 632: "Soient p un nombre premier, Q̄_p une clôture algébrique de Q_p, … C_p le
  complété p-adique de Q̄_p"; p. 629: "soit X une variété abélienne définie sur une extension finie K de Q_p". The
  Lean takes every prime `p` and every finite `F/ℚ_p`, carried onto `F' ⊆ ℚ̄_p`: MATCH after the proved
  identifications above.
* **Abelian variety and model.** p. 638: "Dans la suite de cette section, X sera une variété abélienne, 𝒳 un modèle
  propre de X sur O_K." The Lean has no model parameter. A proper model always exists (the schematic closure of a
  projective embedding; Fontaine prints this construction on pp. 388-389), and the proof shows that the pairing does
  not depend on the model (p. 640: "L'indépendance par rapport à 𝒳 et la fonctorialité se démontrent …"). No
  reduction hypothesis: the semistable model in the Remark after 5.2 and the good reduction of §7 are not part of
  5.2. MATCH.
* **The pairing.** The Lean has `∃ H, ∃ P : H → (V_p(A) →ₗ[ℚ_p] B_dR)`, with the witness `H = H¹_DR(X)` and `P ω`
  the `ℚ_p`-linear extension of `u ↦ ∫_u ω` from `T_p` to `V_p = ℚ_p ⊗ T_p`. This extension exists and is unique
  because `p` is invertible in `B⁺_DR`. WEAKER THAN THE PRINT.
* **Values in `B⁺_DR`.** 5.2 (i): "tend vers une limite dans B⁺_DR". This is the Lean's `P ω u ∈ filB p 0`, and the
  extension to `V_p` stays in `B⁺_DR`, a `ℚ_p`-subspace. MATCH.
* **Galois compatibility.** 5.2 (ii): "g(∫_u ω) = ∫_{g(u)} ω si g ∈ Gal(K̄/K)". The Lean has
  `P ω (ρ(σ) u) = bdrAct (gfToGqp σ) (P ω u)`: `ρ(σ)u` is `g(u)`, and `bdrAct (gfToGqp σ)` is `g` acting on `B_dR`
  through the same embedding. MATCH after the proved identification `embF_gfToGqp`.
* **Non-degeneracy.** 5.2 (ii): "est non-dégénérée quand on étend les scalaires à B_DR". The Lean says that an `x` of
  `B_dR ⊗_{ℚ_p} V_p` killed by every `(P ω).liftBaseChange B_dR` is `0`. That is the `T_p` side of the printed
  non-degeneracy: the `ω ⊗ 1` span `H¹_DR ⊗ B_DR`, and `B_dR ⊗_{ℚ_p} V_p = B_dR ⊗_{ℤ_p} T_p`. WEAKER THAN THE PRINT.
  Not vacuous: for `dim A > 0` an empty `H` or a zero family makes this clause false. At `dim A = 0`, `V_p = 0` and
  the row holds trivially, as the print does.
* **Period ring.** p. 632: "B⁺_DR = lim← W(R)[p⁻¹]/(Ker θ)ⁿ … Notons B_DR le corps des fractions de B⁺_DR". Colmez's
  `R` (sequences `(x^{(n)})` in `O_{C_p}` with `(x^{(n+1)})^p = x^{(n)}`) is canonically Mathlib's `PreTilt`
  (`PreTilt.untilt`), as in the readings of `colmezThm01`. MATCH.
* **Dropped:** linearity in `ω`, independence of the primitive `F_ω`, the `Fil¹` clause of (ii), (iii) (the p-adic
  Riemann relation), and functoriality. All WEAKER THAN THE PRINT. Part (iii) is used in the paper to prove the
  non-degeneracy (p. 640); it is not a hypothesis of (ii).

**Recorded non-blocking points**, with the reading the row follows:

1. **Points of `T_p`.** The row builds `T_p(A)` from the `F̄`-points. Colmez's elements of `T_p(X)` have
   `u_n ∈ 𝒳(O_{C_p}) = X(C_p)` (pp. 638-639: "Par construction, 𝒳(O_{C_p}) s'identifie à X(C_p)"; "Soit
   u=(…,u_n,…), où u_n ∈ 𝒳(O_{C_p}), un élément du module de Tate T_p(X) de X"). The two are isomorphic on torsion,
   `G_F`-equivariantly through `F̄ ≅ ℚ̄_p ⊂ C_p`: `X[pⁿ]` is finite over `F`, so its `C_p`-points are algebraic over
   `F` and lie in `F̄`. Both groups have order `p^{2ng}`, and the tree proves this count over any algebraically
   closed field (`ZInQ.Contrib.CloudB3W16Torsion.card_torsion`). No Lean theorem states the isomorphism itself, so
   it is a reading step. Fontaine's definition of the same module (p. 388) uses the `K̄`-points, and Colmez himself
   writes `u_n ∈ 𝒳(O_{K̄})` for these Tate points in §6 (p. 642). The row follows the standard reading:
   "module de Tate T_p(X)" is the usual Tate module.
2. **`ℤ_p`-linearity in `u`.** The `ℚ_p`-linear extension to `V_p` needs `ℤ_p`-linearity, not only additivity. The
   row reads "bilinéaire" on `H¹_DR(X) × T_p(X)` as `K`-linear in `ω` and `ℤ_p`-linear in `u`. This also follows
   from additivity and the bound in the proof (p. 640: "La linéarité par rapport à u se démontre en utilisant le
   lemme 5.3(i)", with the terms in `π^{en−r−r(e)} A^k_{cris,K}`), which makes `u ↦ ∫_u ω` p-adically continuous.
3. **Dropped clauses.** Bilinearity in `ω`, `Fil¹` and (iii), as listed above. The row keeps only what
   `vpDual_of_colmezFontaine` reads.

The sign convention of the periods (p. 634: "Le signe définissant les périodes est l'opposé de celui auquel on
penserait naturellement") does not enter any kept clause. No printed slip bearing on the kept clauses was found on
pp. 638-641.

## 3. R2 `fontaine1982HTAbVar` (Fontaine 1982, Théorème 2)

| Lens | Verdict |
| --- | --- |
| Fidelity | PASS (direct instance): every kept clause matches the print or matches it after a proved identification; nothing stronger. |
| Skeptic | PASS: the finite-`ℚ_p` instance of the two counts printed in the proof of Théorème 2; no mathematical blocker. |
| Red team | PASS: a direct instance and weakening of Théorème 2 and the count on p. 388, with the cyclotomic sign and the Galois action matching. |

The print, p. 388:

> Théorème 2 (Tate, Raynaud). Soit X une variété abélienne sur K. Il existe des applications K-linéaires
> bijectives, canoniques et fonctorielles en X
> ρ¹_X: H¹(X, O_X) → Hom_{Z_p[G]}(T_p(X), C),
> ρ⁰_X: H⁰(X, Ω_X) → Hom_{Z_p[G]}(T_p(X), C(1)).

and, in the deduction of Théorème 2 from Théorème 2' on the same page:

> Soit d la dimension de X. Le théorème 2' implique que dim_K Hom_{Z_p[G]}(T_p(X), C(1)) ≥ d, avec égalité si et
> seulement si ρ⁰_X est un isomorphisme. […] Comme la somme de la dimension de Hom_{Z_p[G]}(T_p(X), C(1)) et de
> celle de Hom_{Z_p[G]}(T_p(X), C) est inférieure ou égale au rang du Z_p-module libre T_p(X) ([7], prop. 4), qui
> est 2d, chacune de ces dimensions est égale à d et ρ⁰_X est un isomorphisme.

The clauses:

* **Base field.** 0.1, p. 379: "Soit K un corps local de caractéristique 0, à corps résiduel parfait de
  caractéristique p≠0, soit K̄ une clôture algébrique de K et soit C le complété de K̄. L'action de G=Gal(K̄/K) se
  prolonge par continuité à C"; §1.1, p. 381: "K est un corps local, i.e. un corps complet pour une valuation
  discrète, à corps résiduel parfait k de caractéristique p≠0"; §3, p. 387: "on suppose en outre K de
  caractéristique 0". A finite `F/ℚ_p` is such a field, so DIRECT INSTANCE. The auxiliary data of §1.1 (`K₀`, `E`)
  exist in characteristic 0: the maximal unramified subextension and `E = ℚ_p`. No reduction hypothesis.
* **Abelian variety and dimension.** "Soit X une variété abélienne sur K"; "Soit d la dimension de X" (p. 388). The
  Lean has `A : AbVar F` and `A.dim = g`. `A.dim` is finite for every `A` (`HodgeSplit.dim_finite_I4`), so the
  premise excludes nothing. MATCH.
* **Tate module.** 3.1, p. 388: "T_p(X) = Hom_Z(Q_p/Z_p, X(K̄))". Evaluation at `p⁻ⁿ` identifies it with the Lean's
  sequences, `G_F`-equivariantly; no `C`-points are involved. MATCH.
* **The spaces.** `Hom_{Z_p[G]}(T_p(X), C(i))` for `i = 1, 0`, with `M(i) = M ⊗_{Z_p} T^{⊗i}` and
  `T = lim← μ_{pⁿ}(K̄)` (0.1, p. 379), and the cyclotomic character from §1.7, p. 383 ("Le caractère χ_Γ est le
  caractère cyclotomique χ"). The Lean has `htF (A.galRep p) i`: the `ℚ_p`-linear maps `φ : V_p → ℂ_p` with
  `φ(ρ(σ)v) = χ(σ)^i · σ(φ v)`, as an `F'`-space. A `ℤ_p`-linear map from `T_p` to the `ℚ_p`-space `C(i)` extends
  uniquely to `V_p = ℚ_p ⊗ T_p`. A generator of `T` identifies `C(1)` with `C`, `σ` acting by `χ(σ)σ`; the sign was
  checked against `cyclotomicCharacter.spec` and `cycPow_gfToGqp_one`. The `K`-structure is `F'` acting through
  `iotaCp`, from the same embedding as the Galois action (`algebraMap_algCp`, `cpAct_iotaCp_gf`). MATCH after the
  proved identifications.
* **The counts.** The Lean has `finrank_{F'} (htF … 1) = g` and `finrank_{F'} (htF … 0) = g`, printed in the proof
  on p. 388: "chacune de ces dimensions est égale à d". MATCH. For `g > 0`, `finrank = g` also gives finite
  dimension; at `g = 0` the Lean's `finrank = 0` is, if anything, weaker than the print.
* **Dropped:** the maps `ρ¹_X`, `ρ⁰_X`, their bijectivity onto `H¹(X, O_X)` and `H⁰(X, Ω_X)`, canonicity and
  functoriality. WEAKER THAN THE PRINT.

**Recorded non-blocking points**, with the reading the row follows:

1. **"= g" is in the proof.** The equality of the dimensions with `d` is printed in the proof on p. 388 ("chacune de
   ces dimensions est égale à d", in the deduction of Théorème 2 from Théorème 2'), not in the boxed statement. It
   also follows from the boxed statement with `dim_K H⁰(X, Ω_X) = dim_K H¹(X, O_X) = d`. The row cites "Théorème 2
   and its proof, p. 388".
2. **The maps are dropped.** `ρ¹_X`, `ρ⁰_X`, canonicity and functoriality are not part of the row. Only the two
   dimensions are kept, which is what `vpDual_of_colmezFontaine` reads.
3. **Locator.** The Fontaine locator is p. 388, for Théorème 2 and its proof. Fontaine attributes the theorem to
   Tate and Raynaud and gives a new proof of it (p. 380, 0.4; 3.2, p. 388). The citation of Fontaine as the print
   is consistent with the page.

Fontaine's dual variety in the proof does not replace the input `X`: both spaces are Hom out of the same `T_p(X)`.
The printed `V_p(X) = Hom_Z(Z[p⁻¹], X(K̄))` of 3.4 is a larger group than `ℚ_p ⊗ T_p(X)`, which is the one the row
uses (3.8, p. 393, separates them). Théorème 2 is stated with `T_p(X)`. A typo on p. 379 ("d'ordre divisible par
pⁿ" for the `pⁿ`-th roots of unity) is unambiguous from the notation `μ_{pⁿ}` and from p. 383.

## 4. What the readings do not establish

* **The evidence stays AI-READ.** No person has read these pages, and OPEN.md's count of human readings does not
  change.
* **The `C_p`-points step of R1** is argued (finite torsion schemes, the torsion count `card_torsion`) and not
  stated as a Lean theorem.
* **Scope.** R1 is Colmez's theorem at its own generality, minus dropped clauses. R2 is Fontaine's theorem only for
  `K` finite over `ℚ_p` (Fontaine allows any complete discretely valued `K` of characteristic 0 with perfect residue
  field), and only in dimension form.
* **Not read:** the steps of Colmez's proof (Proposition 4.1, Lemma 5.3, the argument from Fontaine he cites), and
  §§4-5 of Fontaine and his reference [7], prop. 4 (the rank bound the proof cites).

## 5. Effect on the board

The two rows replace the added rows `scholzeH1AbVar` and `t10TateDuality` in the bundle `OpenAddedLeaves30`
(`ZInQKernel/OneProof/H/TailZ106.lean`). `vpDual_of_colmezFontaine` derives the merged field
`VpDualDeRhamAbVar` from them in Lean. Both rows are rated LEAF (strict and strictest), with flags recording the
reading, the instance and the points above. The count of open statements stays at 22. The strict count of the H part
goes from 6/13 to 8/11, and from 6/16 to 8/14 with the three root hypotheses.
