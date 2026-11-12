# hdec-elementary: Theorem 4.1 (H) decomposed into elementary leaves and Lean glue

Status: research note (task hdec-elementary, 2026-11-11). Worktree branch `wip/hdec-elementary`
(from `origin/wip/prereq-survey`). Lean draft: `scratch/hdec-elementary/Leaves.lean` (compiles;
one `sorry`). Log, scripts and outputs: `scratch/hdec-elementary/`. No file under `ZInQKernel/`,
`blueprint/` or another note was edited.

Sources read for this note: the frozen manuscript `diophantine_zq.tex` ("N5", lines L377-964);
`docs/research/h-trust.md` (steps A1-F4), `wk-h.md`, `rv-lit.md` §§4-5, `prereq-survey.md`,
`rv-h-cm.md` §7.2, `rv-up.md` §3, `h-b1.md` (summary); the Lean files
`ZInQKernel/Hypotheses/{Height,HeightMin,JHeight}.lean`; Mathlib's `NumberTheory/Height/`.
There is no network: every published locator below that h-trust does not already mark
ASTRA-READ or VERIFIED is **UNVERIFIED** (from memory), and the place to check it is named.

Marks: **VERIFIED** (read in a repository source, computed by a saved script, or compiled);
**STANDARD** (a published theorem; locator as marked); **SPECULATIVE** (an assessment or an
unreviewed new argument). **NEW** marks an argument that appears first in this note: it has had
no review of any kind.

## 1. Verdict

1. **The decomposition.** H (`ZInQ.SixContactMin`) follows from **12 research-level leaves**
   (L1-L12, citing about 20 publications), **5 groups of textbook foundations** (F-a to F-e,
   mostly formalized already in Tau Ceti or Axiom's Stacks), and **23 glue steps** (G1-G23). The
   glue contains every argument of Glazer's (the scalar descent and the uniform conductor
   bound), the repository's replacements (Lemma PR, NoCM), and the bookkeeping. The leaves are:

   | # | Leaf | Main reference |
   | --- | --- | --- |
   | L1 | Canonical model of the level-3 discriminant-6 Shimura curve = fine moduli scheme over `ℚ` | Shimura 1967; Deligne 1971 Thm 4.21; Kottwitz 1992 |
   | L2 | Branch data of `Y₃ → P¹_j` and the Igusa vector of the QM locus | Baba–Granath 2008 Thm 2.1; Lin–Yang 2020 Ex. 30, eqs. (13)-(14) |
   | L3 | Shimura reciprocity at the CM points of `X₆` | Shimura 1967; González–Rotger 2006 Thm 5.12, Prop. 5.6 |
   | L4 | Grothendieck's ℓ-adic monodromy theorem (quasi-unipotence on inertia) | SGA 7 I, Exp. I; Serre–Tate 1968, Appendix |
   | L5 | Faltings: semisimplicity and the Tate conjecture for endomorphisms | Faltings 1983, Satz 3, Satz 4 |
   | L6 | Abelian varieties of GL₂-type over `ℚ` are quotients of `J₁(N)` | Khare–Wintenberger 2009 + Ribet 1992/2004 |
   | L7 | A `ℚ`-simple quotient `B` of `J₁(N)` has conductor `M^{dim B}` and is a quotient of `J₁(M)` | Carayol 1986 Thm A; Shimura 1973; Atkin–Lehner–Li |
   | L8 | `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²` | Javanpeykar 2014 Thm 1.1.1 |
   | L9 | Explicit isogeny estimate | Gaudron–Rémond 2014 (Duke) Thm 1.4 |
   | L10 | Height variation under isogeny, additivity, base change | Faltings 1983 Lemma 5; Raynaud 1985 |
   | L11 | `h_F(A) ≥ −(3/2) dim A` | Bost 1996, as recorded in Gaudron–Rémond 2014 §9 |
   | L12 | Thomae height of a genus-2 curve against `h_F(Jac)` | Pazuki 2012 Cor. 1.3(2) with Thomae's formula |

2. **Two route changes make the definitions far cheaper (§2.2).**
   - **Route K for modularity.** N5's modularity block (C2-C10: Pan's Fontaine–Mazur theorem,
     Scholze's de Rham comparison, Berger, Fontaine's closure theorem, Hodge–Tate weights of
     eigenforms at every level, Deligne–Serre, Kronecker–Weber, Li/Shimura/Eichler–Shimura for
     `A_f`, and C10's compatible system) is replaced by L6 + L7 and two NEW glue lemmas (G14
     "GL₂", G16 "Ind"). This removes **all of p-adic Hodge theory and all Galois
     representations of modular forms** from the definitions. Glazer's descent and conductor
     bound are kept unchanged in substance. N5's own route (route P) remains available, at the
     cost of about eight more leaves and the largest definitions block (§2.3).
   - **Galois-theoretic reduction.** "Good reduction at `v`" is used only as "inertia at `v`
     acts trivially on `T_ℓ`". With L4 and the fact that `B` is ramified at 2 and 3, Lemma
     PR(ii) and N5's use of Raynaud's criterion become elementary (G5, G16). Néron models,
     SGA 7 IX 3.6, Raynaud's criterion and Néron–Ogg–Shafarevich leave the leaf list (Néron
     models survive only inside the definition of the Faltings height).
   - **Theta constants replaced by roots.** By Thomae's formula the ten even theta constants of
     `Jac(y² = a∏(x−rᵢ))` have fourth powers proportional to `T_S = Δ(S)Δ(Sᶜ)`. N5's F1 becomes
     the algebraic identity `j = 3779136·I₁₀²/I₄⁵` on the QM locus
     `[I₂ : I₄ : I₆ : I₁₀] = [96(j+1) : 576j : 4608j(5j+4) : 4096j³]` (VERIFIED: script, and
     **proved in Lean**, `HDec.j_eq_of_onQMLocus`).
3. **Statable in Lean today: none of L1-L12 faithfully.** What is statable now, with genuine
   definitions, is the elementary layer: Igusa–Clebsch invariants, the QM locus, the Thomae
   point, absolute Weil heights, Igusa's 1960 theorem (foundation, used only by an alternative
   proof of A7), and a large part of the glue (G1, the polynomial identities of G4, G17's
   product, G19-G23). `Leaves.lean` states L8-L12 over a **placeholder** signature `Objects`
   (abelian varieties, isogenies, the Jacobian of a sextic, `J₁(N)`, the Faltings height).
   Over a placeholder these Props are not faithful (§3.3); they show the exact shape of the
   final statements.
4. **Biggest missing definitions.** (i) The Faltings height of abelian varieties over number
   fields (D12, very large: Néron models or semistable models plus metrized invariant
   differentials), needed by L8-L12. (ii) The Shimura curve `Y₃` as a PEL moduli scheme over `ℚ`
   with its CM points (D13-D14, very large), needed by L1-L3. (iii) `J₁(N)` over `ℚ` (D9) and the
   ℓ-adic Tate module with its Galois action (D6), large.
5. **Most serious risks (§6).** (a) Route K's two NEW lemmas (G14, G16) have had no review, and
   the locator of the GL₂-type corollary of Khare–Wintenberger is UNVERIFIED. (b) Until D5-D12
   are genuine definitions, the leaf conjunction over a placeholder is a `j`-height bound in
   disguise (wk-h §4.3 applies verbatim). (c) Leaf L12 merges two publications (Pazuki,
   Thomae) to avoid defining analytic theta functions; the normalizations (sup-norm against
   Euclidean, level-2 theta structure) are ASTRA-READ only.

## 2. The proof graph

### 2.1 Node by node (N5 L405-964, steps of h-trust)

Kinds: **LITERATURE** (an application of a published theorem; the node is then the leaf named),
**NEW** (Glazer's argument, or a repository replacement), **BOOKKEEPING** (computation or
routine assembly). Disposition on route K: *kept*, *replaced*, *removed*. Glue numbers refer
to §4.

| Node | N5 lines | Content | Kind | Route K | Leaves / glue |
| --- | --- | --- | --- | --- | --- |
| A1 | L410-420 | QM datum `B = (2,−3)`, `𝒪`, `μ = 2j + ij`, Gram matrix of determinant 1, Rosati `a ↦ μ⁻¹āμ` | BOOKKEEPING | kept | G1 |
| A2 | L420-422, L908-909 | `Y₃/Γ' ≅ P¹_j`, branch values `0, ∞, −16/27`, indices `4, 6, 2`, CM discriminants `−4, −3, −24` | LITERATURE | kept | L2 |
| A3 | L423-441 | `|N/𝔸_f^*K₀| = 4`, central ideles act trivially, `deg(Y₃ → P¹_j) ≤ 324` | NEW (N5) | kept | G2 (L1, F-e) |
| A4 | L528 (h-b1 §4A) | `Y₃` is the fine moduli scheme of `(A, ι, λ, η)` over `ℚ` | LITERATURE | kept | L1, G3 |
| A5 | L443-528 → h-b1 Lemma PR(i) | fibre field `K` Galois, `[K:ℚ] | 144`, unramified outside `T` | NEW (h-b1) | kept | G4 (L1, L2, L3, F-a, F-b) |
| A6 | L529-530 → Lemma PR(ii) | `A` has good reduction at every `v ∤ 3` of `K` | NEW (h-b1) | **simplified** (Galois form) | G5 (L4) |
| A7 | L532-543 | conjugates of `A` geometrically isomorphic | BOOKKEEPING | kept | G6 (L1, L2; or Igusa 1960) |
| A8 | L544-563 | Hom field `L`, `[L:ℚ] ≤ D`, unramified outside `T` | BOOKKEEPING | kept | G7 (F-e) |
| A9 | L564-577 | `End⁰(A_ℚ̄) ∈ {B, M₂(k)}` | LITERATURE + NEW (centralizer) | kept | G8 (F-e) |
| A10 | L578-631 → h-cm NoCM | the CM branch is empty for `u ∈ ℚ \ 𝒞` | NEW (h-cm) | kept | G8 (L3, L2) |
| B1 | L632-664 | sign cocycle `ε` from `B`-linear isogenies `μ_σ` | NEW (N5) | kept | G9 (F-e: Skolem–Noether) |
| B2 | L665-693 | Brauer step: Dirichlet `χ` with the invariants of `[ε]`, `m ≤ 2R^R M` | NEW (N5) | kept | G10 (F-c) |
| B3 | L693-716 | cochain `β`, cleanup, `[L':ℚ] ≤ QM` | NEW (N5) | kept | G11 |
| C1 | L719-731 | `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`, Tate action on `G_{L'}` | NEW (N5) | kept | G12 |
| C2 | L731-734 | `r_ℓ|G_{L'}` absolutely irreducible | LITERATURE | kept | G13 (L5) |
| C3 | L734-737, L10939-11000 | de Rham, HT weights `{0, −1}` | LITERATURE + NEW (lemma) | **removed** | — |
| C4 | L739-741 | Berger: de Rham ⇒ pst | LITERATURE | **removed** | — |
| C5 | L742-751 | oddness | NEW (N5) | **removed** | — |
| C6 | L752-754 | `r_ℓ` unramified outside `T ∪ {ℓ}` | BOOKKEEPING | absorbed in G16-G17 | — |
| C7 | L755-757 | Pan Thm 1.0.4 at `ℓ = 5` | LITERATURE | **replaced** by L6 | L6, G14 |
| C8 | L757-768 | twist and weight, `k = 2` | NEW (N5) + LITERATURE (HT of eigenforms) | **removed** | — |
| C9 | L768-774 | newform `f`, `r₅ ⊂ V₅(A_f)` | LITERATURE | **replaced** by L6 + L7 | G15 |
| C10 | L776-795 | one compatible system at 3 and 5 | NEW (N5) | **removed** (conductor of `B` is defined with one fixed `ℓ ≠ p`) | — |
| D1 | L796-812 | break bound `δ ≤ e − 1 + e v_p(e)`, `u_last ≤ 4a²` | NEW (N5) | kept | G16 (F-d) |
| D2 | L813-823 | semistability (Raynaud) and wild inertia at odd `p` | NEW (N5) | **simplified** (Galois form, no Raynaud) | G16 (L4) |
| D3 | L823-846 | the `p = 2` paragraph | NEW (N5) | kept | G16 (F-d) |
| D4 | L846-852 | conductor exponents `≤ E₀`, `≤ 2`, `0` | NEW (N5) | kept, applied to `B` | G17 |
| D5 | L852-857 | `N ≤ QM²` via local–global compatibility | LITERATURE | kept, as L7 for `A_f` | G17 (L7) |
| E1 | L861-867 | `L'`-isogeny `A × Z → J₁(N)` | LITERATURE (Faltings Hom) | **replaced** (from L6 + G14) | G15 |
| E2 | L868-876 | `h_F(J) ≤ 1.3·10⁷N¹²`, `g ≤ N²` | LITERATURE | kept | L8, G18 |
| E3 | L878-892 | isogeny degree bound | LITERATURE + BOOKKEEPING | kept | L9, G19 |
| E4 | L893-905 | height variation, additivity, Bost; `h_F(A) ≤ Q¹⁷M²⁴` | LITERATURE + BOOKKEEPING | kept | L10, L11, G19 |
| F1 | L908-927 | `j = 3779136 (∏z)⁴/(Σz⁸)⁵` | LITERATURE + BOOKKEEPING | **simplified** (algebra on the QM locus) | L2, G20, G21 |
| F2 | L928-932 | `h(j) ≤ 40 h([z]) + 22` | BOOKKEEPING | kept (Thomae form) | G22 |
| F3 | L934-947 | Pazuki: `h([z]) ≤ 10⁴·2²⁴ X` | LITERATURE + BOOKKEEPING | kept (Thomae form) | L12, G23 |
| F4 | L949-964 | back to `u`, final constant | BOOKKEEPING | kept; **proved in Lean** (repository, `JHeight.lean`) | G23 |

Counts on route K: of N5's 36 nodes, 6 are removed or absorbed (C3, C4, C5, C6, C8, C10), 3 are
replaced by new glue (C7, C9, E1 → G14, G15), and A6, D2, F1 are simplified. The leaves enter at
A2, A4, A5, A6, A10, C2, C7, D5, E2, E3, E4, F1 and F3.

### 2.2 Route K: modularity through GL₂-type abelian varieties over `ℚ` (NEW, SPECULATIVE until reviewed)

N5 builds the 2-dimensional representation `r_ℓ` of `G_ℚ` by the descent (B1-B3, C1) and then
applies Pan's theorem to it, which needs `r_ℓ` de Rham with distinct Hodge–Tate weights (C3, C4),
odd (C5), and afterwards needs the twist and weight argument (C8), newform theory (C9) and the
compatible system (C10). Route K keeps the descent and replaces the rest by an abelian variety
over `ℚ` that carries `r_ℓ`.

- **G14 (Lemma GL₂).** Let `W = Res_{L'/ℚ}(A_{L'})`. Then `V_ℓ(W) ≅ Ind_{G_{L'}}^{G_ℚ} V_ℓ(A)`
  (Milne 1972), and Frobenius reciprocity gives
  `Hom_{G_ℚ}(r_ℓ, V_ℓ(W) ⊗ E) = Hom_{G_{L'}}(r_ℓ|, V_ℓ(A) ⊗ E) ≠ 0`, because
  `ρ_ℓ|G_{L'} = r_ℓ|G_{L'}^{⊕2}` is the Tate action (C1). By L5 over `ℚ` and Poincaré
  reducibility, `r_ℓ` is a constituent of `V_ℓ(B) ⊗ E` for a `ℚ`-simple isogeny factor `B` of
  `W`. Let `D = End⁰_ℚ(B)`, `F` its centre, `s² = [D:F]`. `V_ℓ(B)` is free over `F ⊗ ℚ_ℓ`
  (Betti comparison), so `V_ℓ(B) ⊗ ℚ̄_ℓ = ⊕_{τ: F→ℚ̄_ℓ} V_τ` with all `V_τ` of dimension
  `2 dim B/[F:ℚ]`. By L5, `End_{G_ℚ}(V_τ) = D ⊗_{F,τ} ℚ̄_ℓ = M_s(ℚ̄_ℓ)`, so `V_τ ≅ W_τ^{⊕s}` with
  `W_τ` irreducible. Since `r_ℓ` is one of the `W_τ` and has dimension 2,
  `dim B = s[F:ℚ]`, and `D` contains a maximal subfield of degree `s[F:ℚ] = dim B`: **`B` is of
  GL₂-type.** Finally `W_{L'} ≅ ∏_σ σA ∼ A^{[L':ℚ]}` (the `μ_σ` are defined over `L ⊆ L'`), so
  `B_{L'} ∼ A^k` with `k ≥ 1`.
- **L6** then gives a surjection `J₁(N₀) → B` over `ℚ`, and **L7** a surjection `J₁(N) → B` with
  `N^{dim B} = cond(B)`. Base change to `L'` and Poincaré reducibility: **`J₁(N)_{L'} ∼ A × Z`**
  (G15). This is N5's E1 output, with no use of Faltings' Hom theorem.
- **G16 (Lemma Ind; N5's D1-D3 transplanted).** For `p ≤ R`, every upper ramification group
  `G_{ℚ_p}^u` with `u > U₀ = 4(DG₀)²` acts trivially on `V_ℓ(W)`, where `ℓ = 3` if `p ≠ 3` and
  `ℓ = 2` if `p = 3`. N5 proves that these groups lie in `G_L`, kill `β` (so lie in `G_{L'}`),
  and act trivially on `V_ℓ(A)`. The same argument applies to each conjugate `σA` (with `σ(F)`),
  and Mackey's formula for `Ind` restricted to `G_{ℚ_p}` reduces the action on `V_ℓ(W)` to the
  actions on the `V_ℓ(σA)`. Hence `f_p(V) ≤ dim V·(1 + U₀)` for every subrepresentation `V`,
  in particular `f_p(B) ≤ 2 dim B (1 + U₀) ≤ dim B·E₀`. For `R < p ∈ T` the wild inertia acts
  trivially (N5's tameness argument), so `f_p(B) ≤ 2 dim B`; outside `T`, `f_p(B) = 0`. With L7,
  `v_p(N) = f_p(B)/dim B`, which is N5's exponent bound, and `N ≤ QM²` follows exactly as in N5
  (G17).
- **What route K removes.** Pan; Scholze (or Faltings/Tsuji), Berger and Fontaine's closure
  theorem; N5's Lemma `lem:de-rham-descent`; the Hodge–Tate weights of eigenforms at all levels
  (Saito/Scholl/Kato) and Deligne–Serre; Kronecker–Weber; the twist-and-weight argument C8;
  Li's newform theorem, Shimura's `A_f` construction and the `K_f`-linear Eichler–Shimura
  relation as separate inputs (they are inside L7's proof); oddness C5; the compatible system
  C10 with Mumford's ℓ-independence and the Néron mapping property.
- **What it adds.** L6 (one famous theorem), L7 (in the form "conductor of `A_f` is
  `N^{dim}`"), Weil restriction of abelian varieties (D8), and the conductor of an abelian
  variety over `ℚ` (D10).
- **Status.** The argument of G14 is the standard one by which Ribet shows that building blocks
  are factors of GL₂-type varieties (Ribet 1992 §§5-6, Pyle 2004; UNVERIFIED locators); its
  application to Glazer's `r_ℓ` and G16's transplant of N5's local bounds are NEW here and have
  no review. N5's own route (P) does not depend on them.

### 2.3 Route P (N5's own), for comparison

Route P keeps C2-C10. Its additional leaves would be: Pan 2022 Thm 1.0.4; a de Rham comparison
(Scholze 2013 Cor. 1.8, or Faltings 1989 / Tsuji 1999); Berger 2002 Thm 0.7; Fontaine 1994
Thm 3.8 (closure); Hodge–Tate weights of eigenforms at every level (Saito 1997 or Kato 2004
§9.4) and Deligne–Serre 1974 Thm 4.1; Kronecker–Weber (Tau Ceti has it); Shimura 1973 Thm 1,
Li 1975 Thm 5 and the Eichler–Shimura relation; the Néron mapping property and Mumford §19
Thm 4 (C10). Its definitions add continuous `ℓ`-adic representations of `G_ℚ` and `G_{ℚ_ℓ}`,
`B_dR` with its Galois action and the de Rham / Hodge–Tate / pst conditions, and the Galois
representation attached to a cuspidal eigenform (needs Eichler–Shimura or Deligne). It needs
neither L6 nor D8, D10. Route K is recommended for formalization; route P is the one N5 prints
and h-trust audits.

## 3. The leaves

Each entry gives the statement, the reference, whether the statement is the published one or a
consequence, the objects it needs (definitions D1-D17 of §5), and whether it is statable in Lean
now. Statable now means with Mathlib and cheap new definitions; none of L1-L12 is, so the entry
says what is missing.

### 3.1 Research-level leaves

**L1. Canonical model and moduli interpretation.**
- *Statement.* Let `B = (2,−3)/ℚ`, `𝒪` its maximal order, `μ = 2j + ij`, and
  `K₃ = ker(𝒪̂^× → (𝒪/3𝒪)^×)`. The functor on `ℚ`-schemes `S ↦ {(A, ι, λ, η)}/≅` (an abelian
  scheme `A/S` of relative dimension 2, `ι: 𝒪 → End_S(A)`, a principal polarization `λ` whose
  Rosati involution induces `a ↦ μ⁻¹āμ` on `𝒪`, and an `𝒪`-linear isomorphism
  `η: 𝒪/3𝒪 ≅ A[3]` of `S`-group schemes) is represented by a smooth projective curve `Y₃/ℚ`.
  The normalizer group `Γ' = N/(𝔸_f^×K₃)` acts on `Y₃` over `ℚ`.
- *Reference.* Shimura, Ann. of Math. 85 (1967); Deligne, Sém. Bourbaki 389 (1971), Thm 4.21,
  Cor. 5.7, Ex. 5.8 with §§4.8-4.17 and Prop. 1.15; Kottwitz, J. AMS 5 (1992) §§5, 8; neatness
  of `K₃` by Serre's lemma (Mumford, *Abelian varieties*, §21 Thm 5). Locators as in h-trust A4
  (adopted from V16), UNVERIFIED.
- *Exact or consequence.* Consequence (the specialization of the general PEL theorem to this
  datum, with `ker¹(ℚ, B^×) = 1`; h-b1 §4A items 1-4).
- *Objects.* D5 (abelian schemes over a base, with `𝒪`-action and polarization), D13.
- *Statable now.* With new definitions, **very large** (abelian schemes over schemes, PEL
  moduli functor, representability). Anthropic's FLT has QM fake elliptic curves with level
  structure and polarised abelian schemes (prereq-survey, A4 row), built for a different
  purpose; whether they give `Y₃` over `ℚ` is unchecked.

**L2. Branch data and the Igusa vector.**
- *Statement.* (a) `Y₃/Γ' ≅ P¹_ℚ` with a coordinate `j`; the quotient map is branched exactly
  over `0, ∞, −16/27`, with ramification indices `4, 6, 2`, and these are the images of the CM
  points of discriminants `−4, −3, −24`. (b) For a point `x ∈ Y₃(ℚ̄)` over `j ∉ {0, ∞}`, the
  principally polarized surface `(A_x, λ_x)` is the Jacobian of a genus-2 curve whose
  Igusa–Clebsch invariants satisfy
  `[I₂ : I₄ : I₆ : I₁₀] = [96(j+1) : 576j : 4608j(5j+4) : 4096j³]` in weighted projective space
  (`HDec.OnQMLocus`).
- *Reference.* Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1, Lemma 3.1 and the §3 datum
  (not Props 3.7-3.10, whose printed proof has the defect recorded in rv-up §3); Lin–Yang,
  Math. Z. 295 (2020), Ex. 30 and eqs. (13)-(14) (VERIFIED in arXiv v1 by h-v14; journal
  numbers UNVERIFIED); the conversion `I₂ = 8J₂`, `I₄ = 4J₂² − 96J₄`, `I₆ = 8J₂³ − 160J₂J₄ −
  576J₆`, `I₁₀ = 4096J₁₀` (Igusa 1960; Mestre 1991 §1; UNVERIFIED locators, but cross-checked
  here against Thomae, log Step 2). The constant at `P₋₂₄` has an independent exact check
  (`scratch/rv-up/endo24.py`, `theta24.py`).
- *Exact or consequence.* Consequence: (a) is BG's statement transported to `Y₃` through L1
  (as in N5 L420-441); (b) is Lin–Yang's Igusa vector rewritten in Igusa–Clebsch
  coordinates (`scratch/hdec-elementary/igusa_thomae_check.py`, VERIFIED).
- *Objects.* D2 (done), D7, D13.
- *Statable now.* Part (b)'s right-hand side is statable now (`OnQMLocus`). The leaf needs D13
  for `x ∈ Y₃` and D7 for "is the Jacobian of": **with new definitions, very large** (through
  D13). A genuinely elementary avatar of (b) would quantify over explicit genus-2 curves with
  QM; it would need the Baba–Granath family written out, which no repository source contains
  (risk R6).

**L3. Shimura reciprocity at CM points of `X₆`.**
- *Statement.* For an order `R` of an imaginary quadratic field `K` embedding optimally in `𝒪`,
  the CM points `CM(R) ⊂ X₆(ℚ̄)` are defined over the ring class field `H_R`, and
  `Gal(H_R/K) ≅ Pic(R)` acts on them through Shimura's reciprocity law. In the forms used:
  (i) González–Rotger 2006 Thm 5.12 (the field `ℚ(x)` of a CM point, with
  `[H_R : ℚ(x)] ∈ {1, 2}` according to `D(R)`) and Prop. 5.6 (`#CM(R) = h(R)` under
  `(f, 6) = 1`); (ii) Deligne 1971 §3: the CM points over the elliptic points of `P¹_j` are
  unramified at `p ≥ 5` (Lemma NV, h-b1 §3).
- *Reference.* Shimura 1967 (main theorem of CM for the canonical model); Jordan, thesis
  (Harvard 1981); González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12, Prop. 5.6 (arXiv
  numbering VERIFIED by rv-h-cm; journal numbering UNVERIFIED).
- *Exact or consequence.* (i) exact (as cited by rv-h-cm §7.2); (ii) consequence.
- *Objects.* D13, D14 (CM points and their fields of definition), class groups of orders
  (Tau Ceti has ring class fields and `Pic(𝒪) ≅ Gal`).
- *Statable now.* With new definitions, **very large**.

**L4. Grothendieck's ℓ-adic monodromy theorem.**
- *Statement.* Let `F` be a finite extension of `ℚ_p`, `ℓ ≠ p`, and `ρ: G_F → GL_n(ℚ_ℓ)` a
  continuous representation. Then an open subgroup of the inertia group `I_F` acts unipotently.
  (Used for `ρ = V_ℓ(A)`.)
- *Reference.* Grothendieck, SGA 7 I (LNM 288), Exp. I, Prop. 1.2 / Exp. IX; Serre–Tate, Ann.
  of Math. 88 (1968), Appendix (UNVERIFIED locators).
- *Exact or consequence.* Exact (the general form, valid for every ℓ-adic representation).
- *Objects.* D4 (absolute Galois group of a `p`-adic field with its inertia subgroup), and for
  the application D6.
- *Statable now.* Almost: Mathlib has `Field.absoluteGaloisGroup` with its Krull topology and
  inertia subgroups of valuation subrings; the leaf is **statable with new definitions,
  medium** (the inertia subgroup of `Gal(F̄/F)` for `F/ℚ_p` finite, packaged). Its proof (two
  pages: tame inertia and Frobenius conjugation) is within reach once local Galois theory is in
  place, so L4 could become glue.

**L5. Faltings 1983: semisimplicity and Tate's conjecture.**
- *Statement.* For an abelian variety `A` over a number field `K` and a prime `ℓ`, `V_ℓ(A)` is a
  semisimple `ℚ_ℓ[G_K]`-module, and `End_K(A) ⊗ ℚ_ℓ → End_{G_K}(V_ℓ A)` is an isomorphism.
- *Reference.* Faltings, Invent. Math. 73 (1983), Satz 3, Satz 4 (ASTRA-READ, pp. 360-361); erratum
  Invent. Math. 75 (1984) (that it touches neither: UNVERIFIED).
- *Exact or consequence.* Exact.
- *Objects.* D5, D6.
- *Statable now.* With new definitions, **large** (Tate modules with Galois action).

**L6. Modularity of GL₂-type abelian varieties over `ℚ`.**
- *Statement.* Let `B/ℚ` be a `ℚ`-simple abelian variety such that `End⁰_ℚ(B)` contains a
  number field of degree `dim B`. Then there are `N ≥ 1` and a surjective homomorphism
  `J₁(N) → B` over `ℚ`.
- *Reference.* Khare–Wintenberger, *Serre's modularity conjecture (I)*, Invent. Math. 178
  (2009), 485-504, Thm 1.2 (Serre's conjecture for odd `p`), with (II), ibid. 505-586; Ribet,
  *Abelian varieties over `ℚ` and modular forms* (1992; reprinted in Progr. Math. 224, 2004),
  Thm 4.4 (Serre's conjecture implies the statement). KW (I) record the GL₂-type corollary in
  their introduction. All locators UNVERIFIED (check KW (I) §1 and Ribet's Thm 4.4).
- *Exact or consequence.* Exact as the standard corollary (published in KW (I) as a
  consequence of their theorem together with Ribet).
- *Objects.* D5 over `ℚ` (with `End⁰_ℚ`), D9, D11.
- *Statable now.* With new definitions, **large** (abelian varieties over `ℚ`, `J₁(N)` as an
  abelian variety over `ℚ`, surjective homomorphisms).

**L7. The conductor of a modular quotient.**
- *Statement.* If `B/ℚ` is a `ℚ`-simple quotient of `J₁(N₀)`, there is `M ≥ 1` with
  `M^{dim B} = cond(B)` and a surjective homomorphism `J₁(M) → B` over `ℚ`. Here
  `cond(B) = ∏_p p^{f_p(B)}` with `f_p(B)` the Artin conductor exponent of `V_ℓ(B)` at `p`
  (ℓ = 3 for `p ≠ 3`, ℓ = 2 for `p = 3`).
- *Reference.* Shimura, J. Math. Soc. Japan 25 (1973) Thm 1 (`A_f`); Atkin–Lehner 1970 and Li,
  Math. Ann. 212 (1975) (the newform decomposition of `J₁(N₀)` up to isogeny); Carayol, Ann.
  Sci. ÉNS 19 (1986), Théorème (A) (local–global compatibility: `v_p(M)` is the conductor
  exponent of `ρ_{f,λ}` at `p ≠ ℓ`), whence `cond(A_f) = M^{dim A_f}` (stated in this form in
  Ribet 1992 and Darmon–Diamond–Taylor §1; UNVERIFIED locators). Whether Thm A covers every
  `p ≠ ℓ`, including `p | M`, is h-trust D5's open check (UNVERIFIED).
- *Exact or consequence.* Consequence of the four cited results (no new argument: `B ∼ A_f`
  for a newform `f` of level `M | N₀`, and `V_ℓ(A_f) ⊗ ℚ̄_ℓ = ⊕_σ ρ_{f^σ}`).
- *Objects.* D5, D6, D9, D10.
- *Statable now.* With new definitions, **large**.

**L8. Javanpeykar 2014 at `X₁(N)`.**
- *Statement.* For every number field `K` and `N ≥ 1`, `h_F(J₁(N)_K) ≤ 1.3·10⁷ N¹²`, and
  `dim J₁(N) ≤ N²`.
- *Reference.* Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1 (p. 90) and §2.3 (p. 98)
  (ASTRA-READ): `h_F(Jac X) ≤ 13·10⁶ g deg_B(X)⁵`; with `g, deg_B ≤ [SL₂(ℤ):±Γ₁(N)] ≤ N²`.
- *Exact or consequence.* Consequence (the specialization N5 L868-876 makes).
- *Objects.* D9, D12. *Lean:* `HDec.Javanpeykar` over the placeholder.
- *Statable now.* With new definitions, **very large** (D12).

**L9. Gaudron–Rémond 2014, Thm 1.4.**
- *Statement.* If `A, B` are `K`-isogenous abelian varieties over a number field `K`, there is
  a `K`-isogeny `φ: A → B` with
  `log deg φ ≤ 1024g³(64g² log 14g + log d + 2 log max(h_F(A), log d, 1))`, `g = dim A`,
  `d = [K:ℚ]` (the logarithm of `κ(A)`).
- *Reference.* Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), Thm 1.4
  (ASTRA-READ: original stable Faltings normalization).
- *Exact or consequence.* Exact (logarithmic form).
- *Objects.* D5, D12. *Lean:* `HDec.GaudronRemond`.
- *Statable now.* With new definitions, very large.

**L10. Faltings height under isogeny, products and base change.**
- *Statement.* For a `K`-isogeny `φ: A → B`, `|h_F(A) − h_F(B)| ≤ ½ log deg φ`;
  `h_F(A × B) = h_F(A) + h_F(B)`; the stable `h_F` is unchanged by finite extension of `K`.
- *Reference.* Faltings 1983, §2 and Lemma 5; Raynaud, Astérisque 127 (1985), Exp. VII,
  Cor. 2.1.3 (UNVERIFIED).
- *Exact or consequence.* Exact.
- *Objects.* D5, D12. *Lean:* `HDec.FaltingsHeightVariation` (base change is folded into L12's
  statement).
- *Statable now.* With new definitions, very large.

**L11. Bost's lower bound.**
- *Statement.* `h_F(A) ≥ −(3/2) dim A` for every abelian variety over a number field.
- *Reference.* Bost, Sém. Bourbaki 795 (1994/95), Astérisque 237 (1996); recorded in
  Gaudron–Rémond 2014 §9 (ASTRA-READ) and in Gaudron–Rémond, Comment. Math. Helv. 89 (2014)
  §2.3 as `h_F ≥ −log(π√2)·dim` (read by a model only).
- *Exact or consequence.* Consequence (`log(π√2) < 3/2`). *Lean:* `HDec.BostLower`.
- *Statable now.* With new definitions, very large.

**L12. Pazuki with Thomae.**
- *Statement.* Let `C: y² = f(x)` be a genus-2 curve over a number field `K`, and
  `f = a∏(x − rᵢ)` over an extension `K₂`. Then the Thomae point
  `T = (Δ(S)Δ(Sᶜ))_S ∈ P⁹(K₂)` satisfies
  `h(T) ≤ 4(½X_D + C₂ log(X_D + 2))`, with `X_D = max(1, h_F(Jac C) + log π)` and
  `C₂ = 1000·2⁴(log 2⁴)⁵`, `h` the absolute logarithmic Weil height.
- *Reference.* Pazuki, *Theta height and Faltings height*, Bull. SMF 140 (2012), Cor. 1.3(2)
  and §§2.2-2.3, `g = 2`, `r = 2`, Deligne metric (ASTRA-READ); Thomae, J. reine angew. Math. 71
  (1870); Mumford, *Tata lectures on theta II* (1984), Ch. IIIa §8 (UNVERIFIED): the fourth
  powers of the ten even theta constants are `κ·ε_S·T_S` with one common factor `κ` and signs
  `ε_S`. Pazuki's Euclidean height dominates the sup-norm Weil height (N5 L938-939).
- *Exact or consequence.* Consequence of two publications (merged so that analytic theta
  functions and period matrices are not needed as definitions; the merge is a substitution, not
  an argument). Counted as one leaf citing two theorems.
- *Objects.* D2, D3 (done), D7, D12. *Lean:* `HDec.PazukiThomae`.
- *Statable now.* The left-hand side is statable now (`absLogHeight (thomae r)`); the right
  needs D12: with new definitions, very large.

### 3.2 Foundations (textbook theorems)

These are classical results that a library of abelian varieties and local fields would contain
as API. Several are already formalized (prereq-survey). They are leaves in the sense of the task
(published, not proved by the project), but none is research-level.

- **F-a. Zariski–Nagata purity** (SGA 1, Exp. X, Thm 3.1): used in G4 (h-b1's Prop. TS on the
  regular 2-dimensional scheme `P¹_{ℤ_(p)}`). Formalized: Stacks tag 0BMB (StacksFrontier,
  unreviewed), Tau Ceti for regular local rings of dimension ≤ 2. Statable now with Stacks or
  Tau Ceti.
- **F-b. Abhyankar's lemma** (SGA 1, Exp. XIII, 5.3; Grothendieck–Murre, LNM 208): G4.
  Formalized: Stacks tag 0EYG. Statable with Stacks.
- **F-c. Brauer group of `ℚ` and local reciprocity**: `H²(G_ℚ, ±1) = Br(ℚ)[2]`, injectivity of
  `Br(ℚ) → ⊕_v Br(ℚ_v)`, the sum formula, and "a finite-order character of `ℚ_p^×` has a square
  root iff it is `1` at `−1`" (Milne, ADT Ch. I; Tate in Cassels–Fröhlich Ch. VII; Serre,
  *Corps locaux*). G10. Formalized in Tau Ceti except the identification
  `H²(G_ℚ, ±1) = Br(ℚ)[2]` (not located).
- **F-d. Ramification of local fields** (Serre, *Corps locaux*, III §6, IV §§1-3, VI §2): the
  different bound `δ ≤ e − 1 + e·v_p(e)`, Herbrand's function and the subgroup formula, upper
  numbering, the Artin conductor and Swan conductor of a representation with finite wild image,
  and `U_F^{e+1} ≅ 𝔪_F^{e+1}` via the logarithm (Silverman AEC IV.6.4). G16, G17. Tau Ceti has
  upper numbering, Herbrand and Artin conductor exponents; the different bound was not located.
- **F-e. Abelian-variety API and genus-2 curves.**
  1. Poincaré reducibility (Mumford §19 Thm 1); `rank Hom(A, A') ≤ 4 dim A dim A'` (§19 Thm 3);
     the Weil pairing (§20).
  2. Polarizable complex tori are abelian varieties, GAGA, and rigidity of homomorphisms under
     extension of algebraically closed fields (Mumford §§1-3; Serre 1956; Conrad, Enseign.
     Math. 52 (2006) §3): A9.
  3. Weil restriction: `V_ℓ(Res_{L/ℚ} A) ≅ Ind V_ℓ(A)` and `(Res_{L/ℚ} A)_L ≅ ∏_σ σA` for `L/ℚ`
     Galois (Milne, Invent. Math. 17 (1972)): G7, G14.
  4. `V_ℓ(B)` is free over `F ⊗ ℚ_ℓ` for a number field `F ⊆ End⁰(B)` (comparison with
     `H₁(B(ℂ), ℚ)`; Ribet 1976 §2): G14.
  5. Skolem–Noether (Reiner Thm 7.21; formalized in Tau Ceti): G9.
  6. Vignéras, LNM 800, Ch. II (normalizer of a maximal order at a ramified prime; embedding
     condition): G2, G8.
  7. Weil 1957 (with Torelli and descent for hyperelliptic curves): a principally polarized
     abelian surface over a field of characteristic 0 that is not a product of elliptic curves
     is the Jacobian of a genus-2 curve defined over the same field: G20.
  8. Igusa, Ann. of Math. 72 (1960) (and Mestre 1991 §1): genus-2 sextics over an algebraically
     closed field of characteristic 0 are isomorphic iff their Igusa–Clebsch invariants agree
     in weighted projective space. **Statable now and stated** (`HDec.Igusa1960`); used only by
     the alternative proof of A7.

### 3.3 Faithfulness: no leaf is vacuous or a disguised conclusion

| Leaf | Not vacuous because | Not a disguised conclusion because |
| --- | --- | --- |
| L1 | it asserts representability of an explicit functor; true and nontrivial (`Y₃` has genus ≥ 2) | it says nothing about `u`, `M_S(u)` or heights |
| L2 | it applies to every point of `Y₃`; (a) is checkable data, (b) has the independent `P₋₂₄` check | no height, no `u`; `J(u)` enters only in glue G4, G20 |
| L3 | it is a statement about all CM points | no `u`; NoCM's use of it is glue (G8) |
| L4 | a theorem about all ℓ-adic representations | purely local |
| L5 | general theorem about all abelian varieties over number fields | no heights, no levels |
| L6 | applies to every GL₂-type `B`, e.g. elliptic curves over `ℚ` | gives no level; the level comes from L7 + G16 |
| L7 | applies to every quotient of `J₁(N)` | an equality of conductors, no height |
| L8 | an inequality about one explicit family `J₁(N)` | mentions neither `A` nor `u` |
| L9-L11 | general inequalities about all abelian varieties | no `u`, no `j` |
| L12 | holds for every genus-2 curve; both sides depend on the curve | the `j`-value enters only through glue G21-G22 |

Two cautions.
- **Placeholders.** In `Leaves.lean`, L8-L12 are stated over `Objects`, an unconstrained
  signature. As wk-h §4.3 shows for its `ArakelovSig`, a fake model makes the conjunction of
  these leaves with `ModularityOutput` follow from a bound `h(J(u)) ≲ c·Q¹²M²⁴` alone (set every
  isogeny to degree 1, put `h_F(J₁(N)) = 1.3·10⁷N¹²`, and choose `h_F(Jac C)` at Pazuki's lower
  limit). So over the placeholder the hypothesis is a `j`-height bound in disguise. The leaves
  are faithful only once D5, D6, D7, D9 and D12 are genuine definitions. The concrete pins in the
  draft (`jac f` is the Jacobian of the explicit sextic whose Thomae point and Igusa–Clebsch
  invariants are computed from its roots) reduce, but do not remove, the freedom.
- **Merged leaves.** L7 and L12 each combine several publications without a new argument. L2
  transports BG through L1. These are consequences, never stronger than the published
  statements as written above. L8 is weaker than Javanpeykar's theorem (specialized to
  `X₁(N)`).

## 4. The glue

Size tiers, assuming the definitions of §5 exist: **S** below 300 lines, **M** 300-2000,
**L** 2000-10000, **XL** above. "Lean now" means provable with Mathlib and the cheap
definitions already in `Leaves.lean`.

| # | Statement | Inputs | Origin | Lean provability | Tier |
| --- | --- | --- | --- | --- | --- |
| G1 | QM datum: `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` is a maximal order of `(2,−3)`, `Trd(μ⁻¹xȳ)` has the displayed Gram matrix of determinant 1, Rosati `a ↦ μ⁻¹āμ`, `|(𝒪/3𝒪)^×| = 72` | `form_check.py` | N5 L410-420; h-v14 | **Lean now** (Mathlib `ℍ[ℚ, a, b]`, `decide` on `𝒪/3𝒪`) | S |
| G2 | `|N/𝔸_f^×K₀| = 4`; central ideles act trivially on `Y₃`; `deg(Y₃ → P¹_j) ≤ 324` | L1, F-e6 | N5 L423-441 | over D13 | M |
| G3 | the moduli identification of A4: uniqueness of the principal polarization with the given Rosati involution (elementary), `η` is a `K₃`-structure, neatness | L1, A9's dichotomy | h-b1 §4A | over D5, D13 | M |
| G4 | **Lemma PR(i)**: `K` (splitting field of the fibre of the normalized cover over `u`) is Galois, `[K:ℚ] | 144`, unramified at every `p ∉ T` | L1, L2, L3(ii) (Lemma NV), F-a, F-b; polynomial identities `G⁶ − 97200F² = H²`, resultants and discriminants supported on `p ≤ 13`, `J + 16/27 = 16H²/27G⁶`, non-square discriminants | h-b1 Lemma PR(i) (model-reviewed, rv-h-b1) | identities **Lean now**; the rest over D13 | M |
| G5 | **Lemma PR(ii), Galois form**: inertia at every `v ∤ 3` of `K` acts trivially on `T₃(A)` | L4; `V₃(A)` is free of rank 1 over the division algebra `B ⊗ ℚ₃`, so the monodromy operator (which commutes with `𝒪`) is 0 and the inertia image is finite; `A[3] ⊂ A(K)` (L1) and `1 + 3M₄(ℤ₃)` torsion-free | **NEW** (this note; replaces h-b1's SGA 7 IX 3.6 + toric argument + Serre–Tate) | over D4, D6 | S |
| G6 | conjugates `σA` are geometrically isomorphic | L1 (`σx ∈ Γ'x`), or L2(b) + `Igusa1960` (all conjugates have the Igusa point `[I(j)]`) + Torelli | N5 L532-543 | over D5, D7 | S |
| G7 | Hom field `L = EK`: `[L:ℚ] ≤ F₀·3^{r²} ≤ D`, `r ≤ 16F₀²`, `L` unramified outside `T` | F-e1, F-e3, G5, G4; Minkowski (`1 + 3M_r(ℤ₃)` torsion-free, elementary) | N5 L544-563 | over D5, D6, D8; Minkowski part **Lean now** | M |
| G8 | `End⁰(A_ℚ̄) = B`: the dichotomy `B` or `M₂(k)` (centralizer computation) and NoCM | F-e2; L3(i), L2, Elkies-type model of `X₆ → X₆/W` forced by `W` and Shimura reciprocity; `t(u) = H²/G⁶`, `t(u) − 1 = −3(180F/G³)²` | N5 L564-577; h-cm (rv-h-cm §7.2) | centralizer and `u`-identities **Lean now**; the rest over D13, D14 | M |
| G9 | sign cocycle `ε ∈ Z²(Gal(L/ℚ), ±1)` from `B`-linear isogenies `μ_σ`, `a_σ = (deg μ_σ)^{−1/4}` | F-e5, G7, G8 | N5 L632-664 (rv-h-novel step 1) | over D5 | M |
| G10 | Brauer step: `[ε] ∈ Br(ℚ)[2]` vanishes outside `T`; Dirichlet `χ` of order `m ≤ 2R^R M` with the same invariants; square-root criterion | F-c | N5 L665-693 (rv-h-novel step 2; repair R1) | over D16, D17 (Tau Ceti); square-root criterion `c2_sqrt_criterion.py` | M |
| G11 | cochain `β` with `β² = χ`, `dβ = ε`, the cleanup at odd primes, `L'` Galois, `[L':ℚ] ≤ 2md ≤ 4DR^RM ≤ QM` | G10 | N5 L693-716 (rv-h-novel step 3) | constants **Lean now**; rest over D4, D17 | M |
| G12 | `ρ_ℓ(σ) = β(σ)⁻¹a_σμ_σ∘σ` is a representation, commutes with `B`, `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`, `ρ_ℓ|G_{L'}` is the Tate action | G9, G11 | N5 L719-731 | over D6 | M |
| G13 | `r_ℓ|G_{L'}` is absolutely irreducible | L5, G8, G12 | N5 L731-734 | over D6 | S |
| G14 | **Lemma GL₂** (§2.2): the `ℚ`-simple factor `B` of `Res_{L'/ℚ} A` carrying `r_ℓ` is of GL₂-type, and `B_{L'} ∼ A^k` | L5 (over `ℚ`), F-e1, F-e3, F-e4, G12, G13; Frobenius reciprocity | **NEW** (this note; Ribet's argument for building blocks) | over D5, D6, D8, D11 | M |
| G15 | `J₁(N)_{L'} ∼ A × Z` with `N^{dim B} = cond(B)` | L6, L7, G14, F-e1 | replaces N5 E1 | over D5, D9 | S |
| G16 | **Lemma Ind** (§2.2): for `p ≤ R`, `G_{ℚ_p}^u` (`u > U₀`) acts trivially on `V_ℓ(Res_{L'/ℚ} A)`; for `R < p ∈ T` wild inertia acts trivially; outside `T` all inertia acts trivially. Uses `F = L_v(A[3])` for `p ≠ 3` and `L_v(A[4])` for `p = 3` (`|GL₄(ℤ/4)| = 1321205760 ≤ G₀`), with G5's argument at `ℓ = 3`, resp. `ℓ = 2` (`B` is ramified at 2 and 3) instead of Raynaud's criterion | L4, F-d, G4, G5, G7, G11 | N5 L796-846 (D1-D3, rv-h-novel steps 5-7, repairs R2-R3), transplanted to `Ind`: **NEW** in this form | over D4, D6, D8; D1's inequality `2δ/e ≤ 2(1 + log₂ a!) ≤ 4a²` **Lean now** | L |
| G17 | conductor exponents `f_p(B) ≤ dim B·E₀` (`p ≤ R`), `≤ 2 dim B` (`R < p ∈ T`), `0` (outside `T`), hence `N ≤ ∏_{p≤R} p^{E₀}·M² ≤ QM²` | G16, L7, F-d | N5 L846-857 | over D10; the product **Lean now** (wk-h: about 100 lines) | S |
| G18 | `g = dim J₁(N) ≤ N² ≤ Q³M⁴`, `g ≥ 2` | L8, G15 | N5 L866-876 | over the signature | S |
| G19 | transfer arithmetic: `h_F(A) ≤ Q¹⁷M²⁴` | L8-L11, G15, G18 | N5 L878-905 | **proved** over a signature: wk-h `transfer_numerics` (`scratch/wk-h/Arakelov.lean`) | S |
| G20 | the fibre is `Jac(C)` with `C: y² = f(x)` over `L'`, and its roots are on the QM locus over `J(u)` | F-e7, L2(b), G4 | N5 L908-927 | over D7 | S |
| G21 | `j = 3779136·I₁₀²/I₄⁵` on the QM locus | G20 | N5 L908-927, after Thomae | **proved** (`HDec.j_eq_of_onQMLocus`, standard axioms) | S |
| G22 | `h(j) ≤ 10·h(T) + 22`: `I₄/a⁴ = Σ T_S²`, `(I₁₀/a¹⁰)² = ±∏ T_S`, degree-10 map with ℓ¹ norms `3779136` and `10⁵`; absolute height of `j ∈ ℚ` unchanged in `K₂` | G21; Mathlib `Height.logHeight_eval_le` | N5 L928-932 | **Lean now** (identities: script-checked on 30 root sets; the product identity is combinatorial) | M |
| G23 | `X_D ≤ 3X`, `log(X_D + 2) ≤ 2X_D`, `h(T) ≤ 4·10⁴·2²⁴·X`, so `h(J(u)) ≤ (40·10⁴·2²⁴ + 22)·X·M²⁴` (`JHeightBound`); then F4 and `SixContactMin` | L12, G19, G22; `JHeight.lean` | N5 L934-964 | F4 **proved** (repository); the rest **Lean now** | S |

Top level in Lean: `HDec.sixContactMinAt_of_leaves` (Arakelov leaves + `ModularityOutput` →
`SixContactMinAt S`), whose only `sorry` is `jHeightBoundAt_of_leaves` (G18-G23). The step
`JHeightBoundAt S → SixContactMinAt S` is proved in the draft from a verbatim copy of
`JHeight.lean`'s F4 (axioms `propext`, `Classical.choice`, `Quot.sound`; VERIFIED by
`#print axioms`). `ModularityOutput` is what G1-G17 deliver from L1-L7.

## 5. Definitions

Cost tiers (SPECULATIVE): **cheap** (under 300 lines over Mathlib), **medium** (300-3000),
**large** (3000-20000 or importing a large external development), **very large** (beyond).

| # | Definition | Needed by | Status | Tier |
| --- | --- | --- | --- | --- |
| D1 | quaternion algebra `(2,−3)/ℚ`, maximal order `𝒪`, `𝒪/3𝒪` | G1, L1 | Mathlib `ℍ[ℚ,a,b]`; orders: Anthropic FLT (`CerednikDrinfeld`) | cheap |
| D2 | genus-2 sextic, Igusa–Clebsch invariants from roots, the QM-locus point, the Thomae point, the sextic action of `GL₂` | L2, L12, F-e8, G21, G22 | **done** in `Leaves.lean` (`IC2`-`IC10`, `OnQMLocus`, `thomae`, `actSextic`) | cheap |
| D3 | absolute log Weil height on `Pⁿ` over a number field | L12, G22, G23 | Mathlib `Height.logHeight`; `absLogHeight` **done** | cheap |
| D4 | absolute Galois groups of number fields and `p`-adic fields, decomposition and inertia groups, upper ramification of `G_{ℚ_p}` | L4, G4-G17 | Mathlib: absolute Galois group, inertia of valuation subrings; Tau Ceti: upper numbering for finite Galois extensions | medium |
| D5 | abelian varieties over a field, `dim`, products, homomorphisms, `End`, isogenies and degree, polarizations, Rosati involution; abelian schemes over a base for L1 | L1, L5-L11, most glue | Tau Ceti: abelian varieties (definitions, `Hom`, `IsIsogeny`); Anthropic FLT: polarised abelian schemes | large |
| D6 | `T_ℓ(A)`, `V_ℓ(A)` with continuous Galois action | L4, L5, L7, G5-G17 | not in Mathlib or Tau Ceti for general `A`; Anthropic FLT has Jacobian Tate modules | large |
| D7 | Jacobian of a genus-2 curve with its principal polarization | L2, L12, G20 | Anthropic FLT: `Pic⁰` of curves (special case) | large |
| D8 | Weil restriction of abelian varieties | G7, G14, G16 | absent | large |
| D9 | `X₁(N)` and `J₁(N)` over `ℚ` | L6-L8, G15, G18 | absent as a `ℚ`-curve; Mathlib has `Γ₁(N)` and cusp forms; Lean Pool has a function-field presentation of `X₀(N)` | large |
| D10 | conductor of an abelian variety over `ℚ` (Artin conductor of `V_ℓ` at `p`, fixed `ℓ ≠ p`) | L7, G16, G17 | Tau Ceti: Artin conductor exponents for finite Galois extensions; ℓ-adic conductors absent | medium (given D4, D6) |
| D11 | GL₂-type (`End⁰_ℚ(B)` contains a number field of degree `dim B`) | L6, G14 | trivial given D5 | cheap |
| D12 | **stable Faltings height** (original normalization) | L8-L12, G19 | absent everywhere | **very large** (Néron or semistable models, metrized invariant differentials, Arakelov degree) |
| D13 | **Shimura curve `Y₃`** as the PEL moduli scheme over `ℚ`, its normalizer action and the map to `P¹_j` | L1-L3, G2-G4, G6, G8 | absent (Anthropic FLT's QM moduli is the nearest material) | **very large** |
| D14 | CM points on `X₆` and their fields of definition | L3, G4, G8 | absent | very large (on top of D13) |
| D15 | continuous ℓ-adic representations of profinite groups, Frobenius reciprocity, Mackey | G12-G16 | Mathlib: representations, induced representations of finite index (partial) | medium |
| D16 | `Br(ℚ)`, local invariants, `H²(G_ℚ, ±1)` | G10 | Tau Ceti (proved); Mathlib continuous cohomology | medium (import) |
| D17 | Dirichlet characters as characters of `G_ℚ` | G10, G11 | Mathlib `DirichletCharacter` and cyclotomic Galois groups | cheap |

Route P would add: `B_dR` with its `G_{ℚ_ℓ}`-action and the de Rham, Hodge–Tate and pst
conditions (very large; Mathlib has `B_dR` only as a ring), and the Galois representations
attached to cuspidal eigenforms (very large).

## 6. Risks

- **R1 (route K is new).** G14 and G16 are NEW and unreviewed. G14 is Ribet's standard argument,
  but its use of Faltings over `ℚ` for `W`, the freeness of `V_ℓ(B)` and the identification of
  `r_ℓ` with one `W_τ` need a check. G16 needs Mackey's formula for `Ind` restricted to
  `G_{ℚ_p}` and N5's local argument for each conjugate `σA`; the switch from `A[5]` to `A[4]` at
  `p = 3` keeps the degree below `D G₀` (`|GL₄(ℤ/4)| = 1321205760`, VERIFIED by arithmetic), so
  the constants `U₀`, `E₀`, `H₆` are unchanged. A model review of §2.2 should precede any Lean
  work on route K. Fallback: route P (N5's, model-reviewed by h-trust's sources).
- **R2 (L6's locator).** The GL₂-type corollary of Khare–Wintenberger is quoted from memory.
  Check KW (I), Invent. Math. 178 (2009), §1 and Ribet's Thm 4.4. Ribet's deduction uses Serre's
  conjecture at infinitely many odd primes, so Kisin's 2-adic result is not needed (STANDARD
  reasoning, UNVERIFIED reading).
- **R3 (L7 at `p | M`).** h-trust D5's open question (does Carayol's Thm A cover every `p ≠ ℓ`,
  including `p | M`?) carries over.
- **R4 (placeholders).** Over the `Objects` signature the leaves are not faithful (§3.3). Any
  announcement must say that L8-L12 become faithful only with D5-D7, D9, D12 genuine.
- **R5 (L12 normalizations).** Pazuki's height is Euclidean at archimedean places and uses a
  level-2 theta structure; N5's comparison (L936-947) is ASTRA-READ only. Thomae's formula is
  quoted from memory; the identities `Σ T_S² = I₄/a⁴` and `∏ T_S² = (I₁₀/a¹⁰)⁴` are VERIFIED,
  and the Igusa–Clebsch to Igusa conversion is cross-checked against Thomae up to sign (log
  Step 2). The sign of `∏ T_S` does not affect heights.
- **R6 (no explicit QM family).** The task suggested explicit genus-2 models of the QM surfaces.
  No repository source contains the Baba–Granath family, and it cannot be checked offline. With
  it, Lemma PR might become a discriminant computation over `ℚ(√6)(u)` (note that
  `−6J(u) = 6·240²F²/G⁶`, so `ℚ(J(u), √(−6J(u))) = ℚ(√6)` for every `u`; if BG's field of
  definition is `ℚ(j, √(−6j))`, all fibre curves are defined over `ℚ(√6)`: SPECULATIVE). Local
  monodromy at the contacts would still need the moduli. This is a direction, not a result.
- **R7 (L1-L3 size).** The Shimura-curve leaves need the largest definitions (D13, D14), and
  they are used for one fact each: the fibre field and good reduction (G4, G5), the degree 324
  (G2) and NoCM (G8). A route avoiding them would need explicit equations (R6) or a different
  CM argument (N5's Fowler branch, which needs an effective class number bound and the CM
  Faltings height formula).
- **R8 (inherited).** Everything h-trust §2 lists as model-reviewed only (Glazer's descent and
  conductor bound, Lemma PR, NoCM) is glue here: formalizing the glue is also its first
  machine check.

## 7. First steps for a Lean team

1. **Review route K** (§2.2, G14, G16) by an independent model and a human before formalizing
   it; until then keep route P's leaf list as the fallback.
2. **Elementary glue, now** (about 1000 lines, no new definitions): G1 (`𝒪`, Gram matrix,
   `|(𝒪/3𝒪)^×| = 72`); G4's polynomial identities; G7's Minkowski lemma; D1's inequality and
   G17's product `N ≤ QM²`; G22 (degree-10 height bound with Mathlib's
   `Height.logHeight_eval_le`, the identities `Σ T_S² = I₄/a⁴` and `(I₁₀/a¹⁰)² = ±∏ T_S`); and
   `jHeightBoundAt_of_leaves` over the signature using wk-h's `transfer_numerics`. This makes
   the only `sorry` of `Leaves.lean` disappear and machine-checks all of E and F.
3. **Definitions, in order of leverage:** D4 + D6 (Galois groups of local fields and Tate
   modules: they unlock L4, L5, G5, G12-G16), D5/D7/D8 (import Tau Ceti's abelian varieties and
   Anthropic's Jacobians), D9 (`J₁(N)` over `ℚ`), D10. Then D12 (Faltings height), the largest
   single item, which alone turns L8-L12 from placeholders into faithful leaves.
4. **State L4-L7 in Lean** once D4-D11 exist, replacing the placeholder `Objects`; then
   `ModularityOutput` becomes a theorem to prove from L1-L7.
5. **Shimura-curve block last** (D13, D14, L1-L3). Investigate R6 (explicit Baba–Granath
   family over `ℚ(√6)(u)`) first; if it works, part of L1-L3 may be replaced by computation.

## Changelog

- 2026-11-11: first version (task hdec-elementary).
