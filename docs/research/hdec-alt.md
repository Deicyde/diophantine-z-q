# hdec-alt: published replacements for Glazer's argument, and a leaf/glue decomposition of H

Status: research note (task hdec-alt, 2026-11-11). Work log: `scratch/hdec-alt/log.md`. Lean draft:
`scratch/hdec-alt/Leaves.lean` (compiles with `lake env lean`; one `sorry`, the glue's top
theorem). No file under `ZInQKernel/`, `blueprint/` or other notes was edited. There is no network
on this host: every theorem number below that was not already read by a repository note is
marked UNVERIFIED, and none of the candidate papers of §1.1 could be opened here.

Marks: **VERIFIED** (read in a repository source, computed, or compiled here), **STANDARD**
(a published theorem with a reference; the locator may still be UNVERIFIED), **SPECULATIVE**
(an assessment or an unreviewed proposal). Inherited locator marks (ASTRA-READ, AUDIT-READ) are
those of `docs/research/h-trust.md`.

Target. H = `ZInQ.SixContactMin`, or the stronger `ZInQ.JHeight.JHeightBound Mult.S_mul`
(`ZInQKernel/Hypotheses/JHeight.lean`), from which `SixContactMin` is already proved in Lean
(`sixContactMin_of_jHeightBound`, VERIFIED by rv-lit §4 and recompiled here as
`ZInQ.HDecAlt.sixContactMinAt_of_jHeightBoundAt`, axioms `propext`, `Classical.choice`,
`Quot.sound`).

## 1. Verdict

1. **No published theorem replaces the core of Glazer's argument (SPECULATIVE as a claim about
   the literature; the Baker-type obstruction is VERIFIED, nt-h §3.3; the von Känel obstruction
   is SPECULATIVE, §1.1).** H is an effective Shafarevich
   bound, polynomial in `M = M_S(u)`, for the QM surfaces over the rational points of `X₆/W`.
   No paper that we know states such a bound for QM surfaces or for this family. The candidates
   fail as follows (details §1.1):
   - effective Shafarevich for `GL₂`-type abelian varieties over `ℚ` (von Känel) needs a
     `GL₂`-type variety `B₀/ℚ` containing `A`, whose dimension is not bounded in `M`; with a
     constant that grows with the dimension, the bound is not polynomial in `M`, which the
     multiplication consumer requires (h-map §1; rs-height R6);
   - Baker/S-unit Shafarevich theorems for genus-two curves (Smart 1997, von Känel 2014) are
     excluded, since the curves `C_{J(u)}` have bad stable reduction at every positive contact
     valuation, even or odd (nt-h §3.3, VERIFIED there by computation);
   - the explicit height formulas and comparisons in genus two (Bost–Mestre–Moret-Bailly, Ueno,
     Pazuki), the isogeny theorems (Masser–Wüstholz, Gaudron–Rémond) and the height bounds for
     modular Jacobians (Ullmo, Jorgenson–Kramer, Javanpeykar) are already, or can only be,
     inputs of the Arakelov half; none of them shortens the modularity half;
   - the explicit models of the discriminant-6 curve (Hashimoto–Murabayashi, Baba–Granath,
     Lin–Yang, Elkies) already supply steps A2, A7 and F1; they do not give the field over which
     the fibre has good reduction outside `T` (Lemma PR).
2. **One substitution is sound and shortens the trust base: modularity by Ribet's theorem on
   building blocks plus Khare–Wintenberger, in place of Pan's theorem with p-adic Hodge theory**
   (§1.2; VERIFIED as an argument here, not yet reviewed by anyone else). It removes six leaves
   (Pan; the de Rham comparison of Scholze or Faltings–Tsuji; Fontaine's closure theorem;
   Berger; the Hodge–Tate weights of eigenforms of Saito or Kato; Deligne–Serre) and two passages
   that are new in N5 (the de Rham descent lemma of C3, and C8's weight and determinant
   argument). It adds two leaves (Ribet; Khare–Wintenberger) and an elementary twist lemma. No
   constant changes. h-leaves §4.5 judged the Khare–Wintenberger route "no reduction in depth";
   it considered applying Serre's conjecture and modularity lifting to `r_ℓ` directly, which needs
   residual irreducibility. Applying Khare–Wintenberger to a `GL₂`-type *abelian variety* needs
   neither.
3. **The best sound route R\*** is Glazer's architecture (h-trust A1-F4) with: NoCM for the CM
   branch (h-cm), Lemma PR for the integral model (h-b1), Faltings 1983 for the Tate conjecture
   (h-trust D2), and the modularity substitution above. §2 maps it node by node.
4. **Leaves (§3): 30 published theorems, in three tiers.** Merging no two distinct theorems:
   - **18 deep leaves**, present in no Lean library: Baba–Granath; the canonical model of the
     level-3 curve; Shimura reciprocity; González–Rotger; Grothendieck–Raynaud (SGA 7 IX);
     Serre–Tate; Faltings' Tate theorem; Ribet; Khare–Wintenberger; Shimura's `A_f` with
     Eichler–Shimura; Carayol; Javanpeykar; Gaudron–Rémond; Faltings' isogeny-height lemma;
     additivity; Bost; Pazuki; Igusa–Lin–Yang;
   - **7 library leaves**, proved in Tau Ceti or in the Stacks formalization (prereq-survey §1):
     purity, Abhyankar, Skolem–Noether, the Brauer group of `ℚ`, Kronecker–Weber, the newform
     theory of twists, Chebotarev;
   - **5 textbook leaves**, classical and absent from libraries: Mumford §19 (rank of `Hom`,
     Poincaré reducibility, independence of `ℓ`), complex uniformization with GAGA and rigidity,
     the Néron mapping property, Brauer–Nesbitt, and Serre's *Corps locaux*.

   "About ten" is not reachable without merging distinct theorems or hiding them in the glue.
   The irreducible core that a crowd would have to formalize from scratch is the 18 deep leaves,
   and each of them needs one of four large definitional layers (§5).
5. **Glue (§4): 21 steps G1-G21.** The new mathematics is in G2-G3 (Lemma PR), G7 (NoCM),
   G8-G10 (the scalar descent), G13 (the new modularity step), G15 (one compatible system),
   G16 (the conductor bound) and G19-G20 (the arithmetic). G21 (F4) and the final numerics are
   already proved in Lean; G19's arithmetic is proved in `scratch/wk-h/Arakelov.lean`
   (`transfer_numerics`).
6. **Lean (`scratch/hdec-alt/Leaves.lean`, VERIFIED: compiles).** It states 21 leaves as
   `def … : Prop`. Five are concrete over Mathlib today: the Hasse principle and Hilbert
   reciprocity for quaternion algebras over `ℚ`, Kronecker–Weber, Skolem–Noether,
   Brauer–Nesbitt. Sixteen are stated over 22 `opaque` placeholders for the missing definitions,
   with genuine cheap definitions where possible (abelian varieties over a field from Mathlib's
   group schemes, continuous Galois representations, intertwiners, semisimplicity, projective
   heights). Over placeholders these leaves are not yet faithful (§6 R6). The top theorem
   `jHeightBoundAt_of_leaves` is `sorry`; the last step `sixContactMinAt_of_jHeightBoundAt` is
   proved. The Shimura-curve and scheme-theoretic leaves (L1-L6, L10-L11) are not stated.
7. **Biggest missing definition:** the Faltings height (very large: Néron or semistable models
   and metrized invariant differentials). It carries six leaves (L21-L26). Next: Shimura curves
   with their canonical models (L1-L4), and Tate modules with the Galois representations of
   newforms (L8, L12-L18).
8. **Most serious risk:** the leaf statements of the new route (L13 Ribet, L14
   Khare–Wintenberger) are recalled from memory, not read; Ribet's theorem appeared in a
   proceedings volume, and whether its printed form is exactly "every building block is a
   `ℚ̄`-factor of a `GL₂`-type variety over `ℚ`" must be checked against Ribet 1992 and Pyle 2004.
   Behind it stays the risk that already governs H: the glue G2-G3, G7-G10, G15-G16 has model
   reviews only (h-trust §2.1).

### 1.1 The candidates

| Candidate (theorem numbers UNVERIFIED unless marked) | What it would replace | Assessment |
| --- | --- | --- |
| von Känel, *Modularity and integral points on moduli schemes*, arXiv:1310.7263 (publication status UNVERIFIED); the "von Känel–Kret height argument" of the 10/11 manuscript (README, docs/revision-2.md: replaced in 11/5; no citation record survives in the audit, VERIFIED by grep) | effective Shafarevich for abelian varieties of `GL₂`-type over `ℚ`: `h_F(B) ≤ c(g)·N_S^{e}` with `N_S` the product of the bad primes. Applied to a `GL₂`-type `B₀ ⊇ A`, it would replace C9-C10, D1-D5 and E1-E3 by one theorem | **Not usable as it stands.** (i) `A` lives over a number field; a variety over `ℚ` needs Ribet's construction (L13). (ii) `dim B₀ = [E:ℚ]`, where `E` contains the values of the nebentypus `ε`, and `ε_p(−1) = −1` is forced at each prime `p` where the class `[ε] ∈ Br(ℚ)[2]` of step B2 has invariant `1/2`, so `[ℚ(ε):ℚ] ≥ 2^{v₂(p−1)−1}`; nothing controls which primes of `supp M` occur, so `dim B₀` is not bounded in `M` (SPECULATIVE: the step "the nebentypus of every lift is odd at the primes of `T₋`" is our reading of B2's square-root obstruction, not checked in a source). (iii) In this method (SPECULATIVE) the conductor bound at the primes `p ≤ 2g+1` and the isogeny estimate make the constant grow at least exponentially in `g` (our recollection of vK's main bound is of the form `(3g)^{144g} N_S^{24}`; UNVERIFIED). With `g` up to a power of `M` this is not polynomial in `M`. If the constant were polynomial in `g`, the route would be the largest available simplification: **reading vK's main theorem is the first open check (§7)** |
| Effective Shafarevich for abelian varieties with real multiplication (Hilbert modular varieties; von Känel, von Känel–Kret) | the same | Same obstruction: QM surfaces enter only through `GL₂`-type varieties over `ℚ`, of unbounded dimension |
| Effective Shafarevich for QM surfaces or for this family | everything up to E4 | None known (SPECULATIVE). nt-h §3.6: for families over compact curves in `A_g` the only polynomial bounds go through modularity |
| Smart, Math. Comp. 66 (1997); von Känel, J. Théor. Nombres Bordeaux 26 (2014) (genus-two / hyperelliptic Shafarevich by Baker's method) | H outright | **Excluded**: the curve `C_{J(u)}` has bad stable reduction at every prime with positive contact valuation, even or odd (nt-h §3.3, `genus2cusp.py`); the bad set is not controlled by `M` |
| Bost–Mestre–Moret-Bailly, Astérisque 183 (1990); Ueno, *Discriminants of curves of genus 2* (1988): exact Faltings height of a genus-two Jacobian with semistable reduction | F1-F3 | Not better: the formula needs the stable model of the curve, which degenerates at every contact prime (above), and the archimedean term `‖χ₁₀‖` must still be bounded |
| Pazuki: comparison of the height of the Igusa invariants with `h_F(Jac C)` (from memory, in BSMF 140 (2012) or Manuscripta Math. 142 (2013); existence of an explicit published inequality UNVERIFIED) | F1 and F3 together (with the Igusa vector of A7 in place of the theta formula) | Possible replacement of L26-L27 by one leaf; not adopted until the statement is read |
| Masser–Wüstholz, Ann. of Math. 137 (1993) | Faltings' Tate theorem (L12) | A valid alternative (h-leaves §2); not explicit, so GR14 (L22) stays for E3. Choosing it changes no count |
| Gaudron–Rémond, Duke 163 (2014), Thm 1.4 | E3 | Already the leaf L22 |
| Ullmo, Jorgenson–Kramer (`h_F(J₀(N))`, squarefree `N`); Javanpeykar 2014 (`J₁(N)`, all `N`) | E2 | Javanpeykar stays: the newform has a nebentypus, so `J₀(N)` does not suffice, and `N` is not squarefree |
| Hashimoto–Murabayashi, Tohoku Math. J. 47 (1995); Baba–Granath, Canad. J. Math. 60 (2008); Lin–Yang, Math. Z. 295 (2020); Elkies, ANTS-III (1998) | A2, A7, F1 (already used); possibly A3-A6 through an explicit genus-two model | They do not replace Lemma PR: a model `C_j` over its field of definition is determined up to quadratic twist, and showing that the Jacobian has good reduction outside `T` after a bounded extension needs the same ramification analysis. One fact VERIFIED here: for `j = J(u)`, `−6j = 6·(240F/G³)²` and `27j+16 = 16H²/G⁶` (h-trust A5), so the square classes that govern the field of moduli in these models are constant on the family (SPECULATIVE: that they are the relevant classes in Baba–Granath's model) |
| Ribet, *Abelian varieties over `ℚ` and modular forms* (1992; Progr. Math. 224 (2004)); Pyle, Progr. Math. 224 (2004); Khare–Wintenberger, Invent. Math. 178 (2009) | C3-C5, C7, C8 | **Adopted** (§1.2) |

### 1.2 The modularity substitution (VERIFIED as an argument; unreviewed)

Setting: `A/L'` the non-CM fibre (`End⁰(A_ℚ̄) = B`, G7), with the `B`-linear isogenies
`μ_σ : ᵟA → A` of step B1, and Glazer's `r_ℓ : G_ℚ → GL₂(E_λ)` with
`V_ℓ(A) ⊗ E_λ ≅ r_ℓ ⊕ r_ℓ` on `G_{L'}` (C1).

1. `A_ℚ̄` is a building block: `End⁰` is central simple over the totally real field `ℚ`, with
   Schur index `t = 2` and `t·[ℚ:ℚ] = 2 = dim A`, and every conjugate is isogenous to `A`
   compatibly with `End⁰` (the `μ_σ`).
2. Ribet (L13): there is an abelian variety `B₀/ℚ` of `GL₂`-type, with `E₀ = End⁰_ℚ(B₀)`, such
   that `B₀ ⊗ K ∼ A^n ⊗ K` over some finite Galois `K ⊇ L'`.
3. For an embedding `τ : E₀ → Ē_λ`, let `ρ_τ` be the corresponding `2`-dimensional constituent
   of `V_ℓ(B₀) ⊗ Ē_λ`. On `G_K`, `V_ℓ(B₀) ≅ V_ℓ(A)^n` is semisimple (Faltings, L12), and
   `r_ℓ|G_K` is absolutely irreducible (C2, from L12). So `ρ_τ|G_K ≅ r_ℓ|G_K`.
4. Twist lemma (elementary): `Hom_{G_K}(ρ_τ, r_ℓ)` is a line on which `G_ℚ` acts through
   `Gal(K/ℚ)` by a character `ψ`, and `r_ℓ ≅ ρ_τ ⊗ ψ`. `ψ` has finite order, so by
   Kronecker–Weber (L20) it is a Dirichlet character.
5. Khare–Wintenberger (L14): `ρ_τ ≅ ρ_{f₀,λ}` for a weight-two newform `f₀`. Then
   `r_ℓ ≅ ρ_{f₀,λ} ⊗ ψ`, and the twist is the representation of a newform `f` (L15). This is the
   conclusion of C7-C9 with weight two, which C8 had to derive from Hodge–Tate weights.
6. Everything after C9 is unchanged: C10 (one compatible system at `ℓ = 3, 5`), the conductor
   bound D1-D4 for Glazer's `r_ℓ`, Carayol (D5), and the transfer. The constants are unchanged,
   since the level of `f` is the conductor of the same `r_ℓ`.

What is no longer used: oddness (C5); the de Rham, potentially semistable and Hodge–Tate
properties (C3, C4); Pan's theorem (C7); the eigenform weights (HT), Deligne–Serre, the Weil
pairing and the determinant argument (C8). What remains used: Faltings 1983 (already a leaf),
Kronecker–Weber (already used by C8), C2 and C10.

## 2. The proof graph (h-trust §1, node by node)

Kinds: **LIT** = application of a published theorem; **NEW** = Glazer's argument or a
repository replacement (NoCM, Lemma PR), model-reviewed only; **BK** = bookkeeping or exact
computation. "R\*" = what happens on the route of this note. Leaves `Lk` are §3, glue `Gk` §4.

| Node (N5 lines) | Content | Kind | R\* |
| --- | --- | --- | --- |
| A1 (410-420) | QM datum `B = (2,−3)`, `𝒪`, `μ`, Gram matrix of determinant 1 | BK (script `form_check.py`) + LIT (Lin–Yang convention) | kept: G1 |
| A2 (420-422, 908) | `X₆/W ≅ P¹_j`, branch values `0, ∞, −16/27`, indices `4, 6, 2`, CM labels `−4, −3, −24` | LIT | kept: L1 |
| A3 (423-441) | level 3, normalizer action, `deg(Y₃ → P¹_j) ≤ 324` | BK (Vignéras, Deligne, script) | kept: G1 |
| A4 (528) | `Y₃` = fine moduli scheme over `ℚ` of `(A, ι, λ, η)`, `K₃` neat | LIT (citation task, h-b1 §4A) | kept: L2 |
| A5 (443-528) | Lemma PR(i): fibre field `K`, `[K:ℚ] ∣ 144`, unramified outside `T` | NEW (h-b1, rv-h-b1) | kept: G2 (L1-L3, L5, L6) |
| A6 (529-530) | Lemma PR(ii): good reduction at `v ∤ 3`, all conjugates | NEW | kept: G3 (L2, L7, L8) |
| A7 (532-543) | conjugates geometrically isomorphic (Igusa vector) | BK | kept: G4 (L1, L27's Igusa vector) |
| A8 (544-563) | Hom field `L`, `[L:ℚ] ≤ D`, unramified outside `T` | BK | kept: G5 (L8, L9) |
| A9 (564-577) | `End⁰(A_ℚ̄) ∈ {B, M₂(k)}` | LIT + NEW passage (two model reviews) | kept: G6 (L10) |
| A10 (578-631 replaced) | NoCM: `End⁰(A_ℚ̄) = B` for rational `u ∉ 𝒞` | NEW (h-cm, rv-h-cm) | kept: G7 (L3, L4) |
| B1 (632-664) | sign cocycle `ε` from `B`-linear `μ_σ` | NEW | kept: G8 (L17) |
| B2 (665-693) | `[ε] ∈ Br(ℚ)[2]` vanishes outside `T`; Dirichlet `χ`; `m ≤ 2R^R M` | NEW | kept: G9 (L19) |
| B3 (693-716) | cochain `β`, `[L':ℚ] ≤ QM` | NEW | kept: G10 |
| C1 (719-731) | `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` | NEW | kept: G11 |
| C2 (731-734) | `r_ℓ|G_{L'}` absolutely irreducible | LIT (Faltings) | kept: G11 (L12) |
| C3 (734-737, 10939-11000) | de Rham, HT weights `{0,−1}`; descent lemma | LIT + NEW lemma | **removed** |
| C4 (739-741) | de Rham ⇒ pst (Berger) | LIT | **removed** |
| C5 (742-751) | oddness | BK | **removed** |
| C6 (752-754) | `r_ℓ` unramified outside `T ∪ {ℓ}` | BK | kept: G12 (L8) |
| C7 (755-757) | Pan, Thm 1.0.4 | LIT | **replaced** by G13 (L12, L13, L14, L15, L20) |
| C8 (757-768) | twist, weight two, finiteness of `ψ` (HT, Deligne–Serre, determinant, Kronecker–Weber) | BK + LIT | **replaced** by G13 |
| C9 (768-774) | newform `f`, `A_f`, `r₅ ⊂ V₅(A_f)` | LIT | kept: G14 (L15, L16, L28) |
| C10 (776-795) | one compatible system at 3 and 5 | NEW | kept: G15 (L8, L9, L11, L28) |
| D1 (796-812) | break bound `u_last ≤ 4a²` | NEW (script `c3_breaks.py`) | kept: G16 (L29) |
| D2 (813-823) | semistability, wild inertia at odd `p` | NEW | kept: G16 (L7) |
| D3 (823-846) | `p = 2` | NEW | kept: G16 (L29) |
| D4 (846-852) | `a_p ≤ E₀`, `≤ 2`, `0` | NEW | kept: G16 |
| D5 (852-857) | `N ≤ QM²` | LIT (Carayol) | kept: G17 (L18) |
| E1 (861-867) | `L'`-isogeny `A × Z → J₁(N)` | LIT (Faltings Hom, Poincaré) | kept: G18 (L9, L12, L16) |
| E2 (868-876) | `h_F(J₁(N)) ≤ 1.3·10⁷N¹²` | LIT | kept: L21 |
| E3 (878-892) | isogeny degree bound | LIT + BK | kept: G19 (L22) |
| E4 (893-905) | height variation, additivity, Bost | LIT + BK | kept: G19 (L23-L25) |
| F1 (908-927) | `j = 3779136(∏z_m)⁴/(∑z_m⁸)⁵` | LIT + script | kept: L27 |
| F2 (928-932) | `h(j) ≤ 40h(z) + 22` | BK | kept: G20 |
| F3 (934-947) | Pazuki | LIT + BK | kept: G20 (L26) |
| F4 (949-964) | `h(u) < h(j) + 74`, final constant | BK | kept: G21 (**proved in Lean**) |

Counts on R\* (VERIFIED from the table): of the 36 nodes, 3 are removed (C3-C5) and 2 replaced by
the single glue step G13 (C7, C8). Of the remaining 31: 11 LIT (A2, A4, C2, C9, D5, E1-E4, F1,
F3), 13 NEW (A5, A6, A9, A10, B1-B3, C1, C10, D1-D4; A9 for its N5-new passage) and 7 BK (A1, A3,
A7, A8, C6, F2, F4).

## 3. The leaves

Format: statement (as used, or the published form); reference; **exact** = the published
statement, **consequence** = follows from it by a remark recorded here; objects; statable in Lean
now: yes / with new definitions (tier of the costliest one, §5) / no. "Lean" names the `def` in
`scratch/hdec-alt/Leaves.lean`.

### Deep leaves (in no Lean library)

**L1. Baba–Granath: the discriminant-6 curve modulo Atkin–Lehner.** `X₆/W ≅ P¹_j` over `ℚ`; the
elliptic points are at `j = 0, ∞, −16/27`, of orders `4, 6, 2`, the CM points of discriminants
`−4, −3, −24`; the polarized QM surfaces over a finite nonzero `j` are those of the stated
datum. Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and the §3 datum (journal numbering
UNVERIFIED; the 2005 preprint's Thm 1 is ASTRA-READ); Lin–Yang 2020, Example 30 (VERIFIED in
arXiv v1 by h-v14). Exact (Props 3.7-3.10 not used). Objects: Shimura curves, canonical models,
moduli of QM surfaces. Statable: no (very large).

**L2. Canonical model and moduli interpretation.** The canonical model over `ℚ` of the level-3
Shimura curve `Y₃` of `𝒪` is the fine moduli scheme of `(A, ι : 𝒪 → End A, λ, η)` with `λ` the
principal polarization of Rosati type `μ` and `η` an `𝒪`-linear level-3 structure; `K₃` is neat.
Shimura, Ann. of Math. 85 (1967); Deligne, Sém. Bourbaki 389 (1971), Thm 4.21, Cor. 5.7,
§§4.7-4.17; Kottwitz, JAMS 5 (1992) §§5, 8; neatness: Mumford, *Abelian varieties* §21 Thm 5
(all UNVERIFIED; h-trust A4). Consequence (the four inputs of h-b1 §4A). Objects: Shimura
curves, abelian schemes, level structures. Statable: no (very large). In Lean only its weakest
consequence is stated, as the hypothesis `GeometricInput` (a QM fibre over `J(u)` exists over a
number field).

**L3. Shimura reciprocity at CM points.** The Galois action on CM points of the canonical model
is given by the Artin map of the CM field. Deligne 1971 §3; Shimura 1967 (UNVERIFIED). Exact.
Used in G2 (Lemma NV) and G7 (NoCM). Statable: no (very large).

**L4. González–Rotger.** The rational CM points of `X₆/W` and the fields of moduli of the CM
fibres: González–Rotger, J. Math. Soc. Japan 58 (2006), Thm 5.12 and Prop. 5.6 (Prop. 5.6 only
under `(f, 6) = 1`), numbers of arXiv:math/0612732 (VERIFIED by rv-h-cm; journal numbering
UNVERIFIED); with Vignéras, LNM 800, for the embedding condition. Exact. Statable: no (very large).

**L7. Grothendieck–Raynaud.** Over a field complete for a discrete valuation with residue
characteristic `p`, an abelian variety acquires semistable reduction over `K(A[n])` for
`n ≥ 3`, `p ∤ n` (Raynaud's criterion), and semistable plus potentially good is good; inertia acts
unipotently at semistable reduction. SGA 7 I, Exp. IX, Prop. 4.7 and §3 (UNVERIFIED);
Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5 (ASTRA-READ). Consequence as stated in
Lean (`Leaf_RaynaudGood`). Objects: abelian varieties, good and potentially good reduction,
torsion. Statable: with new definitions (medium).

**L8. Serre–Tate.** For `v ∤ ℓ`: `A` has good reduction at `v` iff `V_ℓ(A)` is unramified at
`v` (Néron–Ogg–Shafarevich, Thm 1), and potentially good reduction iff inertia acts through a
finite quotient (Thm 2). Serre–Tate, Ann. of Math. 88 (1968) (UNVERIFIED). Exact
(`Leaf_NOS` states Thm 1). Objects: Tate modules, inertia groups. Statable: with new definitions
(large, for `tateRep`).

**L12. Faltings' Tate theorem.** Over a number field, `V_ℓ(A)` is a semisimple `G_K`-module and
`Hom_K(A, B) ⊗ ℚ_ℓ → Hom_{G_K}(V_ℓA, V_ℓB)` is an isomorphism. Faltings, Invent. Math. 73
(1983), Satz 3, Satz 4, Korollar 1 (ASTRA-READ pp. 360-361). The Lean form (equality of ranks) is
a consequence, equivalent given the classical injectivity. Used in C2, G13, G15, G18.
Statable: with new definitions (large). Lean: `Leaf_FaltingsTate`.

**L13. Ribet: building blocks.** Every building block (an abelian variety over `ℚ̄` whose `End⁰`
is central simple over a totally real field `F` with Schur index `t ≤ 2`, `t[F:ℚ] = dim`, and
which is isogenous to each Galois conjugate compatibly with `End⁰`) is a `ℚ̄`-factor of a
`GL₂`-type abelian variety over `ℚ`. Ribet, *Abelian varieties over `ℚ` and modular forms*,
Proc. KAIST Workshop 1992, repr. Progr. Math. 224 (2004), 241-261; Pyle, *Abelian varieties
over `ℚ` with large endomorphism algebras and their simple components over `ℚ̄`*, Progr. Math.
224 (2004), 189-239 (theorem numbers UNVERIFIED). Exact (to be confirmed, §6 R1). Statable: with
new definitions (medium-large). Lean: `Leaf_RibetBuildingBlock`.

**L14. Khare–Wintenberger: `GL₂`-type abelian varieties over `ℚ` are modular.** Every
`2`-dimensional constituent of `V_ℓ(B) ⊗ Ē_λ` is the `λ`-adic representation of a weight-two
newform. Khare–Wintenberger, Invent. Math. 178 (2009), 485-504 and 505-586 (Serre's
conjecture), with Kisin, Invent. Math. 178 (2009), 587-634, at `p = 2`; the implication is
Ribet 1992, Thm 4.4 (numbers UNVERIFIED). Consequence (stated through constituents). Statable:
with new definitions (large). Lean: `Leaf_KWModularity`.

**L16. Shimura's `A_f` and the Eichler–Shimura relation.** The `λ`-adic representation of a
newform of level `N` (Tate normalization) is a constituent of `V_ℓ(J₁(N))`. Shimura, J. Math.
Soc. Japan 25 (1973), Thm 1 (AUDIT-READ); Shimura 1971, Thm 7.9; `K_f`-linear form: Ribet 1977,
Diamond–Im 1995 §12.5 (UNVERIFIED). Consequence (rv-h-a9c9 R-C9-1). Statable: with new
definitions (very large, for `J₁(N)`). Lean: `Leaf_ShimuraAf`.

**L18. Carayol.** For a newform `f` of level `N` and `p ≠ ℓ`, `v_p(N)` is the conductor exponent
of `ρ_{f,λ}` at `p`. Carayol, Ann. Sci. ÉNS 19 (1986), Théorème (A) (UNVERIFIED that it covers
`F = ℚ` at every `p ≠ ℓ`, h-trust D5). Exact at `F = ℚ`. Statable: with new definitions
(large). Lean: `Leaf_Carayol`.

**L21. Javanpeykar.** `h_F(Jac X) ≤ 13·10⁶ g·deg_B(X)⁵`; for `X = X₁(N)` with
`g, deg_B ≤ N²`: `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²`. Algebra Number Theory 8 (2014), Thm 1.1.1, §2.3
(ASTRA-READ). Consequence (the bounds on `g` and `deg_B` are elementary, N5 L868-876). Statable:
with new definitions (very large). Lean: `Leaf_Javanpeykar`.

**L22. Gaudron–Rémond.** Isogenous `A, B/K` admit an isogeny `A → B` of degree at most
`κ(A) = ((14g)^{64g²}[K:ℚ] max(h_F(A), log[K:ℚ], 1)²)^{1024g³}`. Duke Math. J. 163 (2014),
Thm 1.4 (ASTRA-READ). Exact (logarithmic form in Lean). Statable: with new definitions (very
large). Lean: `Leaf_GaudronRemond`.

**L23. Faltings: height under isogeny.** `|h_F(A) − h_F(B)| ≤ ½ log deg φ`. Faltings 1983,
Lemma 5; Raynaud, Astérisque 127 (1985), Exp. VII (UNVERIFIED numbers). Exact. Lean:
`Leaf_FaltingsIsogenyHeight`.

**L24. Additivity.** `h_F(A × Z) = h_F(A) + h_F(Z)`. Raynaud 1985, Exp. VII, Cor. 2.1.3
(VERIFIED as GR11's citation, h-leaves §4.5). Exact. Lean: `Leaf_HeightAdditive`.

**L25. Bost's lower bound.** `h_F(A) ≥ −(3/2)·dim A`. Bost, Sém. Bourbaki 795 (1996); in the form
`h_F ≥ −log(π√2)·dim`: Gaudron–Rémond, Comment. Math. Helv. 89 (2014), Cor. 8.4, or GR14 §9
(ASTRA-READ). Consequence (`log(π√2) < 3/2`). Lean: `Leaf_BostLower`.

**L26. Pazuki.** For principally polarized abelian surfaces, the theta height and the Faltings
height satisfy `h_Θ ≤ ½X_D + C₂ log(X_D + 2)`. Bull. SMF 140 (2012), Cor. 1.3(2) with
`g = r = 2` (ASTRA-READ). The Lean form `h([z_m]) ≤ 10⁴·2²⁴·max(1, h_F(A))` is a consequence
(N5 L934-947). Statable: with new definitions (very large). Lean: `Leaf_Pazuki`.

**L27. The Hauptmodul in theta constants.** On the QM locus, `ψ₄ = 144j`, `χ₁₀ = −j³/4`, and with
Igusa's theta expressions `j·(∑z_m⁸)⁵ = 3779136·(∏z_m)⁴`. Lin–Yang, Math. Z. 295 (2020), eqs.
(13)-(14), Example 30; Igusa, Amer. J. Math. 89 (1967), pp. 833-834, 848; Lauter–Naehrig–Yang
(2015) §2.2; exact check `scratch/h-v14/igusa_check.py` (h-trust F1). Consequence (two papers
and a computation; it could be split into L27a Lin–Yang and L27b Igusa). Statable: with new
definitions (large plus very large). Lean: `Leaf_IgusaLinYang`.

### Library leaves (formalized in Tau Ceti or Stacks; prereq-survey §1)

**L5. Zariski–Nagata purity.** SGA 1, Exp. X, Thm 3.1. Stacks 0BMB, proved in StacksFrontier
(unreviewed). Exact. Statable with new definitions (medium: the Stacks port).
**L6. Abhyankar's lemma.** SGA 1, Exp. XIII, 5.3; Grothendieck–Murre, LNM 208. Stacks 0EYG
(StacksFrontier). Exact. Same.
**L15. Twists and newforms.** A finite-order twist of a newform's representation is a newform's
representation: Shimura 1971, Prop. 3.64; Li, Math. Ann. 212 (1975), Thm 5; Atkin–Li 1978. Tau
Ceti (`HeckeRing.GL2.Newform.primitiveTwist` and neighbours). Consequence. Lean:
`Leaf_NewformTwist` (over placeholders, since Mathlib has no newforms).
**L17. Skolem–Noether.** Reiner, *Maximal orders*, Thm 7.21. Tau Ceti `TauCeti.skolemNoether`.
Exact. **Statable now**; Lean: `Leaf_SkolemNoether` (concrete).
**L19. The Brauer group of `ℚ`.** (a) Hasse principle and (b) Hilbert reciprocity for quaternion
algebras (Albert–Brauer–Hasse–Noether; Tau Ceti `brLocalization_injective`,
`sumLocalInv_brLocalization_eq_zero`); (c) `H²(G_ℚ, ±1) = Br(ℚ)[2]` and the local square-root
criterion (Milne, *Arithmetic duality theorems*, Ch. I; local class field theory). Exact.
(a), (b) **statable now** (`Leaf_HasseQuaternion`, `Leaf_HilbertReciprocity`, concrete); (c) with
new definitions (medium: continuous cohomology of `G_ℚ` exists in Mathlib, the identification
does not).
**L20. Kronecker–Weber.** Washington, Thm 14.1. Tau Ceti `kroneckerWeber`. Exact. **Statable
now** (`Leaf_KroneckerWeber`, concrete).
**L28a. Chebotarev.** Neukirch VII.13.4. Tau Ceti. Exact. Statable with new definitions (cheap:
Frobenius elements in `G_ℚ`).

### Textbook leaves (classical; not in any library)

**L9. Mumford, *Abelian varieties* (1970), §19.** (a) `rank Hom(A, B) ≤ 4 dim A dim B` (Thm 3);
(b) Poincaré reducibility (Thm 1); (c) the characteristic polynomial of an endomorphism on
`V_ℓ` is rational and independent of `ℓ` (Thm 4). Numbers UNVERIFIED. Exact. (a) in Lean as
`Leaf_MumfordRank`; statable with new definitions (medium).
**L10. Complex uniformization, GAGA, rigidity.** Polarizable complex tori are abelian varieties,
analytic homomorphisms are algebraic, and `Hom(A, B) = Hom(A_K, B_K)` for `k = k̄ ⊂ K`: Mumford
§§1-3; Serre, Ann. Inst. Fourier 6 (1956); Conrad, Enseign. Math. 52 (2006), §3 (UNVERIFIED).
Exact. Statable: no (needs complex-analytic spaces; very large).
**L11. Néron mapping property for abelian schemes.** A homomorphism of generic fibres of abelian
schemes over a Dedekind base extends. Bosch–Lütkebohmert–Raynaud, *Néron models* (1990), §1.2,
Prop. 8 (UNVERIFIED). Exact. Statable with new definitions (medium; Anthropic FLT has Néron
models in a special case).
**L28b. Brauer–Nesbitt.** Curtis–Reiner (1962), (30.16) (UNVERIFIED). Exact (characteristic zero,
semisimple). **Statable now** (`Leaf_BrauerNesbitt`, concrete).
**L29. Local fields.** Serre, *Corps locaux*: the bound on the different (III §6), Herbrand's
function and upper numbering (IV §§1-3, the subgroup formula), the Artin–Swan conductor and its
invariance under duality (VI §2); Silverman, AEC, IV.6.4 (formal logarithm). Tau Ceti has upper
numbering, Herbrand and Artin conductor exponents for finite Galois extensions. Exact. Statable
with new definitions (medium: conductors of `ℓ`-adic representations).

Counting: 18 deep (L1-L4, L7, L8, L12-L14, L16, L18, L21-L27), 7 library (L5, L6, L15, L17,
L19, L20, L28a), 5 textbook (L9-L11, L28b, L29) = 30 numbered items. Removed from the trust base relative to h-trust: Pan; Scholze (with
corrigendum) or Faltings 1989/Tsuji 1999; Fontaine, Astérisque 223; Berger 2002; Saito 1997 or
Kato 2004 or Scholl 1990; Deligne–Serre 1974; the Betti–étale comparison (C5).

## 4. The glue

"Lean" = provability in Lean once the definitions of §5 exist; size tiers: small (< 300 lines),
medium (300-2000), large (2000-10000), very large.

| Glue | Statement | Inputs | Origin | Lean | Size |
| --- | --- | --- | --- | --- | --- |
| G0 | Definitional facts used everywhere: base-change invariance of the stable `h_F`; `V_ℓ(A × Z) = V_ℓA ⊕ V_ℓZ`; isogenies induce isomorphisms on `V_ℓ`; height of a rational number is unchanged in extensions | the definitions | standard | yes, with the definitions | medium |
| G1 | A1, A3: the Gram matrix of `Trd(μ⁻¹xȳ)` has determinant 1; `|(𝒪/3𝒪)^*| = 72`; `deg(Y₃ → P¹_j) ≤ 324` | L1, L2, Vignéras (local normalizers) | Glazer + scripts | the matrix and the unit count: **yes now** (finite computations over `ℚ` and `𝔽₃`); the degree: needs Shimura curves | small / large |
| G2 | Lemma PR(i): for `u ∉ 𝒞`, the fibre field `K` over `J(u)` is Galois, `[K:ℚ] ∣ 144`, unramified outside `T` (including: `J(u)` is not a branch value) | L1-L3, L5, L6, scripts `b1_checks.py`, `branch_check.py` | repository (h-b1; rv-h-b1) | needs the model `Y₃ → P¹_j` over `ℤ[1/6]` | large |
| G3 | Lemma PR(ii): good reduction at every `v ∤ 3` of `K`, also for every conjugate | L2, L7, L8 (Thm 2), torsion-freeness of `1 + 3M₄(ℤ₃)` | repository | yes, with the definitions | medium |
| G4 | A7: the conjugates of `A` are isomorphic over `ℚ̄` | L1, the Igusa vector (L27a) | Glazer | needs Igusa invariants of genus-two curves (statable now) and L1 | medium |
| G5 | A8: the Hom field `L`, `[L:ℚ] ≤ F₀·3^{r²} ≤ D`, unramified outside `T` | L8, L9(a), Minkowski's lemma (elementary; statable now) | Glazer | yes | medium |
| G6 | A9: `End⁰(A_ℚ̄) ∈ {B, M₂(k)}` | L10, centralizer computation | Glazer | needs L10 | medium |
| G7 | NoCM | L3, L4, script `rv-h-cm/check.py` | repository (h-cm) | needs Shimura curves | large |
| G8 | B1: sign cocycle `ε` with values `±1`, inflated from `Gal(L/ℚ)` | L17 | Glazer | yes | medium |
| G9 | B2: `[ε]` vanishes outside `T`; Dirichlet `χ` with the same local invariants, order `m ≤ 2R^R M` | L19, local class field theory, script `c2_sqrt_criterion.py` | Glazer (repair R1 of rv-h-novel) | yes (Tau Ceti has the inputs) | medium |
| G10 | B3: the cochain `β`, `[L':ℚ] ≤ QM` | G9; script `c1_constants.py` | Glazer | yes | small |
| G11 | C1-C2: `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ` on `G_{L'}`, `r_ℓ` absolutely irreducible | L12 | Glazer | yes | medium |
| G12 | C6: `r_ℓ` unramified outside `T ∪ {ℓ}` | G2, G3, G5, G10, L8 | Glazer | yes | small |
| G13 | **new**: `r₅ ≅ ρ_{f,λ}` for a weight-two newform `f` (§1.2) | G6-G8, L12, L13, L14, L15, L20; twist lemma | this note | yes | medium |
| G14 | C9: Galois conjugates of `f` are new; `r₅` is a constituent of `V₅(A_f)` | L15, L16, L28 | Glazer (rv-h-a9c9) | yes | medium |
| G15 | C10: `r₃`, `r₅` and `ρ_{f,λ}` form one compatible system | L8, L9(c), L11, L28 | Glazer | yes | medium |
| G16 | D1-D4: conductor exponents `a_p(r) ≤ E₀` for `p ≤ R`, `≤ 2` for `R < p ∈ T`, `0` outside `T` | L7, L29, script `c3_breaks.py` | Glazer (repairs R2-R3 of rv-h-novel) | yes; Glazer's inequalities alone ≈ 300 lines | large |
| G17 | D5: `N ≤ ∏_{p≤R} p^{E₀}·M² ≤ QM²` | G16, L18 | Glazer | the product: **yes now** | small |
| G18 | E1: an `L'`-isogeny `A × Z → J₁(N)` | G14, L9(b), L12, L16 | Glazer | yes | medium |
| G19 | E2-E4: `max(1, h_F(A)) ≤ Q¹⁷M²⁴` | L21-L25, G0 | Glazer | the arithmetic is **proved** (`transfer_numerics`, `scratch/wk-h/Arakelov.lean`) | small |
| G20 | F1-F3: `h(J(u)) ≤ (40·10⁴·2²⁴ + 22)·max(1, h_F(A))` | L26, L27; F2 from Mathlib's `logHeight_eval_le` | Glazer | yes | medium |
| G21 | F4 and the final constant: `JHeightBound → SixContactMin` | — | Glazer, strengthened | **proved** (`JHeight.lean`; `sixContactMinAt_of_jHeightBoundAt` here) | done |

The top-level statement is `jHeightBoundAt_of_leaves` in Leaves.lean: for admissible `S`, the
stated leaves together with `GeometricInput` imply `JHeightBoundAt S` (`sorry`).

## 5. Definitions

| Definition | Needed by | Status | Tier |
| --- | --- | --- | --- |
| Number fields, `G_K` with Krull topology, `ℚ_p`, heights on `Pⁿ(K)`, quaternion algebras, CSAs, cyclotomic fields | L17, L19, L20, L28b, G20, G21 | **Mathlib** (used in Leaves.lean) | — |
| Abelian variety over a field | almost all | **defined** in Leaves.lean (`AbelianVariety`: Mathlib `GrpObj` in `Over (Spec K)` + proper + smooth + geometrically integral); dimension via `SmoothOfRelativeDimension`. Tau Ceti has a richer version | cheap |
| Continuous Galois representations, intertwiners, semisimplicity, irreducibility, isomorphism | L8, L12-L18, L28b | **defined** in Leaves.lean (`GalRep`) | cheap |
| Points over extensions, torsion, `V_ℓ(A)` with `G_K`-action | L7, L8, L12-L16 | missing (`tateRep` opaque) | large |
| `Hom(A, B)` as a group, its rank; isogenies and their degree; products; base change; quotients | L9, L12, L22-L24, G0 | missing (opaque `homRank`, `IsIsogenyOfDegree`, `IsProductOf`, `IsBaseChange`, `IsQuotientOf`) | medium |
| Good / potentially good reduction at a place | L7, L8, G3 | missing (opaque) | medium |
| Inertia and decomposition groups in `G_K`; unramified representations; Artin conductor of an `ℓ`-adic representation | L8, L18, G12, G16 | missing (opaque `IsUnramifiedAt`, `condExp`); Tau Ceti has upper numbering and conductors for finite extensions | medium |
| `GL₂`-type; building blocks; `ℚ̄`-factors | L13, L14, G13 | missing (opaque) | medium-large |
| Weight-two newforms and their `λ`-adic representations | L14-L18 | missing in Mathlib (opaque `Newform2`, `IsGalRepOf`); newforms in Tau Ceti; the representations nowhere | large |
| The modular curve `X₁(N)` over `ℚ` and its Jacobian | L16, L21, G18 | missing (opaque `IsJ1`); Jacobians in Anthropic FLT | very large |
| Faltings height (stable) | L21-L26 | missing (opaque `faltingsHeight`) | **very large** |
| Theta constants of a ppav with a level-2 structure over a number field | L26, L27 | missing (opaque `IsEvenThetaNulls`) | large |
| Shimura curves of `𝒪`, level-3 model, canonical model, CM points, Atkin–Lehner quotient, Hauptmodul | L1-L4, G1-G4, G7 | missing (opaque `IsQMFibre` covers only the fibre relation); Anthropic FLT has QM moduli (prereq-survey) | very large |
| Igusa invariants of a genus-two curve | G4, L27a | missing; polynomials in the sextic's coefficients | cheap-medium |
| Schemes over `ℤ`: purity, tame ramification | L5, L6, G2 | in StacksFrontier | medium (port) |
| Complex-analytic uniformization | L10 | missing | very large |

## 6. Risks

- **R1 (new route, statements).** L13 and L14 are recalled, not read. Ribet's theorem is in a
  proceedings volume (refereed status UNVERIFIED); its exact form, and whether it needs the
  compatibility of the `μ_σ` with all of `End⁰` (B1 gives it), must be read in Ribet 1992 and
  Pyle 2004. If L13 turned out to be unpublished in this form, the fallback is h-trust's C3-C8
  (six leaves) for that block only; nothing else changes.
- **R2 (new route, argument).** §1.2 has had no review. A model review should check the twist
  lemma, the semisimplicity step on `G_K`, and that Carayol is applied to the newform of the same
  `r_ℓ` whose conductor G16 bounds.
- **R3 (inherited).** G2-G3 (Lemma PR), G7 (NoCM), G8-G10, G15-G16 are model-reviewed only
  (h-trust §2.1). The decomposition makes them proof obligations for Lean, which would remove
  this risk once formalized, but they need the very large Shimura-curve layer.
- **R4 (locators).** About 40 locators remain UNVERIFIED and about ten ASTRA-READ (h-trust §2.5),
  including GR14, Javanpeykar and Pazuki, whose exact constants enter the numerics.
- **R5 (vK route not closed).** If von Känel's bound has polynomial dependence on the dimension,
  a much shorter route exists (§1.1); this note could not read it.
- **R6 (Lean faithfulness).** Sixteen of the 21 Lean leaves are over `opaque` placeholders. They
  are faithful only after each placeholder is replaced by the genuine definition, and the glue can
  be proved only then. Over arbitrary interpretations the hypotheses say no more than a height
  bound (wk-h §4.3). `GeometricInput` is a weak consequence of L1-L2 standing in for the four
  Shimura-curve leaves, which are not stated.
- **R7 (count).** The owner's "about ten" is not met: 18 deep leaves. Merging (for example
  "Faltings 1983" for L12 and L23, or "Arakelov package" for L21-L25) would reach about ten names
  but hide distinct theorems.

## 7. First steps for a Lean team

1. **Read two papers before committing** (needs network): von Känel arXiv:1310.7263 (main
   theorem: dependence on `dim`, publication), and Ribet 1992 / Pyle 2004 (exact form of L13).
2. **Adopt the concrete layer now**: `AbelianVariety`, `GalRep` and the five concrete leaves of
   Leaves.lean; prove `Leaf_HasseQuaternion`, `Leaf_HilbertReciprocity`,
   `Leaf_KroneckerWeber`, `Leaf_SkolemNoether` by porting Tau Ceti, and `Leaf_BrauerNesbitt`.
3. **Small glue provable today**: G1's matrix and unit counts, G5's Minkowski lemma, G17's
   product `N ≤ QM²`, G10's constants, and moving `transfer_numerics` (G19) and F2 (G20) into
   the kernel tree.
4. **Medium definitional layer** (abelian-variety homomorphisms, isogenies, products, base change,
   good reduction, Tate modules) unlocks L7-L9, L12 and the statements of L13-L14, and the glue
   G3, G5, G8-G15, G18.
5. **The three very large layers are independent and can be crowdsourced in parallel:**
   (a) the Faltings height (L21-L26); (b) modular curves, `J₁(N)` and newform representations
   (L14-L18); (c) Shimura curves of `𝒪` (L1-L4, G1-G4, G7).
6. **Request a model review of §1.2** (the modularity substitution) before it is adopted in
   `docs/research/h-trust.md`.

## Changelog

- 2026-11-11: first version (task hdec-alt).
