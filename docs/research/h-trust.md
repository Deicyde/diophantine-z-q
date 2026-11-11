# h-trust: a trust statement for H that uses no unpublished supplement

Status: research note (task h-trust, 2026-11-11; task T3 of `docs/research/h-map.md`). It turns the
routes of h-map §3.2 (B1-B5), the review rv-h-novel and the earlier H notes into one numbered
outline of the proof of Theorem 4.1, in the form `ZInQ.SixContactEstimate` states it. For each
step it names the supplier and gives the status. It then lists what remains outside refereed
sources (§2) and drafts the replacement docstrings for the two Lean hypotheses (§3). The work log
and the rerun outputs are in `scratch/h-trust/`.

Sources used. All of them are in the repository or on fleet branches. No source outside the
repository could be read (there is no network).

- The frozen 11/5 manuscript `diophantine_zq.tex` (commit 97cec7fd, sha256 `cb1148cd6c77…`).
  "N5 Lxxx" refers to its lines. The proof of Theorem 4.1 is N5 L405-964, and its appendix lemma
  is N5 L10939-11000.
- On main: `h-map`, `h-leaves`, `h-v14`, `h-a011` with `rv-h-a011`, `h-cm` with `rv-h-cm`, and
  `docs/reviews/height-replacement/` (the Astra reviews).
- `origin/wip/h-b1:docs/research/h-b1.md` (route B1; its review branch `wip/rv-h-b1` has no commit
  yet, so the note is **unreviewed**).
- `origin/wip/rv-h-novel:docs/research/rv-h-novel.md` (review of the novel steps, repairs R1-R3).
- The Lean files `ZInQKernel/Hypotheses/Height.lean` and `ZInQKernel/Hypotheses/HeightMin.lean`.

Marks:

- **VERIFIED**: checked in this task, against N5, a repository note or the Lean source, or by
  rerunning a repository script and comparing its output with the saved one.
- **STANDARD**: a published theorem, cited with a locator.
- **UNVERIFIED** (after a locator): no one in this repository has read the source at that place.
  The text says where to check it.
- **SPECULATIVE**: an assessment.

Status of a step (the weakest of its suppliers):

- **[R] refereed**: a theorem in a refereed journal, an Astérisque, SGA or LNM volume, or a
  standard monograph.
- **[P] published but unrefereed**: lecture notes or a preprint. This is used only where N5
  cites such a version today. In every case §2.4 names a refereed replacement.
- **[M] repository argument reviewed by a model only**: N5's own text, or a repository note,
  with the model review named. "Astra" means the four scoped Astra reviews of the **11/4** text
  (sha256 `bfc4192d…`, not N5; rv-h-novel, Provenance).
- **[U] unchecked**: a repository argument that no independent review has read.
- **[S] script**: an exact computation in the repository with its output saved. "rerun" means
  it was rerun here and gave identical output (log, Step 9).

## Summary

1. **The outline (§1)** has 36 steps in six parts: geometry, scalar descent, modularity,
   conductor, transfer, and the return to `u`.
   - 7 steps rest only on refereed theorems and verified scripts: A1, A2, C4, D5, E2, E3, F1.
   - 5 steps apply a refereed theorem through bookkeeping that has had only a model review:
     C2, C7, C9, E4, F3.
   - 21 steps are N5 or repository arguments reviewed by models only. They are covered by
     rv-h-novel (N5 text), Astra (11/4 text), rv-h-a011 (Version 14 text) or rv-h-cm.
   - 3 steps (A4-A6) are **unchecked**. They are the step-A4 identification of N5's level-three
     curve with the moduli scheme, and h-b1's Lemma PR (i) and (ii), which replace the integral
     model.
2. **No unpublished supplement is used.**
   - `direct-p5` was never cited by N5, which applies Pan's Theorem 1.0.4 directly at L756.
     h-a011 is needed only for its hypothesis check.
   - `a001`, `ly-d6` and `igusa-theta` are replaced by Baba–Granath 2008, Lin–Yang 2020,
     Igusa 1967 and Lauter–Naehrig–Yang 2015, read through `scratch/h-v14/form_check.py` and
     `igusa_check.py` (both rerun, identical output).
   - `b11` and Buzzard 1997 (N5 L443-530) are replaced by h-b1's Lemma PR.
3. **Two choices that shorten the trust base (VERIFIED as reasoning).**
   - **(D1)** Potential semistability is taken as N5 has it: Scholze's de Rham comparison with
     Berger's monodromy theorem. It is not taken from Lemma PG plus the crystalline comparison
     (h-leaves R5.2(b)). The reason is that Scholze 2013 and Berger 2002 are refereed and need
     no new repository argument, while Lemma PG would add one.
   - **(D2)** Semisimplicity, the endomorphism theorem and the Hom theorem are taken from
     Faltings 1983, not from GR14 plus Tate's argument (h-leaves R5.1). With this choice the
     non-circularity of GR14 (h-map W4) no longer matters: GR14 is used only for its explicit
     isogeny bound, and its correctness, like that of any refereed theorem, is accepted as
     published.
4. **What remains outside refereed sources (§2):**
   - (a) N5's own arguments. These are W1: the descent, the conductor bound and the transfer,
     plus the geometric bookkeeping. They have model reviews only.
   - (b) Two repository replacements: NoCM (model-reviewed) and Lemma PR (not yet reviewed).
   - (c) One identification: step A4, N5's `Y₃` as the fine moduli scheme over `ℚ`.
   - (d) Seven exact scripts.
   - (e) Five unrefereed editions cited by N5, each with a refereed replacement named.
   - (f) About 40 locators that are UNVERIFIED, with places to check them (§2.5).
   - (g) The policy that the works cited inside Pan's proof are not leaves.
5. **Drafts (§3).** The replacement module docstring and hypothesis docstring for
   `Hypotheses/Height.lean` (`SixContactEstimate`) and `Hypotheses/HeightMin.lean`
   (`SixContactMin`), and a supplement-free H row for KERNEL_PLAN.md. The Lean files were not
   edited.
6. **Minor finding (VERIFIED).** rv-h-novel's line numbers for its steps 5-8 are off by about
   +22. In N5 the break bound is L796-812, semistability and odd `p` L813-823, the `p = 2`
   paragraph L823-846, and the conductor exponents with `N ≤ QM²` L846-857. Its steps 1-3 and 9,
   and its scope line, are right.

## 0. The statement, and the route through the proof

**Statement (VERIFIED).** `SixContactEstimate` (`Hypotheses/Height.lean`, the last definition) is
N5 Theorem 4.1 (L398-403) with the constants of N5 L388-397. The match was checked numeral by
numeral in h-leaves §5.2 and rechecked here by reading. `SixContactMin` is its instance
`S = S_mul`, `R = D` (`sixContactMin_of_sixContactEstimate`, `ZInQKernel/Main.lean:70`). The proof
below is uniform in admissible `S` and `R`, so it proves both.

**Route (the decisions; reasons in the Summary).**

| Part of N5 | Supplier in this outline | Removes |
| --- | --- | --- |
| L405-441, datum and quotient | N5 text, with BG 2008 and LY 2020, through `form_check.py` | `a001` (form part) |
| L443-530, integral model, `K`, good reduction | h-b1 Lemma PR (route B1) | `b11`, Buzzard 1997, uncited scheme theory (A078) |
| L531-577, conjugates, Hom field, dichotomy | N5 text | — |
| L578-631, CM branch | NoCM (rv-h-cm §7.2), route B5 | Fowler, Barquero-Sanchez et al., the CM use of GR14 |
| L632-716, scalar descent | N5 text, with rv-h-novel repair R1 | — |
| L719-795, modularity | N5 text: Pan Thm 1.0.4, Scholze + Berger (D1), Faltings (D2); hypothesis check from rv-h-a011 §3.1; citations per rv-h-a011 R1-R2; route B2 | `direct-p5` (never in N5); Conrad's preprint replaced by Serre 1968 |
| L796-857, conductor | N5 text, with rv-h-novel repairs R2-R3; Carayol 1986 for I1 (B4) | — |
| L860-905, transfer | N5 text; GR14 for the explicit bound only (D2) | the W4 dependency |
| L908-964, back to `u` | N5 text, with LY, LNY, Igusa, Pazuki, through `igusa_check.py`; route B3 | `ly-d6`, `igusa-theta` |

## 1. Numbered outline of the proof of Theorem 4.1

Notation as in N5 and h-map:

- `T = S ∪ supp M`, with `M = M_S(u)`;
- `K` is the fibre field, `L` the Hom field and `L'` the descent field;
- `Q = Q_R = R^{R E₀}`;
- `r_ℓ` is the two-dimensional constituent, and `f` the newform of level `N`.

Each step gives N5 lines, content, supplier(s) with locator, and status.

### Part A. Geometry: from `u` to an abelian surface with good reduction outside `T`

**A1. QM datum** (N5 L410-420).
- *Content.* `B = (2,−3)`, `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` and `μ = 2j + ij`.
  `Trd(μ⁻¹xȳ)` has the displayed Gram matrix, with determinant 1, and Rosati involution
  `a ↦ μ⁻¹āμ`.
- *Suppliers.* The algebra is `scratch/h-v14/form_check.py`, with output `form_check.output.txt`
  (rerun, identical). The Riemann-form convention is Lin–Yang, *Quaternionic loci in Siegel's
  modular threefold*, Math. Z. 295 (2020), eq. (3) and Lemma 3. Locator UNVERIFIED in the journal
  version; N5 cites arXiv:1807.00466v1. Uniqueness of the principal polarization with a given
  Rosati involution is not needed, since the form is written down.
- *Status:* **[S]+[R]**.

**A2. Quotient and branch data** (N5 L420-422; the labelling of `j` at L908-909).
- *Content.* The normalizer quotient of the discriminant-six curve is `P¹_j`. Its branch values
  are `0, ∞, −16/27`, with indices `4, 6, 2`, at the CM points of discriminants `−4, −3, −24`.
- *Suppliers.*
  - Baba–Granath, *Genus 2 curves with quaternionic multiplication*, Canad. J. Math. 60 (2008),
    §2.1 (Thm 2.1) and §3. UNVERIFIED: N5 cites the 2005 MPI preprint, and Version 14 records a
    "local index slip" in its Lemma 3.1 (h-v14 §2.2). Step A3 does not use that lemma.
  - Lin–Yang 2020, Example 30. VERIFIED in arXiv v1 by h-v14; the journal number is UNVERIFIED.
  - Independent check of the elliptic-point data: rv-h-cm §2.3 derives Elkies' twist constants
    from Shimura reciprocity at the three elliptic points.
- *Status:* **[R]**.

**A3. Level three, the normalizer action, and the degree** (N5 L423-441).
- *Content.*
  - `|N/(𝔸_f^* K₀)| = 4`.
  - Central ideles act trivially on `Y₃`.
  - `Γ' = N/(𝔸_f^* K₃)` acts on `Y₃` over `ℚ` with quotient `P¹_j`.
  - `deg(Y₃ → P¹_j) ≤ 4·|(𝒪/3𝒪)^*| ≤ 324`.
- *Suppliers.*
  - The local normalizers: Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800 (1980),
    Ch. II. Locator UNVERIFIED; check the normalizer of a maximal order at a ramified prime.
  - `|(𝒪/3𝒪)^*| = 72`: `form_check.py` (rerun), and `origin/wip/h-b1:scratch/h-b1/b1_checks.py`
    §B (rerun, identical).
  - The action over `ℚ`: Deligne, *Variétés de Shimura*, Proc. Sympos. Pure Math. 33 (1979),
    §2.7 and §5 (UNVERIFIED).
- *Status:* **[M]** (Astra "whole"; h-b1 M1-M3 restates it, unreviewed). The ingredients are [R]
  and [S].

**A4. Moduli interpretation over `ℚ`** (used at N5 L528, "choose a fibre"; h-b1 §4(ii) step 1).
- *Content.* `Y₃` is the fine moduli scheme over `ℚ` of `(A, ι: 𝒪 → End A, λ, η)`, with `λ`
  principal of the type fixed by `μ`, and `η: 𝒪/3𝒪 ≅ A[3]` an `𝒪`-linear isomorphism. `K₃` is
  neat.
- *Suppliers.*
  - Shimura, *Construction of class fields and zeta functions of algebraic curves*, Ann. of
    Math. 85 (1967).
  - Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §4.
  - Kottwitz, J. Amer. Math. Soc. 5 (1992), §5.
  - Milne, *Introduction to Shimura varieties* (Clay Math. Proc. 4, 2005), §8 and §14. These
    are published lecture notes; the first three suffice.
  - All locators UNVERIFIED.
- *Open point.* That N5's `Y₃ = Sh_{K₃}` "with all its determinant components" is this moduli
  scheme, polarization type included, is stated in N5 only through the integral-model
  construction (L465-476). It is standard but not written down (h-b1 §6 item 5).
- *Status:* **[U]** for the identification; [R] for the inputs.

**A5. Lemma PR(i): the fibre field** (replaces N5 L443-528; h-b1 §§1.2, 2-4).
- *Content.* `K`, the splitting field of the fibre over `J(u)`, is Galois over `ℚ` with
  `[K:ℚ] ≤ 324!` (in fact dividing 144, by h-b1 M3). It is unramified at every `p ≥ 17` unless
  some `v_p(u−c)` is positive and odd. Hence it is unramified outside `T`.
- *Suppliers.*
  - Prop. TS (h-b1 §1.2), proved from:
    - Zariski–Nagata purity, SGA 1, Exp. X, Thm 3.1;
    - Abhyankar's lemma, SGA 1, Exp. XIII, 5.3, and Grothendieck–Murre, LNM 208 (1971).

    Locators UNVERIFIED. Beckmann, J. reine angew. Math. 419 (1991), is cited for attribution
    only.
  - Lemma NV (h-b1 §3), from:
    - Shimura reciprocity for CM points on the canonical model (Deligne 1971 §3, UNVERIFIED);
    - maximality of the three CM orders (`b1_checks.py` §C, rerun);
    - the Atkin–Lehner group `W ≅ (ℤ/2)²` (Baba–Granath 2008).
  - The case analysis at `p ≥ 17`: `G⁶ − 97200F² = H²`, the resultant and discriminant supports,
    `J(∞)` and a sample of 30 cases (`b1_checks.py` §§A, E, rerun, identical, "all 30 agree:
    True"; also `scratch/h-map/beckmann_check.py`).
- *Status:* **[U]**. It is a repository argument with no review yet; `wip/rv-h-b1` has no
  commit. Its inputs are [R] and [S].

**A6. Lemma PR(ii): good reduction** (replaces N5 L529-530; used again at L556-559, L752-754,
L781 and L849-850).
- *Content.* `A` has good reduction at every finite place `v ∤ 3` of `K`, and so do all its
  conjugates `σA = A_{σx}`.
- *Suppliers.*
  - A4 gives `A[3] ⊂ A(K)`.
  - Potentially good reduction: Grothendieck's semistable reduction theorem (SGA 7 I, LNM 288,
    Exp. IX, Thm 3.6) plus the toric-part argument of h-b1 §4(ii) step 2. Alternatively Morita,
    Hokkaido Math. J. 10 (1981). Locators UNVERIFIED.
  - Finiteness of `ρ(I_v)` and Néron–Ogg–Shafarevich: Serre–Tate, *Good reduction of abelian
    varieties*, Ann. of Math. 88 (1968), Thms 1-2. Locator UNVERIFIED.
  - `1 + 3M₄(ℤ₃)` is torsion-free (elementary; N5 L468-470).
- *Status:* **[U]** (h-b1, unreviewed). Its inputs are [R].

**A7. The conjugates of `A` are geometrically isomorphic** (N5 L532-543).
- *Content.* Baba–Granath's polarized relation gives `V_ℤ = V/W`. On the finite nonzero
  `j`-locus the polarized point is determined by
  `[J₂, J₄, J₆, J₁₀] = [12(j+1), 6(j²+j+1), 4(j³−2j²+1), j³]`. And `j = J(u)` is rational, finite
  and nonzero.
- *Suppliers.*
  - Baba–Granath 2008, Thm 2.1 (UNVERIFIED).
  - The Igusa vector: Lin–Yang 2020, eqs. (13)-(14) and Examples 29-30, through
    `scratch/h-v14/igusa_check.py` (rerun, identical).
  - `F(u) ≠ 0`, and `disc G = −10800 < 0`.
- *Remark.* An isogeny between the conjugates would suffice (rv-h-novel, Premises). Under A4
  the conjugates are `A_{σx}` with `σx` in one `Γ'`-orbit, so they are related by Hecke
  translates, hence isogenous (STANDARD; it would make A7 independent of the Igusa vector;
  SPECULATIVE simplification).
- *Status:* **[M]** (Astra "whole"). Its inputs are [R] and [S].

**A8. The Hom field `L`** (N5 L544-563).
- *Content.* `W₀ = Res_{K/ℚ} A` has geometric endomorphism rank `r ≤ 16F₀²`, with Galois acting
  through a finite group that injects into `GL_r(𝔽₃)`. For `L = EK`, `L/ℚ` is normal,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D`, and `L` is unramified outside `T`.
- *Suppliers.*
  - `rank Hom(A, A') ≤ 4·dim A·dim A'`: Mumford, *Abelian varieties* (1970), §19, Thm 3.
  - Finite subgroups of `GL_r(ℤ)` inject mod 3 (Minkowski's lemma; the same torsion-freeness
    of `1 + 3M_r(ℤ₃)` as in A6).
  - Néron–Ogg–Shafarevich (Serre–Tate Thm 1), at `p ∉ T` with `ℓ ≠ p`. This uses A5 and A6;
    for `p ∉ T` we have `p ≥ 17`, so `p ≠ 3`.
  - All locators UNVERIFIED.
- *Check here.* The arithmetic `16F₀²` and `F₀·3^{256F₀⁴} = D` was VERIFIED by reading.
- *Status:* **[M]** (Astra "whole"; h-leaves row 4 inventory).

**A9. The dichotomy** (N5 L564-577).
- *Content.* `End⁰(A_ℚ̄)` is `B` or `M₂(k)`.
- *Supplier.* Polarizable tori are abelian varieties and Hodge endomorphisms are algebraic.
  N5 cites Milne's course notes (Part I, Thms 2.8-2.9), which are [P]. A refereed replacement is
  Mumford 1970, §§1-3, or Milne, *Abelian varieties*, in Cornell–Silverman (eds.), *Arithmetic
  Geometry* (1986), §1. Locators UNVERIFIED.
- *Status:* **[M]** (Astra "whole"). The citation is [P] until it is swapped (§2.4).

**A10. NoCM: `End⁰(A_ℚ̄) = B` for every rational `u ∉ 𝒞`** (replaces N5 L578-631; rv-h-cm §7.2).
- *Suppliers.*
  - `t = 1 + 27j/16` and the model `ℚ(t)(√(−t), √(3(t−1)))`: forced by the `W`-action over `ℚ`
    and by Shimura reciprocity at the elliptic points (rv-h-cm §2.3). Elkies, ANTS-III, LNCS 1423
    (1998), §3.2, serves as a cross-check.
  - The fibre over `t(u)` is a free `W`-orbit with residue field `ℚ(i)`:
    `scratch/rv-h-cm/check.py` (rerun, identical).
  - González–Rotger, *Non-elliptic Shimura curves of genus one*, J. Math. Soc. Japan 58 (2006),
    Thm 5.12 and Prop. 5.6. Prop. 5.6 may be cited only under `(f, 6) = 1`. The numbers are
    those of arXiv:math/0612732 (VERIFIED by rv-h-cm); the journal numbering is UNVERIFIED.
  - Vignéras LNM 800 for the embedding condition (UNVERIFIED).
- *Repairs.* rv-h-cm R1-R5 must be applied when the CM paragraph is replaced.
- *Status:* **[M]** (h-cm + rv-h-cm).

### Part B. Scalar descent (N5 L632-716): rv-h-novel steps 1-3

**B1. Sign cocycle** (N5 L632-664).
- *Content.* `B`-linear isogenies `μ_σ` (Skolem–Noether), `c(σ,τ) ∈ ℚ^×`, `a_σ = (deg μ_σ)^{−1/4}`,
  and `ε ∈ {±1}`, a normalized cocycle inflated from `Gal(L/ℚ)`.
- *Supplier.* Skolem–Noether: Reiner, *Maximal orders* (1975), Thm 7.21 (UNVERIFIED).
- *Status:* **[M]** (rv-h-novel step 1; Astra "descent").

**B2. The Brauer step** (N5 L665-693).
- *Content.* `[ε] ∈ Br(ℚ)[2]` vanishes outside `T`. The Dirichlet character `χ` has the same
  local invariants, and `m ≤ 2R^R M`.
- *Suppliers.*
  - `H²(G_ℚ, ±1) = Br(ℚ)[2]`, the Hasse principle and reciprocity: Milne, *Arithmetic duality
    theorems* (Academic Press 1986; 2nd ed. 2006), Ch. I. Also Tate, Ch. VII of Cassels–Fröhlich
    (1967). Locators UNVERIFIED.
  - The square-root criterion: `origin/wip/rv-h-novel:scratch/rv-h-novel/c2_sqrt_criterion.py`
    (rerun: 135 characters, 0 mismatches; output saved in `scratch/h-trust/reruns/`).
- *Repair.* Repair R1 of rv-h-novel: state `ω_p(−1) = χ_p(−1)` explicitly.
- *Status:* **[M]** (rv-h-novel step 2; Astra "descent").

**B3. The cochain β and `[L':ℚ] ≤ QM`** (N5 L693-716).
- *Supplier.* The constants: `c1_constants.py` (rerun, saved).
- *Status:* **[M]** (rv-h-novel step 3; Astra "descent").

### Part C. Modularity (N5 L719-795)

**C1. The representation `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`** (N5 L719-731).
- *Content.* It is the Tate action on `G_{L'}`.
- *Status:* **[M]** (rv-h-novel step 4).

**C2. Absolute irreducibility of `r_ℓ|G_{L'}`** (N5 L731-734).
- *Supplier.* Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent.
  Math. 73 (1983), with erratum, Invent. Math. 75 (1984). Semisimplicity and the Tate
  conjecture for homomorphisms are its Satz 3 and Satz 4 (§5). N5 gives no locator; the numbers
  are UNVERIFIED and should be checked in §5 of the paper.
- *Status:* **[R]**. The commutant argument is [M] (rv-h-a011 §3.1 H2, against Version 14's
  identical argument).

**C3. de Rham with Hodge–Tate weights `{0, −1}`** (N5 L734-737; Lemma `lem:de-rham-descent`,
L10939-11000).
- *Suppliers.*
  - Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 and Thms 9.1, 9.3, with the corrigendum, Forum
    Math. Pi 4 (2016). UNVERIFIED in the journal; h-leaves read the arXiv introduction.
  - `V_ℓ(A) ≅ H¹_et(A_F̄, ℚ_ℓ)^∨`: N5 cites Milne's notes, Part I, Thm 12.1(a), which are [P].
    Replacement: Milne 1986 (Cornell–Silverman), §15, or Mumford §19.
  - Closure under duals and subquotients, and finite descent: N5 cites Brinon–Conrad, CMI notes
    (2009), Thm 5.2.1 and Props. 6.3.3, 6.3.8, which are [P]. Replacement: Fontaine,
    *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exp. VIII (UNVERIFIED).
- *Status:* **[M]** (Astra "descent"; read in h-leaves §3.1). The citations are [P] until they
  are swapped.

**C4. de Rham implies potentially semistable** (N5 L739-741).
- *Supplier.* Berger, *Représentations p-adiques et équations différentielles*, Invent. Math.
  148 (2002), Théorème 0.6 (= Théorème 5.19). This is VERIFIED in arXiv:math/0102179v3 by
  rv-h-a011 §3.2. The journal numbering is UNVERIFIED.
- *Status:* **[R]**.

**C5. Oddness** (N5 L742-751).
- *Content.* The Betti involution exchanges the Hodge summands, so `r_ℓ(c)` has eigenvalues
  `1, −1`.
- *Suppliers.* The comparison between Betti and `ℓ`-adic cohomology (Milne 1986, or SGA 4 XI).
- *Status:* **[M]** (Astra "descent"; rv-h-a011 §3.1 H5 for Version 14's version).

**C6. Finite ramification** (N5 L752-754).
- *Content.* `r_ℓ` is unramified outside `T ∪ {ℓ}`.
- *Suppliers.* A5, A6, A8, the cleanup of `β` (B3) and Néron–Ogg–Shafarevich.
- *Status:* **[M]**. It inherits [U] from A5 and A6.

**C7. Pan's theorem at `ℓ = 5`** (N5 L755-757).
- *Supplier.* Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, J. Amer.
  Math. Soc. 35 (2022), 1031-1169, cited as arXiv:1901.07166v2, Theorem 1.0.4.
  - The statement in arXiv v2 is VERIFIED by h-a011 and rv-h-a011.
  - The JAMS numbering is UNVERIFIED (repair R1 of rv-h-a011).
- *Hypotheses.*
  - continuity, irreducibility (C2), finite ramification (C6), pst at 5 (C3+C4), odd (C5) and
    distinct HT weights (C3);
  - `p = 5` makes the `p = 3` clause vacuous.

  The discharge table rv-h-a011 §3.1 was written for Version 14. It applies to N5 because the
  representation `r₅` and the hypothesis list are the same. Its route (c) is N5's route.
- *Policy.* This is repair R2 of rv-h-a011: the leaf is Pan's stated theorem. The works cited
  inside its proof (Skinner–Wiles 1999/2001, Kisin, Hu–Tan, Khare–Wintenberger) are not leaves.
- *Status:* **[R]** for the theorem; **[M]** for the hypothesis check.

**C8. The twist and the weight** (N5 L757-768).
- *Content.* The twisting character is de Rham and unramified almost everywhere, hence a finite
  character times an integral power of the cyclotomic character. Comparing `{0, −1}` with
  `{n, n+1−k}` gives `k = 2`, `n = 0`. The finite part is absorbed into `f`.
- *Suppliers.* Local algebraicity of Hodge–Tate characters: N5 cites Conrad's preprint (2011),
  App. B, pp. 32-33, which is [P]. Replacement: Serre, *Abelian ℓ-adic representations and
  elliptic curves* (1968), Ch. III (Tate's theorem on Hodge–Tate characters). Locator
  UNVERIFIED; check III-§1 and the appendix.
- *Check here.* `{n, n+1−k} = {0, −1}` with `k ≥ 1` forces `n = 0`, `k = 2`. The other matching
  gives `k = 0` (VERIFIED as an argument).
- *Status:* **[M]**, but only through Astra "descent" on the 11/4 text. rv-h-a011 checked Version
  14's different twist argument (Deligne–Serre / Kato), and rv-h-novel left this paragraph out
  of scope. It is the least-reviewed paragraph of Part C.

**C9. Newform and `A_f`** (N5 L768-774).
- *Suppliers.*
  - Li, *Newforms and functional equations*, Math. Ann. 212 (1975), p. 296, before Lemma 6.
  - Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
    Japan 25 (1973), Thm 1.
  - Locators UNVERIFIED.
- *Status:* **[R]**. The application is [M] (Astra "descent").

**C10. One compatible system at 3 and 5** (N5 L776-795).
- *Content.* The relative Frobenius composed with `μ̄_σ` is an endomorphism of the reduction.
  Its characteristic polynomial is rational and independent of `ℓ`. Then Chebotarev and
  Brauer–Nesbitt.
- *Suppliers.*
  - **I2**, the reduction of `μ_σ`: the Néron mapping property, Bosch–Lütkebohmert–Raynaud,
    *Néron models* (1990), §1.2, Def. 1 and Prop. 8. Locator UNVERIFIED. N5 uses it without a
    citation.
  - The independence of `ℓ`: Mumford 1970, §19, Thm 4 (UNVERIFIED; uncited in N5).
  - Chebotarev: Neukirch, *Algebraic number theory*, VII.13.4. Brauer–Nesbitt: Curtis–Reiner,
    (30.16). Locators UNVERIFIED.
- *Status:* **[M]** (rv-h-novel step 4).

### Part D. Conductor (N5 L796-857)

**D1. Break bound** (N5 L796-812).
- *Content.* `δ ≤ e − 1 + e·v_p(e)`, the Herbrand integral, and `u_last ≤ 2δ/e ≤ 4a²`.
- *Suppliers.*
  - Serre, *Local fields*, III §6 and IV §§1-3. N5 cites Serre in Cassels–Fröhlich, §§4.1-4.3;
    *Corps locaux* is the better locator.
  - The 15 local fields of `c3_breaks.py` (rv-h-novel; not rerun here).
- *Status:* **[M]** (rv-h-novel step 5; Astra "conductor").

**D2. Semistability and wild inertia, odd `p`** (N5 L813-823).
- *Suppliers.*
  - Raynaud's criterion: Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5
    (UNVERIFIED), or SGA 7 I, Exp. IX, Prop. 4.7 (UNVERIFIED).
  - Semistable reduction implies unipotent inertia: SGA 7 I, Exp. IX, §3.
  - `G₀ = |GL₄(𝔽₅)|`: `c1_constants.py` (rerun).
- *Status:* **[M]** (rv-h-novel step 6; Astra "conductor").

**D3. The `p = 2` paragraph** (N5 L823-846).
- *Suppliers.*
  - Silverman, AEC (2nd ed. 2009), IV.6.4.
  - The subgroup formula: Serre, *Local fields*, IV §1 Prop. 2 and §3 Prop. 15 (UNVERIFIED).
    It needs `L_v/ℚ₂` Galois.
- *Repairs.* rv-h-novel R2 ("If `e ≤ D`" → "Since `e ≤ D`") and R3 (cite the subgroup formula
  and its Galois hypothesis).
- *Status:* **[M]** (rv-h-novel step 7; Astra "conductor").

**D4. Conductor exponents** (N5 L846-852).
- *Content.* `a_p ≤ 2 + 2U₀ ≤ E₀` at `p ≤ R`. At `R < p ∈ T` the extension is tame and `A` has
  good reduction (A6), so `a_p ≤ 2`. Outside `T`, `a_p = 0`.
- *Status:* **[M]** (rv-h-novel step 8). It inherits [U] from A6.

**D5. Level ≤ conductor: I1** (N5 L852-857).
- *Content.* `N ≤ ∏_{p≤R} p^{E₀}·M² ≤ QM²`.
- *Supplier.* Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de
  Hilbert*, Ann. Sci. ÉNS 19 (1986), 409-468, Théorème (A). It is applied at `F = ℚ`, weight 2,
  with `λ | 5` for `p ≠ 5` and `λ | 3` for `p = 5`, in the direction "`v_p(N)` = conductor
  exponent". The bibliography entry is already in N5 (`carayol`), but it is not cited in the H
  proof.
- *To check (UNVERIFIED).* That Théorème (A) covers `F = ℚ` at every `p ≠ ℓ`, including
  `p | N`; see the statement in §0 of the paper. Fallback: Langlands, *Modular forms and
  ℓ-adic representations*, LNM 349 (1973), together with Carayol's §0 remarks (SPECULATIVE).
- *Status:* **[R]**.

### Part E. Transfer (N5 L860-905)

**E1. An isogeny `A × Z → J₁(N)` over `L'`** (N5 L861-867).
- *Suppliers.*
  - Faltings 1983, Satz 4 (the Hom theorem; uncited locator in N5, UNVERIFIED).
  - Poincaré reducibility: Mumford §19, Thm 1.
- *Status:* **[M]** (rv-h-novel step 9). With D2, no GR14 input enters here.

**E2. Height of the Jacobian** (N5 L868-876).
- *Content.* `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`.
- *Supplier.* Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1 and §2.3 (UNVERIFIED).
- *Status:* **[R]**.

**E3. The explicit isogeny bound** (N5 L878-892).
- *Supplier.* Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), Thm 1.4.
  UNVERIFIED; the text is not on arXiv.
- *Check.* The arithmetic is in `c1_constants.py` (rerun).
- *Status:* **[R]**.

**E4. Height variation, additivity, lower bound** (N5 L893-900).
- *Suppliers.*
  - Faltings 1983, Lemma 5. Alternative: Raynaud, Astérisque 127 (1985), Exp. VII,
    Cor. 2.1.3.
  - Bost's lower bound `h_F ≥ −(3/2)·dim`, through GR14 §9.
  - Locators UNVERIFIED.
- *Status:* **[R]**. The arithmetic is [M] (rv-h-novel step 9) and [S].

### Part F. Back to `u` (N5 L908-964)

**F1. `j` in theta constants** (N5 L908-927).
- *Content.* `j = 3779136·(∏ z_m)⁴/(∑ z_m⁸)⁵`.
- *Suppliers.*
  - Lin–Yang 2020, eqs. (2), (14), (13).
  - Lauter–Naehrig–Yang, J. Number Theory (2015), §2.2.
  - Igusa, *Modular forms and projective invariants*, Amer. J. Math. 89 (1967), pp. 833-834 and
    848.
  - All checked through `igusa_check.py` (rerun, identical). Journal locators UNVERIFIED.
- *Status:* **[R]+[S]**. This replaces `ly-d6` and `igusa-theta` (route B3).

**F2. `h(j) ≤ 40·h([z_m]) + 22`** (N5 L928-932).
- *Content.* Degree 40, with `ℓ¹` norms `3779136` and `10⁵`.
- *Status:* **[M]** (Astra "height").

**F3. Theta height against Faltings height** (N5 L934-947).
- *Supplier.* Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012),
  Cor. 1.3(2) and §§2.2-2.3 (UNVERIFIED).
- *Status:* **[R]**. The normalization bookkeeping (`X_D ≤ 3X`) is [M] (Astra "height").

**F4. From `j` to `u`, and the final constant** (N5 L949-964).
- *Content.* The rational-root theorem gives `h(u) < h(j) + 74`. Then
  `40·10000·2²⁴ + 96 = 6710886400096 < 10¹³` (VERIFIED here). So
  `h(u) ≤ ½H₆(S;R)·M^{24}`, for every admissible `R`.
- *Status:* **[M]** (Astra "height"); the numerics are VERIFIED.

## 2. What remains outside refereed sources

The list is exhaustive relative to §1. Everything not listed here is a refereed theorem cited
in §1.

### 2.1 Repository arguments reviewed by models only (no human referee)

1. **N5's own text**:
   - A3, A7, A8 and A9 (Astra "whole", 11/4 text);
   - B1-B3, C1, C10 and D1-D4 (rv-h-novel on N5, plus Astra);
   - C3, C5, C8 and C9 (Astra "descent", 11/4 text; parts of C2 and C5 also in rv-h-a011, on
     Version 14);
   - E1 and E4 (rv-h-novel);
   - F2-F4 (Astra "height").

   **C8** (twist and weight) has had the thinnest review. rv-h-novel and rv-h-a011 both left
   N5's version of it out of scope.
2. **NoCM** (A10): h-cm with the review rv-h-cm, after its repairs R1-R5.
3. **The hypothesis check for Pan** (C7): h-a011 with the review rv-h-a011, written for Version
   14 and transferred to N5 in §1 C7.

### 2.2 Repository arguments with no independent review

1. **Lemma PR** (A5, A6): h-b1's Prop. TS, Lemma NV, the M2/M8 bookkeeping, and the reproof of
   Morita. A review (`wip/rv-h-b1`) is pending. Its focus should be Lemma NV steps 3-4, as h-b1
   §6 item 1 asks. Until that review exists, the trust statement of §3 rests on an unreviewed
   argument at this point.
2. **The moduli identification** (A4): N5's `Y₃` as the fine moduli scheme of §1 A4 over `ℚ`.
   This needs half a page in the record that replaces N5 L443-530.

### 2.3 Repository scripts (exact computations)

| Script | Output | Used in | Rerun here |
| --- | --- | --- | --- |
| `scratch/h-v14/form_check.py` | `form_check.output.txt` | A1, A3 | identical |
| `scratch/h-v14/igusa_check.py` | `igusa_check.output.txt` | A7, F1 | identical |
| `origin/wip/h-b1:scratch/h-b1/b1_checks.py` | `b1_checks.output.txt` | A3, A5 | identical |
| `scratch/h-map/beckmann_check.py`, `o3_units.py` | `.output.txt` | A5, A3 | not rerun (subsumed by `b1_checks.py`) |
| `scratch/rv-h-cm/check.py` | `check.output.txt` | A10 | identical |
| `origin/wip/rv-h-novel:scratch/rv-h-novel/c1_constants.py` | none committed; rerun saved in `scratch/h-trust/reruns/` | B3, D2, E3, E4 | agrees with rv-h-novel's log |
| `origin/wip/rv-h-novel:scratch/rv-h-novel/c2_sqrt_criterion.py` | as above | B2 | agrees (135 characters, 0 mismatches) |
| `origin/wip/rv-h-novel:scratch/rv-h-novel/c3_breaks.py` | none committed | D1, D3 | not rerun (PARI) |

### 2.4 Unrefereed editions cited by N5, with refereed replacements (citation swaps only)

| N5 key | Used at | Replacement | Statement change |
| --- | --- | --- | --- |
| `milne-av` (course notes v2.00, 2008) | A9 (L564), C3 (L10968) | Mumford, *Abelian varieties* (1970), §§1-3, 19-20; Milne in Cornell–Silverman (1986) | none |
| `brinon-conrad` (CMI notes, 2009) | C3 | Fontaine, Astérisque 223 (1994), Exp. II-III and VIII | none |
| `conrad-local-characters` (preprint, 2011) | C8 | Serre 1968, Ch. III | none |
| `babagranath` (MPI preprint, 2005) | A2, A7 | Canad. J. Math. 60 (2008) | numbering to compare; the "local index slip" of Lemma 3.1 is not used (A3 is proved in N5) |
| `linyang` (arXiv v1, 2018) | A1, A2, A7, F1 | Math. Z. 295 (2020) | equation and example numbers to compare |
| `buzzard` (author version, 2002) | N5 L444 | deleted by B1 | — |

### 2.5 Locators not read (UNVERIFIED), and where to check them

Every published locator in §1 is UNVERIFIED unless §1 says it was read in the arXiv version.
Those read in arXiv are: Pan v2 Thm 1.0.4, Berger v3 Thm 0.6/5.19, González–Rotger §5, Lin–Yang
v1 Ex. 30 and eqs. (2), (13), (14), and Scholze's introduction. The checks, in order of weight:

1. **Pan, JAMS 35 (2022)**: that Theorem 1.0.4 is numbered and worded as in arXiv v2. Check the
   AMS text, pp. 1031-1040.
2. **Carayol 1986, Théorème (A)**: its coverage of `F = ℚ`, weight 2, every `p ≠ ℓ`. Check the
   statement in §0 of the paper (Numdam ASENS_1986_4_19_3_409_0).
3. **Gaudron–Rémond, Duke 163 (2014), Thm 1.4 and §9**: the exact constant
   `1024g³(64g² log(14g) + …)` and Bost's bound. Check §1 and §9 of the published text.
4. **SGA 1 X 3.1, XIII 5.3; SGA 7 IX 3.6, IX 4.7**, and **Serre–Tate 1968, Thms 1-2**: for
   Lemma PR. These are classical, and the numbering is the risk.
5. **Deligne 1971 (Bourbaki 389) §§3-4; Deligne 1979 §2.7, §5; Shimura 1967; Kottwitz 1992 §5**:
   reciprocity, the Hecke action, the moduli interpretation (A3-A5).
6. **Faltings 1983**: Satz 3, Satz 4 and Lemma 5 (§5), with the erratum.
7. **Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 and Thms 9.1, 9.3**, and the corrigendum.
8. **Berger, Invent. Math. 148 (2002)**: the journal number of Théorème 0.6.
9. **Silverberg–Zarhin 1995, Thm 3.5** (Numdam AIF_1995__45_2_403_0).
10. **Javanpeykar 2014, Thm 1.1.1**; **Pazuki 2012, Cor. 1.3(2)**; **Li 1975, p. 296**; **Shimura
    1973, Thm 1**.
11. **Baba–Granath 2008** and **Lin–Yang 2020**: compare the journal numbering with the preprint
    numbering N5 uses.
12. **Vignéras LNM 800** (local normalizers, embedding condition); **Reiner** (Skolem–Noether);
    **Mumford §19** (Thms 1, 3, 4); **BLR §1.2**; **Milne ADT Ch. I**; **Serre, *Local fields*
    III §6, IV §§1-3**; **Serre 1968 Ch. III**; **Fontaine, Astérisque 223**.

### 2.6 Policy items (not gaps)

- **Inside Pan.** Pan's proof cites Skinner–Wiles, Kisin, Hu–Tan and Khare–Wintenberger
  (rv-h-a011 F2). The leaf is the stated theorem.
- **Inside Berger.** Berger's theorem rests on André, Kedlaya and Mebkhout (rv-h-a011 F3). All
  are refereed. This is not a residual.
- **Conventions.** Hodge–Tate sign, Frobenius and reciprocity normalizations were checked to be
  immaterial (rv-h-a011 §2; h-b1 §6 item 3).

### 2.7 Residual list in one line each

Outside refereed sources, H rests on:

- (i) N5's novel arguments and bookkeeping (§2.1 item 1), reviewed by models only;
- (ii) NoCM (model-reviewed);
- (iii) Lemma PR and the moduli identification (unreviewed);
- (iv) seven exact scripts;
- (v) five citation swaps (§2.4);
- (vi) the locator checks of §2.5.

No unpublished upstream supplement is used.

## 3. Draft docstrings (not applied; the Lean files were not edited)

The drafts assume that `h-b1`, `rv-h-novel` and this note are on main when the docstrings land.
Otherwise, replace those paths with the branch names. The definitions and numerals are
unchanged.

**`ZInQKernel/Hypotheses/Height.lean`**: the module docstring and the docstring of
`SixContactEstimate`.

```lean
/-!
# Hypothesis H: the six-contact height estimate

`SixContactEstimate` is Theorem 4.1 (`thm:height`) of the frozen 11/5 manuscript
`diophantine_zq.tex` (sha256 `cb1148cd…`), with the manuscript's numerals. The statement
concerns only rational numbers, but its proof needs Shimura curves, modularity and Arakelov
geometry, none of which is in Mathlib. It therefore enters the main theorems as an explicit
hypothesis, through its one used instance `SixContactMin` (`Hypotheses/HeightMin.lean`).

## Trust statement

The proof uses no unpublished supplement. `docs/research/h-trust.md` §1 lists every step with its
supplier and status. It rests on the following.

* **Refereed theorems.**
  - The discriminant-six Shimura curve: its canonical model and moduli interpretation (Shimura
    1967; Deligne 1971, 1979), its branch data and Igusa coordinates (Baba–Granath 2008;
    Lin–Yang 2020; Igusa 1967; Lauter–Naehrig–Yang 2015), and its CM points (González–Rotger
    2006).
  - Reduction: tame specialization (SGA 1, Exp. X, XIII), semistable reduction (SGA 7, Exp. IX),
    and Néron–Ogg–Shafarevich (Serre–Tate 1968).
  - Galois representations: Faltings' finiteness theorems (1983); Scholze's de Rham comparison
    (2013, with its 2016 corrigendum); Berger's p-adic monodromy theorem (2002); Pan's
    Fontaine–Mazur theorem (J. Amer. Math. Soc. 35 (2022), Theorem 1.0.4 of
    arXiv:1901.07166v2); Li 1975 and Shimura 1973 for newforms; Carayol's local–global
    compatibility (1986, Théorème A).
  - Local fields: local class field theory and ramification (Serre), and Raynaud's criterion
    (Silverberg–Zarhin 1995).
  - Heights: Javanpeykar 2014, the isogeny theorem of Gaudron–Rémond (2014, Theorem 1.4),
    Faltings' height variation, and Pazuki 2012.
* **Manuscript arguments reviewed by models only, never by a human referee.**
  - The scalar descent, the uniform conductor bound `N ≤ Q_R M²` and the transfer from
    `J₁(N)`: `docs/research/rv-h-novel.md`, plus four scoped Astra reviews of the 11/4 text
    (`docs/reviews/height-replacement/`).
  - The geometric bookkeeping: the Hom field, the endomorphism dichotomy and the conjugates.
  - The application of Pan's theorem: `docs/research/rv-h-a011.md`.
* **Repository arguments that replace manuscript text.**
  - The CM branch is empty for rational `u` (`docs/research/h-cm.md`; model review
    `rv-h-cm.md`).
  - The fibre field is unramified outside `S ∪ supp M_S(u)`, and the fibre surface has good
    reduction away from 3. Both come from tame specialization and a vertical-ramification
    lemma, with no integral model of the Shimura curve (`docs/research/h-b1.md`, Lemma PR).
    **This argument has not yet been reviewed.**
* **Exact computations** in `scratch/`, each with its saved output: the polarization form, the
  Igusa normalization, the ramification case analysis and the constants.

None of the replacements changes the constant `H₆` or the exponent 24. Published locators
that could not be read when the trust statement was written are listed as UNVERIFIED in
`docs/research/h-trust.md` §2.5.
-/
```

```lean
/-- **Hypothesis H** (Theorem 4.1, the six-contact estimate). For every finite set `S` of
primes containing all primes at most `324`, every `R ≥ max(D, max S, 10¹²)` and every
`u ∈ ℚ \ 𝒞`, `h(u) ≤ H₆(S; R) M_S(u)²⁴`.

Not proved in Lean. Its proof rests on refereed theorems, together with manuscript and
repository arguments that have been reviewed by models but not refereed, and uses no
unpublished supplement. See the module docstring and `docs/research/h-trust.md`. The main
theorems use only the instance `SixContactMin`. -/
```

**`ZInQKernel/Hypotheses/HeightMin.lean`**: keep the module docstring and append one paragraph;
replace the docstring of `SixContactMin`.

```lean
/-!
(… existing text unchanged …)

## Trust

`SixContactMin` is not proved in Lean. It is the instance `S = S_mul`, `R = D` of
`SixContactEstimate`, and `sixContactMin_of_sixContactEstimate` (`ZInQKernel/Main.lean`) derives
it in Lean. Its justification is therefore exactly that of Theorem 4.1, recorded in the module
docstring of `Hypotheses/Height.lean` and in `docs/research/h-trust.md`. The proof of Theorem 4.1
uses only two facts about this instance: `S_mul` contains the primes `≤ 324`, and
`max S_mul ≤ D`. H cannot be narrowed further or removed (`docs/research/h-map.md` §§1, 3.1,
3.3): the two consumers need a bound that is effective and uniform in `u`.
-/
```

```lean
/-- **Hypothesis H, minimal form.** For every `u ∈ ℚ \ 𝒞`, `h(u) ≤ H₆(D) · M_{S_mul}(u)²⁴`, where
`H₆(D) = A⁽⁰⁾_ht = 2·10¹³ max(1, C_cm, (D^(D E₀))¹⁷)`. This is the instance `S = S_mul`, `R = D`
of the six-contact estimate `SixContactEstimate`. It is the only form of H that the main theorems
assume. Its trust statement is that of Theorem 4.1: refereed theorems plus model-reviewed
arguments, with no unpublished supplement (`Hypotheses/Height.lean`,
`docs/research/h-trust.md`). -/
```

**Proposed H row for KERNEL_PLAN.md** (T3 success criterion: the row names no supplement; not
applied):

> H (Theorem 4.1): refereed theorems (Shimura curve: Shimura, Deligne, Baba–Granath, Lin–Yang,
> González–Rotger; SGA 1, SGA 7, Serre–Tate; Faltings 1983; Scholze; Berger; Pan's Theorem 1.0.4;
> Carayol; Serre's local fields; Silverberg–Zarhin; Javanpeykar; Gaudron–Rémond; Pazuki; Igusa),
> plus the manuscript's descent, conductor and transfer arguments (model reviews only:
> rv-h-novel, Astra), NoCM (h-cm, rv-h-cm), and Lemma PR in place of the integral model
> (h-b1; review pending). Outline: docs/research/h-trust.md.

## 4. Next step

A single review of this outline (`rv-h-trust`), together with the pending review of h-b1. The
review should check:

- (1) that every N5 line range from L405 to L964 falls in some step of §1;
- (2) the transfer of rv-h-a011's discharge table from Version 14 to N5 (C7);
- (3) C8;
- (4) the moduli identification A4.

The locator checks of §2.5 need network access. Items 1-3 of §2.5 decide whether any statement
must change; the rest decide numbering only (SPECULATIVE).
