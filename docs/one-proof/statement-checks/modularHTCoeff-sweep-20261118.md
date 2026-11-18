Recorded from the statement-check sweep of 2026-11-18, against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: `modularHTCoeff` (packet R7)

Checklist of `docs/one-proof/STATEMENT-CHECKS.md`. Evidence class: **AI-READ** (no human read the print for this report).

## Summary

**Verdict: CONSEQUENCE.** No clause of `HTNewAssembly.ModularHTCoeff` is stronger than the prints, and none of its
conventions conflicts with them. Every print read uses geometric Frobenius, and every one that states Hodge–Tate weights
gives the cyclotomic character weight −1. So each supplier lands in the Lean's **second disjunct** (geometric Frobenius
`σ⁻¹` has trace `a_p`, weights `{0, k−1}` in `PrintHasHTWeights`). No one print states the leaf as written, though, so the Lean needs a further step:

* **Kato** (Astérisque 295) is the closest. It works over `F_λ`, at every level and every residue characteristic. Its
  Hodge–Tate information is printed only as a de Rham filtration, so you need de Rham ⇒ Hodge–Tate with
  `gr^i D_dR(V) = (V ⊗ ℂ_p(i))^G` (Brinon–Conrad, Prop. 6.3.2). Two smaller steps finish it: unramifiedness passes to the
  quotient `V_{F_λ}(f)`, and `F_λ` is transported onto `E ⊆ ℚ̄_ℓ`.
* **Gee, Fact 4.20** (the print the flag cites) is in **§4.19, p. 105**, not in §2. It covers *automorphic
  representations*, not newforms, with coefficients in **`\bar L_{π,λ}`** (an algebraic closure), not in `K_{f,λ}`. You need
  the classical dictionary `f ↦ π_f` with `t_p = a_p(f)`, which Gee does not print. You also need to descend to a finite
  `E`, which Gee's own Fact 2.3 covers.
* **Taylor** (AFST 2004) prints only the GL_n automorphic theorem (Thm 3.6, p. 101) over `\bar ℚ_l`. It has no `a_p`
  trace clause and no `K_{f,λ}`.
* **Deligne** (Bourbaki 355) has no Hodge–Tate content. I found no individual-newform statement over `K_{f,λ}` in the
  pages I read.

## Field and commit

* Field `OpenResearchLeaves65.modularHTCoeff` (bundle `HDec.HSyn.OpenResearchLeaves65`, `ZInQKernel/OneProof/H/TailZ91.lean:17`,
  field at `:35`). Lean constant `HTNewAssembly.ModularHTCoeff`, `ZInQKernel/Contrib/OneProof/ModularHTCoeff.lean:356–370`,
  docstring `:325–355`.
* OPEN.md commit read: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (OPEN.md entry `### modularHTCoeff`, lines 432–445;
  kinds.tsv row 20).

## What the Lean says (unfolded, paths at that commit)

`ModularHTCoeff` (`ModularHTCoeff.lean:356–370`) says: for every prime `ℓ`, all embeddings `ιC : ℚ̄ → ℂ` and
`ιL : ℚ̄ → ℚ̄_ℓ`, every `N ≥ 1` (`[NeZero N]`), every `k : ℤ` with `2 ≤ k`, and every `f : HeckeRing.GL2.Newform N k`,
**there exist** an intermediate field `ℚ_ℓ ⊆ E ⊆ ℚ̄_ℓ` with `[E : ℚ_ℓ] < ∞` and a continuous homomorphism
`ρ : G_ℚ → GL₂(E)` such that:

* **(U)** for every prime `p ∤ Nℓ`, every place `v` of `ℚ̄` over `p` and every `σ` in the inertia group at `v`,
  `ρ(σ) = 1` (`:361–362`);
* **(A ∨ B)** (`:363–370`):
  * **A:** for `p ∤ Nℓ`, every `α ∈ ℚ̄` with `ιC(α) = a_p(f)`, every `v | p` and every arithmetic Frobenius `σ` at `v`,
    `tr ρ(σ) = ιL(α)`; and `PrintHasHTWeightsPos (ρ ∘ decomp) {0, k−1}`.
  * **B:** the same with `tr ρ(σ⁻¹) = ιL(α)`; and `PrintHasHTWeights (ρ ∘ decomp) {0, k−1}`.

The notions it uses:

* **Newform.** `HeckeRing.GL2.Newform N k` is vendored from Tau Ceti
  (`ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Newform.lean:85–109`). It is a nonzero cusp form on
  `Γ₁(N)` with nebentypus `χ`, an eigenvector of the Hecke-ring element `heckeTCompositeGamma0 N n` for every `n` coprime
  to `N`, normalized by `a₁ = 1`. It lies in `cuspFormsNew N k`, the Petersson-orthogonal complement of the old space
  (`.../Newforms/Basic.lean:203–205`). That is Miyake's primitive form, i.e. the printed newform; by Atkin–Lehner–Li it is
  an eigenform for every `T(n)`.
* **Coefficients.** `coeff f m` is the `m`-th coefficient of the period-1 `q`-expansion
  (`ZInQKernel/Contrib/G9/I4Layer.lean:1237–1238`), on `CF N k`, the cusp forms on `Γ₁(N)` (`:1234`).
* **Galois side.** `Qbar = AlgebraicClosure ℚ` (`I4Layer.lean:736`), and `GQ = Gal(ℚ̄/ℚ)` with Mathlib's Krull topology
  (`:739`).
  * `LiesOver v p` (`:743`) means `p` is a nonunit of the valuation subring `v ⊆ ℚ̄`, i.e. `v` is a place over `p`.
  * `IsArithFrob σ v p` (`:746–747`) means `σ ∈ D_v` and `σ(x) ≡ x^p mod m_v` for all `x ∈ v`.
  * `D_v` and `I_v` are Mathlib's `ValuationSubring.decompositionSubgroup` (the stabilizer of `v`) and `inertiaSubgroup`
    (the kernel of the action on the residue field).
* **Coefficient field.** `E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)` with `FiniteDimensional` (`:359`). `PadicAlgCl` is
  `AlgebraicClosure ℚ_ℓ` with the spectral norm, so `E` carries the `ℓ`-adic topology. Continuity of `ρ` is for the Krull
  topology and the topology of `GL₂(E)`.
* **Local side.**
  * `GQp p = Gal(ℚ̄_p/ℚ_p)` (`I4Layer.lean:802`).
  * `decomp` (`:807–809`) is Mathlib's `Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])`: restriction along an
    embedding `ℚ̄ → ℚ̄_p` chosen by `IsAlgClosed.lift`. Its image is one decomposition group, and the choice only
    conjugates it.
  * `ℂ_[p]` is the completion of `PadicAlgCl p`. `cpAct` (`:830–831`) extends `σ` to `ℂ_p` by continuity.
  * `cyc` (`:844–845`) is Mathlib's `cyclotomicCharacter`, with `σ(ζ) = ζ^{χ(σ) mod p^n}` on `p^n`-th roots of unity, and
    `cycPow σ i = χ(σ)^i` (`:848–849`).
* **Hodge–Tate, the tensor-product form** (`ModularHTCoeff.lean`).
  * `cTw w σ = (x ↦ χ(σ)^w σ(x))` on `ℂ_ℓ` (`:91–95`), and `twistAct ρ w σ = ρ(σ) ⊗ cTw w σ` on `Eⁿ ⊗_{ℚ_ℓ} ℂ_ℓ`
    (`:100–102`).
  * `PrintHTSpace ρ w` is the set of tensors fixed by every `twistAct ρ w σ`, i.e. `(V ⊗_{ℚ_ℓ} ℂ_ℓ(w))^{G_{ℚ_ℓ}}`, an
    `E`-subspace (`:120–125`). `PrintHTMult` is its `E`-dimension (`:127`).
  * `PrintHasHTWeights ρ S` means: for all `w`, `PrintHTMult ρ w = count_S w` (`:132–133`). Check: `V = ℚ_ℓ(1)` has only
    the weight `−1`, so this convention gives the cyclotomic character weight −1.
  * `PrintHasHTWeightsPos` is the same with `−w` (`:137–138`), so the cyclotomic character has weight +1.
  * `printHasHTWeightsPos_iff` (`:146–152`), `reading_arith` and `reading_geom` (`:386–394`) are proved in Lean. They
    show that the readings with `{0, 1−k}` are the same two disjuncts. I read them in source and did not rebuild.
* **The trace clause** asks only for traces: no determinant and no semisimplicity. `α` is unique if it exists, because
  `ιC` is injective, and for a newform it exists because `a_p` is algebraic.

## Edition, page, display (what was read)

| source | edition read | locus |
|---|---|---|
| Gee, *Modularity lifting theorems* | Essent. Number Theory 1 (2022), no. 1, 73–126, journal PDF; also arXiv:2202.05818v2 ("Accepted version"), same numbering | **§4.19, Fact 4.20, p. 105** (arXiv v2 p. 28). Also §1.1 p. 74 (Hodge–Tate normalization), Fact 2.3 p. 75 (finite-coefficient descent), §2.7 p. 76 (geometric Frobenius), §2.21 pp. 80–81 (τ-labelled HT weights, defined by reference to BLGGT), §4.8 p. 101 (weights `(k, η)`, `k_v ≥ 2`), Exercise 4.9 p. 102 (`F = ℚ`, `η = 0`), Remark 4.14 and Facts 4.15–4.16 p. 104 |
| Barnet-Lamb–Gee–Geraghty–Taylor, *Potential automorphy and change of weight* | arXiv:1010.2561v4 (9 Dec 2013) | Notation paragraph, p. 8 (definition of `HT_τ`, which Gee cites) |
| Kato, *p-adic Hodge theory and values of zeta functions of modular forms* | Astérisque 295 (2004), 117–290, numdam scan | §6 intro and 6.1 p. 160; 6.3 pp. 161–162; 8.2–8.3 pp. 181–182; **(9.2.2) p. 187, 9.4 p. 188**; 11.3 p. 205 ((11.3.4), (11.3.7)); **(14.10.1)–(14.10.3) p. 240** |
| Brinon–Conrad, *CMI summer school notes on p-adic Hodge theory* | preliminary version, author PDF (2009) | Def. 2.4.12 p. 24; **Prop. 6.3.2 p. 76** and the paragraph after it |
| Taylor, *Galois representations* | Ann. Fac. Sci. Toulouse Math. (6) 13 (2004), no. 1, 73–119, numdam scan | p. 75 (geometric Frobenius), pp. 78–79 (Hodge–Tate numbers), pp. 93–94 (bijection with newforms), pp. 99–101 (**Thm 3.6, p. 101**) |
| Deligne, *Formes modulaires et représentations l-adiques* | Sém. Bourbaki 1968/69, exp. 355 (1971), 139–172, numdam scan | pp. 139–140 (intro, `F_p` = inverse of Frobenius), **Thm 4.9 p. 167**, Thm 5.1 and Lemmas 5.2–5.3 p. 168, pp. 170–172 (Thm 5.6 and its proof, bibliography; text layer only) |

## Copy

Gee: the journal's open-access PDF and the arXiv author version. BLGGT and Brinon–Conrad: author copies. Kato, Taylor and
Deligne: library scans digitized by numdam. URLs and SHA-256 hashes are under Sources.

## Quote

* **Gee, Fact 4.20, p. 105.** "Let π be a regular algebraic cuspidal automorphic representation of GL2(A∞F) of weight
  (k, η). [...] for each finite place λ of Lπ there is a continuous irreducible Galois representation
  rλ(π) : GF → GL2(L̄π,λ) such that: (1) If πv is unramified and v does not divide the residue characteristic of λ, then
  rλ(π)|GFv is unramified, and the characteristic polynomial of Frobv is X² − tvX + (#k(v))sv [...] (3) If v divides the
  residue characteristic of λ then rλ(π)|GFv is de Rham with τ-Hodge–Tate weights ητ, ητ+kτ−1". The bar over `L` is
  printed (checked on a page render): the coefficients are an algebraic closure of `L_{π,λ}`.
* **Gee, p. 74.** "We normalize the definition of Hodge–Tate weights so that all the Hodge–Tate weights of the p-adic
  cyclotomic character εp are −1."
* **Gee, p. 76.** "We let FrobK = Frobk ∈ Gk be the geometric Frobenius element".
* **Gee, Fact 2.3, p. 75.** "If L/Qp is an algebraic extension, and ρ : GK → GLn(L) is a continuous representation, then
  ρ(GK) ⊆ GLn(M) for some L ⊃ M ⊃ Qp with M/Qp finite."
* **Gee, Exercise 4.9(3), p. 102.** "deduce a natural isomorphism between S^{U1(N)}_{D,k,0} and Sk(Γ1(N))".
* **BLGGT, p. 8.** "the multiset HTτ(W) contains i with multiplicity dim_{Q̄l}(W ⊗τ,K K̂̄(i))^{GK}. Thus for example
  HTτ(εl) = {−1}."
* **Kato, 9.4, p. 188.** "Let f be a normalized newform in Mk(X1(N)) ⊗ C of weight k and of level N, and let F, λ, Fλ be as
  in 8.3. Then by (9.2.2), VFλ(f) is a de Rham representation of Gal(Q̄p/Qp), D^i_dR(VFλ(f)) = DdR(VFλ(f)) for i ≤ 0,
  D^i_dR(VFλ(f)) = 0 for i ≥ k, [...] we have D^i_dR(VFλ(f)) = S(f) ⊗F Fλ for 1 ≤ i ≤ k − 1."
* **Kato, (14.10.3), p. 240.** "For any prime number ℓ which is not divided by λ,
  det_{Fλ}(1 − Fr_ℓ^{−1}u ; H⁰(Q_ℓ^{ur}, VFλ(f))) = 1 − a_ℓu + ε(ℓ)ℓ^{k−1}u². Here Fr_ℓ is the arithmetic Frobenius of ℓ."
* **Kato, 8.3, pp. 181–182.** On `V_{k,A}(Y(M,N))`: "This action is unramified at any prime number which does not divide
  pMN." And: "VOλ(f) is a free Oλ-module of rank 2. The action of Gal(Q̄/Q) on VQp(Y1(N)) induces an Fλ-linear action of
  Gal(Q̄/Q) on VFλ(f)".
* **Brinon–Conrad, Prop. 6.3.2, p. 76.** "If V is de Rham then V is Hodge–Tate and gr(DdR(V)) = DHT(V) as graded
  K-vector spaces."
* **Taylor, p. 79.** "The multiplicity of i in HT(R) is dim_{Q̄p}(V ⊗Qp Cp(i))^{GQp}".
* **Taylor, Thm 3.6, p. 101.** "Then there is a continuous representation R_{l,ι} : GQ → GLn(Q̄l) [...] 2. R_{l,ι}|GQl is
  de Rham and HT(R_{l,ι}|GQl) = H."
* **Deligne, Thm 4.9, p. 167.** "F l'endomorphisme φp^{−1} de nWℓ [...] Alors, Tp = F + I*pV , FV = p^{k+1}".

## Standing hypotheses

* **Gee.**
  * "Throughout these notes, p > 2" (p. 73). Fact 4.20 itself is stated "for each finite place λ" in terms of "the residue
    characteristic of λ", with no parity condition. See Unclear below.
  * Fixed embeddings `ℚ̄ ↪ ℚ̄_p` and `ℚ̄ ↪ ℂ` (pp. 73–74). The cyclotomic character `ε_p` has weight −1 (p. 74), and
    `Frob` is geometric (p. 76).
  * Weights `(k, η)` have `k_v ≥ 2` and `k_v + 2η_v − 1` independent of `v` (p. 101). Classical forms are the case
    `F = ℚ`, `η = 0` (Ex. 4.9).
* **BLGGT.** Representations over `\bar ℚ_l`, `τ : K ↪ \bar ℚ_l`.
* **Kato.**
  * "Fix k ≥ 2, N ≥ 1" (p. 160). `F = ℚ(a_n; n ≥ 1) ⊂ ℂ`, `λ` a finite place of `F`, and `p` the residue characteristic
    of `λ` (Kato's `p` is the Lean's `ℓ`).
  * `D^i_dR(V) = H⁰(K, B^i_dR ⊗ V)` (9.2). `Fr_ℓ` is arithmetic in (14.10.3).
  * The cohomology `H^q` is set up for every `p`, including `p = 2` (8.2).
* **Brinon–Conrad.** `D_HT(V) = (B_HT ⊗_{ℚ_p} V)^{G_K}`, graded with degree-`i` piece `(ℂ_K(i) ⊗ V)^{G_K}`. In their
  convention `ℚ_p(n)` has HT weight `−n`.
* **Taylor.** Representations over `\bar ℚ_l`, with `Frob_p^{−1}(x) = x^p` (geometric).
* **Deligne.** `F_p` is the inverse of the Frobenius `φ_p` (geometric, p. 140). Deligne's `k` is the weight minus 2.

## Comparison (clause by clause; the Lean's `ℓ` is the print's `p` or `λ`-characteristic)

| clause | Lean | Kato | Gee Fact 4.20 | verdict for the clause |
|---|---|---|---|---|
| quantifiers | all primes `ℓ` (2 and `ℓ ∣ N` included), all `N ≥ 1`, all `k ≥ 2`, all newforms, all `(ιC, ιL)` | "Fix k ≥ 2, N ≥ 1", every finite place `λ` of `F`. (9.2.2) has no condition linking `p` and `N` | every regular algebraic cuspidal `π` and every finite `λ` of `L_π`, all levels | **Step:** `(ιC, ιL)` picks the place `λ` cut out by `ιL ∘ ιC⁻¹` on `F` (or `L_π`). Gee needs `F = ℚ`, `η = 0` and the map `f ↦ π_f` |
| newform | Tau Ceti `Newform` (`Newform.lean:85–109`) | "normalized newform ([AL], [De2])" with `T(n)f = a_n f` for all `n` (6.1) | none: `π` is automorphic | Kato: the same notion (Atkin–Lehner–Li). Gee: **step** `f ↦ π_f` (Ex. 4.9 gives only the space isomorphism) |
| coefficients | some finite `E ⊆ ℚ̄_ℓ` (∃) | `F_λ`, `dim = 2` (6.3, 8.3) | **`\bar L_{π,λ}`** | Kato: ∃-introduction after transport `F_λ ≅ E`. Gee: **step**, descent to a finite `M` (Gee's Fact 2.3), then embed in `ℚ̄_ℓ` |
| continuity | `Continuous ρ` | implicit (étale cohomology; continuous Galois cohomology of 8.2 is used in 9.4) | "continuous irreducible" | match (implicit for Kato) |
| unramified | at all `p ∤ Nℓ`, all places `v ∣ p` | stated for `V_{k,A}(Y(M,N))`, outside `pMN` (8.3) | (1): unramified where `π_v` is unramified and `v ∤ λ` | Kato: **step**, pass to the quotient `V_{F_λ}(f)`; for `N ≤ 3` compare two auxiliary levels. Gee: **step**, conductor of `π_f` = `N` |
| Frobenius and trace | B: `tr ρ(σ⁻¹) = ιL(α)` for every arithmetic Frobenius `σ` | (14.10.3): `det(1 − Fr⁻¹u) = 1 − a_ℓ u + ε(ℓ)ℓ^{k−1}u²`, so the geometric trace is `a_ℓ` | char. poly. of geometric `Frob_v` is `X² − t_vX + (#k(v))s_v` | Kato: **match** (trace read off; any choice of `σ`, `v` by unramifiedness). Gee: **step** `t_p(π) = a_p(f)` (or use `π_{\bar f}`), not printed |
| HT weights and sign | B: `dim_E (V ⊗ ℂ_ℓ(w))^G = count_w{0, k−1}`, cyclotomic weight −1 | de Rham, `D^i` jumps only at `0` and `k−1`, each of `F_λ`-dimension 1 (9.4, via (9.2.2), (11.3.7)) | de Rham with weights `η, η+k−1`, i.e. `{0, k−1}` for `η = 0`; `ε_p` weight −1; definition by BLGGT's tensor-product formula | Kato: **step**, Brinon–Conrad Prop. 6.3.2 turns the jumps into exactly the Lean's multiplicities (`F_λ`-linear by functoriality). Gee: **match** in sign and definition, after base change `E → \bar ℚ_ℓ` |
| restriction to `G_{ℚ_ℓ}` | Mathlib's `decomp` (one chosen embedding) | the print's fixed embedding | the print's fixed embedding | conjugate restrictions have equal multiplicities |
| disjunct A | arithmetic trace `a_p` with weight convention +1 | not used | not used | harmless (∨-introduction from B) |

Taylor's Thm 3.6 fits the same sign and Frobenius conventions as disjunct B (geometric, p. 75; `HT` multiplicity
`dim(V ⊗ ℂ_p(i))^G`, p. 79). It reaches the Lean only after three steps:

* taking `π ∈ A°_{\{k−1,0\}}` from a weight-`k` newform (p. 94);
* reading `tr = a_p(f)` from `rec_p(π_p)`, which needs a normalization Taylor does not print;
* descending from `\bar ℚ_l`.

Deligne's Thm 4.9 is a congruence relation `T_p = F + I*_pV` on the fundamental representation `nWℓ` over `ℚ_ℓ`. It
carries no Hodge–Tate information.

## Verdict

**CONSEQUENCE.** The best route is Kato §§6.1, 6.3, 8.3, 9.4 and (14.10.3), plus Brinon–Conrad Prop. 6.3.2. The steps:

1. **Place and transport.** Let `λ` be the place of `F` induced by `ιL ∘ ιC⁻¹`. Take `E = closure of ιL(ιC⁻¹(F))`,
   which is `≅ F_λ`, and let `ρ` be `V_{F_λ}(f)` in a basis.
2. **Hodge–Tate from de Rham.** Brinon–Conrad Prop. 6.3.2 gives `gr^i D_dR(V) = (V ⊗ ℂ_p(i))^G`.
3. **Unramified quotient.** Unramifiedness outside `pN` passes from Kato 8.3 to the quotient `V_{F_λ}(f)`.
4. **Trace.** Read the trace of `Fr_p⁻¹` off (14.10.3); this is disjunct B.
5. **Newform.** Kato's normalized newform is the same as Tau Ceti's `Newform`.

Through the flag's own citation, Gee Fact 4.20, the steps are:

1. the classical-to-automorphic dictionary `f ↦ π_f`, with `t_p = a_p(f)` and conductor `N`, which Gee does not print;
2. descent from `\bar L_{π,λ}` to a finite field (Gee's Fact 2.3) and base change of the multiplicities;
3. the choice of `λ` from `(ιC, ιL)`.

The row's kind, consequence, and its strict rating GLUE fit this reading. The ground for a LEAF rating in the assembly
report was "the printed existence form over `K_{f,λ}` / `F_λ` with HT weights in the tensor-product definition", and I
did not find that printed in one place.

## False, incomplete or unclear

* **Not false, and not stronger than the print.** The Lean follows from Kato, plus the standard de Rham ⇒ Hodge–Tate
  step, by the steps named above.
* **Locator corrections.**
  * **Gee.** The existence statement is §4.19, Fact 4.20, p. 105 (ENT), not "section 2". §2 carries only conventions
    (p. 76, pp. 80–81); the HT normalization is in §1.1 (p. 74). The flag's "Gee 2022 Fact 4.20" is correct.
  * **Kato.** The R13 loci are confirmed. "§11.3 (UNVERIFIED)" is confirmed as p. 205, (11.3.4) and (11.3.7). The
    Frobenius and trace normalization the leaf needs is **(14.10.3), p. 240**, which is not in the source line and should
    be added. `V_{F_λ}(f)` and its Galois action are defined in 6.3 (p. 162: `V_A(f) = V_F(f) ⊗_F A`) and 8.3
    (pp. 181–182).
* **Docstring inaccuracies** (`ModularHTCoeff.lean:332`, `:347–348`, `:351–353`; flag text).
  * Taylor is listed with the `K_{f,λ}` prints, but Taylor's theorem is over `\bar ℚ_l` and automorphic.
  * Gee's form is called a `K_{f,λ}`-type existence form, but it is over `\bar L_{π,λ}` and stated for `π`.
  * Deligne 355 is credited with "existence over `K_{f,λ}`", but it prints Thm 4.9 for `nWℓ`; I found no
    individual-newform statement in the pages I read.
  * The R5 concern in `docs/research/htnew-assembly.md` (descent for `\bar ℚ_ℓ`-coefficient prints) therefore **applies
    to Gee**. It is covered by Gee's own printed Fact 2.3, so it is a named step, not an open hole.
* **Unclear.**
  * Gee's blanket "p > 2" (p. 73) against Fact 4.20's "for each finite place λ". I read Fact 4.20 as covering `ℓ = 2`.
    Kato covers `ℓ = 2` either way.
  * Kato does not state continuity in so many words for `V_{F_λ}(f)`.
  * For `N ≤ 3` Kato defines `V_{k,ℤ_p}(Y_1(N))` through an auxiliary level `L ≥ 4`, so unramifiedness at primes
    dividing `L` needs two coprime choices of `L`.

## Not read

* **Gee:** §3, §5 and §6; the rest of §4 (pp. 97–98, 103, 106; §4.6 on pp. 99–100 only skimmed); and the sources behind
  Fact 4.20 (none is cited at the Fact).
* **BLGGT:** everything except the notation paragraph on p. 8.
* **Kato:** everything outside the pages listed, including all proofs and [Ca], [Sa1], [Sa2] behind 14.10.
* **Brinon–Conrad:** only Def. 2.4.12 and §6.3 up to Prop. 6.3.2 and the paragraph after it; not the proof's references.
* **Taylor:** everything outside the pages listed.
* **Deligne:** N°2–N°4 except Thm 4.9. I searched the OCR text for numbered statements: Prop. 2.2, Thm 2.10,
  Props 3.3–3.19, Thm 4.1, Props 4.3–4.8, Thm 4.9, Thm 5.1, Lemmas 5.2–5.5, Thm 5.6. I did not read Props 3.18–3.19
  closely.
* **Faltings,** Math. Ann. 278 (1987), and **Saito,** Invent. Math. 129 (1997): not read, because I found no
  legitimately free copy.
* **Diamond–Shurman 9.6.5:** not read.
* **No Lean build or run.** The Lean was read in source at the commit. The Mathlib definitions (`cyclotomicCharacter`,
  `absoluteGaloisGroup.map`, `decompositionSubgroup`/`inertiaSubgroup`, `PadicAlgCl`/`PadicComplex`) were read in source
  at the manifest revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## AI use

An AI assistant (a large language model) did the whole check, and no human reading is involved. It:

* read the Lean source and the project docs at the commit;
* located and downloaded the open copies listed below;
* extracted text layers and rendered page images to read the displays (the numdam scans have OCR-only text, so the
  displays were read from the images);
* chose the quotes and wrote the comparison.

## Evidence

**AI-READ.** Under STATEMENT-CHECKS.md this does not count as a human reading. It can clear only the `unread` flag, and
only per the integrity rules.

## Sources (URL, SHA-256 of the file read)

| source | URL | SHA-256 |
|---|---|---|
| Gee, ENT 1 (2022) journal PDF (57 pp.) | https://msp.org/ent/2022/1-1/ent-v1-n1-p06-s.pdf | `3ffa71fd684abd88c45853d7a4ed03ac27dfe4a3032487e0aa3863fe6171e94a` |
| Gee, arXiv:2202.05818v2 (45 pp.) | https://arxiv.org/pdf/2202.05818v2 | `878f83e189ad44603ac04f6c16ef17f4c4fe046db91a2f0933a192e048715ea5` |
| BLGGT, arXiv:1010.2561v4 | https://arxiv.org/pdf/1010.2561v4 | `c953df6229ba8d8b4ae25b1a00cf11592864c74692859d324ff10d3eef645d24` |
| Kato, Astérisque 295 (2004) 117–290 (numdam) | https://www.numdam.org/item/AST_2004__295__117_0.pdf | `3c6e14b11fa60262db8aff782ce3cf4d83e9100c0be83621a7e4ce502cec605d` |
| Brinon–Conrad, CMI notes (preliminary version, 2009) | https://math.stanford.edu/~conrad/papers/notes.pdf | `f27d508bc64b3c9e2e9de5041429b2cb6a909b2cd72ff8096c20493f27b5a187` |
| Taylor, AFST (6) 13 (2004) 73–119 (numdam) | https://www.numdam.org/item/AFST_2004_6_13_1_73_0.pdf | `5404f8d7e0969d0b4d0280bef5fa72d5d428835993284534a8de1046f1e95de6` |
| Deligne, Sém. Bourbaki exp. 355 (numdam) | https://www.numdam.org/item/SB_1968-1969__11__139_0.pdf | `19509c19b0cb056f4a5eba83a48a99f54bb6df0c7a96ab7f4018b0765e1ed98c` |

Mathlib source files read, at revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, from
https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/ :

* `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`
* `Mathlib/FieldTheory/AbsoluteGaloisGroup.lean`
* `Mathlib/RingTheory/Valuation/RamificationGroup.lean`
* `Mathlib/NumberTheory/Padics/Complex.lean`
