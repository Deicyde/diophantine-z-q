# pkg-I4: the modularity package (h-trust C3-C5, C7-C9, D5)

Status: research note, task pkg-I4, 2026-11-11. Lean draft `scratch/pkg-I4/I4.lean` (compiles with
`lake env lean`; log `scratch/pkg-I4/log.md`). No file under `ZInQKernel/`, `blueprint/` or other
notes was edited.

Marks. **VERIFIED**: read in a source quoted in the repository, computed, or compiled.
**STANDARD**: a published theorem with an exact reference. **SPECULATIVE**: an assessment.
Theorem numbers recalled from memory are marked UNVERIFIED (no network here). "Lean now" means a
`def … : Prop` over genuine Mathlib definitions plus cheap new definitions, compiled.

Sources read for this note: `diophantine_zq.tex` (N5) L719-857 and L10936-11005;
`docs/research/h-trust.md` §1 C1-C10 and D1-D5; `wk-h.md`; `rv-lit.md`; `h-a011.md` §1 (Pan's
statement as printed in arXiv v2); `h-leaves.md` §3 (options for the de Rham input);
`prereq-survey.md`; the branches `origin/wip/hdec-faithful` and `origin/wip/hdec-alt` (their
`Leaves.lean` and notes); Mathlib v4.35 sources under `.lake/packages/mathlib`.

## Summary

1. **Ten inputs, nine of them refereed theorems** (§1). I4 consists of Pan 2022 Thm 1.0.4
   (C7); the de Rham comparison for abelian varieties with Fontaine's closure (C3); Berger 2002
   (C4); the Betti–étale comparison (C5); the existence of eigenform Galois representations
   (Shimura, Deligne, Deligne–Serre); their Hodge–Tate weights at every level (Saito, Kato, or
   Faltings 1987) and Deligne–Serre finiteness in weight one (C8); twisting, Li's newforms and
   Shimura's `A_f` with the Eichler–Shimura relation (C9); Carayol's Théorème (A) (D5). The glue
   inside the package (C8's weight comparison and determinant argument, C9's constituent
   argument, C10's compatible system) uses Chebotarev, Brauer–Nesbitt, Kronecker–Weber and
   Faltings 1983 from other packages.
2. **New Lean result: Hodge–Tate weights are definable over Mathlib today (VERIFIED, compiles).**
   Mathlib has `ℂ_[p]` (completion of `ℚ̄_p` with the spectral norm), the isometry of
   `ℚ_p`-automorphisms (`spectralNorm_eq_of_equiv`), completion functoriality and the
   cyclotomic character. From these `I4.lean` builds the action of `G_{ℚ_p}` on `ℂ_p` and the
   Tate–Sen Hodge–Tate multiplicities (`htSpace`, `htMult`, `HasHTWeights`), with Pan's and N5's
   convention (cyclotomic weight `−1`). wk-h §3.1 and hdec-faithful rated HT "large"; it is
   about 80 lines.
3. **Leaves statable now (compiled): six.** Existence of eigenform representations; **HT weights
   of eigenform representations at every level** (new, needs item 2); Deligne–Serre finiteness;
   twisting; **Li's newform of an eigensystem** (new: newforms defined through the old space);
   **Carayol at unramified primes** (new). Three are hdec-faithful's, restated in this file.
4. **Templates (compiled, not leaves): Pan, Berger, Carayol.** Each is a function of exactly one
   missing predicate: `PanFor IsPst`, `BergerFor IsDR IsPst`, `CarayolFor a` (the `ℓ`-adic
   conductor exponent). Everything else in their statements is genuine: continuity,
   irreducibility, finite ramification, oddness, **distinct Hodge–Tate weights**, eigenforms,
   newforms, the twist-trace conclusion.
5. **Not statable: C3, C5 and Shimura's `A_f`.** They need abelian varieties with Tate modules
   (C3, C9), complex uniformization (C5) and `J₁(N)` over `ℚ` (C9). These objects belong to I2,
   I3 and I5 as well; I4 adds only the period rings.
6. **The biggest obstacle in I4 is the potentially semistable predicate**, and it can be
   replaced by "de Rham", which Mathlib's `BDeRham` nearly supports (§3.3). Stating Pan in the
   merged form "Pan after Berger" (de Rham at `p` instead of pst; a consequence of the two
   theorems) removes `B_st` entirely. What is missing for "de Rham" is the `G_{ℚ_p}`-action on
   `BDeRham (𝓞_ℂ_[p]) p` (naturality of Fontaine's `θ`, a ring map between adic completions
   through Mathlib's `AdicCompletion.liftRingHom`, a map of localizations) and the
   `ℚ_p`-algebra structure: about 400-800 lines (SPECULATIVE). Then Pan∘Berger is a leaf over
   genuine definitions.
7. **The coarse alternative (Ribet + Pyle + Khare–Wintenberger, §4) is sound for modularity,
   gives no level bound by itself, and is better for statability of the whole proof**: it
   needs no period rings, only abelian varieties with Tate modules, which the rest of H needs
   anyway. It replaces C3, C4, C5, C7 and the Hodge–Tate half of C8. Its statements were
   recalled, not read (hdec-alt R1; same here).

## 1. The inputs one by one

For each: the step, the published statement used, the most concrete faithful leaf formulation,
the Lean objects, and the status. Locators follow h-trust; "AUDIT-READ"/"ASTRA-READ" are
h-trust's marks.

### 1.1 Pan 2022, Theorem 1.0.4 (C7)

- **Published statement** (arXiv:1901.07166v2, FM.tex L226-233, VERIFIED in h-a011 §1.1; JAMS
  35 (2022) numbering UNVERIFIED). For an odd prime `p`, a continuous irreducible
  `ρ : G_ℚ → GL₂(ℚ̄_p)`, ramified at finitely many places, potentially semistable at `p` in
  Fontaine's sense, odd (`det ρ(c) = −1`), with distinct Hodge–Tate weights at `p`, and (only
  if `p = 3`) a residual condition, "comes from a cuspidal eigenform up to twist". Pan's
  conventions: cyclotomic HT weight `−1`; `Frob` geometric; a fixed `ι_p : ℚ̄_p ≅ ℂ`.
- **Used at** `p = 5` for `r₅` (N5 L755-757), hypotheses from C2 (irreducible), C6 (finite
  ramification), C3 + C4 (pst), C5 (odd), C3 (weights `{0, −1}`).
- **Leaf formulation (Lean: `PanFor`).** For `p ≥ 5` (drops the `p = 3` clause; a consequence):
  hypotheses as printed; conclusion in **trace form**: there are a normalized eigenform `g`
  (weight `k ≥ 1`, level `N`, nebentypus `χ`), a continuous character `ψ : G_ℚ → ℚ̄_p^×`,
  embeddings `ιC : ℚ̄ → ℂ`, `ιL : ℚ̄ → ℚ̄_p` and a finite set `S` with
  `tr ρ(Frob_q^{arith}) = ψ(Frob_q) · ιL(α_q)`, `ιC(α_q) = a_q(g)`, for every prime `q ∉ S` and
  every arithmetic Frobenius above `q`. Why this is implied by every reading: §2.1.
- **Lean objects.** All genuine in `I4.lean` except `IsPst`: `GaloisRep` (continuous into
  `GL₂(PadicAlgCl p)`), `IsIrreducible` (Burnside form), `FinitelyRamified` and `UnramifiedAt`
  (inertia of valuation subrings of `ℚ̄`, Mathlib's `ValuationSubring.inertiaSubgroup`),
  `IsOdd` (every complex conjugation, through all embeddings `ℚ̄ → ℂ`), `DistinctHTWeights`
  (new, §3.1), `IsNormalizedEigenform`, `AttachedUpToTwist`.
- **Status.** Template, compiled. Missing: `IsPst` (needs `B_st` with `φ`, `N`, `G_K`-action:
  very large) — or `IsDR` in the merged form of §2.2 (large but close to Mathlib).

### 1.2 The de Rham comparison and closure (C3)

- **Published statements.**
  - Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 (with Thms 9.1, 9.3 for the algebraic case) and
    corrigendum, Forum Math. Pi 4 (2016): for a proper smooth rigid-analytic `X/k`,
    `H^i(X_et, ℚ_p)` is de Rham with `D_dR = H^i_dR(X)` (VERIFIED wording, arXiv:1205.3463, by
    h-leaves §3.1). For abelian varieties the older algebraic sources suffice: Fontaine, LNM
    1016 (1983) and Fontaine–Messing (1987) for abelian varieties; Faltings 1989 and Tsuji 1999
    in general (attributions VERIFIED against Berger's survey by h-leaves §3.2; primary
    numbering UNVERIFIED).
  - `V_ℓ(A) ≅ H¹_et(A_F̄, ℚ_ℓ)^∨`: Mumford §§19-20, or Milne 1986, Thm 15.1(a) (UNVERIFIED).
  - Closure of de Rham representations under duals and subquotients: Fontaine, Astérisque 223
    (1994), Thm 3.8, p. 142 (h-trust C3; content UNVERIFIED).
- **Used** in N5's appendix lemma (L10939-11000) to get `r₅|G_{ℚ₅}` de Rham with weights
  `{0, −1}`. The descent and the weight count in that lemma are glue (new in N5, two model
  reviews: rv-h-trust, rv-h-c3).
- **Leaf formulation.** For an abelian variety `A` of dimension `g` over a finite extension `F`
  of `ℚ_p`, the `G_F`-representation `V_p(A)` is de Rham and has Hodge–Tate weights `0` and `−1`,
  each with multiplicity `g`. (A consequence of any source above with Tate duality.) Fontaine's
  closure is a separate leaf `DR(V) ⇒ DR(V^∨)` and `DR(V ⊕ W) ⇒ DR(V)`.
- **Alternative (h-leaves §3.3, option (b)).** QM surfaces have potentially good reduction
  (Lemma PG, from Raynaud and NOS, no new source). Then the crystalline comparison for good
  reduction (Faltings 1989; Coleman–Iovita 1999; Breuil 2000) gives `r₅` potentially
  crystalline, hence pst, with no Berger. This needs `B_cris`, which Mathlib lacks entirely,
  whereas Mathlib has `B_dR` as a ring. For Lean statability the de Rham route is cheaper; for
  trust, option (b) has one leaf fewer.
- **Lean objects.** Abelian varieties over a `p`-adic field with `V_p` and the Galois action
  (absent; Tau Ceti has abelian varieties as group schemes without Tate modules; Anthropic's
  FLT has Tate modules of Jacobians); `IsDR` (absent; §3.3). The HT half is statable once Tate
  modules exist, with `HasHTWeights` from `I4.lean`.
- **Status.** Not statable now. Missing: Tate modules (I3), `IsDR`.

### 1.3 Berger 2002 (C4)

- **Published statement.** Invent. Math. 148 (2002), Théorème 0.7 in the journal numbering
  (ASTRA-READ) = Thm 0.6 = Thm 5.19 of arXiv:math/0102179v3 (VERIFIED by rv-h-a011): a de Rham
  representation of `G_K` (`K/ℚ_p` finite) is potentially semistable.
- **Leaf formulation (Lean: `BergerFor IsDR IsPst`).** Exact.
- **Status.** Template. Not needed on option (b) of §1.2, nor in the merged leaf of §2.2.

### 1.4 Oddness: the Betti–étale comparison (C5)

- **Statement used.** For an abelian variety `A` over a number field `K ⊂ ℂ`,
  `V_ℓ(A) ≅ H₁(A(ℂ), ℚ) ⊗ ℚ_ℓ`, functorially in `A` and compatibly with complex conjugation
  `A(ℂ) → ᶜA(ℂ)` (SGA 4 XI 4.4, or Milne 1986; for abelian varieties this is the elementary
  identification `A[n](ℂ) = n⁻¹Λ/Λ` once `A(ℂ) = ℂ^g/Λ`). N5 L742-751 then argues on Hodge
  summands (glue; model-reviewed, Astra "descent", rv-h-a011 H5).
- **Lean objects.** `A(ℂ)` as a complex torus (analytification): absent.
- **Status.** Not statable. Not needed on the route of §4.

### 1.5 Galois representations of eigenforms (used by C8, C9, C10)

- **Published statements.** For a normalized eigenform `g ∈ S_k(Γ₁(N), χ)` and a prime `ℓ`
  there is a continuous semisimple `ρ_g : G_ℚ → GL₂(ℚ̄_ℓ)`, unramified outside `Nℓ`, with
  `tr ρ_g(Frob_p) = a_p(g)` and `det = χ·χ_cyc^{k−1}` (Tate normalization): Shimura 1971
  Thm 7.14 for `k = 2` (UNVERIFIED number), Deligne, Sém. Bourbaki 355 (1971) for `k ≥ 2`,
  Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 6.1 for `k = 1` (UNVERIFIED number).
- **Leaf formulation (Lean: `EigenformRepExists`, compiled; = hdec-faithful L27a).** The trace
  part only (consequence).
- **Status.** Statable now.

### 1.6 Hodge–Tate weights of eigenform representations, every level (C8, supplier (HT))

- **Published statements.** For `k ≥ 2` and every level (including `ℓ | N`): Saito, Invent.
  Math. 129 (1997) (pst at `ℓ`); Kato, Astérisque 295 (2004), §9.4 p. 188 (de Rham, jumps `0`,
  `k`), §§5.4, 6.3, 8.3 (all levels), (14.10.2)-(14.10.3) (normalization); or Scholl 1990 with
  the de Rham comparison and Fontaine's closure. Faltings, Math. Ann. 278 (1987) gives
  Hodge–Tate for `k ≥ 2`; whether it covers `ℓ | N` is UNVERIFIED (h-trust C8). Locators are
  h-trust's (UNVERIFIED).
- **Leaf formulation (Lean: `EigenformHT`, compiled, new).** A semisimple `ρ` attached to a
  normalized eigenform of weight `k ≥ 2` and any level has Hodge–Tate weights `{0, 1 − k}` at
  `ℓ` in the Tate normalization (cyclotomic weight `−1`; `tr ρ(Frob^{arith}) = a_p`). A
  consequence: de Rham and pst imply Hodge–Tate with the same weights. The semisimplicity
  hypothesis is needed: `AttachedTo` fixes only the semisimplification, and Hodge–Tate is not
  closed under extensions.
- **Normalization check (VERIFIED as an argument).** `AttachedTo` is the arithmetic-Frobenius
  normalization, as on `V_ℓ(J₁(N))` for `k = 2`, whose weights are `{0, −1}` (h-trust C8). Pan's
  cohomological normalization gives `{0, k − 1}` and differs by duality.
- **Status.** Statable now (VERIFIED: compiles).

### 1.7 Deligne–Serre finiteness in weight one (C8, `k = 1`)

- **Published statement.** Deligne–Serre 1974, Thm 4.1 (weight-one newforms have
  representations with finite image; UNVERIFIED number; h-trust uses it).
- **Leaf (Lean: `DeligneSerreFinite`, compiled; = hdec-faithful L27b).** Consequence form,
  with Chebotarev and Brauer–Nesbitt to pass to any semisimple attached `ρ`.
- **Use.** Excludes `k = 1`: finite image forces all HT weights `0` (STANDARD: a representation
  with finite image on inertia is `ℂ_p`-admissible with weight 0), contradicting `{0, −1}`.
- **Status.** Statable now.

### 1.8 Twisting, newforms, `A_f` (C9)

- **Twisting.** Shimura 1971 Prop. 3.64; Atkin–Li 1978 (UNVERIFIED numbers). Lean:
  `EigenformTwist` (compiled; = hdec-faithful L28a). Statable now.
- **Li's newforms.** Li, Math. Ann. 212 (1975), Thm 5 (strong multiplicity one; Miyake
  Thm 4.6.19), with `S = S^new ⊕ S^old` Hecke-stably. Leaf: every normalized eigenform of
  level `M` shares its eigenvalues at `p ∤ M` with a newform of level `N | M`. Lean:
  `NewformOfEigenform` (compiled, new). Statable now, with `IsNewform` defined through the old
  space (§2.4).
- **Conjugates of newforms are newforms.** Shimura 1971 Thm 3.52 (rationality of the old/new
  decomposition) — needed only on N5's Fricke route. Statable now in the same way (not drafted:
  the `K_f`-linear route below does not use it).
- **Shimura's `A_f` and the `K_f`-linear Eichler–Shimura relation.** Shimura, J. Math. Soc.
  Japan 25 (1973), Thm 1 (AUDIT-READ); Shimura 1971 Thm 7.9 (`T_p = Frob_p + p⟨p⟩Frob_p⁻¹` on
  `J₁(N)`); Ribet 1977 (`V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`). Leaf: for a weight-two
  newform `f` of level `N`, `V_ℓ(J₁(N)) ⊗ ℚ̄_ℓ` has a 2-dimensional `G_ℚ`-quotient attached to
  `f` (in the sense of `AttachedTo`). Lean objects: `X₁(N)`, `J₁(N)` over `ℚ` with Tate module
  (absent everywhere; Anthropic's FLT has mod-`𝔪` Hecke-Galois actions on Jacobian torsion).
  Not statable now. This leaf is the interface to I3/I5 (the isogeny `J₁(N) → A × Z` of E1).

### 1.9 Carayol 1986, Théorème (A) (D5)

- **Published statement.** Ann. Sci. ÉNS 19 (1986), 409-468, Théorème (A), §§0.3-0.7,
  pp. 409-411 (N5's locator at L9778, VERIFIED as what N5 cites; content UNVERIFIED): for a
  Hilbert eigenform of weight `≥ 2`, `ρ_{f,λ}` restricted to a decomposition group at `v ∤ ℓ`
  corresponds to `π_v` under local Langlands, under a discrete-series hypothesis when
  `[F:ℚ]` is even (vacuous for `F = ℚ`). With Casselman's theory of the conductor of `π_p`,
  this gives `v_p(N) = a_p(ρ_f)` for a newform of level `N` and `p ≠ ℓ`. Version 14 cited
  Carayol, Astérisque 147-148 (1987) instead (h-v14 row L1477-1481, UNCHECKED). Whether the
  conductor equality is printed as part of Théorème (A) at `p | N` is h-trust D5's open check.
- **Leaf formulations.** (a) Template `CarayolFor a`: `a(ρ, p) = v_p(N)` for `p ≠ ℓ`, weight 2.
  (b) **Statable now (`CarayolUnramified`, compiled, new):** if `ρ` attached to a weight-two
  newform of level `N` is unramified at `p ≠ ℓ`, then `p ∤ N` (the case `a = 0`; a
  consequence).
- **Lean objects.** The Artin conductor exponent of an `ℓ`-adic representation at `p ≠ ℓ`:
  `codim V^{I_p}` plus the Swan conductor, which needs upper-numbering ramification groups of
  `G_{ℚ_p}` (absent in Mathlib; Tau Ceti has them for finite extensions and characters, not for
  `ℓ`-adic representations). The glue task glue-conductor needs the same definition for
  D1-D4; it should be built once.
- **Status.** (b) statable now; (a) template.

### 1.10 Inputs from other packages used inside I4's glue

Faltings 1983 Satz 3 (semisimplicity, for C2 and for `A_f` in C9) — I3; Chebotarev,
Brauer–Nesbitt, Kronecker–Weber — I6 (all three statable now: hdec-faithful L17-L19, hdec-alt);
the Weil pairing of a polarization (C8's determinant argument) — I3.

## 2. Readings and normalizations

### 2.1 Pan's conclusion in trace form (VERIFIED as an argument)

Pan's introduction does not define "comes from a cuspidal eigenform up to twist" (h-a011 §1.1).
Every reading gives `ρ ≅ ρ_g^{P} ⊗ ψ` for some eigenform `g`, continuous `ψ`, and `ρ_g^{P}` the
representation of `g` in *some* normalization. The trace form of `PanFor` follows in each case:

- Let `ρ_g^{A}` be the arithmetic normalization: `tr ρ_g^{A}(Frob_q^{arith}) = a_q`,
  `det ρ_g^{A} = χ_g χ_cyc^{k−1}`. Pan's cohomological `ρ_g^{P}` has
  `tr ρ_g^{P}(Frob_q^{geom}) = a_q` and `det ρ_g^{P}(Frob_q^{geom}) = χ_g(q) q^{k−1}`. Then
  `tr ρ_g^{P}(Frob_q^{arith}) = tr ρ_g^{P}(Frob_q^{geom})⁻¹ = a_q / (χ_g(q) q^{k−1})`, which is
  the trace of `ρ_g^{A} ⊗ (χ_g χ_cyc^{k−1})⁻¹`. So `ρ_g^{P} ≅ ρ_g^{A} ⊗ ψ₀` with `ψ₀` a
  character (for two-dimensional `U`, `U^∨ ≅ U ⊗ det U⁻¹`), and
  `ρ ≅ ρ_g^{A} ⊗ ψψ₀` has `tr ρ(Frob_q^{arith}) = (ψψ₀)(Frob_q) · a_q` for `q ∤ Np` with `ψ`
  unramified at `q`. Finitely many `q` are excluded: every continuous character
  `G_ℚ → ℚ̄_p^×` is ramified at finitely many primes (through `G_ℚ^{ab} = ℤ̂^×` it is trivial on
  an open subgroup of `∏_{q≠p} ℤ_q^×`, since its image has an open pro-`p` subgroup; STANDARD).
- If a reading uses `\bar a_q` instead of `a_q`: `\bar a_q = χ_g(q)⁻¹ a_q` for `q ∤ N`, again a
  twist.
- The embeddings: Pan fixes `ι_p`; the trace form asks for some pair `(ιC, ιL)`, which is weaker.
- The trace form is weaker than an isomorphism, but sufficient: with Chebotarev,
  Brauer–Nesbitt, irreducibility of `ρ` and `EigenformRepExists` it gives `ρ ≅ ρ_g ⊗ ψ'` back.

So `PanFor IsPst` (with the genuine `IsPst`) is a consequence of Pan's theorem. hdec-faithful
reached the same reading (its R2).

### 2.2 pst versus de Rham: a merged leaf that avoids `B_st`

Pan's hypothesis is pst (h-a011 §1.1, VERIFIED there), not de Rham as the task statement and
wk-h §2 abbreviate. N5 gets pst from de Rham by Berger. For Lean the cheapest faithful form is
the merged statement

> **Pan∘Berger.** The hypotheses of `PanFor` with "de Rham at `p`" in place of "pst at `p`"
> imply its conclusion.

It is a consequence of the two published theorems (Berger turns de Rham into pst), and needs
only `IsDR`, never `B_st`. In Lean it is `PanFor IsDR` once `IsDR` exists, and `BergerFor` is
then not needed as a separate leaf. Its weakness as a leaf is attribution: one Prop now carries
two papers. Recommendation (SPECULATIVE): state Pan∘Berger as the leaf, with the docstring
naming both theorems. The alternative, option (b) of h-leaves (potentially crystalline via good
reduction), needs `B_cris`, which is further from Mathlib.

### 2.3 Hodge–Tate weights in Lean, and the convention (VERIFIED as an argument; the Lean compiles)

For `E/ℚ_p` finite and `ρ : G_{ℚ_p} → GL_n(E)`, `V = E^n`:

`H_i(ρ) = { φ : V →_{ℚ_p} ℂ_p | φ(ρ(σ)v) = χ(σ)^i · σ(φ(v)) for all σ, v }`.

`Hom_{ℚ_p}(V, ℂ_p) = ℂ_p ⊗ V^∨`, and `φ` is invariant under `σ · φ = χ(σ)^i σ ∘ φ ∘ ρ(σ)⁻¹`
exactly when it is in `H_i`; so `H_i = (ℂ_p(i) ⊗ V^∨)^{G}`. The multiplicity of the weight `w`
is `htMult ρ w = dim_{ℚ_p} H_{−w} / [E:ℚ_p]`. Check: for `V = ℚ_p(1)`, `H_i ≅ ℂ_p(i − 1)^G`,
non-zero exactly for `i = 1` (Tate's theorem `ℂ_p(j)^G = 0` for `j ≠ 0`); so `ℚ_p(1)` has weight
`−1`, the convention of N5 (L757) and of Pan. For `K = ℚ_p` the HT weights do not depend on the
embedding of `E` (`K ⊗ E = E` is a field), and the multiplicities do not depend on `E` (base
change; STANDARD), so `LocalHasHTWeights` may quantify `∃ E`.

What is defined but not proved in `I4.lean`: no theorem about `htMult` (for instance
`Σ_w htMult ≤ n`, Tate–Sen, or the value for the trivial representation, which is Ax–Sen–Tate).
These are not needed to state the leaves; they would be needed to prove glue such as C8's weight
comparison from the definitions.

### 2.4 Newforms without the Petersson integral

Mathlib has the Petersson integrand (`petersson`) but no integral over `Γ₁(N)\ℍ`. `I4.lean`
defines the old space (span of `τ ↦ f(dτ)`, `f ∈ S_k(Γ₁(M))`, `M | N`, `M < N`, `dM | N`) and
`IsNewform f χ` := normalized eigenform of all `T_n` and `f ∉ oldSpace`. For an eigenform of all
`T_n` (including `U_p`, `p | N`) this is equivalent to Li's definition: `S^new` and `S^old` are
Hecke-stable, an eigenform splits as `f_new + f_old` with both components eigen for the same
eigenvalues, and by strong multiplicity one a newform's eigenvalues away from `N` do not occur in
`S^old` (Li 1975 Thms 3, 5; Diamond–Shurman Thm 5.8.2; STANDARD, locators UNVERIFIED). Tau Ceti
has genuine Hecke operators and newforms (`HeckeRing.GL2.Newform`), which should replace these
definitions when imported. `IsNormalizedEigenform` is hdec-faithful's (Hecke recursion of
coefficients; equivalent to the Hecke definition, Diamond–Shurman Prop. 5.3.1, UNVERIFIED).

### 2.5 Small corrections to earlier notes

- wk-h §2 and the task statement describe Pan's hypothesis as de Rham; it is pst (§2.2).
- wk-h §3.1 and hdec-faithful's definitions table rate Hodge–Tate representations "large"; over
  Mathlib v4.35 they are cheap (§3.1). De Rham remains large, `B_st` very large.
- hdec-faithful's `L26_EigenformHT` placeholder can be replaced by `EigenformHT` here, and its
  `L28b_Newforms` by `NewformOfEigenform`; `L30_Carayol` can be split into `CarayolUnramified`
  (statable) and the template.

## 3. Lean (`scratch/pkg-I4/I4.lean`)

Compiles with `lake env lean scratch/pkg-I4/I4.lean` (VERIFIED, log Step 2). `#print axioms`
of the proved lemmas: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.

### 3.1 Definitions

| Definition | Content | Built on (Mathlib) |
| --- | --- | --- |
| `GQ`, `LiesOver`, `IsArithFrob`, `GaloisRep`, `UnramifiedAt`, `IsComplexConj`, `IsOdd`, `IsIrreducible`, `IsSemisimple` | as hdec-faithful §0 | `AlgebraicClosure`, `ValuationSubring.decompositionSubgroup/inertiaSubgroup`, `PadicAlgCl` |
| `GaloisChar`, `FinitelyRamified`, `mat` | characters, finite ramification | — |
| `GQp p`, `decomp`, `restrictLocal` | `G_{ℚ_p}`, `G_{ℚ_p} → G_ℚ`, `ρ|_{G_{ℚ_p}}` | `Field.absoluteGaloisGroup.map` |
| `cpAct` (+ `continuous_gqp`, `cpAct_coe`, `cpAct_algebraMap`, proved) | `G_{ℚ_p}` acting on `ℂ_[p]`, fixing `ℚ_p` | `spectralNorm_eq_of_equiv`, `UniformSpace.Completion.mapRingHom` |
| `cyc`, `cycPow` | cyclotomic character, `χ^i ∈ ℚ_p` | `cyclotomicCharacter` |
| `htSpace` (submodule axioms proved), `htMult`, `HasHTWeights`, `LocalHasHTWeights`, `HasHTWeightsAtSelf`, `DistinctHTWeights` | Hodge–Tate multiplicities (§2.3) | `Module.finrank`, `IntermediateField` |
| `CF`, `coeff`, `HasNebentypus`, `IsNormalizedEigenform` | as hdec-faithful | `CuspForm`, `Gamma1`, `qExpansion`, `DirichletCharacter` |
| `scaleH`, `oldSpace`, `IsNewform` | old space, newforms (§2.4) | `Submodule.span` |
| `AttachedTo`, `AttachedUpToTwist` | trace form of `ρ ≅ ρ_g`, `ρ ≅ ρ_g ⊗ ψ` | — |

### 3.2 Statements

| Name | Kind | Input |
| --- | --- | --- |
| `EigenformRepExists` | leaf, statable | §1.5 |
| `EigenformHT` | leaf, statable (new) | §1.6 |
| `DeligneSerreFinite` | leaf, statable | §1.7 |
| `EigenformTwist` | leaf, statable | §1.8 |
| `NewformOfEigenform` | leaf, statable (new) | §1.8 |
| `CarayolUnramified` | leaf, statable (new; consequence of Thm (A)) | §1.9 |
| `PanFor IsPst` | template (missing `IsPst`, or `IsDR` for Pan∘Berger) | §1.1, §2.2 |
| `BergerFor IsDR IsPst` | template | §1.3 |
| `CarayolFor a` | template (missing `ℓ`-adic conductor) | §1.9 |
| `weight_match`, `weight_match_coh` | glue, **proved** | C8 weight arithmetic in both normalizations |

### 3.3 What the de Rham predicate needs from Mathlib (SPECULATIVE sizes; facts VERIFIED by grep)

`D_dR(V) = (B_dR ⊗_{ℚ_p} V)^{G_{ℚ_p}}`, and `V` is de Rham when `dim_{ℚ_p} D_dR(V) = dim_{ℚ_p} V`
(with `K = ℚ_p`). In the Hom form of §2.3 this is the space of `φ : V^∨ →_{ℚ_p} B_dR` with
`φ ∘ ρ^∨(σ) = σ ∘ φ`. Pieces:

| Piece | In Mathlib v4.35 | Missing work |
| --- | --- | --- |
| `B_dR^+ = AdicCompletion (ker θ[1/p]) (W(R♭)[1/p])`, `B_dR` = localization at generators of `ker θ`, for `R = 𝓞_ℂ_[p]` | yes: `BDeRhamPlus`, `BDeRham`, `PadicComplexInt` | — |
| action of `σ` on `ℂ_p`, isometric | built here (`cpAct`) | isometry of the extension, restriction to `𝓞_ℂ_[p]` (short) |
| `R♭` functorial in `R` | `Perfection.map`, `ModP` is a quotient | `PreTilt.map` (short) |
| `W(-)`, `W(R♭)[1/p]` functorial | `WittVector.map`, `IsLocalization.Away.map` | — |
| naturality `f ∘ θ_R = θ_S ∘ W(f♭)` | no; but `eq_of_apply_teichmuller_eq` and `fontaineTheta_teichmuller` reduce it to naturality of `untilt` | 100-200 lines |
| ring map of adic completions for `f(J) ⊆ J'` | `AdicCompletion.liftRingHom` (compatible maps to quotients) | 50-100 lines |
| map of `B_dR` (generators of `ker θ` go to generators under an automorphism) | `IsLocalization.map` | 50-100 lines |
| `ℚ_p → B_dR` and `ℚ_p`-linearity of the action | `ℤ_p ≅ W(𝔽_p)`-type equivalences exist for `WittVector` | 100-200 lines |
| `IsDR` as a finrank condition; Fontaine's filtration (only for weights) | — | 50 lines; weights can be read with `htMult` instead (HT weights of a de Rham representation are its filtration jumps) |

Total about 400-800 lines (SPECULATIVE). With it, Pan∘Berger (§2.2) is a leaf over genuine
definitions. The fact that `B_dR(𝓞_ℂ_p)` from Mathlib's general-perfectoid definition is the
classical `B_dR` (needs `ker θ` principal, a TODO in Mathlib's file) is not needed to *state*
the leaf: the definition is the classical one by construction (completion of `W(R♭)[1/p]` along
`ker θ`), and the localization at all generators agrees with inverting one generator once
`ker θ` is principal (STANDARD).

## 4. The coarse alternative: Ribet, Pyle, Khare–Wintenberger

wk-h §2 proposed, and hdec-alt §1.2 and hdec-elementary (its route K) adopted, modularity
through building blocks. The argument as hdec-alt writes it (steps 1-6) is correct as I read it
(VERIFIED as an argument, given the leaves):

1. `A_ℚ̄` with the `B`-linear `μ_σ` is a building block (`End⁰ = B` central over `ℚ`,
   `t[F:ℚ] = 2 = dim A`, all conjugates `B`-isogenous).
2. Ribet 1992 / Pyle 2004: a building block is a `ℚ̄`-factor of an abelian variety `B₀/ℚ` of
   `GL₂`-type (UNVERIFIED form; Ribet, *Abelian varieties over `ℚ` and modular forms*, repr.
   Progr. Math. 224 (2004), 241-261; Pyle, same volume).
3. Khare–Wintenberger 2009 (Serre's conjecture) with Ribet 1992 Thm 4.4 (Serre's conjecture
   ⇒ `GL₂`-type over `ℚ` modular; UNVERIFIED number): `B₀` is a factor of `J₁(N₀)`, so each
   `λ`-constituent `ρ_τ` of `V_ℓ(B₀)` is `ρ_{f₀}` for a weight-two newform.
4. `ρ_τ|G_K ≅ r_ℓ|G_K` (Faltings semisimplicity and C2), so `r_ℓ ≅ ρ_τ ⊗ ψ` with `ψ` of finite
   order (a character of `Gal(K/ℚ)` on the line `Hom_{G_K}(ρ_τ, r_ℓ)`), a Dirichlet character
   by Kronecker–Weber; absorb it (twisting, Li).

Assessment:

- **What it replaces.** C3 (de Rham comparison and the appendix lemma), C4 (Berger), C5
  (oddness), C7 (Pan), and C8's Hodge–Tate comparison, Deligne–Serre and the determinant
  argument: weight 2 comes for free from `J₁(N₀)`. That removes both N5-new passages in C3 and
  C8 from the trust base.
- **What it does not replace.** The level bound. `N₀` (the level of `B₀`) is not controlled:
  `B₀` comes from Tate's vanishing of `H²(G_ℚ, ℚ̄^×)` (non-effective), and its dimension is not
  bounded in `M` (hdec-alt §1.1(ii)). So the scalar descent B1-B3 (Glazer's effective `β`), the
  conductor bound D1-D4 for Glazer's `r_ℓ`, and Carayol (D5) stay: the twist step 4 brings the
  modular form back to `r_ℓ` itself, whose conductor D bounds. C9 (newform of `r_ℓ`, `A_f`)
  and C10 stay.
- **Statability.** Its leaves need abelian varieties over `ℚ` and `ℚ̄` with `End⁰`, Tate modules
  with Galois action, and `J₁(N)` (or `ρ_f`): objects that I2, I3 and C9 need anyway. Pan's
  route needs the same objects for C3 and in addition period rings (`B_dR` with action, or
  `B_st`). So **the alternative is better for a statable decomposition of H as a whole**, even
  though Pan's own statement, taken alone, is closer to Mathlib (only `IsPst` missing).
- **Trust.** Ribet's theorem appeared in a workshop proceedings reprinted in a refereed volume;
  its exact printed form, and the precise hypotheses on the `μ_σ` (compatibility with all of
  `End⁰`), must be read before adoption (hdec-alt R1). Khare–Wintenberger is refereed (Invent.
  Math. 178 (2009)). Which statement of KW (or of Kisin, Invent. Math. 178 (2009), with KW)
  states "`GL₂`-type abelian varieties over `ℚ` are modular" is UNVERIFIED here.
- **A middle form.** Serre's conjecture in its weak form ("an odd irreducible
  `ρ̄ : G_ℚ → GL₂(𝔽̄_p)` is the reduction of `ρ_g` for some eigenform `g`") is statable now with
  the objects of `I4.lean` (finite-field coefficients and reduction of `a_q` modulo a prime of
  `ℤ̄`). It is not sufficient for step 3: Ribet's Thm 4.4 needs the strong form (bounded level,
  Artin conductor of `ρ̄`, Serre weight), whose conductor again needs ramification groups.
  Not drafted.

## 5. Glue inside I4 (for the glue tasks)

- **C8 weights.** `weight_match` and `weight_match_coh` (proved) are the arithmetic. The
  representation-theoretic part — the line `Hom(ρ_g ⊗ ψ, r)` is Hodge–Tate, HT weights of a
  twist by a HT character shift, HT of `Hom` and of subobjects — needs theorems about `htMult`
  (Tate–Sen theory: `Σ_w htMult ≤ n`, exactness of `D_HT` on HT representations), none in
  Mathlib. These are textbook (Fontaine, Astérisque 223, §§1-3; STANDARD) and would be further
  leaves or glue, not part of Pan.
- **C8 determinant argument** (h-trust C8 items 1-4): Weil pairing (I3), Kronecker–Weber (I6),
  `α² = 1` on an open subgroup ⇒ finite image (elementary, statable now over `GaloisChar`).
- **C9 constituent argument**: Brauer–Nesbitt plus Chebotarev plus the `K_f`-linear
  Eichler–Shimura relation (§1.8); conductor of the dual equals the conductor (Serre, *Corps
  locaux* VI §2; needs the conductor definition).
- **C10**: Mumford §19 Thm 4 (I3), Néron property (I2), Chebotarev and Brauer–Nesbitt (I6).

## 6. Biggest obstacle and recommendations

1. **Obstacle.** The potentially semistable (or de Rham) predicate, together with Tate modules
   of abelian varieties. Without them, Pan (C7) and the comparison (C3) cannot be stated, and
   the part of H that holds Glazer's new modularity argument stays outside Lean.
2. **Cheapest path to stating Pan:** build `IsDR` over Mathlib's `BDeRham` (§3.3, 400-800
   lines), then state Pan∘Berger (§2.2). Everything else in Pan's statement is already genuine
   in `I4.lean`.
3. **For the whole of H, prefer the coarse route of §4** once Ribet's and KW's printed
   statements are read: it needs no period rings at all.
4. **Adopt now** in the synthesis: the six statable leaves of §3.2 (with `EigenformHT`,
   `NewformOfEigenform`, `CarayolUnramified` replacing hdec-faithful's placeholders), and the
   HT definitions.
5. **Checks to make first** (no network here): Pan's JAMS numbering; Carayol's Théorème (A) at
   `p | N` and whether the conductor equality is printed; Faltings 1987's hypothesis on the
   level; Ribet 1992 Thm 4.4 and Pyle's building-block theorem; the KW statement for `GL₂`-type
   varieties.
