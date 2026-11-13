# r10-amend: the amended leaf R10 and glue step G9

Status: research note, task r10-amend, 2026-11-13. Branch `wip/r10-amend`, based on
`wip/integrate-w39` (`322303a2`). The Lean files are new, under `ZInQKernel/Contrib/R10/`. No
existing project file was edited. Log: `scratch/r10-amend/log.md`.

Marks: **VERIFIED** = compiled in Lean, or read in a source on this host; **STANDARD** = published,
with a reference; **SPECULATIVE** = an assessment. Locators recalled from memory are UNVERIFIED.
This host has no literature sources: the only one is the manuscript `diophantine_zq.tex`.

## 1. Main result

All declarations below compile, and `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for every theorem (VERIFIED: `lake build ZInQKernel.Contrib.R10.Amend
ZInQKernel.Contrib.R10.Glue`). Namespace `ZInQ.Contrib.R10`. The objects are g9-derham's verbatim
copies of the pkg-I4 layer (`ZInQ.Contrib.G9.PkgI4`, `I4Layer.lean`) and of `G9Glue`
(`ZInQ.Contrib.G9.G0Galois`, `Statement.lean`).

**The amended leaf** (`ZInQKernel/Contrib/R10/Amend.lean`):

```lean
def DeRhamComparisonHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F),
    (∀ g : ℕ, A.dim = (g : WithBot ℕ∞) →
      IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
        htMultOver p (A.galRep p) (-1) = g) ∧
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0
```

The first conjunct is the old R10 (`PkgI4.DeRhamComparison`) for this `A`. The second is the
multiplicity-0 clause. It has no dimension hypothesis, because it holds for every abelian variety.

**Proved about it** (`Amend.lean`):

```lean
theorem deRhamComparison_of_HT (h : DeRhamComparisonHT) : PkgI4.DeRhamComparison
theorem r10Weights_of_HT (h : DeRhamComparisonHT) : G9Bridge.R10Weights
theorem deRhamComparisonWeights_of_HT (h : DeRhamComparisonHT) : DeRhamComparisonWeights
theorem deRhamComparisonHT_iff :
    DeRhamComparisonHT ↔ PkgI4.DeRhamComparison ∧ G9Bridge.R10Weights
theorem htMultOver_eq_of_HT (h : DeRhamComparisonHT) (p) [Fact p.Prime] (F) [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : PkgI4.I3.AbVar F) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) (w : ℤ) :
    htMultOver p (A.galRep p) w = g * ({0, -1} : Multiset ℤ).count w
```

`deRhamComparisonHT_iff` shows that the amendment adds exactly g9-derham's clause `R10Weights`
and nothing else. `DeRhamComparisonWeights` is run 3c's version, with a dimension hypothesis
(`Contrib/G9/G9Weights.lean`).

**G9** (`ZInQKernel/Contrib/R10/Glue.lean`):

```lean
/-- G9Glue with R10 replaced by the amended leaf; T23 dropped (unused by the proof). -/
def G9GlueHT : Prop :=
  DeRhamComparisonHT →
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G9Out r
/-- G9Glue verbatim with R10 replaced by the amended leaf (T23 kept). -/
def G9GlueHT' : Prop := DeRhamComparisonHT → (∀ p [Fact p.Prime], T23_FontaineClosure p) → …

theorem g9GlueHT'_of_g9GlueHT (h : G9GlueHT) : G9GlueHT'
theorem g9Glue_of_HT (hBC : G9Bridge.AbVarBaseChange) (hR : DeRhamComparisonHT) : G9Glue
theorem g9GlueHT_of_abVarBaseChange (hBC : G9Bridge.AbVarBaseChange) : G9GlueHT
```

`#print axioms` output (VERIFIED, from the build):

```
'ZInQ.Contrib.R10.deRhamComparison_of_HT' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.R10.r10Weights_of_HT' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.R10.deRhamComparisonWeights_of_HT' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.R10.deRhamComparisonHT_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.R10.htMultOver_eq_of_HT' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.R10.g9GlueHT'_of_g9GlueHT' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.R10.g9Glue_of_HT' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.R10.g9GlueHT_of_abVarBaseChange' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**The status of G9.** It now depends on the amended R10 (a leaf) and on
`G9Bridge.AbVarBaseChange`. Task g9-abvarbc is proving the latter (see §5 for the state at the end
of this task).

## 2. The published statement (task part 1)

**What is needed.** For an abelian variety `A/F` of dimension `g` over a finite `F/ℚ_p`, put
`V = V_p(A)`. The multiplicity `htMultOver w` must be `g` for `w ∈ {0, −1}` and `0` for every other
`w`.

**Sources and locators. None of them is on this host, so all are UNVERIFIED** (the task rules
allow VERIFIED only for a source read here):

1. *Hodge–Tate decomposition, general case.* G. Faltings, *p-adic Hodge theory*, J. Amer. Math.
   Soc. 1 (1988), 255–299, **Chapter III, Theorem 4.1**. For `X` proper and smooth over `F`:
   `H^n_et(X_F̄, ℚ_p) ⊗ ℂ_p ≅ ⊕_i H^{n−i}(X, Ω^i_X) ⊗_F ℂ_p(−i)`, `G_F`-equivariantly.
   - The locator is the one the manuscript itself uses (`diophantine_zq.tex` L11003, "The
     Hodge--Tate comparison in \cite[Chapter III, Theorem 4.1]{faltings1988}"). That this citation
     is in the manuscript is VERIFIED. Faltings's text is UNVERIFIED.
2. *Abelian varieties, every reduction type.* J.-M. Fontaine, *Formes différentielles et modules
   de Tate des variétés abéliennes sur les corps locaux*, Invent. Math. 65 (1982), 379–409.
   - It proves the Hodge–Tate decomposition of `ℂ_p ⊗ T_p(A)` for every abelian variety over
     `F`, with no reduction hypothesis.
   - The exact printed form, the section and the theorem number are UNVERIFIED.
3. *Good reduction.* J. Tate, *p-divisible groups*, Proc. Conf. Local Fields (Driebergen 1966),
   Springer 1967, 158–183.
   - §4, Corollary 2 of Theorem 4 (UNVERIFIED numbering): for a `p`-divisible group `G` over
     `𝒪_F`, `T(G) ⊗ ℂ_p ≅ Hom(t_{G'}, ℂ_p) ⊕ (t_G ⊗ ℂ_p(1))`.
4. *Tate's theorem on `ℂ_p(j)`.* Tate 1967, **§3.3, Theorem 2** (UNVERIFIED numbering):
   `H⁰(G_F, ℂ_p(j)) = F` for `j = 0` and `= 0` for `j ≠ 0`.
   - Also Brinon–Conrad, *CMI notes* (2009), Theorem 2.2.7 (UNVERIFIED).
5. *De Rham part* (unchanged from R10): Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 with Thms 9.1
   and 9.3, and the 2016 corrigendum; or Faltings 1989 and Tsuji 1999.
   - `docs/research/locators.md` (row R10) records that another task read Scholze's v2 and journal
     texts. That is not a reading on this host: UNVERIFIED here.
   - Scholze's Cor. 1.8 also yields the Hodge–Tate decomposition: take `gr⁰` of the filtered
     `B_dR`-comparison (STANDARD).
6. *Hodge numbers and duality.*
   - `dim_F H⁰(A, Ω¹) = dim_F H¹(A, 𝒪_A) = g`: Mumford, *Abelian varieties*, §4 and §13
     (UNVERIFIED).
   - `V_p(A) ≅ H¹_et(A_F̄, ℚ_p)^∨`: Milne, *Abelian varieties* (2008), Part I, Thm 12.1(a), as cited
     by the manuscript (VERIFIED: the citation is in the tex, L10969).

**Derivation of the full statement** (STANDARD, from items 1 or 2, 4 and 6). Put `H = V^∨ = H¹_et`.

- (1) or (2) gives `ℂ_p ⊗ H ≅ ℂ_p^g ⊕ ℂ_p(−1)^g`, `G_F`-equivariantly.
- Hence `(ℂ_p(i) ⊗ H)^{G_F} ≅ (ℂ_p(i)^{G_F})^g ⊕ (ℂ_p(i−1)^{G_F})^g`.
- By (4), its `F`-dimension is `g·[i = 0] + g·[i = 1]`. Its `ℚ_p`-dimension is `[F:ℚ_p]` times
  that.
- In particular it is `0` for every `i ∉ {0, 1}`.

So the source gives **both weights with multiplicity `g`, and nothing else**. The vanishing is a
consequence of the decomposition together with Tate's theorem (4), which is a separate theorem of
the same 1967 paper. It is not printed as one sentence. R10's old Lean form was already a
"consequence form" in the same way.

**Sign convention** (VERIFIED by reading the definitions in `I4Layer.lean` L856-879 and
L1206-1225):
- `htSpaceOver p ρ i` is the space of `ℚ_p`-linear `φ : V → ℂ_p` with
  `φ(ρ(σ)v) = χ(σ)^i · σ(φ v)`, i.e. `Hom_{G_F}(V, ℂ_p(i)) = (ℂ_p(i) ⊗ V^∨)^{G_F}`.
- `htMultOver p ρ w = dim_{ℚ_p} htSpaceOver p ρ (−w) / [F:ℚ_p]`.
- So weight `w` corresponds to `i = −w`: the source's `i = 0` is `w = 0`, and `i = 1` is
  `w = −1`. This is the Tate convention (`ℚ_p(1)` has weight `−1`), the same as the old R10, as
  N5's lemma ("with `ℚ_ℓ(1)` assigned weight −1"), and as `G9Out`.
- In the other common convention (`ℚ_p(1)` of weight `+1`, as in Faltings and Fontaine) the
  weights are `0, 1`. That is the same statement.

**Never stronger than the source.**
- Every conjunct of `DeRhamComparisonHT` is an instance of the derivation above, under the
  identification `ℂ_F ≅ ℂ_p` that pkg-I4's `gfToGqp` fixes.
- The dimension-free weight clause is the case `i ∉ {0, 1}` of the derivation. It holds whatever
  `g` is.
- The amendment trusts pkg-I4's definitions of `AbVar`, `V`, `galRep` and `htMultOver` to model the
  classical objects, exactly as the old R10 does.
  - I checked one point of this (VERIFIED by reading): `galAct σ P = Spec(σ) ≫ P` applies `σ` to
    coordinates, and `galRep` is a left action. So `galRep` is the usual Galois action.
  - Faithfulness of these definitions in general is the leaf-statement review's question, not
    changed here.

## 3. Statement-change proposal (for the integrator's leaf-fold/leaf-adopt; not applied here)

R10 is a leaf in `scratch/h-decomposition/Leaves.lean` (`ResearchLeaves.r10 :
PkgI4.DeRhamComparison`, L33371; definition L4538). Proposed change:

(a) In `Leaves.lean`, section `PkgI4Sec`, namespace `PkgI4`, directly after `def
DeRhamComparison` (L4538-4542), add:

```lean
/-- **I4-L0 amended (R10 with the full Hodge–Tate weights)** (task r10-amend). For an abelian
variety `A` over a finite `F/ℚ_p`: if `dim A = g`, `V_p(A)` is de Rham with Hodge–Tate weights `0`
and `−1` each of multiplicity `g` (`DeRhamComparison`), and every other weight has multiplicity
`0`. Faltings, JAMS 1 (1988), Ch. III Thm 4.1 (Hodge–Tate decomposition; Fontaine, Invent. Math.
65 (1982) for abelian varieties) with Tate 1967 §3.3 (`ℂ_p(j)^{G_F} = 0` for `j ≠ 0`); de Rham part
as in `DeRhamComparison`; numbers UNVERIFIED. -/
def DeRhamComparisonHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F),
    (∀ g : ℕ, A.dim = (g : WithBot ℕ∞) →
      IsDeRhamOver p (A.galRep p) ∧ htMultOver p (A.galRep p) 0 = g ∧
        htMultOver p (A.galRep p) (-1) = g) ∧
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0
```

(b) In `structure ResearchLeaves`, replace `r10 : PkgI4.DeRhamComparison` by
`r10 : PkgI4.DeRhamComparisonHT`.

(c) Keep `def DeRhamComparison` as a derived Prop, so that existing consumers (G9's
`G9Glue` hypothesis, `Contrib/G9`) are unaffected. `deRhamComparison_of_HT` gives it from the new
field in one line.

(d) G9 then follows as `g9Glue_of_HT hBC leaves.r10 : G9Glue`. Once `AbVarBaseChange` is proved, it
follows from `leaves.r10` alone.

The amended text is (a) verbatim. The definition in `Contrib/R10/Amend.lean` is the same text
over g9-derham's verbatim copy of `PkgI4Sec` (namespace `ZInQ.Contrib.G9.PkgI4`).

## 4. Proof notes

- `deRhamComparison_of_HT`, `r10Weights_of_HT` and `deRhamComparisonHT_iff` are projections and
  pairings.
- `g9GlueHT_of_abVarBaseChange` reuses g9-derham's proof of `g9Glue_of_fieldEmb`
  (`Contrib/G9/Reduction.lean`) almost verbatim. The changes:
  - `LocalModel` comes from `localModel_of_abVarBaseChange`;
  - `F' ⊆ B_dR` comes from `fieldEmbBdR`;
  - the old R10 and `R10Weights` are both read off the amended leaf.

  The proof never uses T23, so `G9GlueHT` drops it. `G9GlueHT'`, which keeps it, follows
  trivially.

## 5. What remains

See `.fleet/r10-amend.md` for the final state of the merge with g9-abvarbc.
