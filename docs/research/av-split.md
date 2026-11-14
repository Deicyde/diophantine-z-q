# av-split: the abelian-variety GLUE rows of frontier r3 split into published forms

Task av-split, 2026-11-14. Base: fork main cba8157f (w54 + frontier r3), branch wip/av-split. Lean:
`scratch/av-split/` (six component files and their concatenation `AvSplitAll.lean`, each compiled with
`lake env lean`). Results log: `scratch/av-split/log.md`.
No file under `ZInQKernel/` or `blueprint/` and no other task's file was edited. Model work, no human review.

Marks: **VERIFIED** = compiled here, or read in a named file. **STANDARD** = published, reference given.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (no network on
this host, no copy of the books).

## 1. Main result

**Five of the seven rows are now theorems from five published-form leaves, with no glue left** (H-24, H-25, H-38,
H-54, H-69); **two rows cannot be split** over Mathlib's definitions today (H-53 needs the dual abelian variety,
H-78 needs `H¹(X, 𝒪_X)` or `Ω¹_X` on schemes), and both are reported with the decomposition on paper and what is
missing. No row statement was changed; none was found false, vacuous or stronger than its sources.

```lean
-- scratch/av-split/AvSplitAll.lean (one file, 2555 lines, compiles in about 25 s)
theorem AvSplit.Final.all_rows (hE : AvSplit.T4.MulEtaleAbelianScheme)
    (hT : AvSplit.MumfordTorsionAlgClosed) (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hM : AvSplit.MilneIsogenyQuasiInverse) (HG : ZInQ.HomLattice.GAGAMorphism) :
    PkgI2.ReductionTorsionBijective.{0} ∧ PkgI2.TorsionStructure.{0} ∧
      ZInQ.LeafPush2.UniformizationExists ∧ WeilPairing.IsogenyQuasiInverse ∧
      ZInQ.HomUnify.HomLatticeCorr
```

Every theorem below compiles and depends only on `[propext, Classical.choice, Quot.sound]` (VERIFIED, `#print axioms`
at the end of each file; `scratch/av-split/AvSplitAll.out`).

| row | old form (r3) | new leaves (published form, source) | new glue | Lean name of the proof |
|---|---|---|---|---|
| H-24 `t4 : PkgI2.ReductionTorsionBijective` | GLUE, consequence of Serre–Tate 1968 §1 | `AvSplit.T4.MulEtaleAbelianScheme`: `[m]` on an abelian scheme over `Spec O` is étale if `m ∈ O×` (BLR, *Néron models*, §7.3 Lemma 2; Mumford, GIT §6; UNVERIFIED locators) | none: the other two published inputs, Stacks Morphisms 29.35.17 (unramified separated: maps agreeing at a point agree) and Stacks 04GG (sections of étale algebras over henselian rings), are **proved from Mathlib** here, as are the scheme form of Hensel and "`w` is henselian" | `AvSplit.T4.reductionTorsionBijective_of_mulEtale` (`T4.lean`) |
| H-25 `t5 : PkgI2.TorsionStructure` | GLUE, consequence of Mumford §4 App. 2 | `AvSplit.MumfordTorsionAlgClosed`: over an algebraically closed `k`, `A(k)[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` (Mumford, *Abelian varieties*, §4, Application 2 (iv); UNVERIFIED) | none | `AvSplit.torsionStructure_of_mumford` (`T5Isog.lean`) |
| H-38 `t35 : ZInQ.LeafPush2.UniformizationExists` | GLUE, consequence of Mumford §1 with GAGA | none new: bp-analytic's AN3 leaf `BPAnalytic.Uniformization.UniformizationLeafAll` (kernel; Mumford §1 for `A^an` in coordinate form) and the H-25 leaf (to get `g = dim A`) | none | `AvSplit.uniformizationExists_of_mumford ∘ AvSplit.AN3.mumfordUniformizationC_of` (`T35.lean`, `T35AN3.lean`; `AvSplit.Final.h38`) |
| H-54 `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | GLUE, consequence of Mumford §7-8 | `AvSplit.MilneIsogenyQuasiInverse`: `fg = [d]`, `gf = [d]` as morphisms, some `d ≥ 1` (Milne, *Abelian varieties* (1986), Rem. 8.4; Milne's notes Prop. 7.1; Mumford §7; UNVERIFIED) | none | `AvSplit.isogenyQuasiInverse_of_milne` (`T5Isog.lean`) |
| H-69 `homLatticeCorr : HomUnify.HomLatticeCorr` | GLUE, composite of BL 1.2.1 with GAGA | the AN3 kernel leaf (as for H-38) and task homlattice's `ZInQ.HomLattice.GAGAMorphism` (Serre, GAGA, for homomorphisms of complex abelian varieties, `A^an` presented by a strong uniformization; homlattice §3.2) | none: homlattice's reduction needed AN3 at *every* embedding `σ : K → ℂ` (`StrongUniformizationExists`); the base change to `ℂ` is proved here | `AvSplit.HomLatticeAN3.homLatticeCorr_of_leaf_gaga` (`HomLatticeAN3.lean`, containing homlattice's file verbatim) |
| H-53 `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | GLUE, consequence of Mumford §§6, 8, 20, 23 | not splittable over Mathlib definitions (§4.1) | stays GLUE | — |
| H-78 `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | GLUE, composite of Milne JV Prop. 2.1 with Serre duality | not splittable over Mathlib definitions (§4.2) | stays GLUE | — |

**Effect on the count of frontier r3** (strict: LEAF = published form). The five GLUE rows H-24, H-25, H-38, H-54,
H-69 are replaced by five LEAF: `MulEtaleAbelianScheme`, `MumfordTorsionAlgClosed`, `UniformizationLeafAll`,
`MilneIsogenyQuasiInverse`, `GAGAMorphism` (`UniformizationLeafAll` is a kernel leaf but not yet a field of the
H assembly, leaf-fold4 §6). If nothing else changes, 70 Props (17 LEAF, 53 GLUE) become **70 Props: 22 LEAF,
48 GLUE** (SPECULATIVE until an integration fold checks that none of the new leaves duplicates an existing row).
The leaf-status of `UniformizationLeafAll` and `GAGAMorphism` ("coordinate forms" of Mumford §1 and of GAGA) is
the judgement of bp-analytic §4 and homlattice §3, which I share (SPECULATIVE) but did not re-review against the
books.

**Prior work used.** homlattice (`docs/research/homlattice.md`, `scratch/homlattice/HomLattice.lean`, copied
verbatim into `HomLatticeAN3.lean`, VERIFIED by a line-by-line comparison), g9-abvarbc's `AbVarBC` (points and
dimension of base changes, `ptRing`), infra-stalks' `exists_localStructure_pullback`, alg-frob-red's
`pb_symm_mul` (copied), bp-analytic's `exists_complexLinear_lift` and AN3. t5-torsion
(`docs/research/t5-torsion.md`) derives T5 from T35 in characteristic 0 and from Mumford's degree facts in general;
its route and mine are independent (mine: one leaf over `K̄`, base change).

**Universes.** `PkgI2.ReductionTorsionBijective` and `PkgI2.TorsionStructure` are universe-polymorphic
(`K : Type u`); they are proved at `u = 0`, the universe of every consumer (`HSyn.TextbookLeaves.t5 :
PkgI2.TorsionStructure.{0}`, alg-frob-red's `PkgI2.ReductionTorsionBijective.{0}`; VERIFIED by grep). The other
rows are stated at `Type`.

**Where the rows live.** H-24, H-25, H-38, H-69, H-78 are imported from `ZInQKernel/` unchanged. H-54 is a verbatim
copy (with its three dependencies `P`, `homP`, `IsQuasiInverse`) of `scratch/g0-assemble2/parts/a35_g12det.lean`
L17, L100, L303-306, L400-404, over the kernel's `PkgI3`; the text of `IsogenyQuasiInverse` agrees with
`scratch/leaf-fold5/Leaves5.lean` L49753-49755 (VERIFIED by `diff`). In leaf-fold5's flat file the row is over the
copy `HDec.PkgI3` (verbatim text of `Objects.lean`); the proof transfers verbatim (it uses only `PkgI3`; g9-abvarbc's `comp_natCast_hom` is restated in the
file as `comp_natCast_hom'`).

## 2. The five rows that are done

### 2.1 H-25 (T5): `TorsionStructure` from Mumford over `K̄`

```lean
def MumfordTorsionAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    (g n : ℕ), topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : k) ≠ 0 →
      ∃ e : torsion A k n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A k n, ∀ h : x.1 * y.1 ∈ torsion A k n, e ⟨x.1 * y.1, h⟩ = e x + e y
theorem torsionStructure_of_mumford (h : MumfordTorsionAlgClosed) : PkgI2.TorsionStructure.{0}
```

The leaf is the row's own text with `K` algebraically closed and points over `k` itself, i.e. Mumford's statement
(points of a variety over `k = k̄` are its `k`-points; `dim` the Krull dimension). Proof (VERIFIED): apply the leaf to
`A_{K̄}` (`ObjBridge.isAbelianVariety_baseChange`), `dim A_{K̄} = dim A` (`AbVarBC.dim_baseChange_scheme`, kernel),
`A_{K̄}(K̄) ≃* A(K̄)` (`AbVarBC.bcPt`, kernel), restricted to `n`-torsion.

### 2.2 H-54: `IsogenyQuasiInverse` from the morphism form

```lean
def MilneIsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A,
      f.hom ≫ g.hom = (((d : ℤ) : End A)).hom ∧ g.hom ≫ f.hom = (((d : ℤ) : End B)).hom
theorem isogenyQuasiInverse_of_milne (h : MilneIsogenyQuasiInverse) : WeilPairing.IsogenyQuasiInverse
```

Printed (Milne, over any field; UNVERIFIED number): for an isogeny `f` of degree `n` there is an isogeny `g` with
`g ∘ f = n_A`, `f ∘ g = n_B`. The leaf weakens `n = deg f` to some `d ≥ 1` and drops "`g` is an isogeny"; its
hypothesis "finite and surjective" implies Milne's "surjective with finite kernel". The row is the same equalities on
`K̄`-points; proof: `x ≫ [d] = x^d` (`AbVarBC.comp_natCast_hom`, kernel).

### 2.3 H-38 (T35): `UniformizationExists` from AN3 and the H-25 leaf

```lean
def MumfordUniformizationC : Prop :=
  ∀ (A : AbVar ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization (RingHom.id ℂ) Λ Φ
theorem uniformizationExists_of_mumford (h : MumfordUniformizationC) : UniformizationExists   -- T35.lean
theorem mumford_of_uniformizationExists (h : UniformizationExists) : MumfordUniformizationC   -- T35.lean
theorem AN3.card_torsion_torus (Λ) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (n : ℕ) (hn : 0 < n) :
    Nat.card {q : Torus Λ // n • q = 0} = n ^ (2 * g)                                         -- T35AN3.lean
theorem AN3.mumfordUniformizationC_of (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hT : MumfordTorsionAlgClosed) : MumfordUniformizationC                                    -- T35AN3.lean
```

Two steps (VERIFIED):
1. **Base change along `σ`** (`T35.lean`), the only step between the case `K = ℂ` and the row (leaf-review-b
   §2.1's derivation): `A_ℂ = A ×_{K,σ} ℂ`, `dim A_ℂ = dim A` (`AbVar.dim_baseChange`), `Φ := bcPt ∘ Φ'` with
   `(bcPt p).left = p.left ≫ pullback.fst`, preimages of Zariski opens are preimages of their pullbacks, and
   `cEvalAt (bcPt p) U s = cEvalAt p (π⁻¹U) (π^* s)` (`Scheme.Hom.comp_appLE`). The case `K = ℂ`,
   `MumfordUniformizationC`, is equivalent to the row.
2. **The case `K = ℂ` from AN3** (`T35AN3.lean`). bp-analytic's leaf gives a strong uniformization
   `φ : ℂ^{g'}/Λ ≃+ A(ℂ)` for some `g'`, hence a weak one (`ZInQ.LeafPush2.isUniformization_of_bp`, kernel);
   UnifBridge noted that `g' = dim A` was missing. It follows from counting 2-torsion: `#(ℂ^{g'}/Λ)[2] = 2^{2g'}`
   (`card_torsion_torus`: `Λ` is free of rank `2g'` by Mathlib's `ZLattice.rank`, and `λ ↦ λ/n` induces
   `Λ/nΛ ≅ (ℂ^{g'}/Λ)[n]`) and `#A(ℂ)[2] = 2^{2 dim A}` (the H-25 leaf at `k = ℂ`).

So `MumfordUniformizationC`, a candidate leaf in the first version of this report, is not needed.

### 2.4 H-24 (T4): `ReductionTorsionBijective` from one leaf

```lean
def MulEtaleAbelianScheme : Prop :=
  ∀ (O : Type) [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] (m : ℕ),
    IsUnit (m : O) → Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left)
theorem reductionTorsionBijective_of_mulEtale (hE : MulEtaleAbelianScheme) :
    PkgI2.ReductionTorsionBijective.{0}
```

The leaf is the standard statement for abelian schemes (`[n]` is finite flat of degree `n^{2g}`, étale when `n` is
invertible on the base; BLR §7.3 Lemma 2, Mumford GIT §6, Katz–Mazur Thm 2.3.1 for `g = 1`; locators UNVERIFIED),
here over an affine base and with "abelian scheme" as in the kernel's `IsAbelianScheme` (proper, smooth,
geometrically connected fibres; Mumford GIT Def. 6.1). It is used twice: `[m]` étale, and `[m]` unramified.

Two further published inputs of the derivation were first stated as leaves and are now **theorems from Mathlib**
(VERIFIED, `T4.lean`):

```lean
def UnramifiedSectionsEq : Prop :=          -- Stacks, Morphisms, Lemma 29.35.17 (UNVERIFIED number)
  ∀ (X Y S : Scheme.{0}) (π : Y ⟶ S) [IsSeparated π] [LocallyOfFiniteType π]
    [FormallyUnramified π] (a b : X ⟶ Y), ConnectedSpace X → a ≫ π = b ≫ π →
    ∀ x : X, X.fromSpecResidueField x ≫ a = X.fromSpecResidueField x ≫ b → a = b
theorem unramifiedSectionsEq : UnramifiedSectionsEq
def StacksHenselEtaleSection : Prop :=      -- Stacks 04GG, (1) ⇒ (8) (UNVERIFIED item number)
  ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (S : Type) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (q : Ideal S) [q.IsPrime],
    q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R →
    Function.Surjective ((Ideal.Quotient.mk q).comp (algebraMap R S)) →
    ∃ τ : S →ₐ[R] R, q = (IsLocalRing.maximalIdeal R).comap τ
theorem stacksHenselEtaleSection : StacksHenselEtaleSection
```

`unramifiedSectionsEq`: the diagonal of an unramified separated `π` is an open (Mathlib
`isOpenImmersion_diagonal`) and closed immersion, so the preimage of its image under `(a, b)` is clopen, contains
`x`, hence is all of `X`, and `(a, b)` factors through the diagonal. `stacksHenselEtaleSection`: Mathlib's local
structure theorem `Algebra.IsEtaleAt.exists_isStandardEtale` (Stacks 00UE) gives `f ∉ 𝔮` with `S_f ≅ R[X]_g/(P)`
standard étale; with `χ : S → S/𝔮 ≅ R/𝔪` lift the image of `X` to `a ∈ R`; `P(a) ∈ 𝔪`, `P'(a)` a unit, Hensel gives a
root `α ≡ a` with `g(α)` a unit; `X ↦ α` defines `τ`, and `res ∘ τ = χ` (two `R`-algebra maps out of `S_f` agreeing on
`X`), so `τ⁻¹(𝔪) = 𝔮`.

Proof of the row (VERIFIED, `T4.lean`):
1. `G : A(K̄) ≃* 𝒜(K̄/O)` through `e` and `Over.mapPullbackAdj` (`G_injective`, `G_surjective`, multiplicative by
   alg-frob-red's `pb_symm_mul`, copied); `IsReductionOf x y ⟺ ∃ x' ∈ 𝒜(w), ι^* x' = G x ∧ ρ^* x' = y`
   (`isRed_iff`).
2. `ι^* : 𝒜(w) → 𝒜(K̄/O)` is bijective: Mathlib's valuative criteria (`IsSeparated.valuativeCriterion`,
   `UniversallyClosed.eq_valuativeCriterion`) for the proper `𝒜 → Spec O` and the valuation ring `w ⊆ K̄`.
3. `ρ^*` (restriction to `Spec κ(w)`) is injective on `m`-torsion (`rho_inj`): for `a^m = b^m = 1`,
   `a ≫ [m] = b ≫ [m]`, `[m]` is étale (leaf), hence unramified and (being over the separated `𝒜 → Spec O`)
   separated; `Spec w` is connected; `a`, `b` agree on `Spec κ(w) → Spec w`, which factors through
   `Spec κ(closed point)` by an epimorphism; `unramifiedSectionsEq`.
4. `ρ^*` is onto the `m`-torsion of `𝒜(κ(w))` (`rho_surj`): `w` is henselian (`henselian_of_isAlgClosed`, proved:
   monic polynomials split over `K̄` with roots integral over `w`, hence in `w`), `[m]` is étale (leaf), and the scheme
   form of Hensel's lemma `HenselEtaleLift` lifts `y : Spec κ(w) → 𝒜` over the unit section.
5. `HenselEtaleLift` from `stacksHenselEtaleSection` (`henselEtaleLift_of_stacks`): affine opens `U ∋ f(a₀(s))`,
   `V ∋ a₀(s)`, `V ⊆ f⁻¹U`; `b`, `a₀` as ring maps `Γ(U) → R`, `Γ(V) → κ` (g9-abvarbc's `ptRing`, kernel);
   `S = R ⊗_{Γ(U)} Γ(V)` is étale over `R` (Mathlib `Algebra.Etale.baseChange`); `𝔮 = ker(S → κ)`; Stacks 04GG gives
   `τ`; `res ∘ τ = (S → κ)` because both kill `𝔮` and `R → S/𝔮` is onto.
6. Assembly (`reductionTorsionBijective_of`): both `∃!` clauses from 1-4.

## 3. H-69: `HomLatticeCorr` from AN3 and GAGA

`HomLatticeCorr` = lifting half `HomLinearLift` (any `K`, `σ`) ∧ realization half over `ℂ`
(`ZInQ.HomUnify.corr_iff_lift_realize`, kernel). Task homlattice (11-13) proved
`homLatticeCorr_of_strong_gaga : StrongUniformizationExists → GAGAMorphism → HomLatticeCorr`, where
`StrongUniformizationExists` is bp-analytic's AN3 at every field `K` and embedding `σ`; the fold did not adopt it
because it raised the count (leaf-fold4 §6, leaf-fold5). The only use of AN3 at `σ ≠ id` is the lifting half. Here
it is replaced by base change (VERIFIED, `HomLatticeAN3.lean`):

```lean
theorem isAnalyticHom_ptE_symm {n : ℕ} {ψ : (Fin n → ℂ) → CPts A σ} (hψ : IsAnalyticHom σ ψ) :
    IsAnalyticHom (RingHom.id ℂ) (fun z => (ptE A σ).symm (ψ z))
theorem analyticHomLift_of_C (HC : ZInQ.HomLattice.AnalyticHomLiftC) : ZInQ.HomLattice.AnalyticHomLift
theorem homLatticeCorr_of_leaf_gaga (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HG : ZInQ.HomLattice.GAGAMorphism) : ZInQ.HomUnify.HomLatticeCorr
```

* `isAnalyticHom_ptE_symm`: an analytic homomorphism `ψ : ℂ^n → A(ℂ)_σ` (homlattice's `IsAnalyticHom`: homomorphism,
  open preimages of Zariski opens, holomorphic regular functions) is one into `A_ℂ(ℂ)` through
  `A_ℂ(ℂ) ≃* A(ℂ)_σ`: a section of `𝒪` on an open of `A_ℂ = A ×_K ℂ` is, near each point, `N/H` with `N`, `H` sums of
  products of sections of `A` and constants (infra-stalks' `exists_localStructure_pullback`, kernel), so it is
  holomorphic along `ψ` where `H ≠ 0`. This is the argument of infra-stalks' `uniformizationLiftAnalytic` for group
  models, adapted.
* `analyticHomLift_of_C`: homlattice's lifting statement at `(K, σ)` from its case over `ℂ`
  (`AnalyticHomLiftC`, which homlattice derives from AN3 at `ℂ`: `analyticHomLiftC_of_leaf`), applied to `B_ℂ`;
  no dimension hypothesis is used.
* The realization half is homlattice's: `GAGAMorphism` with AN3 at `ℂ` (`strong_id_of_leaf`,
  `analyticMapAlgebraic_of_gaga'`, `analyticHomAlgebraic_of_map`, rigidity copied from mul-rigidity).

The leaves: `UniformizationLeafAll` (bp-analytic §10: `A(ℂ) ≅ ℂ^g/Λ` as complex Lie groups in coordinate form;
Mumford §1, §4; Serre GAGA §2; SGA 1 XII) and `GAGAMorphism` (homlattice §3.2: a holomorphic homomorphism
`A^an → B^an`, with `A^an` presented by a strong uniformization, is algebraic; Serre 1956, SGA 1 XII 4.4). Locators
UNVERIFIED, as in those reports.

**Superseded first attempt** (kept, compiled, `HomLattice.lean`): before finding homlattice's file I reduced the row
to two glue Props, `UnifHoloLift` (weak uniformizations have discrete kernels and algebraic homomorphisms induce
holomorphic torus maps) and the kernel's `HomRealize`, with Birkenhake–Lange Prop. 1.2.1 taken from the kernel
theorem `BPAnalytic.exists_complexLinear_lift` (bp-analytic, covering theory): `AvSplit.HomLattice.homLatticeCorr_of`.
It is not needed for the result above.

## 4. The two rows that cannot be split today

### 4.1 H-53 `T09_SymmIsogenyExists`

The row is existential in the structure `WeilDual A` (an abelian variety `D.dual` with perfect, Galois-equivariant,
compatible pairings `A[n] × D.dual[n] → μ_n` and duals of endomorphisms), so it is no stronger than the literature
(leaf-review-b §2.1, confirmed by reading `a35_g12det.lean` L120-300). Its proof needs a witness `D`; the only known
witness is `Â = Pic⁰_{A/K}` with Mumford's `ē_n`. The published inputs (Mumford, *Abelian varieties*, §6 App. 1:
`A` projective, an ample `L` over `K`, `φ_L` an isogeny; §8 Thm 1: `Â` exists; §20: `ē_n` perfect, functorial,
compatible; §23: `e^L_n(x, x) = 1`; over a non-closed `K`: Milne 1986 §§8-16, Galois equivariance from
`K`-rationality; all UNVERIFIED numbers) are statements about line bundles, the Picard functor and `Pic⁰`.
**Mathlib v4.35 has no line bundles or Picard functor on schemes** (it has sheaves of modules,
`Mathlib/AlgebraicGeometry/Modules`, but no `Pic`; VERIFIED by grep), so none of them can be stated over genuine
definitions, and no shortcut avoids `Â`: `D.dual = A` would need a perfect Galois-equivariant pairing on every
`A[n]` compatible with all endomorphisms, i.e. a principal polarization, which an abelian variety over `K` need not
have. What it needs: definitions of invertible sheaves and `Pic⁰` of an abelian scheme over a field, the
representability theorem (Mumford §8 / Milne 1986 Thm 10.1) as a leaf, then the Weil pairing via the Poincaré
bundle (Mumford §20) as leaves; the row would then be glue over them. Stays GLUE.

### 4.2 H-78 `DimJacobianEqGenus`

`dim J = fieldGenus F` for `(J, aj)` an Albanese variety (`IsJacobian`) of a pointed smooth proper geometrically
connected curve `X/ℚ` and `F ≅ ℚ(X)`, with `fieldGenus F = dim_ℚ` of the differentials of `F/ℚ` regular at every
place. The statement is correct (SPECULATIVE check: for `trdeg F = 1` every valuation ring `⊋ ℚ` of `F` is a place,
so `holoDiff F = H⁰(X, Ω¹)`). The decomposition on paper (curves-g §3, UNVERIFIED numbers): (1) Milne, *Jacobian
varieties*, Thm 1.1 / Prop. 6.1 (the Albanese variety is `Pic⁰`) and Prop. 2.1 (`T₀J ≅ H¹(X, 𝒪_X)`, so
`dim J = dim H¹(X, 𝒪_X)`); (2) Serre duality on curves (Hartshorne III.7.12): `dim H¹(X, 𝒪_X) = dim H⁰(X, Ω¹)`;
(3) `H⁰(X, Ω¹)` = differentials of `ℚ(X)` regular at every closed point = at every place (Hartshorne II.8, I.6).
**Mathlib v4.35 has no sheaf of differentials on schemes and no `K`-linear `H¹(X, 𝒪_X)`** (sheaf cohomology
exists only as abelian groups, `CategoryTheory.Sheaf.H` in `Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean`; VERIFIED by grep), and no `Pic⁰`, so
(1) and (2) cannot be stated over genuine definitions. A route through function fields only (Weil 1948; Chevalley,
*Algebraic functions of one variable*: the genus defined by Riemann–Roch equals the number of differentials of the
first kind) would need a Riemann–Roch genus of `F` (definable from valuations: `g = max (deg D − ℓ(D) + 1)`) and a
scheme-free form of "the Albanese variety has dimension `g`", which I could not locate in a printed source without
the books. Stays GLUE.

## 5. What remains

* H-53 and H-78 stay GLUE (§4); both need definitions that Mathlib v4.35 lacks (line bundles and `Pic⁰`;
  `Ω¹_X` or a `K`-linear `H¹(X, 𝒪_X)`).
* The locators of the five leaves are UNVERIFIED (no network): `MulEtaleAbelianScheme` (BLR §7.3 Lemma 2 or
  Mumford GIT §6), `MumfordTorsionAlgClosed` (Mumford §4 App. 2 (iv)), `MilneIsogenyQuasiInverse` (Milne 1986
  Rem. 8.4 / notes Prop. 7.1, Mumford §7); `UniformizationLeafAll` and `GAGAMorphism` carry the locators of
  bp-analytic and homlattice.
* Integration: `AvSplitAll.lean` imports only `ZInQKernel` modules and Mathlib; its rows are the kernel's own
  constants except H-54 (a verbatim copy of the scratch chain's `WeilPairing.IsogenyQuasiInverse`), and its
  `ZInQ.HomLattice` namespace is homlattice's file verbatim. Two rows are proved at universe `0` only.

## 6. Checks

All in `scratch/av-split/`, one Lean process at a time, `lake env lean <file>` after `lake build` of the imported
kernel modules (build artifacts reused from the leaf-fold6 worktree, same `ZInQKernel/` sources). Each file ends with
`#print axioms` of its theorems; every one prints `[propext, Classical.choice, Quot.sound]` (VERIFIED):

| file | theorems |
|---|---|
| `T5Isog.lean` | `AvSplit.torsionStructure_of_mumford`, `AvSplit.isogenyQuasiInverse_of_milne` |
| `T35.lean` | `AvSplit.uniformizationExists_of_mumford`, `AvSplit.mumford_of_uniformizationExists` |
| `T4.lean` | `AvSplit.T4.henselian_of_isAlgClosed`, `AvSplit.T4.reductionTorsionBijective_of`, `AvSplit.T4.henselEtaleLift_of_stacks`, `AvSplit.T4.reductionTorsionBijective_of_leaves`, `AvSplit.T4.unramifiedSectionsEq`, `AvSplit.T4.stacksHenselEtaleSection`, `AvSplit.T4.reductionTorsionBijective_of_mulEtale` |
| `T35AN3.lean` | `AvSplit.AN3.card_torsion_torus`, `AvSplit.AN3.eq_dim_of_uniformization`, `AvSplit.AN3.mumfordUniformizationC_of` |
| `HomLatticeAN3.lean` | `AvSplit.HomLatticeAN3.isAnalyticHom_ptE_symm`, `AvSplit.HomLatticeAN3.analyticHomLift_of_C`, `AvSplit.HomLatticeAN3.homLatticeCorr_of_leaf_gaga` (homlattice's part: its own 45 reports, not re-printed) |
| `HomLattice.lean` (superseded) | `AvSplit.HomLattice.homLinearLift_of`, `AvSplit.HomLattice.homLatticeCorr_of` |
| `AvSplitAll.lean` (concatenation, `python3 build_all.py`; 0 errors, 24 s) | `AvSplit.Final.h24`, `h25`, `h38`, `h54`, `h69`, `all_rows` |
