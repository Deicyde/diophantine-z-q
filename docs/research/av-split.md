# av-split: the abelian-variety GLUE rows of frontier r3 split into published forms

Task av-split, 2026-11-14. Base: fork main cba8157f (w54 + frontier r3), branch wip/av-split. Lean:
`scratch/av-split/` (four files, each compiled with `lake env lean`). Results log: `scratch/av-split/log.md`.
No file under `ZInQKernel/` or `blueprint/` and no other task's file was edited. Model work, no human review.

Marks: **VERIFIED** = compiled here, or read in a named file. **STANDARD** = published, reference given.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (no network on
this host, no copy of the books).

## 1. Main result

**Four of the seven rows are now theorems from published-form leaves only** (H-24, H-25, H-38, H-54), with no
glue left; **one row is reduced** (H-69: its published input, Birkenhake–Lange Prop. 1.2.1, is already a kernel
theorem; two analytic glue Props remain); **two rows cannot be split** over Mathlib's definitions today (H-53 needs
the dual abelian variety, H-78 needs `H¹(X, 𝒪_X)` or `Ω¹_X` on schemes), and both are reported with the
decomposition on paper and what is missing. No row statement was changed; none was found false, vacuous or
stronger than its sources.

Every theorem below compiles and depends only on `[propext, Classical.choice, Quot.sound]` (VERIFIED, `#print axioms`
at the end of each file; outputs in the log).

| row | old form (r3) | new leaves (published form, source) | new glue | Lean name of the proof |
|---|---|---|---|---|
| H-24 `t4 : PkgI2.ReductionTorsionBijective` | GLUE, consequence of Serre–Tate 1968 §1 | (a) `AvSplit.T4.MulEtaleAbelianScheme`: `[m]` on an abelian scheme over `Spec O` is étale if `m ∈ O×` (BLR, *Néron models*, §7.3 Lemma 2; Mumford, GIT §6; UNVERIFIED locators); (b) `AvSplit.T4.UnramifiedSectionsEq`: two `S`-morphisms from a connected scheme to an unramified separated `S`-scheme agreeing at a point (with residue fields) are equal (Stacks, Morphisms, Lemma 29.35.17; EGA IV 17.4.9; UNVERIFIED); (c) `AvSplit.T4.StacksHenselEtaleSection`: étale algebras over a henselian local ring have sections through rational primes (Stacks 04GG, (1)⇒(8); item number UNVERIFIED) | none: `HenselEtaleLift` (scheme form of Hensel) and `henselian_of_isAlgClosed` are proved | `AvSplit.T4.reductionTorsionBijective_of_leaves` (`scratch/av-split/T4.lean`) |
| H-25 `t5 : PkgI2.TorsionStructure` | GLUE, consequence of Mumford §4 App. 2 | `AvSplit.MumfordTorsionAlgClosed`: over an algebraically closed `k`, `A(k)[n] ≅ (ℤ/n)^{2g}` for `char k ∤ n` (Mumford, *Abelian varieties*, §4, Application 2 (iv); UNVERIFIED) | none | `AvSplit.torsionStructure_of_mumford` (`T5Isog.lean`) |
| H-38 `t35 : ZInQ.LeafPush2.UniformizationExists` | GLUE, consequence of Mumford §1 with GAGA | `AvSplit.MumfordUniformizationC`: the row at `K = ℂ`, `σ = id` (Mumford §1 for Serre's `X^an`, GAGA §2; UNVERIFIED) | none | `AvSplit.uniformizationExists_of_mumford` (`T35.lean`) |
| H-54 `isogenyQuasiInverse : WeilPairing.IsogenyQuasiInverse` | GLUE, consequence of Mumford §7-8 | `AvSplit.MilneIsogenyQuasiInverse`: `fg = [d]`, `gf = [d]` as morphisms, some `d ≥ 1` (Milne, *Abelian varieties* (1986), Rem. 8.4; Milne's notes Prop. 7.1; Mumford §7; UNVERIFIED) | none | `AvSplit.isogenyQuasiInverse_of_milne` (`T5Isog.lean`) |
| H-69 `homLatticeCorr : HomUnify.HomLatticeCorr` | GLUE, composite of BL 1.2.1 with GAGA | none needed: BL Prop. 1.2.1 is the kernel theorem `BPAnalytic.exists_complexLinear_lift` (`ZInQKernel/HDecomp/Analytic/Hom.lean`) | `AvSplit.HomLattice.UnifHoloLift` (weak uniformizations: discrete kernels, algebraic homomorphisms holomorphic on the tori); `ZInQ.HomUnify.HomRealize` (kernel def; realization half, GAGA content) | `AvSplit.HomLattice.homLatticeCorr_of` (`HomLattice.lean`) |
| H-53 `t09SymmIsogenyExists : WeilPairing.T09_SymmIsogenyExists` | GLUE, consequence of Mumford §§6, 8, 20, 23 | not splittable over Mathlib definitions (§4.1) | stays GLUE | — |
| H-78 `ZInQ.Contrib.CurvesG.DimJacobianEqGenus` | GLUE, composite of Milne JV Prop. 2.1 with Serre duality | not splittable over Mathlib definitions (§4.2) | stays GLUE | — |

**Effect on the count of frontier r3** (strict: LEAF = published form). H-24, H-25, H-38, H-54 (4 GLUE) are replaced by
6 LEAF (3 + 1 + 1 + 1); H-69 (1 GLUE) by 2 GLUE; H-53, H-78 unchanged. If nothing else changes, 70 Props (17 LEAF,
53 GLUE) become **73 Props: 23 LEAF, 50 GLUE** (SPECULATIVE until an integration fold checks that none of the six new
leaves duplicates an existing row).

**Universes.** `PkgI2.ReductionTorsionBijective` and `PkgI2.TorsionStructure` are universe-polymorphic
(`K : Type u`); they are proved at `u = 0`, the universe of every consumer (`HSyn.TextbookLeaves.t5 :
PkgI2.TorsionStructure.{0}`, alg-frob-red's `PkgI2.ReductionTorsionBijective.{0}`; VERIFIED by grep). The other
rows are stated at `Type`.

**Where the rows live.** H-24, H-25, H-38, H-69, H-78 are imported from `ZInQKernel/` unchanged. H-54 is a verbatim
copy (with its three dependencies `P`, `homP`, `IsQuasiInverse`) of `scratch/g0-assemble2/parts/a35_g12det.lean`
L17, L100, L303-306, L400-404, over the kernel's `PkgI3`; the text of `IsogenyQuasiInverse` agrees with
`scratch/leaf-fold5/Leaves5.lean` L49753-49755 (VERIFIED by `diff`). In leaf-fold5's flat file the row is over the
copy `HDec.PkgI3` (verbatim text of `Objects.lean`); the proof transfers verbatim once `comp_natCast_hom`
(`AbVarBC/Torsion.lean`, 8 lines) is available over the same `AbVar`.

## 2. The four rows that are done

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

### 2.3 H-38 (T35): `UniformizationExists` from the case `K = ℂ`

```lean
def MumfordUniformizationC : Prop :=
  ∀ (A : AbVar ℂ) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ IsUniformization (RingHom.id ℂ) Λ Φ
theorem uniformizationExists_of_mumford (h : MumfordUniformizationC) : UniformizationExists
theorem mumford_of_uniformizationExists (h : UniformizationExists) : MumfordUniformizationC
```

The leaf is Mumford §1 (a complex abelian variety of dimension `g` has `X^an ≅ ℂ^g/Λ`, `Λ` a lattice, through the
exponential) for Serre's analytification, whose defining properties give the two analytic clauses of
`IsUniformization` (Zariski opens are open, regular functions are holomorphic). The base change along an arbitrary
`σ : K → ℂ`, the only step between the leaf and the row (leaf-review-b §2.1's derivation), is now proved
(VERIFIED): `A_ℂ = A ×_{K,σ} ℂ`, `dim A_ℂ = dim A` (`AbVar.dim_baseChange`), `Φ := bcPt ∘ Φ'` with
`(bcPt p).left = p.left ≫ pullback.fst`, preimages of Zariski opens are preimages of their pullbacks, and
`cEvalAt (bcPt p) U s = cEvalAt p (π⁻¹U) (π^* s)` (`Scheme.Hom.comp_appLE`). The converse is immediate, so the leaf and
the row are equivalent.

### 2.4 H-24 (T4): `ReductionTorsionBijective` from three leaves

```lean
def MulEtaleAbelianScheme : Prop :=
  ∀ (O : Type) [CommRing O] (𝒜 : Grp (Over (Spec (.of O)))) [IsAbelianScheme 𝒜] (m : ℕ),
    IsUnit (m : O) → Etale ((𝟙 𝒜.X ^ m : 𝒜.X ⟶ 𝒜.X).left)
def UnramifiedSectionsEq : Prop :=
  ∀ (X Y S : Scheme.{0}) (π : Y ⟶ S) [IsSeparated π] [LocallyOfFiniteType π]
    [FormallyUnramified π] (a b : X ⟶ Y), ConnectedSpace X → a ≫ π = b ≫ π →
    ∀ x : X, X.fromSpecResidueField x ≫ a = X.fromSpecResidueField x ≫ b → a = b
def StacksHenselEtaleSection : Prop :=
  ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (S : Type) [CommRing S] [Algebra R S]
    [Algebra.Etale R S] (q : Ideal S) [q.IsPrime],
    q.comap (algebraMap R S) = IsLocalRing.maximalIdeal R →
    Function.Surjective ((Ideal.Quotient.mk q).comp (algebraMap R S)) →
    ∃ τ : S →ₐ[R] R, q = (IsLocalRing.maximalIdeal R).comap τ
theorem reductionTorsionBijective_of_leaves (hE : MulEtaleAbelianScheme)
    (hU : UnramifiedSectionsEq) (hS : StacksHenselEtaleSection) : PkgI2.ReductionTorsionBijective.{0}
```

Fidelity of the leaves (SPECULATIVE judgements, sources UNVERIFIED): (a) is the standard statement for abelian
schemes (`[n]` is finite flat of degree `n^{2g}`, étale when `n` is invertible on the base), here over an affine
base and with "abelian scheme" as in the kernel's `IsAbelianScheme` (proper, smooth, geometrically connected
fibres; Mumford GIT Def. 6.1). (b) encodes the printed hypothesis "`a(x) = b(x)` and the two maps
`κ(a(x)) → κ(x)` agree" as equality of the composites with `Spec κ(x) → X` (Mathlib's
`Scheme.fromSpecResidueField`; the two are equivalent by `Scheme.SpecToEquivOfField`); unramified = formally
unramified and locally of finite type (Stacks' definition). (c) states "`κ = κ(𝔮)`" as "`R → S/𝔮` is onto", which
implies it (`R/𝔪 ⊆ S/𝔮 ⊆ κ(𝔮)`); Mathlib's `HenselianLocalRing` is Stacks' Def. 10.153.1.

Proof (VERIFIED, `T4.lean`):
1. `G : A(K̄) ≃* 𝒜(K̄/O)` through `e` and `Over.mapPullbackAdj` (`G_injective`, `G_surjective`, multiplicative by
   alg-frob-red's `pb_symm_mul`, copied); `IsReductionOf x y ⟺ ∃ x' ∈ 𝒜(w), ι^* x' = G x ∧ ρ^* x' = y`
   (`isRed_iff`).
2. `ι^* : 𝒜(w) → 𝒜(K̄/O)` is bijective: Mathlib's valuative criteria (`IsSeparated.valuativeCriterion`,
   `UniversallyClosed.eq_valuativeCriterion`) for the proper `𝒜 → Spec O` and the valuation ring `w ⊆ K̄`.
3. `ρ^*` (restriction to `Spec κ(w)`) is injective on `m`-torsion (`rho_inj`): for `a^m = b^m = 1`,
   `a ≫ [m] = b ≫ [m]`, `[m]` is étale (a), hence unramified and (being over the separated `𝒜 → Spec O`)
   separated; `Spec w` is connected; `a`, `b` agree on `Spec κ(w) → Spec w`, which factors through
   `Spec κ(closed point)` by an epimorphism; leaf (b).
4. `ρ^*` is onto the `m`-torsion of `𝒜(κ(w))` (`rho_surj`): `w` is henselian (`henselian_of_isAlgClosed`, proved:
   monic polynomials split over `K̄` with roots integral over `w`, hence in `w`), `[m]` is étale (a), and the scheme
   form of Hensel's lemma `HenselEtaleLift` lifts `y : Spec κ(w) → 𝒜` over the unit section.
5. `HenselEtaleLift` from (c) (`henselEtaleLift_of_stacks`): affine opens `U ∋ f(a₀(s))`, `V ∋ a₀(s)`, `V ⊆ f⁻¹U`;
   `b`, `a₀` as ring maps `Γ(U) → R`, `Γ(V) → κ` (g9-abvarbc's `ptRing`, kernel); `S = R ⊗_{Γ(U)} Γ(V)` is étale over
   `R` (Mathlib `Algebra.Etale.baseChange`); `𝔮 = ker(S → κ)`; (c) gives `τ`; `res ∘ τ = (S → κ)` because both kill
   `𝔮` and `R → S/𝔮` is onto.
6. Assembly (`reductionTorsionBijective_of`): both `∃!` clauses from 1-4.

## 3. H-69: what remains of `HomLatticeCorr`

`HomLatticeCorr` = lifting half `HomLinearLift` (any `K`, `σ`) ∧ realization half over `ℂ`
(`ZInQ.HomUnify.corr_iff_lift_realize`, kernel). **Finding (VERIFIED):** the published theorem of the lifting half,
Birkenhake–Lange Prop. 1.2.1, is already proved in the kernel, `BPAnalytic.exists_complexLinear_lift`
(holomorphic homomorphisms `ℂ^g/Λ → ℂ^h/Λ'` of bp-analytic's complex tori, `Λ`, `Λ'` discrete, are induced by
`ℂ`-linear maps preserving the lattices; covering theory). So the row needs no leaf for it. What the row still needs
is analytic and not printed in this form:

```lean
def UnifHoloLift : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∃ _ : DiscreteTopology ΛA, ∃ _ : DiscreteTopology ΛB,
      ∀ (f : AbVar.Hom A B) (F : Torus ΛA →+ Torus ΛB), Induces ΦA ΦB f F →
        MDifferentiable 𝓘(ℂ, Fin g → ℂ) 𝓘(ℂ, Fin h → ℂ) F
theorem homLinearLift_of (H : UnifHoloLift) : ZInQ.HomUnify.HomLinearLift
theorem homLatticeCorr_of (H1 : UnifHoloLift) (H2 : ZInQ.HomUnify.HomRealize) : ZInQ.HomUnify.HomLatticeCorr
```

* **GLUE `UnifHoloLift`.** leaf-push2's `IsUniformization` is weak: a surjective homomorphism with kernel `Λ`,
  open preimages of Zariski opens, regular functions holomorphic along `Φ`; it does not say that `Λ` is a lattice or
  that `Φ` is a covering. Both follow (SPECULATIVE sketch): smoothness gives, at each point, `g` regular functions
  with an étale map to `𝔸^g`, hence (holomorphic inverse function theorem, in Mathlib) local holomorphic
  coordinates along `Φ`, so `Λ` is discrete; properness makes `A(ℂ)` compact Hausdorff for the topology of regular
  functions (Serre, GAGA, §2, Prop. 6 / SGA 1 XII 3.2; UNVERIFIED), so `ℂ^g/Λ → A(ℂ)^an` is a homeomorphism; then an
  algebraic `f` is holomorphic in the coordinates. Equivalently: every weak uniformization is bp-analytic's strong
  `BPAnalytic.Uniformization.IsUniformization` (with local coordinates and continuous inverse) composed with a
  `ℂ`-linear isomorphism. Not attempted in Lean (no analytic structure on `A(ℂ)` in Mathlib).
* **GLUE `HomRealize`** (the kernel's existence form of the realization half; uniqueness is the kernel's
  `induces_unique`): over `ℂ`, every `ℂ`-linear `M` with `MΛ_A ⊆ Λ_B` comes from a homomorphism. This is GAGA (Serre
  1956: holomorphic maps between analytifications of projective varieties are algebraic) or Chow's theorem applied
  to the graph. **GAGA's printed statement cannot be stated over Mathlib's definitions** (no analytification of a
  scheme, no complex-analytic spaces); its specialization to abelian varieties with `A^an` presented by a strong
  uniformization would be the closest published-form leaf.
* `homLinearLift_of` (VERIFIED): `Φ̄_B : ℂ^h/Λ_B ≃+ B(ℂ)_σ` from `IsUniformization`; the torus map
  `F = Φ̄_B⁻¹ ∘ f ∘ Φ_A` descends to `ℂ^g/Λ_A`, is induced by `f`, holomorphic by the glue, hence `ℂ`-linear by
  `exists_complexLinear_lift`.

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

## 5. Checks

All in `scratch/av-split/`, one Lean process at a time, `lake env lean <file>` after `lake build` of the imported
kernel modules (build artifacts reused from the leaf-fold6 worktree, same `ZInQKernel/` sources). Each file ends with
`#print axioms` of its theorems; every one prints `[propext, Classical.choice, Quot.sound]` (VERIFIED):

| file | theorems |
|---|---|
| `T5Isog.lean` | `AvSplit.torsionStructure_of_mumford`, `AvSplit.isogenyQuasiInverse_of_milne` |
| `T35.lean` | `AvSplit.uniformizationExists_of_mumford`, `AvSplit.mumford_of_uniformizationExists` |
| `T4.lean` | `AvSplit.T4.henselian_of_isAlgClosed`, `AvSplit.T4.reductionTorsionBijective_of`, `AvSplit.T4.henselEtaleLift_of_stacks`, `AvSplit.T4.reductionTorsionBijective_of_leaves` |
| `HomLattice.lean` | `AvSplit.HomLattice.homLinearLift_of`, `AvSplit.HomLattice.homLatticeCorr_of` |
