# gr56-prove: González–Rotger Prop. 5.6 on `X₆` from Eichler's count and the lattice model

Task gr56-prove (2026-11-15). Base: fork main 43513d87 (leaf-fold25). Target: the research field
`gonzalezRotgerProp56X6 : GRCountX6.GonzalezRotgerProp56X6` of `HDec.HSyn.OpenResearchLeaves22` (TailZ35 L69).
Contributor file: `ZInQKernel/Contrib/OneProof/GR56Lattice.lean` (85 KB, namespace `GR56`, plus a rerouted copy of
the chain's consumer in `HDec.FS5NoCM`; it imports `ZInQKernel.Contrib.OneProof.QMLattice`, `…GRCountX6`,
`…RayClassShimura` and `ZInQKernel.Contrib.HeightBC.G0StableBC`, never `Main`; no `sorry`). Scratch:
`scratch/gr56-prove/`. Results log: `scratch/gr56-prove/log.md`.
Marks: VERIFIED (compiled, or read in the tree), STANDARD (published, exact reference), SPECULATIVE,
UNVERIFIED (theorem numbers from memory; no network on this host).

## 1. Result

**The field is discharged with one new leaf: Eichler's optimal-embedding count, a pure-algebra statement. The
other hypotheses are fields already in the bundles.** It is not proved outright: Eichler's count for every order of
conductor prime to 6 needs the local theory of quaternion orders, which Mathlib does not have. With
`autofold.py --dry-run` (VERIFIED), the fold keeps the strict count at 46/10 on 56 and the strictest count at 45/11.
The research LEAF González–Rotger Prop. 5.6, a count of points on a moduli witness, is replaced by the textbook LEAF
`GRCountX6.EichlerOptEmbCount6`. That leaf is stated over Mathlib's `QuaternionAlgebra ℚ 2 0 (-3)`, the kernel's
maximal order `LeafQM.O`, `CommRing.Pic` and prime ideals of `𝓞 k`.

The new mathematics is the **CM-point correspondence** `CM(R) ≃ Emb(R, 𝒪)/𝒪^×`, which is gt-grcount's
`CMPointsOptEmb6`. Here `CM(R)` is the set of classes of QM pairs over `ℚ̄` with `End_𝒪 ≅ R`. The correspondence is
proved in Lean from bundle fields only:

* **injective** from the three textbook fields alone;
* **surjective** from two existence statements, each proved from an existing field.

Every theorem below compiles. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each one
(`scratch/gr56-prove/Axioms.lean`, output `axioms.txt`, VERIFIED).

### 1.1 Main theorems (verbatim `#check` output)

```
GR56.gonzalezRotgerProp56X6_of_main : GRCountX6.EichlerOptEmbCount6 →
  RayClassCFT.ShimuraMainThmIDeligneY3AbU →
    HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar →
      BPAnalytic.Uniformization.UniformizationLeafAll →
        ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → GRCountX6.GonzalezRotgerProp56X6

GR56.cmPointsOptEmb6_of_main : RayClassCFT.ShimuraMainThmIDeligneY3AbU →
  HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar →
    BPAnalytic.Uniformization.UniformizationLeafAll →
      ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → GRCountX6.CMPointsOptEmb6

GR56.cmMap_injective : ∀ (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
  (hM : AvSplit.MumfordTorsionAlgClosed) {k : Type} [inst : Field k] [inst_1 : NumberField k]
  (hk : Module.finrank ℚ k = 2) {R : Subring k} (hR : R ≤ (integralClosure ℤ k).toSubring)
  (hc : (LeafQM.AV.conductor R).Coprime 6), Function.Injective (GR56.cmMap hU hG hM hk hR hc)

GR56.cmMap_surjective : ∀ (hU …) (hG …) (hM …) {k : Type} [Field k] [NumberField k] (hk …) {R} (hR …) (hc …)
  [NumberField.IsTotallyComplex k],
  GR56.QMTorusAbelian → GR56.CMPairDescendsQbar → Function.Surjective (GR56.cmMap hU hG hM hk hR hc)

GR56.qmTorusAbelian_of_main : RayClassCFT.ShimuraMainThmIDeligneY3AbU → GR56.QMTorusAbelian
GR56.cmPairDescendsQbar_of_st : HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar →
  GR56.CMPairDescendsQbar
```

Other forms of the field theorem, used by the alternative fold specs:

* `GR56.gonzalezRotgerProp56X6_of_st : EichlerOptEmbCount6 → QMTorusAbelian → ShimuraTaniyamaQbar → hU → hG → hM
  → GonzalezRotgerProp56X6`;
* `GR56.gonzalezRotgerProp56X6_of_leaves : EichlerOptEmbCount6 → QMTorusAbelian → CMPairDescendsQbar → hU → hG →
  hM → GonzalezRotgerProp56X6`.

The upper bound only, from Eichler's count and the textbook fields (§4.2):

```
GR56.r5fpCountLe_of_eichler : GRCountX6.EichlerOptEmbCount6 →
  BPAnalytic.Uniformization.UniformizationLeafAll →
    ZInQ.HomLattice.GAGAMorphism → AvSplit.MumfordTorsionAlgClosed → GR56.R5fpCountLe
GR56.r5fpCountLe_of_r5fpCount : LeafQM.AV.R5fpCount → GR56.R5fpCountLe
HDec.FS5NoCM.fibreComTrivialFull_of_leaves''_le : HDec.FS5NoCM.R1R2fpFull → LeafQM.AV.Pin.MobiusGlue →
  HDec.QMLattice.YuB6Alg → PkgI3.HomFreeFinite → HDec.FS5NoCM.CMOptimalEmbedding →
    HDec.FS5NoCM.X6KummerFibre → GR56.R5fpCountLe → HDec.FS5NoCM.FibreComTrivialFull
```

### 1.2 The hypotheses

| hypothesis | where | kind |
|---|---|---|
| `GRCountX6.EichlerOptEmbCount6` | def in `ZInQKernel/Contrib/OneProof/GRCountX6.lean` (gt-grcount); not yet a bundle field | **new LEAF** (§3) |
| `RayClassCFT.ShimuraMainThmIDeligneY3AbU` | field `shimuraMainThmIDeligneY3AbU` of `OpenResearchLeaves22` (TailZ35 L79) | existing (composite, GLUE) |
| `QMSplitSTQM.ShimuraTaniyamaQbar` | field `shimuraTaniyamaQbar` of `OpenAddedLeaves17` (TailZ34 L122) | existing LEAF |
| `UniformizationLeafAll`, `GAGAMorphism`, `MumfordTorsionAlgClosed` | fields of `OpenTextbookLeaves11` (TailZ32 L22, L23, L15) | existing LEAFs |

### 1.3 New definitions (verbatim)

```lean
/-- LEAF candidate (QM complex tori are abelian surfaces; Shimura 1963, …); proved from the research field
`shimuraMainThmIDeligneY3AbU` by `qmTorusAbelian_of_main`. -/
def QMTorusAbelian : Prop :=
  ∀ (τ : ℂ) (hτ : 0 < τ.im), ∃ (A : PkgI3.AbVar ℂ) (_ : A.dim = 2) (q : QMStr A)
    (Φ : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A (RingHom.id ℂ)),
    ZInQ.LeafPush2.IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice hτ.ne') Φ ∧
    ∀ (a : LeafQM.O) (z : Fin 2 → ℂ),
      Φ ((HDec.HSyn.G0Split.FibreQM.qmMat a).mulVec z) = Φ z ≫ (q.iota a).hom

/-- (CM points are algebraic; Shimura–Taniyama, Shimura 1967); proved from the added-bundle LEAF
`shimuraTaniyamaQbar` by `cmPairDescendsQbar_of_st`. `bcQ` is base change along `σQ = IsAlgClosed.lift`. -/
def CMPairDescendsQbar : Prop :=
  ∀ (A : PkgI3.AbVar ℂ) (_ : A.dim = 2) (q : QMStr A),
    (∃ d : ℤ, d < 0 ∧ ∃ ψ ∈ com q, ψ * ψ = (d : PkgI3.AbVar.End A)) →
      ∃ P : QMPair Qbar, Nonempty (QMIso (bcQ P).q q)

/-- GLUE: the upper half of `LeafQM.AV.R5fpCount`, the only half the chain uses (proved). -/
def R5fpCountLe : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] [NumberField.IsTotallyComplex k],
    Module.finrank ℚ k = 2 →
    ∀ R : Subring k, R ≤ (integralClosure ℤ k).toSubring → Nat.Coprime (conductor R) 6 →
      Nat.card (CommRing.Pic R) ≠ 0 →
        Finite {c : Quotient (pairSetoid Qbar) //
            ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} ∧
        Nat.card {c : Quotient (pairSetoid Qbar) //
            ∃ P : QMPair Qbar, Quotient.mk _ P = c ∧ Nonempty (com P.q ≃+* R)} ≤
          2 ^ inertCount6 k * Nat.card (CommRing.Pic R)
```

`cmMap : CMSet R → Quot (GRCountX6.ConjRel R)` is the explicit map. Here `CMSet R` is the set counted by
`R5fpCountLe` (§2.3). `OptEmb`, `ConjRel` and `eichlerFactor6` are gt-grcount's definitions, unchanged.

## 2. `#discharges` and the fold

### 2.1 `#discharges` (`scratch/gr56-prove/Discharges.lean`, output `discharges.txt`, VERIFIED)

The build `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges
+ZInQKernel.Contrib.OneProof.GR56Lattice` succeeded. Then `lake env lean scratch/gr56-prove/Discharges.lean` gave:

```
DISCHARGES [OpenResearchLeaves22.gonzalezRotgerProp56X6] by GR56.gonzalezRotgerProp56X6_of_leaves
  still assumes: [GRCountX6.EichlerOptEmbCount6,
 GR56.QMTorusAbelian,
 GR56.CMPairDescendsQbar,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.gonzalezRotgerProp56X6] by GR56.gonzalezRotgerProp56X6_of_main
  still assumes: [GRCountX6.EichlerOptEmbCount6,
 RayClassCFT.ShimuraMainThmIDeligneY3AbU,
 HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [OpenResearchLeaves22.gonzalezRotgerProp56X6] by GR56.gonzalezRotgerProp56X6_of_st
  still assumes: [GRCountX6.EichlerOptEmbCount6,
 GR56.QMTorusAbelian,
 HDec.HSyn.G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar,
 BPAnalytic.Uniformization.UniformizationLeafAll,
 ZInQ.HomLattice.GAGAMorphism,
 AvSplit.MumfordTorsionAlgClosed]
  axioms: [propext, Classical.choice, Quot.sound]
...
#discharges: 63 open hypotheses, 1976 theorems checked, 10 discharge one
```

The other seven lines come from earlier contributions that are not yet folded, for example
`GRCountX6.prop56X6_of_r5fpCount`; see `discharges.txt`.

### 2.2 Autofold spec (`scratch/gr56-prove/autofold.json`, recommended)

* Field `gonzalezRotgerProp56X6` is replaced by one new leaf, `eichlerOptEmbCount6 : _root_.GRCountX6.EichlerOptEmbCount6`.
  Its kind is `published` and its flag is `locator UNVERIFIED (theorem numbers from memory)`.
* Proof:

  ```
  _root_.GR56.gonzalezRotgerProp56X6_of_main {n}.eichlerOptEmbCount6 {n}.shimuraMainThmIDeligneY3AbU
    {l}.shimuraTaniyamaQbar {t}.uniformizationLeafAll {t}.gagaMorphism {t}.mumfordTorsionAlgClosed
  ```

  The proof refers to two other bundles: `{l}` is `OpenAddedLeaves17` and `{t}` is `OpenTextbookLeaves11`.
* `python3 scripts/one_proof/autofold.py scratch/gr56-prove/autofold.json --dry-run` printed
  `strict count: 46/10 on 56 -> 46/10 on 56; strictest 45/11 -> 45/11` (VERIFIED).
* The generated module is `scratch/gr56-prove/FoldCheck.lean`: the dry-run output without its first line, plus a
  `#print axioms` line. It compiles, and `HDec.HSyn.sixContactMin_of_open30` uses only the standard axioms
  (VERIFIED).

**Alternative** (`scratch/gr56-prove/autofold-alt-torus.json`), for a lead who prefers not to depend on the composite
field `shimuraMainThmIDeligneY3AbU`:

* the new leaves are `eichlerOptEmbCount6` and `qmTorusAbelian : _root_.GR56.QMTorusAbelian`;
* the proof is `GR56.gonzalezRotgerProp56X6_of_st {n}.eichlerOptEmbCount6 {n}.qmTorusAbelian {l}.shimuraTaniyamaQbar {t}…`;
* `--dry-run` gives `46/10 on 56 -> 47/10 on 57; strictest 45/11 -> 46/11` (VERIFIED).

### 2.3 Rating of the new leaf

* **`eichlerOptEmbCount6` (`GRCountX6.EichlerOptEmbCount6`), printed form: yes.**
  * Eichler's theorem on optimal embeddings, in the form of Vignéras, *Arithmétique des algèbres de quaternions*,
    LNM 800 (1980), Ch. III Thm 5.11 and Cor. 5.12, or Voight, *Quaternion Algebras* (2021), Thm 30.7.3.
    Theorem numbers UNVERIFIED.
  * Specialization: `B = (2, −3)`, `𝒪 = LeafQM.O` maximal, `N = 1`. `𝒪` has one left ideal class (indefinite `B`
    over `ℚ`), so the sum over ideal classes has one term.
  * The count is modulo `𝒪^×`: `h(R)·∏_{p∣6}(1 − (k/p))`. Here `eichlerLocal` is 2, 1 or 0 for `p` inert,
    ramified or split. At conductor prime to 6 this is `1 − (R/p)`.
  * It is over genuine definitions only (Mathlib's quaternion algebra, `CommRing.Pic`, `Ideal.IsPrime` in `𝓞 k`,
    and the kernel's `LeafQM.O`), with no structure invented for the purpose.
  * Consistency (by hand, STANDARD formula): `h·∏ = 2, 2, 2, 4` at discriminants −4, −3, −24, −19. These match the
    field's counts and the CM fibres of Elkies' model, and through the proved bijection they are the field's values
    in every occurring case.
  * It is not implied by the field alone: it also asserts that no embedding exists when some `p ∣ 6` splits.
    That clause is classical and true, because `B_p` is a division algebra.
* `qmTorusAbelian` (alternative spec only), printed form: **consequence**.
  * Shimura, Ann. of Math. 78 (1963) §§2-4 shows that QM tori by a maximal order of an indefinite algebra over `ℚ`
    are polarizable; Birkenhake–Lange, Ch. 9. Locators UNVERIFIED.
  * Algebraization uses Riemann's theorem with GAGA (the converse direction is the kernel's `uniformizationLeafAll`).
  * In the recommended spec it is not a leaf: it is the moduli clause `ModuliAtUnits` of the existing field at `u = 1`.
* `CMPairDescendsQbar` is never a leaf: it is proved from `shimuraTaniyamaQbar`.

### 2.4 Optional manual fold (not recommended): the bound only

The chain uses the count once (VERIFIED, `scratch/gr56-prove/Reach.lean`, closure of `ZInQ.OneProof.frozenTarget`,
97682 constants, `reach.txt`): `HDec.FS5NoCM.nocm_on_witness` (TailC L1371). It uses the count only as the bound
`#CM(R) ≤ 2`. `GR56.R5fpCountLe` is that bound: it is implied by `R5fpCount` (`r5fpCountLe_of_r5fpCount`), and it is
proved from Eichler's count and the three textbook fields alone (`r5fpCountLe_of_eichler`; no existence statement is
needed).

The consumer chain is rerouted in the contributor file: `nocm_on_witness_le`, `fibreComTrivialOwn_of_le`,
`fibreComTrivialFull_of_le`, `fibreComTrivialFull_of_leaves'_le` and `fibreComTrivialFull_of_leaves''_le`. Each
is TailC's text with `hC : R5fpCount` replaced by `hC : GR56.R5fpCountLe`, and the count step changed from `=` to
`≤`.

* The fold would replace, at TailK L289-294 (`HDec.HSyn.gluePieces_of_open4`),
  `FS5NoCM.fibreComTrivialFull_of_leaves'' … r.r5count` by
  `FS5NoCM.fibreComTrivialFull_of_leaves''_le … (GR56.r5fpCountLe_of_eichler hE hU hG hM)`.
* But `r5count : R5fpCount` is a field of the old generations `OpenResearchLeaves2` (TailE L6469), `…5` (TailN L76),
  `…7` (TailX L196), `…8` (TailZ4 L188). It is filled from `gonzalezRotgerCountX6` (TailZ9 L96) and
  `gonzalezRotgerCountX6Ab` (TailZ23 L804, TailZ27 L111). A weaker leaf cannot fill it.
* So this fold would have to bypass every generation from TailK up to the top, which costs far more than §2.2 for
  the same leaf count (Eichler replaces the field). The theorems are kept because they show that the chain needs
  only the injection and Eichler's count.

## 3. Method

Notation: `B = (2, −3 | ℚ)`, `𝒪 = LeafQM.O`, and `act x` is the action of `x ∈ B` on `ℂ²` by `qmMatB`. `L(v)` is the
orbit lattice `ι(𝒪)v`. `σQ = IsAlgClosed.lift : ℚ̄ → ℂ` is fixed, and `ψ = IsAlgClosed.lift : k → ℂ` is fixed.

1. **Lattice data** (`LatData`, `exists_latData`). This is gt-qm's `unif_conj` with all its data kept:
   * T35 gives the uniformization `Φ`; T11(a) from `HomLatticeCorr` gives `ρ`; the chain's `QMLatticeAlgebra` gives
     `Fl` and `τ`;
   * `Fl` carries `Λ` onto `L(τ, 1)` and `ρ(ι a)` to `act a`.

   The normalized `ρn = Fl ∘ ρ ∘ Fl⁻¹` is injective, sends `ι a` to `act a`, and has as image the `L(v)`-preserving
   maps.
2. **Isomorphisms from scalars** (`qmIso_of_scalar`). If `μ·L(v) = L(v')`, then `Fl'⁻¹ ∘ μ ∘ Fl` maps `Λ` onto `Λ'`
   and intertwines `ρ(ι a)`. `HomLatticeCorr`'s realization clause turns it and its inverse into homomorphisms.
   Uniqueness gives the inverse laws and `ι`-equivariance.
3. **Base change and descent.** `bcQ P` is `P` base-changed along `σQ`, with `ι_ℂ = endBC ∘ ι`.
   * `qmIso_descend`: T11(b), proved in the chain, descends a `QMIso` of base changes to `ℚ̄`. Faithfulness of
     `Over.pullback` gives the equations.
   * `com_bcQ`: `endBC` is bijective, so `End_𝒪` is unchanged.
4. **Scalars.** An element `e ∈ End_𝒪(A_ℂ)` acts by a scalar `scal e` (gt-qm's `commutant`).
   * `exists_O`: `scal e·v = ι(x)v` for some `x ∈ 𝒪`.
   * `exists_com`: conversely, if `ι(x)v = c·v` with `x ∈ 𝒪`, then `c = scal e` for some `e`.
5. **Orders.**
   * `quad_rel`: an integral `r` satisfies `r² − tr + n = 0` with `t, n ∈ ℤ` (via `minpoly ℤ`).
   * `image_cross`: two ring maps `R → ℂ` have the same image. The two roots of `X² − tX + n` are `ψ(r)` and
     `ψ(t − r)`, with `t − r ∈ R`.
   * `exists_nat_mul_mem`: `n·a ∈ R` for some `n > 0`, because the conductor is finite and nonzero.
6. **The embedding of a CM point** (`emb`, `emb_opt`). `emb(a)` is the unique `b ∈ B` with `ι(b)v = ψ(a)v`
   (uniqueness from `act_inj`).
   * Existence: `ψ(R)` equals the scalar image of `End_𝒪` (step 5), and `n·a ∈ R`.
   * Optimality: `emb(a) ∈ 𝒪` exactly when the scalar `ψ(a)` preserves `L(v)`, that is, when it comes from
     `End_𝒪` (`exists_com`), which happens exactly when `a ∈ R`.
7. **Injectivity** (`iso_of_conj`, `cmMap_injective`). Suppose `Φ₂ = uΦ₁u⁻¹` and `a₀ ∉ ℚ`.
   * `ι(u)v₁` and `v₂` are `ψ(a₀)`-eigenvectors of `ι(Φ₂ a₀)`. Eigenlines are one-dimensional, because otherwise
     `ι(Φ₂ a₀)` is scalar and `Φ₂ a₀` is central (`central_of_comm`, `eig_line`).
   * So `ι(u)v₁ = μv₂`. Then `μ⁻¹L(v₁) = L(v₂)` (using `u ∈ 𝒪^×`), and steps 2-3 give `P₁ ≅ P₂`.
8. **Comparison** (`conj_of_iso`). Two lattice models of isomorphic pairs differ by a unit:
   * the lift of the isomorphism commutes with `ι(𝒪)`, so it is a scalar `s`;
   * `s·v = ι(x)v'` and `s⁻¹v' = ι(y)v` give `xy = yx = 1`, and the embeddings are conjugate by `y`.
9. **Surjectivity** (`cmMap_surjective`).
   * `exists_eigvec`: an optimal `Φ` has an eigenvector `(τ, 1)ᵀ` with `Im τ ≠ 0`. The proof uses the pure part `y₀`
     of `Φ(a₀)` with `y₀² = d`; `ψ(a₁)` is not real because `k` is totally complex; the matrix entries are explicit.
   * If `Im τ < 0`, conjugate by `1 + i` (norm −1). This multiplies `τ` by `(1+√2)/(1−√2) < 0` (`eig_conj_uI`).
   * `QMTorusAbelian` gives `(A, ι)` over `ℂ` with lattice `L(τ, 1)`. Its `End_𝒪 ≅ R` (`com_equiv_of_eig`, using
     gt-qm's `comm_span`: the centralizer of `y₀` is `ℚ + ℚy₀`). It has a CM element `ψ`, `ψ² = d < 0`
     (`sqForm_neg`, `int_of_O`).
   * `CMPairDescendsQbar` gives `Q/ℚ̄`, and step 8 gives `cmMap [Q] = [Φ]`.
10. **The two existence statements from existing fields.**
    * `qmTorusAbelian_of_main` is the clause `ModuliAtUnits` of `shimuraMainThmIDeligneY3AbU` at `u = 1`.
    * `cmPairDescendsQbar_of_st`:
      * `QMSplitSTQM.embed_Ed` (qm-split, general `d < 0`) embeds `ℚ(√2, √d)` in `End⁰(A)`, so
        `shimuraTaniyamaQbar` gives `A ≅ A₀ ×_{ℚ̄, ιe} ℂ` for some `ιe`;
      * `exists_alpha`: `ιe = σQ ∘ α`, because `σQ` maps `ℚ̄` onto the algebraic closure of `ℚ` in `ℂ`
        (`IsAlgClosed.ringHom_bijective_of_isIntegral`);
      * `bc_comp_iso`: `A₀ ×_{ιe} ℂ ≅ (A₀ ×_α ℚ̄) ×_{σQ} ℂ`, through G0StableBC's `exists_pbPaste`. A direct proof
        hit a kernel deterministic timeout;
      * `ι` descends through `endBC_bijective`, with the conjugation `conjEnd` copied from `RayClassCFT.conjEnd`.
11. **Count.** gt-grcount's `r5fpCount_of_eichler` and `prop56X6_of_r5fpCount` conclude.

## 4. What remains

* `GRCountX6.EichlerOptEmbCount6` (Eichler's count). This is pure algebra. A Lean proof needs, beyond Mathlib:
  * local maximal orders of the division algebras over `ℚ₂` and `ℚ₃`, and their optimal embeddings (the factors
    `1 − (k/p)`);
  * the local-global correspondence for lattices;
  * the action of `Pic(R)` on right `𝒪`-ideals (class number one is in the kernel: `QMSplit.CNO.principal_of_lattice`,
    `RayClassCFT.classNumberOneB_proof`).

  Not attempted (SPECULATIVE estimate: weeks).
* The recommended fold depends on the composite field `shimuraMainThmIDeligneY3AbU` only for its moduli clause at
  `u = 1`. If that field is later split, `QMTorusAbelian` should follow from the piece that keeps `ModuliAtUnits`.
* Statement review of `EichlerOptEmbCount6` against the print (normalization by `𝒪^×` rather than `𝒪^1`) is still
  pending. The proved bijection `CM(R) ≃ Emb(R, 𝒪)/𝒪^×` together with the field's printed count confirms the `𝒪^×`
  normalization in every case where `CM(R) ≠ ∅` (`R` occurs).
