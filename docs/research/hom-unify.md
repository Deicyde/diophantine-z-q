# hom-unify: the two `Hom` forms of T11(a), and G10 from `HomLinearLift` in the assembly

Task hom-unify, 2026-11-13.
- Lean, step 1: `ZInQKernel/Contrib/HomUnify/Corr.lean`. It imports only
  `ZInQKernel.HDecomp.LeafPush2.T` and Mathlib. Build it with
  `lake build ZInQKernel.Contrib.HomUnify.Corr`.
- Lean, step 2: `scratch/hom-unify/`. The single-file check is `HomUnifyFlat.lean`, made by
  `py/assemble.py` and checked by `build_flat.sh`. The fast olean chain is
  `build_prefix.sh` → `ctail.sh TailBase.lean TailBase` → `ctail.sh HConj.lean HConj` →
  `ctail.sh HBundle.lean HBundle`.
- Results log: `scratch/hom-unify/log.md`. Verbatim check: `scratch/hom-unify/py/verbatim_check.py`.
- No existing file was edited.

Marks: **VERIFIED** (compiled, or read in a file), **STANDARD** (published, with a reference),
**SPECULATIVE**. Theorem numbers recalled without a source are **UNVERIFIED** (no network). This
is model work; there has been no human review.

## 0. Main result

1. **`T11aHom` and `HomLinearLift` are not equivalent statements. They are the two converse
   halves of one textbook theorem, and neither formally implies the other.** They live over the
   same layer, so no bridge is needed. One new leaf, `HomLatticeCorr`, contains both halves. It
   implies `T11aHom`, `HomLinearLift` and leaf-push2's existing leaf `T11a_RiemannEnd` (T11(a)).
   The uniqueness part of the realization half is proved outright. VERIFIED, compiled.
2. **G10 comes from `HomLinearLift` inside the assembly.**
   - `GaloisPiecesHom` is `GaloisPieces` with `odd : G10Glue` replaced by
     `homLift : HomLinearLift`, and it implies `GaloisPieces`.
   - `GluePieces3Hom` is linked-tate's `GluePieces3` with `g10Glue` replaced by
     `homLinearLift`. It gives `ZInQ.SixContactMin` end to end.
   - VERIFIED, compiled over linked-tate's flat assembly. All axiom reports are standard (§2).
3. **The single leaf for the leaf list is `HomLatticeCorr`** (§3). It should **replace** T11(a)
   (`T11a_RiemannEnd`), which it implies. With that change, T11(a), `T11aHom` and `HomLinearLift`
   are all covered and the leaf count does not grow.

### Declarations proved

All are compiled. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every one.

**Step 1** (`ZInQKernel/Contrib/HomUnify/Corr.lean`, namespace `ZInQ.HomUnify`):

```lean
theorem homLinearLift_of_corr (h : HomLatticeCorr) : HomLinearLift
theorem t11aHom_of_corr (h : HomLatticeCorr) : T11aHom
theorem t11a_riemannEnd_of_corr (h : HomLatticeCorr) : ZInQ.LeafPush2.T11a_RiemannEnd
theorem corr_iff : HomLatticeCorr ↔ HomLinearLift ∧ (realization clause with ∃!)
theorem hom_ext_of_cpts {A B : PkgI3.AbVar ℂ} (f f' : A.X ⟶ B.X)
    (h : ∀ p : CPts A (RingHom.id ℂ), p ≫ f = p ≫ f') : f = f'
theorem induces_unique … (hU : IsUniformization (RingHom.id ℂ) ΛA ΦA) (M) {f f'}
    (hf : ∀ z, ΦB (M z) = ΦA z ≫ f.hom) (hf' : ∀ z, ΦB (M z) = ΦA z ≫ f'.hom) : f = f'
theorem t11aHom_iff_ex : T11aHom ↔ T11aHomEx
theorem corr_iff_lift_realize : HomLatticeCorr ↔ HomLinearLift ∧ HomRealize
theorem t11aHom_of_realize (H : HomRealize) : T11aHom
```

`T11aHom` and `HomLinearLift` in this file are verbatim copies of `R1bState.T11aHom`
(`scratch/r1b-state/Part8b_Hom.part`) and `G0Galois.HomLinearLift`
(`scratch/conj-twist/ConjTwist.lean`). Only the namespace and the `open` lines differ.
`verbatim_check.py` confirms this: ALL OK.

`lake build` output (VERIFIED):

```
'ZInQ.HomUnify.homLinearLift_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HomUnify.t11aHom_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HomUnify.t11a_riemannEnd_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HomUnify.corr_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HomUnify.hom_ext_of_cpts' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HomUnify.induces_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HomUnify.t11aHom_iff_ex' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HomUnify.corr_iff_lift_realize' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.HomUnify.t11aHom_of_realize' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (9064 jobs).
```

**Step 2** (`scratch/hom-unify/parts/H20_bundle.lean`, over linked-tate's assembly):

```lean
theorem G0Galois.g10Glue_of_homLinearLift (h5 : PkgI2.TorsionStructure.{0})
    (hT : PkgI3.TateModuleFree) (h35 : ZInQ.LeafPush2.UniformizationExists)
    (hN2 : HomLinearLift) : G10Glue
structure G0Galois.GaloisPiecesHom : Prop  -- GaloisPieces with `homLift : HomLinearLift` for `odd`
theorem G0Galois.galoisPieces_of_hom (t : HSyn.TextbookLeaves) (m : GaloisPiecesHom) : GaloisPieces
structure HSyn.GluePieces3Hom : Prop       -- GluePieces3 with `homLinearLift` for `g10Glue`
theorem HSyn.gluePieces3_of_hom (t : TextbookLeaves) (gp : GluePieces3Hom) : GluePieces3
theorem HSyn.sixContactMin_of_leaves3Hom (r : ResearchLeaves) (t : TextbookLeaves)
    (gp : GluePieces3Hom) : ZInQ.SixContactMin
theorem HomUnify.homLinearLift_of_corr (h : HomLatticeCorr) : G0Galois.HomLinearLift
theorem HomUnify.g10Glue_of_corr (h5 : PkgI2.TorsionStructure.{0}) (hT : PkgI3.TateModuleFree)
    (h35 : ZInQ.LeafPush2.UniformizationExists) (h : HomLatticeCorr) : G0Galois.G10Glue
```

`T5`, `T26` and `T35` come from the textbook bundle fields `t.t5`, `t.t26` and `t.t35`.

Olean chain output (`olean/HBundle_out.txt`, VERIFIED):

```
'G0Galois.conjTwistNontrivial_of_leaves' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0Galois.g10Glue_of_conjTwist_new' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0Galois.g10Glue_of_homLinearLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'G0Galois.galoisPieces_of_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'HSyn.gluePieces3_of_hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'HSyn.sixContactMin_of_leaves3Hom' depends on axioms: [propext, Classical.choice, Quot.sound]
'HomUnify.homLinearLift_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound]
'HomUnify.g10Glue_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Single-file check (`build_flat.sh`, `HomUnifyFlat.lean`, 47 459 lines; output in
`scratch/hom-unify/flat_out.txt`, VERIFIED):
- `lake env lean` exits 0 in 602 s, with 0 errors and no `sorry`.
- There are 233 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`. Two of them,
  `hodgeLatticeTheorem_of_tangent` and `hodgeLatticeTheorem_of_abVarFacts` from `Leaves.lean`, are
  wrapped over three lines in the output.
- The reports include all eight theorems above, plus `conjTwistFromLeaves_of_homLinearLift` and
  `twistCEval`.

## 1. Step 1: `T11aHom` versus `HomLinearLift`

### 1.1 The layers (VERIFIED, read and compiled)

Both statements are over the build's objects:
- `PkgI3.AbVar`, from `ZInQKernel/HDecomp/Objects.lean`. In `R1b.lean` the name `AbVar` (under
  `open LeafQM LeafQM.AV PkgI3`) resolves to `PkgI3.AbVar`, because no `LeafQM.AV.AbVar` exists;
- `ZInQ.LeafPush2.CPts`, `ZInQ.LeafPush2.IsUniformization` and `PkgI3.AbVar.Hom`, from
  `ZInQKernel/HDecomp/LeafPush2/R22.lean` and `Objects.lean`.

Both verbatim copies elaborate in one file over `ZInQKernel.HDecomp.LeafPush2.T`, so no bridge is
needed.

### 1.2 Why they are not equivalent

The analytic representation is the map `ρ : Hom(A, B) → {M ∈ Hom_ℂ(ℂ^g, ℂ^h) : MΛ_A ⊆ Λ_B}`.

| | `T11aHom` (r1b-state) | `HomLinearLift` (conj-twist) |
|---|---|---|
| base | `K = ℂ`, `σ = id` | any field `K`, any `σ : K → ℂ` |
| dimensions | `dim A = dim B = g` | `g`, `h` arbitrary |
| input → output | lattice map `M` → unique `f` | homomorphism `f` → linear `M` |
| content | `ρ` is onto the lattice maps and injective (GAGA/Chow: holomorphic ⇒ algebraic) | `ρ` is defined (algebraic ⇒ holomorphic; a holomorphic homomorphism of tori lifts to a linear map, Birkenhake–Lange 1.2.1) |

- **`T11aHom` does not give `HomLinearLift`.** `T11aHom` never produces an `M` from an `f`. A
  homomorphism that does not arise from a lattice map is compatible with `T11aHom`. Excluding
  such homomorphisms is exactly `HomLinearLift`'s content. It is also over `ℂ` only, while G10
  needs `HomLinearLift` over number fields at `σ = ι ∘ alg`. Base change of `IsUniformization`
  to `A_ℂ` is not available (conj-twist F3).
- **`HomLinearLift` does not give `T11aHom`.** `HomLinearLift` never produces a homomorphism.
  The existence of `f` for a given lattice map is the GAGA content of `T11aHom`, which nothing in
  `HomLinearLift` touches. The uniqueness of `f` is not leaf content at all: it is proved here
  (`induces_unique`, from `hom_ext_of_cpts` and the surjectivity of `Φ_A`).
- Both statements are true (STANDARD, §3). So "not equivalent" means that neither is a formal
  consequence of the other by an argument available in the project. It does not mean that one
  of them could be false.
- **`T11aHom` is equivalent to its existence form** `T11aHomEx` (`t11aHom_iff_ex`, compiled).
- **`HomLatticeCorr` is equivalent to `HomLinearLift ∧ HomRealize`** (`corr_iff_lift_realize`,
  compiled). Here `HomRealize` is the realization half with `∃`, for all `g`, `h`.
- The proved implications are:
  - `HomLatticeCorr → HomLinearLift`;
  - `HomLatticeCorr → T11aHom`;
  - `HomRealize → T11aHom`;
  - `HomLatticeCorr → T11a_RiemannEnd`.

### 1.3 `hom_ext_of_cpts` (the one non-trivial proof of step 1)

Let `f, f' : A.X ⟶ B.X` be morphisms of abelian varieties over `ℂ` that agree after
precomposition with every `ℂ`-point. Then `f = f'`. The proof:
- `A.X.left` is integral, by `GeometricallyIntegral.isIntegral_of_subsingleton`.
- Mathlib's `ext_of_apply_eq` (`Mathlib/AlgebraicGeometry/AlgClosed/Basic.lean`), applied with
  `S = univ`, reduces the claim to closed points.
- A closed point `x` is the image of the `ℂ`-point `pointOfClosedPoint A.X.hom x hx`, by
  `pointOfClosedPoint_apply`.

## 2. Step 2: `HomLinearLift` in place of `G10Glue`

**Which `G10Glue`.** conj-twist's `g10Glue_of_leaves` proves g10-odd's original `G10Glue`, whose
hypotheses are the opaque `HSyn.T11_RiemannGAGA` and `HSyn.T12_ArtinComparison`. The assembly's
`G10Glue` (`scratch/g0-assemble/parts/70_galois.lean`, identical in linked-tate) takes
`T11a_RiemannEnd → T11b_Rigidity → FaltingsTate → …` instead. The two have the same conclusion.

So `g10Glue_of_homLinearLift` composes two compiled steps:
- conj-twist's `conjTwistNontrivial_of_leaves : T5 → T26 → T35 → HomLinearLift → ConjTwistNontrivial`;
- g10-odd's reduction `g10Glue_of_conjTwist_new : ConjTwistNontrivial → G10Glue`, as re-checked by
  rv-gluepieces2 for the assembly's statement (`scratch/rv-gluepieces2/checks/c1_g10.lean`).

This is conj-twist's `g10Glue_of_leaves` for the assembly's `G10Glue`.

**Which assembly.** The assembly is linked-tate's (`scratch/linked-tate/`), the latest end-to-end
one. It has the pin-applied `Leaves.lean`, g0-assemble's parts 05-90, and linked-tate's parts
92-99 with `GluePieces3` (29 fields) and `HSyn.sixContactMin_of_leaves3`. On top of it come three
parts:
- `H10_conjtwist.lean`: `ConjTwist.lean` lines 39-2005 (§1-§16), verbatim except three
  declarations that part 70_galois already has with identical text (`resQ`, `qEmbRing`,
  `resQ_spec`). The removals are asserted by `assemble.py`.
- `H11_g10new.lean`: rv-gluepieces2's `c1_g10.lean`, verbatim except four declarations already in
  H10 with identical text (`isComplexConj_mul_self`, `one_tmul_injective`,
  `baseChange_injective'`, `ConjTwistNontrivial`). These removals are also asserted.
- `H20_bundle.lean`, the new part:
  - `GaloisPiecesHom` and `galoisPieces_of_hom`;
  - `GluePieces3Hom`, whose 28 other fields are copied verbatim with their docstrings from
    `99_bundle3.lean`;
  - `gluePieces3_of_hom` and `sixContactMin_of_leaves3Hom`;
  - a copy of `HomLatticeCorr` with `g10Glue_of_corr`.

conj-twist's §17 is not used: it holds g10-odd's original `G10Glue` and its copies of `Vb`, `tate`,
`Intertwines` and `G10Out`, which would clash with part 70_galois.

**Mechanical checks** (`verbatim_check.py`, ALL OK). Each copy matches its source:
- `T11aHom` and `HomLinearLift` in `Corr.lean`;
- `HomLatticeCorr` in H20;
- `ConjTwistNontrivial` (the conj-twist and c1 copies are identical);
- `GaloisPiecesHom`: it differs from `GaloisPieces` only in the line `odd : G10Glue` →
  `homLift : HomLinearLift`;
- `GluePieces3Hom`: it differs from `GluePieces3` only in the `g10Glue` field.

Timings (olean chain):

| step | time | result |
|---|---|---|
| LPrefix | 580 s | exit 0 |
| TailBase (linked-tate parts) | about 2 min | exit 0 |
| HConj | 33 s | exit 0 |
| HBundle | 5 s | exit 0 |

`GluePieces3Hom` has 29 fields like `GluePieces3`. The glue field `g10Glue` is gone; the textbook
leaf `homLinearLift` takes its place.

## 3. The single leaf

```lean
def HomLatticeCorr : Prop :=
  (∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom) ∧
  (∀ (A B : PkgI3.AbVar ℂ) (g h : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃! f : PkgI3.AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom)
```

**Source** (STANDARD; all theorem numbers UNVERIFIED):
- Birkenhake–Lange, *Complex Abelian Varieties*, §1.2, Prop. 1.2.1 and the analytic and rational
  representations: homomorphisms `ℂ^g/Λ → ℂ^h/Λ'` of complex tori correspond bijectively to
  `ℂ`-linear `M` with `MΛ ⊆ Λ'`;
- Mumford, *Abelian Varieties*, §1 (`A(ℂ)` is a complex torus) and §3 (Hom of abelian varieties
  over `ℂ` = holomorphic homomorphisms);
- Serre, GAGA (1956), or Chow's theorem, for "holomorphic ⇒ algebraic" in clause 2;
- for clause 1 over a general `K`: the morphism `f_ℂ` induced on `ℂ`-points through `σ` is
  algebraic, hence holomorphic.

`HomLatticeCorr` is the published bijection `Hom(A_ℂ, B_ℂ) ≅ Hom_Λ(ℂ^g, ℂ^h)` together with the
remark that for a `K`-homomorphism the analytic representation is that of `f_ℂ`. It is not a
strengthening.

**Why it is true as stated** (SPECULATIVE in the details; each step STANDARD). Suppose
`IsUniformization` holds and `g = dim A`. Then `Φ` is a surjective holomorphic homomorphism
`ℂ^g → A(ℂ)`, so it equals `exp_A ∘ D` with `D` linear. Surjectivity and equal dimension force `D`
to be bijective. Hence `Λ = D⁻¹(ker exp)` is a full lattice and `Φ` is the standard
uniformization in other coordinates.

Two points about the definition do not matter:
- `IsUniformization`'s analytic clauses use only sections of `A` over `K`. They still pin the
  analytic structure, because `A_ℂ`'s affine coordinate rings are generated over `ℂ` by those
  sections.
- `IsUniformization` does not require `Λ` to be discrete; discreteness follows from the above.

**Recommendation.** Put `HomLatticeCorr` on the leaf list in place of T11(a)
(`ZInQ.LeafPush2.T11a_RiemannEnd`, bundle field `t11a`), which it implies
(`t11a_riemannEnd_of_corr`). It covers:
- conj-twist's N2 (`HomLinearLift`, now the field of `GluePieces3Hom`);
- r1b-state's candidate `T11aHom`;
- T11(a) itself.

Equivalently, by `corr_iff_lift_realize`, it is `HomLinearLift ∧ HomRealize`, with no uniqueness
clause. This is proposed only; no existing statement was changed.

If only one of the two original statements is kept, keep `HomLinearLift`:
- it is the one on the end-to-end route (G10);
- `T11aHom` is used only in r1b-state's finest reduction of `FibreQMPeriod`, which is still a glue
  field of `GluePieces3`.

## 4. What remains

- Nothing remains open in steps 1 and 2.
- `HomLatticeCorr` (or `HomLinearLift`) is a textbook leaf. It is not proved: it needs
  analytification and GAGA, which Mathlib 4.35 lacks.
- r1b-state's consumers of `T11aHom` (`piOfQMLattice_of`, `familyOrbitsInv_of`) can take it from
  `HomLatticeCorr` through `t11aHom_of_corr`. They are not re-run here.
