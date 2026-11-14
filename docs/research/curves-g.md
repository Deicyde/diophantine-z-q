# curves-g: group G of leaf-fold3 (Jacobians, `X₁(N)`, function fields): t33, t34, t38

Task curves-g, 2026-11-13. Base: fork main 8ec80711 with origin/wip/leaf-fold3 (f7951690) merged. Lean:
`ZInQKernel/Contrib/CurvesG/` (three new modules) and `scratch/curves-g/` (single-file check). Results log:
`scratch/curves-g/log.md`. No existing project file was edited. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a named file. **STANDARD** = published, with a reference.
**SPECULATIVE** = a judgement. **UNVERIFIED** = a theorem number or locator recalled without a source (no
network on this host; no copy of the books).

## 1. Main result

Of the three group-G fields of leaf-fold3's `OpenTextbookLeaves3` (T40 belongs to task t40-clash):

| field | owner (kernel) | outcome |
|---|---|---|
| `t38 : X1Belyi.CurveOfFunctionFieldQ` | `ZInQKernel/HDecomp/ModCurves/X1Belyi.lean` | **reduced**: its clause "`X` has a `ℚ`-point when `F` has a place of degree 1" is **proved** (valuative criterion); the rest is reduced to three textbook Props (A) `NormalModelOfFunctionFieldQ`, (B) `NormalCurveSmoothQ`, (C) `GeomConnectedOfConstantFieldQ` |
| `t34 : LeafModCurves.DimJ1Genus` | `ZInQKernel/HDecomp/ModCurves/Leaves.lean` | **reduced** to its two published halves: `DimJacobianEqGenus` (every curve over `ℚ`: `dim Jac = genus`) and `GenusX1Field` (the genus of `K_N` is the genus of `Γ₁(N)`), with the genus of a function field defined in Mathlib terms (`fieldGenus`) |
| `t33 : LeafModCurves.JacobianExists ℚ` | `ZInQKernel/HDecomp/ModCurves/Defs.lean` | **confirmed** the published statement (Weil; Milne, *Jacobian varieties*), not stronger (§4) |

Declarations proved (namespace `ZInQ.Contrib.CurvesG`; the two Props they conclude are the kernel owners' own
definitions, imported, not restated):

```lean
-- ZInQKernel/Contrib/CurvesG/RatPoint.lean
theorem nonempty_ratPt_of_place (X : Over SpecQ) [IsProper X.hom] [IsIntegral X.left]
    {F : Type} [Field F] (e : X.left.functionField ≃+* F) (r : ℚ →+* F)
    (w : ValuationSubring F) (hw : ∀ c : ℚ, r c ∈ w)
    (hres : ∀ x ∈ w, ∃ c : ℚ, x - r c ∈ w.nonunits) : Nonempty (RatPt X)
theorem curveOfFunctionFieldQ_of_noPoint (h : CurveOfFunctionFieldQNoPoint) :
    X1Belyi.CurveOfFunctionFieldQ
-- ZInQKernel/Contrib/CurvesG/CurveSplit.lean
theorem curveOfFunctionFieldQNoPoint_of_split (hA : NormalModelOfFunctionFieldQ)
    (hB : NormalCurveSmoothQ) (hC : GeomConnectedOfConstantFieldQ) : CurveOfFunctionFieldQNoPoint
theorem curveOfFunctionFieldQ_of_split (hA : NormalModelOfFunctionFieldQ)
    (hB : NormalCurveSmoothQ) (hC : GeomConnectedOfConstantFieldQ) : X1Belyi.CurveOfFunctionFieldQ
-- ZInQKernel/Contrib/CurvesG/GenusSplit.lean
theorem dimJ1Genus_of_split (h1 : DimJacobianEqGenus) (h2 : GenusX1Field) :
    LeafModCurves.DimJ1Genus
```

**Axioms** (VERIFIED, `scratch/curves-g/axioms_contrib_out.txt`, `lake env lean scratch/curves-g/AxiomsContrib.lean`
exit 0): each of `hom_to_specQ_ext`, `residueToRat`, `nonempty_ratPt_of_place`, `curveOfFunctionFieldQ_of_noPoint`,
`curveOfFunctionFieldQNoPoint_of_split`, `curveOfFunctionFieldQ_of_split`, `dimJ1Genus_of_split`
`depends on axioms: [propext, Classical.choice, Quot.sound]`. The same file compiles
`example : CurveOfFunctionFieldQNoPoint → X1Belyi.CurveOfFunctionFieldQ := curveOfFunctionFieldQ_of_noPoint`
and the analogous `example`s for the two splits, against the kernel owners' definitions.

**Effect on leaf-fold3's count.** In `OpenTextbookLeaves3` the field `t38` is replaced by `t38a`, `t38b`, `t38c`
and `t34` by `t34a`, `t34b`: `HDec.HSyn.sixContactMin_of_openG` (single-file check, §5) derives the kernel's
`ZInQ.SixContactMin` from the bundle `OpenTextbookLeavesG`. The number of open Props rises from 68 to 71, but
none of the new ones is a composite through `X₁(N)` any more except `GenusX1Field`, and the point clause of T38 is
gone. `t33` is unchanged.

**What remains open in group G** (excluding T40): `JacobianExists ℚ` (T33, LEAF), `DimJacobianEqGenus`,
`GenusX1Field` (from T34), `NormalModelOfFunctionFieldQ`, `NormalCurveSmoothQ`, `GeomConnectedOfConstantFieldQ`
(from T38). None of them is proved here.

## 2. t38: `X1Belyi.CurveOfFunctionFieldQ`

**The field** (`X1Belyi.lean`, leaf M1 of x1-belyi): for every finite extension `F` of `ℚ(T)` with
`ConstantFieldIsQ F`, there is `X : Over SpecQ` with `IsCurve X` (proper, smooth of relative dimension 1,
geometrically connected), `IsIntegral X.left`, `X.left.functionField ≃+* F`, and `HasRationalPlace F →
Nonempty (RatPt X)`.

**2.1 The point clause, proved** (`RatPoint.lean`, VERIFIED compiled). `nonempty_ratPt_of_place`: for `X` proper
and integral over `ℚ`, a field `F ≅ K(X)` and a valuation subring `w ⊆ F` containing `ℚ` with residue field `ℚ`:
the square `Spec F → X` (generic point, `Scheme.fromSpecStalk`), `Spec w → Spec ℚ` commutes (any two maps to
`Spec ℚ` agree, `hom_to_specQ_ext`, from `ext_to_Spec`), so Mathlib's valuative criterion
(`UniversallyClosed.eq_valuativeCriterion`, Stacks 01KF) gives a lift `Spec w → X`; composed with
`Spec ℚ ≅ Spec κ(w) → Spec w` (`residueToRat`: `ℚ → κ(w)` is bijective by `HasRationalPlace`) it is a
`ℚ`-point. `curveOfFunctionFieldQ_of_noPoint` then derives the field from

```lean
def CurveOfFunctionFieldQNoPoint : Prop :=
  ∀ (F : Type) [Field F] [Algebra Qj F] [FiniteDimensional Qj F],
    ConstantFieldIsQ F →
    ∃ X : Over SpecQ, IsCurve X ∧ ∃ (_ : IsIntegral X.left), Nonempty (X.left.functionField ≃+* F)
```

(the field minus one conjunct; strictly weaker).

**2.2 The rest, reduced to three textbook facts** (`CurveSplit.lean`, VERIFIED compiled). With
`IsNormalScheme X := ∀ x, IsIntegrallyClosed (X.presheaf.stalk x)` (Mathlib 4.35 has no normal schemes):

```lean
def NormalModelOfFunctionFieldQ : Prop :=          -- (A)
  ∀ (F : Type) [Field F] [Algebra Qj F] [FiniteDimensional Qj F],
    ∃ X : Over SpecQ, IsProper X.hom ∧ ∃ (_ : IsIntegral X.left), IsNormalScheme X.left ∧
      topologicalKrullDim X.left = 1 ∧ Nonempty (X.left.functionField ≃+* F)
def NormalCurveSmoothQ : Prop :=                   -- (B)
  ∀ (X : Over SpecQ), LocallyOfFiniteType X.hom → ∀ (_ : IsIntegral X.left), IsNormalScheme X.left →
    topologicalKrullDim X.left = 1 → SmoothOfRelativeDimension 1 X.hom
def GeomConnectedOfConstantFieldQ : Prop :=        -- (C)
  ∀ (X : Over SpecQ), IsProper X.hom → ∀ (_ : IsIntegral X.left), IsNormalScheme X.left →
    ∀ (F : Type) [Field F] [Algebra Qj F], ConstantFieldIsQ F →
      Nonempty (X.left.functionField ≃+* F) → GeometricallyConnected X.hom
```

Sources (STANDARD; all locators UNVERIFIED):
- (A) the normalization of `ℙ¹_ℚ` in `F`, finite over `ℙ¹_ℚ` since `F/ℚ(T)` is finite separable: Stacks,
  *Algebraic Curves*, section "Curves and function fields" (Tag 0BXX); Hartshorne I.6.7-6.9, II.6.7.
- (B) one-dimensional normal noetherian local domains are DVRs (Atiyah–Macdonald Prop. 9.2), so `X` is regular;
  regular and locally of finite type over a perfect field implies smooth, of relative dimension the local
  dimension (Stacks 00TV; for curves Lemma 0B8X).
- (C) `Γ(X, 𝒪_X)` is a finite-dimensional `ℚ`-algebra and a domain inside `K(X) ≅ F`, so it is algebraic over
  `ℚ`, so it is `ℚ` by `ConstantFieldIsQ`; a proper scheme over `k` with `Γ(X, 𝒪_X) = k` is geometrically
  connected (Stacks 0FD1; EGA III 4.3 via Stein factorization).

Each of (A), (B), (C) is true as stated (SPECULATIVE only in the sense that no source was read here; the
arguments above are complete modulo the cited facts), and each is strictly smaller than the field. (B) and (C)
are statements about all schemes of a kind, not about `K_N`; they are candidates for a Mathlib-level proof
later (Mathlib 4.35 lacks: normal schemes, regular ⇒ smooth, Stein factorization).
Under frontier's strict rule (frontier.md, H-40: the field is "GLUE (consequence)"), (A) is the printed
statement of the Stacks section (LEAF); (B) and (C) are composites of two printed facts each (lit-composite).

The glue `curveOfFunctionFieldQNoPoint_of_split` is only bookkeeping (`IsProper ⇒ LocallyOfFiniteType` is a
Mathlib instance); `curveOfFunctionFieldQ_of_split` composes it with §2.1.

## 3. t34: `LeafModCurves.DimJ1Genus`

**The field** (`Leaves.lean`): for `N ≥ 1` and `J` with `IsJ1 N J` (a Jacobian of some model of `X₁(N)`
over `ℚ`), `∃ g : ℕ, J.dim = g ∧ (g : ℚ) = genus (Gamma1 N)`, `genus` being the combinatorial
`1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` of `Genus.lean`. Its docstring cites three facts; frontier.md (H-37) classes it
GLUE (citation chain).

**The split** (`GenusSplit.lean`, VERIFIED compiled). The genus of a function field over `ℚ`, in Mathlib terms:

```lean
def regularAt (F : Type) [Field F] [Algebra ℚ F] (w : ValuationSubring F) : AddSubgroup (Ω[F⁄ℚ]) :=
  AddSubgroup.closure {ω | ∃ a b : F, a ∈ w ∧ b ∈ w ∧ ω = a • KaehlerDifferential.D ℚ F b}
def holoDiff (F : Type) [Field F] [Algebra ℚ F] : Submodule ℚ (Ω[F⁄ℚ]) :=
  Submodule.span ℚ {ω | ∀ w : ValuationSubring F, (∀ c : ℚ, algebraMap ℚ F c ∈ w) →
    ω ∈ regularAt F w}
def fieldGenus (F : Type) [Field F] [Algebra ℚ F] : ℕ := Module.finrank ℚ (holoDiff F)

def DimJacobianEqGenus : Prop :=
  ∀ (X : Over SpecQ) (_ : IsCurve X) (P₀ : RatPt X) (J : PkgI3.AbVar ℚ) (aj : X ⟶ J.X),
    IsJacobian X P₀ J aj → ∀ (_ : IsIntegral X.left) (F : Type) [Field F] [Algebra ℚ F],
      Nonempty (X.left.functionField ≃+* F) → J.dim = ((fieldGenus F : ℕ) : WithBot ℕ∞)
def GenusX1Field : Prop :=
  ∀ (N : ℕ) (P : EjBar.toAffine.Point), 0 < N → addOrderOf P = N →
    ((fieldGenus (fieldX1 P) : ℕ) : ℚ) = genus (CongruenceSubgroup.Gamma1 N)
```

`dimJ1Genus_of_split : DimJacobianEqGenus → GenusX1Field → DimJ1Genus` (proved; `g := fieldGenus (fieldX1 P)`
for the `P` of the model; no transport is needed because `DimJacobianEqGenus` quantifies over every field
isomorphic to `K(X)`).

**Why `fieldGenus` is the genus** (STANDARD; locators UNVERIFIED). For `F` the function field of a smooth proper
geometrically connected curve `X/ℚ`: the valuation subrings of `F` containing `ℚ` are `F` and the local rings
`𝒪_{X,x}` of the closed points (Abhyankar's inequality: a valuation of `F/ℚ` is trivial or discrete of rank 1;
the valuative criterion centres it on `X`). For such `w = 𝒪_{X,x}`, a localization of a smooth `ℚ`-algebra,
`Ω_{w/ℚ}` is free of rank 1 and its image in `Ω_{F/ℚ}` is the `w`-span of the `db`, `b ∈ w`, i.e. `regularAt F w`.
So the set spanned in `holoDiff` is `H⁰(X, Ω¹_{X/ℚ})` (it is already a `ℚ`-subspace), and `fieldGenus F =
dim H⁰(X, Ω¹) = g(X)`, finite. If the space were infinite-dimensional `finrank` would be 0, so finiteness matters:
it holds because `H⁰` of a coherent sheaf on a proper scheme is finite-dimensional (Hartshorne II.5.19).
- `DimJacobianEqGenus`: Milne, *Jacobian varieties* (Arithmetic Geometry, Cornell–Silverman eds., 1986),
  Prop. 2.1 (`T₀J ≅ H¹(X, 𝒪_X)`, so `dim J = g`), for the Jacobian of Thm 1.1, which has the Albanese property
  of `IsJacobian` (Prop. 6.1) and so is unique (`IsJacobian.unique`); `dim H¹(𝒪_X) = dim H⁰(Ω¹)` (Serre
  duality, Hartshorne III.7.12). A curve-theory fact about all curves over `ℚ`; nothing about `X₁(N)`.
- `GenusX1Field`: `K_N` is `ℚ`-isomorphic to the function field `ℚ(j, f_{(0,1/N)})` of Shimura's canonical model
  of `X₁(N)` (Shimura 1971 §6.7, Prop. 6.9), whose complex points are `Γ₁(N)\ℍ*`, of genus
  `1 + μ/12 − ν₂/4 − ν₃/3 − ν∞/2` (Shimura 1971 Prop. 1.40); the genus does not change under `ℚ → ℂ` (flat base
  change of `H⁰(Ω¹)`). A fact about the single field `K_N`; it could also be proved from the Belyi data
  (`j : X₁(N) → ℙ¹` ramified only over `0, 1728, ∞` with the `ST`-, `S`-, `T`-orbit structure) by
  Riemann–Hurwitz, which Mathlib does not have.

The combinatorial `genus` agrees with the closed forms for `X₁(N)`, `N ≤ 30` (bp-modcurves' `genus_check.py`,
re-run here: 30/30 `ok`, `scratch/curves-g/genus_check_out.txt`, VERIFIED computed).

**What the chain uses.** Every use of `t34` in leaf-fold3's flat file goes through `LeafModCurves.dim_J1_le`
(`dim J₁(N) ≤ N²`): Leaves3.lean lines 16897, 33861, 34333, 71883 (VERIFIED by grep). See §6.

## 4. t33: `LeafModCurves.JacobianExists ℚ`

**The field** (`Defs.lean`, leaf MC6'):

```lean
def JacobianExists (K : Type) [Field K] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of K))) (_ : IsCurve X)
    (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X),
    ∃ (J : AbVar K) (aj : X ⟶ J.X), IsJacobian X P₀ J aj
```

with `IsJacobian X P₀ J aj`: `P₀ ≫ aj = η[J.X]`, and every `K`-morphism `f : X ⟶ A.X` to an abelian variety
with `P₀ ≫ f = η[A.X]` factors as `aj ≫ φ` for a unique homomorphism `φ` (`IsMonHom`).

**Published statement** (STANDARD; numbers UNVERIFIED): Milne, *Jacobian varieties*, in Cornell–Silverman
(eds.), *Arithmetic Geometry* (Springer 1986), Thm 1.1 (for a complete nonsingular curve `C` over `k` with
`C(k) ≠ ∅`, the functor `P⁰_C` is represented by an abelian variety `J`) and Prop. 6.1 (for `P ∈ C(k)`, the map
`f^P : C → J` has the universal property: every morphism `φ : C → A` to an abelian variety with `φ(P) = 0` is
`ψ ∘ f^P` for a unique homomorphism `ψ`). Weil (1948) over an algebraically closed field; Chow, Amer. J. Math.
77 (1955), over any field.

**Not stronger** (checked against the definitions, VERIFIED read):
- `IsCurve X` = proper + `SmoothOfRelativeDimension 1` + `GeometricallyConnected`; smooth and connected imply
  integral, so `X` is a complete nonsingular geometrically integral curve, Milne's hypothesis; `P₀` is the
  `k`-point.
- `AbVar K` (`ZInQKernel/HDecomp/Objects.lean`) is a group object, proper, smooth and geometrically integral
  over `Spec K`: Milne's abelian varieties, including dimension 0 (needed for genus 0, where `J = Spec K`).
- The universal property asks uniqueness of `φ` among homomorphisms only, which is Milne's statement (any
  morphism `J → A` sending `0 ↦ 0` is a homomorphism, rigidity, so this is not weaker either).
- Morphisms are those of `Over (Spec K)`, i.e. `K`-morphisms, as in Milne.
- It is used at `K = ℚ` only.

**Not provable here**: the construction of `J` (symmetric powers, or representability of `Pic⁰`) is far beyond
Mathlib 4.35 (no Picard functor, no symmetric powers of schemes, no line bundles on curves). Tau Ceti has no
Jacobians (tc-survey: T33 not found). frontier.md classes it **LEAF** (H-36), which this review confirms.

## 5. Checks

**Kernel modules** (VERIFIED): `lake build ZInQKernel.Contrib.CurvesG.RatPoint` (27 s), `.GenusSplit`, `.CurveSplit`
(26 s): 0 errors, no `sorry`. Each imports only kernel modules (`ZInQKernel.HDecomp.ModCurves.X1Belyi` resp.
`.Leaves`) and Mathlib. `scratch/curves-g/AxiomsContrib.lean`: exit 0, axioms as in §1.

**Single-file check** (VERIFIED): `python3 scratch/curves-g/assemble.py` writes `scratch/curves-g/part_g3.lean`
(306 lines: the bodies of the three Contrib files, verbatim, in `namespace HDec.CurvesG3` so that
`LeafModCurves`, `X1Belyi`, `PkgI3` resolve to the flat file's copies, which Lean's "Ambiguous namespace" warnings
confirm; the field lines of leaf-fold3's `OpenTextbookLeaves3`, verbatim from `partsF/d90_fold3.lean`, with `t34`,
`t38` replaced; `textbookLeaves3_of_G`, `sixContactMin_of_openG`) and `scratch/curves-g/CurvesG3.lean` =
leaf-fold3's `Leaves3.lean` (md5 703c1618…, unchanged) + the part (111 132 lines; regenerated, not committed).
`lake env lean scratch/curves-g/CurvesG3.lean`: **exit 0, 0 errors, no `sorry`, 17 min 17 s, max RSS 15.5 GB**
(close to the 16 GB cap). All 295 `#print axioms` reports read `[propext, Classical.choice, Quot.sound]` (290 on one
line, 5 line-wrapped, all in leaf-fold3's text). The part's seven:
`HDec.CurvesG3.nonempty_ratPt_of_place`, `.curveOfFunctionFieldQ_of_noPoint`,
`.curveOfFunctionFieldQNoPoint_of_split`, `.curveOfFunctionFieldQ_of_split`, `.dimJ1Genus_of_split`,
`HDec.HSyn.textbookLeaves3_of_G`, `HDec.HSyn.sixContactMin_of_openG`. The part also compiles
`example : ∀ (_ : OpenResearchLeaves2) (_ : OpenTextbookLeavesG) (_ : OpenAddedLeaves3) (_ : OpenGlue3),
_root_.ZInQ.SixContactMin := HDec.HSyn.sixContactMin_of_openG` (the kernel's `SixContactMin`), and `example`s whose
types are the flat file's own `X1Belyi.CurveOfFunctionFieldQ` and `LeafModCurves.DimJ1Genus` (the bundle's field
types), so the proved Props are the fields themselves.

```lean
theorem HDec.HSyn.sixContactMin_of_openG (r : OpenResearchLeaves2) (t : OpenTextbookLeavesG)
    (l : OpenAddedLeaves3) (g : OpenGlue3) : ZInQ.SixContactMin
```

An earlier run (with T38 only weakened to `CurveOfFunctionFieldQNoPoint`) failed only on the final root `example`
(binder types not inferable); fixed (log.md).

**Verbatim** (VERIFIED, `python3 scratch/curves-g/py/verbatim_check.py`, output `py/verbatim_check_out.txt`): the
code (docstring stripped) of 26 declarations, the three field Props and every definition they use, occurs verbatim
in `Leaves3.lean` in the kernel owners' text: ALL VERBATIM (the docstrings of `Ej` and `DimJ1Genus` differ). So
the kernel-level theorems (`ZInQKernel/Contrib/CurvesG/`) and the flat-file theorems prove the same text.

**Genus formula** (VERIFIED computed): bp-modcurves' `genus_check.py`, 30/30 `ok` for `N ≤ 30`.

**Licence**: no Tau Ceti file vendored or changed; `diffcheck2.py`: MOD-UNNOTED 0, NOTE-ONLY 0.

## 6. Proposals (not applied)

1. **T34 is stronger than the chain needs** (VERIFIED by grep, §3): every consumer uses only `dim J₁(N) ≤ N²`.
   Proposed replacement for the field `t34` (the conclusion of the kernel's `LeafModCurves.dim_J1_le`, so
   `dim_J1_le h` proves it from the present field):
   ```lean
   def DimJ1LeSq : Prop :=
     ∀ (N : ℕ) (J : AbVar ℚ), 0 < N → IsJ1 N J → ∃ g : ℕ, J.dim = (g : WithBot ℕ∞) ∧ g ≤ N ^ 2
   ```
   With the split of §3 the matching weakening of `GenusX1Field` is
   `∀ N P, 0 < N → addOrderOf P = N → fieldGenus (fieldX1 P) ≤ N ^ 2`. This changes no proof difficulty
   (the bound still needs the genus formula or Riemann–Hurwitz), only the size of what is assumed. Not applied.
2. No statement of t33, t34 or t38 is wrong; no other change proposed.
