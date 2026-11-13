# curve-infra: dimension equals transcendence degree, proved in general

Task curve-infra, 2026-11-13. Base 6f296292 (wip/integrate-w42). Scratch: `scratch/curve-infra/`
(results log `log.md`). No file under `ZInQKernel/`, `blueprint/` or another task's directory was
edited. This is model work only; no human has reviewed it.

Marks: **VERIFIED** means compiled, computed, or read in a file. **STANDARD** means published, with
a reference. **UNVERIFIED** means a theorem number recalled without a source (there is no network
here).

## 1. Result

**Scope.** image-plane's proof needs none of (AD), (IC) or (L0).

- image-plane's `ImagePlaneFinal.lean` proves (IC) `ImageClosed` and (AD) `AlgDep` as theorems
  with standard axioms.
- It proves C2K without (L0) `FiniteGlobalSections`. Its report says (L0) is used by no theorem
  of its §1 (VERIFIED: read in `docs/research/image-plane.md` §1 and §7).
- So, as the task instructs, I proved (AD) in general.

**Main theorem: dimension equals transcendence degree.** Let `X` be an integral scheme, locally of
finite type over a field `K`. Then `dim X = trdeg_K K(X)`. This is proved in Lean from Mathlib
alone, with no hypotheses and no leaf.

`scratch/curve-infra/CurveInfraAll.lean` compiles with 0 errors (VERIFIED,
`run_CurveInfraAll.txt`). All eight theorems have axioms `[propext, Classical.choice, Quot.sound]`.

```lean
-- K(X) is a K-algebra via K ≅ Γ(Spec K, ⊤) → Γ(X, ⊤) → K(X)
noncomputable abbrev fnFieldAlgebra (K : Type u) [Field K] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) : Algebra K X.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop ≫ X.germToFunctionField ⊤).hom.toAlgebra

def DimEqTrdeg : Prop :=
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f],
    letI := fnFieldAlgebra K X f
    topologicalKrullDim X = ((Algebra.trdeg K X.functionField).toENat : WithBot ℕ∞)
theorem CurveInfra.dimEqTrdeg : DimEqTrdeg
-- universe-polymorphic form: CurveInfra.dim_eq_trdeg

def DimEqTrdegAlg : Prop :=          -- R a domain of finite type over K: dim R = trdeg_K Frac R
  ∀ (K R : Type) [Field K] [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R],
    ringKrullDim R = ((Algebra.trdeg K (FractionRing R)).toENat : WithBot ℕ∞)
theorem CurveInfra.dimEqTrdegAlg : DimEqTrdegAlg

def AlgDepOfTrdegOne : Prop :=       -- two elements of a field of trdeg 1 are algebraically dependent
  ∀ (K F : Type) [Field K] [Field F] [Algebra K F], Algebra.trdeg K F = 1 →
    ∀ a b : F, ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0
theorem CurveInfra.algDepOfTrdegOne : AlgDepOfTrdegOne

def SmoothTrdeg : Prop :=            -- X integral, smooth of relative dimension n over K: trdeg_K K(X) = n
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    (n : ℕ) [SmoothOfRelativeDimension n f],
    letI := fnFieldAlgebra K X f
    Algebra.trdeg K X.functionField = n
theorem CurveInfra.smoothTrdeg : SmoothTrdeg

def CurveFnFieldAlgDep : Prop :=     -- (AD) on function fields: any two rational functions on a smooth curve
  ∀ (K : Type) [Field K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [SmoothOfRelativeDimension 1 f],
    letI := fnFieldAlgebra K X f
    ∀ a b : X.functionField, ∃ P : MvPolynomial (Fin 2) K, P ≠ 0 ∧ MvPolynomial.aeval ![a, b] P = 0
theorem CurveInfra.curveFnFieldAlgDep : CurveFnFieldAlgDep

-- the same over the kernel's K-algebra structure ZInQ.LeafPush2.ffAlgebra (HDecomp/LeafPush2/R18.lean)
def DimEqTrdegOver : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom],
    letI := ZInQ.LeafPush2.ffAlgebra X
    topologicalKrullDim X.left = ((Algebra.trdeg K X.left.functionField).toENat : WithBot ℕ∞)
def SmoothTrdegOver : Prop :=        -- n-dimensional smooth: trdeg = n, with ffAlgebra
def CurveAlgOverTranscendental : Prop :=
  ∀ (K : Type) [Field K] (X : Over (Spec (CommRingCat.of K))) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom],
    letI := ZInQ.LeafPush2.ffAlgebra X
    ∀ x : X.left.functionField, Transcendental K x →
      Algebra.IsAlgebraic (Algebra.adjoin K {x}) X.left.functionField
theorem CurveInfra.dimEqTrdegOver, CurveInfra.smoothTrdegOver, CurveInfra.curveAlgOverTranscendental
```

**Classification.** All of these are glue, and now proved.

- **Sources** (STANDARD; numbering UNVERIFIED):
  - Hartshorne, *Algebraic Geometry*, I Prop. 1.7, Thm. 1.8A and Ex. II.3.20;
  - the Stacks Project, *Commutative Algebra*, section "Dimension of finite type algebras over
    fields".
- **The one deep input** is Noether normalization. Mathlib provides it as
  `exists_finite_inj_algHom_of_fg`, tagged Stacks 00OW (VERIFIED: g0-dim's report).
- **`DimEqTrdegOver` matches the kernel.** Its algebra structure is the kernel's own `ffAlgebra`.
  The proof is `dim_eq_trdeg K X.left X.hom`, and it is accepted with no conversion: the two
  algebra structures agree definitionally.

**No statement was changed.** These are new statements; no existing Prop was restated. The
copied code is textually identical to its sources; the check is `py/verbatim.py`, output
`verbatim.txt`, ALL OK (VERIFIED).

## 2. Proofs

**Algebra** (`exists_dim_eq_trdeg`). Let `R` be a domain of finite type over `K`, with `K` and `R`
in the same universe.

1. **Noether normalization** gives `g : K[X_1..X_s] → R`, finite and injective.
2. **Dimension.** `dim R = dim K[X_1..X_s] = s`.
   - This uses g0-dim's `ringKrullDim_eq_of_isIntegral_of_injective` (going up and
     incomparability) and Mathlib's `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`.
3. **Transcendence degree.** `trdeg_K R = trdeg_K K[X] + trdeg_{K[X]} R = s + 0`.
   - The tower law is Mathlib's `trdeg_add_eq` (Stacks 030H).
   - `trdeg_K K[X] = s` is `MvPolynomial.trdeg_of_isDomain`.
   - `trdeg_{K[X]} R = 0` holds because `R` is integral over `K[X]`, hence algebraic over it
     (`trdeg_eq_zero`).
4. **Fraction field** (`trdeg_eq_of_isLocalization`). `trdeg_K Frac(R) = trdeg_K R`, by the tower
   law and `IsLocalization.isAlgebraic`.

**Schemes** (`dim_affineOpen_eq_trdeg`, `dim_eq_trdeg`).

1. **Finite type.** For a nonempty affine open `U`, `Γ(X, U)` is a domain of finite type over `K`.
   - This uses `HasRingHomProperty.appLE` for `LocallyOfFiniteType`, composed with the
     isomorphism `K ≅ Γ(Spec K, ⊤)`.
2. **Function field.** `K(X) = Frac Γ(X, U)`, by Mathlib's
   `functionField_isFractionRing_of_isAffineOpen`.
   - The `K`-structures are compatible (`IsScalarTower`), by `germ_res`.
3. **Dimension of `U`.** `dim U = dim Spec Γ(X, U) = dim Γ(X, U)`, so `dim U = trdeg_K K(X)` for
   every such `U`.
4. **Dimension of `X`.** `dim X` is the supremum of `dim U` over the cover by nonempty affine
   opens. This is g0-dim's `topologicalKrullDim_eq_iSup_of_openEmbedding`.

**Corollaries.**

- **`SmoothTrdeg`** combines `dim_eq_trdeg` with infra-smooth-dim's
  `topologicalKrullDim_eq_of_smoothOfRelativeDimension` (`dim X = n` for irreducible smooth `X`).
  `trdeg` is finite here, so `Cardinal.toENat_eq_natCast` applies.
- **`AlgDepOfTrdegOne`.** If `![a, b]` were algebraically independent, then
  `2 = #(Fin 2) ≤ trdeg = 1` (`AlgebraicIndependent.cardinalMk_le_trdeg`), which is false. So
  `aeval ![a, b]` is not injective (`algebraicIndependent_iff_injective_aeval`).
- **`CurveAlgOverTranscendental`.** `![x]` is algebraically independent and has `1 ≥ trdeg`
  elements, so it is a transcendence basis (`isTranscendenceBasis_of_trdeg_le_of_finite`). Hence
  `K(X)` is algebraic over `K[x]` (`IsTranscendenceBasis.isAlgebraic`).

## 3. Who uses this

- **curve-glue §6 and §8** name exactly this missing theorem: "the Krull dimension of a finitely
  generated `K`-domain equals the transcendence degree of its fraction field".
  - Its (AD) `AlgDep` is now proved by image-plane by another route.
  - `CurveFnFieldAlgDep` is the function-field form of the same fact, now proved directly.
- **curve-facts §5 (Mathlib survey)** lists "curves as a notion, with function fields of transcendence degree 1" as
  missing infrastructure. `SmoothTrdeg` / `SmoothTrdegOver` with `n = 1` supply it.
- **Kernel definitions over `ffAlgebra`.**
  - `ZInQ.LeafPush2.HasSexticModel` (`HDecomp/LeafPush2/R3.lean`) asks for a transcendental `x`.
    `CurveAlgOverTranscendental` shows that any such `x` makes `K(X)` algebraic over `K(x)`.
  - The Belyi statements of R18 (`Module.finrank (adjoin K {t}) K(X) = d`) concern the same
    extension.
  - `DimEqTrdegOver` and `SmoothTrdegOver` are stated over that same `ffAlgebra`, so they apply
    to these definitions with no conversion.

## 4. Files and verification

All runs used `lake env lean` on one file, one Lean process at a time. The kernel module
`ZInQKernel.HDecomp.LeafPush2.R18` was built with `lake build` for the import.

| file | content | outcome (VERIFIED) |
|---|---|---|
| `Alg.lean` | algebra: `exists_dim_eq_trdeg`, `trdeg_eq_of_isLocalization` (Mathlib only) | 0 errors, 0 warnings |
| `Dim.lean` | `Alg.lean` plus the scheme part plus `DimEqTrdeg`, `DimEqTrdegAlg`, `AlgDepOfTrdegOne` (Mathlib only) | 0 errors, 0 warnings, standard axioms, `run_Dim.txt` |
| `CurveInfraAll.lean` (`mk_all.sh`) | infra-smooth-dim's `SmoothStalk.lean` lines 2-526 verbatim, then `Dim.lean`, then `tail_part.lean.part` (smooth and kernel-`ffAlgebra` forms) | 0 errors, standard axioms for all 8 theorems, `run_CurveInfraAll.txt`; one unused-variable linter warning, in the copied infra-smooth-dim code |
| `py/verbatim.py`, `verbatim.txt` | copied code matches g0-dim's `part_dim.lean` and infra-smooth-dim's `SmoothStalk.lean` | ALL OK |

## 5. What remains

- **Nothing for (AD), (IC) or (L0) in the image-plane chain.** image-plane closed (IC) and (AD)
  and removed (L0).
- **(L0) `FiniteGlobalSections`** (EGA III 3.2.1) was not attempted, since no proof uses it any
  more. It stays an unused textbook leaf.
- **Integration.** The file depends only on Mathlib, infra-smooth-dim's `SmoothStalk` and the
  kernel's `R18` (for `ffAlgebra`). `Dim.lean` alone is Mathlib-only and could become a kernel
  module as it stands.
