# coarse-factor: `CoarseFactor` (qm-glue (d)) is proved from the leaf-forms already in use

## 1. Result

**Verdict.** The glue Prop `CoarseFactor` (`scratch/qm-glue/ModuliCompare.lean`, copied verbatim) is
**proved** from the leaf-form `CanonicalCoarseX6`, and also from the bundle leaf `R1R2fpRep`. Each of these is
already a hypothesis of the qm-glue theorem that consumes `CoarseFactor`. No new leaf is needed. Together with
curve-split's `CurveBijIso` (proved, no hypotheses), the moduli rows H-1 and H-43 no longer depend on
`CoarseFactor` or `CurveBijIso`. All results COMPILED, with only the axioms `propext`, `Classical.choice`
and `Quot.sound` (VERIFIED by `#print axioms`):

| theorem (namespace `HDec.QMSplit.Moduli` unless noted) | statement |
|---|---|
| `CoarseFactorAG.factorThroughSurj` | `FactorThroughSurj` (AG glue, §2), no hypotheses |
| `coarseFactor_of` | `PairsLift → FactorThroughSurj → CoarseFactor` |
| `pairsLift_of_canonical`, `pairsLift_of_rep` | `CanonicalCoarseX6 → PairsLift`, `R1R2fpRep → PairsLift` |
| `coarseFactor_of_canonical'`, `coarseFactor_of_rep'` | `CanonicalCoarseX6 → CoarseFactor`, `R1R2fpRep → CoarseFactor` |
| `coarseCompare_of_canonical` | `CanonicalCoarseX6 → CoarseCompare` |
| `r1r2fpRep_of_canonical''` (row H-1) | `CanonicalModelY3 → CanonicalCoarseX6 → BabaGranathX6 → GonzalezRotgerX6 → ReciprocityOfFine → R1R2fpRep` |
| `x6ConicModel_of_canonical''` (row H-43) | `R1R2fpRep → ConicCanonical → Pin.MobiusGlue → X6ConicModel` |

The last two are qm-glue's `r1r2fpRep_of_canonical` and `x6ConicModel_of_canonical'` with the arguments
`hF : CoarseFactor` and `hCB : CurveBijIso` filled in.

## 2. The split

**Finding (VERIFIED, by reading the definitions).** `X6Props Y Φ X Ψ fY` does not say that `fY` is onto
`X(ℚ̄)`. Without that, `CoarseFactor` can fail: a component of `X` that `fY` misses is constrained only by
Galois equivariance. Surjectivity holds once every QM pair over `ℚ̄` carries a level-3 structure. That is
published mathematics (`A[3]` is free of rank one over `𝒪/3𝒪`), but it cannot be proved in Lean today.
It is, however, a consequence of the leaf-forms already in use, so it is stated as a derived Prop:

* `PairsLift : ∀ Q : QMPair ℚ̄, ∃ P : QML3 ℚ̄, [P.forget] = [Q]`. This is **not a new leaf**. It follows
  from any coarse witness whose forgetful map is onto `X(ℚ̄)` (`pairsLift_of_witness`), and such a witness is
  given by `CanonicalCoarseX6` and by `R1R2fpRep` (clause `X6Surj`).
* `FactorThroughSurj` (GLUE, now proved). Let `Y`, `X`, `X'` be proper smooth curves over `ℚ` (smooth of
  relative dimension 1). Let `f : Y → X` be onto on `ℚ̄`-points, and let `f' : Y → X'` be constant on the
  `ℚ̄`-fibres of `f`. Then `f' = f ≫ h` for some `h : X → X'`.

`coarseFactor_of` derives `CoarseFactor` from these two Props as follows:
* Take `θ = Ψ'⁻¹ ∘ Ψ`. Both `fY` and `fY'` send `y` to the class of `P.forget`, so `f'` is constant on the
  fibres of `fY`.
* `PairsLift` together with the surjectivity of `Φ` gives that `fY` is onto `X(ℚ̄)`.
* The compatibility `Ψ'(x ≫ h) = Ψ x` then follows by writing `x = y ≫ fY`.

## 3. Proof of `FactorThroughSurj` (scratch/coarse-factor/Factor.lean)

Notation: `P = X ×_ℚ X'`, `g = (f, f') : Y → P`. Let `Z` be the scheme-theoretic image of `g` (Mathlib
`Scheme.Hom.image`), `t : Y → Z`, `ι : Z → P` the closed immersion, and `p = ι ≫ pr₁ : Z → X`.

1. **`Z` is reduced** (`isReduced_image`). `t.app` is injective on the preimages of affine opens (Mathlib
   `toImage_app_injective`), and `Y` is reduced because it is smooth.
2. **`t` is surjective and locally of finite type.** It is proper with dense range.
3. **`ℚ̄`-points.**
   * Surjectivity of `p`: a `ℚ̄`-point of `X` lifts to `Y`, then maps to `Z`.
   * Injectivity of `p`: lift `a, b : Spec ℚ̄ → Z` along `t`. The lifting lemma `exists_lift_of_surjective`
     works through a closed point of the fibre product `Y ×_Z Spec ℚ̄` and Mathlib's `pointOfClosedPoint`.
     The two lifts have equal images under `f` (since `a ≫ p = b ≫ p`), so by hypothesis equal images
     under `f'`. Hence `a ≫ ι = b ≫ ι`, and `a = b` because `ι` is a monomorphism.
4. **Closed fibres of `p` are single points.**
   * Two closed points over the same point of `X` carry `ℚ̄`-points with the same image (`exists_lift_at`),
     so injectivity on `ℚ̄`-points identifies them.
   * Since `Z` is a Jacobson space, a closed fibre is the closure of its closed points, hence a single point.
5. **`p` is finite.** At each closed point `s`, the set `g(f⁻¹ s) ⊆ ι(p⁻¹ s)` is finite, so Mathlib's Stacks
   0AH8 (`exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage`) makes `p` finite over a
   neighbourhood of `s`. Every point of `X` specializes to a closed point, so these neighbourhoods cover `X`.
   `IsFinite` is local on the target (`isZariskiLocalAtTarget_isFinite`; the instance has to be given
   explicitly, type-class search does not find it).
6. **`p` is an isomorphism** (`isIso_of_points`). Cover `X` by nonempty affine opens `U` contained in
   irreducible components; these components are open (curve-split's `isOpen_irreducibleComponent`). On each
   `U`, apply `isIso_affine`, which rests on the algebraic lemma `bijective_of_points`:
   * Setting: `A` is a Dedekind domain of finite type over `ℚ`, `B` is a reduced finite `A`-algebra, and the
     map `Hom(B, ℚ̄) → Hom(A, ℚ̄)` is bijective. Conclusion: `A ≅ B`.
   * `A → B` is injective: its kernel lies in every maximal ideal, because every maximal ideal of `A` is the
     kernel of some map `A → ℚ̄` that lifts to `B`.
   * Over each maximal ideal of `A` there is exactly one maximal ideal of `B` (extend residue embeddings).
   * `B` is a domain: by going-up, a prime of `B` over `0` lies in every maximal ideal of `B`, so it lies in
     the Jacobson radical, which is `0` because `B` is reduced and Jacobson.
   * Some closed point of `B` is unramified over `A` (characteristic 0), and at it the residue degree is 1:
     the extension has at most one `κ(p)`-embedding into `ℚ̄`, and `AlgHom.card` equates the number of such
     embeddings with the degree.
   * Curve-split's `bijective_of_unramifiedAt` (a flatness and rank argument) concludes.
7. Finally, `h = p⁻¹ ≫ ι ≫ pr₂`, and `f ≫ h = t ≫ ι ≫ pr₂ = f'`.

Locators for the textbook statements this replaces (SGA 1 Exp. V Prop. 1.8; Mumford *Abelian varieties*
§7) are UNVERIFIED and no longer needed: the proof uses only Mathlib, the kernel (`ZInQKernel/Contrib/Dim`,
`Contrib/SmoothFibre`, `Contrib/CurvesG`, `Contrib/TauCeti`, `HDecomp/QM`) and copies of curve-split lemmas.

**The cloud-worker connectedness and spreading-out modules** (`Contrib/CloudW02Connectedness`,
`Contrib/CloudW01Spread`, `Contrib/SpreadOut`, `Contrib/ZariskiConn`) were checked. They supply no step:
nothing here needs connectedness, spreading out or Zariski connectedness. The proof works over `ℚ`
directly, with no base change except the fibre products used to lift points.

## 4. Files and checks

| file | content | check |
|---|---|---|
| `scratch/coarse-factor/Reduction.lean` | verbatim `CoarseFactor`, `CanonicalCoarseX6`; `PairsLift`, `FactorThroughSurj`; `coarseFactor_of`, `pairsLift_of_*` | `lake env lean`, 15 s |
| `scratch/coarse-factor/Factor.lean` | Part 1: `factorThroughSurj` and lemmas (imports kernel `QM.Pairs`, `CurvesG`, `Dim`, `SmoothFibre`) | `lake env lean`, 7 s |
| `scratch/coarse-factor/CoarseFactor.lean` | Reduction + Part 1 + curve-split `CurveBijIso` + `coarseCompare_of_canonical` (over `ZInQKernel.OneProof.H.LPrefix`) | `lake env lean`, 10 s |
| `scratch/coarse-factor/Discharge.lean` | `scratch/qm-glue/ModuliCompare.lean` verbatim (first import `TailK` → kernel `ZInQKernel.OneProof.H.TailK`) + all of the above; rows H-1, H-43 discharged | `lake env lean`, 51 s, 0 errors |

Verbatim checks (python substring tests, VERIFIED):
* `CoarseFactor` and `CanonicalCoarseX6` match the qm-glue text.
* The body of `ModuliCompare.lean` appears unchanged inside `Discharge.lean`.
* The `FactorThroughSurj` texts in the two namespaces are identical.

Changes to copied text:
* In `CoarseFactor.lean`, `open LeafQM.AV` is replaced by `open HDec.LeafQM.AV` in the copied curve-split
  parts. Under `LPrefix`/`TailK` the QM definitions live in `HDec.LeafQM.AV`.
* The section variables `[IsAlgClosed k] [CharZero k]` are dropped from the copy of
  `isDedekindDomain_sections`. Its proof does not use them.

Build note: `lean/.lake/build` (the upstream `ZInQ` package) was copied from `~/dzq-wt/leaf-fold7`, whose
`lean/ZInQ` sources are identical (VERIFIED by `diff -rq`). `ZInQKernel.Contrib.CurvesG.CurveSplit` and
`ZInQKernel.Contrib.SmoothFibre.Basic` were built with `lake build`.

## 5. What remains

Nothing remains for `CoarseFactor`. For the moduli rows:
* H-1 now rests on the existential published forms `CanonicalModelY3`, `CanonicalCoarseX6`,
  `BabaGranathX6`, `GonzalezRotgerX6` and the glue `ReciprocityOfFine`.
* H-43 now rests on `R1R2fpRep`, `ConicCanonical` and `MobiusGlue`. `MobiusGlue` is proved from T5 by
  image-plane.

Integration (not done, other tasks' files): replace `hF`, `hCB` in qm-glue's consumers with
`coarseFactor_of_canonical' hC` / `coarseFactor_of_rep' hR` and `CurveSplit.curveBijIso`.
