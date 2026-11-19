import ZInQKernel.Contrib.RC53Assist.CentralKummer.RationalKummer

/-!
# The Tate module of the rational Kummer complex is the inverse limit `TateS`

The ordinary compact and rational Kummer complexes `compactKummerComplex S W hFull` and
`rationalKummerComplex S W hFull` are built directly on the genuine inverse limit
`TateS K S W = lim_n E(K_S)[2^n]` of the coefficient-module development (compatible sequences
under `P ↦ 2P`, with its `ℤ₂`-module structure, its Galois action and its inverse-limit topology
`tateTop`). No second model of `T₂E` occurs. This file records that identification explicitly.

* `tateKummerSelData_eq`, `compactKummerComplex_eq`, `rationalKummerComplex_eq`: the Selmer data
  are `galoisSelData K S ℤ₂ (TateS K S W) Δ` for the `2`-adic Kummer conditions `Δ`, and the
  complexes are their Selmer complex and its rationalization.
* `topology_tateS`: the topology used on the coefficients is `tateTop`.
* `tateComparison`: the comparison of the coefficient module of the complex with `TateS` is the
  identity `ℤ₂`-linear equivalence; it is Galois equivariant (`tateComparison_smul`), continuous
  (`continuous_tateComparison`) and compatible with the projections `projLev n` to `E(K_S)[2^n]`
  (`projLev_tateComparison`).
* `rationalKummerComplexIso`: the induced identification of the rational Kummer complex with the
  complex built on `TateS` (the identity isomorphism).
* `projLev_tateKummerFunOf`: the level-`n` coordinate of every value of a `2`-adic Kummer cocycle,
  read by `projLev n`, is the finite-level Kummer difference `σ R n − R n` transported to
  `E(K_S)[2^n]` by the inverse of the decomposition comparison.
-/

noncomputable section

namespace ZInQ.Manuscript.RC53Assist.CentralKummer

open NumberField IsDedekindDomain CategoryTheory
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
  ZInQ.Manuscript.RC.LambdaCoef ZInQ.Contrib.CloudB3RC53.PairedFunctional

section Complex

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (W : WeierstrassCurve K) [W.IsElliptic] (hFull : ∀ n : ℕ, FullTorsion K S W (2 ^ n))

/-- **The compact Kummer Selmer data are Galois Selmer data for the module `TateS K S W`.** -/
theorem tateKummerSelData_eq :
    tateKummerSelData S W hFull =
      galoisSelData K S ℤ_[2] (TateS K S W) (tateKummerLocalConditions S W hFull) :=
  rfl

/-- **The ordinary compact Kummer complex is the Selmer complex of those data.** -/
theorem compactKummerComplex_eq :
    compactKummerComplex S W hFull =
      (selCx (galoisSelData K S ℤ_[2] (TateS K S W) (tateKummerLocalConditions S W hFull))).toCC :=
  rfl

/-- **The ordinary rational Kummer complex is its rationalization along `ℤ₂ → ℚ₂`.** -/
theorem rationalKummerComplex_eq :
    rationalKummerComplex S W hFull =
      ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex PadicInt.Coe.ringHom
        (selCx (galoisSelData K S ℤ_[2] (TateS K S W)
          (tateKummerLocalConditions S W hFull))).toCC :=
  rfl

/-- **The induced identification of the rational Kummer complex with the complex built on
`TateS`** (the identity isomorphism). -/
def rationalKummerComplexIso :
    rationalKummerComplex S W hFull ≅
      ZInQ.Manuscript.RC53Assist.CentralSelmer.scalarChangedComplex PadicInt.Coe.ringHom
        (selCx (galoisSelData K S ℤ_[2] (TateS K S W)
          (tateKummerLocalConditions S W hFull))).toCC :=
  Iso.refl _

/-- **The levels of the `2`-adic Kummer cocycles in `TateS`**: the `projLev n`-coordinate of the
value at `σ` is the finite-level Kummer difference of the tower, transported to `E(K_S)[2^n]` by
the inverse of the decomposition comparison. -/
theorem projLev_tateKummerFunOf (v : HeightOneSpectrum (𝓞 K)) [DecidableEq (v.adicCompletion K)]
    {P : (W.baseChange (v.adicCompletion K)).toAffine.Point}
    {R : ℕ → PtAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K))}
    (h : IsDivTower _ _ P R) (σ : Gloc K v) (n : ℕ) :
    projLev n (tateKummerFunOf (S := S) W hFull v h σ) =
      (compTorsEquiv W (2 ^ n) (hFull n) v).symm (towerKummerOf h n σ) :=
  rfl

end Complex

section Comparison

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-- The topology used on the coefficients is the inverse-limit topology `tateTop`. -/
theorem topology_tateS :
    (inferInstance : TopologicalSpace (TateS K S W)) = tateTop :=
  rfl

/-- **The comparison of the coefficient module with `TateS`**: the identity `ℤ₂`-linear
equivalence of `TateS K S W`. -/
def tateComparison : TateS K S W ≃ₗ[ℤ_[2]] TateS K S W :=
  LinearEquiv.refl ℤ_[2] (TateS K S W)

/-- The comparison is Galois equivariant. -/
theorem tateComparison_smul (σ : GKS K S) (P : TateS K S W) :
    tateComparison (σ • P) = σ • tateComparison P :=
  rfl

/-- The comparison is compatible with the projections `TateS → E(K_S)[2^n]`. -/
theorem projLev_tateComparison (n : ℕ) (P : TateS K S W) :
    projLev n (tateComparison P) = projLev n P :=
  rfl

/-- The comparison is continuous. -/
theorem continuous_tateComparison : Continuous (tateComparison (K := K) (S := S) (W := W)) :=
  continuous_id

end Comparison

end ZInQ.Manuscript.RC53Assist.CentralKummer
