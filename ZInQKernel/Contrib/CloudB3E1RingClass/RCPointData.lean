import ZInQKernel.Contrib.CloudB3E1RingClass.RCPoint
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointCentral

/-!
# The ring-class point as the point of the calibration's retained point data

Manuscript `diophantine_zq.tex`, tex 2411–2416, 3071–3085, 3895–3907, 4005–4021.

Let `G` be the genuine Kummer data of an address: the support `S`, the curve `E_K`, `√h ∈ K_S`.
Lane RC34's `RetainedPointData G κ j vL` takes as fields:
* the point `P ∈ E^{(h)}(K)`, `E^{(h)} = centralCurve G = twistK E_K h`;
* the multiplier `L`;
* a free generator `gen`, with `P ≡ nP · gen` and `j = v₂ nP`;
* the Kummer and conjugate-dual inputs.

**`rcPoint G hS y hy hQ`** (definition) is `P^{rc}_{h,k}`. It descends to `centralCurve G` the
`χ_h`-weighted conductor-`f` trace of a point `y ∈ E(K_S)` fixed by the elements fixing `H_f`, under
lane E2's genus-theory condition `QuadOfDelta f` (`χ_h` trivial on those elements). For the text, `y`
is the realized Heegner point of conductor `f = |h|`, and `QuadOfDelta f` is `quadOfDelta_family`.
Its characterization: `globalTwistPointEquiv_rcPoint`, `rcPoint_galois_trace`.

**`jrc gen nP`** (definition) is the index valuation `j_rc = v₂ nP` of `P = nP · gen` modulo
torsion (tex 2416).

**`RetainedPointData.ofRC`** (definition) is the retained point data with `P := rcPoint`,
`j := j_rc` and `vL := v₂ L`. Its remaining fields are inputs of their own kinds:
* `L`, `hL`: the multiplier (H11);
* `gen`, `hgen`, `nP`, `hnP`, `hnP0`: rank one and non-torsion (Kolyvagin / GZK); the Kolyvagin
  part is a cited statement, GLUE (MPIM preprint MPI/90-69); the Gross–Zagier part stays PRINT;
* `hκ`, `cK`, `hcK`: GLUE / data, as in `RetainedPointData`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve compactCentralComplex
  globalTwistPointEquiv)
open ZInQ.Contrib.RC53Assist.CalibrationShape (basePointS)
open ZInQ.Contrib.CloudB3E2.NormCochain (QuadOfDelta)
open ZInQ.Manuscript.RC.CalPoint (RetainedPointData IsFreeLineGenerator)
open ZInQ.Manuscript.RC.Height (IsFreeGenerator)
open ZInQ.Manuscript.RC.TwistDictionary (twistK)

variable {K : Type} [Field K] [NumberField K] [DecidableEq K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData K E₀ hZ) {f : ℕ} [NeZero f]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), (f : 𝓞 K) ∈ v.asIdeal → v ∈ G.S)

/-- **The ring-class point `P^{rc}_{h,k} ∈ E^{(h)}(K)`** of the address (tex 2411–2416): the descent
to `centralCurve G` of the `χ_h`-weighted conductor-`f` trace of `y`. Kind: definition. -/
def rcPoint (y : (G.W.baseChange (KS K G.S)).toAffine.Point)
    (hy : ∀ g, ringClassRes f (NeZero.ne f) G.S hS g = 1 → galPtS G.W g y = y)
    (hQ : QuadOfDelta (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 f) :
    (centralCurve G).toAffine.Point :=
  rcPointK (W := G.W) (s := G.s) (hs := G.hs) (hs0 := G.hs0) hy
    (quadTrivial_of_quadOfDelta (hf := NeZero.ne f) (hS := hS) hQ)

omit [DecidableEq K] in
/-- **`P^{rc}` is the `χ_h`-weighted trace**, through the twist identification over `K_S`
(Galois descent). Kind: PROVED. -/
theorem globalTwistPointEquiv_rcPoint (y : (G.W.baseChange (KS K G.S)).toAffine.Point)
    (hy : ∀ g, ringClassRes f (NeZero.ne f) G.S hS g = 1 → galPtS G.W g y = y)
    (hQ : QuadOfDelta (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 f) :
    globalTwistPointEquiv G.W G.s G.hs G.hs0
        (basePointS (twistK G.W (hZ : K)) (rcPoint G hS y hy hQ)) =
      rcTrace G.W G.s G.hs G.hs0 (NeZero.ne f) hS y :=
  basePointS_rcPointK hy (quadTrivial_of_quadOfDelta (hf := NeZero.ne f) (hS := hS) hQ)

omit [DecidableEq K] in
/-- **The trace is in the `χ_h`-eigenspace** (tex 2415). Kind: PROVED. -/
theorem rcPoint_galois_trace (y : (G.W.baseChange (KS K G.S)).toAffine.Point)
    (hy : ∀ g, ringClassRes f (NeZero.ne f) G.S hS g = 1 → galPtS G.W g y = y)
    (hQ : QuadOfDelta (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 f) (σ : GKS K G.S) :
    galPtS G.W σ (rcTrace G.W G.s G.hs G.hs0 (NeZero.ne f) hS y) =
      chiH G.s G.hs G.hs0 σ • rcTrace G.W G.s G.hs G.hs0 (NeZero.ne f) hS y :=
  rcTrace_galois hy (quadTrivial_of_quadOfDelta (hf := NeZero.ne f) (hS := hS) hQ) σ

/-- **The index valuation `j_rc`** of a point `P ≡ nP · gen` modulo torsion, `gen` a free
generator: `v₂ nP` (tex 2416). Kind: definition. -/
def jrc (nP : ℤ) : ℤ := ((padicValInt 2 nP : ℕ) : ℤ)

/-- **The retained point data at the ring-class point** (tex 2411–2416, 3071–3085, 3895–3907):
`P := P^{rc}_{h,k}`, `j := j_rc`, `vL := v₂ L`. The rank-one/non-torsion inputs `gen`, `nP` are
cited from Kolyvagin / GZK (the Kolyvagin part a cited statement, GLUE; the Gross–Zagier
part PRINT), and the Kummer and conjugate-dual inputs are those of
`RetainedPointData`. Kind: definition. -/
def RetainedPointData.ofRC
    (κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1)
    (y : (G.W.baseChange (KS K G.S)).toAffine.Point)
    (hy : ∀ g, ringClassRes f (NeZero.ne f) G.S hS g = 1 → galPtS G.W g y = y)
    (hQ : QuadOfDelta (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 f)
    (L : ℤ) (hL : L ≠ 0) (gen : (centralCurve G).toAffine.Point) (hgen : IsFreeGenerator gen)
    (nP : ℤ) (hnP : IsOfFinAddOrder (rcPoint G hS y hy hQ - nP • gen)) (hnP0 : nP ≠ 0)
    (hκ : IsFreeLineGenerator ℤ_[2] (κ gen))
    (cK : (compactCentralComplex G).homology 1 →ₗ[ℤ_[2]] (compactCentralComplex G).homology 1)
    (hcK : ∀ x, cK (cK x) = x) :
    RetainedPointData G κ (jrc nP) ((padicValInt 2 L : ℕ) : ℤ) where
  L := L
  hL := hL
  hvL := rfl
  P := rcPoint G hS y hy hQ
  gen := gen
  hgen := hgen
  nP := nP
  hnP := hnP
  hnP0 := hnP0
  hj := rfl
  hκ := hκ
  cK := cK
  hcK := hcK

/-- The retained point data's point is the ring-class point. Kind: PROVED. -/
theorem RetainedPointData.ofRC_P
    (κ : (centralCurve G).toAffine.Point →+ (compactCentralComplex G).homology 1)
    (y : (G.W.baseChange (KS K G.S)).toAffine.Point)
    (hy : ∀ g, ringClassRes f (NeZero.ne f) G.S hS g = 1 → galPtS G.W g y = y)
    (hQ : QuadOfDelta (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 f)
    (L : ℤ) (hL : L ≠ 0) (gen : (centralCurve G).toAffine.Point) (hgen : IsFreeGenerator gen)
    (nP : ℤ) (hnP : IsOfFinAddOrder (rcPoint G hS y hy hQ - nP • gen)) (hnP0 : nP ≠ 0)
    (hκ : IsFreeLineGenerator ℤ_[2] (κ gen))
    (cK : (compactCentralComplex G).homology 1 →ₗ[ℤ_[2]] (compactCentralComplex G).homology 1)
    (hcK : ∀ x, cK (cK x) = x) :
    (RetainedPointData.ofRC G hS κ y hy hQ L hL gen hgen nP hnP hnP0 hκ cK hcK).P =
      rcPoint G hS y hy hQ := rfl

end ZInQ.Contrib.CloudB3E1RingClass
