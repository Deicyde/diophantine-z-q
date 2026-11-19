import ZInQKernel.Contrib.CloudB3E1RingClass.RCPointData
import ZInQKernel.Contrib.CloudB3E2Norm.HeegnerRCBridge
import ZInQKernel.Contrib.CloudB3E2Norm.KappaGen
import ZInQKernel.Contrib.CloudB3E2Norm.KummerInj
import ZInQKernel.Contrib.CloudB3E2Norm.GenusQuad
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalPointBlockZ

/-!
# The calibration point half at the actual address

Manuscript `diophantine_zq.tex`, tex 2411–2416, 3071–3085, 3895–3986, 4005–4021, 4057–4064.

Lane RC34's point half consumes `D : RetainedPointData G κ j vL` for the genuine Kummer map
`κ = centralKummer G hdiv` (`CentralPointData`). It produces the central class and functional
`centralClassFunctional hdual D hm` and lane RC35's Kummer block `KummerCoordinateBlockZ`
(`blockZOfPointData`, `KummerPointInputs.toBlockZ`). This file supplies `D` at the actual address,
with `K = ℚ(√k)`, Kummer data `G` whose central twist is `E_ℓ` over `K`, and an address `x` of a
family `F` with `h = h_x`.
* **`actualPointData`** (definition): `RetainedPointData.ofRC` at the ring-class point
  `P^{rc} = rcPoint G hS y hy hQ`, built from:
  * `y`: lane E2's realized Heegner point of conductor `f`, `heegnerPtG` (from the full anchor);
  * `hy`: `heegner_hy_G`;
  * `hQ`: lane E2's genus theory `quadOfDelta_family`, for `h = h_x` and `f` divisible by the
    primes of `h_x`;
  * `hκ`: lane E2's `hκ_central`, with `hδ := hδ_of_equiv` (the Kummer sequence) for the
    point Kummer map `δ = kummerInf ∘ ι`.
  Its `j` is `j_rc = v₂ nP` and its `vL` is `v₂ L`.
* `actual_v2_a0`, `actual_v2_b0`, `actual_core_v2` (PROVED): the valuations of the central
  class and functional, `v₂ a₀ = v₂ b₀ = j_rc + v₂ L + v₂ m`, and
  `v₂ (a b u₀)(0) = 2 (j_rc + v₂ L + v₂ m)` (tex 3905–3907, 4061–4064).
* **`actualKummerPointInputs`** and **`kummerBlockZ_of_actual`** (definitions): lane RC35's Kummer
  block of the actual address, together with `kummerBlockZ_of_actual_Z`: its `Z` is the central
  class and functional of `P^{rc}`.
* `dvd_natAbs_h`, `natAbs_h_ne_zero` (PROVED): `f = |h_x|` is a nonzero conductor divisible by
  the primes `q` with `λ_q(x) = 1`.

Named inputs, beyond the block's non-point fields:
* `hcomp` (GLUE, tex 4005–4014): `κ(P) ⊗ d ↦ δ(P, d)` through the coefficient comparison, with
  the identification `ι` of the points;
* `gen`, `hgen`, `nP`, `hnP`, `hnP0` (PRINT, rank one and non-torsion: Kolyvagin / GZK);
* `L`, `hL` (H11, tex 3071–3085);
* `cK`, `hcK` (the conjugate-dual transport, tex 3904);
* the full anchor `hA`, the coprimality `hcop`, and the support conditions.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain WeierstrassCurve
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Contrib.RC53Assist.Calibration (GenuineKummerData)
open ZInQ.Contrib.RC53Assist.CalibrationIntegral (centralCurve compactCentralComplex)
open ZInQ.Contrib.RC53Assist.CalibrationShape (arithmeticCentralFull)
open ZInQ.Contrib.RC53Assist.CalibrationModel (CalibrationCohomologyShape retainedCentralComplex)
open ZInQ.Manuscript.RC53Assist.CentralUniversal (KummerCoefficientComparison
  KummerCohomologyFinite arithmeticUniversalCoefficientMap QuadraticField)
open ZInQ.Manuscript.RC53Assist.QuadraticDescent (SelK sqrtK)
open ZInQ.Manuscript.RC (SelmerCorankOneOverK)
open ZInQ.Manuscript.RC.CalPoint
open ZInQ.Manuscript.RC.Height (IsFreeGenerator)
open ZInQ.Manuscript.SelmerTwoPower (Q2Z2)
open ZInQ.Contrib.CloudB3E2.NormCochain (QuadOfDelta CSTParam FullAnchor heegnerPtG heegner_hy_G
  quadOfDelta_family family_h_eq_prod)
open ZInQ.Contrib.CloudB3E2.GenusSquare (qstar)
open ZInQ.Contrib.CloudB3E2.KappaGen (centralH1Equiv hκ_central)
open ZInQ.Contrib.CloudB3E2.KummerInj (kummerInf hδ_of_equiv)
open ZInQ.Contrib.RC53Assist.DiskOrders.Limit (pointsK)
open scoped TensorProduct

/-! ### The conductor `|h_x|` -/

/-- `q ∣ |h_x|` for `q ∈ Q` with `λ_q(x) = 1`. Kind: PROVED. -/
theorem dvd_natAbs_h (F : ZInQ.Manuscript.RC.Family) (x : ZInQ.Manuscript.RC.Addr F.b)
    (hodd : ∀ q ∈ F.Q, q % 2 = 1) {q : ℕ} (hq : q ∈ F.Q) (hl : F.lam q x = 1) :
    q ∣ (F.h x).natAbs := by
  classical
  rw [family_h_eq_prod F x hodd]
  have hmem : q ∈ F.Q.filter (fun q => F.lam q x = 1) := Finset.mem_filter.2 ⟨hq, hl⟩
  have h1 : qstar q ∣ ∏ q ∈ F.Q.filter (fun q => F.lam q x = 1), qstar q :=
    Finset.dvd_prod_of_mem _ hmem
  have h2 : (q : ℤ) ∣ qstar q := by
    unfold qstar
    exact Dvd.intro_left _ rfl
  exact Int.natCast_dvd.mp (by simpa using h2.trans h1)

/-- `h_x ≠ 0` for a family of odd primes. Kind: PROVED. -/
theorem natAbs_h_ne_zero (F : ZInQ.Manuscript.RC.Family) (x : ZInQ.Manuscript.RC.Addr F.b)
    (hQ : ∀ q ∈ F.Q, q.Prime ∧ q ≠ 2) : (F.h x).natAbs ≠ 0 := by
  classical
  have hodd : ∀ q ∈ F.Q, q % 2 = 1 := fun q hq =>
    Nat.odd_iff.mp ((hQ q hq).1.odd_of_ne_two (hQ q hq).2)
  rw [Int.natAbs_ne_zero, family_h_eq_prod F x hodd]
  refine Finset.prod_ne_zero_iff.2 fun q hq => ?_
  unfold qstar
  have hq0 : (q : ℤ) ≠ 0 := by
    exact_mod_cast (hQ q (Finset.mem_of_mem_filter q hq)).1.ne_zero
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hq0

/-! ### The point data at the actual address -/

section Actual

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] [DecidableEq (QuadraticField k)]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve G = (Ecurve ℓ).baseChange (QuadraticField k))
  {cp : CSTParam E₀} {emb : AlgebraicClosure ℚ →ₐ[ℚ] ℂ}
  {κ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure (QuadraticField k)}
  {DH : ZInQ.Manuscript.RC.PrintsArith.HeegnerPointData E₀}
  (hA : FullAnchor E₀ (QuadraticField k) cp emb κ' DH)
  (f : ℕ) [NeZero f] (hcop : Nat.Coprime f (DH.N * DH.DK.natAbs))
  (hS : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (f : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
    v ∈ G.S)
  (hQ : QuadOfDelta (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 f)

/-- **The ring-class point of the actual address** `P^{rc}_{h,k} ∈ E^{(h)}(K)` (tex 2411–2416): the
descent of the `χ_h`-weighted conductor-`f` trace of lane E2's realized Heegner point.
Kind: definition. -/
abbrev actualRCPoint : (centralCurve G).toAffine.Point :=
  rcPoint G hS (heegnerPtG G hA f hcop hS) (heegner_hy_G G hA f hcop hS) hQ

omit [DecidableEq (QuadraticField k)] in
include hS in
/-- **The genus input at the address** (lane E2's `quadOfDelta_family`): `QuadOfDelta f` for
`h = h_x`, `f` divisible by the primes `q` with `λ_q(x) = 1`. Kind: PROVED. -/
theorem quadOfDelta_actual (hK2 : Module.finrank ℚ (QuadraticField k) = 2)
    (hTC : IsTotallyComplex (QuadraticField k))
    (F : ZInQ.Manuscript.RC.Family) (x : ZInQ.Manuscript.RC.Addr F.b)
    (hFQ : ∀ q ∈ F.Q, q.Prime ∧ q ≠ 2) (hh : hZ = F.h x)
    (hf : ∀ q ∈ F.Q, F.lam q x = 1 → q ∣ f) :
    QuadOfDelta (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 f :=
  quadOfDelta_family (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 hK2 hTC F x hFQ (by rw [hh]) f
    hf hS

/-- **The point data of the actual address** (tex 2411–2416, 3071–3085, 3895–3907, 4005–4021):
`RetainedPointData.ofRC` at `P^{rc}` for the genuine Kummer map, with `hκ` from lane E2's
`hκ_central` and `hδ_of_equiv`. Kind: definition. -/
def actualPointData (hdiv : GlobalDivisionTowers G.S (centralCurve G))
    (L : ℤ) (hL : L ≠ 0) (gen : (centralCurve G).toAffine.Point) (hgen : IsFreeGenerator gen)
    (nP : ℤ) (hnP : IsOfFinAddOrder (actualRCPoint k G hA f hcop hS hQ - nP • gen))
    (hnP0 : nP ≠ 0)
    (hk : ¬ IsSquare (k : ℚ))
    (I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (Fin : KummerCohomologyFinite ℓ k G.S (arithmeticCentralFull ℓ k G hcurve))
    (hSel : SelmerCorankOneOverK ℓ k)
    (ι : (centralCurve G).toAffine.Point ≃+ pointsK (sqrtK k) (Ecurve ℓ))
    (hcomp : ∀ P d, arithmeticUniversalCoefficientMap ℓ k G.S
      (arithmeticCentralFull ℓ k G hcurve) I
        (centralH1Equiv ℓ k G hcurve (centralKummer G hdiv P) ⊗ₜ[ℤ_[2]] d) =
      kummerInf (sqrtK k) (Ecurve ℓ) (ι P) d)
    (cK : (compactCentralComplex G).homology 1 →ₗ[ℤ_[2]] (compactCentralComplex G).homology 1)
    (hcK : ∀ y, cK (cK y) = y) :
    CentralPointData G hdiv (jrc nP) ((padicValInt 2 L : ℕ) : ℤ) :=
  RetainedPointData.ofRC G hS (centralKummer G hdiv) (heegnerPtG G hA f hcop hS)
    (heegner_hy_G G hA f hcop hS) hQ L hL gen hgen nP hnP hnP0
    (hκ_central ℓ k G hcurve hk I Fin hSel hdiv gen
      (fun P d => kummerInf (sqrtK k) (Ecurve ℓ) (ι P) d) hcomp
      (fun d h => hδ_of_equiv (sqrtK k) (Ecurve ℓ) ι hgen.1 hgen.2 d h))
    cK hcK

/-- The point of the actual point data is `P^{rc}`. Kind: PROVED. -/
theorem actualPointData_P (hdiv) (L hL gen hgen nP hnP hnP0 hk I Fin hSel ι hcomp cK hcK) :
    (actualPointData ℓ k G hcurve hA f hcop hS hQ hdiv L hL gen hgen nP hnP hnP0 hk I Fin hSel ι
      hcomp cK hcK).P = actualRCPoint k G hA f hcop hS hQ := rfl

end Actual

/-! ### The Kummer block of the actual address -/

section Block

open ZInQ.Manuscript.RC.Wiring (CalibrationBookProps)
open ZInQ.Manuscript.RC.Wiring.KmIdent (KummerCoordinateBlockZ centralKMIdentOf
  centralKMIdentModelOf retainedA0 retainedB0 CentralClassFunctional)
open ZInQ.Contrib.RC53Assist.Calibration (DiskArith)
open ZInQ.Manuscript.RC (v2 central)

attribute [local instance] Nat.fact_prime_two

variable (ℓ : ℕ) (k : ℤ) [(Ecurve ℓ).IsElliptic] [DecidableEq (QuadraticField k)]
  {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  (G : GenuineKummerData (QuadraticField k) E₀ hZ)
  (hcurve : centralCurve G = (Ecurve ℓ).baseChange (QuadraticField k))
  (hdiv : GlobalDivisionTowers G.S (centralCurve G))

/-- **The point inputs of the actual address**: the arguments of `actualPointData`.
* the Heegner anchor `hA` (the CST parametrization, the CM points, the full anchor);
* the conductor `f` (`f = |h_x|`, `natAbs_h_ne_zero`, `dvd_natAbs_h`), coprime to `N·|D_K|`,
  with its primes in the support;
* the genus input `hQ` (`quadOfDelta_actual`);
* the multiplier `L` (H11);
* the PRINT inputs `gen`, `nP` (rank one, non-torsion);
* the coefficient comparison, finiteness and Selmer corank one of `hκ_central`, and its GLUE
  `hcomp` with the identification `ι`;
* the conjugate-dual transport `cK`.
Kind: definition (inputs). -/
structure ActualPointInputs where
  /-- the CST parametrization -/
  cp : CSTParam E₀
  /-- the complex embedding -/
  emb : AlgebraicClosure ℚ →ₐ[ℚ] ℂ
  /-- the identification of algebraic closures -/
  κ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure (QuadraticField k)
  /-- the Heegner point data -/
  DH : ZInQ.Manuscript.RC.PrintsArith.HeegnerPointData E₀
  /-- the full anchor -/
  hA : FullAnchor E₀ (QuadraticField k) cp emb κ' DH
  /-- the conductor -/
  f : ℕ
  [hf0 : NeZero f]
  /-- it is prime to `N · |D_K|` -/
  hcop : Nat.Coprime f (DH.N * DH.DK.natAbs)
  /-- its primes lie in the support -/
  hS : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (f : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
    v ∈ G.S
  /-- genus theory: `χ_h` is trivial on the elements fixing `H_f` -/
  hQ : QuadOfDelta (le_refl G.S) (le_refl G.S) G.s G.hs G.hs0 f
  /-- the multiplier of (H11) -/
  L : ℤ
  /-- `L ≠ 0` -/
  hL : L ≠ 0
  /-- a free generator of `E^{(h)}(K)` modulo torsion (PRINT) -/
  gen : (centralCurve G).toAffine.Point
  /-- it is a free generator -/
  hgen : IsFreeGenerator gen
  /-- the coefficient of `P^{rc}` (PRINT) -/
  nP : ℤ
  /-- `P^{rc} ≡ nP · gen` modulo torsion -/
  hnP : IsOfFinAddOrder (actualRCPoint k G hA f hcop hS hQ - nP • gen)
  /-- `P^{rc}` is not torsion -/
  hnP0 : nP ≠ 0
  /-- `k` is not a square -/
  hk : ¬ IsSquare (k : ℚ)
  /-- the coefficient comparison -/
  I : KummerCoefficientComparison ℓ k G.S (arithmeticCentralFull ℓ k G hcurve)
  /-- finite generation -/
  Fin : KummerCohomologyFinite ℓ k G.S (arithmeticCentralFull ℓ k G hcurve)
  /-- Selmer corank one over `K` -/
  hSel : SelmerCorankOneOverK ℓ k
  /-- the identification of the points -/
  ι : (centralCurve G).toAffine.Point ≃+ pointsK (sqrtK k) (Ecurve ℓ)
  /-- **the Kummer compatibility of the comparison** (GLUE, tex 4005–4014) -/
  hcomp : ∀ P d, arithmeticUniversalCoefficientMap ℓ k G.S
      (arithmeticCentralFull ℓ k G hcurve) I
        (centralH1Equiv ℓ k G hcurve (centralKummer G hdiv P) ⊗ₜ[ℤ_[2]] d) =
      kummerInf (sqrtK k) (Ecurve ℓ) (ι P) d
  /-- the conjugate-dual transport -/
  cK : (compactCentralComplex G).homology 1 →ₗ[ℤ_[2]] (compactCentralComplex G).homology 1
  /-- it is involutive -/
  hcK : ∀ y, cK (cK y) = y

attribute [instance] ActualPointInputs.hf0

variable {ℓ k G hcurve hdiv}

/-- The point data of the inputs. Kind: definition. -/
def ActualPointInputs.pointData (A : ActualPointInputs ℓ k G hcurve hdiv) :
    CentralPointData G hdiv (jrc A.nP) ((padicValInt 2 A.L : ℕ) : ℤ) :=
  actualPointData ℓ k G hcurve A.hA A.f A.hcop A.hS A.hQ hdiv A.L A.hL A.gen A.hgen A.nP A.hnP
    A.hnP0 A.hk A.I A.Fin A.hSel A.ι A.hcomp A.cK A.hcK

/-- Its point is `P^{rc}`. Kind: PROVED. -/
theorem ActualPointInputs.pointData_P (A : ActualPointInputs ℓ k G hcurve hdiv) :
    A.pointData.P = actualRCPoint k G A.hA A.f A.hcop A.hS A.hQ := rfl

variable {hfinite : ∀ n : ℤ, Module.Finite ℤ_[2] ((compactCentralComplex G).homology n)}
  {H : CalibrationCohomologyShape (compactCentralComplex G)}

/-- **The point half at the actual address** (tex 3895–3910, 4005–4021, 4057–4064): for the
central class and functional of `L m P^{rc}` with the duality of the book statements,
`v₂ a₀ = v₂ b₀ = j_rc + v₂ L + v₂ m`, `v₂ (a b u₀)(0) = 2 (j_rc + v₂ L + v₂ m)`, and the seven
fields of the block. PROVED. -/
theorem actual_pointHalf (A : ActualPointInputs ℓ k G hcurve hdiv) (B : CalibrationBookProps)
    (hK : IsTotallyComplex (QuadraticField k))
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ G.S) {m : ℤ} (hm : m ≠ 0) :
    let Z := centralClassFunctional (H := H) (bookDuality G hfinite B hK h2) A.pointData hm
    let I := centralKMIdentModelOf G hfinite H Z
    v2 ((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) =
        ((jrc A.nP + ((padicValInt 2 A.L : ℕ) : ℤ) + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) :
          WithTop ℤ) ∧
      v2 ((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) =
        ((jrc A.nP + ((padicValInt 2 A.L : ℕ) : ℤ) + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) :
          WithTop ℤ) ∧
      v2 (central (I.a * I.b * I.u₀)) =
        ((2 * (jrc A.nP + ((padicValInt 2 A.L : ℕ) : ℤ) + ((padicValInt 2 m : ℕ) : ℤ)) : ℤ) :
          WithTop ℤ) ∧
      SevenFields I (jrc A.nP) ((padicValInt 2 A.L : ℕ) : ℤ) m
        (PowerSeries.C (((retainedA0 G hfinite H Z.z0 : ℤ_[2]) : ℚ_[2]) / (m : ℚ_[2])))
        (PowerSeries.C (((retainedB0 G hfinite H Z.lam0 : ℤ_[2]) : ℚ_[2]) / (m : ℚ_[2]))) :=
  ⟨centralClassFunctional_v2_a0 _ A.pointData hm, centralClassFunctional_v2_b0 _ A.pointData hm,
    (pointHalf_of_book B hK h2 hdiv A.pointData hm).1,
    (pointHalf_of_book B hK h2 hdiv A.pointData hm).2⟩

/-- **The Kummer block's inputs at the actual address** (tex 3895–3910, 4005–4021, 4057–4064):
lane RC34's `KummerPointInputs` with the point data of `P^{rc}`; the non-point fields are those
of `KummerPointInputs`. Kind: definition. -/
def actualKummerPointInputs {B : CalibrationBookProps} {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {m : ℤ} {tA shaA : ℕ} (A : ActualPointInputs ℓ k G hcurve hdiv)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ G.S)
    (hK : IsTotallyComplex (QuadraticField k))
    (finite2 : Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (hm : m ≠ 0)
    (link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2],
      ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMIdentOf G hfinite H
        (centralClassFunctional (bookDuality G hfinite B hK h2) A.pointData hm)).coord)
    (arith : DiskArith G tA shaA) :
    KummerPointInputs B (QuadraticField k) E₀ hZ DK zK wK (jrc A.nP)
      ((padicValInt 2 A.L : ℕ) : ℤ) m tA shaA where
  G := G
  hfinite := hfinite
  H := H
  h2 := h2
  hK := hK
  finite2 := finite2
  rank_one := rank_one
  hdiv := hdiv
  pt := A.pointData
  hm := hm
  link := link
  arith := arith

/-- **Lane RC35's Kummer block of the actual address** (tex 3895–3910, 4005–4021,
4057–4064). Kind: definition. -/
def kummerBlockZ_of_actual {B : CalibrationBookProps} {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {m : ℤ} {tA shaA : ℕ} (A : ActualPointInputs ℓ k G hcurve hdiv)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ G.S)
    (hK : IsTotallyComplex (QuadraticField k))
    (finite2 : Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (hm : m ≠ 0)
    (link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2],
      ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMIdentOf G hfinite H
        (centralClassFunctional (bookDuality G hfinite B hK h2) A.pointData hm)).coord)
    (arith : DiskArith G tA shaA) :
    KummerCoordinateBlockZ (QuadraticField k) E₀ hZ DK zK wK (jrc A.nP)
      ((padicValInt 2 A.L : ℕ) : ℤ) m tA shaA :=
  (actualKummerPointInputs (B := B) (hfinite := hfinite) (H := H) A h2 hK finite2 rank_one hm
    link arith).toBlockZ

/-- **The block's central class and functional are those of `L m P^{rc}`**. Kind: PROVED. -/
theorem kummerBlockZ_of_actual_Z {B : CalibrationBookProps} {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {m : ℤ} {tA shaA : ℕ} (A : ActualPointInputs ℓ k G hcurve hdiv)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 (QuadraticField k)), (2 : 𝓞 (QuadraticField k)) ∈ v.asIdeal →
      v ∈ G.S)
    (hK : IsTotallyComplex (QuadraticField k))
    (finite2 : Finite (AddCommGroup.primaryComponent (centralCurve G).toAffine.Point 2))
    (rank_one : Module.finrank ℤ_[2] ((compactCentralComplex G).homology 1) = 1)
    (hm : m ≠ 0)
    (link : ∃ ε : ℤ_[2]ˣ, ∃ uK : PowerSeries ℚ_[2],
      ZInQ.Manuscript.RC.Central.IsClassFunctionalCoord DK zK wK uK ∧
      central uK = ((ε : ℤ_[2]) : ℚ_[2]) * central (centralKMIdentOf G hfinite H
        (centralClassFunctional (bookDuality G hfinite B hK h2) A.pointData hm)).coord)
    (arith : DiskArith G tA shaA) :
    (kummerBlockZ_of_actual (B := B) (hfinite := hfinite) (H := H) (DK := DK) (zK := zK)
      (wK := wK) A h2 hK finite2 rank_one hm link arith).Z =
      centralClassFunctional (H := H) (bookDuality G hfinite B hK h2) A.pointData hm := rfl

end Block

end ZInQ.Contrib.CloudB3E1RingClass
