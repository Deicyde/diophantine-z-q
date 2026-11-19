import ZInQKernel.Contrib.RC53Assist.Calibration.KummerCoordinate
import ZInQKernel.Contrib.RC53Assist.Calibration.GenuineLocalBlocks

/-!
# The Kummer block of the calibration: recorded obstructions, integral disk lengths read from the
# genuine finite-level Kummer Selmer complexes, and the moving prime

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 3877–3909, 3975–3985,
4005–4018, 4050–4080).

## Status of the earlier Kummer block (conditional bookkeeping)

`KummerCoordinateBlock` and `CentralDiskOrders` are **conditional bookkeeping**: they compute the
Knudsen–Mumford coordinate of a rational Kummer model from its disks, but they do not identify the
integral Kummer complex, its retained determinant basis, or its torsion with the actual torsion and
Tate–Shafarevich groups. The field `hK` of the calibration leaf is therefore **not** discharged
arithmetically by them; it stays an ELLIOT input. The obstructions are recorded below, compiled:

* `redisk2`: a Knudsen–Mumford identification over `ℚ₂[[t]]` accepts any unit as its degree-two
  disk, with the same target Selmer complex, class and functional (the disks are units of
  `ℚ₂[[t]]`, so their integral orders are invisible to a rational quasi-isomorphism);
* `manufactureShaBlock`, `manufactured_sha_valuation`: from one fixed normalized identification,
  a complete block with any declared Tate–Shafarevich order `2^s`, and coordinate valuation
  `2g − s`;
* `link_iff_uK_eq`: under `z_K ⊗ w_K = u_K adj D_K` and `adj D_K ≠ 0`, the field `link` is exactly
  the coordinate equation `u_K = I.coord` (coordinate transfer, not an identification of the
  two-term model); `changeDifferential`: in dimension one the differential can be replaced by any
  other, even one for which the class is not a cycle;
* `genuine_length_iff_local_det`: for genuine local presentations at every precision, the length
  input of `GenuineLengthBlockModel` is exactly `det B ≠ 0 ∧ v₂ det B = ℓ`;
* `compositeMovingNumber`: `GenuineLengthBlockModel` does not force its moving number to be prime.

## Integral disk lengths read from the genuine finite-level Kummer Selmer complexes

For the address's data `G : GenuineKummerData` (the curve `E_K`, the twist `h`, a square root of
`h` in `K_S`, full `2`-power torsion over `K_S`) and the central coefficient character, the genuine
finite-level Kummer Selmer data at precision `i` are the local Kummer maps' `kummerSelData` with
the actual Kummer condition at every place (`centralKummerSelData`); `G.selH i n` is the `n`-th
cohomology of their Selmer complex. The two inputs replacing the free disk orders are

* `DiskTie G x₁ x₂ x₃` (GLUE, the order form of the derived reduction of the integral central
  Kummer model: the core with free cohomology of rank one in degrees one and two, and the disks
  with central values `x_i ∈ ℤ₂`, tex 3429–3431, 4005–4018): for all large `i`,
  `|H⁰| = |A_i/(x₁)|`, `|H²| = 2^{i·i} |A_i/(x₂)| |A_i/(x₃)|`, `|H³| = |A_i/(x₃)|`;
* `DiskArith G tA shaA` (ELLIOT: universal coefficients, `H¹(C_K)_tors = 𝒜(ℚ)_tors[2^∞]`,
  `H²(C_K)_tors = Ш(𝒜)[2^∞]` for finite `Ш`, self-duality, tex 4005–4018): for all large `i`,
  `|H⁰| = 2^{i v₂ tA}`, `|H²| = 2^{i (i + v₂ shaA + v₂ tA)}`, `|H³| = 2^{i v₂ tA}`.

Results (PROVED): `cycOrder_eq` (`|A_i/(x)| = 2^{i v₂ x}`); `DiskTie.valuations`: the disk lengths
are derived, `v₂ x₁ = v₂ x₃ = v₂ tA`, `v₂ x₂ = v₂ shaA`; `DiskTie.determined`: for fixed genuine
complexes the disk lengths are determined; `DiskArith.determined`: so are `v₂ tA`, `v₂ shaA`.

* `KummerCoordinateBlockG`: the Kummer block with `disks` replaced by the integral central values,
  `DiskTie` and `DiskArith` over the address's data; `KummerCoordinateBlockG.hK` gives the field
  `hK` in its exact form; `disk_valuations_determined`, `exponents_determined`: two blocks over the
  same genuine data have the same central disk valuations and declared exponents, which excludes
  `Recorded.manufactureShaBlock`. The identification `I` over `ℚ₂[[t]]` and the coordinate transfer
  `link` remain inputs, relabelled GLUE.

## The moving prime

`MovingPrimeData ℓ h r a χ`: `r` is prime, `r ∤ 6hℓ`, `a = r + 1 − |Ẽ(𝔽_r)|` for the integral
model `y² = x³ + 2ℓx² − 3ℓ²x` of `E` (`E0Z_one_map`), and `χ = (h/r)` (the quadratic Frobenius
sign); `MovingPrimeData.chimov_sign`, `MovingPrimeData.odd`.

## The leaves

* `CalibrationModelHK2`: `CalibrationModelH` without `hK`, with `KummerCoordinateBlockG`;
  `CalibrationModelHK2.toModelH`, `calibrationTarget_of_HK2`.
* `CalibrationModelHKL2`: `CalibrationModelH` without `hK` and the local-block fields, with
  `KummerCoordinateBlockG`, `GenuineLengthBlockModel` and `MovingPrimeData`;
  `CalibrationModelHKL2.nonempty_modelP`, `calibrationInputsP_of_HKL2`,
  `calibrationTarget_of_HKL2`.

## Remaining inputs

* The identification `I` over `ℚ₂[[t]]`: its coefficient module and local conditions are not those
  of the curve (no Kummer complex over `ℚ₂[[t]]` exists here), and its Selmer class and functional
  are fields, not the ring-class Kummer class and its conjugate-dual pairing.
* `link`: a coordinate transfer; no chain comparison of the leaf's two-term model with the genuine
  complex, with its determinant-basis factor controlled integrally, is constructed.
* `DiskTie`: an identification at the level of orders at every precision, not an integral lattice
  comparison; `DiskArith`: the arithmetic orders.
* The local presentations and lengths of `GenuineLengthBlockModel` (exactly the local determinant
  valuations) and `MovingPrimeData`.

Kinds: definitions and PROVED theorems; the inputs are the fields, each with its kind.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open Matrix CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-! ### Recorded obstructions to reading the earlier Kummer block arithmetically -/

namespace Recorded

section Redisk

variable {R : Type} [CommRing R] {ke ko : Type}
  [Fintype ke] [Fintype ko] [DecidableEq ke] [DecidableEq ko]

/-- A diagonal unit change of basis, degree by degree. -/
def diagonalAt (C C' : BasedCx R ke ko) (q : ke ⊕ ko → Rˣ)
    (hdeg : C.deg = C'.deg) (i : ℤ) : C.degSub i →ₗ[R] C'.degSub i where
  toFun v := ⟨fun x => (q x : R) * v.1 x, by
    intro x hx
    change (q x : R) * v.1 x = 0
    have hx' : C.deg x ≠ i := by simpa [hdeg] using hx
    rw [v.2 x hx', mul_zero]⟩
  map_add' a b := by apply Subtype.ext; funext x; exact mul_add _ _ _
  map_smul' a v := by
    apply Subtype.ext
    funext x
    change (q x : R) * (a * v.1 x) = a * ((q x : R) * v.1 x)
    ring

/-- A diagonal unit change of basis commuting with the differentials, as a chain map. -/
def diagonalHom (C C' : BasedCx R ke ko) (q : ke ⊕ ko → Rˣ)
    (hdeg : C.deg = C'.deg)
    (hd : Matrix.diagonal (fun x => (q x : R)) * C.dTot =
      C'.dTot * Matrix.diagonal (fun x => (q x : R))) : GHom C.toGCx C'.toGCx where
  f i j hij := hij ▸ diagonalAt C C' q hdeg i
  comm i i₁ j j₁ hij h₁ h₂ hj v := by
    subst hij hj
    let vv : C.degSub i := v
    apply Subtype.ext
    funext x
    change (q x : R) * ∑ y, C.dTot x y * vv.1 y =
      ∑ y, C'.dTot x y * ((q y : R) * vv.1 y)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    have hxy := congrFun (congrFun hd x) y
    rw [diagonal_mul, mul_diagonal] at hxy
    calc (q x : R) * (C.dTot x y * vv.1 y) = ((q x : R) * C.dTot x y) * vv.1 y := by ring
      _ = (C'.dTot x y * (q y : R)) * vv.1 y := by rw [hxy]
      _ = C'.dTot x y * ((q y : R) * vv.1 y) := by ring

theorem inverse_diagonal_comm (C C' : BasedCx R ke ko) (q : ke ⊕ ko → Rˣ)
    (hd : Matrix.diagonal (fun x => (q x : R)) * C.dTot =
      C'.dTot * Matrix.diagonal (fun x => (q x : R))) :
    Matrix.diagonal (fun x => (((q x)⁻¹ : Rˣ) : R)) * C'.dTot =
      C.dTot * Matrix.diagonal (fun x => (((q x)⁻¹ : Rˣ) : R)) := by
  ext x y
  have h := congrFun (congrFun hd x) y
  rw [diagonal_mul, mul_diagonal] at h ⊢
  have hq := Units.inv_mul (q x)
  have hy := Units.mul_inv (q y)
  calc (((q x)⁻¹ : Rˣ) : R) * C'.dTot x y =
        (((q x)⁻¹ : Rˣ) : R) * (C'.dTot x y * (q y : R)) * (((q y)⁻¹ : Rˣ) : R) := by
          rw [mul_assoc, mul_assoc, hy, mul_one]
    _ = (((q x)⁻¹ : Rˣ) : R) * ((q x : R) * C.dTot x y) * (((q y)⁻¹ : Rˣ) : R) := by rw [h]
    _ = C.dTot x y * (((q y)⁻¹ : Rˣ) : R) := by rw [← mul_assoc, hq, one_mul]

/-- The diagonal unit change of basis is an isomorphism of complexes. -/
instance diagonalHom_isIso (C C' : BasedCx R ke ko) (q : ke ⊕ ko → Rˣ)
    (hdeg : C.deg = C'.deg)
    (hd : Matrix.diagonal (fun x => (q x : R)) * C.dTot =
      C'.dTot * Matrix.diagonal (fun x => (q x : R))) :
    IsIso (GHom.toCC (diagonalHom C C' q hdeg hd)) := by
  let g := diagonalHom C' C (fun x => (q x)⁻¹) hdeg.symm (inverse_diagonal_comm C C' q hd)
  refine ⟨⟨GHom.toCC g, ?_, ?_⟩⟩
  · rw [GHom.toCC_comp, ← toCC_idGHom]
    apply GHom.toCC_ext
    intro i v
    apply Subtype.ext
    funext x
    change (((q x)⁻¹ : Rˣ) : R) * ((q x : R) * v.1 x) = v.1 x
    rw [← mul_assoc, Units.inv_mul, one_mul]
  · rw [GHom.toCC_comp, ← toCC_idGHom]
    apply GHom.toCC_ext
    intro i v
    apply Subtype.ext
    funext x
    change (q x : R) * ((((q x)⁻¹ : Rˣ) : R) * v.1 x) = v.1 x
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-- The index type of the Knudsen–Mumford model. -/
abbrev KMTotal (n : ℕ) : Type :=
  ((((Empty ⊕ Unit) ⊕ Empty) ⊕ Empty) ⊕ (((Fin n ⊕ Empty) ⊕ Unit) ⊕ Unit)) ⊕
    ((((Fin n ⊕ Unit) ⊕ Unit) ⊕ Empty) ⊕ (((Empty ⊕ Empty) ⊕ Empty) ⊕ Unit))

/-- The diagonal scaling of the degree-two disk coordinate. -/
def disk2Units (n : ℕ) (r : Rˣ) : KMTotal n → Rˣ
  | .inl (.inr (.inl (.inr _))) => r
  | _ => 1

theorem disk2_comm {n : ℕ} (D : Matrix (Fin n) (Fin n) R) (d1 d2 d3 b : Rˣ) :
    Matrix.diagonal (fun x => (disk2Units n (d2 * b⁻¹) x : R)) *
        (kummerModel D (d1 : R) b d3).toBased.dTot =
      (kummerModel D (d1 : R) d2 d3).toBased.dTot *
        Matrix.diagonal (fun x => (disk2Units n (d2 * b⁻¹) x : R)) := by
  ext x y
  rw [diagonal_mul, mul_diagonal]
  rcases x with (((((e | u) | e) | e) | (((j | e) | u) | u)) |
    ((((j | u) | u) | e) | (((e | e) | e) | u)))
  all_goals rcases y with (((((e | u) | e) | e) | (((j | e) | u) | u)) |
    ((((j | u) | u) | e) | (((e | e) | e) | u)))
  all_goals try casesm* Empty
  all_goals simp [disk2Units, BasedCx.dTot, FourCx.toBased, kummerModel, FourCx.sum,
    twoTerm, disk01, disk12, disk23, sc, mul_assoc]

theorem scale_disk2_vec1 {n : ℕ} (r : Rˣ) (z : Fin n → R) :
    (fun x : KMTotal n => (disk2Units n r x : R) * vec1 (kz z) x) = vec1 (kz z) := by
  funext x
  rcases x with ((a | b) | (c | d))
  all_goals simp [vec1, disk2Units]

theorem scale_disk2_vec2 {n : ℕ} (r : Rˣ)
    (y : ((Fin n ⊕ Empty) ⊕ Unit) ⊕ Unit → R) :
    (fun x : KMTotal n => (disk2Units n r x : R) * vec2 y x) =
      vec2 (fun j => (disk2Units n r (.inl (.inr j)) : R) * y j) := by
  funext x
  rcases x with ((a | b) | (c | d))
  all_goals simp [vec2]

theorem kw_disk2 {n : ℕ} (r : Rˣ) (w : Fin n → R)
    (y : ((Fin n ⊕ Empty) ⊕ Unit) ⊕ Unit → R) :
    kw w ⬝ᵥ (fun j => (disk2Units n r (.inl (.inr j)) : R) * y j) = kw w ⬝ᵥ y := by
  simp [kw, disk2Units, dotProduct, Fintype.sum_sum_type]

/-- **Recorded obstruction (the degree-two disk is invisible rationally).** A Knudsen–Mumford
identification accepts any unit `b` as its degree-two disk: the comparison is composed with a
diagonal isomorphism, and the target Selmer complex, class and functional are unchanged. -/
def redisk2 [IsDomain R] {D : SelData R} (I : KummerModelIdentification D) (b : Rˣ) :
    KummerModelIdentification D := by
  let f := diagonalHom (kummerModel I.Dc (I.δ₁ : R) b I.δ₃).toBased
    (kummerModel I.Dc (I.δ₁ : R) I.δ₂ I.δ₃).toBased
    (disk2Units I.n (I.δ₂ * b⁻¹)) rfl (disk2_comm I.Dc I.δ₁ I.δ₂ I.δ₃ b)
  refine { I with
    δ₂ := b
    φ := ghomComp f I.φ
    qis := ?_
    hclass := ?_
    hfun := ?_ }
  · have : IsIso (GHom.toCC f) := by
      dsimp [f]
      exact diagonalHom_isIso _ _ _ _ _
    have : QuasiIso (GHom.toCC f) := inferInstance
    have : QuasiIso (GHom.toCC I.φ) := I.qis
    rw [← GHom.toCC_comp]
    infer_instance
  · change (I.φ.f 1 1 rfl) ((f.f 1 1 rfl) ⟨vec1 (kz I.z), vec1_mem _ _⟩) = I.zSel
    have hvec : (f.f 1 1 rfl) ⟨vec1 (kz I.z), vec1_mem _ _⟩ =
        ⟨vec1 (kz I.z), vec1_mem _ _⟩ := by
      apply Subtype.ext
      exact scale_disk2_vec1 _ _
    rw [hvec]
    exact I.hclass
  · intro y
    let y' : ((Fin I.n ⊕ Empty) ⊕ Unit) ⊕ Unit → R :=
      fun j => (disk2Units I.n (I.δ₂ * b⁻¹) (.inl (.inr j)) : R) * y j
    change I.lamSel ((I.φ.f 2 2 rfl) ((f.f 2 2 rfl) ⟨vec2 y, vec2_mem _ _⟩)) = kw I.w ⬝ᵥ y
    have hvec : (f.f 2 2 rfl) ⟨vec2 y, vec2_mem _ _⟩ = ⟨vec2 y', vec2_mem _ _⟩ := by
      apply Subtype.ext
      exact scale_disk2_vec2 _ _
    rw [hvec, I.hfun]
    exact kw_disk2 _ _ _

/-- The re-disked identification has the same Selmer class and functional. PROVED. -/
theorem redisk2_same [IsDomain R] {D : SelData R} (I : KummerModelIdentification D) (b : Rˣ) :
    (redisk2 I b).zSel = I.zSel ∧ (redisk2 I b).lamSel = I.lamSel := ⟨rfl, rfl⟩

end Redisk

section GenuineFixed

open ZInQ.Manuscript ZInQ.Manuscript.RC
attribute [local instance] Nat.fact_prime_two

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {M : Type}
  [AddCommGroup M] [Module (PowerSeries ℚ_[2]) M] [DistribMulAction (GKS K S) M]
  [SMulCommClass (GKS K S) (PowerSeries ℚ_[2]) M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul (PowerSeries ℚ_[2]) M]
  [ContinuousSMul (GKS K S) M]
  {Δ : GaloisLocalConditions K S (PowerSeries ℚ_[2]) M}

/-- **Recorded obstruction (any declared Tate–Shafarevich order).** From one fixed normalized
genuine identification (`a = b = u₀ = 1`, `δ₁ = δ₃ = 2^g`), a complete `KummerCoordinateBlock`
with declared orders `tA = 2^g`, `shaA = 2^s` for every `s`, over the same genuine Selmer data,
class and functional. -/
def manufactureShaBlock (hSfin : S.Finite)
    (hinj : ∀ v (k : ℤ), Function.Injective ((Δ.i v).f k k rfl))
    (I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ)
    (g : ℕ) (hd1 : I.δ₁ = twoPowUnit g) (hd3 : I.δ₃ = twoPowUnit g)
    (ha : I.a = 1) (hb : I.b = 1) (hu : I.u₀ = 1) (s : ℕ) :
    KummerCoordinateBlock K I.Dc
      ((((I.δ₁ * (twoPowUnit s)⁻¹ * I.δ₃ : (PowerSeries ℚ_[2])ˣ)) : PowerSeries ℚ_[2]) • I.z)
      I.w 0 0 1 (2 ^ g) (2 ^ s) := by
  let J := redisk2 I (twoPowUnit s)
  have disks : CentralDiskOrders J.δ₁ J.δ₂ J.δ₃ (2 ^ g) (2 ^ s) := by
    change CentralDiskOrders I.δ₁ (twoPowUnit s) I.δ₃ (2 ^ g) (2 ^ s)
    rw [hd1, hd3]
    exact centralDiskOrders_example g s
  refine KummerCoordinateBlock.ofCancellation S hSfin M Δ hinj J (Equiv.refl _) rfl rfl rfl
    1 1 ?_ ?_ ?_ ?_ ?_ disks
  · change I.a = PowerSeries.C (1 : ℚ_[2]) * 1
    simpa using ha
  · change I.b = PowerSeries.C (1 : ℚ_[2]) * 1
    simpa using hb
  · simp [central, v2]
  · simp [central, v2]
  · change v2 (central I.u₀) = 0
    simp [hu, central, v2]

/-- **Recorded obstruction**: the manufactured blocks have coordinate valuation `2g − s`.
PROVED. -/
theorem manufactured_sha_valuation (hSfin : S.Finite)
    (hinj : ∀ v (k : ℤ), Function.Injective ((Δ.i v).f k k rfl))
    (I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ)
    (g : ℕ) (hd1 : I.δ₁ = twoPowUnit g) (hd3 : I.δ₃ = twoPowUnit g)
    (ha : I.a = 1) (hb : I.b = 1) (hu : I.u₀ = 1)
    (hadj : I.Dc.adjugate ≠ 0) (s : ℕ) :
    v2 (central (manufactureShaBlock hSfin hinj I g hd1 hd3 ha hb hu s).I.coord) =
      ((2 * (g : ℤ) - (s : ℤ) : ℤ) : WithTop ℤ) := by
  let B := manufactureShaBlock hSfin hinj I g hd1 hd3 ha hb hu s
  have H := B.hK_eq (by decide) B.link hadj
  simpa [padicValNat.prime_pow] using H

end GenuineFixed

section Link

open ZInQ.Manuscript ZInQ.Manuscript.RC

/-- **Recorded obstruction (the field `link` is a coordinate equation)**: under
`z_K ⊗ w_K = u_K adj D_K` and `adj D_K ≠ 0`, `link` holds exactly when `u_K = I.coord`. PROVED. -/
theorem link_iff_uK_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {uK c : PowerSeries ℚ_[2]} (hKc : Central.IsClassFunctionalCoord DK zK wK uK)
    (hadj : DK.adjugate ≠ 0) :
    Central.IsClassFunctionalCoord DK zK wK c ↔ uK = c :=
  ⟨fun h => Central.isClassFunctionalCoord_unique hadj hKc h, fun h => h ▸ hKc⟩

/-- **Recorded obstruction (dimension one)**: the adjugate of a `1 × 1` matrix is `1`, so a block
with a one-dimensional core accepts any other differential. -/
def changeDifferential {K : Type} [Field K] [NumberField K]
    {DK : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])}
    {zK wK : Fin 1 → PowerSeries ℚ_[2]} {j vL m : ℤ} {tA shaA : ℕ}
    (B : KummerCoordinateBlock K DK zK wK j vL m tA shaA)
    (DK' : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])) :
    KummerCoordinateBlock K DK' zK wK j vL m tA shaA :=
  { B with
    link := by
      simpa only [Central.IsClassFunctionalCoord, adjugate_fin_one] using B.link }

/-- The differential of `changeDifferential` can be one for which the class is not a cycle.
PROVED. -/
theorem changeDifferential_not_cycle {K : Type} [Field K] [NumberField K]
    {DK : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])} {j vL m : ℤ} {tA shaA : ℕ}
    (B : KummerCoordinateBlock K DK (1 : Fin 1 → PowerSeries ℚ_[2]) 1 j vL m tA shaA) :
    Nonempty (KummerCoordinateBlock K (1 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2]))
      (1 : Fin 1 → PowerSeries ℚ_[2]) 1 j vL m tA shaA) ∧
    ¬ ((1 : Matrix (Fin 1) (Fin 1) (PowerSeries ℚ_[2])) *ᵥ
      (1 : Fin 1 → PowerSeries ℚ_[2]) = 0) := by
  refine ⟨⟨changeDifferential B 1⟩, ?_⟩
  rw [Matrix.one_mulVec]
  exact one_ne_zero

end Link

section LocalRecorded

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} {W : WeierstrassCurve K} [W.IsElliptic]
  {s : KS K S} {h : K} {hs : s ^ 2 = algebraMap K (KS K S) h} {hs0 : s ≠ 0}
  {hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)} {v : Places K S}
  {B : Matrix (Fin 2) (Fin 2) ℤ_[2]}

/-- **Recorded (the length inputs are local determinant valuations)**: for genuine local
presentations at every precision, the eventual order `2^{ℓ i}` of `H²` holds exactly when
`det B ≠ 0` and `v₂ det B = ℓ`. PROVED. -/
theorem genuine_length_iff_local_det
    (P : ∀ i : ℕ, PresentsLocalQuotient W i (centralChar i s hs hs0) v s hs hs0 (hFull i)
      (isLocallyQuadAt_centralChar i s hs hs0 v.1) B) (ell : ℕ) :
    (∃ i₀ : ℕ, ∀ i ≥ i₀,
      Nat.card (locH W i (centralChar i s hs hs0) v 2) = 2 ^ (ell * i)) ↔
      B.det ≠ 0 ∧ (B.det).valuation = ell := by
  constructor
  · intro H
    exact ⟨GenuineLengthBlockModel.det_ne_zero_of_length P H,
      GenuineLengthBlockModel.valuation_of_length P H⟩
  · rintro ⟨hdet, hval⟩
    refine ⟨max ell 1, fun i hi => ?_⟩
    have hi0 : i ≠ 0 := by omega
    have hv : (B.det).valuation ≤ i := by rw [hval]; omega
    simpa [hval] using (P i).card_locH2_eq hdet hi0 hv

end LocalRecorded

/-- **Recorded (the length model does not force a prime moving number)**: the moving number `r`
can be replaced by `r²`. -/
def compositeMovingNumber {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ}
    {hZ : ℤ} {κ : Type} [Fintype κ] [DecidableEq κ]
    {DW : Matrix κ κ (PowerSeries ℚ_[2])} {r ell omega : ℕ}
    (G : GenuineLengthBlockModel K E₀ hZ DW r ell omega) :
    GenuineLengthBlockModel K E₀ hZ DW (r * r) ell omega :=
  { G with
    hwmov := by
      simpa only [Nat.cast_mul] using (G.wmov.1.asIdeal.mul_mem_left (r : 𝓞 K) G.hwmov)
    hwmov' := by
      simpa only [Nat.cast_mul] using (G.wmov'.1.asIdeal.mul_mem_left (r : 𝓞 K) G.hwmov') }

end Recorded

/-! ### The genuine finite-level Kummer Selmer complexes and the integral disk lengths -/

section DiskLengths

open ZInQ.Manuscript ZInQ.Manuscript.RC

/-- **The genuine finite-level Kummer Selmer data at precision `i`** (tex 3455–3463, 3413–3438):
the coefficient module `M_i = (E[2^i] ⊗ A_i)(χ_h)` with the central character and the actual
Kummer condition (genuine coefficient map through the twist identification) at every place of `S`
(the local Kummer maps' `kummerSelData`). -/
def centralKummerSelData {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
    (W : WeierstrassCurve K) [W.IsElliptic] (s : KS K S) {h : K}
    (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0)
    (hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)) (i : ℕ) : SelData (Acoef i) :=
  kummerSelData (subset_refl S) W i s hs hs0 (centralChar i s hs hs0) (hFull i) S
    (fun v _ => isLocallyQuadAt_centralChar i s hs hs0 v) (fun v _ hP => absurd v.2 hP)

/-- **The genuine data of the address for the Kummer complexes**: the finite Selmer support, the
curve `E_K` (the base change of the fixed curve), a square root of `h` in `K_S`, and full
`2`-power torsion over `K_S` (so `S` contains the places above `2` and of bad reduction). -/
structure GenuineKummerData (K : Type) [Field K] [NumberField K] (E₀ : WeierstrassCurve ℚ)
    (hZ : ℤ) where
  /-- the finite set of places of the Selmer complexes -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- it is finite -/
  hSfin : S.Finite
  /-- the curve `E` over `K` -/
  W : WeierstrassCurve K
  [ellW : W.IsElliptic]
  /-- it is the base change of the fixed curve -/
  hW : W = E₀.baseChange K
  /-- a square root of `h` in `K_S` -/
  s : KS K S
  /-- `s² = h` -/
  hs : s ^ 2 = algebraMap K (KS K S) (hZ : K)
  /-- `s ≠ 0` -/
  hs0 : s ≠ 0
  /-- `E[2^i] ⊂ E(K_S)` at every precision -/
  hFull : ∀ i : ℕ, FullTorsion K S W (2 ^ i)

attribute [instance] GenuineKummerData.ellW

namespace GenuineKummerData

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}

/-- `Hⁿ` of the genuine finite-level Kummer Selmer complex at precision `i`. -/
abbrev selH (G : GenuineKummerData K E₀ hZ) (i : ℕ) (n : ℤ) : ModuleCat (Acoef i) :=
  (selCx (centralKummerSelData G.W G.s G.hs G.hs0 G.hFull i)).toCC.homology n

end GenuineKummerData

/-- The order `|A_i/(x)|` of the reduction to `A_i` of the cyclic module `ℤ₂/(x)`. -/
abbrev cycOrder (i : ℕ) (x : ℤ_[2]) : ℕ := Nat.card (Acoef i ⧸ Ideal.span {constRed i x})

/-- `|A_i/(x)| = 2^{i · v₂ x}` for `x ≠ 0` and `v₂ x ≤ i`. PROVED. -/
theorem cycOrder_eq {i : ℕ} (hi : i ≠ 0) {x : ℤ_[2]} (hx : x ≠ 0) (hv : x.valuation ≤ i) :
    cycOrder i x = 2 ^ (x.valuation * i) := by
  have hspan : (Ideal.span {constRed i x} : Ideal (Acoef i)) =
      Ideal.span {(2 : Acoef i) ^ x.valuation} := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    rw [map_mul, map_pow, map_natCast, Nat.cast_ofNat]
    exact Ideal.span_singleton_mul_left_unit ((PadicInt.unitCoeff hx).isUnit.map _) _
  rw [cycOrder, hspan, card_acoef_quot i _ hi hv]

/-- A precision large enough for finitely many conditions. -/
theorem two_pow_mul_inj {a b i : ℕ} (hi : i ≠ 0) (h : 2 ^ (a * i) = 2 ^ (b * i)) : a = b :=
  Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) (Nat.pow_right_injective (le_refl 2) h)

/-- **The integral Kummer model computes the orders of the genuine finite-level Kummer Selmer
cohomology** (tex 3429–3431, 4005–4018, 4057–4060; the order form of the derived reduction of the
integral central Kummer model): for all large `i`, `|H⁰| = |A_i/(x₁)|`,
`|H²| = 2^{i·i} |A_i/(x₂)| |A_i/(x₃)|` (the core has free degree-two cohomology of rank one),
`|H³| = |A_i/(x₃)|`, for the central values `x₁, x₂, x₃` of the three disks. -/
structure DiskTie {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
    (G : GenuineKummerData K E₀ hZ) (x₁ x₂ x₃ : ℤ_[2]) : Prop where
  /-- degree zero: the degree-one disk -/
  tie0 : ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 0) = cycOrder i x₁
  /-- degree two: the free part, the degree-two disk and the degree-three disk -/
  tie2 : ∃ i₀ : ℕ, ∀ i ≥ i₀,
    Nat.card (G.selH i 2) = 2 ^ (i * i) * cycOrder i x₂ * cycOrder i x₃
  /-- degree three: the degree-three disk -/
  tie3 : ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 3) = cycOrder i x₃

/-- **The genuine orders are those of the actual groups** (ELLIOT, tex 4005–4018: universal
coefficients and the degree-zero identifications, `H¹(C_K)_tors = 𝒜(ℚ)_tors[2^∞]`,
`H²(C_K)_tors = Ш(𝒜)[2^∞]` for finite `Ш`, self-duality): for all large `i`,
`|H⁰| = 2^{i v₂ tA}`, `|H²| = 2^{i (i + v₂ shaA + v₂ tA)}`, `|H³| = 2^{i v₂ tA}`. -/
structure DiskArith {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
    (G : GenuineKummerData K E₀ hZ) (tA shaA : ℕ) : Prop where
  /-- `H⁰` is the actual rational torsion, at precision `i` -/
  arith0 : ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 0) = 2 ^ (padicValNat 2 tA * i)
  /-- `H²`: the free part, the actual `Ш` and the dual torsion, at precision `i` -/
  arith2 : ∃ i₀ : ℕ, ∀ i ≥ i₀,
    Nat.card (G.selH i 2) = 2 ^ ((i + padicValNat 2 shaA + padicValNat 2 tA) * i)
  /-- `H³` is the dual of the actual torsion, at precision `i` -/
  arith3 : ∃ i₀ : ℕ, ∀ i ≥ i₀, Nat.card (G.selH i 3) = 2 ^ (padicValNat 2 tA * i)

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}
  {G : GenuineKummerData K E₀ hZ}

/-- **The disk lengths are read from the genuine Selmer complexes**: `v₂ x₁ = v₂ x₃ = v₂ tA` and
`v₂ x₂ = v₂ shaA`. PROVED. -/
theorem DiskTie.valuations {x₁ x₂ x₃ : ℤ_[2]} (T : DiskTie G x₁ x₂ x₃) {tA shaA : ℕ}
    (A : DiskArith G tA shaA) (h₁ : x₁ ≠ 0) (h₂ : x₂ ≠ 0) (h₃ : x₃ ≠ 0) :
    x₁.valuation = padicValNat 2 tA ∧ x₂.valuation = padicValNat 2 shaA ∧
      x₃.valuation = padicValNat 2 tA := by
  obtain ⟨a, ha⟩ := T.tie0
  obtain ⟨b, hb⟩ := T.tie2
  obtain ⟨c, hc⟩ := T.tie3
  obtain ⟨d, hd⟩ := A.arith0
  obtain ⟨e, he⟩ := A.arith2
  obtain ⟨f, hf⟩ := A.arith3
  set i := a + b + c + d + e + f + x₁.valuation + x₂.valuation + x₃.valuation + 1 with hidef
  have hi : i ≠ 0 := by omega
  have v1 : x₁.valuation = padicValNat 2 tA := by
    have h := (ha i (by omega)).symm.trans (hd i (by omega))
    rw [cycOrder_eq hi h₁ (by omega)] at h
    exact two_pow_mul_inj hi h
  have v3 : x₃.valuation = padicValNat 2 tA := by
    have h := (hc i (by omega)).symm.trans (hf i (by omega))
    rw [cycOrder_eq hi h₃ (by omega)] at h
    exact two_pow_mul_inj hi h
  refine ⟨v1, ?_, v3⟩
  have h := (hb i (by omega)).symm.trans (he i (by omega))
  rw [cycOrder_eq hi h₂ (by omega), cycOrder_eq hi h₃ (by omega), ← pow_add, ← pow_add] at h
  have h' := Nat.pow_right_injective (le_refl 2) h
  have h'' : (i + x₂.valuation + x₃.valuation) * i =
      (i + padicValNat 2 shaA + padicValNat 2 tA) * i := by
    rw [← h']; ring
  have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h''
  omega

/-- **For fixed genuine Selmer complexes the disk lengths are determined**: two integral models
computing the same genuine finite-level Kummer Selmer cohomology have the same disk valuations (so
a degree-two disk of arbitrary order cannot be chosen). PROVED. -/
theorem DiskTie.determined {x₁ x₂ x₃ y₁ y₂ y₃ : ℤ_[2]} (T : DiskTie G x₁ x₂ x₃)
    (T' : DiskTie G y₁ y₂ y₃) (hx₁ : x₁ ≠ 0) (hx₂ : x₂ ≠ 0) (hx₃ : x₃ ≠ 0) (hy₁ : y₁ ≠ 0)
    (hy₂ : y₂ ≠ 0) (hy₃ : y₃ ≠ 0) :
    x₁.valuation = y₁.valuation ∧ x₂.valuation = y₂.valuation ∧
      x₃.valuation = y₃.valuation := by
  obtain ⟨a, ha⟩ := T.tie0
  obtain ⟨b, hb⟩ := T.tie2
  obtain ⟨c, hc⟩ := T.tie3
  obtain ⟨d, hd⟩ := T'.tie0
  obtain ⟨e, he⟩ := T'.tie2
  obtain ⟨f, hf⟩ := T'.tie3
  set i := a + b + c + d + e + f + x₁.valuation + x₂.valuation + x₃.valuation + y₁.valuation +
    y₂.valuation + y₃.valuation + 1 with hidef
  have hi : i ≠ 0 := by omega
  have v1 : x₁.valuation = y₁.valuation := by
    have h := (ha i (by omega)).symm.trans (hd i (by omega))
    rw [cycOrder_eq hi hx₁ (by omega), cycOrder_eq hi hy₁ (by omega)] at h
    exact two_pow_mul_inj hi h
  have v3 : x₃.valuation = y₃.valuation := by
    have h := (hc i (by omega)).symm.trans (hf i (by omega))
    rw [cycOrder_eq hi hx₃ (by omega), cycOrder_eq hi hy₃ (by omega)] at h
    exact two_pow_mul_inj hi h
  refine ⟨v1, ?_, v3⟩
  have h := (hb i (by omega)).symm.trans (he i (by omega))
  rw [cycOrder_eq hi hx₂ (by omega), cycOrder_eq hi hx₃ (by omega), cycOrder_eq hi hy₂ (by omega),
    cycOrder_eq hi hy₃ (by omega), ← pow_add, ← pow_add, ← pow_add, ← pow_add] at h
  have h' := Nat.pow_right_injective (le_refl 2) h
  have h'' : (i + x₂.valuation + x₃.valuation) * i = (i + y₂.valuation + y₃.valuation) * i := by
    have e1 : i * i + x₂.valuation * i + x₃.valuation * i =
        (i + x₂.valuation + x₃.valuation) * i := by ring
    have e2 : i * i + y₂.valuation * i + y₃.valuation * i =
        (i + y₂.valuation + y₃.valuation) * i := by ring
    rw [← e1, ← e2]; exact h'
  have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) h''
  omega

/-- **The Tate–Shafarevich and torsion exponents are determined by the genuine Selmer
complexes**: two arithmetic identifications over the same genuine complexes have the same
`v₂ tA` and `v₂ shaA`. PROVED. -/
theorem DiskArith.determined {tA shaA tA' shaA' : ℕ} (A : DiskArith G tA shaA)
    (A' : DiskArith G tA' shaA') :
    padicValNat 2 tA = padicValNat 2 tA' ∧ padicValNat 2 shaA = padicValNat 2 shaA' := by
  obtain ⟨b, hb⟩ := A.arith2
  obtain ⟨c, hc⟩ := A.arith3
  obtain ⟨e, he⟩ := A'.arith2
  obtain ⟨f, hf⟩ := A'.arith3
  set i := b + c + e + f + 1 with hidef
  have hi : i ≠ 0 := by omega
  have v3 := two_pow_mul_inj hi ((hc i (by omega)).symm.trans (hf i (by omega)))
  refine ⟨v3, ?_⟩
  have h := two_pow_mul_inj hi ((hb i (by omega)).symm.trans (he i (by omega)))
  omega

end DiskLengths

/-! ### The Kummer block with the disk lengths read from the genuine Selmer complexes -/

section BlockG

open ZInQ.Manuscript ZInQ.Manuscript.RC
attribute [local instance] Nat.fact_prime_two

/-- **The Kummer block, with integral disk lengths read from the genuine finite-level Kummer
Selmer complexes** (tex 3877–3909, 4005–4018, 4050–4064). As `KummerCoordinateBlock`, with the
free disk orders `disks` replaced by the integral central values `x₁, x₂, x₃` of the three disks,
the genuine data of the address (`G`: the curve `E_K` and the twist `h`), the order tie `tie`
(the integral central Kummer model computes the orders of the genuine finite-level Kummer Selmer
cohomology) and the arithmetic identification `arith` (the genuine orders are those of the actual
torsion and `Ш`).

| field | content | tex | kind |
|---|---|---|---|
| `S` … `I` | the Knudsen–Mumford identification over `ℚ₂[[t]]` (coefficient module and local conditions over `ℚ₂[[t]]` not tied to the curve: no limit Kummer complex over `ℚ₂[[t]]` is available) | 3877–3892, 4057–4060 | GLUE |
| `link` | coordinate transfer `u_K = I.coord` (`Recorded.link_iff_uK_eq`), not an identification of the two-term model | 3889–3890 | GLUE |
| `aP` … `hu₀` | the free coefficients of the class and the functional | 3898–3906, 4061–4064 | ELLIOT |
| `G`, `x₁`–`x₃`, `hx₁`–`hx₃`, `tie` | the integral central disks compute the orders of the genuine finite-level Kummer Selmer cohomology of the address | 3429–3431, 4005–4018 | GLUE (integral model) |
| `arith` | the genuine orders are those of `𝒜(ℚ)_tors[2^∞]`, `Ш(𝒜)[2^∞]` | 4005–4018 | ELLIOT |
-/
structure KummerCoordinateBlockG (K : Type) [Field K] [NumberField K] (E₀ : WeierstrassCurve ℚ)
    (hZ : ℤ) {n : ℕ} (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2]))
    (zK wK : Fin n → PowerSeries ℚ_[2]) (j vL m : ℤ) (tA shaA : ℕ) : Type 1 where
  /-- the finite set of places of the Selmer complex over `ℚ₂[[t]]` -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- it is finite -/
  hSfin : S.Finite
  /-- the coefficient module over `ℚ₂[[t]]` -/
  M : Type
  [addM : AddCommGroup M]
  [modM : Module (PowerSeries ℚ_[2]) M]
  [actM : DistribMulAction (GKS K S) M]
  [commM : SMulCommClass (GKS K S) (PowerSeries ℚ_[2]) M]
  [topM : TopologicalSpace M]
  [caddM : ContinuousAdd M]
  [cconstM : ContinuousConstSMul (PowerSeries ℚ_[2]) M]
  [csmulM : ContinuousSMul (GKS K S) M]
  /-- the local conditions over `ℚ₂[[t]]` -/
  Δ : GaloisLocalConditions K S (PowerSeries ℚ_[2]) M
  /-- they are subcomplexes of the local cochains -/
  hinj : ∀ v (k : ℤ), Function.Injective ((Δ.i v).f k k rfl)
  /-- the Knudsen–Mumford identification over `ℚ₂[[t]]` -/
  I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ
  /-- the coordinate transfer to the leaf's two-term model -/
  link : Central.IsClassFunctionalCoord DK zK wK I.coord
  /-- the free coefficient of the point in the class -/
  aP : PowerSeries ℚ_[2]
  /-- the free coefficient of the point in the functional -/
  bP : PowerSeries ℚ_[2]
  /-- the class coefficient is `m · a_P` -/
  ha : I.a = PowerSeries.C (m : ℚ_[2]) * aP
  /-- the functional coefficient is `m · b_P` -/
  hb : I.b = PowerSeries.C (m : ℚ_[2]) * bP
  /-- `v₂ a_P(0) = j_rc + v₂L` -/
  haP : v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ)
  /-- `v₂ b_P(0) = j_rc + v₂L` -/
  hbP : v2 (central bP) = ((j + vL : ℤ) : WithTop ℤ)
  /-- the core coordinate is a unit at the centre -/
  hu₀ : v2 (central I.u₀) = 0
  /-- the genuine data of the address -/
  G : GenuineKummerData K E₀ hZ
  /-- the central value of the degree-one disk -/
  x₁ : ℤ_[2]
  /-- the central value of the degree-two disk -/
  x₂ : ℤ_[2]
  /-- the central value of the degree-three disk -/
  x₃ : ℤ_[2]
  /-- the degree-one disk is integral at the centre -/
  hx₁ : central (I.δ₁ : PowerSeries ℚ_[2]) = x₁
  /-- the degree-two disk is integral at the centre -/
  hx₂ : central (I.δ₂ : PowerSeries ℚ_[2]) = x₂
  /-- the degree-three disk is integral at the centre -/
  hx₃ : central (I.δ₃ : PowerSeries ℚ_[2]) = x₃
  /-- the integral central model computes the genuine finite-level Kummer Selmer orders -/
  tie : DiskTie G x₁ x₂ x₃
  /-- the genuine orders are those of the actual torsion and `Ш` -/
  arith : DiskArith G tA shaA

attribute [instance] KummerCoordinateBlockG.addM KummerCoordinateBlockG.modM
  KummerCoordinateBlockG.actM KummerCoordinateBlockG.commM KummerCoordinateBlockG.topM
  KummerCoordinateBlockG.caddM KummerCoordinateBlockG.cconstM KummerCoordinateBlockG.csmulM

namespace KummerCoordinateBlockG

variable {K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ} {n : ℕ}
  {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
  {j vL m : ℤ} {tA shaA : ℕ}

/-- **The central disk valuations are the genuine lengths**: `v₂ δ₁(0) = v₂ δ₃(0) = v₂ tA`,
`v₂ δ₂(0) = v₂ shaA`. PROVED. -/
theorem disk_valuations (B : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA) :
    v2 (central (B.I.δ₁ : PowerSeries ℚ_[2])) = (((padicValNat 2 tA : ℕ) : ℤ) : WithTop ℤ) ∧
      v2 (central (B.I.δ₂ : PowerSeries ℚ_[2])) = (((padicValNat 2 shaA : ℕ) : ℤ) : WithTop ℤ) ∧
      v2 (central (B.I.δ₃ : PowerSeries ℚ_[2])) = (((padicValNat 2 tA : ℕ) : ℤ) : WithTop ℤ) := by
  have h₁ := CentralDiskOrders.x_ne_zero B.hx₁
  have h₂ := CentralDiskOrders.x_ne_zero B.hx₂
  have h₃ := CentralDiskOrders.x_ne_zero B.hx₃
  obtain ⟨v1, v2', v3⟩ := B.tie.valuations B.arith h₁ h₂ h₃
  refine ⟨?_, ?_, ?_⟩
  · rw [B.hx₁, v2_coe_padicInt _ h₁, v1]
  · rw [B.hx₂, v2_coe_padicInt _ h₂, v2']
  · rw [B.hx₃, v2_coe_padicInt _ h₃, v3]

/-- `v₂ a(0) = j + v₂L + v₂ m`. PROVED. -/
theorem v2_a (B : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    v2 (central B.I.a) = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hC : central (PowerSeries.C (m : ℚ_[2])) = (m : ℚ_[2]) := by simp [central]
  rw [B.ha, ZInQ.Contrib.CloudB3RC53.Calibration.central_mul,
    ZInQ.Contrib.CloudB3RC53.Calibration.v2_mul, hC,
    ZInQ.Contrib.CloudB3RC53.Calibration.v2_intCast hm, B.haP, ← WithTop.coe_add]
  congr 1
  ring

/-- `v₂ b(0) = j + v₂L + v₂ m`. PROVED. -/
theorem v2_b (B : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    v2 (central B.I.b) = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hC : central (PowerSeries.C (m : ℚ_[2])) = (m : ℚ_[2]) := by simp [central]
  rw [B.hb, ZInQ.Contrib.CloudB3RC53.Calibration.central_mul,
    ZInQ.Contrib.CloudB3RC53.Calibration.v2_mul, hC,
    ZInQ.Contrib.CloudB3RC53.Calibration.v2_intCast hm, B.hbP, ← WithTop.coe_add]
  congr 1
  ring

/-- **The field `hK` of the calibration leaf, in its exact form**, from the block with the disk
lengths read from the genuine Selmer complexes (conditional on the GLUE identification `I`, the
coordinate transfer `link`, the ELLIOT free coefficients and arithmetic orders). PROVED. -/
theorem hK (B : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA) (hm : m ≠ 0)
    {uK : PowerSeries ℚ_[2]} (hKc : Central.IsClassFunctionalCoord DK zK wK uK)
    (hadj : DK.adjugate ≠ 0) :
    v2 (central uK) =
      (((j + vL + ((padicValInt 2 m : ℕ) : ℤ)) + (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) +
        (Central.diskContribution 1 ((padicValNat 2 tA : ℕ) : ℤ) +
          Central.diskContribution 2 ((padicValNat 2 shaA : ℕ) : ℤ) +
          Central.diskContribution 3 ((padicValNat 2 tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [Central.isClassFunctionalCoord_unique hadj hKc B.link]
  obtain ⟨d1, d2, d3⟩ := B.disk_valuations
  exact hK_of_identification B.I j vL ((padicValInt 2 m : ℕ) : ℤ) ((padicValNat 2 tA : ℕ) : ℤ)
    ((padicValNat 2 shaA : ℕ) : ℤ) B.hu₀ (B.v2_a hm) (B.v2_b hm) d1 d2 d3

/-- **Two blocks over the same genuine data have the same central disk valuations**: a
degree-two disk of arbitrary order (`Recorded.manufactureShaBlock`) is excluded. PROVED. -/
theorem disk_valuations_determined {n' : ℕ}
    {DK' : Matrix (Fin n') (Fin n') (PowerSeries ℚ_[2])} {zK' wK' : Fin n' → PowerSeries ℚ_[2]}
    {j' vL' m' : ℤ} {tA' shaA' : ℕ}
    (B : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA)
    (B' : KummerCoordinateBlockG K E₀ hZ DK' zK' wK' j' vL' m' tA' shaA') (hG : B.G = B'.G) :
    v2 (central (B.I.δ₁ : PowerSeries ℚ_[2])) = v2 (central (B'.I.δ₁ : PowerSeries ℚ_[2])) ∧
      v2 (central (B.I.δ₂ : PowerSeries ℚ_[2])) =
        v2 (central (B'.I.δ₂ : PowerSeries ℚ_[2])) ∧
      v2 (central (B.I.δ₃ : PowerSeries ℚ_[2])) =
        v2 (central (B'.I.δ₃ : PowerSeries ℚ_[2])) := by
  have T' : DiskTie B.G B'.x₁ B'.x₂ B'.x₃ := by rw [hG]; exact B'.tie
  have h₁ := CentralDiskOrders.x_ne_zero B.hx₁
  have h₂ := CentralDiskOrders.x_ne_zero B.hx₂
  have h₃ := CentralDiskOrders.x_ne_zero B.hx₃
  have h₁' := CentralDiskOrders.x_ne_zero B'.hx₁
  have h₂' := CentralDiskOrders.x_ne_zero B'.hx₂
  have h₃' := CentralDiskOrders.x_ne_zero B'.hx₃
  obtain ⟨e1, e2, e3⟩ := B.tie.determined T' h₁ h₂ h₃ h₁' h₂' h₃'
  refine ⟨?_, ?_, ?_⟩
  · rw [B.hx₁, B'.hx₁, v2_coe_padicInt _ h₁, v2_coe_padicInt _ h₁', e1]
  · rw [B.hx₂, B'.hx₂, v2_coe_padicInt _ h₂, v2_coe_padicInt _ h₂', e2]
  · rw [B.hx₃, B'.hx₃, v2_coe_padicInt _ h₃, v2_coe_padicInt _ h₃', e3]

/-- **Two blocks over the same genuine data declare the same torsion and `Ш` exponents.**
PROVED. -/
theorem exponents_determined {n' : ℕ}
    {DK' : Matrix (Fin n') (Fin n') (PowerSeries ℚ_[2])} {zK' wK' : Fin n' → PowerSeries ℚ_[2]}
    {j' vL' m' : ℤ} {tA' shaA' : ℕ}
    (B : KummerCoordinateBlockG K E₀ hZ DK zK wK j vL m tA shaA)
    (B' : KummerCoordinateBlockG K E₀ hZ DK' zK' wK' j' vL' m' tA' shaA') (hG : B.G = B'.G) :
    padicValNat 2 tA = padicValNat 2 tA' ∧ padicValNat 2 shaA = padicValNat 2 shaA' := by
  have A' : DiskArith B.G tA' shaA' := by rw [hG]; exact B'.arith
  exact B.arith.determined A'

end KummerCoordinateBlockG

end BlockG

/-! ### The moving prime -/

section Moving

/-- **The moving prime, tied to the curve** (tex 4066–4075): `r` is prime, `r ∤ 6hℓ` (good
reduction of `E` and of `E^{(h)}` at `r`), `a_r = r + 1 − |Ẽ(𝔽_r)|` for the integral model
`y² = x³ + 2ℓx² − 3ℓ²x` of `E`, and `χ = (h/r)`, the quadratic Frobenius sign. -/
structure MovingPrimeData (ℓ : ℕ) (hZ : ℤ) (rmov : ℕ) (amov chimov : ℤ) : Prop where
  /-- `r` is prime -/
  hprime : rmov.Prime
  /-- `r ∤ 6hℓ` -/
  hgood : ¬ ((rmov : ℤ) ∣ 6 * hZ * ℓ)
  /-- `a_r` is the Frobenius trace of `E` at `r` -/
  htrace : amov = (rmov : ℤ) + 1 - (Nat.card
    (((ZInQ.Contrib.CloudB3RC53.Calibration.E0Z ℓ 1).map
      (Int.castRingHom (ZMod rmov))).toAffine.Point) : ℤ)
  /-- `χ_h(r)` is the Legendre symbol `(h/r)` -/
  hsign : chimov = @legendreSym rmov ⟨hprime⟩ hZ

/-- The integral model `y² = x³ + 2ℓx² − 3ℓ²x` used in `MovingPrimeData` is a model of `E`.
PROVED. -/
theorem E0Z_one_map (ℓ : ℕ) :
    (ZInQ.Contrib.CloudB3RC53.Calibration.E0Z ℓ 1).map (Int.castRingHom ℚ) =
      ZInQ.Contrib.CloudB3RC53.Ecurve ℓ := by
  rw [ZInQ.Contrib.CloudB3RC53.Calibration.E0Z_map]
  ext
  all_goals simp [ZInQ.Contrib.CloudB3RC53.qtwist, ZInQ.Contrib.CloudB3RC53.Ecurve,
    ZInQ.Manuscript.curve, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
  ring

namespace MovingPrimeData

variable {ℓ : ℕ} {hZ : ℤ} {rmov : ℕ} {amov chimov : ℤ}

/-- The quadratic Frobenius sign is `±1` (`r ∤ h`). PROVED. -/
theorem chimov_sign (H : MovingPrimeData ℓ hZ rmov amov chimov) : chimov = 1 ∨ chimov = -1 := by
  have : Fact rmov.Prime := ⟨H.hprime⟩
  have hh : ((hZ : ZMod rmov)) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hd
    exact H.hgood (Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 6) _)
  rw [H.hsign]
  exact legendreSym.eq_one_or_neg_one rmov hh

/-- The moving prime is odd (`r ∤ 6`). PROVED. -/
theorem odd (H : MovingPrimeData ℓ hZ rmov amov chimov) : Odd rmov := by
  rcases H.hprime.eq_two_or_odd' with h2 | hodd
  · exfalso
    apply H.hgood
    rw [h2]
    exact ⟨3 * hZ * ℓ, by push_cast; ring⟩
  · exact hodd

end MovingPrimeData

end Moving

/-! ### The calibration leaves -/

section Leaves

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.Calibration
open ZInQ.Manuscript.RC.Wiring
open WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

attribute [local instance] Nat.fact_prime_two

/-- **The inputs of (4.6) at one address, with the Kummer disk lengths read from the genuine
Selmer complexes** (tex 3987–4141): every field of `CalibrationModelH` except `hK`, with the same
names and types, and `kummer : KummerCoordinateBlockG …` in place of `hK`. -/
structure CalibrationModelHK2 {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
  /-- `|Ш(𝒜)[2^∞]|` -/
  shaA : ℕ
  /-- `|Ш(ℬ)[2^∞]|` -/
  shaB : ℕ
  /-- `|𝒜(ℚ)_tors[2^∞]|` -/
  tA : ℕ
  /-- `|ℬ(ℚ)_tors[2^∞]|` -/
  tB : ℕ
  /-- finiteness of `Ш(𝒜)` -/
  shaA_ne : shaA ≠ 0
  /-- finiteness of `Ш(ℬ)` -/
  shaB_ne : shaB ≠ 0
  /-- `𝒜` has torsion -/
  tA_ne : tA ≠ 0
  /-- `ℬ` has torsion -/
  tB_ne : tB ≠ 0
  /-- the finite set of primes carrying the component numbers -/
  Scomp : Finset ℕ
  /-- the component numbers of `𝒜` -/
  cA : ℕ → ℕ
  /-- the component numbers of `ℬ` -/
  cB : ℕ → ℕ
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- the companion primes are odd -/
  hodd : ∀ p ∈ D.kfin.natAbs.primeFactors, p ≠ 2
  /-- the companion primes exactly divide `k` -/
  hram : ∀ p ∈ D.kfin.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ D.kfin)
  /-- `E₀ = E^{(h_x)}` has good reduction at each companion prime (a good integral model up to
  isomorphism) -/
  goodModel : ∀ p ∈ D.kfin.natAbs.primeFactors, GoodModelIso (qtwist (Ecurve ℓ) (Fam.h x : ℚ)) p
  /-- **PRINT (Edixhoven, Thm 5.3 and Rem 5.4.1) as GLUE**, model-free form -/
  hEdix : EdixhovenComponentNumberIso ℓ (Fam.h x : ℚ) D.kfin cB
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : QuadData K (D.kfin : ℚ)
  /-- `φ^*ω_ℬ = a ω_𝒜` -/
  aPull : ℤ
  /-- `ψ^*ω_𝒜 = b ω_ℬ` -/
  bPull : ℤ
  /-- `ab = 4` -/
  hab : aPull * bPull = 4
  /-- `|coker φ_ℝ|` -/
  gam : ℕ
  /-- `|ker φ_ℝ|` -/
  kap : ℕ
  /-- both at most four -/
  hgam : 1 ≤ gam ∧ gam ≤ 4
  /-- both at most four -/
  hkap : 1 ≤ kap ∧ kap ≤ 4
  /-- the Néron period of `𝒜` -/
  OmA : ℝ
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators of any free
  generators of the two rank-one lattices -/
  hmilne : ∀ (gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point)
    (gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point),
    IsFreeGenerator gA → IsFreeGenerator gB →
    Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
      (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
      (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
      ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℕ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- the constant `c_E` of the Tate image -/
  cE : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ (rmov : ℤ) - 1
  /-- `2^{c_E + 1} ∤ a_{r_i} − 2χ` (the non-divisibility of the moving-prime construction) -/
  hnd : ¬ (2 : ℤ) ^ (cE + 1) ∣ amov - 2 * chimov
  /-- `B_i ≥ c_E + 1` -/
  hcB : cE + 1 ≤ Bexp
  /-- the size of the Kummer two-term model -/
  nK : ℕ
  /-- the index set of the quotient block -/
  κ : Type
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  /-- the Kummer differential -/
  DK : Matrix (Fin nK) (Fin nK) (PowerSeries ℚ_[2])
  /-- the off-diagonal block of the relaxation -/
  X : Matrix (Fin nK) κ (PowerSeries ℚ_[2])
  /-- the quotient block at the moving and active places -/
  DW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the Kummer class -/
  zK : Fin nK → PowerSeries ℚ_[2]
  /-- the Kummer functional -/
  wK : Fin nK → PowerSeries ℚ_[2]
  /-- the primitive class -/
  zP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the primitive functional -/
  wP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the Kummer coordinate -/
  uK : PowerSeries ℚ_[2]
  /-- the primitive class restricts to the Kummer class -/
  hz : ∀ i, zP (Sum.inl i) = zK i
  /-- the primitive functional restricts to the Kummer functional -/
  hw : ∀ i, wP (Sum.inl i) = wK i
  /-- `u_prim` is the coordinate of the primitive model -/
  hP : CommonCoordinate.IsCoordOn (fromBlocks DK X 0 DW) zP wP (D.uPrim Fam x)
  /-- `u_K` is the coordinate of the Kummer model -/
  hKc : Central.IsClassFunctionalCoord DK zK wK uK
  /-- The Kummer differential has nonzero adjugate; this is weaker than
  saying that its generic cohomology has dimensions (1,1). -/
  hadj : DK.adjugate ≠ 0
  /-- **the Kummer block with the disk lengths read from the genuine Selmer complexes**; it
  replaces the field `hK`, which is derived -/
  kummer : KummerCoordinateBlockG K (Ecurve ℓ) (Fam.h x) DK zK wK (D.jrc (Fam.h x) D.kfin) vL
    (amov - 2 * chimov) tA shaA
  /-- the Frobenius at the moving prime, over `ℚ₂[[t]]` -/
  Fr : Matrix (Fin 2) (Fin 2) (PowerSeries ℚ_[2])
  /-- its central value has trace `a_{r_i}` -/
  hFtr : (Fr.map central).trace = (amov : ℚ_[2])
  /-- its central value has determinant `r_i` -/
  hFdet : (Fr.map central).det = (rmov : ℚ_[2])
  /-- the change of basis on the left -/
  PW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the change of basis on the right -/
  QW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the relabelling of the quotient block by the two moving places and the active places -/
  eW : κ ≃ (Fin 2 ⊕ Fin 2) ⊕ Fin (4 * omega (Fam.h x))
  /-- the moving scalar at the first place above `r_i` -/
  zmov : PowerSeries ℚ_[2]
  /-- the moving scalar at the second place above `r_i` -/
  zmov' : PowerSeries ℚ_[2]
  /-- the block at the active places -/
  Bact : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x))) (PowerSeries ℚ_[2])
  /-- the quotient block is the direct sum of the local blocks, up to the changes of basis -/
  hDW : DW = PW * (fromBlocks (CommonCoordinate.twoPlaceBlock Fr (rmov : PowerSeries ℚ_[2]) zmov
    zmov') 0 0 Bact).submatrix eW eW * QW
  /-- the left change of basis has a unit determinant at the centre -/
  hPW : v2 (central PW.det) = 0
  /-- the right change of basis has a unit determinant at the centre -/
  hQW : v2 (central QW.det) = 0
  /-- the moving character is trivial at the centre: the first scalar is `χ_h(r_i)` -/
  hzmov : central zmov = chimov
  /-- the second scalar is `χ_h(r_i)` at the centre -/
  hzmov' : central zmov' = chimov
  /-- the active block is the minimal model `2 · 1` of `E[2]` at the centre -/
  hact : Bact.map central =
    (2 : ℚ_[2]) • (1 : Matrix (Fin (4 * omega (Fam.h x))) (Fin (4 * omega (Fam.h x))) ℚ_[2])

attribute [instance] CalibrationModelHK2.fieldK CalibrationModelHK2.nfK CalibrationModelHK2.decK
  CalibrationModelHK2.quadK CalibrationModelHK2.fκ CalibrationModelHK2.dκ

namespace CalibrationModelHK2

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- `m = a_r − 2χ_h(r) ≠ 0`. PROVED. -/
theorem m_ne_zero (M : CalibrationModelHK2 D vL G₀ Fam x) : M.amov - 2 * M.chimov ≠ 0 := by
  intro h0
  exact M.hnd (by rw [h0]; exact dvd_zero _)

/-- **`CalibrationModelH` from `CalibrationModelHK2`**: `hK` from `KummerCoordinateBlockG.hK`.
PROVED. -/
def toModelH (M : CalibrationModelHK2 D vL G₀ Fam x) : CalibrationModelH D vL G₀ Fam x :=
  { M with hK := M.kummer.hK M.m_ne_zero M.hKc M.hadj }

end CalibrationModelHK2

/-- The inputs with `CalibrationModelHK2` at every address. -/
def CalibrationInputsHK2 {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelHK2 D vL G₀ F x)

/-- **`RCSteps.calibration` from `CalibrationInputsHK2`** ((4.6), tex 3987–4141). PROVED. -/
theorem calibrationTarget_of_HK2 {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsHK2 D) : CalibrationTarget D := by
  refine calibrationTarget_of_H Pr hℓ ?_
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨M.toModelH⟩

/-- **The inputs of (4.6) at one address, with the Kummer disk lengths read from the genuine
Selmer complexes, the local lengths read from the genuine local quotients, and the moving prime
tied to the curve** (tex 3987–4141): every field of `CalibrationModelH` except `hK` and the
local-block fields, with `kummer`, `blocks` and `moving`. -/
structure CalibrationModelHKL2 {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
    (x : Addr Fam.b) : Type 1 where
  /-- `|Ш(𝒜)[2^∞]|` -/
  shaA : ℕ
  /-- `|Ш(ℬ)[2^∞]|` -/
  shaB : ℕ
  /-- `|𝒜(ℚ)_tors[2^∞]|` -/
  tA : ℕ
  /-- `|ℬ(ℚ)_tors[2^∞]|` -/
  tB : ℕ
  /-- finiteness of `Ш(𝒜)` -/
  shaA_ne : shaA ≠ 0
  /-- finiteness of `Ш(ℬ)` -/
  shaB_ne : shaB ≠ 0
  /-- `𝒜` has torsion -/
  tA_ne : tA ≠ 0
  /-- `ℬ` has torsion -/
  tB_ne : tB ≠ 0
  /-- the finite set of primes carrying the component numbers -/
  Scomp : Finset ℕ
  /-- the component numbers of `𝒜` -/
  cA : ℕ → ℕ
  /-- the component numbers of `ℬ` -/
  cB : ℕ → ℕ
  /-- the companion primes are among them -/
  hTS : D.kfin.natAbs.primeFactors ⊆ Scomp
  /-- component numbers are positive -/
  hcpos : ∀ p ∈ Scomp, 0 < cA p
  /-- cancellation away from the companion primes -/
  hcancel : ∀ p ∈ Scomp, p ∉ D.kfin.natAbs.primeFactors → cA p = cB p
  /-- the Weil restriction has connected special fiber at a companion prime -/
  hA1 : ∀ p ∈ D.kfin.natAbs.primeFactors, cA p = 1
  /-- the companion primes are odd -/
  hodd : ∀ p ∈ D.kfin.natAbs.primeFactors, p ≠ 2
  /-- the companion primes exactly divide `k` -/
  hram : ∀ p ∈ D.kfin.natAbs.primeFactors, ¬ ((p : ℤ) ^ 2 ∣ D.kfin)
  /-- `E₀ = E^{(h_x)}` has good reduction at each companion prime (a good integral model up to
  isomorphism) -/
  goodModel : ∀ p ∈ D.kfin.natAbs.primeFactors, GoodModelIso (qtwist (Ecurve ℓ) (Fam.h x : ℚ)) p
  /-- **PRINT (Edixhoven, Thm 5.3 and Rem 5.4.1) as GLUE**, model-free form -/
  hEdix : EdixhovenComponentNumberIso ℓ (Fam.h x : ℚ) D.kfin cB
  /-- the field `K = ℚ(√k)` -/
  K : Type
  [fieldK : Field K]
  [nfK : NumberField K]
  [decK : DecidableEq K]
  [quadK : Algebra.IsQuadraticExtension ℚ K]
  /-- `√k ∈ K` and the nontrivial automorphism `√k ↦ −√k` -/
  quad : QuadData K (D.kfin : ℚ)
  /-- `φ^*ω_ℬ = a ω_𝒜` -/
  aPull : ℤ
  /-- `ψ^*ω_𝒜 = b ω_ℬ` -/
  bPull : ℤ
  /-- `ab = 4` -/
  hab : aPull * bPull = 4
  /-- `|coker φ_ℝ|` -/
  gam : ℕ
  /-- `|ker φ_ℝ|` -/
  kap : ℕ
  /-- both at most four -/
  hgam : 1 ≤ gam ∧ gam ≤ 4
  /-- both at most four -/
  hkap : 1 ≤ kap ∧ kap ≤ 4
  /-- the Néron period of `𝒜` -/
  OmA : ℝ
  /-- nonzero period -/
  hOmA : OmA ≠ 0
  /-- the rational period ratio `Ω_ℬ/Ω_𝒜` -/
  rhoOm : ℚ
  /-- the real change of variables -/
  hcv : (|aPull| : ℝ) * OmA = ((kap : ℝ) / gam) * ((rhoOm : ℝ) * OmA)
  /-- Cassels' isogeny invariance in Milne's form, with the canonical regulators of any free
  generators of the two rank-one lattices -/
  hmilne : ∀ (gA : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange K).toAffine.Point)
    (gB : ((qtwist (Ecurve ℓ) (Fam.h x : ℚ)).baseChange ℚ).toAffine.Point ×
      ((qtwist (Ecurve ℓ) ((Fam.h x : ℚ) * (D.kfin : ℚ))).baseChange ℚ).toAffine.Point),
    IsFreeGenerator gA → IsFreeGenerator gB →
    Central.MilneIsogenyInvariance shaA shaB tA tA tB tB
      (∏ p ∈ Scomp, cA p) (∏ p ∈ Scomp, cB p) gA.canonicalHeight
      (ZInQ.Manuscript.RC.Height.heightB (Ecurve ℓ) (Fam.h x : ℚ) (D.kfin : ℚ) gB) OmA
      ((rhoOm : ℝ) * OmA)
  /-- `s_ℬ = s(h_x) + s(h_x k)` -/
  hsB : ((padicValNat 2 shaB : ℕ) : ℤ) =
    (shaLength (Etw ℓ (Fam.h x)) : ℤ) + (shaLength (Etw ℓ (Fam.h x * D.kfin)) : ℤ)
  /-- the rational torsion of `ℬ` is bounded by `G₀` -/
  hgB : ((padicValNat 2 tB : ℕ) : ℤ) ≤ G₀
  /-- the moving prime `r_i` -/
  rmov : ℕ
  /-- its trace `a_{r_i}` -/
  amov : ℤ
  /-- the quadratic sign `χ_h(r_i)` -/
  chimov : ℤ
  /-- the moving exponent `B_i` -/
  Bexp : ℕ
  /-- the constant `c_E` of the Tate image -/
  cE : ℕ
  /-- `χ = ±1` -/
  hchi : chimov = 1 ∨ chimov = -1
  /-- `r_i ≡ 1 (mod 2^{B_i})` -/
  hrmov : (2 : ℤ) ^ Bexp ∣ (rmov : ℤ) - 1
  /-- `2^{c_E + 1} ∤ a_{r_i} − 2χ` (the non-divisibility of the moving-prime construction) -/
  hnd : ¬ (2 : ℤ) ^ (cE + 1) ∣ amov - 2 * chimov
  /-- `B_i ≥ c_E + 1` -/
  hcB : cE + 1 ≤ Bexp
  /-- the size of the Kummer two-term model -/
  nK : ℕ
  /-- the index set of the quotient block -/
  κ : Type
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  /-- the Kummer differential -/
  DK : Matrix (Fin nK) (Fin nK) (PowerSeries ℚ_[2])
  /-- the off-diagonal block of the relaxation -/
  X : Matrix (Fin nK) κ (PowerSeries ℚ_[2])
  /-- the quotient block at the moving and active places -/
  DW : Matrix κ κ (PowerSeries ℚ_[2])
  /-- the Kummer class -/
  zK : Fin nK → PowerSeries ℚ_[2]
  /-- the Kummer functional -/
  wK : Fin nK → PowerSeries ℚ_[2]
  /-- the primitive class -/
  zP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the primitive functional -/
  wP : Fin nK ⊕ κ → PowerSeries ℚ_[2]
  /-- the Kummer coordinate -/
  uK : PowerSeries ℚ_[2]
  /-- the primitive class restricts to the Kummer class -/
  hz : ∀ i, zP (Sum.inl i) = zK i
  /-- the primitive functional restricts to the Kummer functional -/
  hw : ∀ i, wP (Sum.inl i) = wK i
  /-- `u_prim` is the coordinate of the primitive model -/
  hP : CommonCoordinate.IsCoordOn (fromBlocks DK X 0 DW) zP wP (D.uPrim Fam x)
  /-- `u_K` is the coordinate of the Kummer model -/
  hKc : Central.IsClassFunctionalCoord DK zK wK uK
  /-- The Kummer differential has nonzero adjugate; this is weaker than
  saying that its generic cohomology has dimensions (1,1). -/
  hadj : DK.adjugate ≠ 0
  /-- **the Kummer block with the disk lengths read from the genuine Selmer complexes**; it
  replaces the field `hK`, which is derived -/
  kummer : KummerCoordinateBlockG K (Ecurve ℓ) (Fam.h x) DK zK wK (D.jrc (Fam.h x) D.kfin) vL
    (amov - 2 * chimov) tA shaA
  /-- **the local blocks with the lengths read from the genuine local quotients**; they replace
  the fields `Fr` … `hact` -/
  blocks : GenuineLengthBlockModel K (Ecurve ℓ) (Fam.h x) DW rmov
    (padicValInt 2 ((rmov : ℤ) + 1 - chimov * amov)) (omega (Fam.h x))
  /-- **the moving prime tied to the curve**: prime, good, with the actual Frobenius trace and
  quadratic Frobenius sign -/
  moving : MovingPrimeData ℓ (Fam.h x) rmov amov chimov

attribute [instance] CalibrationModelHKL2.fieldK CalibrationModelHKL2.nfK
  CalibrationModelHKL2.decK CalibrationModelHKL2.quadK CalibrationModelHKL2.fκ
  CalibrationModelHKL2.dκ

namespace CalibrationModelHKL2

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- `m = a_r − 2χ_h(r) ≠ 0`. PROVED. -/
theorem m_ne_zero (M : CalibrationModelHKL2 D vL G₀ Fam x) : M.amov - 2 * M.chimov ≠ 0 := by
  intro h0
  exact M.hnd (by rw [h0]; exact dvd_zero _)

/-- The quadratic Frobenius sign of the leaf is the Legendre symbol, and is `±1`. PROVED. -/
theorem chimov_sign (M : CalibrationModelHKL2 D vL G₀ Fam x) :
    M.chimov = 1 ∨ M.chimov = -1 :=
  M.moving.chimov_sign

/-- **`CalibrationModelP` from `CalibrationModelHKL2`**: `hvprim` from the triangular Kummer model,
`KummerCoordinateBlockG.hK` and `GenuineLengthBlockModel.hδ`. PROVED. -/
theorem nonempty_modelP (M : CalibrationModelHKL2 D vL G₀ Fam x) :
    Nonempty (CalibrationModelP D vL G₀ Fam x) := by
  obtain ⟨tp, hB, htp⟩ := componentFields_of_edixhovenIso M.hEdix M.hodd M.hram M.goodModel
  obtain ⟨hchi, hmne, hrmov, hBexp⟩ := movingFields_of_nondiv (M.rmov : ℤ) M.amov
    M.chimov M.cE M.Bexp M.hchi M.hnd M.hrmov M.hcB
  have hvprim := hvprim_of_triangular_model M.DK M.X M.DW M.zK M.wK M.zP M.wP M.uK
    (D.uPrim Fam x) M.hz M.hw M.hP M.hKc M.hadj (D.jrc (Fam.h x) D.kfin) vL
    ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ) ((padicValNat 2 M.tA : ℕ) : ℤ)
    ((padicValNat 2 M.shaA : ℕ) : ℤ)
    ((padicValInt 2 ((M.rmov : ℤ) + 1 - M.chimov * M.amov) : ℕ) : ℤ)
    ((omega (Fam.h x) : ℕ) : ℤ) (M.kummer.hK M.m_ne_zero M.hKc M.hadj) M.blocks.hδ
  exact ⟨{ M with
    tp := tp
    hB := hB
    htp := htp
    rmov := (M.rmov : ℤ)
    hchi := hchi
    hmne := hmne
    hrmov := hrmov
    hBexp := hBexp
    hvprim := hvprim }⟩

end CalibrationModelHKL2

/-- The inputs with `CalibrationModelHKL2` at every address. -/
def CalibrationInputsHKL2 {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelHKL2 D vL G₀ F x)

/-- `CalibrationInputsP` from `CalibrationInputsHKL2` (PROVED). -/
theorem calibrationInputsP_of_HKL2 {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputsHKL2 D) :
    CalibrationInputsP D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact M.nonempty_modelP

/-- **`RCSteps.calibration` from `CalibrationInputsHKL2`** ((4.6), tex 3987–4141), with the
uniform error bound `C_cal = 2v₂L + 2G₀ + 5`. PROVED. -/
theorem calibrationTarget_of_HKL2 {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsHKL2 D) : CalibrationTarget D :=
  calibrationTarget_of_inputs (calibrationInputs_of_P Pr hℓ (calibrationInputsP_of_HKL2 h))

end Leaves

end ZInQ.Contrib.RC53Assist.Calibration
