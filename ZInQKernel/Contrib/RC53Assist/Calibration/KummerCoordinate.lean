import ZInQKernel.Contrib.CloudB3RC53.Torsion.KummerIdentification
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.Instances
import ZInQKernel.Contrib.OneProof.RC.Wiring.CalibrationLeaf3
import ZInQKernel.Contrib.OneProof.RC.Wiring.GenuineSwitchLeaf

/-!
# The Kummer coordinate of the calibration leaf, derived from the Knudsen–Mumford model

Proposition `ex:arith-central-calibration` (`diophantine_zq.tex`, tex 4005–4016 and 4050–4064).
The calibration leaf `CalibrationModelH` carries the Kummer two-term model `D_K`, its class `z_K`,
functional `w_K`, coordinate `u_K` with `z_K ⊗ w_K = u_K · adj D_K` and `adj D_K ≠ 0`, and,
as a separate field, the central valuation

  `v₂ u_K(0) = 2 (j_rc + v₂L + v₂ m) + g_𝒜 − s_𝒜 + g_𝒜`,  `m = a_r − 2χ_h(r)`,

with `g_𝒜 = v₂ |𝒜(ℚ)_tors[2^∞]|` and `s_𝒜 = v₂ |Ш(𝒜)[2^∞]|`. The text derives this valuation as
follows (tex 4057–4064): the ordinary Kummer complex has torsion lengths `g_𝒜, s_𝒜, g_𝒜` in degrees
one, two, three; a torsion disk with cokernel of length `e` in degree `i` contributes `(−1)^{i+1} e`
to the inverse determinant coordinate; the central class `Lm P` and its paired functional each have
free coordinate valuation `j_rc + v₂(Lm)`. This file carries out that derivation from the
Knudsen–Mumford coordinate of a rational Kummer model.

**Status: conditional bookkeeping.** The identification `I` is over `ℚ₂[[t]]`, where the three
disks are units, so their integral orders are invisible to it; `CentralDiskOrders` asserts the
orders of three chosen cyclic modules `ℤ₂/(x_i)`, not identified with the torsion of an integral
Kummer complex or with the actual torsion and Tate–Shafarevich groups; and the field `link` is the
coordinate equation `u_K = I.coord`, not an identification of the leaf's two-term model with the
genuine complex. So `KummerCoordinateBlock.hK` computes the coordinate valuation from these
inputs, and the field `hK` of the leaf is **not** discharged arithmetically by it: it remains an
ELLIOT input. The obstructions are recorded, compiled, as `Recorded.redisk2`,
`Recorded.manufactureShaBlock`, `Recorded.manufactured_sha_valuation`, `Recorded.link_iff_uK_eq`
and `Recorded.changeDifferential`; the repair that reads the disk lengths from the genuine
finite-level Kummer Selmer complexes of the address is `KummerCoordinateBlockG`.

Mathematical content.

* `card_quot_span`: for `x ∈ ℤ₂`, `x ≠ 0`, the cyclic module `ℤ₂/(x)` has `2^{v₂ x}` elements.
  Hence (`v2_eq_padicValNat_of_card`) a central torsion disk whose cokernel has `n` elements has
  central valuation `v₂ n`: the length of a disk is read from the order of its cokernel.
* `CentralDiskOrders δ₁ δ₂ δ₃ t s`: the three torsion disks `δ_i` of the Kummer model (units of
  `ℚ₂[[t]]`, so generically acyclic) are integral at the centre, `δ_i(0) = x_i ∈ ℤ₂`, and the
  cokernels `ℤ₂/(x_i)` of the central integral disks have the orders of the torsion groups they
  model: `|ℤ₂/(x₁)| = |𝒜(ℚ)_tors[2^∞]|` (`H¹(C_K)_tors = E^{(h)}(K)[2^∞]`, tex 4007),
  `|ℤ₂/(x₂)| = |Ш(𝒜)[2^∞]|` (`H²(C_K)_tors` is Selmer modulo its maximal divisible subgroup,
  which is `Ш(𝒜)[2^∞]` when `Ш` is finite, tex 4008–4011, 4019–4020), and
  `|ℤ₂/(x₃)| = |𝒜(ℚ)_tors[2^∞]|` (self-duality identifies the degree-three torsion with the
  degree-one torsion, tex 4012–4013).
* `KummerCoordinateBlock K D_K z_K w_K j vL m t s`: the ordinary Kummer complex as the genuine
  Galois Selmer complex over the leaf's field `K` of a `ℚ₂[[t]][G_{K,S}]`-module, with injective
  local conditions and finite `S` (`KummerCoordinateBlock.isGaloisSelData`), with a
  Knudsen–Mumford identification `I` over these genuine data (the core `[R^n → R^n]` plus the
  three disks, quasi-isomorphic to the genuine Selmer complex in the retained bases, carrying the
  model class and functional to the Selmer class and functional); the two-term model
  `(D_K, z_K, w_K)` computes the Knudsen–Mumford coordinate of `I` (`link`); the class and
  functional free coefficients are `a = m · a_P`, `b = m · b_P` with `v₂ a_P(0) = v₂ b_P(0) =
  j + v₂L` (Lemma `ex:arith-central-specialization`, tex 3898–3906: the boundary (4.5) is
  `z_0 = i(L m P)`, and both free-line coefficients of the point have valuation `j_rc + v₂L`);
  the core coordinate `u₀` is a unit at the centre; and the disk orders `CentralDiskOrders`.
* `KummerCoordinateBlock.uK_eq`: the Kummer coordinate `u_K` of the leaf is the Knudsen–Mumford
  coordinate of `I` (uniqueness of the class-functional coordinate when `adj D_K ≠ 0`).
* `KummerCoordinateBlock.hK`: the type of the field `hK` of the calibration leaf, from the block
  (conditional bookkeeping, see the status above), `m ≠ 0`, `z_K ⊗ w_K = u_K adj D_K` and
  `adj D_K ≠ 0`. The disk signs `(−1)^{i+1}` are those of the Knudsen–Mumford coordinate (the
  torsion of `kummerModel`), not an input.
* `KummerCoordinateBlock.hK_eq`: the same valuation in the manuscript's form
  `2 j_rc + 2 v₂(Lm) + 2 g_𝒜 − s_𝒜`.
* `link_core`, `link_of_cancellation`, `KummerCoordinateBlock.ofCancellation`: the link holds
  whenever the two-term model is the core of the identification up to relabelling, with the
  torsion of the cancelled (generically acyclic) disks absorbed into the retained class; the block
  can be built from that structural datum instead of `link`.
* `centralDiskOrders_example`: the disk-order hypotheses are inhabited for every pair of
  two-power orders.
* `CalibrationModelHK`: every field of `CalibrationModelH` except `hK`, with the same names and
  types, and the field `kummer : KummerCoordinateBlock …` in place of `hK`;
  `CalibrationModelHK.hK` (the field `hK` of `CalibrationModelH` in its exact type, derived),
  `CalibrationModelHK.toModelH`, `CalibrationModelHK.nonempty_modelP`, `calibrationInputsH_of_HK`,
  `calibrationInputs_of_HK`, `calibrationTarget_of_HK`.

Kinds: PROVED, conditional on the fields of the block (each with its manuscript lines); the
block is conditional bookkeeping, not an arithmetic discharge of `hK`.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open Matrix NumberField IsDedekindDomain ZInQ.Manuscript ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudB3RC53.PairedFunctional (SelData)
open ZInQ.Manuscript.RC.SelmerComplex (GKS GaloisLocalConditions galoisSelData
  GenuineKummerModelIdentification)
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.CloudB3RC53.Calibration (central_mul v2_mul v2_intCast)

attribute [local instance] Nat.fact_prime_two

/-! ### Lengths of cyclic `ℤ₂`-modules -/

/-- **`|ℤ₂/(x)| = 2^{v₂ x}`** for `x ≠ 0` (write `x = u · 2^{v₂ x}` with `u` a unit; the kernel
of `ℤ₂ → ℤ/2^n` is `(2^n)`). PROVED. -/
theorem card_quot_span (x : ℤ_[2]) (hx : x ≠ 0) :
    Nat.card (ℤ_[2] ⧸ Ideal.span {x}) = 2 ^ x.valuation := by
  have hspan : Ideal.span {x} = Ideal.span {((2 : ℕ) : ℤ_[2]) ^ x.valuation} := by
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff hx).isUnit _
  rw [hspan, ← PadicInt.ker_toZModPow]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow (p := 2) x.valuation))).toEquiv]
  exact Nat.card_zmod _

/-- The valuation of a nonzero `2`-adic integer, read in `ℚ₂`. PROVED. -/
theorem v2_coe_padicInt (x : ℤ_[2]) (hx : x ≠ 0) :
    v2 (x : ℚ_[2]) = ((x.valuation : ℤ) : WithTop ℤ) := by
  have hx' : (x : ℚ_[2]) ≠ 0 := PadicInt.coe_ne_zero.2 hx
  rw [v2, Padic.addValuation.apply hx', PadicInt.valuation_coe]

/-- **The length of a central disk from the order of its cokernel**: if `c = x ∈ ℤ₂`, `x ≠ 0`, and
`ℤ₂/(x)` has `n` elements, then `v₂ c = v₂ n`. PROVED. -/
theorem v2_eq_padicValNat_of_card {x : ℤ_[2]} {c : ℚ_[2]} (hc : c = x) (hx : x ≠ 0) {n : ℕ}
    (hcard : Nat.card (ℤ_[2] ⧸ Ideal.span {x}) = n) :
    v2 c = (((padicValNat 2 n : ℕ) : ℤ) : WithTop ℤ) := by
  subst hc
  rw [v2_coe_padicInt x hx, ← hcard, card_quot_span x hx, padicValNat.prime_pow]

/-- The central value of a unit of `ℚ₂[[t]]` is nonzero. PROVED. -/
theorem central_unit_ne_zero (δ : (PowerSeries ℚ_[2])ˣ) : central (δ : PowerSeries ℚ_[2]) ≠ 0 := by
  intro h0
  have h := congrArg central δ.mul_inv
  rw [central_mul, h0, zero_mul] at h
  have h1 : central (1 : PowerSeries ℚ_[2]) = 1 := by simp [central]
  rw [h1] at h
  exact zero_ne_one h

/-! ### The torsion disks of the ordinary Kummer complex -/

/-- **Declared orders of the central disks (conditional bookkeeping)** (tex 4005–4016,
4057–4060). The disks `δ₁, δ₂, δ₃` (cokernels in degrees one, two, three) are integral at the
centre, `δ_i(0) = x_i ∈ ℤ₂`, and the chosen cyclic modules `ℤ₂/(x_i)` are declared to have the
orders `tA`, `shaA`, `tA`. Nothing here identifies them with the torsion of an integral Kummer
complex or with `𝒜(ℚ)_tors[2^∞]`, `Ш(𝒜)[2^∞]` (`Recorded.manufactureShaBlock`); the integral
version is `DiskTie` with `DiskArith`. -/
structure CentralDiskOrders (δ₁ δ₂ δ₃ : (PowerSeries ℚ_[2])ˣ) (tA shaA : ℕ) where
  /-- the central value of the degree-one disk -/
  x₁ : ℤ_[2]
  /-- the central value of the degree-two disk -/
  x₂ : ℤ_[2]
  /-- the central value of the degree-three disk -/
  x₃ : ℤ_[2]
  /-- the degree-one disk is integral at the centre -/
  hx₁ : central (δ₁ : PowerSeries ℚ_[2]) = x₁
  /-- the degree-two disk is integral at the centre -/
  hx₂ : central (δ₂ : PowerSeries ℚ_[2]) = x₂
  /-- the degree-three disk is integral at the centre -/
  hx₃ : central (δ₃ : PowerSeries ℚ_[2]) = x₃
  /-- `H¹(C_K)_tors = 𝒜(ℚ)_tors[2^∞]` -/
  card₁ : Nat.card (ℤ_[2] ⧸ Ideal.span {x₁}) = tA
  /-- `H²(C_K)_tors = Ш(𝒜)[2^∞]` -/
  card₂ : Nat.card (ℤ_[2] ⧸ Ideal.span {x₂}) = shaA
  /-- `H³(C_K)_tors ≅ H¹(C_K)_tors` -/
  card₃ : Nat.card (ℤ_[2] ⧸ Ideal.span {x₃}) = tA

namespace CentralDiskOrders

variable {δ₁ δ₂ δ₃ : (PowerSeries ℚ_[2])ˣ} {tA shaA : ℕ}

/-- A unit of `ℚ₂[[t]]` with integral central value has a nonzero one. PROVED. -/
theorem x_ne_zero {δ : (PowerSeries ℚ_[2])ˣ} {x : ℤ_[2]} (h : central (δ : PowerSeries ℚ_[2]) = x) :
    x ≠ 0 := by
  rintro rfl
  exact central_unit_ne_zero δ (by rw [h]; rfl)

/-- `v₂ δ₁(0) = g_𝒜`. PROVED. -/
theorem v2₁ (O : CentralDiskOrders δ₁ δ₂ δ₃ tA shaA) :
    v2 (central (δ₁ : PowerSeries ℚ_[2])) = (((padicValNat 2 tA : ℕ) : ℤ) : WithTop ℤ) :=
  v2_eq_padicValNat_of_card O.hx₁ (x_ne_zero O.hx₁) O.card₁

/-- `v₂ δ₂(0) = s_𝒜`. PROVED. -/
theorem v2₂ (O : CentralDiskOrders δ₁ δ₂ δ₃ tA shaA) :
    v2 (central (δ₂ : PowerSeries ℚ_[2])) = (((padicValNat 2 shaA : ℕ) : ℤ) : WithTop ℤ) :=
  v2_eq_padicValNat_of_card O.hx₂ (x_ne_zero O.hx₂) O.card₂

/-- `v₂ δ₃(0) = g_𝒜`. PROVED. -/
theorem v2₃ (O : CentralDiskOrders δ₁ δ₂ δ₃ tA shaA) :
    v2 (central (δ₃ : PowerSeries ℚ_[2])) = (((padicValNat 2 tA : ℕ) : ℤ) : WithTop ℤ) :=
  v2_eq_padicValNat_of_card O.hx₃ (x_ne_zero O.hx₃) O.card₃

end CentralDiskOrders

/-! ### The Kummer coordinate block -/

/-- **The Kummer block of the calibration leaf** (tex 3877–3892, 3898–3906, 4005–4016, 4050–4064),
over the field `K = ℚ(√k)` of the leaf, for the two-term Kummer model `(D_K, z_K, w_K)` of the
leaf, the integers `j = j_rc(h,k)`, `vL = v₂L`, `m = a_r − 2χ_h(r)`, and the orders
`tA = |𝒜(ℚ)_tors[2^∞]|`, `shaA = |Ш(𝒜)[2^∞]|`.

| field | content | tex | kind |
|---|---|---|---|
| `S`, `hSfin`, `M`, `Δ`, `hinj` | the ordinary Kummer complex is the genuine Galois Selmer complex over `K` of a topological `ℚ₂[[t]][G_{K,S}]`-module `M` with local conditions `Δ` that are subcomplexes of the local cochains, `S` finite | 3455–3463, 4005 | definition |
| `I` | its Knudsen–Mumford model (`GenuineKummerModelIdentification`): core `[R^n → R^n]` with acyclic augmentation, class `a z₀`, functional `b λ₀`, `z₀ ⊗ λ₀ = u₀ adj D_c`, disks `δ₁, δ₂, δ₃`, and a quasi-isomorphism to the genuine Selmer complex in the retained bases carrying class and functional | 3877–3892, 4057–4060 | GLUE (identification) |
| `link` | coordinate transfer: equivalent to `u_K = I.coord` (`Recorded.link_iff_uK_eq`), not an identification of the two-term model (`Recorded.changeDifferential`); `link_of_cancellation` gives it from a rational cancellation datum | 3889–3890 | GLUE |
| `aP`, `bP`, `ha`, `hb`, `haP`, `hbP` | the class and functional free coefficients are `m · a_P`, `m · b_P` with `v₂ a_P(0) = v₂ b_P(0) = j + v₂L` | 3898–3906, 4061–4062 | ELLIOT (Lemma `ex:arith-central-specialization`) |
| `hu₀` | the core coordinate is a unit at the centre | 4061–4064 | ELLIOT |
| `disks` | declared orders `tA`, `shaA`, `tA` of the chosen cyclic modules `ℤ₂/(x_i)` (conditional bookkeeping: freely assignable, `Recorded.manufactureShaBlock`) | 4005–4016, 4057–4058 | ELLIOT (not identified) |

Conditional bookkeeping: see the status in the module documentation. -/
structure KummerCoordinateBlock (K : Type) [Field K] [NumberField K] {n : ℕ}
    (DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])) (zK wK : Fin n → PowerSeries ℚ_[2])
    (j vL m : ℤ) (tA shaA : ℕ) : Type 1 where
  /-- the finite set of places of the Selmer complex -/
  S : Set (HeightOneSpectrum (𝓞 K))
  /-- it is finite -/
  hSfin : S.Finite
  /-- the coefficient module -/
  M : Type
  [addM : AddCommGroup M]
  [modM : Module (PowerSeries ℚ_[2]) M]
  [actM : DistribMulAction (GKS K S) M]
  [commM : SMulCommClass (GKS K S) (PowerSeries ℚ_[2]) M]
  [topM : TopologicalSpace M]
  [caddM : ContinuousAdd M]
  [cconstM : ContinuousConstSMul (PowerSeries ℚ_[2]) M]
  [csmulM : ContinuousSMul (GKS K S) M]
  /-- the local conditions of the ordinary Kummer complex -/
  Δ : GaloisLocalConditions K S (PowerSeries ℚ_[2]) M
  /-- they are subcomplexes of the local cochains -/
  hinj : ∀ v (k : ℤ), Function.Injective ((Δ.i v).f k k rfl)
  /-- the Knudsen–Mumford model of the ordinary Kummer complex -/
  I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ
  /-- the two-term Kummer model of the leaf computes its coordinate in the retained bases -/
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
  /-- the central integral disks and their orders -/
  disks : CentralDiskOrders I.δ₁ I.δ₂ I.δ₃ tA shaA

attribute [instance] KummerCoordinateBlock.addM KummerCoordinateBlock.modM
  KummerCoordinateBlock.actM KummerCoordinateBlock.commM KummerCoordinateBlock.topM
  KummerCoordinateBlock.caddM KummerCoordinateBlock.cconstM KummerCoordinateBlock.csmulM

namespace KummerCoordinateBlock

variable {K : Type} [Field K] [NumberField K] {n : ℕ}
  {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
  {j vL m : ℤ} {tA shaA : ℕ}

/-- **The ordinary Kummer complex of the block is genuine Galois Selmer data.** PROVED. -/
theorem isGaloisSelData (B : KummerCoordinateBlock K DK zK wK j vL m tA shaA) :
    ZInQ.Manuscript.RC.Wiring.IsGaloisSelData (galoisSelData K B.S (PowerSeries ℚ_[2]) B.M B.Δ) :=
  ⟨K, inferInstance, inferInstance, B.S, B.M, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, B.Δ, B.hSfin,
    B.hinj, rfl⟩

/-- **The Kummer coordinate of the leaf is the Knudsen–Mumford coordinate of the ordinary Kummer
complex** (uniqueness of the class-functional coordinate, `adj D_K ≠ 0`). PROVED. -/
theorem uK_eq (B : KummerCoordinateBlock K DK zK wK j vL m tA shaA) {uK : PowerSeries ℚ_[2]}
    (hKc : Central.IsClassFunctionalCoord DK zK wK uK) (hadj : DK.adjugate ≠ 0) :
    uK = B.I.coord :=
  Central.isClassFunctionalCoord_unique hadj hKc B.link

/-- `v₂ a(0) = j + v₂L + v₂ m` (the moving factor of the boundary (4.5)). PROVED. -/
theorem v2_a (B : KummerCoordinateBlock K DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    v2 (central B.I.a) = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hC : central (PowerSeries.C (m : ℚ_[2])) = (m : ℚ_[2]) := by simp [central]
  rw [B.ha, central_mul, v2_mul, hC, v2_intCast hm, B.haP, ← WithTop.coe_add]
  congr 1
  ring

/-- `v₂ b(0) = j + v₂L + v₂ m`. PROVED. -/
theorem v2_b (B : KummerCoordinateBlock K DK zK wK j vL m tA shaA) (hm : m ≠ 0) :
    v2 (central B.I.b) = ((j + vL + ((padicValInt 2 m : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  have hC : central (PowerSeries.C (m : ℚ_[2])) = (m : ℚ_[2]) := by simp [central]
  rw [B.hb, central_mul, v2_mul, hC, v2_intCast hm, B.hbP, ← WithTop.coe_add]
  congr 1
  ring

/-- **The Kummer-coordinate valuation of the calibration leaf** (tex 4057–4064), in the exact form
of the field `hK` of `CalibrationModelH` with `vm = v₂ m`, `g_𝒜 = v₂ tA`, `s_𝒜 = v₂ shaA`:
`v₂ u_K(0) = (j + v₂L + v₂m) + (j + v₂L + v₂m) + ((−1)² g_𝒜 + (−1)³ s_𝒜 + (−1)⁴ g_𝒜)`. PROVED,
from the Knudsen–Mumford coordinate of the identified Kummer model (Torsion's
`hK_of_identification`). -/
theorem hK (B : KummerCoordinateBlock K DK zK wK j vL m tA shaA) (hm : m ≠ 0)
    {uK : PowerSeries ℚ_[2]} (hKc : Central.IsClassFunctionalCoord DK zK wK uK)
    (hadj : DK.adjugate ≠ 0) :
    v2 (central uK) =
      (((j + vL + ((padicValInt 2 m : ℕ) : ℤ)) + (j + vL + ((padicValInt 2 m : ℕ) : ℤ)) +
        (Central.diskContribution 1 ((padicValNat 2 tA : ℕ) : ℤ) +
          Central.diskContribution 2 ((padicValNat 2 shaA : ℕ) : ℤ) +
          Central.diskContribution 3 ((padicValNat 2 tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ) := by
  rw [B.uK_eq hKc hadj]
  exact hK_of_identification B.I j vL ((padicValInt 2 m : ℕ) : ℤ) ((padicValNat 2 tA : ℕ) : ℤ)
    ((padicValNat 2 shaA : ℕ) : ℤ) B.hu₀ (B.v2_a hm) (B.v2_b hm) B.disks.v2₁ B.disks.v2₂
    B.disks.v2₃

/-- **The Kummer-coordinate valuation in the manuscript's form** `2 j_rc + 2 v₂(Lm) + 2 g_𝒜 − s_𝒜`
(tex 4063–4064), with `v₂(Lm) = v₂L + v₂m`. PROVED. -/
theorem hK_eq (B : KummerCoordinateBlock K DK zK wK j vL m tA shaA) (hm : m ≠ 0)
    {uK : PowerSeries ℚ_[2]} (hKc : Central.IsClassFunctionalCoord DK zK wK uK)
    (hadj : DK.adjugate ≠ 0) :
    v2 (central uK) =
      ((2 * j + 2 * (vL + ((padicValInt 2 m : ℕ) : ℤ)) + 2 * ((padicValNat 2 tA : ℕ) : ℤ) -
        ((padicValNat 2 shaA : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by
  rw [B.hK hm hKc hadj]
  congr 1
  simp only [Central.diskContribution]
  ring

end KummerCoordinateBlock

/-! ### The link is realized by the core -/

/-- **The two-term model of the core, in the retained bases, computes the Knudsen–Mumford
coordinate** (tex 3889–3890, 4057–4060): with the torsion `δ₁ δ₂⁻¹ δ₃` of the cancelled
(generically acyclic) disks absorbed into the retained class, the core `D_c` with class
`δ₁ δ₂⁻¹ δ₃ · z` and functional `λ` has class-functional coordinate `I.coord`. So the field `link`
is satisfied by the core of any identification. PROVED. -/
theorem link_core {S : Type} [CommRing S] [IsDomain S] {D : SelData S}
    (I : KummerModelIdentification D) :
    Central.IsClassFunctionalCoord I.Dc
      ((((I.δ₁ * I.δ₂⁻¹ * I.δ₃ : Sˣ)) : S) • I.z) I.w I.coord := by
  have h := isClassFunctionalCoord_smul I.Dc ((((I.δ₁ * I.δ₂⁻¹ * I.δ₃ : Sˣ)) : S)) 1 I.hu
  rw [one_smul] at h
  convert h using 1
  rw [I.coord_eq]
  push_cast
  ring

/-- The class-functional coordinate is invariant under a relabelling of the basis. PROVED. -/
theorem isClassFunctionalCoord_submatrix {S : Type} [CommRing S] {n n' : ℕ} (e : Fin n ≃ Fin n')
    {D : Matrix (Fin n') (Fin n') S} {z w : Fin n' → S} {u : S}
    (h : Central.IsClassFunctionalCoord D z w u) :
    Central.IsClassFunctionalCoord (D.submatrix e e) (z ∘ e) (w ∘ e) u := by
  unfold Central.IsClassFunctionalCoord at h ⊢
  rw [Matrix.adjugate_submatrix_equiv_self]
  ext a b
  have := congrFun (congrFun h (e a)) (e b)
  simpa [Matrix.vecMulVec_apply] using this

/-- **The link from the cancellation of the disks** (tex 3877–3892, 4057–4060): if the two-term
model `(D_K, z_K, w_K)` is the core `D_c` of the identification, up to a relabelling `e` of the
basis, with the class `δ₁ δ₂⁻¹ δ₃ · z` (the torsion of the three cancelled, generically acyclic
disks absorbed into the retained class) and the functional `λ`, then it computes the
Knudsen–Mumford coordinate: the field `link` of `KummerCoordinateBlock` holds. PROVED. -/
theorem link_of_cancellation {S : Type} [CommRing S] [IsDomain S] {D : SelData S}
    (I : KummerModelIdentification D) {n : ℕ} (e : Fin n ≃ Fin I.n)
    {DK : Matrix (Fin n) (Fin n) S} {zK wK : Fin n → S} (hD : DK = I.Dc.submatrix e e)
    (hz : zK = ((((I.δ₁ * I.δ₂⁻¹ * I.δ₃ : Sˣ)) : S) • I.z) ∘ e) (hw : wK = I.w ∘ e) :
    Central.IsClassFunctionalCoord DK zK wK I.coord := by
  subst hD hz hw
  exact isClassFunctionalCoord_submatrix e (link_core I)

/-- **The Kummer block from the cancellation of the disks**: the field `link` discharged by
`link_of_cancellation` (the two-term model is the relabelled core with the disk torsion in the
retained class). PROVED. -/
def KummerCoordinateBlock.ofCancellation {K : Type} [Field K] [NumberField K] {n : ℕ}
    {DK : Matrix (Fin n) (Fin n) (PowerSeries ℚ_[2])} {zK wK : Fin n → PowerSeries ℚ_[2]}
    {j vL m : ℤ} {tA shaA : ℕ} (S : Set (HeightOneSpectrum (𝓞 K))) (hSfin : S.Finite)
    (M : Type) [AddCommGroup M] [Module (PowerSeries ℚ_[2]) M] [DistribMulAction (GKS K S) M]
    [SMulCommClass (GKS K S) (PowerSeries ℚ_[2]) M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul (PowerSeries ℚ_[2]) M] [ContinuousSMul (GKS K S) M]
    (Δ : GaloisLocalConditions K S (PowerSeries ℚ_[2]) M)
    (hinj : ∀ v (k : ℤ), Function.Injective ((Δ.i v).f k k rfl))
    (I : GenuineKummerModelIdentification K S (PowerSeries ℚ_[2]) M Δ) (e : Fin n ≃ Fin I.n)
    (hD : DK = I.Dc.submatrix e e)
    (hz : zK = ((((I.δ₁ * I.δ₂⁻¹ * I.δ₃ : (PowerSeries ℚ_[2])ˣ)) : PowerSeries ℚ_[2]) • I.z) ∘ e)
    (hw : wK = I.w ∘ e) (aP bP : PowerSeries ℚ_[2])
    (ha : I.a = PowerSeries.C (m : ℚ_[2]) * aP) (hb : I.b = PowerSeries.C (m : ℚ_[2]) * bP)
    (haP : v2 (central aP) = ((j + vL : ℤ) : WithTop ℤ))
    (hbP : v2 (central bP) = ((j + vL : ℤ) : WithTop ℤ)) (hu₀ : v2 (central I.u₀) = 0)
    (disks : CentralDiskOrders I.δ₁ I.δ₂ I.δ₃ tA shaA) :
    KummerCoordinateBlock K DK zK wK j vL m tA shaA where
  S := S
  hSfin := hSfin
  M := M
  Δ := Δ
  hinj := hinj
  I := I
  link := link_of_cancellation I e hD hz hw
  aP := aP
  bP := bP
  ha := ha
  hb := hb
  haP := haP
  hbP := hbP
  hu₀ := hu₀
  disks := disks

/-! ### Non-vacuity of the disk orders -/

/-- The constant unit `2^e` of `ℚ₂[[t]]`. -/
def twoPowUnit (e : ℕ) : (PowerSeries ℚ_[2])ˣ :=
  Units.map (PowerSeries.C (R := ℚ_[2])).toMonoidHom
    (Units.mk0 ((2 : ℚ_[2]) ^ e) (pow_ne_zero _ two_ne_zero))

theorem central_twoPowUnit (e : ℕ) :
    central ((twoPowUnit e : (PowerSeries ℚ_[2])ˣ) : PowerSeries ℚ_[2]) = ((2 ^ e : ℤ_[2]) : ℚ_[2]) := by
  change PowerSeries.coeff 0 (PowerSeries.C ((2 : ℚ_[2]) ^ e)) = _
  rw [PowerSeries.coeff_zero_C]
  norm_cast

theorem valuation_two_padicInt : (2 : ℤ_[2]).valuation = 1 := by
  simpa using PadicInt.valuation_p (p := 2)

/-- **The disk orders are inhabited** for all two-power orders `tA = 2^g`, `shaA = 2^s`: the
constant disks `2^g, 2^s, 2^g`. PROVED. -/
def centralDiskOrders_example (g s : ℕ) :
    CentralDiskOrders (twoPowUnit g) (twoPowUnit s) (twoPowUnit g) (2 ^ g) (2 ^ s) where
  x₁ := 2 ^ g
  x₂ := 2 ^ s
  x₃ := 2 ^ g
  hx₁ := central_twoPowUnit g
  hx₂ := central_twoPowUnit s
  hx₃ := central_twoPowUnit g
  card₁ := by
    rw [card_quot_span _ (pow_ne_zero _ two_ne_zero), PadicInt.valuation_pow,
      valuation_two_padicInt, mul_one]
  card₂ := by
    rw [card_quot_span _ (pow_ne_zero _ two_ne_zero), PadicInt.valuation_pow,
      valuation_two_padicInt, mul_one]
  card₃ := by
    rw [card_quot_span _ (pow_ne_zero _ two_ne_zero), PadicInt.valuation_pow,
      valuation_two_padicInt, mul_one]

/-! ### The calibration leaf with `hK` derived

`CalibrationModelHK` has every field of `CalibrationModelH` except
`hK`, with the same names and types, and the Kummer block `kummer` in place of `hK`. -/

section Leaf

open ZInQ.Manuscript.SelmerTwoPower ZInQ.Contrib.CloudB3RC53
open ZInQ.Contrib.CloudB3RC53.Calibration
open ZInQ.Manuscript.RC.Wiring
open WeierstrassCurve WeierstrassCurve.Affine
open ZInQ.Manuscript.RC.Height (IsFreeGenerator QuadData)

/-- **The inputs of (4.6) at one address, with the Kummer coordinate derived** (tex 3987–4141).
Every field of `CalibrationModelH` except `hK`, with the same names, types, tex lines, kinds and
owners (see the table there), and the Kummer block `kummer` in place of `hK`. -/
structure CalibrationModelHK {ℓ : ℕ} (D : RCData ℓ) (vL G₀ : ℤ) (Fam : Family)
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
  /-- **the Kummer block**: the ordinary Kummer complex as genuine Galois Selmer data with its
  Knudsen–Mumford model, the link with the two-term model above, the free coefficients of the
  class and functional, and the central torsion disks with the orders `tA`, `shaA`, `tA`; it
  replaces the field `hK` of `CalibrationModelH`, which is derived from it -/
  kummer : KummerCoordinateBlock K DK zK wK (D.jrc (Fam.h x) D.kfin) vL (amov - 2 * chimov) tA
    shaA
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

attribute [instance] CalibrationModelHK.fieldK CalibrationModelHK.nfK CalibrationModelHK.decK
  CalibrationModelHK.quadK CalibrationModelHK.fκ CalibrationModelHK.dκ

namespace CalibrationModelHK

variable {ℓ : ℕ} {D : RCData ℓ} {vL G₀ : ℤ} {Fam : Family} {x : Addr Fam.b}

/-- `m = a_r − 2χ_h(r) ≠ 0`, from the non-divisibility `2^{c_E+1} ∤ m`. PROVED. -/
theorem m_ne_zero (M : CalibrationModelHK D vL G₀ Fam x) : M.amov - 2 * M.chimov ≠ 0 := by
  intro h0
  exact M.hnd (by rw [h0]; exact dvd_zero _)

/-- **The field `hK` of `CalibrationModelH`, derived** (tex 4057–4064): the Kummer coordinate of
the leaf is the Knudsen–Mumford coordinate of the ordinary Kummer complex, whose central valuation
is `2(j_rc + v₂L + v₂m) + g_𝒜 − s_𝒜 + g_𝒜`. PROVED. -/
theorem hK (M : CalibrationModelHK D vL G₀ Fam x) :
    v2 (central M.uK) =
      ((((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ)) +
        ((D.jrc (Fam.h x) D.kfin) + vL + ((padicValInt 2 (M.amov - 2 * M.chimov) : ℕ) : ℤ)) +
        (Central.diskContribution 1 ((padicValNat 2 M.tA : ℕ) : ℤ) +
          Central.diskContribution 2 ((padicValNat 2 M.shaA : ℕ) : ℤ) +
          Central.diskContribution 3 ((padicValNat 2 M.tA : ℕ) : ℤ)) : ℤ) : WithTop ℤ) :=
  M.kummer.hK M.m_ne_zero M.hKc M.hadj

/-- **`CalibrationModelH` from `CalibrationModelHK`**: all fields copied, `hK` derived. PROVED. -/
def toModelH (M : CalibrationModelHK D vL G₀ Fam x) : CalibrationModelH D vL G₀ Fam x :=
  { M with hK := M.hK }

/-- `CalibrationModelP` from `CalibrationModelHK` (through `CalibrationModelH.nonempty_modelP`).
PROVED. -/
theorem nonempty_modelP (M : CalibrationModelHK D vL G₀ Fam x) :
    Nonempty (CalibrationModelP D vL G₀ Fam x) :=
  M.toModelH.nonempty_modelP

end CalibrationModelHK

/-- **The remaining inputs of `RCSteps.calibration`, with the Kummer coordinate derived** ((4.6),
tex 3987–4141): as `CalibrationInputsH`, with `CalibrationModelHK` at every address. -/
def CalibrationInputsHK {ℓ : ℕ} (D : RCData ℓ) : Prop :=
  ∃ vL G₀ : ℤ, 0 ≤ vL ∧ ∀ Co Ce : ℤ, ∀ F : Family, D.FinalFamilyAt Co Ce F →
    ∀ x : Addr F.b, AnalyticRank (Etw ℓ (F.h x)) 1 →
      AnalyticRank (Etw ℓ (F.h x * D.kfin)) 0 → Nonempty (CalibrationModelHK D vL G₀ F x)

/-- `CalibrationInputsH` from `CalibrationInputsHK` (PROVED). -/
theorem calibrationInputsH_of_HK {ℓ : ℕ} {D : RCData ℓ} (h : CalibrationInputsHK D) :
    CalibrationInputsH D := by
  obtain ⟨vL, G₀, hvL, H⟩ := h
  refine ⟨vL, G₀, hvL, fun Co Ce F hF x h1 h0 => ?_⟩
  obtain ⟨M⟩ := H Co Ce F hF x h1 h0
  exact ⟨M.toModelH⟩

/-- `CalibrationInputs` from `CalibrationInputsHK` and the prints (PROVED). -/
theorem calibrationInputs_of_HK {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsHK D) : CalibrationInputs D :=
  calibrationInputs_of_H Pr hℓ (calibrationInputsH_of_HK h)

/-- **`RCSteps.calibration` from `CalibrationInputsHK`** ((4.6), tex 3987–4141), with the uniform
error bound `C_cal = 2v₂L + 2G₀ + 5`. PROVED. -/
theorem calibrationTarget_of_HK {ℓ : ℕ} {D : RCData ℓ} (Pr : Prints) (hℓ : 0 < ℓ)
    (h : CalibrationInputsHK D) : CalibrationTarget D :=
  calibrationTarget_of_H Pr hℓ (calibrationInputsH_of_HK h)


end Leaf

end ZInQ.Contrib.RC53Assist.Calibration
