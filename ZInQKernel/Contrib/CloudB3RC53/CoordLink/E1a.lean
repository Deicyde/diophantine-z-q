import ZInQKernel.Contrib.CloudB3RC53.CoordLink.PreCancel

/-!
# E1a, part 2: `CoordLink` for the Knudsen–Mumford coordinate of the remaining complex

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:limits-fixed-field-clearing`, tex
L5509–5516, 5605–5617, with Lemma `ex:arith-common-coordinate` (tex 4142–4328). E1a is
`ũ_x = η_x κ_x 2^{−a} c_x` where `Δ_x ≠ 0`, with `c_x` the coordinate of `[z] ⊗ [μ]` of the
remaining complex `D_x` (lane ClearingComplex's `cOf`, the Knudsen–Mumford coordinate `kmCoord` of
lane Torsion). Against the strengthened identification `Identification2` (lane ClearingComplex):

* `Cx M x`: the sign-evaluated pre-cancellation complex `C_x` over `K = Frac 𝒪` (the original
  complex of the clearing, before the new-local cancellation); `Dx_toFour_eq`: the sign-evaluated
  remaining complex is the cancellation of `C_x`; `kappa M = det B ∈ 𝒪[G]` and `isUnit_kappa`
  (tex 5510–5512: "`κ` is an `S`-unit");
* the transported cycle and functional: a cycle `z` of `D¹ = C¹` and a closed functional `λ` on
  `C² = D² ⊕ N` over `𝒪[G]`; `μ = transportFun λ = λ ∘ incl` (`hzC`, `hμ_transport`);
* the two inputs (GLUE, named): `CorrectedIsEta` (`ũ_x = η_x u_{rel,x}`, the definition of the
  corrected coordinate, tex 4222) and `RelIsKM` (`u_{rel,x}` is the coordinate of `[z] ⊗ [λ]` of
  the original complex `C_x` in the original determinant basis, i.e. lane Torsion's `kmCoord` in the
  orientation `σPre`);
* `correctedIsEta_of_47` (PROVED, the (4.7) bridge): `CorrectedIsEta` follows from RC15's
  `corrected_eq` (the evaluated ratios `l_q/e_q² = 1 + 2v_q` and the multi-prime (4.7)) and the
  common-coordinate identity `ũ_x = (∏_{q unused} ε_q) u_{prim,x}`;
* **`coordLink_of_km` (E1a, PROVED from the two inputs)**: `CoordLink M.toIdentification.B κ η 0
  e g (cOf M.D z μ hz hμ)` for every representation `UTildeRep Dd F e g` — the cancellation factor
  is `κ = det B` (`kmCoord_preCancel`), the functional is transported, and `c = kmCoord(D_x)`.
* `coordLink_example`: the inputs are inhabited (LESSON 2) for the trivial new-local model.

**Classification.** PROVED (the two named inputs are GLUE).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CoordLink

open Matrix ZInQ.Contrib.CloudB3RC53.Torsion ZInQ.Contrib.CloudB3RC53.ClearingComplex
open ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
open ZInQ.Manuscript.RC.Determinant (Lam OO SignGroup evK uK sgnChar)

variable {b dK hK cE tK : ℕ}

/-- `FourCx` equality from the differentials. -/
theorem FourCx.ext' {R : Type*} [CommRing R] {ι0 ι1 ι2 ι3 : Type*} [Fintype ι1] [Fintype ι2]
    {C C' : FourCx R ι0 ι1 ι2 ι3} (h0 : C.d0 = C'.d0) (h1 : C.d1 = C'.d1) (h2 : C.d2 = C'.d2) :
    C = C' := by
  cases C; cases C'; simp only at h0 h1 h2; subst h0 h1 h2; rfl

/-- `kmCoord` depends only on the complex, the class and the functional. -/
theorem kmCoord_congr {R : Type*} [CommRing R] {ι0 ι1 ι2 ι3 : Type*} [Fintype ι0] [Fintype ι1]
    [Fintype ι2] [Fintype ι3] [DecidableEq ι0] [DecidableEq ι1] [DecidableEq ι2] [DecidableEq ι3]
    {C C' : FourCx R ι0 ι1 ι2 ι3} {z z' : ι1 → R} {lam lam' : ι2 → R} (hC : C = C') (hz' : z = z')
    (hl : lam = lam') (hz : C.d1 *ᵥ z = 0) (hlam : lam ᵥ* C.d1 = 0) (hz2 : C'.d1 *ᵥ z' = 0)
    (hlam2 : lam' ᵥ* C'.d1 = 0) (σ : (ι0 ⊕ Unit) ⊕ ι2 ≃ ι1 ⊕ (ι3 ⊕ Unit)) :
    kmCoord C z lam hz hlam σ = kmCoord C' z' lam' hz2 hlam2 σ := by
  subst hC hz' hl; rfl

/-! ### Generic: a pre-cancellation complex over `𝒪[G]` and its sign evaluations -/

section Generic

variable (C : ClearingComplex.PreComplex (MonoidAlgebra OO (SignGroup b))) (hB : IsUnit C.B.det)

/-- The sign-evaluated pre-cancellation complex `C_x` over `Frac 𝒪`. -/
abbrev Cev (x : Addr b) : ClearingComplex.PreComplex (FractionRing OO) := C.map (evK (sgnChar x))

include hB in
theorem isUnit_Bev (x : Addr b) : IsUnit (Cev C x).B.det := by
  have h := RingHom.map_det (evK (sgnChar x)) C.B
  rw [RingHom.mapMatrix_apply] at h
  change IsUnit (C.B.map (evK (sgnChar x))).det
  rw [← h]
  exact hB.map _

theorem det_Bev (x : Addr b) : (Cev C x).B.det = evK (sgnChar x) C.B.det := by
  have h := RingHom.map_det (evK (sgnChar x)) C.B
  rw [RingHom.mapMatrix_apply] at h
  exact h.symm

/-- **The sign-evaluated remaining complex is the cancellation of `C_x`.** -/
theorem Dev_toFour_eq (x : Addr b) :
    (Dx (C.cancel hB) x).toFour = ((Cev C x).cancel (isUnit_Bev C hB x)).toFour := by
  refine FourCx.ext' rfl rfl ?_
  change (C.P - C.Q * C.B⁻¹ * C.T).map (evK (sgnChar x)) =
    C.P.map (evK (sgnChar x)) - C.Q.map (evK (sgnChar x)) * (C.B.map (evK (sgnChar x)))⁻¹ *
      C.T.map (evK (sgnChar x))
  rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, map_inv_of_isUnit _ _ hB]

variable {C}

include hB in
/-- A cycle of the remaining complex is a cycle of the pre-cancellation complex. -/
theorem hzC {z : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → MonoidAlgebra OO (SignGroup b)}
    (hX : C.X *ᵥ z = 0) : fromRows C.X C.Y *ᵥ z = 0 := by
  have hY : C.Y *ᵥ z = 0 := by
    rw [PreComplex.Y_eq hB, neg_mulVec, ← mulVec_mulVec, hX, mulVec_zero, neg_zero]
  funext i
  rcases i with i | i
  · exact congrFun hX i
  · exact congrFun hY i

theorem hzev {z : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → MonoidAlgebra OO (SignGroup b)}
    (hz : fromRows C.X C.Y *ᵥ z = 0) (x : Addr b) :
    (PreComplex'.toFour (Cev C x)).d1 *ᵥ (evK (sgnChar x) ∘ z) = 0 := by
  change fromRows (C.X.map (evK (sgnChar x))) (C.Y.map (evK (sgnChar x))) *ᵥ
    (evK (sgnChar x) ∘ z) = 0
  rw [← fromRows_map]
  funext i
  rw [← RingHom.map_mulVec, hz]
  simp

theorem hlamev {lam : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → MonoidAlgebra OO (SignGroup b)}
    (hlam : lam ᵥ* fromRows C.X C.Y = 0) (x : Addr b) :
    (evK (sgnChar x) ∘ lam) ᵥ* (PreComplex'.toFour (Cev C x)).d1 = 0 := by
  change (evK (sgnChar x) ∘ lam) ᵥ*
    fromRows (C.X.map (evK (sgnChar x))) (C.Y.map (evK (sgnChar x))) = 0
  rw [← fromRows_map]
  funext i
  rw [← RingHom.map_vecMul, hlam]
  simp

include hB in
theorem transport_map (lam : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → MonoidAlgebra OO (SignGroup b))
    (x : Addr b) :
    evK (sgnChar x) ∘ transportFun C lam = transportFun (Cev C x) (evK (sgnChar x) ∘ lam) := by
  funext j
  change evK (sgnChar x) ((lam ∘ Sum.inl) j - ((((lam ∘ Sum.inr) ᵥ* C.B⁻¹) ᵥ* C.T) j)) =
    (evK (sgnChar x) ∘ lam) (Sum.inl j) - ((((evK (sgnChar x) ∘ lam) ∘ Sum.inr) ᵥ*
      (C.B.map (evK (sgnChar x)))⁻¹) ᵥ* C.T.map (evK (sgnChar x))) j
  have h1 : ∀ {m n : Type} [Fintype m] (v : m → MonoidAlgebra OO (SignGroup b))
      (M : Matrix m n (MonoidAlgebra OO (SignGroup b))),
      (evK (sgnChar x) ∘ (v ᵥ* M)) = (evK (sgnChar x) ∘ v) ᵥ* M.map (evK (sgnChar x)) :=
    fun v M => funext fun i => RingHom.map_vecMul _ M v i
  rw [map_sub, RingHom.map_vecMul, h1, ← map_inv_of_isUnit _ _ hB]
  rfl

/-- **E1a, generic core** (PROVED): if `ũ_x = η_x u_{rel,x}` and `u_{rel,x}` is the
Knudsen–Mumford coordinate of `C_x` (orientation `σPre`) where `Δ_x ≠ 0`, then
`ũ_x = η_x κ_x c_x` with `κ = det B` and `c_x = kmCoord(D_x, z, λ ∘ incl)`. -/
theorem coordLink_core {ℓ : ℕ} (Dd : RCData ℓ) (F : Family)
    (C : ClearingComplex.PreComplex (MonoidAlgebra OO (SignGroup F.b))) (hB : IsUnit C.B.det)
    (Bs : Determinant.SmithBlocks (MonoidAlgebra OO (SignGroup F.b)) OO)
    (z : Fin C.m0 ⊕ Unit ⊕ Fin C.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin C.m1 ⊕ Unit ⊕ Fin C.m2) ⊕ C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : (C.cancel hB).d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows C.X C.Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (urel : Addr F.b → FractionRing OO)
    (hη : ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      ∀ x, uK (e x) (g x) = evK (sgnChar x) η * urel x)
    (hrel : ∀ x : Addr F.b, evK (sgnChar x) Bs.Δ ≠ 0 →
      urel x = kmCoord (PreComplex'.toFour (Cev C x)) (evK (sgnChar x) ∘ z)
        (evK (sgnChar x) ∘ lam) (hzev (hzC hB hz) x) (hlamev hlam x)
        (σPre C.m0 C.m1 C.m2 C.N)) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      CoordLink Bs C.B.det η 0 e g
        (cOf (C.cancel hB) z (transportFun C lam) hz (hμ_cancel C hB hlam)) := by
  intro e g hrep x hΔ
  rw [hη e g hrep x, hrel x hΔ, pow_zero, inv_one, mul_one]
  have key := kmCoord_preCancel (C := Cev C x) (isUnit_Bev C hB x)
    (z := evK (sgnChar x) ∘ z) (lam := evK (sgnChar x) ∘ lam) (hz := hzev (hzC hB hz) x)
    (hlam := hlamev hlam x)
  refine (congrArg (evK (sgnChar x) η * ·) key).trans ?_
  rw [det_Bev C x, mul_assoc]
  congr 2
  unfold cOf
  exact (kmCoord_congr (Dev_toFour_eq C hB x) rfl (transport_map hB lam x) _ _ _ _ _).symm

end Generic

/-! ### Against the strengthened identification `Identification2` -/

/-- **The determinant comparison factor** of the new-local cancellation: `κ = det B ∈ 𝒪[G]`. -/
def kappaOf (M : Identification2 b dK hK cE tK) : MonoidAlgebra OO (SignGroup b) :=
  (M.C.map (φO b)).B.det

/-- `κ` is an `S`-unit (tex 5510–5512). -/
theorem isUnit_kappa (M : Identification2 b dK hK cE tK) : IsUnit (kappaOf M) := M.isUnit_B

/-- **GLUE: the corrected coordinate is `η` times the relaxed coordinate** (tex 4219–4222:
`ũ = η u_rel`), for every representation `ũ_x = g_x / 2^{e_x}`. -/
def CorrectedIsEta {ℓ : ℕ} (Dd : RCData ℓ) (F : Family) (η : MonoidAlgebra OO (SignGroup F.b))
    (urel : Addr F.b → FractionRing OO) : Prop :=
  ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
    ∀ x, uK (e x) (g x) = evK (sgnChar x) η * urel x

/-- **GLUE: the relaxed coordinate is the Knudsen–Mumford coordinate of the original complex**
(the coordinate of `[z] ⊗ [λ]` of the sign-evaluated pre-cancellation complex `C_x` in the original
determinant basis, oriented by `σPre`; tex 3877–3892, 5513–5516), where `Δ_x ≠ 0`. -/
def RelIsKM (M : Identification2 b dK hK cE tK) (urel : Addr b → FractionRing OO)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup b))
    (hz : M.D.d1 *ᵥ z = 0) (hlam : lam ᵥ* fromRows (M.C.map (φO b)).X (M.C.map (φO b)).Y = 0) :
    Prop :=
  ∀ x : Addr b, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
    urel x = kmCoord (PreComplex'.toFour (Cev (M.C.map (φO b)) x)) (evK (sgnChar x) ∘ z)
      (evK (sgnChar x) ∘ lam) (hzev (hzC M.isUnit_B hz) x) (hlamev hlam x)
      (σPre M.C.m0 M.C.m1 M.C.m2 M.C.N)

/-- **E1a (`CoordLink`) for the Knudsen–Mumford coordinate of the remaining complex** (PROVED
from `CorrectedIsEta` and `RelIsKM`): `ũ_x = η_x κ_x c_x` with `κ = det B` and
`c = cOf M.D z μ`, `μ = λ ∘ incl`; in the form expected by lane ClearingComplex's
`clearingInputsCx_of_km`. -/
theorem coordLink_of_km {ℓ : ℕ} (Dd : RCData ℓ) (F : Family) (M : Identification2 F.b dK hK cE tK)
    (z : Fin M.D.m0 ⊕ Unit ⊕ Fin M.D.m1 → MonoidAlgebra OO (SignGroup F.b))
    (lam : (Fin M.C.m1 ⊕ Unit ⊕ Fin M.C.m2) ⊕ M.C.N → MonoidAlgebra OO (SignGroup F.b))
    (hz : M.D.d1 *ᵥ z = 0)
    (hlam : lam ᵥ* fromRows (M.C.map (φO F.b)).X (M.C.map (φO F.b)).Y = 0)
    (η : MonoidAlgebra OO (SignGroup F.b)) (urel : Addr F.b → FractionRing OO)
    (hη : CorrectedIsEta Dd F η urel) (hrel : RelIsKM M urel z lam hz hlam) :
    ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g →
      CoordLink M.toIdentification.B (kappaOf M) η 0 e g
        (cOf M.D z (transportFun (M.C.map (φO F.b)) lam) hz
          (hμ_cancel (M.C.map (φO F.b)) M.isUnit_B hlam)) :=
  coordLink_core Dd F (M.C.map (φO F.b)) M.isUnit_B M.toIdentification.B z lam hz hlam η urel
    hη hrel

/-! ### The (4.7) bridge: `CorrectedIsEta` from RC15's `corrected_eq` -/

/-- **`CorrectedIsEta` from the common coordinate and RC15's η algebra** (PROVED): if at every
character `x` the corrected coordinate is `(∏_{q unused} ε_q) u_{prim,x}` (the common-coordinate
identity (4.7)) and the hypotheses of `corrected_eq` hold (the signs of `x(g_q)`, the evaluated
ratios `x(l_q) x(e_q⁻¹)² = 1 + 2x(v_q)` and the multi-prime (4.7) between `u_rel` and `u_prim`),
then `ũ_x = η_x u_{rel,x}` with `η = ∏_q (1 + v_q(1 + g_q))`. -/
theorem correctedIsEta_of_47 {ℓ : ℕ} (Dd : RCData ℓ) (F : Family) {ι : Type} [DecidableEq ι]
    (Q : Finset ι) (v gq l eq ei : ι → MonoidAlgebra OO (SignGroup F.b))
    (ε : Addr F.b → ι → FractionRing OO) (urel uprim : Addr F.b → FractionRing OO)
    [∀ x : Addr F.b, DecidablePred fun q => evK (sgnChar x) (gq q) = 1]
    (hsign : ∀ x, ∀ q ∈ Q, evK (sgnChar x) (gq q) = 1 ∨ evK (sgnChar x) (gq q) = -1)
    (hratio : ∀ x, ∀ q ∈ Q, evK (sgnChar x) (l q) * evK (sgnChar x) (ei q) ^ 2 =
      1 + 2 * evK (sgnChar x) (v q))
    (hinv : ∀ x, ∀ q ∈ Q, evK (sgnChar x) (eq q) * evK (sgnChar x) (ei q) = 1)
    (h47 : ∀ x, (∏ q ∈ Q with evK (sgnChar x) (gq q) = 1, evK (sgnChar x) (l q)) * urel x =
      (∏ q ∈ Q with evK (sgnChar x) (gq q) = 1, evK (sgnChar x) (eq q) ^ 2 * ε x q) * uprim x)
    (hcommon : ∀ (e : Addr F.b → ℕ) (g : Addr F.b → Lam), UTildeRep Dd F e g → ∀ x,
      uK (e x) (g x) = (∏ q ∈ Q with evK (sgnChar x) (gq q) = 1, ε x q) * uprim x) :
    CorrectedIsEta Dd F (ZInQ.Manuscript.RC.Central.eta Q v gq) urel := by
  intro e g hrep x
  rw [hcommon e g hrep x, ZInQ.Manuscript.RC.Central.corrected_eq (evK (sgnChar x)) Q v gq l eq ei
    (ε x) (urel x) (uprim x) (hsign x) (hratio x) (hinv x) (h47 x)]

end ZInQ.Contrib.CloudB3RC53.CoordLink
