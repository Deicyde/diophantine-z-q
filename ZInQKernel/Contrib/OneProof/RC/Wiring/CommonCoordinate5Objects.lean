import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate4
import ZInQKernel.Contrib.OneProof.RC.Wiring.Uniform
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Symbols
import ZInQKernel.Contrib.OneProof.RC.Rings.GroupRing

/-!
# Theorem 5.3, Lane RC32: the objects of Lemma `ex:arith-common-coordinate` and where they live

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex 4142–4328) works with two carriers:

* the **universal** coefficient ring `R = 𝒪[G]`, `𝒪 = (Λ_{(2)})^`, `Λ = ℤ₂[[t]]`, `G = 𝔽₂^b`
  (tex 2747–2751, 4148–4149, 4196–4229, 4297–4308): the inertia generators `g_q`, the scalars `z_q`
  defined with a Frobenius lift, the point factors `e_q` (units of `R`), the quotient factors
  `l_q`, `v_q = (l_q/e_q² − 1)/2` and the universal correction `η = ∏_{q ∈ Q} (1 + v_q(1 + g_q))`;
* the **scalar** constituent at a character `x`, over `A = Λ_(t)` with fraction field
  `F = Frac Λ` (tex 4341–4342): the primitive coordinate `u_{prim,x}` (regular at `t = 0` where the
  text proves it), the relaxed coordinates, and the evaluated `e_q(x)`, `l_q(x)`, `e_q(x)⁻¹`,
  `v_q(x)` and `η_x`. Evaluated, `e_q(x) ∈ Λ` may vanish at `t = 0`; so `e_q(x)⁻¹`, `v_q(x)` and `η_x`
  lie in `F` (in `Λ_{(2)}`, since `e_q(x) ∉ (2)`) and may have a pole at `t = 0` (tex 4153–4155,
  4229–4231, 4318–4320). They are therefore evaluated in `F`, never in `ℚ₂[[t]]`.

This file defines both sets of objects from the family and the curve, with no free ring:

| object | tex | definition here | kind |
|---|---|---|---|
| `g_q ∈ G`, `x(g_q) = (−1)^{λ_q(x)}` | 4283–4285 | `inertiaGen`, `sgnChar_inertiaGen` | definition, PROVED |
| `ε(F̃r_q) ∈ G`, the image of a Frobenius lift | 4285–4291 | `frobLift` (lift choice `c`) | definition |
| `x(ε(F̃r_q)) = (h_x/q)` at an unused `q` | 4288–4292 | `sgnChar_frobLift_of_unused` | PROVED |
| `a_q` | 4213 | `apE ℓ q`, Mathlib's `L(E,s)` coefficient | definition (RC3: `q + 1 − |Ẽ(𝔽_q)|`) |
| `z = x(z_q) = x(ε(F̃r_q))(1 + t) ∈ Λ^×` | 4144–4145, 4286–4292 | `zAt` | definition |
| `e_q(x) = a_q − z − z⁻¹ ∈ Λ`, nonzero | 4145, 4158 | `ptFac`, `ptFac_ne_zero` | definition, PROVED |
| `l_q(x) = det(1 − q⁻¹zFr)det(1 − q⁻¹z⁻¹Fr) ∈ Λ` | 4209–4213 | `quotFac` (through `tr = a_q`, `det = q`) | definition |
| `e_q(x)`, `l_q(x)` in `F`; `v_q(x) = (l/e² − 1)/2 ∈ F` | 4219–4220 | `eF`, `lF`, `vF` | definition |
| `η_x = ∏_{q∈Q} (1 + v_q(x)(1 + x(g_q))) ∈ F` | 4221–4223 | `etaF`, `etaF_eq` (`= ∏_{unused} l/e²`) | definition, PROVED |

The universal objects over `𝒪[G]`, their integrality and their evaluation are in
`CommonCoordinate5Universal.lean`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Central ZInQ.Manuscript.RC.Uniform
  ZInQ.Contrib.CloudB3RC53

/-! ## The inertia generators and the Frobenius lifts in `G = 𝔽₂^b` -/

/-- The vector of the linear form `λ_q`: its `i`-th entry is `λ_q(e_i)`. -/
def inertiaVec (Fam : Family) (q : ℕ) : Addr Fam.b := fun i => Fam.lam q (Pi.single i 1)

/-- `∑_i x_i λ_q(e_i) = λ_q(x)` (PROVED). -/
theorem sum_mul_inertiaVec (Fam : Family) (q : ℕ) (x : Addr Fam.b) :
    ∑ i, x i * inertiaVec Fam q i = Fam.lam q x := by
  conv_rhs => rw [pi_eq_sum_univ' x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- **The inertia generator `g_q ∈ G`** of the universal quadratic character at `q`
(tex 4283–4285): the element of `G = 𝔽₂^b` with `x(g_q) = (−1)^{λ_q(x)}` for every character `x`. -/
def inertiaGen (Fam : Family) (q : ℕ) : Determinant.SignGroup Fam.b :=
  Multiplicative.ofAdd (inertiaVec Fam q)

/-- The sign character of an address on `ofAdd v` (PROVED). -/
theorem sgnChar_ofAdd {b : ℕ} (x : Addr b) (v : Addr b) :
    Determinant.sgnChar x (Multiplicative.ofAdd v) =
      if (∑ i, x i * v i) = 0 then 1 else -1 := rfl

/-- **`x(g_q) = (−1)^{λ_q(x)}`** (tex 4285): `x(g_q) = 1` exactly when `λ_q(x) = 0` (PROVED). -/
theorem sgnChar_inertiaGen (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    Determinant.sgnChar x (inertiaGen Fam q) = if Fam.lam q x = 0 then 1 else -1 := by
  rw [inertiaGen, sgnChar_ofAdd, sum_mul_inertiaVec]

/-- `δ(d, q) ∈ 𝔽₂`: `0` when `(d/q) = 1`, `1` otherwise (the additive form of an unramified
quadratic character at a Frobenius). -/
def legendreBit (d : ℤ) (q : ℕ) : ZMod 2 := if jacobiSym d q = 1 then 0 else 1

/-- **The image in `G` of a lift of arithmetic Frobenius at `q`** (tex 4283–4291). The universal
quadratic character is `ε = ∑_{q'} δ_{q'} g_{q'}`, `δ_{q'}` the additive quadratic character of
`q'^*`; at a lift `F̃r_q` every other graph prime `q'` contributes the unramified value
`δ(q'^*, q)`, and the ramified component at `q` itself is the lift choice `c` ("Changing the
Frobenius lift can therefore only replace `z_q` by `g_q z_q`", tex 4290–4291). -/
def frobLiftVec (Fam : Family) (q : ℕ) (c : ZMod 2) : Addr Fam.b :=
  ∑ q' ∈ Fam.Q.erase q, legendreBit (qstar q') q • inertiaVec Fam q' + c • inertiaVec Fam q

/-- The Frobenius lift as an element of `G` (lift choice `c`). -/
def frobLift (Fam : Family) (q : ℕ) (c : ZMod 2) : Determinant.SignGroup Fam.b :=
  Multiplicative.ofAdd (frobLiftVec Fam q c)

/-- `(−1)^{s.val}` turns sums in `𝔽₂` into products (PROVED). -/
theorem neg_one_pow_val_add (a b : ZMod 2) :
    (-1 : ℤ) ^ (a + b).val = (-1) ^ a.val * (-1) ^ b.val := by
  fin_cases a <;> fin_cases b <;> rfl

/-- `(−1)^{(∑ a_i).val} = ∏ (−1)^{a_i.val}` in `ℤ` (PROVED). -/
theorem neg_one_pow_val_sum {ι : Type*} (s : Finset ι) (a : ι → ZMod 2) :
    (-1 : ℤ) ^ (∑ i ∈ s, a i).val = ∏ i ∈ s, (-1 : ℤ) ^ (a i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, neg_one_pow_val_add, ih]

/-- The sign of an element of `𝔽₂` as an integer (PROVED). -/
theorem ite_eq_neg_one_pow_val (s : ZMod 2) :
    ((if s = 0 then (1 : ℤˣ) else -1 : ℤˣ) : ℤ) = (-1) ^ s.val := by
  fin_cases s <;> rfl

/-- `(d/q) = (−1)^{δ(d,q)}` when `(d/q) = ±1` (PROVED). -/
theorem jacobiSym_eq_neg_one_pow_legendreBit {d : ℤ} {q : ℕ}
    (h : jacobiSym d q = 1 ∨ jacobiSym d q = -1) :
    jacobiSym d q = (-1) ^ (legendreBit d q).val := by
  unfold legendreBit
  rcases h with h | h
  · rw [ite_eq_left h, h]; rfl
  · rw [ite_eq_right (by rw [h]; decide), h]; rfl

/-- `(q'^*/q) = ±1` for distinct primes `q ≠ q'`, `q` odd (PROVED). -/
theorem jacobiSym_qstar_eq_one_or {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) (hne : q' ≠ q) :
    jacobiSym (qstar q') q = 1 ∨ jacobiSym (qstar q') q = -1 := by
  apply jacobiSym.eq_one_or_neg_one
  have hcop : Nat.Coprime q' q := (Nat.coprime_primes hq' hq).mpr hne
  unfold qstar
  apply Int.isCoprime_iff_gcd_eq_one.mp
  exact IsCoprime.mul_left (IsCoprime.pow_left isCoprime_one_left.neg_left)
    (Nat.isCoprime_iff_coprime.mpr hcop)

/-- `(h_x/q) = ∏_{q' ∈ Q} (q'^*/q)^{λ_{q'}(x)}` (PROVED). -/
theorem jacobiSym_h (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    jacobiSym (Fam.h x) q = ∏ q' ∈ Fam.Q, jacobiSym (qstar q') q ^ (Fam.lam q' x).val := by
  unfold Family.h
  classical
  induction Fam.Q using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, jacobiSym.mul_left, jacobiSym.pow_left, ih]

/-- **At an unused prime the Frobenius lift evaluates to the Legendre symbol of `h_x`**
(tex 4288–4292): for `λ_q(x) = 0`, `x(ε(F̃r_q)) = (h_x/q)`, the genuine unramified quadratic sign,
whatever the lift choice. PROVED. -/
theorem sgnChar_frobLift_of_unused (Fam : Family) (hQ : ∀ q ∈ Fam.Q, q.Prime) {x : Addr Fam.b}
    {q : ℕ} (hq : q ∈ Fam.Q) (hx : Fam.lam q x = 0) (c : ZMod 2) :
    ((Determinant.sgnChar x (frobLift Fam q c) : ℤˣ) : ℤ) = jacobiSym (Fam.h x) q := by
  have hsum : (∑ i, x i * frobLiftVec Fam q c i) =
      ∑ q' ∈ Fam.Q.erase q, legendreBit (qstar q') q * Fam.lam q' x := by
    simp only [frobLiftVec, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.mul_sum, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    have h2 : ∑ i, x i * (c * inertiaVec Fam q i) = 0 := by
      have : ∑ i, x i * (c * inertiaVec Fam q i) = c * ∑ i, x i * inertiaVec Fam q i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [this, sum_mul_inertiaVec, hx, mul_zero]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [← sum_mul_inertiaVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [frobLift, sgnChar_ofAdd, ite_eq_neg_one_pow_val, hsum, neg_one_pow_val_sum, jacobiSym_h,
    ← Finset.mul_prod_erase Fam.Q _ hq, hx]
  simp only [ZMod.val_zero, pow_zero, one_mul]
  refine Finset.prod_congr rfl fun q' hq' => ?_
  have hne : q' ≠ q := Finset.ne_of_mem_erase hq'
  have hq'Q : q' ∈ Fam.Q := Finset.mem_of_mem_erase hq'
  rw [jacobiSym_eq_neg_one_pow_legendreBit (jacobiSym_qstar_eq_one_or (hQ q hq) (hQ q' hq'Q) hne),
    ← pow_mul]
  have : ((legendreBit (qstar q') q) * Fam.lam q' x).val =
      ((legendreBit (qstar q') q).val * (Fam.lam q' x).val) % 2 := ZMod.val_mul _ _
  rw [this, ← neg_one_pow_eq_pow_mod_two]

/-! ## The scalar carrier `F = Frac Λ` and the evaluated objects -/

/-- **`F = Frac Λ`**, the fraction field of `A = Λ_(t)` (tex 4341–4342): the carrier of the
generic class-functional coordinates and of the evaluated `e_q⁻¹`, `v_q`, `η_x`. -/
abbrev FracLam : Type := FractionRing Lambda

/-- `Λ → F`. -/
abbrev lamToF : Lambda →+* FracLam := algebraMap Lambda FracLam

/-- `ℤ₂ → F`. -/
abbrev zTwoToF : ℤ_[2] →+* FracLam := lamToF.comp PowerSeries.C

/-- **`c ∈ Λ^×`, viewed in `F`** (the units of (4.7), tex 4187–4193). -/
def LamUnitF (c : FracLam) : Prop := ∃ e : Lambdaˣ, c = lamToF (e : Lambda)

theorem isUnit_one_add_X : IsUnit (1 + PowerSeries.X : Lambda) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  simp

/-- `1 + t ∈ Λ^×`: the value of the moving character at every graph orientation
(tex 4276–4277, 4287–4288). -/
def onePlusT : Lambdaˣ := isUnit_one_add_X.unit

@[simp] theorem onePlusT_val : (onePlusT : Lambda) = 1 + PowerSeries.X := rfl

/-- **The trace of Frobenius `a_q` of `E = E_ℓ`** (tex 4213): the coefficient at `q` of Mathlib's
`L(E, s)`; at a prime `q ∤ 6ℓ` it is `q + 1 − |Ẽ(𝔽_q)|` (lane RC3's `LFunction_curve_apply_prime`). -/
def apE (ℓ : ℕ) (q : ℕ) : ℤ := (Ecurve ℓ).LFunction q

/-- **`a_q` is even at every good odd prime** (tex 4200–4201: "Since `E[2]` is rational, `a_q` is
even at every good odd prime"; PROVED from the full rational two-torsion, lane RC24's
`apEven_curve`). -/
theorem apE_even {ℓ q : ℕ} (hq : q.Prime) (hgood : ¬ ((q : ℤ) ∣ 6 * ℓ)) : Even (apE ℓ q) := by
  have hM : ∀ p : ℕ, p.Prime → p ∣ 6 * (ℓ : ℤ).natAbs → p ∣ 6 * ℓ := by
    intro p _ hp; simpa using hp
  have hcop : Nat.Coprime q (6 * ℓ) :=
    (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h' => hgood (by exact_mod_cast h')
  have := ZInQ.Manuscript.RC.AddressGenuine.apEven_curve (ℓ : ℤ) (6 * ℓ) hM q hq hcop
  simpa [apE, Ecurve] using this

/-- **The sign of the Frobenius lift at the address** `x(ε(F̃r_q)) = ±1` (lift choice `0`). -/
def frobSign (Fam : Family) (x : Addr Fam.b) (q : ℕ) : ℤˣ :=
  Determinant.sgnChar x (frobLift Fam q 0)

/-- **The scalar Frobenius value** `z = x(z_q) = x(ε(F̃r_q)) (1 + t) ∈ Λ^×` (tex 4144–4145,
4286–4292; the fixed base character is trivial, `h₀ = 1`, tex 4331). -/
def zAt (Fam : Family) (x : Addr Fam.b) (q : ℕ) : Lambdaˣ :=
  Units.map (Int.castRingHom Lambda).toMonoidHom (frobSign Fam x q) * onePlusT

/-- **The point factor `e_q(x) = a_q − z − z⁻¹ ∈ Λ`** (tex 4145, 4158). -/
def ptFac (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) : Lambda :=
  pointFactor (apE ℓ q : Lambda) (zAt Fam x q : Lambda) ((zAt Fam x q)⁻¹ : Lambdaˣ)

/-- `q⁻¹ ∈ ℤ₂` (a unit for odd `q`; tex 4318–4320). -/
def qInv (q : ℕ) : ℤ_[2] := Ring.inverse (q : ℤ_[2])

/-- The two-place quotient factor through the trace `a` and determinant `q` of `Fr_q`:
`(1 − q⁻¹ z a + (q⁻¹z)² q)(1 − q⁻¹ z⁻¹ a + (q⁻¹z⁻¹)² q)` (tex 4209–4213). -/
def quotPoly {K : Type*} [CommRing K] (a q qi z zi : K) : K :=
  (1 - qi * z * a + (qi * z) ^ 2 * q) * (1 - qi * zi * a + (qi * zi) ^ 2 * q)

/-- `quotientFactor` is `quotPoly` for a Frobenius matrix with trace `a` and determinant `q`
(PROVED; RC15's `det_one_sub_smul`). -/
theorem quotientFactor_eq_quotPoly {K : Type*} [CommRing K] {Fr : Matrix (Fin 2) (Fin 2) K}
    {a q : K} (qi z zi : K) (ha : Fr.trace = a) (hd : Fr.det = q) :
    quotientFactor Fr qi z zi = quotPoly a q qi z zi := by
  unfold quotientFactor quotPoly
  rw [det_one_sub_smul, det_one_sub_smul, ha, hd]

/-- `quotPoly` commutes with ring homomorphisms (PROVED). -/
theorem map_quotPoly {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L) (a q qi z zi : K) :
    f (quotPoly a q qi z zi) = quotPoly (f a) (f q) (f qi) (f z) (f zi) := by
  simp only [quotPoly, map_mul, map_sub, map_add, map_one, map_pow]

/-- **The quotient factor `l_q(x) = det(1 − q⁻¹zFr_q) det(1 − q⁻¹z⁻¹Fr_q) ∈ Λ`** (tex 4209–4213),
`tr Fr_q = a_q`, `det Fr_q = q`. -/
def quotFac (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) : Lambda :=
  quotPoly (apE ℓ q : Lambda) (q : Lambda) (PowerSeries.C (qInv q)) (zAt Fam x q : Lambda)
    ((zAt Fam x q)⁻¹ : Lambdaˣ)

/-- `e_q(x)` in `F`. -/
def eF (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) : FracLam := lamToF (ptFac ℓ Fam x q)

/-- `l_q(x)` in `F`. -/
def lF (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) : FracLam := lamToF (quotFac ℓ Fam x q)

/-- **`v_q(x) = (l_q(x)/e_q(x)² − 1)/2`, evaluated in `F`** (tex 4219–4220; it lies in `Λ_{(2)}`
and may have a pole at `t = 0`). -/
def vF (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) : FracLam :=
  (lF ℓ Fam x q / eF ℓ Fam x q ^ 2 - 1) / 2

/-- **`x(g_q) = ±1` in `F`** (tex 4285). -/
def gF (Fam : Family) (x : Addr Fam.b) (q : ℕ) : FracLam :=
  ((Determinant.sgnChar x (inertiaGen Fam q) : ℤˣ) : ℤ)

/-- **`η_x`, the universal correction evaluated at `x`, in `F`** (tex 4221–4223, 4229):
`η_x = ∏_{q ∈ Q} (1 + v_q(x)(1 + x(g_q)))`. -/
def etaF (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) : FracLam :=
  Central.eta Fam.Q (vF ℓ Fam x) (gF Fam x)

/-! ## Facts about the evaluated objects -/

theorem gF_of_unused {Fam : Family} {x : Addr Fam.b} {q : ℕ} (h : Fam.lam q x = 0) :
    gF Fam x q = 1 := by
  rw [gF, sgnChar_inertiaGen, ite_eq_left h]; simp

theorem gF_of_active {Fam : Family} {x : Addr Fam.b} {q : ℕ} (h : Fam.lam q x ≠ 0) :
    gF Fam x q = -1 := by
  rw [gF, sgnChar_inertiaGen, ite_eq_right h]; simp

/-- `(1 + t) · e_q(x) = a_q (1 + t) − σ (1 + t)² − σ` for the sign `σ = x(ε(F̃r_q))` (PROVED). -/
theorem one_add_X_mul_ptFac (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    (1 + PowerSeries.X) * ptFac ℓ Fam x q =
      (apE ℓ q : Lambda) * (1 + PowerSeries.X) -
        ((frobSign Fam x q : ℤ) : Lambda) * (1 + PowerSeries.X) ^ 2 -
          ((frobSign Fam x q : ℤ) : Lambda) := by
  have hσ : ((frobSign Fam x q : ℤ) : Lambda) * ((frobSign Fam x q : ℤ) : Lambda) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hzi : ((zAt Fam x q)⁻¹ : Lambdaˣ) =
      ((frobSign Fam x q : ℤ) : Lambda) * ((onePlusT⁻¹ : Lambdaˣ) : Lambda) := by
    rw [zAt, mul_inv, Units.val_mul, ← map_inv, mul_comm]
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, eq_intCast,
      Int.units_inv_eq_self]
    ring
  have hu : (1 + PowerSeries.X : Lambda) * ((onePlusT⁻¹ : Lambdaˣ) : Lambda) = 1 := by
    rw [← onePlusT_val, Units.mul_inv]
  unfold ptFac pointFactor
  rw [hzi]
  simp only [zAt, Units.val_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    eq_intCast, onePlusT_val]
  linear_combination (-((frobSign Fam x q : ℤ) : Lambda)) * hu

/-- **`e_q(x) ≠ 0`** (PROVED): the coefficient of `t²` in `(1 + t) e_q(x)` is `−σ ≠ 0`. So
`e_q(x)⁻¹` exists in `F`; it need not exist in `Λ` or `ℚ₂[[t]]` (it does not when
`a_q = 2σ`, `ptFac_eval_zero`). -/
theorem ptFac_ne_zero (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) :
    ptFac ℓ Fam x q ≠ 0 := by
  intro h0
  have h := one_add_X_mul_ptFac ℓ Fam x q
  rw [h0, mul_zero] at h
  set σ : ℤ := (frobSign Fam x q : ℤ) with hσdef
  have key : (apE ℓ q : Lambda) * (1 + PowerSeries.X) - (σ : Lambda) * (1 + PowerSeries.X) ^ 2 -
      (σ : Lambda) = PowerSeries.C ((apE ℓ q : ℤ_[2]) - 2 * (σ : ℤ_[2])) * (1 + PowerSeries.X) -
        PowerSeries.C (σ : ℤ_[2]) * PowerSeries.X ^ 2 := by
    simp only [map_sub, map_mul, map_intCast, map_ofNat]
    ring
  rw [key] at h
  have hc : ∀ c : ℤ_[2], PowerSeries.coeff 2 (PowerSeries.C c * (1 + PowerSeries.X)) = 0 := by
    intro c
    rw [PowerSeries.coeff_C_mul]
    simp [PowerSeries.coeff_one, PowerSeries.coeff_X]
  have hs2 : PowerSeries.coeff 2 (PowerSeries.C (σ : ℤ_[2]) * PowerSeries.X ^ 2) = (σ : ℤ_[2]) := by
    rw [PowerSeries.coeff_C_mul_X_pow, ite_eq_left rfl]
  have h2 := congrArg (PowerSeries.coeff 2) h
  rw [map_zero, map_sub, hc, hs2, zero_sub, zero_eq_neg] at h2
  rcases Int.units_eq_one_or (frobSign Fam x q) with hs | hs <;>
  · rw [hσdef, hs] at h2
    norm_num at h2

theorem eF_ne_zero (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) (q : ℕ) : eF ℓ Fam x q ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective Lambda FracLam)).mpr (ptFac_ne_zero ℓ Fam x q)

/-- **`η_x = ∏_{q unused at x} l_q(x)/e_q(x)²`** (tex 4221–4223: "`1 + v_q(1 + g_q)` selects
`l_q/e_q²` at an inactive character and one at an active character"). PROVED. -/
theorem etaF_eq (ℓ : ℕ) (Fam : Family) (x : Addr Fam.b) :
    etaF ℓ Fam x = ∏ q ∈ unusedAt Fam x, lF ℓ Fam x q / eF ℓ Fam x q ^ 2 := by
  classical
  rw [etaF, Central.eta, unusedAt, Finset.prod_filter]
  refine Finset.prod_congr rfl fun q _ => ?_
  have h2 : (2 : FracLam) ≠ 0 := by
    have h2L : (2 : Lambda) ≠ 0 := by
      intro h
      have := congrArg (PowerSeries.constantCoeff (R := ℤ_[2])) h
      simp only [map_ofNat, map_zero] at this
      exact two_ne_zero this
    have := (map_ne_zero_iff lamToF (IsFractionRing.injective Lambda FracLam)).mpr h2L
    rwa [map_ofNat] at this
  have he := eF_ne_zero ℓ Fam x q
  by_cases h : Fam.lam q x = 0
  · rw [ite_eq_left h, Central.correctionFactor, gF_of_unused h, vF]
    field_simp
    ring
  · rw [ite_eq_right h, Central.correctionFactor, gF_of_active h]
    ring

end ZInQ.Manuscript.RC.Wiring
