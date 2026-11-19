import ZInQKernel.Contrib.CloudB3E1RingClass.KRVal
import ZInQKernel.Contrib.CloudB3E1RingClass.Setup
import ZInQKernel.Contrib.CloudB3E1RingClass.MovingGenuine

/-!
# Assembling the genuine moving data from its remaining core inputs

Manuscript `diophantine_zq.tex`, tex 3530–3595, 3662–3693.

`GenuineMovingCore E n s C` collects what is still needed for a genuine `MovingDataK`, over
`K = ℚ(s) ⊂ ℚ̄` (so the Kummer data and the ring-class data live over the same field). Its fields are
either facts the construction supplies or the inputs still open:
* the data `D` (with `s² = D`), `t`, `kd`, `act`, `over2N`, `m`, `Sexc`;
* `hgen`: the chosen primes generate `Cl(K)` (from `exists_setup`);
* `m_span`: the relation vectors span (from `exists_relation_basis` when `m` is that basis);
* `h2`, `hval`: the active primes are odd and `v_{𝔭_j}(α_a) = m_j^{(a)}`;
* `p_mem`, `hsupp`: the primes under the chosen primes are excluded, and the radicands are units
  away from `Sexc`;
* `placeR_over`;
* open: `δ`, `δ_inj`, `exact`, `rel` and `inertia_eq` on the genuine places `kummerPlaces r`, with
  `x := kummerX`.

`GenuineMovingCore.toInputs` builds `GenuineMovingInputs` with `Pl := kummerPlaces`, `x := kummerX`,
`κ := kummerKappa`. The fields proved, not assumed, are:
* `cls_gen` (`clsGen_of_closure`);
* `KR_val` (`krVal_genuine`);
* `κ_surj` (`kappa_surj_genuine`);
* `frob_kummer` (`frob_kummer_genuine` with `hαunit_of_support`).

`moving_character_core` is then the moving character on the genuine groups (`moving_character_genuine`)
from the core.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Contrib.ChebFD.C10 (Qbar)
open scoped nonZeroDivisors

/-- **The remaining core inputs of a genuine `MovingDataK`** over `K = ℚ(s)` (tex 3530–3595,
3662–3693). Kind: definition (of the structure). -/
structure GenuineMovingCore (E : WeierstrassCurve ℚ) (n : ℕ) (s : Qbar) {S : ℕ}
    (C : RingClassSetup (quadField s) S) where
  D : ℚ
  sqrtD_sq : s ^ 2 = algebraMap ℚ Qbar D
  t : ℕ
  kd : KummerData s n t
  act : Fin S → Prop
  [decAct : DecidablePred act]
  over2N : Fin S → Prop
  act_not_over2N : ∀ j, act j → ¬ over2N j
  /-- the chosen primes generate `Cl(K)` (tex 3532–3534; `exists_setup`) -/
  hgen : Subgroup.closure (Set.range fun j =>
    ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩) = ⊤
  m : Fin t → Fin S → ℤ
  m_span : ∀ v : Fin S → ℤ, ∑ j, v j • setupCls C j = 0 → ∃ b : Fin t → ℤ, v = ∑ a, b a • m a
  /-- the active primes are odd -/
  h2 : ∀ j, act j → (2 : 𝓞 (quadField s)) ∉ (C.𝔭 j).asIdeal
  /-- `v_{𝔭_j}(α_a) = m_j^{(a)}` (tex 3540–3542) -/
  hval : ∀ j, act j → ∀ a,
    (C.𝔭 j).valuation (quadField s) ⟨kd.α a, kd.α_mem a⟩ = WithZero.exp (-(m a j))
  Sexc : Finset ℕ
  p_mem : ∀ j, C.p j ∈ Sexc
  /-- the radicands are units away from `Sexc` (tex 3536–3540) -/
  hsupp : ∀ a (𝔯 : HeightOneSpectrum (𝓞 (quadField s))) (q : ℕ), q.Prime → q ∉ Sexc →
    ((q : ℤ) : 𝓞 (quadField s)) ∈ 𝔯.asIdeal →
      𝔯.valuation (quadField s) ⟨kd.α a, kd.α_mem a⟩ = 1
  placeR_over : ∀ r, GoodPrime E s Sexc r → ((r : ℤ) : 𝓞 (quadField s)) ∈ (C.placeR r).asIdeal
  /-- open (with E2): the connecting map on the genuine places -/
  δ : ∀ r, kummerPlaces r → (Additive (ZMod r)ˣ →+ Additive (setupGal C r))
  δ_inj : ∀ r, GoodPrime E s Sexc r → ∀ v, Function.Injective (δ r v)
  exact : ∀ r, GoodPrime E s Sexc r → ∀ v, ∀ p : Additive (setupGal C r),
    setupPi C r p = 0 ↔ ∃ y, δ r v y = p
  /-- open: the principal relations (tex 3576–3579) -/
  rel : ∀ r, GoodPrime E s Sexc r → ∀ v a,
    ∑ j, m a j • setupQ C r j + δ r v (kummerX (kd.α a) v) = 0
  /-- open: the genuine inertia group is the range of `δ` (tex 3679–3681) -/
  inertia_eq : ∀ r, GoodPrime E s Sexc r → ∀ v, setupInertia C r = (δ r v).range

attribute [instance] GenuineMovingCore.decAct

variable {E : WeierstrassCurve ℚ} {n : ℕ} {s : Qbar} {S : ℕ} {C : RingClassSetup (quadField s) S}

/-- **The genuine `MovingInputs` from the core** (tex 3530–3595, 3662–3693): `Pl := kummerPlaces`,
`x := kummerX`, `κ := kummerKappa`. The fields `cls_gen`, `KR_val`, `κ_surj` and `frob_kummer` are
PROVED. Kind: definition. -/
def GenuineMovingCore.toInputs (I : GenuineMovingCore E n s C) : GenuineMovingInputs E n C where
  D := I.D
  sqrtD := s
  sqrtD_sq := I.sqrtD_sq
  t := I.t
  kd := I.kd
  act := I.act
  over2N := I.over2N
  act_not_over2N := I.act_not_over2N
  cls_gen := clsGen_of_closure C I.hgen
  m := I.m
  m_span := I.m_span
  KR_val := krVal_genuine s I.kd I.act I.m C.𝔭 I.h2 I.hval
  Sexc := I.Sexc
  p_mem := I.p_mem
  placeR_over := I.placeR_over
  Pl := kummerPlaces
  δ := I.δ
  δ_inj := I.δ_inj
  exact := I.exact
  x _ v a := kummerX (I.kd.α a) v
  rel := I.rel
  κ _ v := kummerKappa n I.kd.ζ v
  κ_surj := kappa_surj_genuine I.kd I.Sexc
  inertia_eq := I.inertia_eq
  frob_kummer := frob_kummer_genuine I.kd I.Sexc (hαunit_of_support s I.kd I.Sexc I.hsupp)

open ZInQ.Manuscript.RC.GlueSweep.Tate ZInQ.Manuscript.RC.Moving in
/-- **The moving character on the genuine groups, from the core inputs** (tex 2729–2737,
3500–3506, 4258–4268): `moving_character_genuine` for `GenuineMovingCore.toInputs`. Kind: PROVED. -/
theorem moving_character_core {ℓ : ℕ}
    (I : GenuineMovingCore (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n s C)
    (hS : ZInQ.Manuscript.RC.PrintsArith.SerreThm3) (hcm : ZInQ.Manuscript.RC.PrintsArith.CMjInteger)
    (hℓ : 0 < ℓ) (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 (quadField s))))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (T : Finset ℕ) :
    ∃ r : ℕ, r ∉ T ∧ r.Prime ∧ GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) s I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : ZInQ.Manuscript.RC.SelmerComplex.GKS (quadField s) (C.Sr r) →*
          Multiplicative (ZMod (2 ^ n)),
        (∀ y : ZMod (2 ^ n), ∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR r).adicCompletion (quadField s)),
          ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.placeR r) σ) =
            Multiplicative.ofAdd y) ∧
        (∀ v ∈ P, ∀ σ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) v,
          ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) v σ) = 1) ∧
        (∀ j, I.act j → ∀ φ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) (C.𝔭 j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion (quadField s)) φ →
            ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.𝔭 j) φ) =
              Multiplicative.ofAdd 1) ∧
        (∀ j, I.act j → ∀ φ : ZInQ.Manuscript.RC.SelmerComplex.Gloc (quadField s) (C.𝔭bar j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion (quadField s)) φ →
            ξ (ZInQ.Manuscript.RC.SelmerComplex.locMap (quadField s) (C.Sr r) (C.𝔭bar j) φ) =
              Multiplicative.ofAdd (-1)) ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          2 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          2 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          1 + (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
          1 - (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r + r ∧
        ∀ χ : ℤ, (χ = 1 ∨ χ = -1) →
          ¬ (2 : ℤ) ^ (cE (tateImageEcurveS hS hcm hℓ).d + 1) ∣
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ :=
  moving_character_genuine I.toInputs hS hcm hℓ hT P hP B T

end ZInQ.Contrib.CloudB3E1RingClass
