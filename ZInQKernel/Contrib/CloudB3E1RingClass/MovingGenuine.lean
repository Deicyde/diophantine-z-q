import ZInQKernel.Contrib.CloudB3E1RingClass.ClassGen
import ZInQKernel.Contrib.CloudB3E1RingClass.Decomposition
import ZInQKernel.Contrib.OneProof.RC.CoefModules.Characters

/-!
# The moving character on the genuine Galois groups

Manuscript `diophantine_zq.tex`, Proposition `ex:arith-moving-character` (tex 3500–3506) as used at
tex 2729–2737 and 4258–4268. The character `ξ_i` (and `Ψ_i = (1 + t)^{ξ_i}`) is
* finite;
* trivial at `2N`;
* ramified at a moving conductor prime `r_i` and surjective on inertia there;
* equal to `1` at every prescribed orientation `Fr_q`, and `−1` at the conjugate orientation;
* subject to the trace bounds.
One character serves the whole binary family.

`moving_character_genuine` states this on the GENUINE groups: `ξ : G_{K,S_r} → ℤ/2^n` is the
restriction to the ring class field `H_r` followed by lane RC4/RC17's character of `Gal(H_r/K)`,
for the genuine `MovingDataK` of `GenuineMovingInputs.toMovingDataK`. The properties are:
* every value of `ℤ/2^n` is taken on the genuine inertia group `I_{K_w}` at the place `w` over `r`;
* `ξ` vanishes on the genuine decomposition groups `G_{K_v}`, `v ∈ P` (the places over `2N`);
* every arithmetic Frobenius lift at an active `𝔭_j` has value `1`, and at `𝔭̄_j` value `−1`;
* the trace bounds of Proposition `ex:arith-moving-character`.
`movingPsi_genuine` gives the same for `Ψ = (1 + t)^ξ` with values in `A_i^×` (`n = 2i`).

Kind: PROVED from `SerreThm3` (PRINT), `CMjInteger` (GLUE), `FrobeniusTrace` (PROVED in the tree)
and the inputs `GenuineMovingInputs` (the remaining interface fields, typed over the genuine
objects).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open TauCeti TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory
open ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Manuscript.RC.Moving ZInQ.Manuscript.RC.TateWiring ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.GlueSweep.Tate
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {s : ℕ} {C : RingClassSetup K s} {n ℓ : ℕ}

/-- **The moving character on the genuine groups** (tex 2729–2737, 3500–3506, 4258–4268).
Kind: PROVED. -/
theorem moving_character_genuine (I : GenuineMovingInputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) n C)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ n)),
        -- surjective on the genuine inertia group at the place over `r`
        (∀ y : ZMod (2 ^ n), ∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR r).adicCompletion K),
          ξ (locMap K (C.Sr r) (C.placeR r) σ) = Multiplicative.ofAdd y) ∧
        -- trivial on the genuine decomposition groups at `2N`
        (∀ v ∈ P, ∀ σ : Gloc K v, ξ (locMap K (C.Sr r) v σ) = 1) ∧
        -- value `1` at the active orientations, `−1` at their conjugates
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭 j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion K) φ →
            ξ (locMap K (C.Sr r) (C.𝔭 j) φ) = Multiplicative.ofAdd 1) ∧
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭bar j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion K) φ →
            ξ (locMap K (C.Sr r) (C.𝔭bar j) φ) = Multiplicative.ofAdd (-1)) ∧
        -- the trace bounds
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
            (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ).LFunction r - 2 * χ := by
  obtain ⟨r, hrS, hrp, hgood, hr1, ξ0, hin, h2N, hact, hb1, hb2, hb3, hb4, hb5⟩ :=
    moving_character_ecurve_genuineS hS hcm hℓ hT I.toMovingDataK B S
  have hgood' : GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r := hgood
  let res := ringClassRes (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r)
  let ξ0' : Additive (setupGal C r) →+ ZMod (2 ^ n) := ξ0
  let ξ : GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ n)) :=
    (AddMonoidHom.toMultiplicative ξ0').comp res
  have hξ : ∀ g, ξ g = Multiplicative.ofAdd (ξ0' (Additive.ofMul (res g))) := fun _ => rfl
  refine ⟨r, hrS, hrp, hgood', hr1, ξ, ?_, ?_, ?_, ?_, hb1, hb2, hb3, hb4, hb5⟩
  · intro y
    obtain ⟨z, hz, hzy⟩ := hin y
    obtain ⟨σ, hσ, hσz⟩ := (show Additive.toMul z ∈ inertiaGal (max r 1) (max_one_ne_zero r)
      (C.Sr r) (C.hSr r) (C.placeR r) from hz)
    refine ⟨σ, hσ, ?_⟩
    rw [hξ, ← hzy]
    exact congrArg (fun w => Multiplicative.ofAdd (ξ0' (Additive.ofMul w))) hσz
  · intro v hv σ
    obtain ⟨j, hj, hvj⟩ := hP v hv
    have hz : Additive.ofMul (res (locMap K (C.Sr r) v σ)) ∈
        setupDecomp C r j ⊔ setupDecompBar C r j := by
      rcases hvj with rfl | rfl
      · exact AddSubgroup.mem_sup_left (show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, rfl⟩)
      · exact AddSubgroup.mem_sup_right (show Additive.toMul (Additive.ofMul _) ∈ _ from ⟨σ, rfl⟩)
    rw [hξ]
    change Multiplicative.ofAdd (ξ0 _) = 1
    rw [h2N j hj _ hz]
    rfl
  · intro j hj φ hφ
    have hnm := (I.not_mem hgood' j).1
    have h1 := locGal_frobeniusLift (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭 j) hnm
      (primeToIdeal _ _ (C.𝔭 j) hnm) rfl hφ
    rw [hξ]
    congr 1
    have h2 : Additive.ofMul (res (locMap K (C.Sr r) (C.𝔭 j) φ)) = I.toMovingDataK.q r j := by
      change Additive.ofMul (locGal _ _ _ _ (C.𝔭 j) φ) = setupQ C r j
      rw [setupQ_eq hnm, h1]
    rw [h2]
    exact (hact j hj).1
  · intro j hj φ hφ
    have hnm := (I.not_mem hgood' j).2
    have h1 := locGal_frobeniusLift (max r 1) (max_one_ne_zero r) (C.Sr r) (C.hSr r) (C.𝔭bar j)
      hnm (primeToIdeal _ _ (C.𝔭bar j) hnm) rfl hφ
    rw [hξ]
    congr 1
    have h2 : Additive.ofMul (res (locMap K (C.Sr r) (C.𝔭bar j) φ)) =
        I.toMovingDataK.qbar r j := by
      change Additive.ofMul (locGal _ _ _ _ (C.𝔭bar j) φ) = setupQbar C r j
      rw [setupQbar_eq hnm, h1]
    rw [h2]
    exact (hact j hj).2

open ZInQ.Manuscript.RC.CoefModules in
/-- **`Ψ = (1 + t)^ξ` on the genuine groups** (tex 2729–2737, 2781–2783, 4266–4268), with values
in `A_i^×` and `n = 2i`:
* `Ψ = 1 + t` on a genuine inertia element at `r`;
* `Ψ` is trivial at `2N`;
* `Ψ = 1 + t` on every Frobenius lift at the active orientations, and `(1 + t)^{-1}` at their
  conjugates.
Kind: PROVED. -/
theorem movingPsi_genuine {i : ℕ} [NeZero i]
    (I : GenuineMovingInputs (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) (2 * i) C)
    (hS : SerreThm3) (hcm : CMjInteger) (hℓ : 0 < ℓ)
    (hT : FrobeniusTrace (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ))
    (P : Set (HeightOneSpectrum (𝓞 K)))
    (hP : ∀ v ∈ P, ∃ j, I.over2N j ∧ (v = C.𝔭 j ∨ v = C.𝔭bar j)) (B : ℕ) (S : Finset ℕ) :
    ∃ r : ℕ, r ∉ S ∧ r.Prime ∧ GoodPrime (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ) I.sqrtD I.Sexc r ∧
      (2 : ℤ) ^ B ∣ (r : ℤ) - 1 ∧
      ∃ ξ : GKS K (C.Sr r) →* Multiplicative (ZMod (2 ^ (2 * i))),
        (∃ σ ∈ TauCeti.inertiaSubgroup ((C.placeR r).adicCompletion K),
          movingCharS i ξ (locMap K (C.Sr r) (C.placeR r) σ) = onePlusT i) ∧
        (∀ v ∈ P, ∀ σ : Gloc K v, movingCharS i ξ (locMap K (C.Sr r) v σ) = 1) ∧
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭 j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭 j).adicCompletion K) φ →
            movingCharS i ξ (locMap K (C.Sr r) (C.𝔭 j) φ) = onePlusT i) ∧
        (∀ j, I.act j → ∀ φ : Gloc K (C.𝔭bar j),
          TauCeti.IsArithFrobeniusLift ((C.𝔭bar j).adicCompletion K) φ →
            movingCharS i ξ (locMap K (C.Sr r) (C.𝔭bar j) φ) = (onePlusT i)⁻¹) := by
  obtain ⟨r, hrS, hrp, hgood, hr1, ξ, hin, h2N, hact, hbar, -⟩ :=
    moving_character_genuine I hS hcm hℓ hT P hP B S
  have h1 : 1 < 2 ^ (2 * i) := Nat.one_lt_two_pow (by have := NeZero.ne i; omega)
  have hone : ∀ g, ξ g = Multiplicative.ofAdd 1 → movingCharS i ξ g = onePlusT i := by
    intro g hg
    have : Fact (1 < 2 ^ (2 * i)) := ⟨h1⟩
    change ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * i) (onePlusT i) (onePlusT_pow i)
      (ξ g) = _
    rw [hg, ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom_apply, toAdd_ofAdd, ZMod.val_one,
      pow_one]
  refine ⟨r, hrS, hrp, hgood, hr1, ξ, ?_, ?_, ?_, ?_⟩
  · obtain ⟨σ, hσ, hσ1⟩ := hin 1
    exact ⟨σ, hσ, hone _ hσ1⟩
  · intro v hv σ
    change ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * i) (onePlusT i) (onePlusT_pow i)
      (ξ _) = 1
    rw [h2N v hv σ, map_one]
  · intro j hj φ hφ
    exact hone _ (hact j hj φ hφ)
  · intro j hj φ hφ
    have : Fact (1 < 2 ^ (2 * i)) := ⟨h1⟩
    change ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom (2 * i) (onePlusT i) (onePlusT_pow i)
      (ξ _) = _
    rw [hbar j hj φ hφ, ofAdd_neg, map_inv, ZInQ.Manuscript.RC.HeegnerAlgebra.unitPowHom_apply,
      toAdd_ofAdd, ZMod.val_one, pow_one]

end ZInQ.Contrib.CloudB3E1RingClass
