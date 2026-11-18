import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.ConstituentLeaf
import ZInQKernel.Contrib.OneProof.RC.Wiring.ConstituentModelRel

/-!
# Theorem 5.3, Lane RC24: the genuine instances of lane RC0's corrected models

Lane RC0's corrected interfaces `TraceModelRel` and `ConstituentModelRel` (`RC/Wiring/`), with
`chebotarev` relative to `N_U` and `chi_surj` at sets of good primes, are instantiated here by the
genuine Galois objects of lane RC24: the group `G_ℚ = Aut(ℚ̄/ℚ)`, genuine Frobenius elements, the
genuine type and bit characters, and `N_U` defined from the characters and the reduced trace
action (`GaloisModel.lean`, `Constituents.lean`):

* `GaloisTraceModel.toTraceModelRel`, `GaloisConstituentModel.toConstituentModelRel`, with their
  ELLIOT inputs carried over (`toConstituentModelRel_inputs`);
* the genuine non-vacuity instance: lane RC0's `ConstituentModelRel` inhabited with one constituent
  whose representation is the genuine `2`-adic Tate representation of an elliptic curve
  (`tateConstituentModelRel`, from `tateConstituentModel'`);
* the conjuncts 8⁗ and 9⁶ of lane RC0's `AddressPackage6` from the genuine constituent models of
  `ConstituentLeaf.lean` (`addressPackage6_odd_of_genuine`, `addressPackage6_even_of_genuine`),
  with `a_p` even PROVED.

The constituents of the actual forms `F_U = θ H_U` are weight-two newforms and Eisenstein pairs
(tex 9647–9654, 9762–9771), not `E` or its twists; the Tate representation only shows that the
interface is inhabited by a genuine Galois representation.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary Filter
open ZInQ.Manuscript.RC.PrintsArith

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
  {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ} {chiType : GalQ →* Multiplicative L}

/-- **The genuine Galois trace model as lane RC0's `TraceModelRel`** (PROVED: `G = G_ℚ`,
`chiBit = bitChar`, `N = galN`; `level`, `N_anti`, `N_chi`, `chi_surj` (good `U`), `typ_frob`,
`bit_frob` are the theorems of `GaloisModel.lean`; tex 9641–9771, 9905–9953). -/
def GaloisTraceModel.toTraceModelRel (X : GaloisTraceModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) : TraceModelRel T R ap B where
  G := GalQ
  M := X.M
  t := X.t
  d := X.d
  F := X.F
  read := X.read
  frob := X.frob
  N := X.N
  chiType := chiType
  chiBit := bitChar
  trace_mul := X.trace_mul
  det_orbit := X.det_orbit
  two_fresh := X.two_fresh
  trace_one := X.trace_one
  level := X.level
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer := X.kummer
  chi_surj := X.chi_surj htyp
  chebotarev := X.chebotarev
  t_class := X.t_class
  typ_frob := X.typ_frob htyp
  bit_frob := X.bit_frob
  reading := X.reading
  o12 := X.o12

/-- **The genuine constituent model as lane RC0's `ConstituentModelRel`** (PROVED: `G = G_ℚ`,
`chiBit = bitChar`, `N = consN`; `level_red`, `N_anti`, `N_chi`, `chi_surj` (good `U`),
`typ_frob`, `bit_frob` are the theorems of `Constituents.lean`; tex 9638–9797). -/
def GaloisConstituentModel.toConstituentModelRel (X : GaloisConstituentModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) : ConstituentModelRel T R ap B where
  G := GalQ
  I := X.I
  K := X.K
  O := X.O
  m := X.m
  two_mem := X.two_mem
  ρ := X.ρ
  Λ := X.Λ
  stable_t := X.stable_t
  stable_d := X.stable_d
  F := X.F
  read := X.read
  frob := X.frob
  N := X.N
  chiType := chiType
  chiBit := bitChar
  det_orbit := X.det_orbit
  two_fresh := X.two_fresh
  level_red := fun U g n hn => X.level_red U g n hn
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer := X.kummer
  chi_surj := X.chi_surj htyp
  chebotarev := X.chebotarev
  typ_frob := X.typ_frob htyp
  bit_frob := X.bit_frob

/-- **The ELLIOT inputs carry over** (PROVED: the two readings are stated for the same reduced
operators). -/
theorem GaloisConstituentModel.toConstituentModelRel_inputs
    (X : GaloisConstituentModel T R ap B chiType) (htyp : IsTypeChar T chiType)
    (hI : X.Inputs) : (X.toConstituentModelRel htyp).Inputs := hI

/-- **Lane RC0's `ConstituentModelRel` is inhabited by a genuine Galois representation**
(PROVED): one constituent, the `2`-adic Tate representation of an elliptic curve `E/ℚ`, over the
genuine type data `typeData m` and the genuine group `G_ℚ`, for the zero reading, with its
inputs. -/
theorem tateConstituentModelRel (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m]
    (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ) :
    ∃ X : ConstituentModelRel (typeData m hm h4) (fun _ => 0) ap B, X.Inputs :=
  ⟨(tateConstituentModel' E m hm h4 ap B).toConstituentModelRel
      (isTypeChar_typeData m hm h4),
    (tateConstituentModel' E m hm h4 ap B).toConstituentModelRel_inputs _
      (tateConstituentModel'_inputs E m hm h4 ap B)⟩

section Leaf6

variable {ℓ : ℕ} (W : WData ℓ) (D : LabelData W) (Rev : Finset ℕ → ZMod 2)

/-- **Conjunct 8⁗ of lane RC0's `AddressPackage6` from the genuine odd constituent models**
(PROVED; `a_p` even by `LabelData.apEven₁`). -/
theorem addressPackage6_odd_of_genuine (h : OddConstituentModels W D) :
    ∀ Wc : ℕ, ∀ᶠ θ in (W.stages : Filter ℕ),
      (∃ X : ConstituentModelRel (D.T₁ θ) (Rodd W θ) (apo ℓ) (Wc + 1), X.Inputs) ∧
        ApEven (D.T₁ θ) (apo ℓ) := by
  intro Wc
  filter_upwards [h Wc] with θ hθ
  obtain ⟨X, hX⟩ := hθ
  have hℓ₀2 : D.ℓ₀ θ ≠ 2 := ne_two_of_coprime_even (dvd_trans (by norm_num) D.four) (D.ℓ₀_cop θ)
  have htyp : IsTypeChar (D.T₁ θ) (stageChar D.m₁ (D.ℓ₀ θ)) :=
    isTypeChar_stage (D.T₁ θ) (D.T₁_m θ) (D.T₁_typ θ) (D.ℓ₀_prime θ) hℓ₀2
  exact ⟨⟨X.toConstituentModelRel htyp, X.toConstituentModelRel_inputs htyp hX⟩, D.apEven₁ θ⟩

/-- **Conjunct 9⁶ of lane RC0's `AddressPackage6` from the genuine even constituent models**
(PROVED; `a_p(E^{(k)})` even by `LabelData.apEven₂`). -/
theorem addressPackage6_even_of_genuine (h : EvenConstituentModels W D Rev) :
    (∀ B, ∃ X : ConstituentModelRel D.T₂ Rev (apk W) B, X.Inputs) ∧ ApEven D.T₂ (apk W) := by
  have htyp : IsTypeChar D.T₂ (typChar D.m₂) := isTypeChar_typeData D.m₂ D.m₂_pos D.four₂
  refine ⟨fun B => ?_, D.apEven₂⟩
  obtain ⟨X, hX⟩ := h B
  exact ⟨X.toConstituentModelRel htyp, X.toConstituentModelRel_inputs htyp hX⟩

end Leaf6

end ZInQ.Manuscript.RC.AddressGenuine
