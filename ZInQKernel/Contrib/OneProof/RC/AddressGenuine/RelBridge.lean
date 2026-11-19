import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Constituents
import ZInQKernel.Contrib.OneProof.RC.Wiring.ConstituentModelRel

/-!
# Theorem 5.3, Lane RC24: the genuine instances of lane RC0's corrected models

Lane RC0's corrected interfaces `TraceModelRel` and `ConstituentModelRel` (`RC/Wiring/`), with
`chebotarev` relative to `N_U` and `chi_surj` at sets of good primes, are instantiated here by the
genuine Galois objects of lane RC24: the group `G_ℚ = Aut(ℚ̄/ℚ)`, genuine Frobenius elements, the
genuine type and bit characters, and `N_U` defined from the characters and the reduced trace
action (`GaloisModel.lean`, `Constituents.lean`).

Round 4: the module of the Galois trace model is `Mst` (no congruence hypothesis on the
operators). Round 3: the constituent model is on coefficientwise reduced expansions
(tex 9639–9646). The faithful bridge is to lane RC0's `TraceModelRel`, whose module is abstract
(`GaloisConstituentModel.toTraceModelRel`). Lane RC0's `ConstituentModelRel` reads the forms in
`Λ/𝔪Λ` and needs, besides the unbudgeted forms, saturation (`Saturated`, not assumed by the text);
the Tate instance satisfies both.

Round 2: lane RC24's models state their module fields only within the operator budget (tex
9447–9468, 9649–9654), while lane RC0's interfaces ask `det_orbit`, `two_fresh`, `kummer` and
`chebotarev` at every `U`. The bridges therefore take the unbudgeted forms as an explicit
hypothesis (`GaloisTraceModel.Unbudgeted`, `GaloisConstituentModel.Unbudgeted`), which the text
does not give off the budget and which holds for the zero-form models:

* `GaloisTraceModel.toTraceModelRel`, `GaloisConstituentModel.toConstituentModelRel`, with their
  ELLIOT inputs carried over (`toConstituentModelRel_inputs`);
* the genuine non-vacuity instance: lane RC0's `ConstituentModelRel` inhabited with one constituent
  whose representation is the genuine `2`-adic Tate representation of an elliptic curve
  (`tateConstituentModelRel`, from `tateConstituentModel'` and `tateConstituentModel'_unbudgeted`).

The round-1 bridges to lane RC0's `AddressPackage6` are withdrawn: that leaf is no longer the
field of the wiring, and its model conjuncts would need the unbudgeted forms. The constituents of
the actual forms `F_U = θ H_U` are weight-two newforms and Eisenstein pairs (tex 9647–9654,
9762–9771), not `E` or its twists; the Tate representation only shows that the interface is
inhabited by a genuine Galois representation.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AddressGenuine

open ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.Symbols
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open ZInQ.Manuscript.RC.PrintsArith

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
  {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ} {chiType : GalQ →* Multiplicative L}

/-- **The genuine Galois trace model as lane RC0's `TraceModelRel`** (PROVED, given the unbudgeted
forms of the module fields: `G = G_ℚ`, `chiBit = bitChar`, `N = galN`; `level`, `N_anti`, `N_chi`,
`chi_surj` (good `U`), `typ_frob`, `bit_frob` are the theorems of `GaloisModel.lean`; tex
9641–9771, 9905–9953). -/
def GaloisTraceModel.toTraceModelRel (X : GaloisTraceModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) (hX : X.Unbudgeted) : TraceModelRel T R ap B where
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
  det_orbit := hX.det_orbit
  two_fresh := hX.two_fresh
  trace_one := X.trace_one
  level := X.level
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer := hX.kummer
  chi_surj := X.chi_surj htyp
  chebotarev := hX.chebotarev
  t_class := X.t_class
  typ_frob := X.typ_frob htyp
  bit_frob := X.bit_frob
  reading := X.reading
  o12 := X.o12

attribute [local instance] GaloisConstituentModel.modMst

/-- **The genuine constituent model as lane RC0's `TraceModelRel`, through its auxiliary quotient
module `Mst`** (PROVED, given the unbudgeted forms; no saturation is needed: lane RC0's
`TraceModelRel` has an abstract module, tex 9639–9646).
The module is the auxiliary quotient `Mst = Λ/Kst`, not an identification
with the image of coefficientwise reduction. Its readings factor through
that reduction; the budgeted orbit identities and subgroup comparison are
proved. The density conversion needs no saturation. The legacy bridge to
`ConstituentModelRel` separately requires `Saturated` and `Unbudgeted`.
This is the faithful bridge to lane RC0's interfaces. -/
def GaloisConstituentModel.toTraceModelRel (X : GaloisConstituentModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) (hX : X.Unbudgeted) (hI : X.Inputs) : TraceModelRel T R ap B :=
  (X.toGaloisTraceModel hI).toTraceModelRel htyp (X.unbudgeted_toGaloisTraceModel hX hI)

/-- **The genuine constituent model as lane RC0's `ConstituentModelRel`** (PROVED, given the
unbudgeted forms AND saturation). Lane RC0's interface reads the forms in `Λ/𝔪Λ` and asks
membership in `𝔪Λ`, which the coefficientwise identities of the text give only for a saturated
module. The text assumes no saturation (tex 9644–9646). The functionals are those of the reduced
expansions, through `Λ/𝔪Λ → (C → 𝒪/𝔪)` (`le_ker_redE`). `G = G_ℚ`, `chiBit = bitChar`,
`N = consN`; the
remaining fields are theorems of `Constituents.lean` (tex 9638–9797). -/
def GaloisConstituentModel.toConstituentModelRel (X : GaloisConstituentModel T R ap B chiType)
    (htyp : IsTypeChar T chiType) (hX : X.Unbudgeted) (hsat : X.Saturated) :
    ConstituentModelRel T R ap B where
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
  read U := (X.read U).comp
    ((X.m • ⊤ : Submodule X.O X.Λ).liftQ X.redE X.le_ker_redE).toAddMonoidHom
  frob := X.frob
  N := X.N
  chiType := chiType
  chiBit := bitChar
  det_orbit U u v := hsat (X.dΛ u (X.tΛ v (X.F U)) - X.tΛ v (X.F U)) (by
    rw [map_sub, sub_eq_zero]
    exact hX.det_orbit U u v)
  two_fresh U g h := hsat _ (hX.two_fresh U g h)
  level_red U g n hn := hsat (X.tΛ (g * n) (X.F U) - X.tΛ g (X.F U)) (by
    rw [map_sub, sub_eq_zero]
    exact X.level_red U g n hn)
  N_anti := X.N_anti
  N_chi := X.N_chi
  kummer := hX.kummer
  chi_surj := X.chi_surj htyp
  chebotarev := hX.chebotarev
  typ_frob := X.typ_frob htyp
  bit_frob := X.bit_frob

/-- **The ELLIOT inputs carry over** (PROVED: the readings of `Λ/𝔪Λ` factor through the reduced
expansions). -/
theorem GaloisConstituentModel.toConstituentModelRel_inputs
    (X : GaloisConstituentModel T R ap B chiType) (htyp : IsTypeChar T chiType)
    (hX : X.Unbudgeted) (hsat : X.Saturated) (hI : X.Inputs) :
    (X.toConstituentModelRel htyp hX hsat).Inputs := by
  have key : ∀ (U : Finset ℕ) (g : GalQ), (X.toConstituentModelRel htyp hX hsat).readM U
      ((X.toConstituentModelRel htyp hX hsat).tM g ((X.toConstituentModelRel htyp hX hsat).FM U)) =
        X.read U (X.redE (X.tΛ g (X.F U))) := by
    intro U g
    rfl
  obtain ⟨h1, h2⟩ := hI
  refine ⟨fun U q hU hq hqU hc => by
    have h := h1 U q hU hq hqU hc
    rw [← key] at h
    exact h, fun U p hp hU hc (g : GalQ) => ?_⟩
  obtain ⟨τ, φ, κ0, hκ, a1, a2, a3, a4, a5, hO⟩ := h2 U p hp hU hc g
  refine ⟨τ, φ, κ0, hκ, a1, a2, a3, a4, a5, ?_⟩
  rw [← key, ← key, ← key, ← key] at hO
  exact hO

/-- **Lane RC0's `ConstituentModelRel` is inhabited by a genuine Galois representation**
(PROVED): one constituent, the `2`-adic Tate representation of an elliptic curve `E/ℚ`, over the
genuine type data `typeData m` and the genuine group `G_ℚ`, for the zero reading, with its inputs.
The zero forms satisfy the unbudgeted fields, and the rank-one lattice over `ℤ₂` is saturated. -/
theorem tateConstituentModelRel (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m]
    (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ) :
    ∃ X : ConstituentModelRel (typeData m hm h4) (fun _ => 0) ap B, X.Inputs :=
  ⟨(tateConstituentModel' E m hm h4 ap B).toConstituentModelRel (isTypeChar_typeData m hm h4)
      (tateConstituentModel'_unbudgeted E m hm h4 ap B)
      (tateConstituentModel'_saturated E m hm h4 ap B),
    (tateConstituentModel' E m hm h4 ap B).toConstituentModelRel_inputs _ _ _
      (tateConstituentModel'_inputs E m hm h4 ap B)⟩

/-- **Lane RC0's `TraceModelRel` is inhabited by the trace model of a genuine Galois
representation** (its module the auxiliary quotient `Mst`, its readings on reduced expansions;
PROVED; the faithful bridge, no saturation). -/
theorem tateTraceModelRel (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) [NeZero m]
    (hm : 0 < m) (h4 : 4 ∣ m) (ap : ℕ → ℤ) (B : ℕ) :
    Nonempty (TraceModelRel (typeData m hm h4) (fun _ => 0) ap B) :=
  ⟨(tateConstituentModel' E m hm h4 ap B).toTraceModelRel (isTypeChar_typeData m hm h4)
    (tateConstituentModel'_unbudgeted E m hm h4 ap B) (tateConstituentModel'_inputs E m hm h4 ap B)⟩

end ZInQ.Manuscript.RC.AddressGenuine
