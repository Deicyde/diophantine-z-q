import ZInQKernel.Contrib.OneProof.RC.O12.Local
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Determinant

/-! The integral Fourier comparison and the reduction of (O.12), tex 9638–9668,
9688–9694, 9844–9856 and 9891–9902. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12

open AddressGenuine PrintsArith TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
variable {chiType : GalQ →* Multiplicative L}
variable (X : GaloisConstituentModel T R ap B chiType)

attribute [local instance] GaloisConstituentModel.modMexp

abbrev PosIndex := {n : ℕ // n ≠ 0}

/-- The positive Fourier coordinates and coefficient-one reading of the model.
The rings and linear coefficient family are those of `buildConstituentModel`.
The function to `𝔽₂` reads the prime subfield identically; its other values
play no role on the final readings. -/
structure FourierData where
  index : PosIndex → X.C
  coeff : ℕ → X.Λ →ₗ[X.O] X.O
  expand_coeff : ∀ (v : X.Λ) (n : PosIndex), X.expand v (index n) = coeff n v
  integral_inclusion : Function.Injective (algebraMap X.O X.K)
  decode : (X.O ⧸ X.m) →+ ZMod 2
  decode_one : decode 1 = 1
  read_at_one : ∀ U (v : X.Λ), X.read U (X.redE v) =
    decode (Ideal.Quotient.mk X.m (coeff 1 v))

namespace FourierData

variable {X} (A : FourierData X)

/-- The good Hecke formula where it is used: on `F_U` at a good prime outside
`U` and the fixed level. The fixed and moving exclusions are in the good
condition for the actual stage. These are the same operator and formula types
as in `DeterminantFourierData`. The operators need only agree with the trace
on the tested form, since the shared ambient space includes other levels. -/
def FormwiseHecke : Prop :=
  ∀ (U : Finset ℕ) (q : ℕ), (∀ s ∈ U, T.Good s) → T.Good q → q ∉ U →
    U.card + 1 ≤ B → ∃ diamondF : X.Λ, ∀ n,
      A.coeff n (X.tΛ (X.frob q) (X.F U)) =
        A.coeff (q * n) (X.F U) + if q ∣ n then (q : X.O) * A.coeff (n / q) diamondF else 0

/-- Reuse the constructor's supplied Hecke formula and trace comparison at any
prime in the domain of those data (tex 9660–9668). -/
theorem goodHecke_of_data {avoid : Finset ℕ}
    (ops : GoodOperators T avoid X.frob X.ρ X.Λ) (U : Finset ℕ)
    (D : DeterminantFourierData ops X.m (X.F U)) (hD : D.coeff = A.coeff)
    {q : ℕ} (hq : T.Good q) (hqa : q ∉ avoid) :
    ∃ diamondF : X.Λ, ∀ n,
      A.coeff n (X.tΛ (X.frob q) (X.F U)) =
        A.coeff (q * n) (X.F U) + if q ∣ n then (q : X.O) * A.coeff (n / q) diamondF else 0 := by
  refine ⟨ops.diamond q (X.F U), fun n => ?_⟩
  have hh : HeckeFourier A.coeff (ops.hecke q) (ops.diamond q) q := hD ▸ D.hecke_eq q hq hqa
  have ht : X.tΛ (X.frob q) (X.F U) = ops.hecke q (X.F U) :=
    Subtype.ext (ops.trace_eq q hq hqa (X.F U))
  rw [ht, hh]

/-- If `q ∤ n`, the good Hecke formula has no diamond term (tex 9688,
9905–9921). -/
theorem trace_coeff_of_not_dvd (H : A.FormwiseHecke) {U : Finset ℕ} {q n : ℕ}
    (hU : ∀ s ∈ U, T.Good s) (hq : T.Good q) (hqU : q ∉ U) (hB : U.card + 1 ≤ B)
    (hn : ¬ q ∣ n) :
    A.coeff n (X.tΛ (X.frob q) (X.F U)) = A.coeff (q * n) (X.F U) := by
  obtain ⟨diamondF, h⟩ := H U q hU hq hqU hB
  rw [h, ite_eq_right hn, add_zero]

/-- The reduced coefficient of the trace orbit. -/
def orbitCoeff (U : Finset ℕ) (g : GalQ) (n : PosIndex) : X.O ⧸ X.m :=
  (X.tE g (X.FE U)).val (A.index n)

/-- The positive coefficient of the reduced trace orbit is the residue of
the corresponding integral coefficient (tex 9638–9646). -/
theorem orbitCoeff_eq (U : Finset ℕ) (g : GalQ) (n : PosIndex) :
    A.orbitCoeff U g n = Ideal.Quotient.mk X.m (A.coeff n (X.tΛ g (X.F U))) := by
  unfold orbitCoeff GaloisConstituentModel.FE
  rw [X.tE_redM, X.redM_coe, redExpOf_apply, A.expand_coeff]

/-- Apply the manuscript's coefficient-one reading to the reduced orbit. -/
theorem read_orbit (U : Finset ℕ) (g : GalQ) :
    X.readE U (X.tE g (X.FE U)) = A.decode (A.orbitCoeff U g ⟨1, one_ne_zero⟩) := by
  rw [A.orbitCoeff_eq, GaloisConstituentModel.FE, X.tE_redM, X.readE_redM]
  exact A.read_at_one U _

/-- The Fourier comparison needed for the actual `U_p^{(2)}`. The matrix
and finite-sum part is `whittaker_sum`; the identification of the finite
Whittaker coefficient with the Fourier coefficient divided by the index is
part of the theta data here (tex 9841–9856). -/
def UpAtOne {U : Finset ℕ} {p : ℕ} {P : LocalPair p} (D : LocalBlocks X U P)
    (hp : p ≠ 0) : Prop :=
  ∀ v : X.I → X.K, (∀ i, i ∉ D.active → v i = 0) →
    X.coefK (D.Up v) (A.index ⟨1, one_ne_zero⟩) = X.coefK v (A.index ⟨p, hp⟩)

/-- The (p)-th coefficient of the integral trace difference equals the
first coefficient of the integral determinant applied to the other
difference. Integrality uses the two lattice stability fields; no
integral eigenspace projectors are needed (tex 9891–9902). -/
theorem o12_integral {U : Finset ℕ} {p : ℕ} {P : LocalPair p}
    (D : LocalBlocks X U P) (hp : p ≠ 0) (hUp : A.UpAtOne D hp) (g : GalQ) :
    A.coeff p (X.tΛ (g * P.τ * P.φ) (X.F U) - X.tΛ (g * P.φ) (X.F U)) =
    A.coeff 1 (X.dΛ P.φ (X.tΛ (g * P.τ) (X.F U) - X.tΛ g (X.F U))) := by
  let v : X.Λ := X.tΛ (g * P.τ * P.φ) (X.F U) - X.tΛ (g * P.φ) (X.F U)
  let w : X.Λ := X.dΛ P.φ (X.tΛ (g * P.τ) (X.F U) - X.tΛ g (X.F U))
  change A.coeff p v = A.coeff 1 w
  apply A.integral_inclusion
  have spec (x : X.Λ) (n : PosIndex) :
      algebraMap X.O X.K (A.coeff n x) = X.coefK x (A.index n) := by
    rw [← A.expand_coeff x n, X.expand_spec]
  rw [spec v ⟨p, hp⟩, spec w ⟨1, one_ne_zero⟩]
  change X.coefK (upDifference X U P.τ P.φ g) _ =
    X.coefK (dV X.ρ P.φ (tV X.ρ (g * P.τ) (X.F U) - tV X.ρ g (X.F U))) _
  rw [← o12_charZero X D g]
  exact (hUp _ (fun i hi => upDifference_supported X D g i (fun h => hi h.1))).symm

/-- Reduced (O.12), evaluated at one and (p) (tex 9891–9905).
The determinant disappears by the existing reduced orbit identity. -/
theorem o12_reduced {U : Finset ℕ} {p : ℕ} {P : LocalPair p}
    (D : LocalBlocks X U P) (hp : p ≠ 0) (hUp : A.UpAtOne D hp)
    (hU : ∀ s ∈ U, T.Good s) (hB : U.card + 1 ≤ B) (g : GalQ) :
    A.orbitCoeff U (g * P.τ * P.φ) ⟨p, hp⟩ - A.orbitCoeff U (g * P.φ) ⟨p, hp⟩ =
    A.orbitCoeff U (g * P.τ) ⟨1, one_ne_zero⟩ - A.orbitCoeff U g ⟨1, one_ne_zero⟩ := by
  have det (h : GalQ) :
      Ideal.Quotient.mk X.m (A.coeff 1 (X.dΛ P.φ (X.tΛ h (X.F U)))) =
      Ideal.Quotient.mk X.m (A.coeff 1 (X.tΛ h (X.F U))) := by
    have e := congrFun (X.det_orbit U hU hB P.φ h) (A.index ⟨1, one_ne_zero⟩)
    simpa only [redExpOf_apply, A.expand_coeff] using e
  have e := congrArg (Ideal.Quotient.mk X.m) (A.o12_integral D hp hUp g)
  simpa only [orbitCoeff_eq, map_sub, det] using e

#print axioms goodHecke_of_data
#print axioms trace_coeff_of_not_dvd
#print axioms orbitCoeff_eq
#print axioms read_orbit
#print axioms o12_integral
#print axioms o12_reduced

end FourierData

end ZInQ.Manuscript.RC.O12
