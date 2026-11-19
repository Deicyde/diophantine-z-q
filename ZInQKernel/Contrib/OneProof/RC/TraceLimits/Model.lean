import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Determinant
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Open
import ZInQKernel.Contrib.OneProof.RC.TraceLimits.AbsoluteInertia

/-!
# Building the constituent model with its lattice comparison

Tex 9638–9750. This constructor keeps the lattice fixed.

Lane RC24, round 3: adapted to the constituent model on coefficientwise reduced expansions
(tex 9639–9646, 9716–9717, 9728–9729). Its `det_orbit` is now the coefficientwise identity, so
`detOrbit_coefficient` discharges it directly and the lattice comparison `DetectsDetOrbit` is no
longer used by the constructor.

Lane RC24, round 4: the constituent model no longer has congruence fields. The text proves the
integrality of the diamond translates with correction coefficients (tex 9655–9660), evaluates
its identities in `Λ` and then reduces (tex 9898–9900); it does not assert that the diamond
operators preserve coefficientwise congruences on `Λ`. The round-3 lemma `congruence_of_hecke`
and its hypothesis `hdiam`, which assumed such a preservation, are removed. The constructor now
needs only the coefficientwise identities.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

open AddressGenuine
open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)}
variable {m : Ideal O} {C : Type} {expand : Λ →ₗ[O] (C → O)}
variable {hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ}

/-- For good sets, openness and constituent unramifiedness reduce the radical
support condition to the odd-divisor inertia comparison (tex 9748–9750). -/
theorem consN_supported_of_ramification {chiType : GalQ →* Multiplicative L}
    {F : Finset ℕ → Λ} {S U : Finset ℕ}
    (hU : ∀ p ∈ U, T.Good p) (htyp : IsTypeChar T chiType)
    (hunr : UnramifiedConstituents T avoid ρ)
    (hopen : IsOpen (consN chiType (redTrace m expand ρ hst F) U : Set GalQ))
    (hS : T.m.primeFactors ∪ avoid ⊆ S) (h2 : 2 ∈ S)
    (hram : OddRadicalRamification) :
    SupportedQuadraticCharacters (consN chiType (redTrace m expand ρ hst F) U) (S ∪ U) := by
  refine supportedQuadratic_of_inertia _ _ hopen (Finset.mem_union_left _ h2) ?_ hram
  intro q hq hqa Q hQ hqQ
  have qS : q ∉ S := fun e => hqa (Finset.mem_union_left _ e)
  have qU : q ∉ U := fun e => hqa (Finset.mem_union_right _ e)
  have hgood : T.Good q := ⟨hq, (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd =>
    qS (hS (Finset.mem_union_left _ (Nat.mem_primeFactors.2 ⟨hq, hd, T.m_pos.ne'⟩)))⟩
  exact inertia_le_consN T htyp hunr hU hgood qU
    (fun e => qS (hS (Finset.mem_union_right _ e))) hQ hqQ

/-- The stationary type and the added bits detect the elementary quotient of
the constituent subgroup for every good set (tex 9745–9750). -/
theorem consN_kummer_at_good {chiType : GalQ →* Multiplicative L}
    {F : Finset ℕ → Λ} {S U : Finset ℕ}
    (hU : ∀ p ∈ U, T.Good p) (htyp : IsTypeChar T chiType)
    (hunr : UnramifiedConstituents T avoid ρ)
    (hopen : IsOpen (consN chiType (redTrace m expand ρ hst F) U : Set GalQ))
    (hS : T.m.primeFactors ∪ avoid ⊆ S) (h2 : 2 ∈ S)
    (hfixed : TypeDetectsRadicals chiType S) (g : GalQ)
    (hg : chiType g = 1) (hbits : ∀ p ∈ U, bitChar p g = 1) :
    g ∈ Subgroup.closure (sqSet GalQ) ⊔ consN chiType (redTrace m expand ρ hst F) U :=
  kummer_of_support hfixed
    (consN_supported_of_ramification hU htyp hunr hopen hS h2 oddRadicalRamification) g hg hbits

/-- Extending the forms by zero on sets of nongood indices extends the Kummer
conclusion from good sets to all finite sets, as required by the constituent
interface (proved here). -/
theorem consN_kummer_of_good {chiType : GalQ →* Multiplicative L} (F : Finset ℕ → Λ)
    (hzero : ∀ W, ¬ (∀ p ∈ W, T.Good p) → F W = 0)
    (hk : ∀ W, (∀ p ∈ W, T.Good p) → ∀ g, chiType g = 1 →
      (∀ p ∈ W, bitChar p g = 1) → g ∈ Subgroup.closure (sqSet GalQ) ⊔ consN chiType (redTrace m expand ρ hst F) W)
    (U : Finset ℕ) (g : GalQ) (hg : chiType g = 1) (hbit : ∀ p ∈ U, bitChar p g = 1) :
    g ∈ Subgroup.closure (sqSet GalQ) ⊔ consN chiType (redTrace m expand ρ hst F) U := by
  classical
  let V := U.filter T.Good
  let S := Subgroup.closure (sqSet GalQ)
  have hs (x : GalQ) : x ^ 2 ∈ S := Subgroup.subset_closure ⟨x, rfl⟩
  have : S.Normal := normal_of_all_squares S hs
  have hV : ∀ p ∈ V, T.Good p := fun p hp => (Finset.mem_filter.1 hp).2
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.1
    (hk V hV g hg (fun p hp => hbit p (Finset.mem_filter.1 hp).1) :
      g ∈ S ⊔ consN chiType (redTrace m expand ρ hst F) V)
  have ha' (p : ℕ) : bitChar p a = 1 := by
    have h : S ≤ (bitChar p).ker := (Subgroup.closure_le _).2 (by
      rintro _ ⟨x, rfl⟩
      change bitChar p (x ^ 2) = 1
      rw [map_pow, pow_two]
      exact (show ∀ z : Multiplicative (ZMod 2), z * z = 1 by decide) _)
    exact MonoidHom.mem_ker.1 (h ha)
  have hbn : b ∈ consN chiType (redTrace m expand ρ hst F) U := by
    refine ⟨hb.1, ?_, fun σ W hW => ?_⟩
    · intro p hp
      simpa only [map_mul, ha' p, one_mul] using hbit p hp
    · by_cases hw : ∀ p ∈ W, T.Good p
      · exact hb.2.2 σ W (fun p hp => Finset.mem_filter.2 ⟨hW hp, hw p hp⟩)
      · simp only [redTrace, hzero W hw, map_zero]
  exact Subgroup.mul_mem_sup ha hbn

/-- The comparison missing at tex 9725–9729, restricted to the discrepancy
vectors used there. There is no saturation hypothesis on the whole lattice. Lane RC24, round 3:
the reduced-expansion model does not use it; it is the form of saturation that lane RC0's
`ConstituentModelRel` (on `Λ/𝔪Λ`) would need. -/
def DetectsDetOrbit (F : Finset ℕ → Λ)
    {ops : GoodOperators T avoid frob ρ Λ}
    (D : ∀ U, DeterminantFourierData ops m (F U)) : Prop :=
  ∀ U u v (x : Λ), (x : I → K) =
      dV ρ u (tV ρ v (F U)) - tV ρ v (F U) →
    (∀ n : ℕ, n ≠ 0 → (D U).coeff n x ∈ m) →
      (x : I → K) ∈ (m • ⊤ : Submodule O Λ).map Λ.subtype

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
variable [TopologicalSpace O] [CompactSpace O] [IsNoetherianRing O]
variable [ContinuousSMul O K] [Finite (O ⧸ m)]

/-- A constituent model from good-prime operators, continuous representations,
the Fourier determinant calculation, and coverage of the stationary support by the type. The
existing `Inputs` can be supplied directly to `GaloisConstituentModel.toGaloisTraceModel`.

Lane RC24, round 3: the model is on coefficientwise reduced expansions at the positive Fourier
indices `C = {n // n ≠ 0}`, with expansion `expand v n = coeff n v` (the Fourier coefficients of
`D U` are this family for every `U`, `hD`). Its `det_orbit` is `detOrbit_coefficient`, with no
lattice comparison. Round 4: no congruence hypothesis on the operators. `two_fresh` is the
reduced-expansion statement of tex 9741–9745 within the budget, and `read` is a functional on
reduced expansions.

This constructor is not a discharge for the genuine added-prime packets.
`htyp`, `hS` and `hlevel` force `avoid` to contain no good prime; together
with `hunr` they make every constituent unramified at every good added prime.
Thus it cannot carry the ramified blocks of tex 9754–9758 and 9866–9873.
Tex 9649–9668 also supplies finiteness only at each fixed packet. A genuine
family discharge must assemble separate packets with per-U openness and
inertia support S ∪ U; it is not constructed here. -/
def buildConstituentModel (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
    (chiType : GalQ →* Multiplicative L) (hchi : OpenTypeKernel chiType)
    (htyp : IsTypeChar T chiType)
    (hm2 : (2 : O) ∈ m) (hm : IsClosed (m : Set O)) (hΛ : Λ.FG)
    (F : Finset ℕ → Λ)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hcont : ContinuousOperators ρ Λ) (hunr : UnramifiedConstituents T avoid ρ)
    (ops : GoodOperators T avoid frob ρ Λ)
    (coeff : ℕ → Λ →ₗ[O] O)
    (coefK : (I → K) →ₗ[K] ({n : ℕ // n ≠ 0} → K))
    (hspec : ∀ (v : Λ) (n : {n : ℕ // n ≠ 0}), algebraMap O K (coeff n v) = coefK v n)
    (D : ∀ U, DeterminantFourierData ops m (F U)) (hD : ∀ U, (D U).coeff = coeff)
    (hcoeff : ∀ n, Continuous (coeff n))
    (read : Finset ℕ → ({n : ℕ // n ≠ 0} → O ⧸ m) →+ ZMod 2)
    (h2fresh : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
      ∀ n : ℕ, n ≠ 0 → coeff n ⟨tV ρ g (tV ρ h (F U)),
        (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1 g _
          ((stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1 h _ (F U).2)⟩ ∈ m)
    (S : Finset ℕ) (hS : TypeDetectsRadicals chiType S)
    (hlevel : T.m.primeFactors ∪ avoid ⊆ S) (hS2 : 2 ∈ S)
    (hzero : ∀ W, ¬ (∀ p ∈ W, T.Good p) → F W = 0) :
    GaloisConstituentModel T R ap B chiType := by
  have hs := stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops
  let expand : Λ →ₗ[O] ({n : ℕ // n ≠ 0} → O) := LinearMap.pi fun n => coeff n
  have hred : ∀ x : Λ, redExpOf m expand x = 0 ↔ ∀ n : ℕ, n ≠ 0 → coeff n x ∈ m := by
    intro x
    constructor
    · intro h n hn
      have := congrFun h ⟨n, hn⟩
      rw [redExpOf_apply] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro h
      funext n
      rw [redExpOf_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h n.1 n.2)
  have ho U := consN_isOpen (F := F) (expand := expand) hchi (residual_isOpen Λ hΛ m) hs.1 hcont U
  exact {
    I := I
    K := K
    O := O
    m := m
    two_mem := hm2
    ρ := ρ
    Λ := Λ
    stable_t := hs.1
    stable_d := hs.2
    C := {n : ℕ // n ≠ 0}
    coefK := coefK
    expand := expand
    expand_spec := hspec
    F := F
    read := read
    frob := frob
    frob_spec := hfrob
    det_orbit := fun U _ _ u v => by
      rw [← sub_eq_zero, ← map_sub]
      refine (hred _).mpr fun n hn => ?_
      have h := detOrbit_coefficient hfrob hcont hunr ops hs.1 hs.2 (F U) (D U) hm
        n hn (by rw [hD U]; exact hcoeff n) u v
      rw [hD U] at h
      exact h
    two_fresh := fun U hU hUB g h => (hred _).mpr (h2fresh U hU hUB g h)
    kummer := fun U _ _ => consN_kummer_of_good F hzero (fun U hU =>
      consN_kummer_at_good hU htyp hunr (ho U) hlevel hS2 hS) U
    finiteIndex := fun U _ _ => consN_finiteIndex U (ho U)
    chebotarev := fun U hU _ => consN_chebotarev T htyp hfrob hunr U hU (ho U) }


end ZInQ.Manuscript.RC.TraceLimits
