import ZInQKernel.Contrib.OneProof.RC.O12.Build
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Reading

/-! Separate the fixed Kummer support from the ambient good-Hecke domain.
Only the forms indexed by subsets of the current set need have unramified
trace orbits outside that set (tex 9745–9750). -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Theta

open AddressGenuine PrintsArith TraceLimits O12
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable {avoid : Finset ℕ} {frob : ℕ → GalQ} {ρ : I → GalQ →* GL (Fin 2) K}
variable {Λ : Submodule O (I → K)} {m : Ideal O}
variable {chiType : GalQ →* Multiplicative L}
variable {C : Type} {expand : Λ →ₗ[O] (C → O)} {F : Finset ℕ → Λ}
variable {hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ}

/-- The supported radical comparison uses inertia on the forms in the
current orbit, even at a prime excluded from the ambient Hecke tests. -/
theorem formwise_kummer {support U : Finset ℕ}
    (htyp : IsTypeChar T chiType) (hU : ∀ p ∈ U, T.Good p)
    (hlevel : T.m.primeFactors ⊆ support) (h2 : 2 ∈ support)
    (hs : TypeDetectsRadicals chiType support)
    (ho : IsOpen (consN chiType (redTrace m expand ρ hst F) U : Set GalQ))
    (htrace : ∀ (q : ℕ), T.Good q → q ∉ support → q ∉ U →
      ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
      ∀ σ ∈ Q.inertia GalQ, ∀ W ⊆ U, ∀ g, tV ρ (g * σ) (F W) = tV ρ g (F W))
    (g : GalQ) (hg : chiType g = 1) (hbits : ∀ p ∈ U, bitChar p g = 1) :
    g ∈ Subgroup.closure (sqSet GalQ) ⊔ consN chiType (redTrace m expand ρ hst F) U := by
  apply kummer_of_support hs _ g hg hbits
  refine supportedQuadratic_of_inertia _ _ ho (Finset.mem_union_left _ h2) ?_ oddRadicalRamification
  intro q hq hqa Q hQ hqQ σ hσ
  have hqs : q ∉ support := fun e => hqa (Finset.mem_union_left _ e)
  have hqU : q ∉ U := fun e => hqa (Finset.mem_union_right _ e)
  have hgood : T.Good q := ⟨hq, (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd =>
    hqs (hlevel (Nat.mem_primeFactors.2 ⟨hq, hd, T.m_pos.ne'⟩))⟩
  obtain ⟨hc, hb⟩ := chars_eq_one_of_mem_inertia T htyp hU hgood hqU hQ hqQ hσ
  refine ⟨hc, hb, fun g W hW => ?_⟩
  unfold redTrace
  congr 1
  exact Subtype.ext (htrace q hgood hqs hqU Q hQ hqQ σ hσ W hW g)

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
variable [TopologicalSpace O] [CompactSpace O] [IsNoetherianRing O]
variable [ContinuousSMul O K] [Finite (O ⧸ m)]

/-- The positive coefficient expansion, the actual coefficient-one reading,
and the split support condition. The remaining trace input is the existing
coefficientwise two-fresh identity. -/
def buildWithFormwiseInertia (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
    (hchi : OpenTypeKernel chiType) (htyp : IsTypeChar T chiType)
    (hm : m.IsMaximal) (hm2 : (2 : O) ∈ m) (hclosed : IsClosed (m : Set O))
    (hinj : Function.Injective (algebraMap O K))
    (hΛ : Λ.FG) (F : Finset ℕ → Λ)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hcont : ContinuousOperators ρ Λ) (hunr : UnramifiedConstituents T avoid ρ)
    (ops : GoodOperators T avoid frob ρ Λ)
    (coeff : ℕ → Λ →ₗ[O] O) (coefK : (I → K) →ₗ[K] (PosIndex → K))
    (hspec : ∀ (v : Λ) (n : PosIndex), algebraMap O K (coeff n v) = coefK v n)
    (D : ∀ U, DeterminantFourierData ops m (F U)) (hD : ∀ U, (D U).coeff = coeff)
    (hcoeff : ∀ n, Continuous (coeff n))
    (h2fresh : let st := (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1
      ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
        ∀ n : ℕ, n ≠ 0 → coeff n (latT ρ Λ st g (latT ρ Λ st h (F U))) ∈ m)
    (support : Finset ℕ) (hs : TypeDetectsRadicals chiType support)
    (hlevel : T.m.primeFactors ⊆ support) (hs2 : 2 ∈ support)
    (htrace : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
      ∀ (q : ℕ), T.Good q → q ∉ support → q ∉ U →
      ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
      ∀ σ ∈ Q.inertia GalQ, ∀ W ⊆ U, ∀ g, tV ρ (g * σ) (F W) = tV ρ g (F W)) :
    Σ X : GaloisConstituentModel T R ap B chiType, FourierData X := by
  let st := stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops
  let expand : Λ →ₗ[O] (PosIndex → O) := LinearMap.pi fun n => coeff n
  have hred (x : Λ) (hx : ∀ n : ℕ, n ≠ 0 → coeff n x ∈ m) :
      redExpOf m expand x = 0 := by
    funext n
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hx n n.2)
  have ho U := consN_isOpen (F := F) (expand := expand) hchi
    (residual_isOpen Λ hΛ m) st.1 hcont U
  let X : GaloisConstituentModel T R ap B chiType := {
    I := I
    K := K
    O := O
    m := m
    two_mem := hm2
    ρ := ρ
    Λ := Λ
    stable_t := st.1
    stable_d := st.2
    C := PosIndex
    coefK := coefK
    expand := expand
    expand_spec := hspec
    F := F
    read := fun _ => readOne m hm hm2
    frob := frob
    frob_spec := hfrob
    det_orbit := fun U _ _ u v => by
      rw [← sub_eq_zero, ← map_sub]
      refine hred _ fun n hn => ?_
      have h := detOrbit_coefficient hfrob hcont hunr ops st.1 st.2 (F U) (D U) hclosed
        n hn (by rw [hD U]; exact hcoeff n) u v
      rwa [hD U] at h
    two_fresh := fun U hu hb g h => hred _ (h2fresh U hu hb g h)
    kummer := fun U hu hb => formwise_kummer htyp hu hlevel hs2 hs (ho U) (htrace U hu hb)
    finiteIndex := fun U _ _ => consN_finiteIndex U (ho U)
    chebotarev := fun U hu _ => consN_chebotarev T htyp hfrob hunr U hu (ho U) }
  exact ⟨X, {
    index := id
    coeff := coeff
    expand_coeff := fun _ _ => rfl
    integral_inclusion := hinj
    decode := decode m hm hm2
    decode_one := decode_one m hm hm2
    read_at_one := fun _ _ => rfl }⟩


end ZInQ.Manuscript.RC.O12Theta
