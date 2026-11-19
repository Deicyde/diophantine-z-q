import ZInQKernel.Contrib.OneProof.RC.SieveAvoid.Hecke
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Model
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Reading

/-! Separate the fixed Kummer support from the ambient good-Hecke domain.
Only the forms indexed by subsets of the current set need have unramified
trace orbits outside that set (tex 9745–9750). -/

noncomputable section

namespace ZInQ.Manuscript.RC.SieveAvoid

open AddressGenuine PrintsArith TraceLimits O12 O12Theta
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {T : TypeData L ε}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable {avoid : Finset ℕ} {frob : ℕ → GalQ} {ρ : I → GalQ →* GL (Fin 2) K}
variable {Λ : Submodule O (I → K)} {m : Ideal O}
variable {chiType : GalQ →* Multiplicative L}
variable {C : Type} {expand : Λ →ₗ[O] (C → O)} {F : Finset ℕ → Λ}
variable {hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ}

/-- A local test on the part of the actual coefficient support not recorded
by the retained type or an active bit. Inertia may act on individual
constituents there; the elementary quotient only sees its image modulo
squares and the reduced trace stabilizer. -/
def SieveInertia {Y : Type*} (χ : GalQ →* Multiplicative L)
    (rt : GalQ → Finset ℕ → Y) (support Scoeff U : Finset ℕ) : Prop :=
  ∀ q, T.Good q → q ∈ Scoeff → q ∉ support ∪ U →
    ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
    ∀ σ ∈ Q.inertia GalQ, σ ∈ Subgroup.closure (sqSet GalQ) ⊔ consN χ rt U

/-- Away from the coefficient support and the active primes, formwise
inertia controls the reduced trace. The extra local test shrinks the
ramification bound for the elementary quotient to the retained support.
The comparison with the coarser type is on-the-spot (c). -/
theorem formwise_kummer {Y : Type*} {rt : GalQ → Finset ℕ → Y}
    {support Scoeff U : Finset ℕ}
    (htyp : IsTypeChar T chiType) (hU : ∀ p ∈ U, T.Good p)
    (hlevel : T.m.primeFactors ⊆ support) (h2 : 2 ∈ support)
    (hs : TypeDetectsRadicals chiType support)
    (ho : IsOpen (consN chiType rt U : Set GalQ))
    (htrace : ∀ q, T.Good q → q ∉ Scoeff ∪ U →
      ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
      ∀ σ ∈ Q.inertia GalQ, ∀ g : GalQ, ∀ V ⊆ U, rt (g * σ) V = rt g V)
    (hsieve : SieveInertia (T := T) chiType rt support Scoeff U)
    (g : GalQ) (hg : chiType g = 1) (hbits : ∀ p ∈ U, bitChar p g = 1) :
    g ∈ Subgroup.closure (sqSet GalQ) ⊔ consN chiType rt U := by
  apply kummer_of_support hs _ g hg hbits
  intro ψ hN
  have hSq : Subgroup.closure (sqSet GalQ) ≤ ψ.ker := by
    apply (Subgroup.closure_le _).2
    rintro _ ⟨x, rfl⟩
    change ψ (x ^ 2) = 1
    rw [map_pow]
    exact (show ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 by decide) _
  refine supportedQuadratic_of_inertia _ _ (Subgroup.isOpen_mono le_sup_right ho)
    (Finset.mem_union_left _ h2) ?_ oddRadicalRamification ψ (sup_le hSq hN)
  intro q hq hqa Q hQ hqQ σ hσ
  have hqs : q ∉ support := fun e => hqa (Finset.mem_union_left _ e)
  have hqU : q ∉ U := fun e => hqa (Finset.mem_union_right _ e)
  have hgood : T.Good q := ⟨hq, (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd =>
    hqs (hlevel (Nat.mem_primeFactors.2 ⟨hq, hd, T.m_pos.ne'⟩))⟩
  by_cases hsc : q ∈ Scoeff
  · exact hsieve q hgood hsc hqa Q hQ hqQ σ hσ
  · obtain ⟨hc, hb⟩ := chars_eq_one_of_mem_inertia T htyp hU hgood hqU hQ hqQ hσ
    apply le_sup_right (a := Subgroup.closure (sqSet GalQ))
    exact ⟨hc, hb, htrace q hgood (by simpa only [Finset.mem_union, not_or] using And.intro hsc hqU)
      Q hQ hqQ σ hσ⟩

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
variable [TopologicalSpace O] [CompactSpace O] [IsNoetherianRing O]
variable [ContinuousSMul O K] [Finite (O ⧸ m)]

/-- The positive coefficient expansion, the actual coefficient-one reading,
and the split support condition. The remaining trace input is the existing
coefficientwise two-fresh identity. -/
def buildWithRestrictedInertia (R : Finset ℕ → ZMod 2) (ap : ℕ → ℤ) (B : ℕ)
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
    (support Scoeff : Finset ℕ) (hs : TypeDetectsRadicals chiType support)
    (hlevel : T.m.primeFactors ⊆ support) (hs2 : 2 ∈ support)
    (htrace : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
      ∀ (q : ℕ), T.Good q → q ∉ Scoeff ∪ U →
      ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
      ∀ σ ∈ Q.inertia GalQ, ∀ W ⊆ U, ∀ g, tV ρ (g * σ) (F W) = tV ρ g (F W))
    (hsieve : let st := (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1
      let expand : Λ →ₗ[O] (PosIndex → O) := LinearMap.pi fun n => coeff n
      ∀ U, (∀ p ∈ U, T.Good p) → U.card + 1 ≤ B →
        SieveInertia (T := T) chiType (redTrace m expand ρ st F) support Scoeff U) :
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
    kummer := fun U hu hb => formwise_kummer htyp hu hlevel hs2 hs (ho U)
      (fun q hq hf Q hQ hqQ σ hσ g V hV => by
        unfold redTrace
        congr 1
        exact Subtype.ext (htrace U hu hb q hq hf Q hQ hqQ σ hσ V hV g))
      (hsieve U hu hb)
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


#print axioms formwise_kummer
#print axioms buildWithRestrictedInertia

end ZInQ.Manuscript.RC.SieveAvoid
