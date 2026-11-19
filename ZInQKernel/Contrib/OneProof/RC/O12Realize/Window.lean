import ZInQKernel.Contrib.OneProof.RC.O12Realize.Stage
import ZInQKernel.Contrib.OneProof.RC.O12Theta.Window

/-! Use one copy of the finite block realization for each fixed root.
The two operator hypotheses are needed only on actual window seeds;
the zero extension makes the existing constructor applicable outside
the window without supplying any extra Fourier readings there. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Realize

open AddressGenuine PrintsArith TraceLimits ThetaCoeff O12 O12Theta Finset
open ZInQ.Manuscript.RC.Odd
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {I K O G L : Type} [Fintype I] [Field K] [CharZero K]
  [CommRing O] [IsDomain O] [CharZero O] [Algebra O K] [Group G] [AddCommGroup L]
variable {ε : L →+ ZMod 2} {T : TypeData L ε} {χ : GalQ →* Multiplicative L}
variable {avoid : Finset ℕ} {frob : ℕ → GalQ} {m : Ideal O} {B : ℕ}
variable {M W R : ℕ} {δ : ℤ} {adm : ℕ → Prop} {S : AppF.ThetaStage (StageRing O M)}
variable {P : Window T.Good S W} {A : Basis I K G (Test T avoid)}
variable {E : Lift S} {D : Divisions E δ W R adm} {C : DiamondCharacters O G E.η}
/-- The root itself is a sufficient pool for a fixed-set application. -/
def poolOfTest (U : Finset ℕ) (hU : ∀ p ∈ U, T.Good p)
    (hstage : ∀ p ∈ U, S.Good p) (hB : U.card + 1 ≤ B) (hbudget : B ≤ W + 1) :
    ThetaCoeff.Window T.Good S W :=
  ⟨U, by omega, hU, hstage⟩

variable (V : Blocks (P := P) A E D C)
variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
  [TopologicalSpace O] [CompactSpace O] [IsNoetherianRing O] [ContinuousSMul O K] [Finite (O ⧸ m)]
variable (ρ₀ : Attachment A frob) (hinj : Function.Injective (algebraMap O K))

/-- The constructor's coefficientwise two-fresh hypothesis, restricted to
the actual seeds (tex 9712–9717, 9741–9745). -/
def TwoFreshOn (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q) (B : ℕ) : Prop :=
  let st := (stable_operators T hfrob
      (lattice_closed _ (A.finite V.seed hinj (V.integral_seed hinj)))
      (V.hcont ρ₀) ρ₀.unramified (V.ops ρ₀)).1
  ∀ U ⊆ P.pool, U.card + 1 ≤ B → ∀ g h, ∀ n : ℕ, n ≠ 0 →
    V.coeff hinj n (latT ρ₀.ρ _ st g (latT ρ₀.ρ _ st h (V.F U))) ∈ m

/-- Formwise inertia on each actual seed, outside its own added primes and
the stationary support (tex 9745–9750). -/
def InertiaOn (support : Finset ℕ) : Prop :=
  ∀ U ⊆ P.pool, U.card + 1 ≤ B →
    ∀ q, T.Good q → q ∉ support → q ∉ U →
    ∀ Q : Ideal Zbar, Q.IsMaximal → ((q : ℤ) : Zbar) ∈ Q →
    ∀ σ ∈ Q.inertia GalQ, ∀ i, V.seed U i ≠ 0 → ρ₀.ρ i σ = 1

/-- Construct the model on the actual common lattice. No operator or
inertia statement on forms outside the pool is needed from the stage. -/
def commonSpace (R₀ : Finset ℕ → ZMod 2)
    (hχ : OpenTypeKernel χ) (htyp : IsTypeChar T χ)
    (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) (hclosed : IsClosed (m : Set O))
    (he : Topology.IsEmbedding (algebraMap O K))
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (support : Finset ℕ) (hs : TypeDetectsRadicals χ support)
    (hlevel : T.m.primeFactors ⊆ support) (hs2 : 2 ∈ support)
    (h2fresh : TwoFreshOn (m := m) V ρ₀ hinj hfrob B)
    (hseed : InertiaOn (B := B) V ρ₀ support) :
    Σ X : GaloisConstituentModel T R₀ S.ap B χ, FourierData X :=
  windowModel V hinj ρ₀ R₀ B χ hχ htyp hm h2 hclosed he hfrob
    (by
      intro st U _ hB g h n hn
      by_cases hU : U ⊆ P.pool
      · exact h2fresh U hU hB g h n hn
      · have hz : V.F U = 0 := Subtype.ext (dite_eq_right hU)
        rw [hz, map_zero, map_zero, map_zero]
        exact m.zero_mem)
    support hs hlevel hs2
    (by
      intro U _ hB q hq hqs hqU Q hQ hqQ σ hσ V' hV i hi
      have hVP : V' ⊆ P.pool := by
        by_contra hh
        exact hi (by simp [Blocks.seed, hh])
      exact hseed V' hVP ((Nat.add_le_add_right (card_le_card hV) 1).trans hB) q hq hqs
        (fun e => hqU (hV e)) Q hQ hqQ σ hσ i hi)

variable {R₀ : Finset ℕ → ZMod 2} (hχ : OpenTypeKernel χ) (htyp : IsTypeChar T χ)
variable (hm : m.IsMaximal) (h2 : (2 : O) ∈ m) (hclosed : IsClosed (m : Set O))
variable (he : Topology.IsEmbedding (algebraMap O K))
variable (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
variable (support : Finset ℕ) (hs : TypeDetectsRadicals χ support)
variable (hlevel : T.m.primeFactors ⊆ support) (hs2 : 2 ∈ support)
variable (h2fresh : TwoFreshOn (m := m) V ρ₀ hinj hfrob B)
variable (hseed : InertiaOn (B := B) V ρ₀ support)

/-- Name both parts of the constructed common space to keep the theorem
statements on its actual lattice and Fourier coordinates. -/
abbrev realizedSpace :=
  commonSpace (B := B) V ρ₀ hinj R₀ hχ htyp hm h2 hclosed he hfrob support hs hlevel hs2 h2fresh hseed

-- These are the original coefficient types; expose their instances before
-- elaborating the pointwise stage lemmas on the constructed model.
local instance :
    CharZero (realizedSpace (R₀ := R₀) V ρ₀ hinj hχ htyp hm h2 hclosed he hfrob
      support hs hlevel hs2 h2fresh hseed).1.O :=
  show CharZero O from inferInstance

local instance :
    IsDomain (realizedSpace (R₀ := R₀) V ρ₀ hinj hχ htyp hm h2 hclosed he hfrob
      support hs hlevel hs2 h2fresh hseed).1.O :=
  show IsDomain O from inferInstance

local instance :
    CharZero (realizedSpace (R₀ := R₀) V ρ₀ hinj hχ htyp hm h2 hclosed he hfrob
      support hs hlevel hs2 h2fresh hseed).1.K :=
  show CharZero K from inferInstance

omit [CharZero K] in
/-- The common space uses the actual positive Fourier coefficients of the
window, including every omitted subset. -/
theorem expansions_on_window :
    ExpansionsOn (realizedSpace (R₀ := R₀) V ρ₀ hinj hχ htyp hm h2 hclosed he hfrob support hs hlevel hs2 h2fresh hseed).2 E D P.pool := by
  intro U hU
  exact ⟨P.admissible U hU, V.coeff_F hinj U hU⟩

/-- Supply the window hypothesis of the dictionary consumer directly from
the finite blocks and the named stage and local inputs. -/
theorem readings_on_window (hB : P.pool.card + 1 ≤ B) (hbudget : B ≤ W + 1) :
    let pair := realizedSpace (R₀ := R₀) V ρ₀ hinj hχ htyp hm h2 hclosed he hfrob
      support hs hlevel hs2 h2fresh hseed
    StageValuation (X := pair.1) (S := S) (δ := δ) →
      (∀ p ∈ P.pool, ∃ k : ℕ, E.η p ^ (2 ^ k) = 1) →
      LocalOn pair.2 P.pool P.type_good → ReadingsOn pair.1 P.pool avoid := by
  intro pair valuation hphase localData
  exact readings_on_of_stage P.type_good hB hbudget
    (expansions_on_window (R₀ := R₀) V ρ₀ hinj hχ htyp hm h2 hclosed he hfrob
      support hs hlevel hs2 h2fresh hseed)
    hm rfl htyp (V.ops ρ₀) (V.determinant ρ₀ hinj hm.isPrime h2) (V.hD ρ₀ hinj hm.isPrime h2)
    valuation hphase localData

/-- Supply the root hypothesis of the fixed-set and primary consumers
with the additional coefficient-one comparison only at excluded primes. -/
theorem root_readings_on_window (hB : P.pool.card + 1 ≤ B) (hbudget : B ≤ W + 1) :
    let pair := realizedSpace (R₀ := R₀) V ρ₀ hinj hχ htyp hm h2 hclosed he hfrob
      support hs hlevel hs2 h2fresh hseed
    StageValuation (X := pair.1) (S := S) (δ := δ) →
      ExcludedAtOne pair.2 P.pool avoid →
      ∀ q, T.Good q → q ∉ P.pool → FreshAt pair.1 P.pool q := by
  intro pair valuation hexcl
  exact root_readings_of_stage P.type_good hB hbudget
    (expansions_on_window (R₀ := R₀) V ρ₀ hinj hχ htyp hm h2 hclosed he hfrob
      support hs hlevel hs2 h2fresh hseed)
    hm (V.ops ρ₀) (V.determinant ρ₀ hinj hm.isPrime h2 P.pool)
    (V.hD ρ₀ hinj hm.isPrime h2 P.pool) valuation hexcl

end ZInQ.Manuscript.RC.O12Realize

#print axioms ZInQ.Manuscript.RC.O12Realize.expansions_on_window
#print axioms ZInQ.Manuscript.RC.O12Realize.readings_on_window
#print axioms ZInQ.Manuscript.RC.O12Realize.root_readings_on_window
