import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Determinant
import ZInQKernel.Contrib.OneProof.RC.TwoFresh.Stage

/-!
# The reduced two-trace vanishing

Tex 9741–9745. At each positive index choose two distinct good Frobenius
primes, avoiding that index, the ambient excluded primes and the added primes.
Then use continuity and the closed coefficient ideal. The odd stage is fixed
for the entire budget before any of these tests.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TwoFresh

open AddressGenuine PrintsArith Symbols TraceLimits
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable {T : TypeData L ε} {avoid : Finset ℕ} {frob : ℕ → GalQ}
variable {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)}
variable {m : Ideal O}

/-- The two good Hecke formulas both have zero diamond term at the tested
indices (tex 9660–9662, 9741–9745). -/
theorem two_hecke_coeff (coeff : ℕ → Λ →ₗ[O] O)
    {H₁ D₁ H₂ D₂ : Λ →ₗ[O] Λ} {n q₁ q₂ : ℕ}
    (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    (hn₁ : ¬ q₁ ∣ n) (hn₂ : ¬ q₂ ∣ n)
    (hecke₁ : HeckeFourier coeff H₁ D₁ q₁) (hecke₂ : HeckeFourier coeff H₂ D₂ q₂)
    (F : Λ) : coeff n (H₁ (H₂ F)) = coeff (q₂ * (q₁ * n)) F := by
  have h₂ : ¬ q₂ ∣ q₁ * n := fun hd => hne.symm
    ((Nat.prime_dvd_prime_iff_eq hq₂ hq₁).mp ((hq₂.dvd_mul.mp hd).resolve_right hn₂))
  rw [hecke₁ n, ite_eq_right hn₁, add_zero, hecke₂ (q₁ * n), ite_eq_right h₂, add_zero]

/-- Pairs of all good Frobenius lifts at distinct primes outside any finite
set are dense. The second test excludes the first prime in addition to the
original set (tex 9666–9668, 9745; product argument on-the-spot, provenance (c)). -/
theorem dense_twoFreshTests (T : TypeData L ε) (A : Finset ℕ) :
    Dense {x : GalQ × GalQ | ∃ q₁ q₂, T.Good q₁ ∧ T.Good q₂ ∧ q₁ ∉ A ∧ q₂ ∉ A ∧
      q₁ ≠ q₂ ∧ IsFrobAt x.1 q₁ ∧ IsFrobAt x.2 q₂} := by
  refine dense_iff_inter_open.mpr ?_
  rintro W hW ⟨⟨g, h⟩, hgh⟩
  obtain ⟨V₁, V₂, hV₁, hV₂, hg, hh, hVW⟩ := isOpen_prod_iff.mp hW g h hgh
  obtain ⟨x, ⟨q₁, hq₁, hA₁, hx⟩, hxV⟩ :=
    (dense_frobeniusTests T A).exists_mem_open hV₁ ⟨g, hg⟩
  obtain ⟨y, ⟨q₂, hq₂, hA₂, hy⟩, hyV⟩ :=
    (dense_frobeniusTests T (insert q₁ A)).exists_mem_open hV₂ ⟨h, hh⟩
  exact ⟨(x, y), hVW ⟨hxV, hyV⟩, q₁, q₂, hq₁, hq₂, hA₁,
    fun e => hA₂ (Finset.mem_insert_of_mem e),
    fun e => hA₂ (e ▸ Finset.mem_insert_self q₁ A), hx, hy⟩

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- Joint continuity on a fixed vector follows from the stated pointwise
continuity, because trace acts by multiplication on each constituent
(on-the-spot, provenance (c), for tex 9745). -/
theorem continuous_twoTraces (hcont : ContinuousOperators ρ Λ) (v : Λ) :
    Continuous fun x : GalQ × GalQ => tV ρ x.1 (tV ρ x.2 v) := by
  apply continuous_pi
  intro i
  by_cases hi : (v : I → K) i = 0
  · simpa only [tV, scalarOp_apply, hi, mul_zero] using
      (continuous_const : Continuous fun _ : GalQ × GalQ => (0 : K))
  · have hc : Continuous fun g : GalQ => tV ρ g v i :=
      (continuous_apply i).comp (hcont.trace v)
    have he (x : GalQ × GalQ) :
        tV ρ x.1 (tV ρ x.2 v) i =
          (tV ρ x.1 v i * tV ρ x.2 v i) * ((v : I → K) i)⁻¹ := by
      simp only [tV, scalarOp_apply, mul_assoc, mul_inv_cancel₀ hi, mul_one]
      ring
    simp_rw [he]
    exact ((hc.comp continuous_fst).mul (hc.comp continuous_snd)).mul continuous_const

variable [T2Space K] [TopologicalSpace O] [CompactSpace O]
variable [ContinuousSMul O K]

open ZInQ.Manuscript.RC.Odd

/-- The `h2fresh` argument of `buildConstituentModel` for the actual odd
source (tex 9741–9745). The two coefficient comparisons are `theta_mod_two`
and `H_off_unary` of the (O.12) interface, stated on the constructor's data.
The depth hypothesis is the existing `OddStageSource` at the fixed budget. -/
theorem h2fresh [CharZero K] (B : ℕ) (F : Finset ℕ → Λ)
    (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hcont : ContinuousOperators ρ Λ) (hunr : UnramifiedConstituents T avoid ρ)
    (ops : GoodOperators T avoid frob ρ Λ)
    (coeff : ℕ → Λ →ₗ[O] O)
    (D : ∀ U, DeterminantFourierData ops m (F U)) (hD : ∀ U, (D U).coeff = coeff)
    (hcoeff : ∀ n, Continuous (coeff n))
    (hm2 : (2 : O) ∈ m) (hm : IsClosed (m : Set O)) (hΛ : Λ.FG)
    (S : Finset ℕ) (hlevel : T.m.primeFactors ∪ avoid ⊆ S)
    (integral_inclusion : Function.Injective (algebraMap O K))
    {WU R M : ℕ} {δ : ℤ} {η a : ℕ → O} {Good adm : ℕ → Prop} {ap : ℕ → ℤ}
    (hR : 2 ≤ R)
    (hstage : OddStageSource O WU R M δ (fun p => stageReduction O M (η p))
      Good adm ap (fun n => stageReduction O M (a n)))
    (hwindow : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
      F U ≠ 0 → U.card ≤ WU ∧ ∀ s ∈ U, Good s)
    (H : Finset ℕ → ℕ → O)
    (theta_mod_two : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B →
      ∀ n, n ≠ 0 → (2 : O) ∣ coeff n (F U) - H U n)
    (H_off_unary : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → F U ≠ 0 →
      ∀ (J : List ℕ), J.Nodup → J.toFinset = U → ∀ n : ℕ, ¬ oddPart n ⊆ U →
      ∃ b : O, algebraMap O K b =
        (2 : K) ^ (-(δ + (U.card : ℤ) + 1)) * algebraMap O K (TL η J a n) ∧
        (2 : O) ∣ H U n - b) :
    ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → U.card + 1 ≤ B → ∀ g h,
      ∀ n : ℕ, n ≠ 0 → coeff n ⟨tV ρ g (tV ρ h (F U)),
        (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1 g _
          ((stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1 h _ (F U).2)⟩ ∈ m := by
  intro U hU hUB g h n hn
  let hst := (stable_operators T hfrob (lattice_closed Λ hΛ) hcont hunr ops).1
  let trace (g : GalQ) (x : Λ) : Λ := ⟨tV ρ g x, hst g _ x.2⟩
  change coeff n (trace g (trace h (F U))) ∈ m
  by_cases hzero : F U = 0
  · have hz : trace g (trace h (F U)) = 0 := Subtype.ext (by simp [trace, hzero])
    rw [hz, map_zero]
    exact m.zero_mem
  obtain ⟨hWU, hGU⟩ := hwindow U hU hUB hzero
  let A := S ∪ U ∪ n.primeFactors
  have hc : Continuous fun x : GalQ × GalQ => coeff n (trace x.1 (trace x.2 (F U))) :=
    (hcoeff n).comp ((continuous_twoTraces hcont (F U)).subtype_mk _)
  refine (dense_twoFreshTests T A).induction
    (P := fun x => coeff n (trace x.1 (trace x.2 (F U))) ∈ m) ?_ (hm.preimage hc) (g, h)
  rintro ⟨x, y⟩ ⟨q₁, q₂, hq₁, hq₂, hA₁, hA₂, hne, hx, hy⟩
  have hqa {q : ℕ} (hq : q ∉ A) : q ∉ avoid := fun e =>
    hq (Finset.mem_union_left _ (Finset.mem_union_left _ (hlevel (Finset.mem_union_right _ e))))
  have hqU {q : ℕ} (hq : q ∉ A) : q ∉ U := fun e =>
    hq (Finset.mem_union_left _ (Finset.mem_union_right _ e))
  have hqn {q : ℕ} (hp : q.Prime) (hq : q ∉ A) : ¬ q ∣ n := fun e =>
    hq (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp, e, hn⟩))
  have ht {z : GalQ} {q : ℕ} (hq : T.Good q) (hA : q ∉ A) (hz : IsFrobAt z q) (v : Λ) :
      trace z v = ops.hecke q v := by
    apply Subtype.ext
    change tV ρ z v = _
    rw [(operators_eq_at_frobenius T hunr hq (hqa hA) hz (hfrob q hq)).1,
      ops.trace_eq q hq (hqa hA)]
  have hecke {q : ℕ} (hq : T.Good q) (hA : q ∉ A) :
      HeckeFourier coeff (ops.hecke q) (ops.diamond q) q :=
    hD U ▸ (D U).hecke_eq q hq (hqa hA)
  change coeff n (trace x (trace y (F U))) ∈ m
  rw [ht hq₂ hA₂ hy, ht hq₁ hA₁ hx,
    two_hecke_coeff coeff hq₁.1 hq₂.1 hne (hqn hq₁.1 hA₁) (hqn hq₂.1 hA₂)
      (hecke hq₁ hA₁) (hecke hq₂ hA₂)]
  let j := q₂ * (q₁ * n)
  have hj : j ≠ 0 := mul_ne_zero hq₂.1.ne_zero (mul_ne_zero hq₁.1.ne_zero hn)
  obtain ⟨hw, hoff⟩ := fresh_squarefree_weight hn hq₁.1 hq₂.1 hne (hqU hA₁) (hqU hA₂)
    (hqn hq₁.1 hA₁) (hqn hq₂.1 hA₂)
  have hcard : U.toList.length = U.card := Finset.length_toList _
  have hbudget : U.toList.length ≤ WU := by simpa only [hcard] using hWU
  have hw' : 2 ≤ (oddPart j \ U.toList.toFinset).card := by simpa using hw
  obtain ⟨c, -, hnorm⟩ := fresh_normalizations (K := K) hstage hR U.toList U.nodup_toList
    (fun p hp => hGU p (Finset.mem_toList.mp hp)) hbudget j hw'
  obtain ⟨b, hb, hb₂⟩ :=
    H_off_unary U hU hUB hzero U.toList U.nodup_toList (Finset.toList_toFinset U) j hoff
  have hb' : b = 2 * c := integral_inclusion (hb.trans (by simpa only [hcard] using hnorm))
  have hH : (2 : O) ∣ H U j := (dvd_iff_dvd_of_dvd_sub hb₂).mpr ⟨c, hb'⟩
  have hF : (2 : O) ∣ coeff j (F U) := (dvd_iff_dvd_of_dvd_sub
    (theta_mod_two U hU hUB j hj)).mpr hH
  obtain ⟨b, hb⟩ := hF
  rw [hb]
  exact m.mul_mem_right b hm2


end ZInQ.Manuscript.RC.TwoFresh
