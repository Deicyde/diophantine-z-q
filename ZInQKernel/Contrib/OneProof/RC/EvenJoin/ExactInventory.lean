import ZInQKernel.Contrib.OneProof.RC.EvenJoin.DistinctCuspColumns
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.Coefficient

/-! The finite image of the actual columns is an independent inventory
over the receiving coefficient field. Intrinsic spans survive the merge. -/

noncomputable section

set_option maxHeartbeats 900000

namespace ZInQ.Manuscript.RC.EvenJoin

open AddressGenuine AuxInputs BlocksPerU EvenBudget EvenExpansion HeckeRing.GL2
open IsDedekindDomain ModularForm NumberField ThetaCoeff TauCeti Wiring
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped AdicCompletionExtension MatrixGroups

variable {K G L : Type} [Field K] [Group G] [AddCommGroup L]
variable {ε : L →+ ZMod 2} {T : TypeData L ε}

/-- Pull a character back along the same embedding as its Fourier
coefficients. The values on all units are specified, including inverses. -/
def charAt (κ : K →+* ℂ) (χ : G →* ℂˣ)
    (h : ∀ u, ∃ x : K, κ x = (χ u : ℂ)) : G →* Kˣ where
  toFun u := Units.mk0 (h u).choose fun hz =>
    (χ u).ne_zero ((h u).choose_spec.symm.trans (by simp [hz]))
  map_one' := by
    apply Units.ext
    apply κ.injective
    change κ (h 1).choose = κ 1
    rw [(h 1).choose_spec, map_one χ, Units.val_one, map_one κ]
  map_mul' u v := by
    apply Units.ext
    apply κ.injective
    change κ (h (u * v)).choose = κ ((h u).choose * (h v).choose)
    rw [(h (u * v)).choose_spec, map_mul κ, (h u).choose_spec, (h v).choose_spec,
      map_mul χ, Units.val_mul]

@[simp] theorem charAt_apply (κ : K →+* ℂ) (χ : G →* ℂˣ) (h) (u : G) :
    κ (charAt κ χ h u : K) = (χ u : ℂ) :=
  (h u).choose_spec

/-- Good recurrence on the genuine normalized newform, transported through
the common embedding. -/
def NormalizedCuspSource.eigen (s : NormalizedCuspSource) (κ : K →+* ℂ)
    (ha : ∀ n, ∃ x : K, κ x = s.coeff n)
    (hχ : ∀ u, ∃ x : K, κ x = (s.char u : ℂ)) : EigenSource K (IntrinsicGood T s.level) := by
  classical
  letI : NeZero s.level := ⟨s.level_ne⟩
  let a (n : ℕ) := (ha n).choose
  let χ (q : ℕ) := if h : q.Coprime s.level then
    (charAt κ s.char hχ (ZMod.unitOfCoprime q h) : K) else 0
  have hmap (n : ℕ) : κ (a n) = s.coeff n := (ha n).choose_spec
  refine .cusp a χ (κ.injective (by rw [hmap, s.coeff_zero, map_zero])) ?_
  intro q hq n
  let f := s.newform.toEigenformAwayFromLevel
  have hf := f.isEigen ⟨q, hq.1.1.pos⟩ hq.2
  rw [← f.qExpansion_coeff_eq_eigenvalue s.newform.isNorm ⟨q, hq.1.1.pos⟩ hq.2] at hf
  have hr := qExpansion_coeff_prime_mul_of_heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul
    hq.1.1 hq.2 hf n
  apply κ.injective
  simp only [map_mul, map_add, map_natCast, hmap, χ, dite_eq_left hq.2, charAt_apply]
  change s.coeff q * s.coeff n = s.coeff (q * n) +
    (q : ℂ) * (s.char (ZMod.unitOfCoprime q hq.2) : ℂ) * κ (Odd.divCoeff a q n)
  change s.coeff (q * n) = s.coeff q * s.coeff n -
    (if q ∣ n then (s.char (ZMod.unitOfCoprime q hq.2) : ℂ) * (q : ℂ) ^ ((2 : ℤ) - 1) *
      s.coeff (n / q) else 0) at hr
  rw [hr]
  by_cases hd : q ∣ n <;> simp [Odd.divCoeff, hd, hmap] <;> ring

@[simp] theorem NormalizedCuspSource.eigen_a (s : NormalizedCuspSource) (κ : K →+* ℂ)
    (ha hχ) (n : ℕ) :
    κ ((s.eigen (T := T) κ ha hχ).a n) = s.coeff n := (ha n).choose_spec

@[simp] theorem NormalizedCuspSource.eigen_char (s : NormalizedCuspSource) (κ : K →+* ℂ)
    (ha hχ) {q : ℕ} (hq : q.Coprime s.level) :
    (s.eigen (T := T) κ ha hχ).χ q = (charAt κ s.char hχ (ZMod.unitOfCoprime q hq) : K) := by
  classical
  change (if h : q.Coprime s.level then
    (charAt κ s.char hχ (ZMod.unitOfCoprime q h) : K) else 0) = _
  rw [dite_eq_left hq]

section Finite

variable {N : ℕ} [NeZero N] (D : Finset (CuspDilation N))
variable (κ : K →+* ℂ)
variable (ha : ∀ x : ↥D, ∀ n, ∃ z : K, κ z = x.val.source.coeff n)
variable (hχ : ∀ x : ↥D, ∀ u, ∃ z : K, κ z = (x.val.source.char u : ℂ))

/-- The source index is the image of the dilation index. All dilations of
one normalized newform therefore use one representation at the next step. -/
def cuspSources : Finset NormalizedCuspSource := by
  classical
  exact D.image CuspDilation.source

abbrev cuspOrigin (x : ↥D) : ↥(cuspSources D) := by
  classical
  exact ⟨x.val.source, Finset.mem_image.mpr ⟨x, x.property, rfl⟩⟩

theorem cuspSource_dvd (s : ↥(cuspSources D)) : s.val.level ∣ N := by
  classical
  obtain ⟨x, _, he⟩ := Finset.mem_image.mp s.property
  rw [← he]
  exact x.source_dvd

theorem cuspSource_exists (s : ↥(cuspSources D)) : ∃ x : ↥D, x.val.source = s.val := by
  classical
  obtain ⟨x, hx, he⟩ := Finset.mem_image.mp s.property
  exact ⟨⟨x, hx⟩, he⟩

include ha in
theorem cuspSourceCoeff (s : ↥(cuspSources D)) (n : ℕ) :
    ∃ z : K, κ z = s.val.coeff n :=
  let ⟨x, hx⟩ := cuspSource_exists D s
  hx ▸ ha x n

include hχ in
theorem cuspSourceChar (s : ↥(cuspSources D)) (u : (ZMod s.val.level)ˣ) :
    ∃ z : K, κ z = (s.val.char u : ℂ) := by
  obtain ⟨x, hx⟩ := cuspSource_exists D s
  have hs : ∀ t : NormalizedCuspSource, t = x.val.source →
      ∀ v : (ZMod t.level)ˣ, ∃ z : K, κ z = (t.char v : ℂ) := by
    intro t ht
    subst t
    exact hχ x
  exact hs s.val hx.symm u

/-- One independent inventory per tested set. Its column and character
equations are part of the construction in the following lemmas. -/
def cuspInventory (hLi : OldNewIndependenceWeightTwo) :
    Inventory ↥D ↥(cuspSources D) K T N where
  sourceLevel s := s.val.level
  source s := s.val.eigen κ (cuspSourceCoeff D κ ha s) (cuspSourceChar D κ hχ s)
  origin := cuspOrigin D
  degree x := x.val.degree
  degree_pos x := (NeZero.of_dvd (dvd_of_mul_right_dvd x.val.divides)).pos _
  level_dvd x := by
    change x.val.source.level * x.val.degree ∣ N
    rw [Nat.mul_comm]
    exact x.val.divides
  χ s := (charAt κ s.val.char (cuspSourceChar D κ hχ s)).comp (ZMod.unitsMap (cuspSource_dvd D s))
  χ_good s q hq := by
    dsimp
    rw [NormalizedCuspSource.eigen_char _ _ _ _ (hq.of_dvd_right (cuspSource_dvd D s))]
    rw [ZMod.unitsMap_unitOfCoprime]
  independent := by
    classical
    have hLI := (cuspDilation_coeff_independent hLi (N := N)).comp
      ((↑) : ↥D → CuspDilation N) Subtype.val_injective
    have hI := (linearIndependent_iff_injective_fintypeLinearCombination.mp hLI)
    intro v w hv
    have eqc (x : ↥D) (n : ℕ) :
        κ (Odd.divCoeff
          (((cuspOrigin D x).val.eigen (T := T) κ (cuspSourceCoeff D κ ha (cuspOrigin D x))
            (cuspSourceChar D κ hχ (cuspOrigin D x))).a) x.val.degree n) =
          x.val.coeff n := by
      unfold CuspDilation.coeff Odd.divCoeff
      by_cases hd : x.val.degree ∣ n
      · rw [ite_eq_left hd, ite_eq_left hd, NormalizedCuspSource.eigen_a]
      · rw [ite_eq_right hd, ite_eq_right hd, map_zero]
    have hs : (fun x => κ (v x)) = (fun x => κ (w x)) := by
      apply hI
      funext n
      simpa only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        map_sum, map_mul, eqc] using congrArg κ (congrFun hv n)
    exact funext fun x => κ.injective (congrFun hs x)

@[simp] theorem cuspInventory_coeff (hLi : OldNewIndependenceWeightTwo) (x : ↥D) (n : ℕ) :
    κ ((cuspInventory (T := T) D κ ha hχ hLi).expansion x n) = x.val.coeff n := by
  change κ (Odd.divCoeff (((cuspOrigin D x).val.eigen (T := T) κ
      (cuspSourceCoeff D κ ha (cuspOrigin D x)) (cuspSourceChar D κ hχ (cuspOrigin D x))).a)
      x.val.degree n) = x.val.coeff n
  unfold CuspDilation.coeff Odd.divCoeff
  by_cases hd : x.val.degree ∣ n
  · rw [ite_eq_left hd, ite_eq_left hd, NormalizedCuspSource.eigen_a]
  · rw [ite_eq_right hd, ite_eq_right hd, map_zero]

@[simp] theorem cuspInventory_char (hLi : OldNewIndependenceWeightTwo)
    (x : ↥D) (u : (ZMod N)ˣ) :
    κ ((cuspInventory (T := T) D κ ha hχ hLi).χ (cuspOrigin D x) u : K) =
      (x.val.char u : ℂ) :=
  charAt_apply _ _ _ _

end Finite

end ZInQ.Manuscript.RC.EvenJoin
