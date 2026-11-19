import ZInQKernel.Contrib.OneProof.RC.ThetaCoeff.Forms

/-! The specified late Fourier sieve of tex 8427–8428 and 9477–9479.
It acts on the extracted index. The norm mask below implements that operation
on the weighted stage and its lift, with the same ideal classes and weights (P_M). -/

noncomputable section

open scoped Classical Quaternion
open Finset

namespace ZInQ.Manuscript.RC.StageJoin

open ThetaCoeff ZInQ.Manuscript.RC.Odd

/-- Precisely the primes at which the extra zero-or-retain operations are applied.
Label-only tests are not operations on the Fourier series. -/
structure LateSieve where
  primes : Finset ℕ
  prime : ∀ p ∈ primes, p.Prime

/-- Retain an extracted index exactly when none of the named primes divides it. -/
def LateSieve.Keep (B : LateSieve) (n : ℕ) : Prop :=
  ∀ b ∈ B.primes, ¬ b ∣ n

/-- At norm (m n), test divisibility of the extracted index (n). -/
def LateSieve.KeepNorm (B : LateSieve) (m k : ℕ) : Prop :=
  ∀ b ∈ B.primes, ¬ m * b ∣ k

variable {B : LateSieve} {m n p : ℕ}

theorem keepNorm_extract (hm : m ≠ 0) :
    B.KeepNorm m (m * n) ↔ B.Keep n := by
  simp only [LateSieve.KeepNorm, LateSieve.Keep, Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hm)]

/-- Away from the sieve and the extraction modulus the mask is constant
on the (p^2)-scalings used by the Brandt frame. -/
private theorem keepNorm_mul_sq (hp : p.Prime) (hm : ¬ p ∣ m) (hB : p ∉ B.primes) :
    B.KeepNorm m (p ^ 2 * n) ↔ B.KeepNorm m n := by
  unfold LateSieve.KeepNorm
  have hc (b : ℕ) (hb : b ∈ B.primes) : (m * b).Coprime (p ^ 2) := by
    apply Nat.Coprime.pow_right
    apply Nat.Coprime.symm
    apply hp.coprime_iff_not_dvd.mpr
    intro h
    rcases hp.dvd_mul.mp h with hd | hd
    · exact hm hd
    · exact hB ((Nat.prime_dvd_prime_iff_eq hp (B.prime b hb)).mp hd ▸ hb)
  exact forall_congr' fun b => forall_congr' fun hb => not_congr (hc b hb).dvd_mul_left

variable {A : Type*} [CommRing A]

/-- Select entire norm spheres in each good frame; keep its vector weights. -/
private abbrev sieveFrame (B : LateSieve) (m : ℕ) (Φ : AppF.PFrame p A)
    (hp : p.Prime) (hm : ¬ p ∣ m) (hB : p ∉ B.primes) : AppF.PFrame p A where
  V := Φ.V
  deq := Φ.deq
  vecs k := if B.KeepNorm m k then Φ.vecs k else ∅
  coord := Φ.coord
  F := Φ.F
  scale := Φ.scale
  coord_det k x hx := Φ.coord_det k x (by
    by_cases hk : B.KeepNorm m k
    · simpa only [ite_eq_left hk] using hx
    · simp [hk] at hx)
  scale_mem k x hx := by
    have h := keepNorm_mul_sq (B := B) (n := k) hp hm hB
    by_cases hk : B.KeepNorm m k
    · simpa only [ite_eq_left hk, ite_eq_left (h.mpr hk)] using
        Φ.scale_mem k x (by simpa only [ite_eq_left hk] using hx)
    · simp [hk] at hx
  div_mem k y hy hd := by
    have hk : B.KeepNorm m k := by
      by_contra h
      simp [h] at hy
    obtain ⟨hdk, x, hx, he⟩ := Φ.div_mem k y (by simpa only [ite_eq_left hk] using hy) hd
    have hj : B.KeepNorm m (k / p ^ 2) :=
      (keepNorm_mul_sq hp hm hB).mp (by rwa [Nat.mul_div_cancel' hdk])
    exact ⟨hdk, x, by simpa only [ite_eq_left hj] using hx, he⟩
  scale_inj := Φ.scale_inj
  coord_scale := Φ.coord_scale

private theorem sieveFrame_theta (Φ : AppF.PFrame p A)
    (hp : p.Prime) (hm : ¬ p ∣ m) (hB : p ∉ B.primes) (k : ℕ) :
    (sieveFrame B m Φ hp hm hB).theta k = if B.KeepNorm m k then Φ.theta k else 0 := by
  by_cases hk : B.KeepNorm m k <;> simp [AppF.PFrame.theta, sieveFrame, hk]

private theorem sieveFrame_nbrSum (Φ : AppF.PFrame p A)
    (hp : p.Prime) (hm : ¬ p ∣ m) (hB : p ∉ B.primes) (k : ℕ) (j : Option (ZMod p)) :
    (sieveFrame B m Φ hp hm hB).nbrSum j k = if B.KeepNorm m k then Φ.nbrSum j k else 0 := by
  rw [← keepNorm_mul_sq hp hm hB (n := k)]
  by_cases hk : B.KeepNorm m (p ^ 2 * k)
  · simp [AppF.PFrame.nbrSum, AppF.PFrame.mem1, sieveFrame, hk] <;> rfl
  · simp [AppF.PFrame.nbrSum, sieveFrame, hk]

/-- Apply the actual Fourier sieve to the weighted stage, retaining precisely
the original good primes that are outside the sieve list. -/
abbrev sieveStage (S : AppF.ThetaStage A) (B : LateSieve) : AppF.ThetaStage A where
  __ := S
  θ z k := if B.KeepNorm S.m k then S.θ z k else 0
  Good p := S.Good p ∧ p ∉ B.primes
  good_prime p hp := S.good_prime p hp.1
  good_ne_two p hp := S.good_ne_two p hp.1
  good_m p hp := S.good_m p hp.1
  s_unit p hp := S.s_unit p hp.1
  η_good p hp := S.η_good p hp.1
  hecke p hp := S.hecke p hp.1
  adjoint p hp := S.adjoint p hp.1
  frame p hp z := sieveFrame B S.m (S.frame p hp.1 z)
    (S.good_prime p hp.1) (S.good_m p hp.1) hp.2
  frame_theta p hp z k := by rw [sieveFrame_theta, S.frame_theta p hp.1]
  frame_scale p hp z x := S.frame_scale p hp.1 z x
  frame_nbr p hp z j k := by
    rw [sieveFrame_nbrSum]
    by_cases hk : B.KeepNorm S.m k
    · simpa only [ite_eq_left hk] using S.frame_nbr p hp.1 z j k
    · simp [hk]
  theta_zero z := by simp [S.theta_zero]

theorem sieveStage_aθ (S : AppF.ThetaStage A) (B : LateSieve) (hm : S.m ≠ 0) (n : ℕ) :
    (sieveStage S B).aθ n = if B.Keep n then S.aθ n else 0 := by
  have hk := keepNorm_extract (B := B) (n := n) hm
  by_cases hn : B.Keep n <;>
    simp [AppF.ThetaStage.aθ, AppF.ThetaStage.H, sieveStage, hk, hn]

variable {O : Type} [CommRing O] {M : ℕ}
variable {S : AppF.ThetaStage (StageRing O M)}

/-- Put the same norm mask into the integral ternary weights. -/
private def sieveWeight {a b : ℚ} (B : LateSieve) (m : ℕ) (f : ℍ[ℚ,a,0,b] → O)
    (x : ℍ[ℚ,a,0,b]) : O :=
  if ∃ k : ℕ, Visibility.nrd x = (k : ℚ) ∧ ¬ B.KeepNorm m k then 0 else f x

private theorem sieveWeight_at {a b : ℚ} (B : LateSieve) (m : ℕ) (f : ℍ[ℚ,a,0,b] → O)
    {x : ℍ[ℚ,a,0,b]} {k : ℕ} (hx : Visibility.nrd x = (k : ℚ)) :
    sieveWeight B m f x = if B.KeepNorm m k then f x else 0 := by
  have h : (∃ j : ℕ, Visibility.nrd x = (j : ℚ) ∧ ¬ B.KeepNorm m j) ↔ ¬ B.KeepNorm m k := by
    constructor
    · rintro ⟨j, hj, hkeep⟩
      have he : j = k := by exact_mod_cast hj.symm.trans hx
      exact he ▸ hkeep
    · exact fun hkeep => ⟨k, hx, hkeep⟩
  by_cases hk : B.KeepNorm m k <;> simp [sieveWeight, h, hk]

private theorem sieveWeight_sum {a b : ℚ} (B : LateSieve) (m : ℕ) (f : ℍ[ℚ,a,0,b] → O)
    (k : ℕ) :
    (∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ Visibility.nrd x = (k : ℚ)}, sieveWeight B m f x)
      = if B.KeepNorm m k then
        ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ Visibility.nrd x = (k : ℚ)}, f x
        else 0 := by
  by_cases hk : B.KeepNorm m k
  · rw [ite_eq_left hk]
    apply finsum_congr
    intro x
    by_cases hx : x.re = 0 ∧ Visibility.nrd x = (k : ℚ)
    · simp [finsum_eq_if, hx, sieveWeight_at B m f hx.2, hk]
    · simp [finsum_eq_if, hx]
  · rw [ite_eq_right hk]
    calc
      _ = ∑ᶠ _ : ℍ[ℚ,a,0,b], (0 : O) := by
        apply finsum_congr
        intro x
        by_cases hx : x.re = 0 ∧ Visibility.nrd x = (k : ℚ)
        · simp [hx, sieveWeight_at B m f hx.2, hk]
        · simp [finsum_eq_if, hx]
      _ = 0 := finsum_zero

/-- The integral lift of the sieved stage uses the original class weights
and the same coefficient mask before reduction. -/
def sieveLift (B : LateSieve) (E : Lift S) : Lift (sieveStage S B) where
  geom :=
    { E.geom with
      f := fun z => sieveWeight B S.m (E.geom.f z)
      f_conj := fun z u hu x => by
        simp only [sieveWeight, Visibility.nrd_conj]
        split_ifs
        · rfl
        · exact E.geom.f_conj z u hu x
      finite_supp := fun z k => (E.geom.finite_supp z k).subset (by
        rintro x ⟨hr, hn, hf⟩
        refine ⟨hr, hn, ?_⟩
        intro h
        exact hf (by simp [sieveWeight, h])) }
  classes := E.classes
  mass := E.mass
  P := E.P
  normChar := E.normChar
  localSum z k := by
    change stageReduction O M (∑ᶠ x ∈ _, sieveWeight B S.m (E.geom.f z) x) =
      if B.KeepNorm S.m k then S.θ (E.classes z) k else 0
    rw [sieveWeight_sum B S.m (E.geom.f z) k]
    split_ifs with hk
    · exact E.localSum z k
    · exact map_zero _
  η := E.η
  phase := E.phase
  parity := E.parity

theorem sieveLift_aθ (B : LateSieve) (E : Lift S) (hm : S.m ≠ 0) (n : ℕ) :
    (sieveLift B E).aθ n = if B.Keep n then E.aθ n else 0 := by
  have hk := keepNorm_extract (B := B) (n := n) hm
  simp only [Lift.aθ, Lift.H, Visibility.thetaCoeff, sieveLift, sieveStage, sieveWeight_sum, hk]
  by_cases hn : B.Keep n
  · simp only [hn, ite_true] <;> rfl
  · simp [hn]

/-- Keep the exact list with the integral source. Both projections are computed
from that single list, including primes where the original coefficient was zero. -/
structure SievedSource (S : AppF.ThetaStage (StageRing O M)) where
  late : LateSieve
  before : Lift S

abbrev SievedSource.stage (C : SievedSource S) : AppF.ThetaStage (StageRing O M) :=
  sieveStage S C.late

abbrev SievedSource.lift (C : SievedSource S) : Lift C.stage :=
  sieveLift C.late C.before

#print axioms keepNorm_extract
#print axioms keepNorm_mul_sq
#print axioms sieveFrame_theta
#print axioms sieveFrame_nbrSum
#print axioms sieveStage_aθ
#print axioms sieveWeight_at
#print axioms sieveWeight_sum
#print axioms sieveLift_aθ
#print axioms sieveStage
#print axioms sieveLift

end ZInQ.Manuscript.RC.StageJoin
