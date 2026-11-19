import ZInQKernel.Contrib.OneProof.R16Thm1b
import ZInQKernel.Contrib.AbVarBC.Main
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing

/-! # Shimura 1973, Theorem 1: comparison with the kernel interface

The composite operators are data on the Jacobian, with an independent divisor-class
description. The relations connecting that description to the prime operators are
separated from the proof of Theorem 1. See `docs/research/shimura-steps.md`.
-/

noncomputable section

namespace ShimuraSteps

set_option maxHeartbeats 1000000

open scoped TensorProduct MatrixGroups ModularForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open LeafModCurves PkgI3 PkgI3.AbVar
open PkgI4 (CF coeff IsNewform IsNormalizedEigenform)
open AfTateLam (IsX1Gen IsHeckeT IsDiamond HeckeFree evF heckeJ KillsIf IsAfQuotient
  CPt AtTau ajC endC shiftDiv mulNat)
open R16Thm1

variable {N : ℕ} {J : AbVar ℚ} {tp : Nat.Primes → AbVar.End J} {δ : (ZMod N)ˣ → AbVar.End J}
  {ξ : ℕ → AbVar.End J} {χ : DirichletCharacter ℂ N} {f : CF N 2}

/-- Triangular representatives of the weight-two correspondence of index `n`:
for `a ∣ n`, `gcd(a,N)=1`, `0 ≤ b < d=n/a`, use
`τ ↦ γ_a ((aτ+b)/d)`, where `γ_a ∈ Γ₀(N)` has lower right entry `a mod N`.
This is a condition on the actual action on degree-zero divisor classes, extending
`IsHeckeT`. The convention dictionary for the printed `ξ_n` belongs to the bridge. -/
def IsXi {X : Over SpecQ} [IsIntegral X.left] (jX tX : X.left.functionField)
    (aj : X ⟶ J.X) (n : ℕ) (t : AbVar.End J) : Prop :=
  let D := n.divisors.filter fun a => a.Coprime N
  ∀ (g : D → SL(2, ℤ)),
    (∀ a : D, (N : ℤ) ∣ g a 1 0 ∧ ((g a 1 1 : ℤ) : ZMod N) = (a.val : ZMod N)) →
    ∀ (τ τ' : UpperHalfPlane) (x x' : CPt X)
      (y y' : (a : D) → Fin (n / a.val) → CPt X),
      AtTau N jX tX x τ → AtTau N jX tX x' τ' →
      (∀ a b, AtTau N jX tX (y a b) (g a • shiftDiv (n / a.val) b (mulNat a.val τ))) →
      (∀ a b, AtTau N jX tX (y' a b) (g a • shiftDiv (n / a.val) b (mulNat a.val τ'))) →
      endC t (ajC aj x / ajC aj x') =
        ∏ a : D, ∏ b, ajC aj (y a b) / ajC aj (y' a b)

/-- The Hecke multiplication laws on the Jacobian. At a bad prime the correction
term vanishes; at a good prime it is `p⟨p⟩ ξ_{p^k}`. The zero index is a dummy. -/
structure HeckeRelations (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J)
    (ξ : ℕ → AbVar.End J) : Prop where
  zero : ξ 0 = 0
  one : ξ 1 = 1
  prime : ∀ p : Nat.Primes, ξ p = tp p
  coprime : ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → ξ (m * n) = ξ m * ξ n
  good : ∀ (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N) (k : ℕ),
    ξ ((p : ℕ) ^ (k + 2)) = tp p * ξ ((p : ℕ) ^ (k + 1)) -
      ((p : ℕ) : AbVar.End J) * δ (unitOf N p.2 hpN) * ξ ((p : ℕ) ^ k)
  bad : ∀ (p : Nat.Primes), (p : ℕ) ∣ N → ∀ k : ℕ, ξ ((p : ℕ) ^ k) = tp p ^ k

/-- Each positive-index operator is characterized by the independent action
formula. The pinning condition rules out spurious choices if the complex-point
dictionary does not yet realize the formula on enough classes. -/
def XiAction {X : Over SpecQ} [IsIntegral X.left] (jX tX : X.left.functionField)
    (aj : X ⟶ J.X) (ξ : ℕ → AbVar.End J) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ t : AbVar.End J, IsXi (N := N) jX tX aj n t ↔ t = ξ n

/-- Missing on-the-spot bridge: the composite correspondences on the same rational
Jacobian, in the normalization of Shimura's Hecke ring (Shimura 1973, pp. 525–526,
AI page read for the ring and its use). The triangular representative dictionary
and the multiplication and descent on this model still need a proof. Neither
Shimura's 1971 book nor Diamond–Shurman is a manuscript citation for this bridge. -/
def ShimuraHeckeRelations : Prop :=
  ∀ (N : ℕ), 2 ≤ N →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ (tp : Nat.Primes → AbVar.End J) (δ : (ZMod N)ˣ → AbVar.End J),
      (∀ p : Nat.Primes, IsHeckeT N jX tX aj (p : ℕ) (tp p)) →
      (∀ d : (ZMod N)ˣ, IsDiamond N jX tX aj d (δ d)) →
      ∃ ξ : ℕ → AbVar.End J,
        XiAction (N := N) jX tX aj ξ ∧ HeckeRelations tp δ ξ

/-- The good-prime square is an equality for the independent operators. -/
theorem xi_sq (h : HeckeRelations tp δ ξ) (p : Nat.Primes) (hpN : ¬ (p : ℕ) ∣ N) :
    ξ ((p : ℕ) * p) = xiSq tp δ p hpN := by
  simpa [pow_two, h.one, h.prime, xiSq] using h.good p hpN 0

/-- Two different Dirichlet primes represent the same diamond class. -/
theorem two_primes (hN : 2 ≤ N) (d : (ZMod N)ˣ) :
    ∃ (p q : Nat.Primes) (hp : ¬ (p : ℕ) ∣ N) (hq : ¬ (q : ℕ) ∣ N),
      p ≠ q ∧ unitOf N p.2 hp = d ∧ unitOf N q.2 hq = d := by
  let : NeZero N := ⟨by omega⟩
  obtain ⟨p, hpN, hp, hpd⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := N) d.isUnit N
  obtain ⟨q, hqp, hq, hqd⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := N) d.isUnit p
  have hp' : ¬ p ∣ N := fun h => (not_le_of_gt hpN) (Nat.le_of_dvd (by omega) h)
  have hq' : ¬ q ∣ N := fun h => (not_le_of_gt (hpN.trans hqp)) (Nat.le_of_dvd (by omega) h)
  refine ⟨⟨p, hp⟩, ⟨q, hq⟩, hp', hq', ?_, Units.ext ?_, Units.ext ?_⟩
  · exact fun e => hqp.ne (congrArg Subtype.val e)
  · simpa [unitOf, ZMod.coe_unitOfCoprime] using hpd
  · simpa [unitOf, ZMod.coe_unitOfCoprime] using hqd

/-- The coprime coefficient identity, in the order of the Hecke product. -/
theorem coeff_coprime (hf : IsNormalizedEigenform f χ)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n) :
    coeff f (m * n) = coeff f m * coeff f n := by
  simpa [hmn.gcd_eq_one] using (hf.2.2 m n hm hn).symm

/-- The weight-two coefficient recurrence, including bad primes. -/
theorem coeff_prime_power (hf : IsNormalizedEigenform f χ) (p : Nat.Primes) (k : ℕ) :
    coeff f ((p : ℕ) ^ (k + 2)) =
      coeff f p * coeff f ((p : ℕ) ^ (k + 1)) -
        ((p : ℕ) : ℂ) * χ ((p : ℕ) : ZMod N) * coeff f ((p : ℕ) ^ k) := by
  let q : ℕ := p
  have hp : q.Prime := p.2
  change coeff f (q ^ (k + 2)) = coeff f q * coeff f (q ^ (k + 1)) -
    (q : ℂ) * χ (q : ZMod N) * coeff f (q ^ k)
  have h := hf.2.2 q (q ^ (k + 1)) hp.pos (pow_pos hp.pos _)
  rw [Nat.gcd_eq_left (dvd_pow_self q (by omega)), hp.divisors, Finset.sum_pair hp.one_lt.ne] at h
  have hm : q * q ^ (k + 1) = q ^ (k + 2) := (pow_succ' q (k + 1)).symm
  have hd : q * q ^ (k + 1) / q ^ 2 = q ^ k := by
    rw [hm, pow_add, Nat.mul_div_cancel _ (pow_pos hp.pos _)]
  rw [hd, one_pow, Nat.div_one, hm] at h
  norm_num at h
  linear_combination -h

/-- The bad prime powers are pure powers of the prime coefficient. -/
theorem coeff_bad_power (hf : IsNormalizedEigenform f χ) (p : Nat.Primes)
    (hpN : (p : ℕ) ∣ N) (k : ℕ) :
    coeff f ((p : ℕ) ^ k) = coeff f p ^ k := by
  have hz : χ ((p : ℕ) : ZMod N) = 0 := by
    apply χ.map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    exact fun h => (Nat.Prime.coprime_iff_not_dvd p.2).1 h hpN
  induction k using Nat.twoStepInduction with
  | zero => simpa using hf.2.1
  | one => simp
  | more k _ ih =>
    rw [coeff_prime_power hf p k, hz, mul_zero, zero_mul, sub_zero, ih]
    exact (pow_succ' (coeff f p) (k + 1)).symm

/-- The coefficient of index `n` as an element of the coefficient field. -/
def ak (f : CF N 2) (n : ℕ) : coeffField f := ⟨coeff f n, coeff_mem_coeffField f n⟩

/-- Diamond eigenvalues belong to `K_f`: use the good square coefficient at a
Dirichlet prime. -/
theorem chi_mem (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ) (d : (ZMod N)ˣ) :
    χ (d : ZMod N) ∈ coeffField f := by
  obtain ⟨p, _, hp, _, _, hd, -⟩ := two_primes hN d
  have ha : ((p : ℕ) : ZMod N) = (d : ZMod N) := by
    simpa [unitOf, ZMod.coe_unitOfCoprime] using congrArg Units.val hd
  have h := coeff_sq_relation hf p.2
  rw [ha] at h
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have he : χ (d : ZMod N) =
      (coeff f p * coeff f p - coeff f ((p : ℕ) * p)) / ((p : ℕ) : ℂ) :=
    (div_eq_iff hp0).2 h |>.symm
  rw [he]
  exact (coeffField f).div_mem
    ((coeffField f).sub_mem ((coeffField f).mul_mem (coeff_mem_coeffField f p)
      (coeff_mem_coeffField f p)) (coeff_mem_coeffField f _)) ((coeffField f).natCast_mem _)

/-- The diamond eigenvalues lifted to the coefficient field. -/
def dk (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ) (d : (ZMod N)ˣ) : coeffField f :=
  ⟨χ (d : ZMod N), chi_mem hN hf d⟩

theorem ak_good (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ) (p : Nat.Primes)
    (hp : ¬ (p : ℕ) ∣ N) (k : ℕ) :
    ak f ((p : ℕ) ^ (k + 2)) = ak f p * ak f ((p : ℕ) ^ (k + 1)) -
      ((p : ℕ) : coeffField f) * dk hN hf (unitOf N p.2 hp) * ak f ((p : ℕ) ^ k) := by
  apply Subtype.ext
  simpa [ak, dk, unitOf, ZMod.coe_unitOfCoprime] using coeff_prime_power hf p k

theorem ak_mul (hf : IsNormalizedEigenform f χ) {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (h : m.Coprime n) :
    ak f (m * n) = ak f m * ak f n :=
  Subtype.ext (coeff_coprime hf hm hn h)

theorem ak_bad (hf : IsNormalizedEigenform f χ) (p : Nat.Primes)
    (hp : (p : ℕ) ∣ N) (k : ℕ) :
    ak f ((p : ℕ) ^ k) = ak f p ^ k := by
  apply Subtype.ext
  simpa [ak] using coeff_bad_power hf p hp k

/-- Forward generation, with the eigenvalue tracked in parallel. This also serves
as the induction for clause (ii) in the subring of compatible pairs. -/
theorem xi_mem (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) (S : Subring (AbVar.End J × coeffField f))
    (hT : ∀ p : Nat.Primes, (tp p, ak f p) ∈ S)
    (hD : ∀ d : (ZMod N)ˣ, (δ d, dk hN hf d) ∈ S) :
    ∀ n : ℕ, (ξ n, ak f n) ∈ S := by
  have hz : coeff f 0 = 0 := by
    unfold coeff
    exact CuspFormClass.qExpansion_coeff_zero f one_pos (by simp [CongruenceSubgroup.strictPeriods_Gamma1])
  have h0 : (ξ 0, ak f 0) = 0 :=
    Prod.ext h.zero (Subtype.ext hz)
  have h1 : (ξ 1, ak f 1) = 1 :=
    Prod.ext h.one (Subtype.ext hf.2.1)
  apply Nat.recOnPrimeCoprime
  · rw [h0]; exact S.zero_mem
  · intro p k hp
    let P : Nat.Primes := ⟨p, hp⟩
    change (ξ ((P : ℕ) ^ k), ak f ((P : ℕ) ^ k)) ∈ S
    by_cases hpN : p ∣ N
    · rw [h.bad P hpN, ak_bad hf P hpN]
      exact S.pow_mem (hT P) k
    induction k using Nat.twoStepInduction with
    | zero => rw [pow_zero, h1]; exact S.one_mem
    | one => simpa [h.prime P] using hT P
    | more k ih₀ ih₁ =>
      rw [h.good P hpN k, ak_good hN hf P hpN k]
      change (tp P, ak f P) * (ξ ((P : ℕ) ^ (k + 1)), ak f ((P : ℕ) ^ (k + 1))) -
        ((P : ℕ) : AbVar.End J × coeffField f) *
          (δ (unitOf N P.2 hpN), dk hN hf (unitOf N P.2 hpN)) *
          (ξ ((P : ℕ) ^ k), ak f ((P : ℕ) ^ k)) ∈ S
      apply S.sub_mem
      · exact S.mul_mem (hT P) ih₁
      · exact S.mul_mem (S.mul_mem (natCast_mem S (P : ℕ)) (hD (unitOf N P.2 hpN))) ih₀
  · intro m n hm hn hmn ihₘ ihₙ
    rw [h.coprime m n (by omega) (by omega) hmn, ak_mul hf (by omega) (by omega) hmn]
    exact S.mul_mem ihₘ ihₙ

/-- Reverse integral generation: two primes representing the diamond class give two
coprime multiples of the same pair. Bézout recovers the pair itself. -/
theorem diamond_mem (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) (S : Subring (AbVar.End J × coeffField f))
    (hξ : ∀ n : ℕ, (ξ n, ak f n) ∈ S) (d : (ZMod N)ˣ) :
    (δ d, dk hN hf d) ∈ S := by
  obtain ⟨p, q, hp, hq, hpq, hpd, hqd⟩ := two_primes hN d
  have hs (r : Nat.Primes) (hr : ¬ (r : ℕ) ∣ N) (hd : unitOf N r.2 hr = d) :
      (r : ℕ) • (δ d, dk hN hf d) ∈ S := by
    have he := h.good r hr 0
    have ha := ak_good hN hf r hr 0
    have ha1 : ak f 1 = 1 := Subtype.ext hf.2.1
    simp only [Nat.zero_add, pow_one, pow_zero, h.prime, h.one, ha1, hd, _root_.mul_one] at he ha
    have hsub := S.sub_mem (S.mul_mem (hξ r) (hξ r)) (hξ ((r : ℕ) ^ 2))
    have e : (r : ℕ) • (δ d, dk hN hf d) =
        (ξ r, ak f r) * (ξ r, ak f r) - (ξ ((r : ℕ) ^ 2), ak f ((r : ℕ) ^ 2)) := by
      apply Prod.ext
      · change (r : ℕ) • δ d = ξ r * ξ r - ξ ((r : ℕ) ^ 2)
        rw [he, h.prime, sub_sub_cancel, nsmul_eq_mul]
      · change (r : ℕ) • dk hN hf d = ak f r * ak f r - ak f ((r : ℕ) ^ 2)
        rw [ha, sub_sub_cancel, nsmul_eq_mul]
    exact e ▸ hsub
  let r : ℕ := p
  let s : ℕ := q
  have hc : r.Coprime s := (Nat.Prime.coprime_iff_not_dvd p.2).2
    (fun h' => hpq (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).1 h')))
  have hz : (r : ℤ) * r.gcdA s + (s : ℤ) * r.gcdB s = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hc.gcd_eq_one, Nat.cast_one]
  have hsum := S.add_mem (S.zsmul_mem (hs p hp hpd) (r.gcdA s))
    (S.zsmul_mem (hs q hq hqd) (r.gcdB s))
  change r.gcdA s • (r • (δ d, dk hN hf d)) +
    r.gcdB s • (s • (δ d, dk hN hf d)) ∈ S at hsum
  rw [← natCast_zsmul (δ d, dk hN hf d) r, ← natCast_zsmul (δ d, dk hN hf d) s,
    smul_smul, smul_smul,
    ← add_smul, mul_comm (r.gcdA s), mul_comm (r.gcdB s), hz, one_smul] at hsum
  exact hsum

/-- The two sets of generators yield the same integral ring, including their
eigenvalue maps. Projecting to the first factor gives equality in `End(J)`. -/
theorem closure_eq (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) :
    Subring.closure (Set.range fun n : ℕ => (ξ n, ak f n)) =
      Subring.closure (Set.range (fun p : Nat.Primes => (tp p, ak f p)) ∪
        Set.range (fun d : (ZMod N)ˣ => (δ d, dk hN hf d))) := by
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro _ ⟨n, rfl⟩
    exact xi_mem hN hf h _ (fun p => Subring.subset_closure (Or.inl ⟨p, rfl⟩))
      (fun d => Subring.subset_closure (Or.inr ⟨d, rfl⟩)) n
  · apply Subring.closure_le.mpr
    rintro _ (⟨p, rfl⟩ | ⟨d, rfl⟩)
    · exact Subring.subset_closure ⟨(p : ℕ), Prod.ext (h.prime p) rfl⟩
    · have hξ (n : ℕ) : (ξ n, ak f n) ∈ Subring.closure (Set.range fun i : ℕ => (ξ i, ak f i)) :=
        Subring.subset_closure (Set.mem_range_self n)
      exact diamond_mem hN hf h _ hξ d

/-- The two generator systems give the same integral subring of `End(J)`. -/
theorem end_ring_eq (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) :
    Subring.closure (Set.range ξ) = Subring.closure (Set.range tp ∪ Set.range δ) := by
  have hh := congrArg (fun S => S.map (RingHom.fst (AbVar.End J) (coeffField f)))
    (closure_eq hN hf h)
  simp only [RingHom.map_closure, Set.image_union, ← Set.range_comp] at hh
  exact hh

section Quotient

variable {A : AbVar ℚ} {ν : AbVar.Hom J A}

/-- Precomposing with `[m]` is `m`-fold addition on `Hom(J,A)`. -/
theorem nsmul_hom_eq (m : ℕ) (v : AbVar.Hom J A) :
    comp (((m : ℤ) : AbVar.End J)) v = m • v := by
  have hm : (((m : ℤ) : AbVar.End J)) = m • (1 : AbVar.End J) := by
    rw [Int.cast_natCast, nsmul_one]
  change preC v (((m : ℤ) : AbVar.End J)) = m • v
  rw [hm, map_nsmul]
  apply congrArg (m • ·)
  apply Hom.ext'
  change 𝟙 J.X ≫ v.hom = v.hom
  exact Category.id_comp _

/-- Multiplication by a positive integer does not change the scheme-theoretic
image of an endomorphism: the ideal sheaves defining the images are equal. -/
theorem image_ideal_nsmul (m : ℕ) (hm : 0 < m) (t : AbVar.End J) :
    (m • t).hom.left.ker = t.hom.left.ker := by
  have hs := (ZInQ.Contrib.AbVarBC.mulIsogeny ℚ J (m : ℤ) (by exact_mod_cast hm.ne')).2
  let : Surjective (((m : ℤ) : AbVar.End J).hom.left) := hs
  have : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  have : IsSchemeTheoreticallyDominant (((m : ℤ) : AbVar.End J).hom.left) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  rw [← nsmul_hom_eq m t, comp_hom, Over.comp_left, Scheme.Hom.ker_comp,
    Scheme.Hom.ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- The cancellability needed for quotient annihilators and for Hecke-compatible
maps is a direct consequence of surjectivity of multiplication by `m`. -/
theorem hom_nsmul_eq_zero (m : ℕ) (hm : 0 < m) (v : AbVar.Hom J A)
    (hv : m • v = 0) : v = 0 := by
  have : Surjective (((m : ℤ) : AbVar.End J).hom.left) :=
    (ZInQ.Contrib.AbVarBC.mulIsogeny ℚ J (m : ℤ) (by exact_mod_cast hm.ne')).2
  have hcomp : comp (((m : ℤ) : AbVar.End J)) v = 0 := (nsmul_hom_eq m v).trans hv
  have : IsIntegral J.X.left := GeometricallyIntegral.isIntegral_of_subsingleton J.X.hom
  apply Hom.ext'
  rw [Hom.hom_zero]
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated A.X.hom (by rw [Over.w, Over.w])
    (((m : ℤ) : AbVar.End J).hom.left)
  rw [← Over.comp_left, ← Over.comp_left, MonObj.comp_one]
  simpa only [comp_hom, Hom.hom_zero] using
    congrArg (fun u : AbVar.Hom J A => u.hom.left) hcomp

/-- The integral elements of the rational annihilator, by clearing a positive
denominator in the image of the Hecke ring. -/
def Sat (I : Set (AbVar.End J)) : Set (AbVar.End J) :=
  { t | ∃ m : ℕ, 0 < m ∧ m • t ∈ I }

/-- Saturation leaves the whole family of scheme-theoretic images unchanged,
so it also leaves their sum unchanged. Here images are given by their defining
ideal sheaves in `J`. -/
theorem image_family_sat (I : Set (AbVar.End J)) :
    (fun t : AbVar.End J => t.hom.left.ker) '' Sat I =
      (fun t : AbVar.End J => t.hom.left.ker) '' I := by
  ext s
  constructor
  · rintro ⟨t, ⟨m, hm, ht⟩, rfl⟩
    exact ⟨m • t, ht, image_ideal_nsmul m hm t⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ⟨1, one_pos, by simpa using ht⟩, rfl⟩

/-- Annihilation by a family of endomorphisms, as a test on the maps out of `J`. -/
def Kills (I : Set (AbVar.End J)) (ν : AbVar.Hom J A) : Prop :=
  ∀ t ∈ I, t.hom ≫ ν.hom = (0 : AbVar.Hom J A).hom

/-- Stable under saturation in the precise sense used by the quotient universal
property. Together with `image_ideal_nsmul`, each new summand of the image is
already an image of one of the old endomorphisms. -/
theorem kills_sat_iff (I : Set (AbVar.End J)) : Kills (Sat I) ν ↔ Kills I ν := by
  constructor
  · intro h t ht
    exact h t ⟨1, one_pos, by simpa using ht⟩
  · rintro h t ⟨m, hm, ht⟩
    have he : comp (m • t) ν = 0 := Hom.ext' (h _ ht)
    have hzero : m • comp t ν = 0 := (map_nsmul (preC ν) m t).symm.trans he
    exact congrArg Hom.hom (hom_nsmul_eq_zero m hm (comp t ν) hzero)

/-- Projection of the annihilator of `f` from the joint Hecke ring acting on
`J` and on the eigenline of `f`. This is used before intersecting the
rational annihilator with `End(J)`, which is `Sat`. -/
def annihilator (S : Subring (AbVar.End J × coeffField f)) : Set (AbVar.End J) :=
  {t | (t, 0) ∈ S}

/-- Shimura's integral Hecke ring and its eigenvalue map, in joint-image form. -/
def printRing (ξ : ℕ → AbVar.End J) (f : CF N 2) :
    Subring (AbVar.End J × coeffField f) :=
  Subring.closure (Set.range fun n : ℕ => (ξ n, ak f n))

/-- The universal property of the printed `J/C` together with the kernel
condition, encoded by the homomorphisms annihilating each summand of `C`.
Here `C` is the sum of the images of the integral endomorphisms in the
rational annihilator, rather than a preselected subgroup scheme of `J`. -/
def PrintQuotient (ξ : ℕ → AbVar.End J) (f : CF N 2) (ν : AbVar.Hom J A) : Prop :=
  Kills (Sat (annihilator (printRing ξ f))) ν ∧
    ∀ (B : AbVar ℚ) (v : AbVar.Hom J B), Kills (Sat (annihilator (printRing ξ f))) v →
      ∃! ψ : AbVar.Hom A B, ν.hom ≫ ψ.hom = v.hom

/-- The coefficients of the original free-algebra evaluation, lifted to `K_f`. -/
def evK (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ) : HeckeFree N →ₐ[ℤ] coeffField f :=
  FreeAlgebra.lift ℤ (Sum.elim (ak f ∘ fun p : Nat.Primes => (p : ℕ)) (dk hN hf))

theorem evK_coe (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ) (w : HeckeFree N) :
    (evK hN hf w : ℂ) = evF χ f w := by
  let e : coeffField f →ₐ[ℤ] ℂ := (coeffField f).val.restrictScalars ℤ
  change (e.comp (evK hN hf)) w = evF χ f w
  congr 1
  apply FreeAlgebra.hom_ext
  funext x
  cases x <;> simp [evF, evK, e, ak, dk]

/-- The kernel's free-algebra joint image is its ring of primes and diamonds. -/
theorem kernel_range (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ) :
    ((heckeJ tp δ).prod (evK hN hf)).range.toSubring =
      Subring.closure (Set.range (fun p : Nat.Primes => (tp p, ak f p)) ∪
        Set.range (fun d : (ZMod N)ˣ => (δ d, dk hN hf d))) := by
  let g : Nat.Primes ⊕ (ZMod N)ˣ → AbVar.End J × coeffField f :=
    Sum.elim (fun p => (tp p, ak f p)) (fun d => (δ d, dk hN hf d))
  have e : (heckeJ tp δ).prod (evK hN hf) = FreeAlgebra.lift ℤ g := by
    apply FreeAlgebra.hom_ext
    funext x
    cases x <;> simp [heckeJ, evK, g]
  rw [e, ← Algebra.adjoin_range_eq_range_freeAlgebra_lift, Algebra.adjoin_eq_ring_closure]
  rw [show Set.range g = _ from Set.Sum.elim_range _ _]
  apply le_antisymm
  · apply Subring.closure_le.mpr
    rintro _ (⟨n, rfl⟩ | h)
    · exact intCast_mem (Subring.closure _) n
    · exact Subring.subset_closure h
  · exact Subring.closure_mono Set.subset_union_right

/-- Before saturation, the two presentations give the same integral
annihilating endomorphisms. -/
theorem print_annihilator_eq (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) :
    annihilator (printRing ξ f) = (heckeJ tp δ) '' {w | evF χ f w = 0} := by
  rw [printRing, closure_eq hN hf h, ← kernel_range (tp := tp) (δ := δ) hN hf]
  ext t
  constructor
  · rintro ⟨w, hw⟩
    have he : evK hN hf w = 0 := congrArg Prod.snd hw
    refine ⟨w, ?_, congrArg Prod.fst hw⟩
    change evF χ f w = 0
    rw [← evK_coe hN hf w, he]
    rfl
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w, Prod.ext rfl ?_⟩
    apply Subtype.ext
    simpa [evK_coe hN hf w] using hw

/-- The summands in Shimura's `C` and in `I_f J) agree as scheme-theoretic
images, so any sum of these images is the same in the two constructions. -/
theorem print_images_eq (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) :
    (fun t : AbVar.End J => t.hom.left.ker) '' Sat (annihilator (printRing ξ f)) =
      (fun t : AbVar.End J => t.hom.left.ker) ''
        ((heckeJ tp δ) '' {w | evF χ f w = 0}) := by
  rw [image_family_sat, print_annihilator_eq hN hf h]

/-- The annihilator in the printed construction and the kernel's `KillsIf`
have exactly the same annihilating maps (step 1). -/
theorem kills_print_iff (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) (ν : AbVar.Hom J A) :
    Kills (Sat (annihilator (printRing ξ f))) ν ↔ KillsIf χ f tp δ ν := by
  rw [kills_sat_iff, print_annihilator_eq hN hf h]
  constructor
  · intro hK w hw
    exact hK _ ⟨w, hw, rfl⟩
  · rintro hK _ ⟨w, hw, rfl⟩
    exact hK w hw

/-- The universal property of Shimura's constructed quotient gives the
kernel's `IsAfQuotient` (step 1). -/
theorem isAfQuotient_of_print (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) (hs : Surjective ν.hom.left) (hQ : PrintQuotient ξ f ν) :
    IsAfQuotient χ f tp δ A ν :=
  ⟨hs, (kills_print_iff hN hf h ν).1 hQ.1, fun _ v hv =>
    hQ.2 _ v ((kills_print_iff hN hf h v).2 hv)⟩

end Quotient

section Compatibility

variable {A : AbVar ℚ} {ν : AbVar.Hom J A} {θ : coeffField f →+* A.End0}

abbrev incl (A : AbVar ℚ) : AbVar.End A →+* A.End0 :=
  (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℚ) (B := AbVar.End A)).toRingHom

theorem compat_zero : HeckeCompat ν 0 0 := by
  refine ⟨1, 0, one_pos, by simp, ?_⟩
  rw [one_nsmul]
  exact (map_zero (preC ν)).trans (map_zero (postC ν)).symm

theorem compat_one : HeckeCompat ν 1 1 := by
  refine ⟨1, 1, one_pos, ?_, ?_⟩
  · change 1 • (1 : A.End0) = incl A 1
    rw [one_smul, map_one]
  · rw [one_nsmul]; exact rel_one ν

theorem common_denominator {E : Type*} [AddCommMonoid E] (m n : ℕ) (u v : E) :
    (m * n) • (u + v) = n • (m • u) + m • (n • v) := by
  rw [nsmul_add, smul_smul, smul_smul, Nat.mul_comm n m]

theorem compat_add {s t : AbVar.End J} {x y : A.End0}
    (hs : HeckeCompat ν s x) (ht : HeckeCompat ν t y) : HeckeCompat ν (s + t) (x + y) := by
  obtain ⟨m, a, hm, hax, ha⟩ := hs
  obtain ⟨n, b, hn, hby, hb⟩ := ht
  change m • x = incl A a at hax
  change n • y = incl A b at hby
  change m • preC ν s = postC ν a at ha
  change n • preC ν t = postC ν b at hb
  refine ⟨m * n, n • a + m • b, Nat.mul_pos hm hn, ?_, ?_⟩
  · change (m * n) • (x + y) = incl A (n • a + m • b)
    rw [common_denominator, map_add, map_nsmul, map_nsmul, hax, hby]
  · change (m * n) • preC ν (s + t) = postC ν (n • a + m • b)
    rw [map_add, common_denominator, map_add, map_nsmul, map_nsmul, ha, hb]

theorem compat_neg {t : AbVar.End J} {x : A.End0}
    (ht : HeckeCompat ν t x) : HeckeCompat ν (-t) (-x) := by
  obtain ⟨m, e, hm, hx, h⟩ := ht
  change m • x = incl A e at hx
  refine ⟨m, -e, hm, ?_, ?_⟩
  · change m • (-x) = incl A (-e)
    rw [smul_neg, hx, map_neg]
  · change m • preC ν (-t) = postC ν (-e)
    rw [map_neg, map_neg, smul_neg]
    exact congrArg Neg.neg h

theorem compat_mul {s t : AbVar.End J} {x y : A.End0}
    (hs : HeckeCompat ν s x) (ht : HeckeCompat ν t y) : HeckeCompat ν (s * t) (x * y) := by
  obtain ⟨m, a, hm, hax, ha⟩ := hs
  obtain ⟨n, b, hn, hby, hb⟩ := ht
  change m • x = incl A a at hax
  change n • y = incl A b at hby
  refine ⟨m * n, a * b, Nat.mul_pos hm hn, ?_, ?_⟩
  · change (m * n) • (x * y) = incl A (a * b)
    rw [map_mul, ← hax, ← hby, smul_mul_smul_comm]
  · have hr := rel_mul (show R16Thm1.Rel ν (m • s) a from (map_nsmul (preC ν) _ _).trans ha)
      (show R16Thm1.Rel ν (n • t) b from (map_nsmul (preC ν) _ _).trans hb)
    change preC ν ((m • s) * (n • t)) = _ at hr
    rw [smul_mul_smul_comm, map_nsmul] at hr
    exact hr

theorem compat_cancel {t : AbVar.End J} {x : A.End0} {n : ℕ} (hn : 0 < n)
    (h : HeckeCompat ν (n • t) (n • x)) : HeckeCompat ν t x := by
  obtain ⟨m, e, hm, hx, he⟩ := h
  change m • preC ν (n • t) = _ at he
  rw [map_nsmul, smul_smul] at he
  exact ⟨m * n, e, Nat.mul_pos hm hn, by simpa only [smul_smul] using hx, he⟩

/-- The pairs that intertwine with `ν` form a subring. -/
def compatRing (ν : AbVar.Hom J A) (θ : coeffField f →+* A.End0) :
    Subring (AbVar.End J × coeffField f) where
  carrier := {te | HeckeCompat ν te.1 (θ te.2)}
  zero_mem' := by change HeckeCompat ν 0 (θ 0); rw [map_zero]; exact compat_zero
  one_mem' := by change HeckeCompat ν 1 (θ 1); rw [map_one]; exact compat_one
  add_mem' := by
    intro a b ha hb
    change HeckeCompat ν (a.1 + b.1) (θ (a.2 + b.2))
    rw [map_add]
    exact compat_add ha hb
  neg_mem' := by
    intro a ha
    change HeckeCompat ν (-a.1) (θ (-a.2))
    rw [map_neg]
    exact compat_neg ha
  mul_mem' := by
    intro a b ha hb
    change HeckeCompat ν (a.1 * b.1) (θ (a.2 * b.2))
    rw [map_mul]
    exact compat_mul ha hb

/-- The prime and good-square cases of (ii) imply the diamond relation, with no
prior quotient property: clear the scalar `p` in the intertwining equation. -/
theorem diamond_compat (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (hcl : ShimuraClauses f tp δ A ν θ) (d : (ZMod N)ˣ) :
    HeckeCompat ν (δ d) (θ (dk hN hf d)) := by
  obtain ⟨p, _, hp, _, _, hd, -⟩ := two_primes hN d
  have hT : (tp p, ak f p) ∈ compatRing ν θ := hcl.2.1.1 p
  have hS : (xiSq tp δ p hp, ak f ((p : ℕ) * p)) ∈ compatRing ν θ := hcl.2.1.2 p hp
  have hsub := (compatRing ν θ).sub_mem ((compatRing ν θ).mul_mem hT hT) hS
  have ha := ak_good hN hf p hp 0
  have ha1 : ak f 1 = 1 := Subtype.ext hf.2.1
  simp only [Nat.zero_add, pow_one, pow_two, pow_zero, ha1, hd, _root_.mul_one] at ha
  change HeckeCompat ν (tp p * tp p - xiSq tp δ p hp)
    (θ (ak f p * ak f p - ak f ((p : ℕ) * p))) at hsub
  rw [ha, xiSq, hd, sub_sub_cancel, sub_sub_cancel, ← nsmul_eq_mul,
    ← nsmul_eq_mul, map_nsmul] at hsub
  exact compat_cancel p.2.pos hsub

/-- Clause (ii) at all positive indices, proved by the good and bad prime-power
recurrences and coprime multiplicativity (step 2). -/
theorem compat_all (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) (hcl : ShimuraClauses f tp δ A ν θ) (n : ℕ) :
    HeckeCompat ν (ξ n) (θ (ak f n)) :=
  xi_mem hN hf h (compatRing ν θ) (hcl.2.1.1) (diamond_compat hN hf hcl) n

theorem incl_eq_zero {e : AbVar.End A} (h : incl A e = 0) : e = 0 := by
  let T : AbVar.End A →ₗ[ℤ] A.End0 := TensorProduct.mk ℤ ℚ (AbVar.End A) 1
  let : IsLocalizedModule (nonZeroDivisors ℤ) T :=
    IsLocalization.tensorProduct_isLocalizedModule (nonZeroDivisors ℤ) ℚ
  have he : T e = T 0 := by
    change incl A e = (1 : ℚ) ⊗ₜ[ℤ] (0 : AbVar.End A)
    rw [TensorProduct.tmul_zero, h]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors ℤ) T).mp he
  change (c : ℤ) • e = (c : ℤ) • (0 : AbVar.End A) at hc
  rw [smul_zero] at hc
  have hn : 0 < (c : ℤ).natAbs :=
    Int.natAbs_pos.mpr (nonZeroDivisors.ne_zero c.property)
  apply hom_nsmul_eq_zero _ hn e
  rw [← natCast_zsmul]
  rcases Int.natAbs_eq (c : ℤ) with h' | h'
  · rwa [← h']
  · have hh := congrArg Neg.neg h'
    rw [neg_neg] at hh
    rw [← hh, neg_smul, hc, neg_zero]

/-- A competitor satisfying (i)–(iii) kills the kernel's annihilator.
In fact its restricted (ii) is sufficient; no geometry of quotients is used. -/
theorem killsIf_of_clauses (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (hcl : ShimuraClauses f tp δ A ν θ) : KillsIf χ f tp δ ν := by
  intro w hw
  have hle : ((heckeJ tp δ).prod (evK hN hf)).range.toSubring ≤ compatRing ν θ := by
    rw [kernel_range hN hf]
    apply Subring.closure_le.mpr
    rintro _ (⟨p, rfl⟩ | ⟨d, rfl⟩)
    · exact hcl.2.1.1 p
    · exact diamond_compat hN hf hcl d
  have hw' : evK hN hf w = 0 := Subtype.ext (by simpa [evK_coe hN hf w] using hw)
  have h : HeckeCompat ν (heckeJ tp δ w) (θ (evK hN hf w)) :=
    hle ⟨w, rfl⟩
  rw [hw', map_zero] at h
  obtain ⟨m, e, hm, he, hc⟩ := h
  have he' : e = 0 := incl_eq_zero (by simpa using he.symm)
  rw [he'] at hc
  have hz : m • comp (heckeJ tp δ w) ν = 0 :=
    hc.trans (map_zero (postC ν))
  exact congrArg Hom.hom (hom_nsmul_eq_zero m hm _ hz)

end Compatibility

/-- The three printed clauses: quotient by a connected kernel, intertwining
at every positive Hecke index, and dimension equal to the coefficient degree. -/
def PrintedClauses (ξ : ℕ → AbVar.End J) (f : CF N 2) {A : AbVar ℚ}
    (ν : AbVar.Hom J A) (θ : coeffField f →+* A.End0) : Prop :=
  (Surjective ν.hom.left ∧ KerConnected ν) ∧
  (∀ n : ℕ, 0 < n → HeckeCompat ν (ξ n) (θ (ak f n))) ∧
  A.dim = ((Module.finrank ℚ (coeffField f) : ℕ) : WithBot ℕ∞)

/-- Restrict the printed (ii) to the prime and good-square tests. -/
theorem clauses_of_printed (h : HeckeRelations tp δ ξ) {A : AbVar ℚ} {ν : AbVar.Hom J A}
    {θ : coeffField f →+* A.End0} (hc : PrintedClauses ξ f ν θ) :
    ShimuraClauses f tp δ A ν θ := by
  refine ⟨hc.1, ⟨?_, ?_⟩, hc.2.2⟩
  · intro p
    change HeckeCompat ν (tp p) (θ (ak f p))
    rw [← h.prime p]
    exact hc.2.1 p p.2.pos
  · intro p hp
    change HeckeCompat ν (xiSq tp δ p hp) (θ (ak f ((p : ℕ) * p)))
    rw [← xi_sq h p hp]
    exact hc.2.1 _ (Nat.mul_pos p.2.pos p.2.pos)

/-- Conversely, the restricted tests give the printed clauses (step 2). -/
theorem printed_of_clauses (hN : 2 ≤ N) (hf : IsNormalizedEigenform f χ)
    (h : HeckeRelations tp δ ξ) {A : AbVar ℚ} {ν : AbVar.Hom J A}
    {θ : coeffField f →+* A.End0} (hc : ShimuraClauses f tp δ A ν θ) :
    PrintedClauses ξ f ν θ :=
  ⟨hc.1, fun n _ => compat_all hN hf h hc n, hc.2.2⟩

/-- Shimura 1973, Theorem 1 and its construction, at `Γ₁(N))
(J. Math. Soc. Japan 25 (1973), 523–544; AI page read pp. 525–527;
manuscript L770–773 and L11053–11057).

* pp. 525–526: the constructed `A = J/C` with `C = ker ν`.
  `PrintQuotient` encodes the quotient through its universal property and
  the family of images defining `C`: use the annihilator of the eigenline,
  intersect the rational ideal with `End(J)`, and sum the images.
* (i) is surjectivity and `KerConnected` (the tree's isogeny criterion for
  a connected kernel); (ii) uses the independent `ξ_n` for every positive
  index and the tree's integral encoding of the rational intertwining;
  (iii) is `dim A = [K_f : ℚ]`, with the printed multiplicity `m = 1`
  from q-expansions (p. 527).
* p. 526: among such triples, the abelian variety is unique up to an
  isomorphism over ℚ; no condition on its composite with `ν` is asserted.

This is the portion of the print used for the quotient row. The cotangent-space
clause (iv) and the total Euler identity are omitted. The existing standard
model interface is retained; the Hecke correspondence dictionary is supplied
separately. The p. 526 misprint in the conjugate-form sentence is recorded in
the report and is outside these clauses. -/
def ShimuraThm1AsPrinted : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 2 ≤ N → IsNewform f χ →
    ∀ (X : Over SpecQ) [IsIntegral X.left] (jX tX : X.left.functionField),
    IsCurve X → IsX1Gen N X jX tX →
    ∀ (P₀ : RatPt X) (J : AbVar ℚ) (aj : X ⟶ J.X), IsJacobian X P₀ J aj →
    ∀ ξ : ℕ → AbVar.End J,
      XiAction (N := N) jX tX aj ξ →
      FiniteDimensional ℚ (coeffField f) ∧
        ∃ (A : AbVar ℚ) (ν : AbVar.Hom J A) (θ : coeffField f →+* A.End0),
          PrintedClauses ξ f ν θ ∧ PrintQuotient ξ f ν ∧
          ∀ (A' : AbVar ℚ) (ν' : AbVar.Hom J A') (θ' : coeffField f →+* A'.End0),
            PrintedClauses ξ f ν' θ' →
              ∃ ψ : AbVar.Hom A A', IsIso ψ.hom

/-- Scoped remaining geometry for step 3: a surjective homomorphism of
equal-dimensional abelian varieties over ℚ is finite (and so is an isogeny).
This is the finite-kernel criterion used in the dimension argument for
Shimura 1973, Thm. 1 (p. 526); treated here as on-the-spot glue. The ordinary
argument uses the dimension of the generic fibre, translation of geometric
fibres, and proper quasi-finite implies finite. It needs no construction of a
new quotient. -/
def SameDimSurjectiveFinite : Prop :=
  ∀ (A A' : AbVar ℚ) (ψ : AbVar.Hom A A'), A.dim = A'.dim →
    Surjective ψ.hom.left → IsFinite ψ.hom.left

/-- The constructed quotient maps to any competitor, whose map kills
`I_f J`. Equal dimensions make the induced map an isogeny under the scoped
geometry input; the competitor's `KerConnected` then makes it an isomorphism. -/
theorem compatible_iso (hfin : SameDimSurjectiveFinite)
    {A A' : AbVar ℚ} {ν : AbVar.Hom J A} {ν' : AbVar.Hom J A'}
    (hQ : IsAfQuotient χ f tp δ A ν) (hK : KillsIf χ f tp δ ν')
    (hs : Surjective ν'.hom.left) (hc : KerConnected ν') (hd : A.dim = A'.dim) :
    ∃ ψ : AbVar.Hom A A', IsIso ψ.hom ∧ ν.hom ≫ ψ.hom = ν'.hom := by
  obtain ⟨ψ, hψ, -⟩ := hQ.2.2 A' ν' hK
  have hsψ : Surjective ψ.hom.left := by
    refine ⟨fun y => ?_⟩
    obtain ⟨x, hx⟩ := hs.surj y
    exact ⟨ν.hom.left x, by simpa only [← Scheme.Hom.comp_apply, ← Over.comp_left, hψ] using hx⟩
  exact ⟨ψ, hc A ν ψ hQ.1 ⟨hfin _ _ ψ hd hsψ, hsψ⟩ hψ, hψ⟩

/-- The existing row follows from the printed construction and the remaining
bridge inputs. The quotient and all Hecke tests are transported in Lean. -/
theorem shimuraThm1Af_of_printed (hP : ShimuraThm1AsPrinted) (hH : ShimuraHeckeRelations)
    (hF : SameDimSurjectiveFinite) : R16Thm1b.ShimuraThm1Af := by
  intro N χ f hN hf X _ jX tX hC hX P₀ J aj hJ tp δ ht hd
  obtain ⟨ξ, hξ, hr⟩ := hH N hN X jX tX hC hX P₀ J aj hJ tp δ ht hd
  obtain ⟨hK, A, ν, θ, hc, hQ, -⟩ := hP N χ f hN hf X jX tX hC hX P₀ J aj hJ ξ hξ
  have hA := isAfQuotient_of_print hN hf.1 hr hc.1.1 hQ
  refine ⟨hK, A, ν, θ, clauses_of_printed hr hc, hA, ?_⟩
  intro A' ν' θ' hc'
  exact compatible_iso hF hA (killsIf_of_clauses hN hf.1 hc') hc'.1.1 hc'.1.2
    (hc.2.2.trans hc'.2.2.symm)

end ShimuraSteps
