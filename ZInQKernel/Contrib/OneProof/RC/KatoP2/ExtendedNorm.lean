import ZInQKernel.Contrib.OneProof.RC.KatoP2.KodaiPrint
import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Print
import ZInQKernel.Contrib.OneProof.RC.AppEK1.Coefficients

/-! The enlarged (K8) system, conditional on the retained construction (K4),
the support-sensitive Prop. 8.12, and the two corestriction laws of (K7)–(K9).
The arithmetic comparison of the abstract cohomology modules is separate. -/

noncomputable section

namespace ZInQ.Manuscript.RC.KatoP2

open PrintsArith Kato812 AppEK1 ZInQ.Contrib.CloudB3RC53

/-- The finite part of the retained 2004 input. No divisibility theorem is a
field. The symbol and lattice are fixed; `c, ds` label the (K5) smoothers. -/
structure RetainedZeta (E : WeierstrassCurve ℚ) (c ds : ℕ) where
  es : EulerSystemData ℤ_[2]
  zAt : ∀ m : ℕ, Finset ℕ → es.H m
  z_spec : ∀ m, zAt m (fixedSupport E ∪ m.primeFactors) = es.z m
  elliptic : E.IsElliptic
  level_pos : 0 < CST.newformLevel E
  cuspForm : CST.HasCuspFormAtLevel E (CST.newformLevel E)
  c_gt_one : 1 < c
  ds_gt_one : 1 < ds
  smooth_coprime_six : Nat.Coprime (c * ds) 6
  smooth_fixed : Nat.Coprime (c * ds) (2 * CST.newformLevel E)

variable {E : WeierstrassCurve ℚ} {c ds : ℕ}

/-- The norm argument of the widened interface, with no Iwasawa fields.
This uses a new copy of the finite argument because the old statement takes
a bundle containing the dyadic 2004 divisibility. -/
theorem retained_norm (Z : RetainedZeta E c ds)
    (h812 : KatoProp812Print E c ds Z.es Z.zAt) {m m' : ℕ}
    (hm : 0 < m) (hm' : 0 < m') (h : m ∣ m')
    (hsmooth : Nat.Coprime m' (c * ds)) :
    Z.es.cor m m' h (Z.es.z m') =
      (∏ q ∈ m'.primeFactors \ (fixedSupport E ∪ m.primeFactors),
        eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit m q)) • Z.es.z m := by
  have hlevels := Nat.primeFactors_mono h hm'.ne'
  have hup : (fixedSupport E ∪ m.primeFactors) ∪ m'.primeFactors ⊆
      fixedSupport E ∪ m'.primeFactors :=
    Finset.union_subset (Finset.union_subset_union Finset.Subset.rfl hlevels)
      Finset.subset_union_right
  have hp : ∀ q ∈ fixedSupport E ∪ m'.primeFactors, Nat.Prime q := by
    intro q hq
    exact (Finset.mem_union.mp hq).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  have rel := h812 Z.elliptic Z.level_pos Z.cuspForm Z.c_gt_one Z.ds_gt_one
    Z.smooth_coprime_six m m' (fixedSupport E ∪ m.primeFactors)
    (fixedSupport E ∪ m'.primeFactors) hm hm' h hp Finset.Subset.rfl hup
    (Finset.disjoint_union_right.mpr
      ⟨Z.smooth_fixed.disjoint_primeFactors, hsmooth.symm.disjoint_primeFactors⟩)
  rw [Z.z_spec, Z.z_spec] at rel
  have hdiff : (fixedSupport E ∪ m'.primeFactors) \ (fixedSupport E ∪ m.primeFactors) =
      m'.primeFactors \ (fixedSupport E ∪ m.primeFactors) := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rwa [hdiff] at rel

/-- The full conductor is always `D = d * 2^a`; the caller uses the full odd
conductor `d = |h|` of its constituent, including primes dividing the form level. -/
abbrev primitiveD (d a : ℕ) : ℕ := d * 2 ^ a

/-- Level in the Kodai input. Its odd support includes the whole odd conductor. -/
abbrev kodaiBase (E : WeierstrassCurve ℚ) (d : ℕ) : ℕ := 2 * CST.newformLevel E * d

/-- The original (K8) domain is a subfamily of the levels prime to the smoothers.
It need not be a subfamily of multiples of `kodaiBase E d`. -/
theorem smoother_coprime_of_katoXi (Z : RetainedZeta E c ds) {d m : ℕ}
    (hm : KatoXi 2 (twistedSigma E d c ds) m) :
    Nat.Coprime m (c * ds) := by
  rw [Nat.coprime_comm, Nat.coprime_iff_gcd_eq_one]
  by_contra h
  obtain ⟨q, hq, hg⟩ := Nat.exists_prime_and_dvd h
  have hqm := hg.trans (Nat.gcd_dvd_right (c * ds) m)
  have hqs := hg.trans (Nat.gcd_dvd_left (c * ds) m)
  have hs : (c * ds) ≠ 0 := Nat.mul_ne_zero
    (by have := Z.c_gt_one; omega) (by have := Z.ds_gt_one; omega)
  have h2 := hm.2.2 q hq hqm
    (Finset.mem_union_left _ (Finset.mem_union_right _ (hq.mem_primeFactors hqs hs)))
  subst q
  have hd := Nat.dvd_gcd hqs (dvd_mul_right 2 (CST.newformLevel E))
  have heq : (c * ds).gcd (2 * CST.newformLevel E) = 1 := Z.smooth_fixed
  rw [heq] at hd
  exact (by decide : ¬ 2 ∣ (1 : ℕ)) hd

/-- A newly introduced prime on the new domain cannot divide `2Nd`. -/
theorem new_prime_not_dvd_base {d m m' q : ℕ} (hm : 0 < m)
    (hbase : kodaiBase E d ∣ m) (hq : q ∈ m'.primeFactors \ m.primeFactors) :
    ¬ q ∣ kodaiBase E d := by
  obtain ⟨hu, hl⟩ := Finset.mem_sdiff.mp hq
  exact fun h => hl ((Nat.prime_of_mem_primeFactors hu).mem_primeFactors
    (h.trans hbase) hm.ne')

/-- The (K4) norm at the levels `D*m` and `D*m'`. Here the fixed support
and `prime(D)` already lie in the lower `prime(m)`. -/
theorem norm_above_kodaiBase (Z : RetainedZeta E c ds)
    (h812 : KatoProp812Print E c ds Z.es Z.zAt) {d a m m' : ℕ}
    (hd : 0 < d) (hD : Nat.Coprime (primitiveD d a) (c * ds))
    (hm : KodaiIndex (kodaiBase E d) (c * ds) m)
    (hm' : KodaiIndex (kodaiBase E d) (c * ds) m') (h : m ∣ m') :
    Z.es.cor _ _ (Nat.mul_dvd_mul_left (primitiveD d a) h)
      (Z.es.z (primitiveD d a * m')) =
      (∏ q ∈ m'.primeFactors \ m.primeFactors,
        eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit (primitiveD d a * m) q)) •
          Z.es.z (primitiveD d a * m) := by
  have hDp : 0 < primitiveD d a := by dsimp [primitiveD]; positivity
  have hs : fixedSupport E ⊆ m.primeFactors :=
    Nat.primeFactors_mono ((dvd_mul_right (2 * CST.newformLevel E) d).trans hm.2.1) hm.1.ne'
  have hds : d.primeFactors ⊆ m.primeFactors :=
    Nat.primeFactors_mono ((dvd_mul_left d (2 * CST.newformLevel E)).trans hm.2.1) hm.1.ne'
  have h₂ : 2 ∈ m.primeFactors := hs (Nat.prime_two.mem_primeFactors (dvd_mul_right _ _)
    (Nat.mul_ne_zero (by decide) Z.level_pos.ne'))
  have hpow : (2 ^ a : ℕ).primeFactors ⊆ m.primeFactors := by
    by_cases ha : a = 0
    · simp [ha]
    · rw [Nat.primeFactors_pow _ ha, Nat.prime_two.primeFactors, Finset.singleton_subset_iff]
      exact h₂
  have hDf : (primitiveD d a).primeFactors ⊆ m.primeFactors := by
    rw [primitiveD, Nat.primeFactors_mul hd.ne' (by positivity)]
    exact Finset.union_subset hds hpow
  have hlow : (primitiveD d a * m).primeFactors = m.primeFactors := by
    rw [Nat.primeFactors_mul hDp.ne' hm.1.ne', Finset.union_eq_right.mpr hDf]
  have hupp : (primitiveD d a * m').primeFactors = m'.primeFactors := by
    rw [Nat.primeFactors_mul hDp.ne' hm'.1.ne',
      Finset.union_eq_right.mpr (hDf.trans (Nat.primeFactors_mono h hm'.1.ne'))]
  simpa only [hlow, hupp, Finset.union_eq_right.mpr hs] using
    retained_norm Z h812 (Nat.mul_pos hDp hm.1) (Nat.mul_pos hDp hm'.1)
      (Nat.mul_dvd_mul_left (primitiveD d a) h) (hD.mul_left hm'.2.2)

/-- Literal tensor by the primitive character line and trace (K8). The two laws
are on all classes, not on zeta classes or their length bounds. -/
structure TwistTransfer (Z : RetainedZeta E c ds) (d a : ℕ) (Y : EulerSystemData ℤ_[2]) where
  χ : (ZMod (primitiveD d a))ˣ →* ℤ_[2]ˣ
  quadratic : ∀ u, χ u * χ u = 1
  trace : ∀ m, Z.es.H (primitiveD d a * m) →+ Y.H m
  z_spec : ∀ m, Y.z m = trace m (Z.es.z (primitiveD d a * m))
  trans : ∀ m m' (h : m ∣ m'),
    (Y.cor m m' h).comp (trace m') =
      (trace m).comp (Z.es.cor _ _ (Nat.mul_dvd_mul_left (primitiveD d a) h))
  equiv : ∀ m r z, trace m (r • z) =
    weightedMap
      (Units.map (ZMod.castHom (dvd_mul_left m (primitiveD d a)) (ZMod m)).toMonoidHom)
      (χ.comp (Units.map (ZMod.castHom (dvd_mul_right (primitiveD d a) m)
        (ZMod (primitiveD d a))).toMonoidHom)) r • trace m z

/-- The polynomial of arithmetic Frobenius on the quadratic twist. The value
at zero or at a prime of the conductor is unused. -/
def twistedPoly {D : ℕ} (E : WeierstrassCurve ℚ)
    (χ : (ZMod D)ˣ →* ℤ_[2]ˣ) (q : ℕ) : Polynomial ℤ_[2] :=
  1 - Polynomial.C (((E.LFunction q : ℤ) : ℤ_[2]) * (χ (frobUnit D q) : ℤ_[2])) *
    Polynomial.X + Polynomial.C (q : ℤ_[2]) * Polynomial.X ^ 2

/-- At a new good prime, reduction of the upper arithmetic Frobenius to
either the lower level or the character conductor is arithmetic Frobenius. -/
theorem map_frobUnit {m n q : ℕ} (h : m ∣ n) (hq : Nat.Coprime q n) :
    Units.map (ZMod.castHom h (ZMod m)).toMonoidHom (frobUnit n q) = frobUnit m q := by
  have hm := hq.coprime_dvd_right h
  rw [frobUnit, dite_eq_left hq, frobUnit, dite_eq_left hm]
  apply Units.ext
  simp

/-- Weighted transfer changes the linear coefficient by `χ(q)` and leaves
the top coefficient unchanged. The proof works directly on the polynomial
under the integral group basis map. -/
theorem weightedEuler {D m : ℕ} (χ : (ZMod D)ˣ →* ℤ_[2]ˣ)
    (hχ : ∀ u, χ u * χ u = 1) (q : ℕ) (hq : Nat.Coprime q (D * m)) :
    weightedMap
      (Units.map (ZMod.castHom (dvd_mul_left m D) (ZMod m)).toMonoidHom)
      (χ.comp (Units.map (ZMod.castHom (dvd_mul_right D m) (ZMod D)).toMonoidHom))
      (eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit (D * m) q)) =
      eulerFactor (twistedPoly E χ q) (invNat ℤ_[2] q) (frobUnit m q) := by
  classical
  simp only [eulerFactor, map_sum, weightedMap_single, map_pow, map_inv,
    MonoidHom.comp_apply, map_frobUnit (dvd_mul_left m D) hq,
    map_frobUnit (dvd_mul_right D m) hq]
  rw [inv_eq_of_mul_eq_one_right (hχ (frobUnit D q))]
  have hcoeff (i : ℕ) : (twistedPoly E χ q).coeff i =
      (katoP E q).coeff i * (↑(χ (frobUnit D q)) : ℤ_[2]) ^ i := by
    have hs : (↑(χ (frobUnit D q)) : ℤ_[2]) ^ 2 = 1 := by
      rw [pow_two, ← Units.val_mul, hχ, Units.val_one]
    simp only [twistedPoly, katoP, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_one]
    rcases i with _ | _ | _ | i <;> simp [hs]
  have hsupp : (twistedPoly E χ q).support = (katoP E q).support := by
    ext i
    simp only [Polynomial.mem_support_iff, hcoeff, mul_ne_zero_iff, ne_eq,
      pow_eq_zero_iff', Units.ne_zero, false_and, not_false_eq_true, and_true]
  rw [hsupp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoeff, Units.val_pow_eq_pow_val]
  ac_rfl

/-- The complete transition formula (0.1.1) on the enlarged domain. -/
theorem kodaiNorm_of_prop812 (Z : RetainedZeta E c ds)
    (h812 : KatoProp812Print E c ds Z.es Z.zAt) {d a : ℕ} {Y : EulerSystemData ℤ_[2]}
    (T : TwistTransfer Z d a Y) (hd : 0 < d)
    (hD : Nat.Coprime (primitiveD d a) (c * ds)) :
    KodaiNorm Y (kodaiBase E d) (c * ds) (twistedPoly E T.χ) := by
  intro m m' hm hm' h
  have ht := DFunLike.congr_fun (T.trans m m' h) (Z.es.z (primitiveD d a * m'))
  simp only [AddMonoidHom.comp_apply] at ht
  rw [T.z_spec m', ht, norm_above_kodaiBase Z h812 hd hD hm hm' h, T.equiv, map_prod, ← T.z_spec]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  apply weightedEuler T.χ T.quadratic
  have hqp := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hq).1
  have hqm : ¬ q ∣ m :=
    fun hq' => (Finset.mem_sdiff.mp hq).2 (hqp.mem_primeFactors hq' hm.1.ne')
  have hqb := new_prime_not_dvd_base (E := E) hm.1 hm.2.1 hq
  have hqD : ¬ q ∣ primitiveD d a := by
    intro h
    rcases hqp.dvd_mul.mp h with h | h
    · exact hqb (h.trans (dvd_mul_left _ _))
    · exact hqb ((hqp.dvd_of_dvd_pow h).trans
        ((dvd_mul_right 2 _).trans (dvd_mul_right _ _)))
  exact (hqp.coprime_iff_not_dvd.mpr hqD).mul_right (hqp.coprime_iff_not_dvd.mpr hqm)

/-- Prime steps: a repeated prime gives norm multiplier one; a new prime
gives the single twisted factor and is prime to the form level and conductor. -/
theorem kodaiNorm_prime {Y : EulerSystemData ℤ_[2]} {NK Np : ℕ}
    {P : ℕ → Polynomial ℤ_[2]} (hY : KodaiNorm Y NK Np P) {m q : ℕ}
    (hm : KodaiIndex NK Np m) (hmq : KodaiIndex NK Np (m * q)) (hq : q.Prime) :
    Y.cor m (m * q) (dvd_mul_right m q) (Y.z (m * q)) =
      if q ∣ m then Y.z m else eulerFactor (P q) (invNat ℤ_[2] q) (frobUnit m q) • Y.z m := by
  classical
  have hdiff : (m * q).primeFactors \ m.primeFactors = if q ∣ m then ∅ else {q} := by
    rw [Nat.primeFactors_mul hm.1.ne' hq.ne_zero, hq.primeFactors]
    ext r
    by_cases hr : r = q
    · subst r
      by_cases h : q ∣ m <;> simp [h, hm.1.ne', hq]
    · by_cases hh : q ∣ m <;>
        simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, hr, or_false,
          hh, ↓reduceIte, Finset.notMem_empty, and_not_self]
  rw [hY _ _ hm hmq _, hdiff]
  split_ifs <;> simp

end ZInQ.Manuscript.RC.KatoP2
