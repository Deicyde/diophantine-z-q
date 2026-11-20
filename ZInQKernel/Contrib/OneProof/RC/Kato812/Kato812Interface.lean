import ZInQKernel.Contrib.OneProof.RC.Kato812.Kato812Print

/-!
# Widened retained Kato interface and restriction to the old range

The other fields are those of the old interface. The smoothers label the retained
classes in this witness; the fixed reciprocity scalar is left as in the old interface.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Kato812

open PrintsArith ZInQ.Contrib.CloudB3RC53

/-- The support-dependent norm replaces the old restricted Euler-system field.
`es.z m` is the retained class for the support `Sbad ∪ prime(m)`. -/
structure KatoZetaInterface812 (E : WeierstrassCurve ℚ) (c ds : ℕ) (Sbad : Finset ℕ) where
  es : EulerSystemData ℤ_[2]
  zAt : ∀ m : ℕ, Finset ℕ → es.H m
  z_spec : ∀ m, zAt m (Sbad ∪ m.primeFactors) = es.z m
  elliptic : E.IsElliptic
  level_pos : 0 < CST.newformLevel E
  cuspForm : CST.HasCuspFormAtLevel E (CST.newformLevel E)
  c_gt_one : 1 < c
  ds_gt_one : 1 < ds
  smooth_coprime_six : Nat.Coprime (c * ds) 6
  bad_primes : ∀ q ∈ Sbad, Nat.Prime q
  fixed_subset : fixedSupport E ⊆ Sbad
  smooth_bad : Disjoint (c * ds).primeFactors Sbad
  es_812 : KatoProp812Print E c ds es zAt
  iw : IwasawaData KatoLambda2
  proj : ∀ n : ℕ, iw.H1 →+ es.H (2 ^ n)
  iw_z : ∀ n : ℕ, proj n iw.zIw = es.z (2 ^ n)
  iw_thm13_4 : iw.Thm13_4Conclusion 2
  per : ∀ m, es.H m →+ ℂ
  s : ℂ
  s_ne_zero : s ≠ 0
  b : ∀ {m : ℕ}, DirichletCharacter ℂ m → ℂ
  b_ne_zero : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m), b χ ≠ 0
  Lcont : ∀ {m : ℕ}, DirichletCharacter ℂ m → ℂ → ℂ
  Lcont_entire : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m), Differentiable ℂ (Lcont χ)
  Lcont_eq : ∀ {m : ℕ} (χ : DirichletCharacter ℂ m) (s : ℂ), 3 / 2 < s.re →
    Lcont χ s = LSeries (twistedCoeffS E (Sbad ∪ m.primeFactors) χ) s
  recip : ∀ (m : ℕ) [NeZero m], KatoXi 2 (oldSigma Sbad c ds) m →
    ∀ χ : DirichletCharacter ℂ m,
    ∑ g : (ZMod m)ˣ, χ (g : ZMod m) * per m (MonoidAlgebra.of ℤ_[2] (ZMod m)ˣ g • es.z m) =
      s * b χ * Lcont χ 1

namespace KatoZetaInterface812

variable {E : WeierstrassCurve ℚ} {c ds : ℕ} {Sbad : Finset ℕ}
    (K : KatoZetaInterface812 E c ds Sbad)

/-- The full divisibility norm for the retained classes. Cyclotomic levels may
contain primes of `Sbad`; those primes are already in the lower support.
Only primes of the smoothers are excluded from the upper level. -/
theorem norm {m m' : ℕ} (hm : 0 < m) (hm' : 0 < m') (h : m ∣ m')
    (hsmooth : Disjoint (c * ds).primeFactors m'.primeFactors) :
    K.es.cor m m' h (K.es.z m') =
      (∏ q ∈ m'.primeFactors \ (Sbad ∪ m.primeFactors),
        eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit m q)) • K.es.z m := by
  have hlevels := Nat.primeFactors_mono h hm'.ne'
  have h₁ : fixedSupport E ∪ m.primeFactors ⊆ Sbad ∪ m.primeFactors :=
    Finset.union_subset_union K.fixed_subset Finset.Subset.rfl
  have h₂ : (Sbad ∪ m.primeFactors) ∪ m'.primeFactors ⊆ Sbad ∪ m'.primeFactors :=
    Finset.union_subset (Finset.union_subset_union Finset.Subset.rfl hlevels)
      (Finset.subset_union_right)
  have hp : ∀ q ∈ Sbad ∪ m'.primeFactors, Nat.Prime q := by
    intro q hq
    exact (Finset.mem_union.mp hq).elim (K.bad_primes q) Nat.prime_of_mem_primeFactors
  have rel := K.es_812 K.elliptic K.level_pos K.cuspForm K.c_gt_one K.ds_gt_one
    K.smooth_coprime_six m m'
    (Sbad ∪ m.primeFactors) (Sbad ∪ m'.primeFactors) hm hm' h hp h₁ h₂
    (Finset.disjoint_union_right.mpr ⟨K.smooth_bad, hsmooth⟩)
  rw [K.z_spec, K.z_spec] at rel
  have hdiff : (Sbad ∪ m'.primeFactors) \ (Sbad ∪ m.primeFactors) =
      m'.primeFactors \ (Sbad ∪ m.primeFactors) := by
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rwa [hdiff] at rel

/-- For a one-prime step, a repeated prime and a prime already in the fixed
omitted support both give the identity multiplier. A prime in neither gives
one good Euler factor. -/
theorem norm_mul_prime {m q : ℕ} (hm : 0 < m) (hq : q.Prime)
    (hsmooth : Disjoint (c * ds).primeFactors (m * q).primeFactors) :
    K.es.cor m (m * q) (dvd_mul_right m q) (K.es.z (m * q)) =
      (if q ∣ m ∨ q ∈ Sbad then 1
        else eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit m q)) • K.es.z m := by
  classical
  have hM := K.norm hm (Nat.mul_pos hm hq.pos) (dvd_mul_right m q) hsmooth
  have hdiff : (m * q).primeFactors \ (Sbad ∪ m.primeFactors) =
      if q ∣ m ∨ q ∈ Sbad then ∅ else {q} := by
    rw [Nat.primeFactors_mul hm.ne' hq.ne_zero, hq.primeFactors]
    ext r
    by_cases hr : r = q
    · subst r
      by_cases hh : q ∣ m ∨ q ∈ Sbad <;>
        simp [hh, hm.ne', hq] <;> tauto
    · by_cases hh : q ∣ m ∨ q ∈ Sbad <;> simp [hh, hr] <;> tauto
  rw [hdiff] at hM
  split_ifs at hM ⊢ <;> simpa only [Finset.prod_empty, Finset.prod_singleton] using hM

include K in
theorem two_mem_bad : 2 ∈ Sbad :=
  K.fixed_subset (Nat.prime_two.mem_primeFactors (dvd_mul_right _ _)
    (Nat.mul_ne_zero (by decide) K.level_pos.ne'))

include K in
/-- A level in an old exclusion range has no smoother primes. -/
theorem smooth_disjoint_of_katoXi {Sig : Finset ℕ} {m : ℕ}
    (hSig : oldSigma Sbad c ds ⊆ Sig) (hm : KatoXi 2 Sig m) :
    Disjoint (c * ds).primeFactors m.primeFactors := by
  rw [Finset.disjoint_left]
  intro q hqs hq
  have h₂ := hm.2.2 q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
    (hSig (Finset.mem_union_right _ hqs))
  subst q
  exact Finset.disjoint_left.mp K.smooth_bad hqs K.two_mem_bad

/-- Restricting the printed norm to the old indices recovers the full old
Euler-system relation for any superset of the old exclusions. -/
theorem isEulerSystem {Sig : Finset ℕ} (hSig : oldSigma Sbad c ds ⊆ Sig) :
    K.es.IsEulerSystem 2 Sig (katoP E) := by
  intro m m' hm hm' h
  have hmpos : 0 < m := hm.1
  have h₂ : 2 ∈ m.primeFactors := Nat.prime_two.mem_primeFactors hm.2.1 hmpos.ne'
  have hdiff : m'.primeFactors \ (Sbad ∪ m.primeFactors) =
      m'.primeFactors \ m.primeFactors := by
    apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨hqm', hq_not⟩ := Finset.mem_sdiff.mp hq
      exact Finset.mem_sdiff.mpr ⟨hqm', fun hq => hq_not (Finset.mem_union_right _ hq)⟩
    · intro q hq
      obtain ⟨hqm', hqm⟩ := Finset.mem_sdiff.mp hq
      refine Finset.mem_sdiff.mpr ⟨hqm', ?_⟩
      intro hq
      rcases Finset.mem_union.mp hq with hqb | hq
      · have hq₂ := hm'.2.2 q (Nat.prime_of_mem_primeFactors hqm')
          (Nat.dvd_of_mem_primeFactors hqm') (hSig (Finset.mem_union_left _ hqb))
        exact hqm (hq₂.symm ▸ h₂)
      · exact hqm hq
  simpa only [hdiff] using K.norm hmpos hm'.1 h (K.smooth_disjoint_of_katoXi hSig hm')

/-- Recover the old bundle with the same classes, corestrictions, periods and
Iwasawa data, on any `Sig` containing its standard exclusions. -/
def toOld {Sig : Finset ℕ} (hSig : oldSigma Sbad c ds ⊆ Sig) :
    KatoZetaInterface E Sig Sbad where
  es := K.es
  es_euler := K.isEulerSystem hSig
  iw := K.iw
  proj := K.proj
  iw_z := K.iw_z
  iw_thm13_4 := K.iw_thm13_4
  per := K.per
  s := K.s
  s_ne_zero := K.s_ne_zero
  b := K.b
  b_ne_zero := K.b_ne_zero
  Lcont := K.Lcont
  Lcont_entire := K.Lcont_entire
  Lcont_eq := K.Lcont_eq
  recip := by
    intro m _ hm χ
    exact K.recip m ⟨hm.1, hm.2.1, fun q hq hqm hqSig => hm.2.2 q hq hqm (hSig hqSig)⟩ χ

end KatoZetaInterface812

/-- The untwisted norm at the levels in (K8). Both levels include the full
primitive conductor `D = d * 2^a`. Its odd part `d` must avoid the smoothers,
but can share primes with the form level. -/
theorem norm_at_twisted_indices {E : WeierstrassCurve ℚ} {c ds d a m m' : ℕ}
    (K : KatoZetaInterface812 E c ds (fixedSupport E))
    (hd : d ≠ 0) (hsd : Disjoint (c * ds).primeFactors d.primeFactors)
    (hm : KatoXi 2 (twistedSigma E d c ds) m)
    (hm' : KatoXi 2 (twistedSigma E d c ds) m') (h : m ∣ m') :
    K.es.cor (d * 2 ^ a * m) (d * 2 ^ a * m') (Nat.mul_dvd_mul_left _ h)
      (K.es.z (d * 2 ^ a * m')) =
      (∏ q ∈ m'.primeFactors \ m.primeFactors,
        eulerFactor (katoP E q) (invNat ℤ_[2] q) (frobUnit (d * 2 ^ a * m) q)) •
        K.es.z (d * 2 ^ a * m) := by
  have hprime {k : ℕ} (hk : 0 < k) (h2k : 2 ∣ k) :
      (d * 2 ^ a * k).primeFactors = d.primeFactors ∪ k.primeFactors := by
    have hpow : (2 ^ a : ℕ).primeFactors ⊆ k.primeFactors := by
      by_cases ha : a = 0
      · simp [ha]
      · rw [Nat.primeFactors_pow _ ha, Nat.prime_two.primeFactors, Finset.singleton_subset_iff]
        exact Nat.prime_two.mem_primeFactors h2k hk.ne'
    rw [mul_assoc, Nat.primeFactors_mul hd (by positivity),
      Nat.primeFactors_mul (by positivity) hk.ne', Finset.union_eq_right.mpr hpow]
  have hmpos : 0 < m := hm.1
  have hm'pos : 0 < m' := hm'.1
  have hL := hprime hmpos hm.2.1
  have hU := hprime hm'pos hm'.2.1
  have hsmooth : Disjoint (c * ds).primeFactors (d * 2 ^ a * m').primeFactors := by
    rw [hU, Finset.disjoint_union_right]
    exact ⟨hsd, K.smooth_disjoint_of_katoXi Finset.subset_union_left hm'⟩
  have hnorm := K.norm (by positivity : 0 < d * 2 ^ a * m) (by positivity)
    (Nat.mul_dvd_mul_left (d * 2 ^ a) h) hsmooth
  have hdiff : (d * 2 ^ a * m').primeFactors \ (fixedSupport E ∪ (d * 2 ^ a * m).primeFactors) =
      m'.primeFactors \ m.primeFactors := by
    rw [hL, hU]
    ext q
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · tauto
    · rintro ⟨hq, hqnot⟩
      refine ⟨Or.inr hq, ?_⟩
      rintro (hqN | hqd | hqm)
      · have hq₂ := hm'.2.2 q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
          (Finset.mem_union_left _ (Finset.mem_union_left _ hqN))
        exact hqnot (hq₂.symm ▸ Nat.prime_two.mem_primeFactors hm.2.1 hmpos.ne')
      · have hq₂ := hm'.2.2 q (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq)
          (Finset.mem_union_right _ hqd)
        exact hqnot (hq₂.symm ▸ Nat.prime_two.mem_primeFactors hm.2.1 hmpos.ne')
      · exact hqnot hqm
  simpa only [hdiff] using hnorm

end ZInQ.Manuscript.RC.Kato812
