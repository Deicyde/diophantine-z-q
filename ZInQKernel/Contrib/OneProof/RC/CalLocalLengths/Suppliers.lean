import ZInQKernel.Contrib.OneProof.RC.CalLocalLengths.Calibration
import ZInQKernel.Contrib.OneProof.RC.TateWiring.Kummer
import ZInQKernel.Contrib.OneProof.RC.KSplit.Ap
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Chebotarev
import ZInQKernel.Contrib.RC53Assist.StrictSymmFull.LocalContractions
import ZInQKernel.Contrib.RC53Assist.DivisionPoints.Support
import ZInQKernel.Contrib.RC53Assist.FrobeniusMatch.Arithmetic
import ZInQKernel.Contrib.TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic

/-!
Suppliers for the active inertia and moving Frobenius facts (tex 2720–2723,
3686–3691, 4032–4036, 4066–4080). No additional printed statement is used.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open NumberField IsDedekindDomain Matrix TauCeti ValuativeRel
open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.DivisionPoints ZInQ.Manuscript.RC.KummerMaps
open ZInQ.Manuscript.RC.TateWiring
open ZInQ.Manuscript.RC.PrintsArith (Qbar)
open ZInQ.Contrib.CloudB3RC53.RankCounts (resAbs_apply_coe)
open ZInQ.Contrib.CloudB3RC53 (Ecurve)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.RC53Assist.StrictSymmFull.LocalContractions
open ZInQ.Contrib.RC53Assist.FrobeniusMatch

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {s : KS K S} {h : K} {hs : s ^ 2 = algebraMap K (KS K S) h} {hs0 : s ≠ 0}

/-- At a good odd place, the vendored good-reduction results imply trivial inertia on every
untwisted coefficient level: take the smaller support consisting of primes above two and
places of bad reduction. -/
theorem localUnramifiedTorsion_of_goodReduction (W : WeierstrassCurve K) [W.IsElliptic]
    (v : Places K S) (h2 : (2 : 𝓞 K) ∉ v.1.asIdeal) (hGood : HasGoodReductionAt W v.1) :
    LocalUnramifiedTorsion W v := by
  classical
  let S₀ : Set (HeightOneSpectrum (𝓞 K)) :=
    {u | (2 : 𝓞 K) ∈ u.asIdeal ∨ ¬ HasGoodReductionAt W u}
  have hv : v.1 ∉ S₀ := fun hv => hv.elim h2 (fun hn => hn hGood)
  intro σ hσ i P
  have hσI : σ ∈ TauCeti.inertiaSubgroup (v.1.adicCompletion K) := by
    rw [← TauCeti.ker_restrictMaximalUnramifiedHom]
    exact hσ
  let _ : NeZero (2 ^ i : ℕ) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hFull : FullTorsion K S₀ W (2 ^ i) := fullTorsion_of_goodReduction W
    (pow_ne_zero _ two_ne_zero)
    (fun _ hu => Or.inl (natCast_mem_of_two_pow hu))
    (fun u hu => not_not.mp (fun hn => hu (Or.inr hn)))
  exact torsion_fixed_outside_coefficient_support W (2 ^ i) hFull v.1 hv σ hσI P

/-- An odd good place with valuation-one radicand supplies the active action, including the
quadratic sign of a genuine inertia element. -/
theorem activeLocalAction_of_goodReduction (W : WeierstrassCurve K) [W.IsElliptic]
    (v : Places K S) (h2 : (2 : 𝓞 K) ∉ v.1.asIdeal) (hGood : HasGoodReductionAt W v.1)
    (hh0 : algebraMap K (v.1.adicCompletion K) h ≠ 0)
    (hv : (normalizedValuation (v.1.adicCompletion K)
      (Units.mk0 (algebraMap K (v.1.adicCompletion K) h) hh0)).toAdd = 1) :
    ActiveLocalAction W s hs hs0 v := by
  have hp := CharP.prime_ringChar 𝓀[v.1.adicCompletion K]
  have hnd : ¬ ringChar 𝓀[v.1.adicCompletion K] ∣ 2 := by
    rw [HeightOneSpectrum.ringChar_residueField_adicCompletion_dvd_iff]
    exact_mod_cast h2
  have hodd := (hp.coprime_iff_not_dvd.mpr hnd).symm
  obtain ⟨σ, hσI, hsign⟩ := exists_actual_primitive_inertia s hs hs0 v hodd hh0 hv
  exact ⟨σ, urRes_inertia_one v σ hσI, hsign,
    localUnramifiedTorsion_of_goodReduction W v h2 hGood σ (urRes_inertia_one v σ hσI)⟩

omit [NumberField K] in
private theorem prime_under_of_above (v : Places K S) {r : ℕ} (hr : r.Prime)
    (hAbove : (r : 𝓞 K) ∈ v.1.asIdeal) :
    v.1.asIdeal.under ℤ = Ideal.span {(r : ℤ)} := by
  let _ : Fact r.Prime := ⟨hr⟩
  symm
  apply (Int.ideal_span_isMaximal_of_prime r).eq_of_le
    (Ideal.comap_ne_top _ v.1.isPrime.ne_top)
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_under]
  simpa using hAbove

private theorem ncard_primesOver_eq_of_two_places [Algebra.IsQuadraticExtension ℚ K]
    {r : ℕ} (hr : r.Prime) (v w : Places K S) (hne : v ≠ w)
    (hv : (r : 𝓞 K) ∈ v.1.asIdeal) (hw : (r : 𝓞 K) ∈ w.1.asIdeal) :
    ((Ideal.span {(r : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K := by
  let _ : Fact r.Prime := ⟨hr⟩
  let p : Ideal ℤ := Ideal.span {(r : ℤ)}
  let _ : p.IsPrime := (Int.ideal_span_isMaximal_of_prime r).isPrime
  let _ : v.1.asIdeal.LiesOver p := ⟨(prime_under_of_above v hr hv).symm⟩
  let _ : w.1.asIdeal.LiesOver p := ⟨(prime_under_of_above w hr hw).symm⟩
  have hI : v.1.asIdeal ≠ w.1.asIdeal := fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  have hl : 2 ≤ (p.primesOver (𝓞 K)).ncard := by
    have hs : ({v.1.asIdeal, w.1.asIdeal} : Set (Ideal (𝓞 K))) ⊆ p.primesOver (𝓞 K) :=
      Set.insert_subset_iff.mpr ⟨⟨inferInstance, inferInstance⟩,
        Set.singleton_subset_iff.mpr ⟨inferInstance, inferInstance⟩⟩
    simpa only [Set.ncard_pair hI] using Set.ncard_le_ncard hs
      (Algebra.QuasiFinite.finite_primesOver p)
  have hu := TauCeti.RamificationInertia.ncard_primesOver_le_finrank (S := 𝓞 K) p
  rw [NumberField.RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two ℚ K] at hu
  rw [Algebra.IsQuadraticExtension.finrank_eq_two ℚ K]
  exact le_antisymm hu hl

/-- At a split prime of the quadratic field both places have residue degree one. -/
theorem movingPrime_absNorm_of_two_places [Algebra.IsQuadraticExtension ℚ K]
    {r : ℕ} (hr : r.Prime) (v w : Places K S) (hne : v ≠ w)
    (hv : (r : 𝓞 K) ∈ v.1.asIdeal) (hw : (r : 𝓞 K) ∈ w.1.asIdeal) :
    v.1.asIdeal.absNorm = r := by
  let _ : Fact r.Prime := ⟨hr⟩
  let _ : v.1.asIdeal.LiesOver (Ideal.span {(r : ℤ)}) :=
    ⟨(prime_under_of_above v hr hv).symm⟩
  exact Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank v.1.asIdeal
    (ncard_primesOver_eq_of_two_places hr v w hne hv hw)

/-- At an active split odd prime dividing a squarefree radicand, the local valuation is one.
Together with good reduction, this supplies the sign-negative inertia action. -/
theorem activeLocalAction_of_split_squarefree [Algebra.IsQuadraticExtension ℚ K]
    (W : WeierstrassCurve K) [W.IsElliptic] {hZ : ℤ}
    {hs : s ^ 2 = algebraMap K (KS K S) (hZ : K)}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (v w : Places K S) (hne : v ≠ w)
    (hv : (p : 𝓞 K) ∈ v.1.asIdeal) (hw : (p : 𝓞 K) ∈ w.1.asIdeal)
    (hGood : HasGoodReductionAt W v.1) (hsq : Squarefree hZ) (hd : (p : ℤ) ∣ hZ) :
    ActiveLocalAction W s hs hs0 v := by
  let _ : Fact p.Prime := ⟨hp⟩
  let P : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hP := prime_under_of_above v hp hv
  let _ : v.1.asIdeal.LiesOver P := ⟨hP.symm⟩
  have hsplit := ncard_primesOver_eq_of_two_places hp v w hne hv hw
  have he : v.1.asIdeal.ramificationIdx ℤ = 1 :=
    (TauCeti.RamificationInertia.ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
      P v.1.asIdeal (by rwa [NumberField.RingOfIntegers.rank])).1
  have hmem (n : ℤ) : (n : 𝓞 K) ∈ v.1.asIdeal ↔ (p : ℤ) ∣ n := by
    change n ∈ v.1.asIdeal.under ℤ ↔ _
    rw [hP, Ideal.mem_span_singleton]
  have h2 : (2 : 𝓞 K) ∉ v.1.asIdeal := by
    intro h2
    have hd2 : p ∣ 2 := by exact_mod_cast (hmem 2).1 (by simpa using h2)
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hd2 |>.resolve_left hp.ne_one)
  obtain ⟨b, hb⟩ := hd
  have hpb : ¬ (p : ℤ) ∣ b := by
    intro hpb
    apply (Int.prime_iff_natAbs_prime.mpr (by simpa using hp) : Prime (p : ℤ)).not_isUnit
    exact hsq _ (hb.symm ▸ (mul_dvd_mul_left (p : ℤ) hpb))
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmap : P.map (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : 𝓞 K)} := by
    rw [show P = Ideal.span {(p : ℤ)} by rfl, Ideal.map_span, Set.image_singleton]
    simp
  have hpm := Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity P v.1.asIdeal
    (by rw [hmap]; exact fun heq => hp0 (Ideal.span_singleton_eq_bot.mp heq))
  rw [he, hmap] at hpm
  have hvp : v.1.intValuation (p : 𝓞 K) = WithZero.exp (-1) := by
    rw [v.1.intValuation_eq_exp_neg_multiplicity hp0, ← hpm]
    rfl
  have hvb : v.1.intValuation (b : 𝓞 K) = 1 :=
    HeightOneSpectrum.intValuation_eq_one_iff.mpr (fun h => hpb ((hmem b).mp h))
  have hhval : v.1.valuation K (hZ : K) = WithZero.exp (-1) := by
    rw [← show algebraMap (𝓞 K) K (hZ : 𝓞 K) = (hZ : K) by simp,
      v.1.valuation_of_algebraMap, hb, Int.cast_mul, Int.cast_natCast, map_mul, hvp, hvb, mul_one]
  have h0 : (hZ : K) ≠ 0 := Int.cast_ne_zero.mpr hsq.ne_zero
  have hh0 : algebraMap K (v.1.adicCompletion K) (hZ : K) ≠ 0 :=
    (map_ne_zero_iff (algebraMap K (v.1.adicCompletion K)) (algebraMap K _).injective).2 h0
  refine activeLocalAction_of_goodReduction W v h2 hGood hh0 ?_
  have hh := v.1.coe_normalizedValuation_unitsMap_algebraMap (K := K) (Units.mk0 (hZ : K) h0)
  change (normalizedValuation (v.1.adicCompletion K)
    (Units.mk0 (algebraMap K (v.1.adicCompletion K) (hZ : K)) hh0) : WithZero (Multiplicative ℤ)) =
      (v.1.valuation K (hZ : K))⁻¹ at hh
  rw [hhval, ← WithZero.exp_neg, neg_neg, WithZero.exp_eq_coe_ofAdd, WithZero.coe_inj] at hh
  exact congrArg Multiplicative.toAdd hh

/-- An arithmetic Frobenius of the chosen degree-one place is a rational arithmetic
Frobenius under the actual decomposition embedding. Transfer the congruence at the
decomposition prime through the ring-of-integers equivalence. -/
theorem moving_isFrobAt_of_residueDegreeOne (v : Places K S) {r : ℕ} (hr : r.Prime)
    (hAbove : (r : 𝓞 K) ∈ v.1.asIdeal) (hNorm : v.1.asIdeal.absNorm = r)
    (φ : Gloc K v.1) (hφ : urRes K v.1 φ = frobElt (eUr K v.1)) :
    ZInQ.Contrib.ChebFD.C10.IsFrobAt (tateGalToQ (tateAlgEquiv K) (decompMap K v.1 φ)) r := by
  let e := tateAlgEquiv K
  let τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := decompMap K v.1 φ
  let eZ := integersEquiv e
  let P := localPrime v.1
  let Q : Ideal ZInQ.Contrib.ChebFD.C10.Zbar := P.comap eZ.symm.toRingHom
  have hφ' : IsArithFrobeniusLift (v.1.adicCompletion K) φ := by
    rw [isArithFrobeniusLift_def, ← frobElt_eUr K v.1]
    exact hφ
  have hF : IsArithFrobAt (𝓞 K) τ P := decompMap_isArithFrobAt v.1 φ hφ'
  refine ⟨Q, Ideal.comap_isPrime _ _, ?_, ?_⟩
  · have hQP : Q.under ℤ = P.under ℤ := by
      ext n
      rw [Ideal.mem_under, Ideal.mem_under, Ideal.mem_comap]
      change eZ.symm (n : ZInQ.Contrib.ChebFD.C10.Zbar) ∈ P ↔
        (n : 𝓞 (AlgebraicClosure K)) ∈ P
      rw [map_intCast]
    rw [hQP, ← Ideal.under_under (B := 𝓞 K), show P.under (𝓞 K) = v.1.asIdeal from
      localPrime_under v.1, prime_under_of_above v hr hAbove]
  · intro x y hxy
    have hf := hF (eZ.symm x)
    change τ • eZ.symm x - (eZ.symm x) ^ Nat.card (𝓞 K ⧸ P.under (𝓞 K)) ∈ P at hf
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hNorm
    rw [show P.under (𝓞 K) = v.1.asIdeal from localPrime_under v.1, hNorm] at hf
    change eZ.symm y ∈ P
    suffices he : eZ.symm y = τ • eZ.symm x - (eZ.symm x) ^ r by rwa [he]
    apply RingOfIntegers.ext
    apply e.injective
    change e (e.symm (y : Qbar)) = e (τ (e.symm (x : Qbar)) - (e.symm (x : Qbar)) ^ r)
    rw [map_sub, map_pow, ← tateGalToQ_apply_e e τ, e.apply_symm_apply, e.apply_symm_apply]
    exact hxy

/-- Under the place comparison, the sign on the actual localized square root is the Legendre
symbol. The global Euler criterion applies to either choice of the square root. -/
theorem localQuadChar_of_isFrobAt {hZ : ℤ} {hs : s ^ 2 = algebraMap K (KS K S) (hZ : K)}
    (v : Places K S) (φ : Gloc K v.1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hR : ¬ (r : ℤ) ∣ hZ)
    (hF : ZInQ.Contrib.ChebFD.C10.IsFrobAt (tateGalToQ (tateAlgEquiv K) (decompMap K v.1 φ)) r) :
    (quadChar s hs hs0 (locMap K S v.1 φ) : ℤ) = @legendreSym r ⟨hr⟩ hZ := by
  let _ : Fact r.Prime := ⟨hr⟩
  let e := tateAlgEquiv K
  let x := e (inclS K S s)
  let g := tateGalToQ e (decompMap K v.1 φ)
  have hx : x ^ 2 = (hZ : Qbar) := by
    change (e (inclS K S s)) ^ 2 = _
    rw [← map_pow, ← map_pow, hs, map_intCast, map_intCast, map_intCast]
  have hcomp : g x = e (inclS K S (galS K S (locMap K S v.1 φ) s)) := by
    exact (tateGalToQ_apply_e e (decompMap K v.1 φ) (inclS K S s)).trans
      (congrArg e (resAbs_apply_coe K S (decompMap K v.1 φ) s).symm)
  have hfix : g x = x ↔ galS K S (locMap K S v.1 φ) s = s := by
    rw [hcomp]
    change e (inclS K S (galS K S (locMap K S v.1 φ) s)) = e (inclS K S s) ↔ _
    exact ⟨fun ht => (inclS K S).injective (e.injective ht),
      congrArg (fun y => e (inclS K S y))⟩
  have hsq : g x = x ↔ IsSquare (hZ : ZMod r) := by
    have ha := ZInQ.Manuscript.RC.AddressGenuine.galQ_sqrtQbar_eq_iff_of_isFrobAt hr hr2 hR
      ((ZInQ.Manuscript.RC.AddressGenuine.isFrobAt_iff_c10 hr).2 hF)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hx.trans (ZInQ.Manuscript.RC.AddressGenuine.sqrtQbar_sq hZ).symm) with ht | ht
    · simpa only [ht] using ha
    · simpa only [ht, map_neg, neg_inj] using ha
  have hn : (hZ : ZMod r) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hh := hfix.symm.trans hsq
  by_cases hS : IsSquare (hZ : ZMod r)
  · simp [quadChar, hh.mpr hS, (legendreSym.eq_one_iff r hn).mpr hS]
  · have hnf : galS K S (locMap K S v.1 φ) s ≠ s := fun h0 => hS (hh.mp h0)
    simp [quadChar, hnf, (legendreSym.eq_neg_one_iff r).mpr hS]

/-- Moving trace, determinant and sign from the existing global Frobenius facts and the
place comparison. Comparing any lift with its translate by inertia shows the sign is
unramified. -/
theorem movingLocalAction_of_frobeniusTrace {E : WeierstrassCurve ℚ} [E.IsElliptic]
    {hZ : ℤ} {hs : s ^ 2 = algebraMap K (KS K S) (hZ : K)}
    (v : Places K S) {r : ℕ} {a χ : ℤ}
    (hT : FrobeniusTrace E) (hr : r.Prime) (hr2 : r ≠ 2) (hR : ¬ (r : ℤ) ∣ hZ)
    (hQ : ZInQ.Manuscript.RC.Nonvanishing.GoodAt E r) (ha : E.LFunction r = a)
    (hχ : χ = @legendreSym r ⟨hr⟩ hZ)
    (h2 : (2 : 𝓞 K) ∉ v.1.asIdeal) (hGood : HasGoodReductionAt (E.baseChange K) v.1)
    (hAbove : (r : 𝓞 K) ∈ v.1.asIdeal) (hNorm : v.1.asIdeal.absNorm = r) :
    Nonempty (MovingLocalAction E s hs hs0 v r a χ) := by
  obtain ⟨φ, hφ⟩ := ZInQ.Manuscript.RC.SelmerComplex.urRes_surjective K v.1 (frobElt (eUr K v.1))
  have H := moving_isFrobAt_of_residueDegreeOne v hr hAbove hNorm
  have hF := H φ hφ
  have hsign (τ) (hτ : urRes K v.1 τ = frobElt (eUr K v.1)) :
      (quadChar s hs hs0 (locMap K S v.1 τ) : ℤ) = χ :=
    (localQuadChar_of_isFrobAt v τ hr hr2 hR (H τ hτ)).trans hχ.symm
  refine ⟨⟨φ, hφ, localUnramifiedTorsion_of_goodReduction _ v h2 hGood, ?_, ?_, ?_, hsign φ hφ⟩⟩
  · intro σ hσ
    have hσφ : urRes K v.1 (σ * φ) = frobElt (eUr K v.1) := by
      rw [map_mul, hσ, one_mul, hφ]
    have he := Units.ext ((hsign _ hσφ).trans (hsign _ hφ).symm)
    have he' : quadChar s hs hs0 (locMap K S v.1 σ) *
        quadChar s hs hs0 (locMap K S v.1 φ) = 1 * quadChar s hs hs0 (locMap K S v.1 φ) := by
      simpa only [map_mul, one_mul] using he
    exact mul_right_cancel he'
  · rw [localTateMatrix, trace_tateMatrix, hT r hr hr2 hQ _ hF, ha]
  · rw [localTateMatrix, det_tateMatrix,
      ZInQ.Manuscript.RC.GlueSweep.Tate.det_tateRep_eq_of_isFrobAt E hr2 hF]

/-- The arithmetic input `MovingPrimeData` supplies good reduction and identifies the
point-count trace with the trace convention of `FrobeniusTrace`. -/
theorem MovingPrimeData.localAction {ℓ r : ℕ} {hZ a χ : ℤ} [(Ecurve ℓ).IsElliptic]
    [Algebra.IsQuadraticExtension ℚ K] (M : MovingPrimeData ℓ hZ r a χ)
    (v w : Places K S) (hne : v ≠ w)
    (hAbove : (r : 𝓞 K) ∈ v.1.asIdeal) (hw : (r : 𝓞 K) ∈ w.1.asIdeal)
    {hs : s ^ 2 = algebraMap K (KS K S) (hZ : K)}
    (hT : FrobeniusTrace (Ecurve ℓ)) :
    Nonempty (MovingLocalAction (Ecurve ℓ) s hs hs0 v r a χ) := by
  let _ : Fact r.Prime := ⟨M.hprime⟩
  have hbad : ¬ (r : ℤ) ∣ 6 * (ℓ : ℤ) := by
    intro hd
    apply M.hgood
    rw [show (6 : ℤ) * hZ * (ℓ : ℤ) = hZ * (6 * (ℓ : ℤ)) by ring]
    exact Dvd.dvd.mul_left hd _
  have hI := prime_under_of_above v M.hprime hAbove
  have hv (m : ℤ) : (m : 𝓞 K) ∈ v.1.asIdeal ↔ (r : ℤ) ∣ m := by
    change m ∈ v.1.asIdeal.under ℤ ↔ _
    rw [hI, Ideal.mem_span_singleton]
  have h2 : (2 : 𝓞 K) ∉ v.1.asIdeal := fun h2 =>
    hbad (dvd_mul_of_dvd_left ((hv 2).1 (by simpa using h2) |>.trans (by decide : (2 : ℤ) ∣ 6)) _)
  have h3 : (3 : 𝓞 K) ∉ v.1.asIdeal := fun h3 =>
    hbad (dvd_mul_of_dvd_left ((hv 3).1 (by simpa using h3) |>.trans (by decide : (3 : ℤ) ∣ 6)) _)
  have hℓ : (ℓ : 𝓞 K) ∉ v.1.asIdeal := fun hℓ =>
    hbad (Dvd.dvd.mul_left ((hv (ℓ : ℤ)).1 (by simpa using hℓ)) _)
  have hGood : HasGoodReductionAt ((Ecurve ℓ).baseChange K) v.1 := by
    rw [tate_ecurve_baseChange]
    exact hasGoodReductionAt_curveEll v.1 (valuation_natCast_eq_one v.1 hℓ) h2 h3
  have hr2 : r ≠ 2 := by
    intro he
    have ho := M.odd
    rw [he] at ho
    exact (by decide : ¬ Odd (2 : ℕ)) ho
  have hQ : ZInQ.Manuscript.RC.Nonvanishing.GoodAt (Ecurve ℓ) r := by
    simpa only [Ecurve, Int.cast_natCast] using
      ZInQ.Manuscript.RC.Nonvanishing.goodAt_curve M.hprime hbad
  have hRed : ((ZInQ.Contrib.CloudB3RC53.Calibration.E0Z ℓ 1).map
      (Int.castRingHom (ZMod r))) = ZInQ.Manuscript.PoleRC.curveF ((ℓ : ℤ) : ZMod r) := by
    ext <;> simp [ZInQ.Contrib.CloudB3RC53.Calibration.E0Z, ZInQ.Manuscript.PoleRC.curveF]
  have ha : (Ecurve ℓ).LFunction r = a := by
    rw [M.htrace, hRed]
    simpa only [Ecurve, Int.cast_natCast] using
      ZInQ.Manuscript.RC.KSplit.LFunction_curve_apply_prime (ℓ : ℤ) r hbad
  have hR : ¬ (r : ℤ) ∣ hZ :=
    fun hd => M.hgood (Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 6) _)
  exact movingLocalAction_of_frobeniusTrace v hT M.hprime hr2 hR hQ ha M.hsign h2 hGood hAbove
    (movingPrime_absNorm_of_two_places M.hprime v w hne hAbove hw)

end ZInQ.Contrib.RC53Assist.Calibration
