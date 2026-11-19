import ZInQKernel.Contrib.CloudB3E1RingClass.PowerResidue
import ZInQKernel.Contrib.CloudB3E1RingClass.GenuineMovingData

/-!
# Split primes avoiding a finite set generate the class group of a quadratic field

Manuscript `diophantine_zq.tex`, tex 3532–3534 ("enough additional split prime ideals to generate
`Cl(K)`. The latter exist outside any finite set"; the interface's `cls_gen`).

For a quadratic number field `K` and a finite set `T` of primes, `exists_split_generators` gives
finitely many split primes `𝔭_j`, with conjugates `𝔭̄_j ≠ 𝔭_j` and `𝔭_j 𝔭̄_j = (p_j)` for rational
primes `p_j`, none of them in `T`, whose classes generate `Cl(K)`. The proof needs no Chebotarev
theorem:
* every ideal class contains an integral ideal prime to a given integer `N` (Tau Ceti's ray class
  groups: `rayClassToClassGroup_surjective`, `idealClass_surjective`);
* take `N = |disc K| · ∏_{w ∈ T} N(w)`. A prime `v` not containing `N` is unramified
  (`not_dvd_discr_iff_forall_liesOver`), and it is either inert, so `v = (p)` is principal, or split,
  with `v v' = (p)` and `v' ≠ v` (`isPrincipal_or_split`: the fundamental identity
  `∑ e f = [K : ℚ] = 2` with the factorization `p𝒪_K = ∏ P^{e_P}`). Neither `v` nor `v'` lies in `T`.
* the class of such an ideal is a product of classes of its prime factors (induction on the
  factorization).
`clsGen_of_generators`: the interface's `cls_gen` for any `RingClassSetup` whose chosen primes
include these generators.

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1RingClass

open NumberField IsDedekindDomain
open TauCeti TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

/-! ### The rational prime under a prime of `𝒪_K` -/

/-- Every prime of `𝒪_K` lies over a rational prime. Kind: PROVED. -/
theorem exists_rat_prime_under (v : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ v.asIdeal.under ℤ = Ideal.span {(q : ℤ)} := by
  set I := v.asIdeal.under ℤ
  have hI : I.IsPrime := Ideal.IsPrime.comap _
  have hI0 : I ≠ ⊥ := by
    intro h
    have hmem : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ∈ v.asIdeal := Ideal.absNorm_mem _
    have hmem' : ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) ∈ I := by
      change algebraMap ℤ (𝓞 K) _ ∈ v.asIdeal
      simpa using hmem
    rw [h, Ideal.mem_bot] at hmem'
    have hne : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact hne (by exact_mod_cast hmem')
  obtain ⟨g, hg⟩ := (inferInstance : I.IsPrincipal)
  have hg' : I = Ideal.span {g} := by rw [hg]
  have hg0 : g ≠ 0 := by rintro rfl; exact hI0 (by rw [hg', Ideal.span_singleton_eq_bot])
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ hI)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, ?_⟩
  rw [hg', Ideal.span_singleton_eq_span_singleton]
  exact Int.associated_natAbs g

omit [NumberField K] in
/-- Membership of a natural number in a prime over `q`. Kind: PROVED. -/
theorem natCast_mem_iff {v : HeightOneSpectrum (𝓞 K)} {q : ℕ}
    (hq : v.asIdeal.under ℤ = Ideal.span {(q : ℤ)}) (n : ℕ) :
    (n : 𝓞 K) ∈ v.asIdeal ↔ (q : ℤ) ∣ n := by
  rw [← Ideal.mem_span_singleton, ← hq, Ideal.under, Ideal.mem_comap, map_natCast]

/-! ### Unramified primes of a quadratic field are inert or split -/

/-- **An unramified prime of a quadratic field is inert or split** (the fundamental identity
`∑ e f = 2` with `q𝒪_K = ∏ P^{e_P}`): either `v = (q)`, or `v v' = (q)` for a second prime
`v' ≠ v` over `q`. Kind: PROVED. -/
theorem isPrincipal_or_split (hK : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K)) {q : ℕ}
    (hq : q.Prime) (hvq : v.asIdeal.under ℤ = Ideal.span {(q : ℤ)})
    (he : v.asIdeal.ramificationIdx ℤ = 1) :
    v.asIdeal = Ideal.span {((q : ℤ) : 𝓞 K)} ∨
      ∃ v' : HeightOneSpectrum (𝓞 K), v' ≠ v ∧ v'.asIdeal.under ℤ = Ideal.span {(q : ℤ)} ∧
        v.asIdeal * v'.asIdeal = Ideal.span {((q : ℤ) : 𝓞 K)} := by
  classical
  set p : Ideal ℤ := Ideal.span {(q : ℤ)} with hp
  have hpmax : p.IsMaximal :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hq) |>.isMaximal (by
        rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero)
  have hp0 : p ≠ 0 := by
    rw [hp, Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) p = Ideal.span {((q : ℤ) : 𝓞 K)} := by
    rw [hp, Ideal.map_span, Set.image_singleton, eq_intCast]
  have hprod := Ideal.map_algebraMap_eq_finsetProd_pow (R := 𝓞 K) hp0
  have hsum := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K)
  rw [RingOfIntegers.rank, hK] at hsum
  set F := (p.primesOver (𝓞 K)).toFinset with hF
  have hsum' : ∑ P ∈ F, P.ramificationIdx ℤ * P.inertiaDeg ℤ = 2 := by
    rw [← hsum, hF, ← Finset.sum_coe_sort]
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight (fun x => Set.mem_toFinset)) _ _ (fun _ => rfl)
  have hvF : v.asIdeal ∈ F := by
    rw [hF, Set.mem_toFinset]
    exact ⟨v.isPrime, ⟨hvq.symm⟩⟩
  have hpos : ∀ P ∈ F, 1 ≤ P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
    intro P hP
    rw [hF, Set.mem_toFinset] at hP
    obtain ⟨hPp, hPl⟩ := hP
    have h1 : 0 < P.ramificationIdx ℤ :=
      Ideal.ramificationIdx_pos_of_isDedekindDomain (p := p) P
        (by rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero)
    have h2 : 0 < P.inertiaDeg ℤ := Ideal.inertiaDeg_pos P ℤ
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h1.ne' h2.ne')
  rw [← Finset.add_sum_erase F _ hvF, he, one_mul] at hsum'
  have hcard : (F.erase v.asIdeal).card ≤
      ∑ P ∈ F.erase v.asIdeal, P.ramificationIdx ℤ * P.inertiaDeg ℤ := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun P hP => hpos P (Finset.mem_of_mem_erase hP)
  have hfv : 0 < v.asIdeal.inertiaDeg ℤ := Ideal.inertiaDeg_pos _ ℤ
  rcases Nat.lt_or_ge (v.asIdeal.inertiaDeg ℤ) 2 with hlt | hge
  · -- split: `f(v) = 1`, one more prime with `e f = 1`
    have hf1 : v.asIdeal.inertiaDeg ℤ = 1 := by omega
    have hrest : ∑ P ∈ F.erase v.asIdeal, P.ramificationIdx ℤ * P.inertiaDeg ℤ = 1 := by omega
    have hc1 : (F.erase v.asIdeal).card = 1 := by
      refine le_antisymm (hrest ▸ hcard) (Finset.card_pos.mpr ?_)
      by_contra hem
      rw [Finset.not_nonempty_iff_eq_empty] at hem
      rw [hem, Finset.sum_empty] at hrest
      exact absurd hrest (by norm_num)
    obtain ⟨P', hP'⟩ := Finset.card_eq_one.mp hc1
    have hP'mem : P' ∈ F.erase v.asIdeal := by rw [hP']; exact Finset.mem_singleton_self _
    have hP'F := Finset.mem_of_mem_erase hP'mem
    have hP'ne := Finset.ne_of_mem_erase hP'mem
    rw [hP', Finset.sum_singleton] at hrest
    have heP' : P'.ramificationIdx ℤ = 1 := Nat.eq_one_of_mul_eq_one_right hrest
    have hFeq : F = {v.asIdeal, P'} := by
      rw [← Finset.insert_erase hvF, hP']
    rw [hFeq, Finset.prod_pair (Ne.symm hP'ne), he, heP', pow_one, pow_one, hmap]
      at hprod
    rw [hF, Set.mem_toFinset] at hP'F
    obtain ⟨hP'p, hP'l⟩ := hP'F
    have hP'0 : P' ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P'
    refine Or.inr ⟨⟨P', hP'p, hP'0⟩, fun h => hP'ne (congrArg HeightOneSpectrum.asIdeal h), ?_,
      hprod.symm⟩
    exact hP'l.over.symm
  · -- inert: `f(v) = 2`, no other prime
    have hrest : ∑ P ∈ F.erase v.asIdeal, P.ramificationIdx ℤ * P.inertiaDeg ℤ = 0 := by omega
    have hc0 : F.erase v.asIdeal = ∅ := by
      rw [← Finset.card_eq_zero]; omega
    have hFeq : F = {v.asIdeal} := by rw [← Finset.insert_erase hvF, hc0]; rfl
    rw [hFeq, Finset.prod_singleton, he, pow_one, hmap] at hprod
    exact Or.inl hprod.symm

/-! ### Avoiding a finite set: the integer `N` -/

/-- `N = |disc K| · ∏_{w ∈ T} N(w)`: a prime not containing `N` is unramified and lies over no
prime of `T`. Kind: definition. -/
def avoidNat (T : Finset (HeightOneSpectrum (𝓞 K))) : ℕ :=
  (discr K).natAbs * ∏ w ∈ T, Ideal.absNorm w.asIdeal

theorem avoidNat_ne_zero (T : Finset (HeightOneSpectrum (𝓞 K))) : avoidNat T ≠ 0 := by
  refine Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr (discr_ne_zero K)) ?_
  rw [Finset.prod_ne_zero_iff]
  intro w _
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact w.ne_bot

theorem avoidNat_mem {T : Finset (HeightOneSpectrum (𝓞 K))} {w : HeightOneSpectrum (𝓞 K)}
    (hw : w ∈ T) : (avoidNat T : 𝓞 K) ∈ w.asIdeal := by
  rw [avoidNat, Nat.cast_mul]
  refine Ideal.mul_mem_left _ _ ?_
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 K) =>
    Ideal.absNorm w.asIdeal) hw
  rw [hk, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

/-- A prime not containing `N` is unramified over `ℤ`. Kind: PROVED. -/
theorem ramificationIdx_eq_one_of_not_mem (T : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : (avoidNat T : 𝓞 K) ∉ v.asIdeal) {q : ℕ} (hq : q.Prime)
    (hvq : v.asIdeal.under ℤ = Ideal.span {(q : ℤ)}) :
    v.asIdeal.ramificationIdx ℤ = 1 := by
  have hqd : ¬ (q : ℤ) ∣ discr K := by
    intro h
    apply hv
    rw [avoidNat, Nat.cast_mul]
    refine Ideal.mul_mem_right _ _ ((natCast_mem_iff hvq _).mpr ?_)
    exact Int.dvd_natAbs.mpr h
  have hU := (not_dvd_discr_iff_forall_liesOver K (𝓞 K) (Nat.prime_iff_prime_int.mp hq)).mp hqd
    v.asIdeal v.isMaximal ⟨hvq.symm⟩
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

/-! ### Every class contains an ideal avoiding `N` -/

/-- **Every ideal class contains an integral ideal all of whose prime factors avoid `N`**
(Tau Ceti's ray class groups for the modulus `(N)`). Kind: PROVED. -/
theorem exists_mk0_avoid (N : ℕ) (hN : N ≠ 0) (c : ClassGroup (𝓞 K)) :
    ∃ (J : Ideal (𝓞 K)) (hJ : J ≠ 0),
      ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩ = c ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ J → (N : 𝓞 K) ∉ v.asIdeal := by
  let m : Modulus K :=
    ⟨Ideal.span {(N : 𝓞 K)}, by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hN, ∅⟩
  obtain ⟨x, hx⟩ := rayClassToClassGroup_surjective m c
  obtain ⟨J, rfl⟩ := idealClass_surjective m x
  obtain ⟨hJ0, hJ⟩ := NumberFieldArithmetic.mem_integralIdealsAway_iff.mp J.2
  refine ⟨J, hJ0, ?_, fun v hv hNv => hJ v ?_ hv⟩
  · rw [← classOfIdeal_eq_mk0 J]
    exact hx
  · rw [Modulus.mem_support_iff]
    exact Ideal.dvd_span_singleton.mpr hNv

/-! ### The split generators -/

/-- **The classes of split primes outside `T`**, with conjugates outside `T`. Kind: definition. -/
def splitGens (T : Finset (HeightOneSpectrum (𝓞 K))) : Set (ClassGroup (𝓞 K)) :=
  {g | ∃ (v v' : HeightOneSpectrum (𝓞 K)) (q : ℕ), q.Prime ∧ v ≠ v' ∧ v ∉ T ∧ v' ∉ T ∧
    v.asIdeal * v'.asIdeal = Ideal.span {((q : ℤ) : 𝓞 K)} ∧
      g = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩}

theorem mk0_prime_mem_closure (hK : Module.finrank ℚ K = 2) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (v : HeightOneSpectrum (𝓞 K)) (hv : (avoidNat T : 𝓞 K) ∉ v.asIdeal) :
    ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ ∈
      Subgroup.closure (splitGens T) := by
  obtain ⟨q, hq, hvq⟩ := exists_rat_prime_under v
  have he := ramificationIdx_eq_one_of_not_mem T v hv hq hvq
  rcases isPrincipal_or_split hK v hq hvq he with h | ⟨v', hne, hv'q, hmul⟩
  · have h1 : ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ = 1 := by
      rw [ClassGroup.mk0_eq_one_iff, h]
      exact ⟨⟨_, rfl⟩⟩
    rw [h1]
    exact one_mem _
  · refine Subgroup.subset_closure ⟨v, v', q, hq, hne.symm, fun hT => hv (avoidNat_mem hT),
      fun hT => hv ?_, hmul, rfl⟩
    exact (natCast_mem_iff hvq _).mpr ((natCast_mem_iff hv'q _).mp (avoidNat_mem hT))

theorem mk0_mem_closure (hK : Module.finrank ℚ K = 2) (T : Finset (HeightOneSpectrum (𝓞 K)))
    (J : Ideal (𝓞 K)) :
    ∀ (hJ : J ≠ 0), (∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ J →
      (avoidNat T : 𝓞 K) ∉ v.asIdeal) →
      ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩ ∈ Subgroup.closure (splitGens T) := by
  induction J using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx =>
    intro _ _
    have hx1 : x = ⊤ := Ideal.isUnit_iff.mp hx
    subst hx1
    have : (⟨⊤, mem_nonZeroDivisors_of_ne_zero ‹_›⟩ : (Ideal (𝓞 K))⁰) = 1 :=
      Subtype.ext Ideal.one_eq_top.symm
    rw [this, map_one]
    exact one_mem _
  | h₃ a p ha hp ih =>
    intro hpa hdiv
    have hp0 : p ≠ ⊥ := hp.ne_zero
    let vp : HeightOneSpectrum (𝓞 K) := ⟨p, (Ideal.prime_iff_isPrime hp0).mp hp, hp0⟩
    have hsplit : (⟨p * a, mem_nonZeroDivisors_of_ne_zero hpa⟩ : (Ideal (𝓞 K))⁰) =
        ⟨p, mem_nonZeroDivisors_of_ne_zero hp0⟩ * ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ :=
      Subtype.ext rfl
    rw [hsplit, map_mul]
    refine mul_mem ?_ (ih ha fun v hv => hdiv v (dvd_mul_of_dvd_right hv p))
    exact mk0_prime_mem_closure hK T vp (hdiv vp (dvd_mul_right p a))

/-- **The split primes outside `T` generate `Cl(K)`.** Kind: PROVED. -/
theorem closure_splitGens (hK : Module.finrank ℚ K = 2) (T : Finset (HeightOneSpectrum (𝓞 K))) :
    Subgroup.closure (splitGens T) = ⊤ := by
  refine eq_top_iff.mpr fun c _ => ?_
  obtain ⟨J, hJ0, rfl, hJ⟩ := exists_mk0_avoid (K := K) (avoidNat T) (avoidNat_ne_zero T) c
  exact mk0_mem_closure hK T J hJ0 hJ

/-- **Finitely many split primes outside `T` generate `Cl(K)`** (tex 3532–3534): split primes
`𝔭_j ≠ 𝔭̄_j` with `𝔭_j 𝔭̄_j = (p_j)`, `p_j` prime, none in `T`, whose classes generate the class
group. Kind: PROVED. -/
theorem exists_split_generators (hK : Module.finrank ℚ K = 2)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (s : ℕ) (𝔭 𝔭bar : Fin s → HeightOneSpectrum (𝓞 K)) (p : Fin s → ℕ),
      (∀ j, (p j).Prime) ∧ (∀ j, 𝔭 j ≠ 𝔭bar j) ∧ (∀ j, 𝔭 j ∉ T ∧ 𝔭bar j ∉ T) ∧
      (∀ j, (𝔭 j).asIdeal * (𝔭bar j).asIdeal = Ideal.span {(((p j : ℤ)) : 𝓞 K)}) ∧
      Subgroup.closure (Set.range fun j =>
        ClassGroup.mk0 ⟨(𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (𝔭 j).ne_bot⟩) = ⊤ := by
  classical
  set G := splitGens (K := K) T
  let L := (Set.toFinite G).toFinset
  let e : Fin L.card ≃ L := L.equivFin.symm
  have hmem : ∀ j : Fin L.card, ((e j : ClassGroup (𝓞 K))) ∈ G := fun j =>
    (Set.Finite.mem_toFinset _).mp (e j).2
  choose 𝔭 𝔭bar p hp hne h1 h2 hmul heq using hmem
  refine ⟨L.card, 𝔭, 𝔭bar, p, hp, hne, fun j => ⟨h1 j, h2 j⟩, hmul, ?_⟩
  rw [eq_top_iff, ← closure_splitGens hK T]
  refine Subgroup.closure_mono fun g hg => ?_
  have hgL : g ∈ L := (Set.Finite.mem_toFinset _).mpr hg
  refine ⟨e.symm ⟨g, hgL⟩, ?_⟩
  change ClassGroup.mk0 _ = g
  rw [← heq (e.symm ⟨g, hgL⟩), Equiv.apply_symm_apply]

/-- **The interface's `cls_gen`** (tex 3532–3534) for a `RingClassSetup` whose chosen primes
include a generating family. Kind: PROVED. -/
theorem clsGen_of_closure {s : ℕ} (C : RingClassSetup K s)
    (hC : Subgroup.closure (Set.range fun j =>
      ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩) = ⊤)
    (c : Additive (ClassGroup (𝓞 K))) : ∃ v : Fin s → ℤ, ∑ j, v j • setupCls C j = c := by
  have hc : Additive.toMul c ∈ Subgroup.closure (Set.range fun j =>
      ClassGroup.mk0 ⟨(C.𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (C.𝔭 j).ne_bot⟩) :=
    hC ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := Subgroup.mem_closure_range_iff_of_fintype.mp hc
  refine ⟨a, ?_⟩
  apply Additive.toMul.injective
  rw [ha, toMul_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [toMul_zsmul]
  rfl

/-- A prime containing `q`, where `(q) = 𝔭 𝔭'`, is `𝔭` or `𝔭'`. Kind: PROVED. -/
theorem eq_or_eq_of_mul_eq_span {𝔭 𝔭' w : HeightOneSpectrum (𝓞 K)} {q : ℤ}
    (hmul : 𝔭.asIdeal * 𝔭'.asIdeal = Ideal.span {(q : 𝓞 K)}) (hw : (q : 𝓞 K) ∈ w.asIdeal) :
    w = 𝔭 ∨ w = 𝔭' := by
  have hle : 𝔭.asIdeal * 𝔭'.asIdeal ≤ w.asIdeal := by
    rw [hmul, Ideal.span_le, Set.singleton_subset_iff]; exact hw
  rcases w.isPrime.mul_le.mp hle with h | h
  · exact Or.inl (HeightOneSpectrum.ext (𝔭.isMaximal.eq_of_le w.isPrime.ne_top h).symm)
  · exact Or.inr (HeightOneSpectrum.ext (𝔭'.isMaximal.eq_of_le w.isPrime.ne_top h).symm)

/-- **Finitely many split primes in distinct conjugate pairs outside `T` generate `Cl(K)`**
(tex 3528–3534): as `exists_split_generators`, with distinct rational primes `p_j`, so that the
pairs `{𝔭_j, 𝔭̄_j}` are pairwise disjoint. Kind: PROVED. -/
theorem exists_split_generators_distinct (hK : Module.finrank ℚ K = 2)
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ (s : ℕ) (𝔭 𝔭bar : Fin s → HeightOneSpectrum (𝓞 K)) (p : Fin s → ℕ),
      (∀ j, (p j).Prime) ∧ Function.Injective p ∧ (∀ j, 𝔭 j ≠ 𝔭bar j) ∧
      (∀ j, 𝔭 j ∉ T ∧ 𝔭bar j ∉ T) ∧
      (∀ j, (𝔭 j).asIdeal * (𝔭bar j).asIdeal = Ideal.span {(((p j : ℤ)) : 𝓞 K)}) ∧
      Subgroup.closure (Set.range fun j =>
        ClassGroup.mk0 ⟨(𝔭 j).asIdeal, mem_nonZeroDivisors_of_ne_zero (𝔭 j).ne_bot⟩) = ⊤ := by
  classical
  obtain ⟨s₀, 𝔭₀, 𝔭bar₀, p₀, hp₀, hne₀, hT₀, hmul₀, hcl₀⟩ := exists_split_generators hK T
  let Q : Finset ℕ := Finset.univ.image p₀
  have hrep : ∀ q : Q, ∃ j, p₀ j = q := fun q => by
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp q.2; exact ⟨j, hj⟩
  choose rep hrep using hrep
  let e : Fin Q.card ≃ Q := Q.equivFin.symm
  let ι : Fin Q.card → Fin s₀ := fun i => rep (e i)
  refine ⟨Q.card, 𝔭₀ ∘ ι, 𝔭bar₀ ∘ ι, p₀ ∘ ι, fun i => hp₀ _, ?_, fun i => hne₀ _,
    fun i => hT₀ _, fun i => hmul₀ _, ?_⟩
  · intro i i' h
    have h1 : (e i : ℕ) = e i' := by
      change p₀ (rep (e i)) = p₀ (rep (e i')) at h
      rw [hrep, hrep] at h; exact h
    exact e.injective (Subtype.ext h1)
  · rw [eq_top_iff, ← hcl₀]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨j, rfl⟩
    -- the representative over the same rational prime
    have hq : p₀ j ∈ Q := Finset.mem_image_of_mem _ (Finset.mem_univ j)
    let i := e.symm ⟨p₀ j, hq⟩
    have hpi : p₀ (ι i) = p₀ j := by
      change p₀ (rep (e (e.symm ⟨p₀ j, hq⟩))) = _
      rw [Equiv.apply_symm_apply, hrep]
    have hmem : (((p₀ j : ℤ)) : 𝓞 K) ∈ (𝔭₀ j).asIdeal := by
      have : (((p₀ j : ℤ)) : 𝓞 K) ∈ (𝔭₀ j).asIdeal * (𝔭bar₀ j).asIdeal := by
        rw [hmul₀ j]; exact Ideal.mem_span_singleton_self _
      exact Ideal.mul_le_left (I := (𝔭₀ j).asIdeal) (J := (𝔭bar₀ j).asIdeal) this
    have hmul_i := hmul₀ (ι i)
    rw [hpi] at hmul_i
    have hgen : ClassGroup.mk0 ⟨(𝔭₀ (ι i)).asIdeal,
        mem_nonZeroDivisors_of_ne_zero (𝔭₀ (ι i)).ne_bot⟩ ∈ Subgroup.closure (Set.range fun i =>
          ClassGroup.mk0 ⟨((𝔭₀ ∘ ι) i).asIdeal,
            mem_nonZeroDivisors_of_ne_zero ((𝔭₀ ∘ ι) i).ne_bot⟩) :=
      Subgroup.subset_closure ⟨i, rfl⟩
    change ClassGroup.mk0 ⟨(𝔭₀ j).asIdeal, mem_nonZeroDivisors_of_ne_zero (𝔭₀ j).ne_bot⟩ ∈ _
    rcases eq_or_eq_of_mul_eq_span hmul_i hmem with h | h
    · rw [h]; exact hgen
    · rw [h]
      have hprod : ClassGroup.mk0 ⟨(𝔭₀ (ι i)).asIdeal,
            mem_nonZeroDivisors_of_ne_zero (𝔭₀ (ι i)).ne_bot⟩ *
          ClassGroup.mk0 ⟨(𝔭bar₀ (ι i)).asIdeal,
            mem_nonZeroDivisors_of_ne_zero (𝔭bar₀ (ι i)).ne_bot⟩ = 1 := by
        rw [← map_mul]
        have hsub : (⟨(𝔭₀ (ι i)).asIdeal, mem_nonZeroDivisors_of_ne_zero (𝔭₀ (ι i)).ne_bot⟩ *
            ⟨(𝔭bar₀ (ι i)).asIdeal, mem_nonZeroDivisors_of_ne_zero (𝔭bar₀ (ι i)).ne_bot⟩ :
              (Ideal (𝓞 K))⁰) =
            ⟨Ideal.span {(((p₀ j : ℤ)) : 𝓞 K)}, hmul_i ▸ mul_mem
              (mem_nonZeroDivisors_of_ne_zero (𝔭₀ (ι i)).ne_bot)
              (mem_nonZeroDivisors_of_ne_zero (𝔭bar₀ (ι i)).ne_bot)⟩ :=
          Subtype.ext hmul_i
        rw [hsub, ClassGroup.mk0_eq_one_iff]
        exact ⟨⟨_, rfl⟩⟩
      rw [eq_inv_of_mul_eq_one_right hprod]
      exact inv_mem hgen

end ZInQ.Contrib.CloudB3E1RingClass
