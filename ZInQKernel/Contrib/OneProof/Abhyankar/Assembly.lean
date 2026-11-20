import ZInQKernel.Contrib.OneProof.Abhyankar.Defs

/-!
# abhyankar: `TBNLocal` from the named steps

`tbnLocal_of_pieces : KummerBase → KummerUnram → EtaleBranch → BranchDescent → TBNLocal`, with the Kummer
field `Ω = L(f^{1/N}, g^{1/N})` constructed inside an algebraic closure (`exists_kummer_field`) and purity
of the branch locus in dimension 2 (`TPurity3.purityGlobalDim2'`, proved in the chain).
-/

open IsLocalRing HDec Polynomial IntermediateField

set_option linter.all false

noncomputable section

namespace Abhyankar

theorem isUnit_natCast_of_not_dvd {A : Type*} [CommRing A] [IsLocalRing A] {p : ℕ} (hp : p.Prime)
    (hpm : (p : A) ∈ maximalIdeal A) {n : ℕ} (hn : ¬ p ∣ n) : IsUnit (n : A) := by
  by_contra h
  have hnm : (n : A) ∈ maximalIdeal A := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h)
  have hcop : IsCoprime (n : ℤ) (p : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime n p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn)
    exact_mod_cast this
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : A) ∈ maximalIdeal A := by
    have h1 := congrArg (Int.cast : ℤ → A) hab
    push_cast at h1
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hnm) (Ideal.mul_mem_left _ _ hpm)
  exact (maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

theorem natDegree_minpoly_le {F E : Type*} [Field F] [Field E] [Algebra F E] {N : ℕ} (hN : 0 < N)
    {x : E} {a : F} (hx : x ^ N = algebraMap F E a) : (minpoly F x).natDegree ≤ N := by
  have hdvd : minpoly F x ∣ X ^ N - C a := minpoly.dvd F x (by simp [hx])
  have := natDegree_le_of_dvd hdvd (X_pow_sub_C_ne_zero hN a)
  rwa [natDegree_X_pow_sub_C] at this

theorem isSeparable_of_pow {F E : Type*} [Field F] [Field E] [Algebra F E] {N : ℕ}
    (hNF : (N : F) ≠ 0) {x : E} {a : F} (ha : a ≠ 0) (hx : x ^ N = algebraMap F E a) :
    IsSeparable F x :=
  (separable_X_pow_sub_C a hNF ha).of_dvd (minpoly.dvd F x (by simp [hx]))

/-- **The Kummer field** `Ω = L(a^{1/N}, b^{1/N})`, inside an algebraic closure of `L`: `[Ω : L]` is a product of
two integers `≤ N`, so it is prime to every prime `> N`. -/
theorem exists_kummer_field (L : Type) [Field L] (N : ℕ) (hN : 0 < N) (hNL : (N : L) ≠ 0) (a b : L)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra L Ω), FiniteDimensional L Ω ∧ Algebra.IsSeparable L Ω ∧
      (∀ q : ℕ, q.Prime → N < q → ¬ q ∣ Module.finrank L Ω) ∧
      ∃ t u : Ω, t ^ N = algebraMap L Ω a ∧ u ^ N = algebraMap L Ω b ∧
        IntermediateField.adjoin L {t, u} = ⊤ := by
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap L (AlgebraicClosure L) a) hN
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap L (AlgebraicClosure L) b) hN
  set E := IntermediateField.adjoin L ({t, u} : Set (AlgebraicClosure L)) with hE
  have htE : t ∈ E := IntermediateField.subset_adjoin _ _ (by simp)
  have huE : u ∈ E := IntermediateField.subset_adjoin _ _ (by simp)
  have hti : IsIntegral L t := Algebra.IsIntegral.isIntegral t
  have hui : IsIntegral L u := Algebra.IsIntegral.isIntegral u
  haveI : FiniteDimensional L E := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl)
    · exact hti
    · exact hui)
  have hts : IsSeparable L t := isSeparable_of_pow hNL ha ht
  have hus : IsSeparable L u := isSeparable_of_pow hNL hb hu
  haveI : Algebra.IsSeparable L E := IntermediateField.isSeparable_adjoin_pair_of_isSeparable (hx := hts) (hy := hus)
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ⟨t, htE⟩, ⟨u, huE⟩,
    ?_, ?_, ?_⟩
  · intro q hq hNq hdvd
    have h1 : Module.finrank L L⟮t⟯ * Module.finrank L⟮t⟯ L⟮t⟯⟮u⟯ = Module.finrank L E := by
      rw [hE, ← IntermediateField.adjoin_simple_adjoin_simple]
      exact Module.finrank_mul_finrank L L⟮t⟯ L⟮t⟯⟮u⟯
    have hd1 : Module.finrank L L⟮t⟯ ≤ N := by
      rw [IntermediateField.adjoin.finrank hti]
      exact natDegree_minpoly_le hN ht
    have hd2 : Module.finrank L⟮t⟯ L⟮t⟯⟮u⟯ ≤ N := by
      rw [IntermediateField.adjoin.finrank (hui.tower_top)]
      exact natDegree_minpoly_le (a := algebraMap L L⟮t⟯ b) hN (by rw [hu]; rfl)
    have hp1 : 0 < Module.finrank L L⟮t⟯ := Module.finrank_pos
    have hp2 : 0 < Module.finrank L⟮t⟯ L⟮t⟯⟮u⟯ := Module.finrank_pos
    rw [← h1] at hdvd
    rcases (Nat.Prime.dvd_mul hq).mp hdvd with h | h
    · exact absurd (Nat.le_of_dvd hp1 h) (by omega)
    · exact absurd (Nat.le_of_dvd hp2 h) (by omega)
  · exact Subtype.ext (by simpa using ht)
  · exact Subtype.ext (by simpa using hu)
  · apply IntermediateField.lift_injective
    rw [IntermediateField.lift_adjoin, IntermediateField.lift_top, Set.image_insert_eq,
      Set.image_singleton]

/-- The integral closure of `A''` in `Ω`, `A''` integral over `A`, is integrally closed (it has the carrier of the
integral closure of `A`). -/
theorem isIntegrallyClosed_tower (A K Ω : Type) [CommRing A] [IsDomain A] [Field K] [Field Ω]
    [Algebra A K] [IsFractionRing A K] [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω]
    [FiniteDimensional K Ω] (A'' : Subalgebra A Ω) [hint : Algebra.IsIntegral A A''] :
    IsIntegrallyClosed (integralClosure A'' Ω) := by
  haveI : IsIntegrallyClosed (integralClosure A Ω) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  have hmem : ∀ x : Ω, x ∈ integralClosure A Ω ↔ x ∈ integralClosure A'' Ω := by
    intro x
    rw [mem_integralClosure_iff, mem_integralClosure_iff]
    exact ⟨fun h => h.tower_top, fun h => isIntegral_trans x h⟩
  let e : integralClosure A Ω ≃+* integralClosure A'' Ω :=
    { toFun := fun x => ⟨x.1, (hmem x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (hmem x.1).mpr x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact IsIntegrallyClosed.of_equiv e

theorem maximalIdeal_ne_span_singleton {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A = 2) (f : A) : maximalIdeal A ≠ Ideal.span {f} := by
  intro h
  have h1 := TPurity3.height_maximalIdeal_le_one_of_eq_span_singleton h
  rw [TPurity3.height_maximalIdeal_of_dim2 hdim] at h1
  norm_num at h1

theorem under_maximal_eq {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S]
    [Algebra.IsIntegral A S] (𝔓 : Ideal S) [𝔓.IsMaximal] : 𝔓.under A = maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A 𝔓)

/-- **`TBNLocal` from the named steps** (compiled). -/
theorem tbnLocal_of_pieces (hB : KummerBase) (hU : KummerUnram) (hE : EtaleBranch)
    (hD : BranchDescent) : TBNLocal := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _ _ hdim f g hm hfp p hp hpm hdeg hunr 𝔓 h𝔓 Q hQ hQu hQ𝔓
  set N := Module.finrank K L with hNdef
  have hN : 0 < N := Module.finrank_pos
  have hht : (maximalIdeal A).height = 2 := TPurity3.height_maximalIdeal_of_dim2 hdim
  have hf0 : f ≠ 0 := TPurity3.ne_zero_of_pair hm hht
  have hg0 : g ≠ 0 := TPurity3.ne_zero_of_pair (by rw [hm, TPurity3.span_pair_comm]) hht
  have hNA : IsUnit (N : A) := isUnit_natCast_of_not_dvd hp hpm
    (fun h => absurd (Nat.le_of_dvd hN h) (not_le.mpr hdeg))
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have hNL : (N : L) ≠ 0 := by
    rw [← map_natCast (algebraMap A L)]
    exact fun h => (hNA.ne_zero) (hAL (by rw [h, map_zero]))
  obtain ⟨Ω, _, _, hfin, hsep, hdvd, t, u, ht, hu, hadj⟩ :=
    exists_kummer_field L N hN hNL (algebraMap A L f) (algebraMap A L g)
      (fun h => hf0 (hAL (by rw [h, map_zero]))) (fun h => hg0 (hAL (by rw [h, map_zero])))
  letI : Algebra K Ω := ((algebraMap L Ω).comp (algebraMap K L)).toAlgebra
  letI : Algebra A Ω := ((algebraMap L Ω).comp (algebraMap A L)).toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq (fun x =>
    congrArg (algebraMap L Ω) (IsScalarTower.algebraMap_apply A K L x))
  haveI : FiniteDimensional K Ω := Module.Finite.trans L Ω
  have ht' : t ^ N = algebraMap A Ω f := ht
  have hu' : u ^ N = algebraMap A Ω g := hu
  have hinj : Function.Injective (algebraMap A Ω) := (algebraMap L Ω).injective.comp hAL
  obtain ⟨hreg, hdim'', hmax''⟩ := hB A Ω hinj hdim f g hm N N hN hN t u ht' hu'
  obtain ⟨hfin', hunr'⟩ := hU A K L Ω hdim f g hm hfp p hp hpm hdeg hunr t u ht' hu' hadj
  set A'' := Algebra.adjoin A ({t, u} : Set Ω) with hA''
  haveI := hreg
  haveI := hfin'
  haveI hintA : Algebra.IsIntegral A A'' := Algebra.IsIntegral.adjoin (by
    rintro x (rfl | rfl)
    · exact ⟨_, monic_X_pow_sub_C (algebraMap A A f) hN.ne', by simp [ht']⟩
    · exact ⟨_, monic_X_pow_sub_C (algebraMap A A g) hN.ne', by simp [hu']⟩)
  set S' := integralClosure A'' Ω with hS'
  haveI : IsIntegrallyClosed S' := isIntegrallyClosed_tower A K Ω A''
  have hinjS : Function.Injective (algebraMap A'' S') := fun x y h =>
    Subtype.ext (congrArg (fun z : S' => (z : Ω)) h)
  have hét : Algebra.Etale A'' S' := TPurity3.purityGlobalDim2' hdim'' hinjS hunr'
  haveI : Algebra.IsIntegral A S' := Algebra.IsIntegral.trans A''
  set t'' : A'' := ⟨t, Algebra.subset_adjoin (by simp)⟩ with ht''
  set u'' : A'' := ⟨u, Algebra.subset_adjoin (by simp)⟩ with hu''
  have hmB : maximalIdeal A'' = Ideal.span {t'', u''} := (IsLocalRing.eq_maximalIdeal hmax'').symm
  have ht0 : t'' ≠ 0 := by
    intro h
    have : (t : Ω) = 0 := congrArg Subtype.val h
    apply hf0
    apply hinj
    rw [← ht', this, zero_pow hN.ne', map_zero]
  have hfS : ∀ Q'' : Ideal S', Q''.IsPrime → Q''.under A = Ideal.span {f} →
      algebraMap A'' S' t'' ∈ Q'' := by
    intro Q'' hQ'' hQ''u
    have hf : algebraMap A S' f ∈ Q'' := by
      have : f ∈ Q''.under A := by rw [hQ''u]; exact Ideal.mem_span_singleton_self f
      exact this
    have heq : algebraMap A S' f = (algebraMap A'' S' t'') ^ N := by
      apply Subtype.ext
      show algebraMap A Ω f = t ^ N
      rw [ht']
    rw [heq] at hf
    exact hQ''.mem_of_pow_mem N hf
  have hne : ∀ Q'' : Ideal S', Q''.under A = Ideal.span {f} → ∀ 𝔓' : Ideal S', 𝔓'.IsMaximal →
      Q'' ≠ 𝔓' := by
    rintro Q'' hQ''u 𝔓' h𝔓' rfl
    have := under_maximal_eq (A := A) Q''
    rw [hQ''u] at this
    exact maximalIdeal_ne_span_singleton hdim f this.symm
  have hbr : ∀ 𝔓' : Ideal S', 𝔓'.IsMaximal → ∀ Q' : Ideal S', Q'.IsPrime →
      Q'.under A = Ideal.span {f} → Q' ≤ 𝔓' → BranchConcl (Ideal.span {f}) 𝔓' Q' := by
    intro 𝔓' h𝔓' Q' hQ' hQ'u hQ'𝔓'
    obtain ⟨hub, hn⟩ := hE A'' S' hdim'' t'' u'' hmB ht0 hét hfin' hinjS 𝔓' h𝔓' Q' hQ'
      (hfS Q' hQ' hQ'u) hQ'𝔓' (hne Q' hQ'u 𝔓' h𝔓')
    exact ⟨fun Q'' hQ'' hQ''u hQ''𝔓' => hub Q'' hQ'' (hfS Q'' hQ'' hQ''u) hQ''𝔓'
      (hne Q'' hQ''u 𝔓' h𝔓'), hn⟩
  haveI : IsIntegrallyClosed A := TPurity3.isIntegrallyClosed_of_dim2 hdim
  haveI : IsNoetherianRing S' := IsNoetherianRing.of_finite A'' S'
  have hd : ((Module.finrank L Ω : ℕ) : integralClosure A L) ∉ 𝔓 := by
    intro h
    have h1 : ((Module.finrank L Ω : ℕ) : A) ∈ 𝔓.under A := by
      show algebraMap A _ _ ∈ 𝔓
      rwa [map_natCast]
    rw [under_maximal_eq] at h1
    exact (isUnit_natCast_of_not_dvd hp hpm (hdvd p hp hdeg)).ne_zero
      (by exact absurd h1 ((mem_maximalIdeal _).not.mpr (fun h' =>
        (mem_nonunits_iff.mp h') (isUnit_natCast_of_not_dvd hp hpm (hdvd p hp hdeg)))))
  exact hD A K L Ω A'' hintA inferInstance (Ideal.span {f}) hfp hbr 𝔓 h𝔓 Q hQ hQu hQ𝔓 hd

end Abhyankar
