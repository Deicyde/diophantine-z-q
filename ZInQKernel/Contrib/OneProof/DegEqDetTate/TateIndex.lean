import ZInQKernel.Contrib.OneProof.H.LF4T5

/-!
# deg-det, step (3): `|det T_ℓ φ|_ℓ = |#ker φ|_ℓ` (elementary divisors)

Task deg-det (2026-11-16), report `docs/research/deg-det.md`.

Abstract form (`norm_det_map_eq`): `M` an abelian group with `#M[ℓⁿ] = ℓ^{nr}` for all `n` (for `M = A(k̄)`
this is Mumford's `A[ℓⁿ] ≅ (ℤ/ℓⁿ)^{2g}`, the open field `mumfordTorsionAlgClosed`) and `φ : M → M` a
homomorphism with finite kernel. Then `T_ℓ φ` is injective, `[T_ℓ M : T_ℓ φ (T_ℓ M)] = |det T_ℓ φ|_ℓ⁻¹`
(Smith normal form over `ℤ_ℓ`), this index is `#(M[ℓⁿ]/φ M[ℓⁿ]) = #(ker φ)[ℓⁿ]` for `n` large, and that is
the `ℓ`-part of `#ker φ`. Uses the kernel's `PkgI3.Tate.T` and t5-torsion's `exists_lift`.
-/

open Polynomial

noncomputable section

namespace ZInQ.Contrib.OneProof.DegDet.TateIndex

/-! ## 1. Index of a full sublattice of a free `ℤ_ℓ`-module -/

section Index

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

theorem card_quot_span (a : ℤ_[ℓ]) (ha : a ≠ 0) :
    Nat.card (ℤ_[ℓ] ⧸ Ideal.span {a}) = ℓ ^ a.valuation := by
  have hspan : Ideal.span {a} = Ideal.span {(ℓ : ℤ_[ℓ]) ^ a.valuation} := by
    conv_lhs => rw [PadicInt.unitCoeff_spec ha]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff ha).isUnit _
  rw [hspan, ← PadicInt.ker_toZModPow]
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow a.valuation))).toEquiv, Nat.card_zmod]

/-- `|a|_ℓ = #(ℤ_ℓ/(a))⁻¹`. -/
theorem norm_eq_inv_card_quot (a : ℤ_[ℓ]) (ha : a ≠ 0) :
    ‖a‖ = ((Nat.card (ℤ_[ℓ] ⧸ Ideal.span {a}) : ℕ) : ℝ)⁻¹ := by
  have hspan : Ideal.span {a} = Ideal.span {(ℓ : ℤ_[ℓ]) ^ a.valuation} := by
    conv_lhs => rw [PadicInt.unitCoeff_spec ha]
    exact Ideal.span_singleton_mul_left_unit (PadicInt.unitCoeff ha).isUnit _
  have hcard : Nat.card (ℤ_[ℓ] ⧸ Ideal.span {a}) = ℓ ^ a.valuation := by
    rw [hspan, ← PadicInt.ker_toZModPow]
    rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow a.valuation))).toEquiv, Nat.card_zmod]
  rw [hcard, PadicInt.norm_eq_zpow_neg_valuation ha, zpow_neg, zpow_natCast]
  push_cast
  rfl

variable {T : Type*} [AddCommGroup T] [Module ℤ_[ℓ] T] [Module.Free ℤ_[ℓ] T] [Module.Finite ℤ_[ℓ] T]

/-- **`|det F|_ℓ = [T : F(T)]⁻¹`** for an injective `ℤ_ℓ`-linear endomorphism of a free module of finite rank. -/
theorem norm_det_eq_inv_card (F : T →ₗ[ℤ_[ℓ]] T) (hF : Function.Injective F) :
    ‖LinearMap.det F‖ = ((Nat.card (T ⧸ LinearMap.range F) : ℕ) : ℝ)⁻¹ := by
  classical
  set N := LinearMap.range F
  let b := Module.Free.chooseBasis ℤ_[ℓ] T
  let eF : T ≃ₗ[ℤ_[ℓ]] N := LinearEquiv.ofInjective F hF
  have h : Module.finrank ℤ_[ℓ] N = Module.finrank ℤ_[ℓ] T := eF.symm.finrank_eq
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let e' : T ≃ₗ[ℤ_[ℓ]] N := b'.equiv ab (Equiv.refl _)
  let f : T →ₗ[ℤ_[ℓ]] T := N.subtype.comp (e' : T →ₗ[ℤ_[ℓ]] N)
  have hFf : Associated (LinearMap.det F) (LinearMap.det f) := by
    have h1 : F = N.subtype.comp (eF : T →ₗ[ℤ_[ℓ]] N) := by
      ext x; rfl
    rw [h1]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have ha : ∀ i, f (b' i) = a i • b' i := by
    intro i
    change ((b'.equiv ab (Equiv.refl _)) (b' i) : T) = _
    rw [b'.equiv_apply, Equiv.refl_apply]
    exact ab_eq i
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b', ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply, ha, map_smul, Module.Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    by_cases hij : i = j
    · rw [hij, Matrix.diagonal_apply_eq, Finsupp.single_eq_same]
    · rw [Matrix.diagonal_apply_ne _ hij, Finsupp.single_eq_of_ne hij]
  have hnorm : ‖LinearMap.det F‖ = ‖LinearMap.det f‖ := by
    obtain ⟨u, hu⟩ := hFf
    rw [← hu, norm_mul, PadicInt.isUnit_iff.mp u.isUnit, mul_one]
  rw [hnorm, hdet, norm_prod]
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi]
  push_cast
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact norm_eq_inv_card_quot (a i) (Submodule.smithNormalFormCoeffs_ne_zero b h i)

/-- The index `[T : F(T)]` is a power of `ℓ`. -/
theorem card_quot_range_pow (F : T →ₗ[ℤ_[ℓ]] T) (hF : Function.Injective F) :
    ∃ v : ℕ, Nat.card (T ⧸ LinearMap.range F) = ℓ ^ v := by
  classical
  set N := LinearMap.range F
  let b := Module.Free.chooseBasis ℤ_[ℓ] T
  let eF : T ≃ₗ[ℤ_[ℓ]] N := LinearEquiv.ofInjective F hF
  have h : Module.finrank ℤ_[ℓ] N = Module.finrank ℤ_[ℓ] T := eF.symm.finrank_eq
  refine ⟨∑ i, (Submodule.smithNormalFormCoeffs b h i).valuation, ?_⟩
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan N b h).toEquiv, Nat.card_pi, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_congr rfl fun i _ => card_quot_span _ (Submodule.smithNormalFormCoeffs_ne_zero b h i)

end Index

/-! ## 2. Finite levels of the Tate module -/

section Levels

open PkgI3.Tate T5Torsion.TateFree

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M]

/-- Every `y ∈ M[ℓⁿ]` is the `n`-th term of an element of `T_ℓ M`. -/
theorem exists_tate_lift_n (r : ℕ) (hcard : ∀ n : ℕ, Nat.card (tb ℓ M n) = ℓ ^ (n * r))
    (n : ℕ) (y : M) (hy : ℓ ^ n • y = 0) : ∃ x : T ℓ M, x.1 n = y := by
  let g : (k : ℕ) → {z : M // ℓ ^ (n + k) • z = 0} := fun k =>
    Nat.rec ⟨y, by simpa using hy⟩
      (fun k z => ⟨(exists_lift r hcard (n + k) z.1 z.2).choose,
        (exists_lift r hcard (n + k) z.1 z.2).choose_spec.1⟩) k
  have hg : ∀ k, ℓ • (g (k + 1)).1 = (g k).1 := fun k =>
    (exists_lift r hcard (n + k) (g k).1 (g k).2).choose_spec.2
  have hg0 : (g 0).1 = y := rfl
  let x : ℕ → M := fun m => if m ≤ n then ℓ ^ (n - m) • y else (g (m - n)).1
  have hx : x ∈ T ℓ M := by
    refine ⟨by simp [x, hy], fun m => ?_⟩
    simp only [x]
    by_cases h1 : m + 1 ≤ n
    · rw [if_pos h1, if_pos (by omega), smul_smul, ← pow_succ']
      congr 2
      omega
    · by_cases h2 : m ≤ n
      · have hm : m = n := by omega
        subst hm
        rw [if_neg h1, if_pos h2, Nat.sub_self, pow_zero, one_smul, show m + 1 - m = 0 + 1 by omega,
          hg 0, hg0]
      · rw [if_neg h1, if_neg h2, show m + 1 - n = (m - n) + 1 by omega, hg]
  refine ⟨⟨x, hx⟩, ?_⟩
  simp [x]

/-- `(ℓⁿ • x)ₙ = 0`. -/
theorem pow_smul_apply_self (x : T ℓ M) (n : ℕ) : (((ℓ : ℤ_[ℓ]) ^ n) • x).1 n = 0 := by
  change smulSeq _ x.1 n = 0
  rw [smulSeq_congr x.2 n (c := ℓ ^ n) (by rw [map_pow, map_natCast, Nat.cast_pow]),
    pow_smul_eq_zero x.2 n]

/-- If `xₙ = 0` then `x ∈ ℓⁿ T`. -/
theorem exists_eq_pow_smul (x : T ℓ M) (n : ℕ) (hx : x.1 n = 0) :
    ∃ x' : T ℓ M, x = ((ℓ : ℤ_[ℓ]) ^ n) • x' := by
  refine ⟨⟨fun m => x.1 (m + n), ⟨by simpa using hx, fun m => ?_⟩⟩, ?_⟩
  · have := x.2.2 (m + n)
    rwa [show m + n + 1 = m + 1 + n by omega] at this
  · apply Subtype.ext
    funext m
    change x.1 m = smulSeq _ (fun m => x.1 (m + n)) m
    rw [smulSeq_congr (x := fun m => x.1 (m + n)) ⟨by simpa using hx, fun m => by
      have := x.2.2 (m + n)
      rwa [show m + n + 1 = m + 1 + n by omega] at this⟩ m (c := ℓ ^ n) (by simp)]
    exact (pow_smul_add x.2 m n).symm

end Levels

/-! ## 3. `|det T_ℓ φ|_ℓ = |#ker φ|_ℓ` -/

section Count

open PkgI3.Tate T5Torsion.TateFree

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {M : Type*} [AddCommGroup M]

/-- `T_ℓ φ` is injective when `ker φ` is finite. -/
theorem map_injective_of_finite_ker (φ : M →+ M) [Finite φ.ker] :
    Function.Injective (PkgI3.Tate.map φ : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  funext n
  set c := Nat.card φ.ker
  have hc : 0 < c := Nat.card_pos
  have hk : ∀ m, φ (x.1 m) = 0 := fun m => by
    have := congrArg (fun y : T ℓ M => y.1 m) hx
    simpa using this
  have hord : ℓ ^ c • x.1 (n + c) = 0 := by
    let k : φ.ker := ⟨x.1 (n + c), hk (n + c)⟩
    have h1 : addOrderOf k ∣ ℓ ^ (n + c) :=
      addOrderOf_dvd_of_nsmul_eq_zero (Subtype.ext (by
        change ℓ ^ (n + c) • x.1 (n + c) = 0
        exact pow_smul_eq_zero x.2 (n + c)))
    obtain ⟨j, -, hjk⟩ := (Nat.dvd_prime_pow hℓ.out).mp h1
    have h2 : addOrderOf k ∣ c := addOrderOf_dvd_natCard k
    have hjc : j ≤ c := by
      rw [hjk] at h2
      exact (Nat.lt_pow_self hℓ.out.one_lt).le.trans (Nat.le_of_dvd hc h2)
    have h3 : addOrderOf k ∣ ℓ ^ c := hjk ▸ pow_dvd_pow ℓ hjc
    have := congrArg Subtype.val (addOrderOf_dvd_iff_nsmul_eq_zero.mp h3)
    simpa [k] using this
  have := pow_smul_add x.2 n c
  rw [hord] at this
  exact this.symm

/-- `φ` restricted to `M[ℓⁿ]`. -/
def phiN (φ : M →+ M) (n : ℕ) : tb ℓ M n →+ tb ℓ M n where
  toFun y := ⟨φ y.1, mem_tb.2 (by rw [← map_nsmul, mem_tb.1 y.2, map_zero])⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

/-- For a finite abelian group, `#(G / f(G)) = #ker f`. -/
theorem card_quot_range_eq_card_ker {G : Type*} [AddCommGroup G] [Finite G] (f : G →+ G) :
    Nat.card (G ⧸ f.range) = Nat.card f.ker := by
  have h1 := AddSubgroup.card_mul_index f.ker
  rw [AddSubgroup.index_ker] at h1
  have h2 := AddSubgroup.card_mul_index f.range
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  change f.range.index = _
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h2, mul_comm, h1]

/-- `ker(φ on M[ℓⁿ]) ≃ (ker φ)[ℓⁿ]`. -/
def kerPhiNEquiv (φ : M →+ M) (n : ℕ) : (phiN (ℓ := ℓ) φ n).ker ≃ tb ℓ φ.ker n where
  toFun y := ⟨⟨y.1.1, congrArg Subtype.val y.2⟩, mem_tb.2 (Subtype.ext (by
    change ℓ ^ n • y.1.1 = 0
    exact mem_tb.1 y.1.2))⟩
  invFun k := ⟨⟨k.1.1, mem_tb.2 (by
    have := congrArg Subtype.val (mem_tb.1 k.2)
    simpa using this)⟩, Subtype.ext (by
    change φ k.1.1 = 0
    exact k.1.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Step (3) of the task, abstract form.** Let `M` have `#M[ℓⁿ] = ℓ^{nr}` and let `φ : M → M` be a
homomorphism with finite kernel (no surjectivity needed). Then `|det T_ℓ(φ)|_ℓ = |#ker φ|_ℓ`. -/
theorem norm_det_map_eq (r : ℕ) (hcard : ∀ n : ℕ, Nat.card (tb ℓ M n) = ℓ ^ (n * r))
    (φ : M →+ M) [Finite φ.ker] :
    haveI : Module.Free ℤ_[ℓ] (T ℓ M) := Module.Free.of_equiv (tate_linearEquiv r hcard).some.symm
    haveI : Module.Finite ℤ_[ℓ] (T ℓ M) := Module.Finite.equiv (tate_linearEquiv r hcard).some.symm
    ‖LinearMap.det (PkgI3.Tate.map φ : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ M)‖ = ‖((Nat.card φ.ker : ℕ) : ℤ_[ℓ])‖ := by
  haveI : Module.Free ℤ_[ℓ] (T ℓ M) := Module.Free.of_equiv (tate_linearEquiv r hcard).some.symm
  haveI : Module.Finite ℤ_[ℓ] (T ℓ M) := Module.Finite.equiv (tate_linearEquiv r hcard).some.symm
  set F : T ℓ M →ₗ[ℤ_[ℓ]] T ℓ M := PkgI3.Tate.map φ with hFdef
  have hF : Function.Injective F := map_injective_of_finite_ker φ
  obtain ⟨v, hv⟩ := card_quot_range_pow F hF
  have hQfin : Finite (T ℓ M ⧸ LinearMap.range F) :=
    Nat.finite_of_card_ne_zero (by rw [hv]; exact pow_ne_zero _ hℓ.out.ne_zero)
  -- `ℓ^v T ⊆ F(T)`
  have hkill : ∀ x : T ℓ M, ((ℓ : ℤ_[ℓ]) ^ v) • x ∈ LinearMap.range F := by
    intro x
    have h := card_nsmul_eq_zero' (G := T ℓ M ⧸ LinearMap.range F) (x := Submodule.Quotient.mk x)
    rw [hv, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    convert h using 1
    rw [← Nat.cast_smul_eq_nsmul ℤ_[ℓ], Nat.cast_pow]
  -- the level-`n` map
  let π : ∀ n, T ℓ M →+ tb ℓ M n := fun n =>
    { toFun := fun x => ⟨x.1 n, mem_tb.2 (pow_smul_eq_zero x.2 n)⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let Ψ : ∀ n, T ℓ M →+ (tb ℓ M n ⧸ (phiN φ n).range) := fun n =>
    (QuotientAddGroup.mk' _).comp (π n)
  have hΨsurj : ∀ n, Function.Surjective (Ψ n) := by
    intro n q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    obtain ⟨x, hx⟩ := exists_tate_lift_n r hcard n y.1 (mem_tb.1 y.2)
    exact ⟨x, by simp only [Ψ, AddMonoidHom.comp_apply]; congr 1; exact Subtype.ext hx⟩
  have hker : ∀ n, v ≤ n → (Ψ n).ker = (LinearMap.range F).toAddSubgroup := by
    intro n hn
    ext x
    simp only [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
    constructor
    · intro hx
      have : π n x ∈ (phiN φ n).range := (QuotientAddGroup.eq_zero_iff _).mp hx
      obtain ⟨m, hm⟩ := this
      obtain ⟨z, hz⟩ := exists_tate_lift_n r hcard n m.1 (mem_tb.1 m.2)
      have h0 : (x - F z).1 n = 0 := by
        change x.1 n - φ (z.1 n) = 0
        rw [hz]
        exact sub_eq_zero.mpr (congrArg Subtype.val hm).symm
      obtain ⟨x', hx'⟩ := exists_eq_pow_smul _ n h0
      obtain ⟨w, hw⟩ := hkill x'
      refine ⟨z + ((ℓ : ℤ_[ℓ]) ^ (n - v)) • w, ?_⟩
      rw [map_add, map_smul, hw, smul_smul, ← pow_add, Nat.sub_add_cancel hn, ← hx']
      abel
    · rintro ⟨z, rfl⟩
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      exact ⟨π n z, rfl⟩
  have hcardQ : ∀ n, v ≤ n → Nat.card (tb ℓ φ.ker n) = ℓ ^ v := by
    intro n hn
    have := finite_tb r hcard n
    rw [← Nat.card_congr (kerPhiNEquiv φ n), ← card_quot_range_eq_card_ker, ← hv,
      ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective (Ψ n) (hΨsurj n)).toEquiv,
      hker n hn]
    rfl
  -- the `ℓ`-part of `#ker φ`
  set K := φ.ker
  have hstab : tb ℓ K v = tb ℓ K (v + 1) := by
    haveI : Finite (tb ℓ K (v + 1)) := inferInstance
    refine AddSubgroup.eq_of_le_of_card_ge (fun k hk => ?_) ?_
    · rw [mem_tb] at hk ⊢
      rw [pow_succ', mul_smul, hk, smul_zero]
    · rw [hcardQ v le_rfl, hcardQ (v + 1) (Nat.le_succ v)]
  have hcop : ℓ.Coprime (tb ℓ K v).index := by
    rw [Nat.Prime.coprime_iff_not_dvd hℓ.out]
    intro hdvd
    haveI : Fintype (K ⧸ tb ℓ K v) := Fintype.ofFinite _
    rw [AddSubgroup.index, Nat.card_eq_fintype_card] at hdvd
    obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card ℓ hdvd
    obtain ⟨k, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    have hk1 : ℓ • k ∈ tb ℓ K v := by
      rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_nsmul]
      have := addOrderOf_nsmul_eq_zero (QuotientAddGroup.mk' (tb ℓ K v) k)
      rwa [hq] at this
    have hk2 : k ∈ tb ℓ K (v + 1) := by
      rw [mem_tb] at hk1 ⊢
      rw [pow_succ, mul_smul]
      exact hk1
    rw [← hstab] at hk2
    have : QuotientAddGroup.mk' (tb ℓ K v) k = 0 := (QuotientAddGroup.eq_zero_iff _).mpr hk2
    rw [this, addOrderOf_zero] at hq
    exact hℓ.out.one_lt.ne hq
  have hK : Nat.card K = ℓ ^ v * (tb ℓ K v).index := by
    rw [← hcardQ v le_rfl, AddSubgroup.card_mul_index]
  have hdet := norm_det_eq_inv_card F hF
  rw [hdet, hv, hK, Nat.cast_mul, norm_mul, PadicInt.norm_natCast_eq_one_iff.mpr hcop, mul_one]
  push_cast
  rw [norm_pow, PadicInt.norm_p, inv_pow]

end Count

end ZInQ.Contrib.OneProof.DegDet.TateIndex
