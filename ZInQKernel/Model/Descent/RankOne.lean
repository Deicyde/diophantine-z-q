import ZInQKernel.Model.Descent.Torsion
import ZInQKernel.Model.Descent.MordellWeil

/-!
# `E(K₀)` has rank one

Blueprint: `model/descent/rank-one.md`.

Assuming `E(K₀)` finitely generated (the Mordell–Weil hypothesis, proved in
`ZInQKernel/Model/Descent/MordellWeil.lean`), `C(K₀) = ℤ S ⊕ C(K₀)[2]` for a point `S` of
infinite order. By the structure theorem `C(K₀) ≃ ℤⁿ × D` with `D` finite; `D` is the torsion,
which is `C(K₀)[2]` of order four, so `[C(K₀) : 2C(K₀)] = 2ⁿ · 4`, and the descent index
`8` forces `n = 1`.
-/

namespace ZInQ

open WeierstrassCurve WeierstrassCurve.Affine

section General

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem nsmul_range_map_equiv (f : G ≃+ H) (k : ℕ) :
    (nsmulAddMonoidHom (α := G) k).range.map (f : G →+ H) =
      (nsmulAddMonoidHom (α := H) k).range := by
  ext y
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨f x, by simp⟩
  · rintro ⟨y', rfl⟩
    exact ⟨k • f.symm y', ⟨f.symm y', rfl⟩, by simp⟩

theorem index_nsmul_range_congr (f : G ≃+ H) (k : ℕ) :
    (nsmulAddMonoidHom (α := G) k).range.index = (nsmulAddMonoidHom (α := H) k).range.index := by
  rw [← nsmul_range_map_equiv f k]
  exact (AddSubgroup.index_map_equiv _ f).symm

theorem nsmul_range_prod (k : ℕ) :
    (nsmulAddMonoidHom (α := G × H) k).range =
      (nsmulAddMonoidHom (α := G) k).range.prod (nsmulAddMonoidHom (α := H) k).range := by
  ext ⟨a, b⟩
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_prod, Prod.ext_iff,
    Prod.smul_fst, Prod.smul_snd, Prod.exists]
  constructor
  · rintro ⟨x, y, h1, h2⟩; exact ⟨⟨x, h1⟩, ⟨y, h2⟩⟩
  · rintro ⟨⟨x, h1⟩, ⟨y, h2⟩⟩; exact ⟨x, y, h1, h2⟩

theorem index_nsmul_range_pi_int (n k : ℕ) :
    (nsmulAddMonoidHom (α := Fin n → ℤ) k).range.index = k ^ n := by
  have : (nsmulAddMonoidHom (α := Fin n → ℤ) k).range =
      AddSubgroup.pi Set.univ (fun _ => AddSubgroup.zmultiples (k : ℤ)) := by
    ext f
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_pi, Set.mem_univ,
      true_implies, Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨g, rfl⟩ i
      exact ⟨g i, by simp⟩
    · intro h
      choose g hg using h
      exact ⟨g, funext fun i => by simp [hg i]⟩
  rw [this, AddSubgroup.index_pi]
  simp

end General

theorem cT_distinct : (0 : curveC.toAffine.Point) ∉ ({cT0, cTdelta, cTnegdelta} : Set _) ∧
    cT0 ∉ ({cTdelta, cTnegdelta} : Set curveC.toAffine.Point) ∧ cTdelta ≠ cTnegdelta := by
  have hd := delta_ne_zero
  have hd2 : delta ≠ -delta := by
    intro h; apply hd; have : (2 : K0) * delta = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left two_ne_zero
  refine ⟨?_, ?_, ?_⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨(Point.some_ne_zero _).symm, (Point.some_ne_zero _).symm, (Point.some_ne_zero _).symm⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, cT0, cTdelta, cTnegdelta,
      Point.mk, Point.some.injEq, and_true]
    exact ⟨fun h => hd h.symm, fun h => hd (neg_eq_zero.mp h.symm)⟩
  · simp only [cTdelta, cTnegdelta, Point.mk, ne_eq, Point.some.injEq, and_true]
    exact hd2

theorem card_two_torsion_C : Nat.card {T : curveC.toAffine.Point // 2 • T = 0} = 4 := by
  obtain ⟨h1, h2, h3⟩ := cT_distinct
  rw [Nat.card_congr (Equiv.subtypeEquivRight curveC_two_torsion)]
  change Nat.card ↥({0, cT0, cTdelta, cTnegdelta} : Set curveC.toAffine.Point) = 4
  rw [Nat.card_coe_set_eq, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
    Set.ncard_pair h3]

/-- The torsion subgroup of `C(K₀)` has order four. -/
theorem card_torsion_C : Nat.card (AddCommGroup.torsion curveC.toAffine.Point) = 4 := by
  rw [← card_two_torsion_C]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun T =>
    ⟨two_nsmul_eq_zero_of_isOfFinAddOrder_C, fun h => isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨2, by norm_num, h⟩⟩)

/-- The torsion subgroup of `E(K₀)` has order four. -/
theorem card_torsion_E : Nat.card (AddCommGroup.torsion genCurve.toAffine.Point) = 4 := by
  rw [← card_two_torsion_C]
  refine Nat.card_congr ((Equiv.subtypeEquivRight fun T =>
    isOfFinAddOrder_iff_two_nsmul_eq_zero T).trans ?_)
  exact theta.toEquiv.subtypeEquiv fun P => (two_nsmul_theta_eq_zero_iff P).symm

/-- **`C(K₀)` has rank one** (under the Mordell–Weil hypothesis): there is a point `S` of
infinite order such that every `P ∈ C(K₀)` is uniquely `[m] S + T` with `T ∈ C(K₀)[2]`. -/
theorem exists_generator_C (hMW : MordellWeilE) :
    ∃ S : curveC.toAffine.Point, ¬IsOfFinAddOrder S ∧
      ∀ P, ∃! mT : ℤ × {T : curveC.toAffine.Point // 2 • T = 0}, P = mT.1 • S + mT.2 := by
  have : AddGroup.FG genCurve.toAffine.Point := hMW
  have : AddGroup.FG curveC.toAffine.Point :=
    AddGroup.fg_of_surjective (f := (theta : genCurve.toAffine.Point →+ curveC.toAffine.Point))
      theta.surjective
  obtain ⟨n, ι, hι, p, hp, e, ⟨φ⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod curveC.toAffine.Point
  have : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  have : Finite (DirectSum ι fun i => ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  -- `D` is killed by `2`
  have hD2 : ∀ d : DirectSum ι (fun i => ZMod (p i ^ e i)), 2 • d = 0 := by
    intro d
    obtain ⟨k, hk, hkd⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp (isOfFinAddOrder_of_finite d)
    have hfin : IsOfFinAddOrder (φ.symm (0, d)) :=
      isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨k, hk, by rw [← map_nsmul, Prod.smul_mk, smul_zero,
        hkd, Prod.mk_zero_zero, map_zero]⟩
    have := congrArg φ (two_nsmul_eq_zero_of_isOfFinAddOrder_C hfin)
    rw [map_nsmul, AddEquiv.apply_symm_apply, map_zero, Prod.smul_mk, Prod.mk_eq_zero] at this
    exact this.2
  -- `ℤⁿ` has no `2`-torsion
  have hA2 : ∀ a : Fin n →₀ ℤ, 2 • a = 0 → a = 0 := by
    intro a ha
    ext i
    have : (2 : ℤ) * a i = 0 := by
      simpa [Finsupp.smul_apply, nsmul_eq_mul] using congrArg (fun f => f i) ha
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    omega
  -- `D ≃ C(K₀)[2]`, of order four
  have hcardD : Nat.card (DirectSum ι fun i => ZMod (p i ^ e i)) = 4 := by
    rw [← card_two_torsion_C]
    refine Nat.card_congr
      { toFun := fun d => ⟨φ.symm (0, d), by rw [← map_nsmul, Prod.smul_mk, smul_zero, hD2,
          Prod.mk_zero_zero, map_zero]⟩
        invFun := fun T => (φ T.1).2
        left_inv := fun d => by simp
        right_inv := fun T => by
          apply Subtype.ext
          have h2 := congrArg φ T.2
          rw [map_nsmul, map_zero] at h2
          have ha : (φ T.1).1 = 0 := hA2 _ (by simpa using congrArg Prod.fst h2)
          show φ.symm (0, (φ T.1).2) = T.1
          rw [← ha, Prod.mk.eta, AddEquiv.symm_apply_apply] }
  -- the index
  have hidx : (nsmulAddMonoidHom (α := curveC.toAffine.Point) 2).range.index = 8 := by
    rw [← index_nsmul_range_congr theta]; exact index_two_E
  rw [index_nsmul_range_congr φ, nsmul_range_prod, AddSubgroup.index_prod] at hidx
  have h2D : (nsmulAddMonoidHom (α := DirectSum ι fun i => ZMod (p i ^ e i)) 2).range = ⊥ := by
    ext d
    simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply, AddSubgroup.mem_bot]
    exact ⟨fun ⟨x, hx⟩ => hx ▸ hD2 x, fun h => ⟨0, by rw [h, smul_zero]⟩⟩
  rw [h2D, AddSubgroup.index_bot, hcardD,
    index_nsmul_range_congr (Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv,
    index_nsmul_range_pi_int] at hidx
  have hn : n = 1 := by
    have h2n : 2 ^ n = 2 ^ 1 := by omega
    exact Nat.pow_right_injective (le_refl 2) h2n
  subst hn
  -- the generator
  set S := φ.symm (Finsupp.single 0 1, 0) with hS
  have hφS : φ S = (Finsupp.single 0 1, 0) := by rw [hS, AddEquiv.apply_symm_apply]
  refine ⟨S, ?_, ?_⟩
  · intro hfin
    obtain ⟨k, hk, hkS⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hfin
    have := congrArg (fun P => (φ P).1 0) hkS
    simp only [map_nsmul, hφS, Prod.smul_mk, map_zero, Prod.fst_zero, Finsupp.coe_zero,
      Pi.zero_apply, Finsupp.smul_apply, Finsupp.single_eq_same, nsmul_eq_mul, mul_one] at this
    norm_num at this
    omega
  · intro P
    have hT : 2 • φ.symm (0, (φ P).2) = 0 := by
      rw [← map_nsmul, Prod.smul_mk, smul_zero, hD2, Prod.mk_zero_zero, map_zero]
    refine ⟨((φ P).1 0, ⟨φ.symm (0, (φ P).2), hT⟩), ?_, ?_⟩
    · apply φ.injective
      rw [map_add, map_zsmul, hφS, AddEquiv.apply_symm_apply, Prod.smul_mk, smul_zero,
        Prod.mk_add_mk, add_zero, zero_add]
      have h1 : (φ P).1 = (φ P).1 0 • Finsupp.single 0 1 :=
        Finsupp.ext fun i => by fin_cases i; simp
      exact Prod.ext h1 rfl
    · rintro ⟨m, T⟩ hPm
      have hPm' := congrArg φ hPm
      rw [map_add, map_zsmul, hφS, Prod.smul_mk, smul_zero, Prod.mk_add_mk, zero_add] at hPm'
      have hT1 : (φ T.1).1 = 0 := hA2 _ (by
        have := congrArg (fun Q => (φ Q).1) T.2
        simpa using this)
      rw [hT1, add_zero] at hPm'
      have hm : (φ P).1 0 = m := by
        rw [hPm']; simp
      have hd : (φ P).2 = (φ T.1).2 := by rw [hPm']
      refine Prod.ext hm.symm (Subtype.ext ?_)
      show T.1 = φ.symm (0, (φ P).2)
      rw [eq_comm, AddEquiv.symm_apply_eq, hd, ← hT1]

/-- The same for `E(K₀)`: `E(K₀) = ℤ θ⁻¹(S) ⊕ E(K₀)[2]`. -/
theorem exists_generator_E (hMW : MordellWeilE) :
    ∃ S : genCurve.toAffine.Point, ¬IsOfFinAddOrder S ∧
      ∀ P, ∃! mT : ℤ × {T : genCurve.toAffine.Point // 2 • T = 0}, P = mT.1 • S + mT.2 := by
  obtain ⟨S, hS, h⟩ := exists_generator_C hMW
  refine ⟨theta.symm S, fun hfin => hS ?_, fun P => ?_⟩
  · obtain ⟨k, hk, hkS⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hfin
    exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr
      ⟨k, hk, by rw [← theta.apply_symm_apply S, ← map_nsmul, hkS, map_zero]⟩
  obtain ⟨⟨m, T⟩, hP, huniq⟩ := h (theta P)
  have hT' : 2 • theta.symm T.1 = 0 := by rw [← map_nsmul, T.2, map_zero]
  refine ⟨(m, ⟨theta.symm T, hT'⟩), ?_, ?_⟩
  · apply theta.injective
    simp only [map_add, map_zsmul, AddEquiv.apply_symm_apply]
    exact hP
  · rintro ⟨m', T'⟩ hP'
    have hT'' : 2 • theta T'.1 = 0 := by rw [← map_nsmul, T'.2, map_zero]
    have := huniq (m', ⟨theta T', hT''⟩) (by
      simp only
      rw [hP', map_add, map_zsmul, AddEquiv.apply_symm_apply])
    simp only [Prod.mk.injEq] at this
    refine Prod.ext this.1 (Subtype.ext ?_)
    simp only
    rw [← this.2, AddEquiv.symm_apply_apply]

/-- Unconditionally, using `mordellWeilE`. -/
theorem exists_generator_C' :
    ∃ S : curveC.toAffine.Point, ¬IsOfFinAddOrder S ∧
      ∀ P, ∃! mT : ℤ × {T : curveC.toAffine.Point // 2 • T = 0}, P = mT.1 • S + mT.2 :=
  exists_generator_C mordellWeilE

end ZInQ
