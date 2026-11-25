import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelIdealTate

/-! The placed level-`N` Hom ideal is a locally principal left ideal of the
enhanced reference order (tex 9136–9142). Away from `N` this is the level-one
principality of the placement. At a prime `p ∣ N` (so `p ≠ q`), an isomorphism
of integral Tate chains `β : T_p E ≃ T_p E₀` generates the completed level
lattice over the completed enhanced order. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {a b : ℚ} {E₀ E : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

theorem orderOf_primary_pow {G : Type*} [Group G] (Q : G) (N p : ℕ) [Fact p.Prime]
    (hN : N ≠ 0) (hQ : orderOf Q = N) :
    orderOf (Q ^ (N / p ^ N.factorization p)) = p ^ N.factorization p := by
  set n := N.factorization p
  set r := N / p ^ n
  have hn : N = r * p ^ n := by
    rw [mul_comm]
    exact (Nat.ordProj_mul_ordCompl_eq_self N p).symm
  have hr₀ : r ≠ 0 := fun h => hN (by simp [hn, h])
  rw [orderOf_pow_of_dvd hr₀ (by rw [hQ, hn]; exact dvd_mul_right _ _), hQ, hn,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hr₀)]

theorem mem_completion_iff (R : Order a b) (p : ℕ) [Fact p.Prime] (s : Bp p a b) :
    s ∈ R.completion p ↔ s ∈ localLattice p R.lattice := by
  rw [← R.completion_toSubmodule]
  rfl

set_option maxHeartbeats 800000 in
/-- At a prime dividing the level, the placed level ideal is principal over
the completed enhanced order. -/
theorem levelIdeal_locallyPrincipal_tate (P : HomPlacement S j E) (hE : E.dim = 1)
    (hE₀ : E₀.dim = 1) (N : ℕ) (hN : N ≠ 0) (Pt : E.Pt k) (hPt : orderOf Pt = N)
    (P₀ : E₀.Pt k) (hP₀ : orderOf P₀ = N)
    (hC₀ : ∀ x ∈ Subgroup.zpowers P₀, x ^ N = 1) (hC : ∀ x ∈ Subgroup.zpowers Pt, x ^ N = 1)
    (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0) (hpN : p ∣ N) :
    ∃ u : (Bp p a b)ˣ,
      (localLattice p (levelIdeal P (Subgroup.zpowers P₀) hN hC₀ (Subgroup.zpowers Pt) hC).lattice :
          Set (Bp p a b)) =
        (fun x : Bp p a b => x * (u : Bp p a b)) ''
          ((levelOrderOfEndOrder S j (Subgroup.zpowers P₀) N hN hC₀).completion p :
            Set (Bp p a b)) := by
  set S' := levelOrderOfEndOrder S j (Subgroup.zpowers P₀) N hN hC₀ with hS'
  set n := N.factorization p with hn_def
  set r := N / p ^ n with hr_def
  have hn : 0 < n := (Fact.out : p.Prime).factorization_pos_of_dvd hN hpN
  -- integral Tate comparisons
  have hfull := span_tateHom_eq_top P hp hE hE₀
  let bE₀ := S.basis.map j.symm.toAddEquiv.toIntLinearEquiv
  have hfull₀ : Submodule.span ℤ_[p] (Set.range (tateHom p E₀ E₀)) = ⊤ :=
    span_homT_eq_top_of_basis p 4 hp bE₀ (tateHomBasisFour hp hE₀ hE₀)
  have hM := span_levelHom_cyclic p hp N hN Pt hPt P₀ hP₀ hfull
  have hM₀ := span_levelHom_cyclic p hp N hN P₀ hP₀ P₀ hP₀ hfull₀
  simp only at hM hM₀
  rw [← hn_def, ← hr_def] at hM hM₀
  set U := levelPointsToClosure E Pt ^ r with hU_def
  set U₀ := levelPointsToClosure E₀ P₀ ^ r with hU₀_def
  set X := tateLevelPreimage E p n (Subgroup.zpowers U) with hX
  set Y := tateLevelPreimage E₀ p n (Subgroup.zpowers U₀) with hY
  have hQ : orderOf (levelPointsToClosure E Pt) = N :=
    (orderOf_injective (levelPointsToClosure E) (levelPointsToClosure_injective E) Pt).trans hPt
  have hQ₀ : orderOf (levelPointsToClosure E₀ P₀) = N :=
    (orderOf_injective (levelPointsToClosure E₀) (levelPointsToClosure_injective E₀) P₀).trans hP₀
  have hUo : orderOf U = p ^ n := orderOf_primary_pow _ N p hN hQ
  have hU₀o : orderOf U₀ = p ^ n := orderOf_primary_pow _ N p hN hQ₀
  -- chain bases and the chain isomorphism
  obtain ⟨eE, heE⟩ := exists_tateLevelPreimage_standard p hp n hn U hUo
    (nonempty_tateBasis p hp E hE).some
  obtain ⟨eE₀, heE₀⟩ := exists_tateLevelPreimage_standard p hp n hn U₀ hU₀o
    (nonempty_tateBasis p hp E₀ hE₀).some
  let β : E.T p ≃ₗ[ℤ_[p]] E₀.T p := eE.trans eE₀.symm
  have hβ (y : E.T p) : y ∈ X ↔ β y ∈ Y := by
    rw [heE, heE₀]
    change _ ↔ eE₀ (eE₀.symm (eE y)) ∈ _
    rw [LinearEquiv.apply_symm_apply]
  let Ψ := tateToLocal P hp hE hE₀
  let w := Ψ β.toLinearMap
  let Λ := localLattice p (levelLattice P (Subgroup.zpowers Pt) (Subgroup.zpowers P₀))
  -- the completed level lattice is the image of the Tate level maps
  have hΛ : Λ = (Submodule.span ℤ_[p] (tateHom p E E₀ ''
      (levelHom (L := k) (Subgroup.zpowers Pt) (Subgroup.zpowers P₀) : Set (Hom E E₀)))).map Ψ := by
    change Submodule.span ℤ_[p] (toLocal p '' _) = _
    rw [Submodule.map_span, Set.image_image]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
      exact ⟨α, hα, tateToLocal_tateHom P hp hE hE₀ α⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨P.emb α, ⟨α, hα, rfl⟩, (tateToLocal_tateHom P hp hE hE₀ α).symm⟩
  have hmemΛ (y : Bp p a b) : y ∈ Λ ↔ ∃ φ : E.T p →ₗ[ℤ_[p]] E₀.T p,
      Set.MapsTo (⇑φ) X Y ∧ Ψ φ = y := by
    rw [hΛ]
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      have hφ' : φ ∈ (Submodule.span ℤ_[p] (tateHom p E E₀ ''
          (levelHom (L := k) (Subgroup.zpowers Pt) (Subgroup.zpowers P₀) : Set (Hom E E₀))) :
            Set (E.T p →ₗ[ℤ_[p]] E₀.T p)) := hφ
      rw [hM] at hφ'
      exact ⟨φ, hφ', rfl⟩
    · rintro ⟨φ, hφ, rfl⟩
      refine ⟨φ, ?_, rfl⟩
      have hφ' : φ ∈ (Submodule.span ℤ_[p] (tateHom p E E₀ ''
          (levelHom (L := k) (Subgroup.zpowers Pt) (Subgroup.zpowers P₀) : Set (Hom E E₀))) :
            Set (E.T p →ₗ[ℤ_[p]] E₀.T p)) := by
        rw [hM]
        exact hφ
      exact hφ'
  -- the left action of the completed enhanced order
  have hact : ∀ s ∈ S'.completion p, ∀ y ∈ Λ, s * y ∈ Λ := by
    intro s hs y hy
    rw [mem_completion_iff] at hs
    induction hs using Submodule.span_induction with
    | mem s hs =>
      obtain ⟨_, ⟨o, ho, rfl⟩, rfl⟩ := hs
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨_, ⟨α, hα, rfl⟩, rfl⟩ := hy
        refine Submodule.subset_span ⟨P.emb (postcomp o α), ⟨postcomp o α,
          postcomp_mem_levelHom ho hα, rfl⟩, ?_⟩
        change toLocal p (P.emb (postcomp o α)) = toLocal p (j o : B a b) * toLocal p (P.emb α)
        rw [P.map_postcomp, map_mul]
      | zero => rw [mul_zero]; exact Λ.zero_mem
      | add y y' _ _ hy hy' => rw [mul_add]; exact Λ.add_mem hy hy'
      | smul c y _ hy => rw [mul_smul_comm]; exact Λ.smul_mem c hy
    | zero => rw [zero_mul]; exact Λ.zero_mem
    | add s s' _ _ hs hs' => rw [add_mul]; exact Λ.add_mem hs hs'
    | smul c s _ hs => rw [smul_mul_assoc]; exact Λ.smul_mem c hs
  -- the Tate level endomorphisms are realized by the completed enhanced order
  have hreal : ∀ ψ ∈ Submodule.span ℤ_[p] (tateHom p E₀ E₀ ''
      (levelEnd E₀ (Subgroup.zpowers P₀) : Set E₀.End)),
      ∃ s ∈ S'.completion p, ∀ φ : E.T p →ₗ[ℤ_[p]] E₀.T p, Ψ (ψ.comp φ) = s * Ψ φ := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ hψ =>
      obtain ⟨o, ho, rfl⟩ := hψ
      refine ⟨toLocal p (j o : B a b), Algebra.subset_adjoin ⟨_, ⟨o, ho, rfl⟩, rfl⟩,
        fun φ => tateToLocal_comp P hp hE hE₀ o φ⟩
    | zero => exact ⟨0, (S'.completion p).zero_mem, fun φ => by simp⟩
    | add ψ ψ' _ _ hψ hψ' =>
      obtain ⟨s, hs, h⟩ := hψ
      obtain ⟨s', hs', h'⟩ := hψ'
      exact ⟨s + s', (S'.completion p).add_mem hs hs', fun φ => by
        rw [LinearMap.add_comp, map_add, h, h', add_mul]⟩
    | smul c ψ _ hψ =>
      obtain ⟨s, hs, h⟩ := hψ
      exact ⟨c • s, (S'.completion p).smul_mem hs c, fun φ => by
        rw [LinearMap.smul_comp, map_smul, h, smul_mul_assoc]⟩
  have hβM : Set.MapsTo (⇑β.toLinearMap) X Y := fun y hy => (hβ y).mp hy
  have hw : w ∈ Λ := (hmemΛ w).mpr ⟨β.toLinearMap, hβM, rfl⟩
  have hset : (Λ : Set (Bp p a b)) =
      (fun x : Bp p a b => x * w) '' (S'.completion p : Set (Bp p a b)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨φ, hφ, rfl⟩ := (hmemΛ y).mp hy
      let ψ := φ.comp β.symm.toLinearMap
      have hψ : ψ ∈ Submodule.span ℤ_[p] (tateHom p E₀ E₀ ''
          (levelEnd E₀ (Subgroup.zpowers P₀) : Set E₀.End)) := by
        have h : ψ ∈ (Submodule.span ℤ_[p] (tateHom p E₀ E₀ ''
            (levelHom (L := k) (Subgroup.zpowers P₀) (Subgroup.zpowers P₀) :
              Set (Hom E₀ E₀))) : Set (E₀.T p →ₗ[ℤ_[p]] E₀.T p)) := by
          rw [hM₀]
          intro y' hy'
          apply hφ
          rw [hβ]
          change β (β.symm y') ∈ Y
          rw [LinearEquiv.apply_symm_apply]
          exact hy'
        exact h
      obtain ⟨s, hs, h⟩ := hreal ψ hψ
      refine ⟨s, hs, ?_⟩
      have hc : ψ.comp β.toLinearMap = φ := by
        ext x
        simp [ψ]
      change s * Ψ β.toLinearMap = Ψ φ
      rw [← h, hc]
    · rintro ⟨s, hs, rfl⟩
      exact hact s hs w hw
  -- the generator is a unit
  have hfullΛ := localLattice_full (⟨p, Fact.out⟩ : Prime)
    (levelIdeal P (Subgroup.zpowers P₀) hN hC₀ (Subgroup.zpowers Pt) hC).full
  have h1 : (1 : Bp p a b) ∈ Submodule.span ℚ_[p] (Λ : Set (Bp p a b)) := by
    have ht := hfullΛ.span_eq_top
    change Submodule.span ℚ_[p] (Λ : Set (Bp p a b)) = ⊤ at ht
    rw [ht]
    exact Submodule.mem_top
  have hle : Submodule.span ℚ_[p] (Λ : Set (Bp p a b)) ≤
      LinearMap.range (LinearMap.mulRight ℚ_[p] w) := by
    apply Submodule.span_le.mpr
    intro y hy
    rw [hset] at hy
    obtain ⟨s, -, rfl⟩ := hy
    exact ⟨s, rfl⟩
  obtain ⟨v, hv⟩ := hle h1
  obtain ⟨u, hu⟩ := exists_unit_of_left_inverse p (show v * w = 1 from hv)
  refine ⟨u, ?_⟩
  change (Λ : Set (Bp p a b)) = _
  rw [hset, hu]

end ZInQ.Manuscript.RC.HCMV21
