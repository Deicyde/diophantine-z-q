import ZInQKernel.Contrib.OneProof.RC.HCMV21.EndPlacement
import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelIdealPrincipal

/-! The level endomorphisms of an enhanced curve are the right order of its
placed level ideal (tex 8467–8468). For `x` in the right order of the placed
level ideal, `N x` lies in the right order of the level-one ideal; a placement
moved by a right unit to an integral ideal containing an integer prime to `q`
(`LeftIdeal.exists_integral_primeTo`) lets the order candidate (Voight,
Cor. 42.3.7, ring statement from Lemma 42.2.9, in separable scope) produce
`γ'` with `γ' ↦ N x`. At every prime `p ∣ N` a chain isomorphism of the Tate
modules shows that `T_p γ'` is divisible by `p^{v_p(N)}`, so `γ' = N γ`
(divisibility descends from the Tate module at primes invertible in `k`).
The same chain isomorphism shows that `γ` preserves each primary part of the
level subgroup, hence the subgroup. All steps after the candidate are Lean
proofs. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

section Arith

/-- Divisibility by every primary part of `N` gives divisibility by `N`. -/
theorem exists_nsmul_of_forall_primary {G : Type*} [AddCommGroup G] (f : G) :
    ∀ N : ℕ, N ≠ 0 →
      (∀ p : ℕ, p.Prime → p ∣ N → ∃ g : G, f = (p ^ N.factorization p : ℕ) • g) →
        ∃ g : G, f = N • g := by
  intro N
  induction N using Nat.recOnPrimeCoprime with
  | zero => intro hN; exact absurd rfl hN
  | prime_pow p n hp =>
    intro _ h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨f, by simp⟩
    · obtain ⟨g, hg⟩ := h p hp (dvd_pow_self p hn.ne')
      have hf : (p ^ n).factorization p = n := by
        rw [Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
      rw [hf] at hg
      exact ⟨g, hg⟩
  | coprime a b ha hb hab iha ihb =>
    intro _ h
    have hpart (c d : ℕ) (hcd : (c * d) = a * b) (hc : c.Coprime d) (hc0 : 0 < c) :
        ∀ p : ℕ, p.Prime → p ∣ c → ∃ g : G, f = (p ^ c.factorization p : ℕ) • g := by
      intro p hp hpc
      obtain ⟨g, hg⟩ := h p hp (hcd ▸ dvd_mul_of_dvd_left hpc d)
      refine ⟨g, ?_⟩
      have hpd : ¬ p ∣ d := fun hpd => hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hc hpc hpd)
      rwa [← hcd, Nat.factorization_mul_apply_of_coprime hc,
        Nat.factorization_eq_zero_of_not_dvd hpd, add_zero] at hg
    obtain ⟨g₁, hg₁⟩ := iha (by omega) (hpart a b rfl hab (by omega))
    obtain ⟨g₂, hg₂⟩ := ihb (by omega) (hpart b a (mul_comm b a) hab.symm (by omega))
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hab
    refine ⟨u • g₂ + v • g₁, ?_⟩
    have hf₁ : f = (a : ℤ) • g₁ := by rw [natCast_zsmul]; exact hg₁
    have hf₂ : f = (b : ℤ) • g₂ := by rw [natCast_zsmul]; exact hg₂
    rw [← natCast_zsmul, smul_add, smul_smul, smul_smul]
    have e₁ : ((a * b : ℕ) : ℤ) * u = u * a * b := by push_cast; ring
    have e₂ : ((a * b : ℕ) : ℤ) * v = v * b * a := by push_cast; ring
    rw [e₁, e₂, mul_smul, ← hf₂, mul_smul (v * b), ← hf₁, ← add_smul, huv, one_smul]

/-- An element of order dividing `N` lies in a subgroup once each of its
primary components does. -/
theorem mem_of_primary_pow_mem {G : Type*} [CommGroup G] (H : Subgroup G) (Q : G) (N : ℕ)
    (hN : N ≠ 0) (hQ : Q ^ N = 1)
    (h : ∀ p : ℕ, p.Prime → p ∣ N → Q ^ (N / p ^ N.factorization p) ∈ H) : Q ∈ H := by
  let Q' : G ⧸ H := (Q : G ⧸ H)
  have hdN : orderOf Q' ∣ N := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, hQ, QuotientGroup.mk_one])
  by_contra hQH
  have hne : orderOf Q' ≠ 1 := by
    intro h1
    rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    exact hQH h1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpN := hpd.trans hdN
  have hd : orderOf Q' ∣ N / p ^ N.factorization p := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact h p hp hpN)
  exact Nat.not_dvd_ordCompl hp hN (hpd.trans hd)

end Arith

section Tate

variable {k : Type} [Field k] [IsAlgClosed k] {a b : ℚ} {E₀ E : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

/-- The `p`-primary level preimage in the Tate module. -/
def primaryPreimage (A : PkgI3.AbVar k) (P : A.Pt k) (N p : ℕ) [Fact p.Prime] : Set (A.T p) :=
  tateLevelPreimage A p (N.factorization p)
    (Subgroup.zpowers (levelPointsToClosure A P ^ (N / p ^ N.factorization p)))

theorem mem_span_levelHom_primary {A B : PkgI3.AbVar k} (p : ℕ) [Fact p.Prime]
    (hp : (p : k) ≠ 0) (N : ℕ) (hN : N ≠ 0) (PA : A.Pt k) (hPA : orderOf PA = N) (PB : B.Pt k)
    (hPB : orderOf PB = N) (hfull : Submodule.span ℤ_[p] (Set.range (tateHom p A B)) = ⊤)
    (φ : A.T p →ₗ[ℤ_[p]] B.T p) :
    φ ∈ Submodule.span ℤ_[p] (tateHom p A B '' (levelHom (L := k) (Subgroup.zpowers PA)
      (Subgroup.zpowers PB) : Set (Hom A B))) ↔
      Set.MapsTo φ (primaryPreimage A PA N p) (primaryPreimage B PB N p) := by
  have h := span_levelHom_cyclic p hp N hN PA hPA PB hPB hfull
  simp only at h
  exact Set.ext_iff.mp h φ

/-- A chain isomorphism of the integral Tate modules at a prime dividing the
level. -/
theorem exists_chainIso (hE : E.dim = 1) (hE₀ : E₀.dim = 1) (p : ℕ) [Fact p.Prime]
    (hp : (p : k) ≠ 0) (N : ℕ) (hN : N ≠ 0) (hpN : p ∣ N) (Pt : E.Pt k) (hPt : orderOf Pt = N)
    (P₀ : E₀.Pt k) (hP₀ : orderOf P₀ = N) :
    ∃ β : E.T p ≃ₗ[ℤ_[p]] E₀.T p, ∀ y,
      y ∈ primaryPreimage E Pt N p ↔ β y ∈ primaryPreimage E₀ P₀ N p := by
  have hn : 0 < N.factorization p := (Fact.out : p.Prime).factorization_pos_of_dvd hN hpN
  have hQ : orderOf (levelPointsToClosure E Pt) = N :=
    (orderOf_injective (levelPointsToClosure E) (levelPointsToClosure_injective E) Pt).trans hPt
  have hQ₀ : orderOf (levelPointsToClosure E₀ P₀) = N :=
    (orderOf_injective (levelPointsToClosure E₀) (levelPointsToClosure_injective E₀) P₀).trans hP₀
  obtain ⟨eE, heE⟩ := exists_tateLevelPreimage_standard p hp _ hn _
    (orderOf_primary_pow _ N p hN hQ) (nonempty_tateBasis p hp E hE).some
  obtain ⟨eE₀, heE₀⟩ := exists_tateLevelPreimage_standard p hp _ hn _
    (orderOf_primary_pow _ N p hN hQ₀) (nonempty_tateBasis p hp E₀ hE₀).some
  refine ⟨eE.trans eE₀.symm, fun y => ?_⟩
  unfold primaryPreimage
  rw [heE, heE₀]
  change _ ↔ eE₀ (eE₀.symm (eE y)) ∈ _
  rw [LinearEquiv.apply_symm_apply]

/-- The completed comparison is injective: it sends a `ℤ_p`-basis to the
images of a rational basis, which are independent over `ℚ_p`. -/
theorem tateToLocal_injective (P : HomPlacement S j E) (p : ℕ) [Fact p.Prime]
    (hp : (p : k) ≠ 0) (hE : E.dim = 1) (hE₀ : E₀.dim = 1) :
    Function.Injective (tateToLocal P hp hE hE₀) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro φ hφ
  set bT := tatePlacementBasis P hp hE hE₀
  let e := P.ideal.val.full.ratBasis (QuaternionAlgebra.basisOneIJK a 0 b)
  have hemb (i : Fin 4) : P.emb (P.homBasis i) = e i := by
    rw [HomPlacement.homBasis, Module.Basis.map_apply, HomPlacement.emb_latticeEquiv_symm]
    letI := P.ideal.val.full
    exact (Module.Basis.extendOfIsLattice_apply ℚ _ i).symm
  have hΨ : tateToLocal P hp hE hE₀ φ = ∑ i, bT.repr φ i • toLocal p (e i) := by
    conv_lhs => rw [← bT.sum_repr φ]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, tateToLocal, Module.Basis.constr_basis, hemb]
  apply bT.repr.injective
  rw [map_zero]
  ext i
  have h := congrArg (fun v => localCoordinates (⟨p, Fact.out⟩ : Prime) e v i) (hΨ.symm.trans hφ)
  simp only [map_sum, map_zero, Pi.zero_apply] at h
  have hterm (l : Fin 4) : localCoordinates (⟨p, Fact.out⟩ : Prime) e
      (bT.repr φ l • toLocal p (e l)) i = if l = i then (bT.repr φ l : ℚ_[p]) else 0 := by
    rw [← algebraMap_smul ℚ_[p] (bT.repr φ l), map_smul]
    change (algebraMap ℤ_[p] ℚ_[p] (bT.repr φ l) •
      localCoordinates (⟨p, Fact.out⟩ : Prime) e (toLocal (⟨p, Fact.out⟩ : Prime).val (e l))) i = _
    rw [localCoordinates_toLocal, Module.Basis.repr_self]
    by_cases hl : l = i
    · subst hl
      simp
    · simp [hl, Finsupp.single_apply]
  simp only [Finset.sum_apply, hterm, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact_mod_cast h

/-- The completed placed level lattice is the image of the span of the Tate
maps of the level maps. -/
theorem localLattice_levelLattice_eq_map (P : HomPlacement S j E) (p : ℕ) [Fact p.Prime]
    (hp : (p : k) ≠ 0) (hE : E.dim = 1) (hE₀ : E₀.dim = 1) (C : Subgroup (E.Pt k))
    (C₀ : Subgroup (E₀.Pt k)) :
    localLattice p (levelLattice P C C₀) =
      (Submodule.span ℤ_[p] (tateHom p E E₀ ''
        (levelHom (L := k) C C₀ : Set (Hom E E₀)))).map (tateToLocal P hp hE hE₀) := by
  change Submodule.span ℤ_[p] (toLocal p '' _) = _
  rw [Submodule.map_span, Set.image_image]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    exact ⟨α, hα, tateToLocal_tateHom P hp hE hE₀ α⟩
  · rintro ⟨α, hα, rfl⟩
    exact ⟨P.emb α, ⟨α, hα, rfl⟩, (tateToLocal_tateHom P hp hE hE₀ α).symm⟩

/-- **Recovery of the level from the Hom lattice.** If precomposition with
`f : A → B` carries the level maps of `(B, ⟨PtB⟩)` into those of `(A, ⟨PtA⟩)`
(both towards `(E₀, ⟨P₀⟩)`), then `f` carries `⟨PtA⟩` into `⟨PtB⟩`. At each
prime `p ∣ N` a chain isomorphism `T_p B ≃ T_p E₀` shows that `T_p f`
preserves the primary chains; the primary components then assemble. -/
theorem mem_levelHom_of_comp {A B : PkgI3.AbVar k} (PB : HomPlacement S j B)
    (hA : A.dim = 1) (hB : B.dim = 1) (hE₀ : E₀.dim = 1) (N : ℕ) (hN : N ≠ 0)
    (PtA : A.Pt k) (hPtA : orderOf PtA = N) (PtB : B.Pt k) (hPtB : orderOf PtB = N)
    (P₀ : E₀.Pt k) (hP₀ : orderOf P₀ = N) (hpk : ∀ p : ℕ, p.Prime → p ∣ N → (p : k) ≠ 0)
    (hfullA : ∀ (p : ℕ) [Fact p.Prime], (p : k) ≠ 0 →
      Submodule.span ℤ_[p] (Set.range (tateHom p A E₀)) = ⊤)
    (f : Hom A B)
    (hlev : ∀ α ∈ levelHom (L := k) (Subgroup.zpowers PtB) (Subgroup.zpowers P₀),
      homPull f α ∈ levelHom (L := k) (Subgroup.zpowers PtA) (Subgroup.zpowers P₀)) :
    f ∈ levelHom (L := k) (Subgroup.zpowers PtA) (Subgroup.zpowers PtB) := by
  set QA := levelPointsToClosure A PtA with hQAdef
  set QB := levelPointsToClosure B PtB with hQBdef
  have hQA : orderOf QA = N :=
    (orderOf_injective (levelPointsToClosure A) (levelPointsToClosure_injective A) PtA).trans hPtA
  have hQB : orderOf QB = N :=
    (orderOf_injective (levelPointsToClosure B) (levelPointsToClosure_injective B) PtB).trans hPtB
  have hprim : ∀ p : ℕ, p.Prime → p ∣ N →
      QA ^ (N / p ^ N.factorization p) ∈
        (Subgroup.zpowers QB).comap (ptMap (L := AlgebraicClosure k) f) := by
    intro p hp hpN
    haveI : Fact p.Prime := ⟨hp⟩
    have hpk' := hpk p hp hpN
    obtain ⟨β, hβ⟩ := exists_chainIso hB hE₀ p hpk' N hN hpN PtB hPtB P₀ hP₀
    have hfullB := span_tateHom_eq_top PB hpk' hB hE₀
    set MB := Submodule.span ℤ_[p] (tateHom p B E₀ ''
      (levelHom (L := k) (Subgroup.zpowers PtB) (Subgroup.zpowers P₀) : Set (Hom B E₀)))
    set MA := Submodule.span ℤ_[p] (tateHom p A E₀ ''
      (levelHom (L := k) (Subgroup.zpowers PtA) (Subgroup.zpowers P₀) : Set (Hom A E₀)))
    have hcompM : ∀ φ ∈ MB, φ.comp (homT (ℓ := p) f) ∈ MA := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem φ hφ =>
        obtain ⟨α, hα, rfl⟩ := hφ
        change (homT (ℓ := p) α).comp (homT (ℓ := p) f) ∈ MA
        rw [← homT_homPull]
        exact Submodule.subset_span ⟨_, hlev α hα, rfl⟩
      | zero => rw [LinearMap.zero_comp]; exact MA.zero_mem
      | add φ ψ _ _ h1 h2 => rw [LinearMap.add_comp]; exact MA.add_mem h1 h2
      | smul c φ _ h1 => rw [LinearMap.smul_comp]; exact MA.smul_mem c h1
    have hβM := (mem_span_levelHom_primary p hpk' N hN PtB hPtB P₀ hP₀ hfullB
      β.toLinearMap).mpr (fun y hy => (hβ y).mp hy)
    have hfM := (mem_span_levelHom_primary p hpk' N hN PtA hPtA P₀ hP₀ (hfullA p hpk') _).mp
      (hcompM _ hβM)
    have hmaps : Set.MapsTo (homT (ℓ := p) f) (primaryPreimage A PtA N p)
        (primaryPreimage B PtB N p) := by
      intro y hy
      exact (hβ _).mpr (hfM hy)
    set UA := QA ^ (N / p ^ N.factorization p) with hUA
    set UB := QB ^ (N / p ^ N.factorization p) with hUB
    have hUAo : orderOf UA = p ^ N.factorization p := orderOf_primary_pow QA N p hN hQA
    have hCU : ∀ R ∈ Subgroup.zpowers UA, R ^ (p ^ N.factorization p) = 1 := by
      intro R hR
      obtain ⟨m', rfl⟩ := hR
      change (UA ^ m') ^ (p ^ N.factorization p) = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hUAo,
        pow_orderOf_eq_one, one_zpow]
    have hfU := (mem_levelHom_iff_tateLevelPreimage_mapsTo f p (N.factorization p)
      (Subgroup.zpowers UA) (Subgroup.zpowers UB) hCU
      (surjective_nsmul_of_ne_zero A p hpk')).mpr hmaps
    have hUQ : Subgroup.zpowers UB ≤ Subgroup.zpowers QB :=
      Subgroup.zpowers_le.mpr ((Subgroup.zpowers QB).pow_mem (Subgroup.mem_zpowers QB) _)
    exact hUQ (hfU UA (Subgroup.mem_zpowers UA))
  have hQN : QA ^ N = 1 := hQA ▸ pow_orderOf_eq_one QA
  have hQH := mem_of_primary_pow_mem _ QA N hN hQN hprim
  have hlevQ : f ∈ levelHom (Subgroup.zpowers QA) (Subgroup.zpowers QB) := by
    intro R hR
    exact (Subgroup.zpowers_le.mpr hQH) hR
  rw [levelHom_iff_closure, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  exact hlevQ

end Tate

/-- Right stability passes to the completion. -/
theorem localLattice_mul_right_mem {a b : ℚ} (p : ℕ) [Fact p.Prime] {L : Submodule ℤ (B a b)}
    {x : B a b} (hx : ∀ z ∈ L, z * x ∈ L) {y : Bp p a b} (hy : y ∈ localLattice p L) :
    y * toLocal p x ∈ localLattice p L := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, hz, rfl⟩ := hy
    rw [← map_mul]
    exact Submodule.subset_span ⟨_, hx z hz, rfl⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add y y' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
  | smul c y _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h

section Surj

variable {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [Algebra (ZMod q) k]
  [IsAlgClosure (ZMod q) k] {a b : ℚ} {E₀ E : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

set_option maxHeartbeats 800000 in
/-- **Surjectivity of the order map.** Every element of the right order of
the placed level ideal is the action of a level endomorphism. The order
candidate is applied to an integral placement containing an integer prime to
`q` (separable scope). -/
theorem exists_endRight_eq_level (hCor : VoightCor4237) (ha : a < 0) (hb : b < 0)
    (h₀ : IsSupersingular E₀) (hE : IsSupersingular E) (P : HomPlacement S j E)
    (N : ℕ) (hN : N ≠ 0) (hcop : N.Coprime q) (Pt : E.Pt k) (hPt : orderOf Pt = N)
    (P₀ : E₀.Pt k) (hP₀ : orderOf P₀ = N)
    (hC₀ : ∀ x ∈ Subgroup.zpowers P₀, x ^ N = 1) (hC : ∀ x ∈ Subgroup.zpowers Pt, x ^ N = 1)
    (x : B a b)
    (hx : x ∈ (levelIdeal P (Subgroup.zpowers P₀) hN hC₀ (Subgroup.zpowers Pt) hC).rightRing) :
    ∃ gam ∈ levelEnd E (Subgroup.zpowers Pt), P.endRight gam = x := by
  haveI := charP_of_isAlgClosure q k
  haveI := isAlgClosed_of_isAlgClosure q k
  set I := P.ideal.val with hI
  have hpk : ∀ p : ℕ, p.Prime → p ∣ N → (p : k) ≠ 0 := by
    intro p hp hpN hz
    have hd := (CharP.cast_eq_zero_iff k q p).mp hz
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq Fact.out hp).mp hd
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop.symm (hqp ▸ hpN)
  -- `N x` lies in the right order of the level-one ideal
  have hNx : ∀ y ∈ I.lattice, y * ((N : B a b) * x) ∈ I.lattice := by
    intro y hy
    obtain ⟨α, rfl⟩ := P.exists_of_mem hy
    have hmem : P.emb (N • α) * x ∈ levelLattice P (Subgroup.zpowers Pt) (Subgroup.zpowers P₀) :=
      hx _ ⟨N • α, nsmul_mem_levelHom hC α, rfl⟩
    have he : P.emb α * ((N : B a b) * x) = P.emb (N • α) * x := by
      rw [map_nsmul, nsmul_eq_mul, ← mul_assoc, (Nat.cast_commute N (P.emb α)).eq]
    rw [he]
    exact levelLattice_le P hmem
  -- move the placement to an integral ideal containing an integer prime to `q`
  obtain ⟨u, huR, m, hmq, hm⟩ := I.exists_integral_primeTo P.ideal.prop ha hb q
  let P' := P.translate u (I.locallyPrincipal_translate P.ideal.prop u)
  have hP'emb : ∀ α, P'.emb α = P.emb α * u := fun α => rfl
  set x' : B a b := (↑u⁻¹ : B a b) * ((N : B a b) * x) * u with hx'def
  have hx' : x' ∈ P'.ideal.val.rightRing := by
    intro y hy
    change y ∈ (I.translate u).lattice at hy
    change y * x' ∈ (I.translate u).lattice
    rw [LeftIdeal.mem_translate] at hy ⊢
    have he : y * x' * (↑u⁻¹ : B a b) = y * (↑u⁻¹ : B a b) * ((N : B a b) * x) := by
      simp only [hx'def, mul_assoc, Units.mul_inv, mul_one]
    rw [he]
    exact hNx _ hy
  obtain ⟨gam', hgam'⟩ := hCor q k E₀ h₀ a b S j E hE P' huR ⟨m, hmq, hm⟩ x' hx'
  have hgam'N : ∀ α, P.emb (homPull gam' α) = P.emb α * ((N : B a b) * x) := by
    intro α
    have h := hgam' α
    rw [hP'emb, hP'emb] at h
    have h2 := congrArg (· * (↑u⁻¹ : B a b)) h
    simpa only [hx'def, mul_assoc, Units.mul_inv, mul_one, Units.mul_inv_cancel_left] using h2
  -- divisibility of `γ'` at every prime dividing the level
  have hdivp : ∀ p : ℕ, p.Prime → p ∣ N →
      ∃ g : E.End, gam' = (p ^ N.factorization p : ℕ) • g := by
    intro p hp hpN
    haveI : Fact p.Prime := ⟨hp⟩
    have hpk' := hpk p hp hpN
    have hNr : N = p ^ N.factorization p * (N / p ^ N.factorization p) :=
      (Nat.ordProj_mul_ordCompl_eq_self N p).symm
    obtain ⟨β, hβ⟩ := exists_chainIso hE.1 h₀.1 p hpk' N hN hpN Pt hPt P₀ hP₀
    have hfull := span_tateHom_eq_top P hpk' hE.1 h₀.1
    have hβM := (mem_span_levelHom_primary p hpk' N hN Pt hPt P₀ hP₀ hfull
      β.toLinearMap).mpr (fun y hy => (hβ y).mp hy)
    have hβΛ : tateToLocal P hpk' hE.1 h₀.1 β.toLinearMap ∈
        localLattice p (levelLattice P (Subgroup.zpowers Pt) (Subgroup.zpowers P₀)) := by
      rw [localLattice_levelLattice_eq_map P p hpk' hE.1 h₀.1]
      exact ⟨_, hβM, rfl⟩
    have hβx := localLattice_mul_right_mem p (L := levelLattice P (Subgroup.zpowers Pt)
      (Subgroup.zpowers P₀)) hx hβΛ
    rw [localLattice_levelLattice_eq_map P p hpk' hE.1 h₀.1] at hβx
    obtain ⟨φ₁, -, hφ₁⟩ := hβx
    have hext : (tateToLocal P hpk' hE.1 h₀.1).comp
        ({ toFun := fun φ => φ.comp (homT (ℓ := p) gam')
           map_add' := fun _ _ => LinearMap.add_comp _ _ _
           map_smul' := fun _ _ => LinearMap.smul_comp _ _ _ } :
          (E.T p →ₗ[ℤ_[p]] E₀.T p) →ₗ[ℤ_[p]] (E.T p →ₗ[ℤ_[p]] E₀.T p)) =
        (localMulRight p (toLocal p ((N : B a b) * x))).comp (tateToLocal P hpk' hE.1 h₀.1) := by
      apply LinearMap.ext_on_range hfull
      intro α
      change tateToLocal P hpk' hE.1 h₀.1 ((homT (ℓ := p) α).comp (homT (ℓ := p) gam')) =
        tateToLocal P hpk' hE.1 h₀.1 (tateHom p E E₀ α) * toLocal p ((N : B a b) * x)
      rw [← homT_homPull]
      change tateToLocal P hpk' hE.1 h₀.1 (tateHom p E E₀ (homPull gam' α)) = _
      rw [tateToLocal_tateHom, tateToLocal_tateHom, hgam'N, map_mul]
    have heq : β.toLinearMap.comp (homT (ℓ := p) gam') = N • φ₁ := by
      apply tateToLocal_injective P p hpk' hE.1 h₀.1
      have h1 := LinearMap.congr_fun hext β.toLinearMap
      change tateToLocal P hpk' hE.1 h₀.1 (β.toLinearMap.comp (homT (ℓ := p) gam')) =
        tateToLocal P hpk' hE.1 h₀.1 β.toLinearMap * toLocal p ((N : B a b) * x) at h1
      rw [h1, map_nsmul, hφ₁, map_mul, map_natCast, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
        (Nat.cast_commute N (tateToLocal P hpk' hE.1 h₀.1 β.toLinearMap)).eq]
    refine exists_eq_nsmul_of_primeTo_homT_dvd gam' p _ hpk'
      (fun y => ⟨((N / p ^ N.factorization p : ℕ) : ℤ_[p]) • β.symm (φ₁ y), ?_⟩)
    have h1 := congrArg (fun f : E.T p →ₗ[ℤ_[p]] E₀.T p => β.symm (f y)) heq
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.smul_apply] at h1
    rw [h1, map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p], smul_smul]
    congr 1
    conv_lhs => rw [hNr]
    push_cast
    rfl
  obtain ⟨gam, hgam⟩ := exists_nsmul_of_forall_primary gam' N hN hdivp
  -- `γ` acts by `x`
  have hgamx : P.endRight gam = x := by
    apply P.endRight_eq ha hb
    intro α
    have hl : N • P.emb (homPull gam α) = P.emb (homPull gam' α) := by
      rw [← map_nsmul, ← homPullLeft_apply, ← map_nsmul, homPullLeft_apply, ← hgam]
    have hr : N • (P.emb α * x) = P.emb α * ((N : B a b) * x) := by
      rw [nsmul_eq_mul, ← mul_assoc, ← mul_assoc, (Nat.cast_commute N (P.emb α)).eq]
    have h2 : (N : ℚ) • P.emb (homPull gam α) = (N : ℚ) • (P.emb α * x) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hl, hr, hgam'N]
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hN) h2
  refine ⟨gam, ?_, hgamx⟩
  -- composites with level maps are level maps
  have hlev : ∀ α ∈ levelHom (L := k) (Subgroup.zpowers Pt) (Subgroup.zpowers P₀),
      homPull gam α ∈ levelHom (L := k) (Subgroup.zpowers Pt) (Subgroup.zpowers P₀) := by
    intro α hα
    have hm : P.emb (homPull gam α) ∈ levelLattice P (Subgroup.zpowers Pt) (Subgroup.zpowers P₀) := by
      rw [P.endRight_spec, hgamx]
      exact hx _ ⟨α, hα, rfl⟩
    obtain ⟨β', hβ', hβ'e⟩ := hm
    have hb' : β' = homPull gam α := P.injective hβ'e
    rw [← hb']
    exact hβ'
  have hfullE : ∀ (p : ℕ) [Fact p.Prime], (p : k) ≠ 0 →
      Submodule.span ℤ_[p] (Set.range (tateHom p E E₀)) = ⊤ :=
    fun p _ hp => span_tateHom_eq_top P hp hE.1 h₀.1
  exact mem_levelHom_of_comp P hE.1 hE.1 h₀.1 N hN Pt hPt Pt hPt P₀ hP₀ hpk hfullE gam hlev

end Surj

section Equiv

variable {q : ℕ} [Fact q.Prime] {k : Type} [Field k] [Algebra (ZMod q) k]
  [IsAlgClosure (ZMod q) k] {a b : ℚ} {E₀ E : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

/-- **The order statement for a placement.** The level endomorphisms of
`(E, ⟨Pt⟩)` are isomorphic, through the right action on the placement, to the
right order of the placed level ideal. -/
def levelEndEquivRight (hCor : VoightCor4237) (hT : VoightThm4219)
    (hV : QuaternionRamificationUniqueness) (hq : q % 4 = 3) (ha : a < 0) (hb : b < 0)
    (h₀ : IsSupersingular E₀) (hE : IsSupersingular E) (P : HomPlacement S j E)
    (N : ℕ) (hN : N ≠ 0) (hcop : N.Coprime q) (Pt : E.Pt k) (hPt : orderOf Pt = N)
    (P₀ : E₀.Pt k) (hP₀ : orderOf P₀ = N)
    (hC₀ : ∀ x ∈ Subgroup.zpowers P₀, x ^ N = 1) (hC : ∀ x ∈ Subgroup.zpowers Pt, x ^ N = 1) :
    levelEnd E (Subgroup.zpowers Pt) ≃+*
      (levelIdeal P (Subgroup.zpowers P₀) hN hC₀ (Subgroup.zpowers Pt) hC).rightRing :=
  RingEquiv.ofBijective
    ((P.endRightHom ha hb).comp (levelEnd E (Subgroup.zpowers Pt)).subtype |>.codRestrict _
      (fun gam => P.endRight_mem_levelRight hN hC₀ hC gam.prop))
    ⟨fun gam δ h => by
      haveI := charP_of_isAlgClosure q k
      obtain ⟨SE, ⟨jE⟩, -⟩ := exists_referenceFrame hT hV q hq E hE
      have hq2 : ((2 : ℕ) : k) ≠ 0 := by
        intro hz
        have hd := (CharP.cast_eq_zero_iff k q 2).mp hz
        have h2 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd
        omega
      haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
      apply Subtype.ext
      exact endRight_injective ha hb P hE.1 h₀.1 SE jE 2 hq2 (congrArg Subtype.val h),
     fun ⟨x, hx⟩ => by
      obtain ⟨gam, hgam, hgamx⟩ := exists_endRight_eq_level hCor ha hb h₀ hE P N hN hcop Pt hPt P₀ hP₀
        hC₀ hC x hx
      exact ⟨⟨gam, hgam⟩, Subtype.ext hgamx⟩⟩

theorem levelEndEquivRight_apply (hCor : VoightCor4237) (hT : VoightThm4219)
    (hV : QuaternionRamificationUniqueness) (hq : q % 4 = 3) (ha : a < 0) (hb : b < 0)
    (h₀ : IsSupersingular E₀) (hE : IsSupersingular E) (P : HomPlacement S j E)
    (N : ℕ) (hN : N ≠ 0) (hcop : N.Coprime q) (Pt : E.Pt k) (hPt : orderOf Pt = N)
    (P₀ : E₀.Pt k) (hP₀ : orderOf P₀ = N)
    (hC₀ : ∀ x ∈ Subgroup.zpowers P₀, x ^ N = 1) (hC : ∀ x ∈ Subgroup.zpowers Pt, x ^ N = 1)
    (gam : levelEnd E (Subgroup.zpowers Pt)) :
    ((levelEndEquivRight hCor hT hV hq ha hb h₀ hE P N hN hcop Pt hPt P₀ hP₀ hC₀ hC gam :
      (levelIdeal P (Subgroup.zpowers P₀) hN hC₀ (Subgroup.zpowers Pt) hC).rightRing) :
        B a b) = P.endRight gam := rfl

end Equiv

end ZInQ.Manuscript.RC.HCMV21
