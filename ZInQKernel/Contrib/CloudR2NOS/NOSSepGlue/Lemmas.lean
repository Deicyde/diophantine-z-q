/-
H5 lane C3 NOS-F1 edition (2026-11-17), Source only. In `isInertia_comap_of_comm` the bound variable `ι` is
renamed to `j`: `ι` is notation once `MonObj` is opened, so it cannot be a binder name. Statements are unchanged up to
the name of a bound variable; there is no other change.
-/
/-
H5 lane3: NOSConverseSep GLUE LEMMAS (Parent target change, lead 07:41Z). 2026-11-17. New file.
SOURCE-ONLY, UNCOMPILED. Universe 0, matching `NOSProof.NOSConverseSep`.

This module needs NO H5 converse source. It imports only main's published suppliers:
* `ZInQKernel.Contrib.OneProof.NeronOggShafarevichSep` (c0f3d085), which provides
  `NOSSepDict.exists_pow_mem_sep`, `NOSSepDict.mem_of_pow_mem_vs` and
  `NOSSepDict.inertiaTrivialOn_sep_iff`;
* `ZInQKernel.Contrib.AbVarBC.Points` (c0f3d085), which provides `extPt`, `extPt_injective` and
  `extPt_galAct`;
* `ZInQKernel.HDecomp.Objects` (`PkgI2`, `ObjBridge`).
They are imported, never copied. The final theorem `nosConverseSep_of_converse` derives the
`NOSConverseSep` statement from our converse statement at universe 0.

Contents:
* `isInertia_comap_of_comm`: inertia pulls back along a K-embedding of fields compatible with the
  automorphisms. The proof follows main's `UnipotentForward.inertiaRestrict'` (which compiles), with
  the inclusion `K^s → Ω` replaced by an arbitrary `j`.
* `inertiaTrivialOn_comap_equiv`: inertia-triviality transports along a K-isomorphism `e : L₁ ≃ L₂`,
  with `w ↦ w.comap e.symm`. The proof follows main's `NOSSepDict.inertiaTrivialOn_sep_iff`.
* `exists_extension_sepClosure`: every valuation subring of `K^s = separableClosure K K̄` extends to
  `K̄`. The extension is the "radical" subring `{y | ∃ n, y^(q^n) ∈ w_s}`, `q` the exponential
  characteristic, using the pure inseparability of `K̄/K^s`.
* `nosConverseSep_of_converse`, steps (a)–(d) of the lead's plan:
  - (a) `e : Ks ≃ₐ[K] K^s` by `IsSepClosure.equiv`, and `w_s := w.comap e.symm`;
  - (b) `w̄ ⊆ K̄` extending `w_s`;
  - (c) `InertiaTrivialOn A w̄ m` from the `K^s` form, via
    `(NOSSepDict.inertiaTrivialOn_sep_iff A w̄ m _).mpr`;
  - (d) apply the converse at `(K, O, w̄)`.
-/
import ZInQKernel.Contrib.OneProof.NeronOggShafarevichSep
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.HDecomp.Objects

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Pointwise

namespace ZInQ.Contrib.CloudR2NOS.NOSSepGlue

/-! ## 1. Inertia pulls back along a compatible embedding -/

/-- If `j : L₁ → L₂` is a K-embedding with `j ∘ τ = σ ∘ j` and `σ` lies in the inertia group of
`w ⊆ L₂`, then `τ` lies in the inertia group of `w.comap j`. -/
theorem isInertia_comap_of_comm {K L₁ L₂ : Type} [Field K] [Field L₁] [Field L₂] [Algebra K L₁]
    [Algebra K L₂] (j : L₁ →ₐ[K] L₂) (w : ValuationSubring L₂) (σ : L₂ ≃ₐ[K] L₂)
    (hσ : PkgI2.IsInertia w σ) (τ : L₁ ≃ₐ[K] L₁) (hcomm : ∀ x, j (τ x) = σ (j x)) :
    PkgI2.IsInertia (w.comap (j : L₁ →+* L₂)) τ := by
  obtain ⟨hd, hi⟩ := hσ
  have hs : σ • w = w := hd
  set w' := w.comap (j : L₁ →+* L₂)
  have hd' : τ ∈ w'.decompositionSubgroup K := by
    show τ • w' = w'
    ext y
    simp only [← SetLike.mem_coe, ValuationSubring.coe_pointwise_smul, Set.mem_smul_set,
      AlgEquiv.smul_def]
    constructor
    · rintro ⟨z, hz, rfl⟩
      show j (τ z) ∈ w
      rw [hcomm, ← hs]
      exact ⟨j z, hz, rfl⟩
    · intro hy
      refine ⟨τ.symm y, ?_, τ.apply_symm_apply y⟩
      have hy' : j y ∈ σ • w := by rw [hs]; exact hy
      have hy'' : j y ∈ σ • (w : Set L₂) := by
        rw [← ValuationSubring.coe_pointwise_smul]; exact hy'
      obtain ⟨u, hu, hu'⟩ := Set.mem_smul_set.mp hy''
      rw [AlgEquiv.smul_def] at hu'
      have : j (τ.symm y) = u := by
        apply σ.injective
        rw [← hcomm, τ.apply_symm_apply]
        exact hu'.symm
      show j (τ.symm y) ∈ w
      rw [this]; exact hu
  refine ⟨hd', ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker] at hi ⊢
  refine RingEquiv.ext fun r => ?_
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  -- the image of `a` in `w`
  let b : w := ⟨j (a : L₁), a.2⟩
  have h1 := RingEquiv.congr_fun hi (IsLocalRing.residue w b)
  change (⟨σ, hd⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w b =
    IsLocalRing.residue w b at h1
  change (⟨τ, hd'⟩ : w'.decompositionSubgroup K) • IsLocalRing.residue w' a =
    IsLocalRing.residue w' a
  rw [← IsLocalRing.ResidueField.residue_smul] at h1 ⊢
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff] at h1 ⊢
  let f : w' →+* w :=
    { toFun := fun x => ⟨j (x : L₁), x.2⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' := fun x y => Subtype.ext (map_mul j (x : L₁) (y : L₁))
      map_zero' := Subtype.ext (map_zero j)
      map_add' := fun x y => Subtype.ext (map_add j (x : L₁) (y : L₁)) }
  have hfc : f ((⟨τ, hd'⟩ : w'.decompositionSubgroup K) • a - a) =
      (⟨σ, hd⟩ : w.decompositionSubgroup K) • b - b := by
    apply Subtype.ext
    change j (τ (a : L₁) - (a : L₁)) = σ (j (a : L₁)) - j (a : L₁)
    rw [map_sub, hcomm]
  intro hu
  exact h1 (by rw [← hfc]; exact hu.map f)

/-! ## 2. Inertia-triviality transports along a K-isomorphism of fields -/

open ZInQ.Contrib.AbVarBC in
/-- For `e : L₁ ≃ₐ[K] L₂` and `w ⊆ L₁`, `InertiaTrivialOn A w m` implies
`InertiaTrivialOn A (w.comap e.symm) m`. -/
theorem inertiaTrivialOn_comap_equiv {K : Type} [Field K] (A : Grp (Over (Spec (.of K))))
    [PkgI2.IsAbelianVariety A] {L₁ L₂ : Type} [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂]
    (e : L₁ ≃ₐ[K] L₂) (w : ValuationSubring L₁) (m : ℕ) (h : PkgI2.InertiaTrivialOn A w m) :
    PkgI2.InertiaTrivialOn A (w.comap (e.symm : L₂ →+* L₁)) m := by
  let B := ObjBridge.ofGrp A
  let κ : L₂ →ₐ[K] L₁ := (e.symm : L₂ →ₐ[K] L₁)
  intro τ hτ x hx
  -- the conjugate `σ = e⁻¹ ∘ τ ∘ e` on `L₁`
  let σ : L₁ ≃ₐ[K] L₁ := (e.trans τ).trans e.symm
  have hcomm : ∀ y : L₁, (e : L₁ →ₐ[K] L₂) (σ y) = τ ((e : L₁ →ₐ[K] L₂) y) := by
    intro y
    show e (e.symm (τ (e y))) = τ (e y)
    rw [AlgEquiv.apply_symm_apply]
  have hσ : PkgI2.IsInertia w σ := by
    have h0 := isInertia_comap_of_comm (e : L₁ →ₐ[K] L₂) (w.comap (e.symm : L₂ →+* L₁)) τ hτ σ
      hcomm
    have hww : (w.comap (e.symm : L₂ →+* L₁)).comap ((e : L₁ →ₐ[K] L₂) : L₁ →+* L₂) = w := by
      ext y
      change e.symm (e y) ∈ w ↔ y ∈ w
      rw [AlgEquiv.symm_apply_apply]
    rw [hww] at h0
    exact h0
  have hκ : ∀ y : L₂, κ (τ y) = σ (κ y) := by
    intro y
    show e.symm (τ y) = e.symm (τ (e (e.symm y)))
    rw [AlgEquiv.apply_symm_apply]
  let x' : B.Pt L₂ := x
  have hx' : x' ^ m = 1 := hx
  have hfix : B.galAct σ (extPt B κ x') = extPt B κ x' := by
    refine h σ hσ (extPt B κ x') ?_
    show (extPt B κ x') ^ m = 1
    rw [← map_pow, hx', map_one]
  show B.galAct τ x' = x'
  apply extPt_injective B κ
  rw [extPt_galAct B κ τ σ hκ x', hfix]

/-! ## 3. Valuation subrings of `K^s` extend to `K̄` (pure inseparability) -/

/-- Every valuation subring `w_s` of `K^s = separableClosure K K̄` is `w̄ ∩ K^s` for a valuation
subring `w̄` of `K̄`: take `w̄ = {y | ∃ n, y^(q^n) ∈ w_s}`, `q` the exponential characteristic. -/
theorem exists_extension_sepClosure {K : Type} [Field K]
    (ws : ValuationSubring (separableClosure K (AlgebraicClosure K))) :
    ∃ wbar : ValuationSubring (AlgebraicClosure K),
      wbar.comap (algebraMap (separableClosure K (AlgebraicClosure K)) (AlgebraicClosure K)) = ws := by
  obtain ⟨q, hq⟩ := ExpChar.exists K
  haveI := hq
  haveI : ExpChar (AlgebraicClosure K) q :=
    expChar_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective q
  have hq0 : ∀ n : ℕ, q ^ n ≠ 0 := fun n => pow_ne_zero _ (expChar_pos K q).ne'
  have hmono : ∀ (y : AlgebraicClosure K) (n : ℕ) (z : separableClosure K (AlgebraicClosure K)),
      y ^ q ^ n = (z : AlgebraicClosure K) → ∀ k : ℕ,
        y ^ q ^ (n + k) =
          ((z ^ q ^ k : separableClosure K (AlgebraicClosure K)) : AlgebraicClosure K) := by
    intro y n z hz k
    rw [pow_add, pow_mul, hz, SubmonoidClass.coe_pow]
  refine ⟨
    { carrier := {y | ∃ n : ℕ, ∃ z : separableClosure K (AlgebraicClosure K),
        y ^ q ^ n = (z : AlgebraicClosure K) ∧ z ∈ ws}
      mul_mem' := by
        intro a b ha hb
        obtain ⟨n1, z1, h1, hz1⟩ := ha
        obtain ⟨n2, z2, h2, hz2⟩ := hb
        refine ⟨n1 + n2, z1 ^ q ^ n2 * z2 ^ q ^ n1, ?_,
          ws.mul_mem _ _ (ws.pow_mem hz1 _) (ws.pow_mem hz2 _)⟩
        rw [mul_pow, hmono a n1 z1 h1 n2, add_comm n1 n2, hmono b n2 z2 h2 n1,
          MulMemClass.coe_mul]
      one_mem' := ⟨0, 1, by simp, ws.one_mem⟩
      add_mem' := by
        intro a b ha hb
        obtain ⟨n1, z1, h1, hz1⟩ := ha
        obtain ⟨n2, z2, h2, hz2⟩ := hb
        refine ⟨n1 + n2, z1 ^ q ^ n2 + z2 ^ q ^ n1, ?_,
          ws.add_mem _ _ (ws.pow_mem hz1 _) (ws.pow_mem hz2 _)⟩
        rw [add_pow_expChar_pow, hmono a n1 z1 h1 n2, add_comm n1 n2, hmono b n2 z2 h2 n1,
          AddMemClass.coe_add]
      zero_mem' := ⟨0, 0, by simp, ws.zero_mem⟩
      neg_mem' := by
        intro a ha
        obtain ⟨n, z, h, hz⟩ := ha
        refine ⟨n, (-1) ^ q ^ n * z, ?_,
          ws.mul_mem _ _ (ws.pow_mem (ws.neg_mem _ ws.one_mem) _) hz⟩
        rw [neg_eq_neg_one_mul a, mul_pow, h]
        simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, NegMemClass.coe_neg,
          OneMemClass.coe_one]
      mem_or_inv_mem' := by
        intro y
        obtain ⟨n, z, hz⟩ := NOSSepDict.exists_pow_mem_sep K q y
        rcases ws.mem_or_inv_mem z with h | h
        · exact Or.inl ⟨n, z, hz, h⟩
        · refine Or.inr ⟨n, z⁻¹, ?_, h⟩
          rw [inv_pow, hz, IntermediateField.coe_inv] }, ?_⟩
  ext x
  constructor
  · rintro ⟨n, z, hz, hzw⟩
    have hxz : x ^ q ^ n = z := by
      apply Subtype.val_injective
      rw [SubmonoidClass.coe_pow]
      exact hz
    exact NOSSepDict.mem_of_pow_mem_vs ws (hq0 n) (by rw [hxz]; exact hzw)
  · intro hx
    exact ⟨0, x, by simp, hx⟩

/-! ## 4. `NOSConverseSep` from the converse over `K̄` -/

/-- **`NOSConverseSep` (statement of `NOSProof.NOSConverseSep`, owner's e9828e92 L332–337) from the
original (c) ⇒ (a) over `K̄ = AlgebraicClosure K` at universe 0.** Steps (a)–(d) as above. -/
theorem nosConverseSep_of_converse
    (hconv : ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (w : ValuationSubring (AlgebraicClosure K)),
      w.comap (algebraMap K (AlgebraicClosure K)) = O →
      ∀ (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A],
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite →
        PkgI2.HasGoodReduction A O) :
    ∀ (K : Type) [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
      (Ks : Type) [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]
      (w : ValuationSubring Ks), w.comap (algebraMap K Ks) = O →
      ∀ (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A],
        {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ PkgI2.InertiaTrivialOn A w m}.Infinite →
        PkgI2.HasGoodReduction A O := by
  intro K _ O _ Ks _ _ _ w hw A _ hinf
  -- (a) `Ks ≃ₐ[K] K^s` and the transported valuation subring `w_s`
  let e : Ks ≃ₐ[K] separableClosure K (AlgebraicClosure K) :=
    IsSepClosure.equiv K Ks (separableClosure K (AlgebraicClosure K))
  let ws : ValuationSubring (separableClosure K (AlgebraicClosure K)) :=
    w.comap (e.symm : separableClosure K (AlgebraicClosure K) →+* Ks)
  have hws : ws.comap (algebraMap K (separableClosure K (AlgebraicClosure K))) = O := by
    rw [← hw]
    ext x
    change e.symm (algebraMap K _ x) ∈ w ↔ algebraMap K Ks x ∈ w
    rw [AlgEquiv.commutes]
  -- (b) `w̄ ⊆ K̄` with `w̄ ∩ K^s = w_s`, hence `w̄ ∩ K = O`
  obtain ⟨wbar, hwbar⟩ := exists_extension_sepClosure ws
  have hwbarO : wbar.comap (algebraMap K (AlgebraicClosure K)) = O := by
    have h1 : (wbar.comap (algebraMap (separableClosure K (AlgebraicClosure K))
        (AlgebraicClosure K))).comap (algebraMap K (separableClosure K (AlgebraicClosure K))) = O := by
      rw [hwbar]; exact hws
    rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq] at h1
    exact h1
  -- (c) inertia-triviality: `Ks` → `K^s` (transport along `e`) → `K̄` (main's `inertiaTrivialOn_sep_iff`)
  have key : ∀ m : ℕ, IsUnit (m : O) → PkgI2.InertiaTrivialOn A w m →
      PkgI2.InertiaTrivialOn A wbar m := by
    intro m hu ht
    have hmK : (m : K) ≠ 0 := by
      intro h0
      apply hu.ne_zero
      apply Subtype.ext
      simpa using h0
    have hts : PkgI2.InertiaTrivialOn A ws m := inertiaTrivialOn_comap_equiv A e w m ht
    rw [← hwbar] at hts
    exact (NOSSepDict.inertiaTrivialOn_sep_iff A wbar m hmK).mpr hts
  -- (d) the converse at `(K, O, w̄)`
  refine hconv K O wbar hwbarO A (hinf.mono ?_)
  rintro m ⟨hm, hu, ht⟩
  exact ⟨hm, hu, key m hu ht⟩

end ZInQ.Contrib.CloudR2NOS.NOSSepGlue
