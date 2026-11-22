import ZInQKernel.Contrib.AbVarBC.Tangent

/-!
# Base change of abelian varieties, IX: the unit section of `A[n]` is an open immersion

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

In characteristic `0` and for `n ≠ 0`, the unit section `kerUnit A [n] : Spec K → A[n]` is an
open immersion: mul-rigidity's leaf `KerUnitOpen` is a theorem (`kerUnitOpen`). Proof:
* §1 a `K`-derivation `D : Γ(A[n], W) → K` at the origin gives a tangent vector `v` of `A[n]`;
  its image in `A` is a tangent vector killed by `[n]`, hence trivial (`Tangent.lean` §6), so
  `v` is trivial and `D = 0` (`derivation_eq_zero`);
* §2 hence the maximal ideal `P` of the origin in `T = Γ(A[n], W)` satisfies `P = P²`
  (functionals on `P / P²` are derivations), so `P = (e)` with `e` idempotent (`T` Noetherian);
* §3 on the basic open `D(1 - e)` the structure map to `Spec K` is surjective on sections, so
  formally unramified, and the unit section is a section of it, hence an open immersion.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.AbVarBC.Tangent

open TrivSqZeroExt

/-! ## §1. Derivations at the origin of `A[n]` vanish -/

section Der

variable {K : Type} [Field K]

/-- The ring map `t ↦ ev t + ε D t` of a derivation `D` at `ev`. -/
def dualHom {T : Type} [CommRing T] (ev : T →+* K) (D : T → K)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hmul : ∀ a b, D (a * b) = ev a * D b + ev b * D a) :
    T →+* TrivSqZeroExt K K where
  toFun t := inl (ev t) + inr (D t)
  map_one' := by
    have h : D 1 = 0 := by
      have := hmul 1 1
      rw [_root_.mul_one, map_one, _root_.one_mul] at this
      linear_combination -this
    ext <;> simp [h]
  map_mul' a b := by
    ext
    · simp
    · simp [hmul]
      ring
  map_zero' := by
    have h : D 0 = 0 := by
      have := hadd 0 0
      rw [add_zero] at this
      linear_combination -this
    ext <;> simp [h]
  map_add' a b := by
    ext
    · simp
    · simp [hadd]

end Der

section KerDer

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℤ)

/-- `[n] : A → A`. -/
abbrev mulN : A.X ⟶ A.X := ((n : PkgI3.AbVar.End A)).hom

/-- The kernel `A[n]` (as an object over `Spec K`). -/
abbrev KerN : Over (Spec (CommRingCat.of K)) := pullback (mulN A n) η[A.X]

/-- The unit section of `A[n]`, as a morphism of schemes. -/
def ks : Spec (CommRingCat.of K) ⟶ (KerN A n).left :=
  (MulRigidity.kerUnit A (mulN A n)).left

theorem ks_hom : ks A n ≫ (KerN A n).hom = 𝟙 _ :=
  Over.w (MulRigidity.kerUnit A (mulN A n))

theorem comp_mem_of_subsingleton {X : Scheme.{0}} {W : X.Opens}
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s (IsLocalRing.closedPoint K) ∈ W) {Λ : CommRingCat.{0}}
    (p : Spec Λ ⟶ Spec (CommRingCat.of K)) (x : Spec Λ) : (p ≫ s) x ∈ W := by
  show s (p x) ∈ W
  rw [Subsingleton.elim (p x) (IsLocalRing.closedPoint K)]
  exact hs

theorem exists_affine_orig :
    ∃ U : A.X.left.Opens, IsAffineOpen U ∧ orig A (IsLocalRing.closedPoint K) ∈ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := A.X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (orig A (IsLocalRing.closedPoint K))) isOpen_univ
  exact ⟨U, hU, hxU⟩

/-- **A derivation at the origin of `A[n]` vanishes** (characteristic `0`, `n ≠ 0`). -/
theorem derivation_eq_zero [CharZero K] (hn : n ≠ 0) {W : (KerN A n).left.Opens}
    (hW : IsAffineOpen W) (hz0 : ks A n (IsLocalRing.closedPoint K) ∈ W)
    (D : Γ((KerN A n).left, W) → K) (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = (ptRing (Λ := CommRingCat.of K) (ks A n) hz0).hom a * D b +
      (ptRing (Λ := CommRingCat.of K) (ks A n) hz0).hom b * D a)
    (hκ : ∀ x, D ((KerN A n).hom.appLE ⊤ W le_top x) = 0) : ∀ t, D t = 0 := by
  obtain ⟨U, hU, ho⟩ := exists_affine_orig A
  set ev := ptRing (Λ := CommRingCat.of K) (ks A n) hz0 with hev
  set φ : Γ((KerN A n).left, W) ⟶ CommRingCat.of (TrivSqZeroExt K K) :=
    CommRingCat.ofHom (dualHom ev.hom D hadd hmul) with hφ
  set v := ofRing hW φ with hv
  have hvmem := ofRing_mem hW φ
  have hpv : ptRing v hvmem = φ := ptRing_ofRing hW φ
  have htop : ∀ (Λ : CommRingCat.{0}) [IsLocalRing Λ] (p : Spec Λ ⟶ Spec (CommRingCat.of K)),
      p (IsLocalRing.closedPoint Λ) ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) :=
    fun _ _ _ => trivial
  -- the evaluation on sections coming from `K`
  have hevκ : ∀ x, ev.hom ((KerN A n).hom.appLE ⊤ W le_top x) =
      (ptRing (Λ := CommRingCat.of K) (𝟙 (Spec (CommRingCat.of K))) (htop _ _)).hom x := by
    intro x
    have h := ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top (ks A n) hz0
      (htop _ _)
    rw [ptRing_congr (ks_hom A n) _ (htop _ _)] at h
    rw [h]
    rfl
  -- `v` is a point over `K`
  have hvK : v ≫ (KerN A n).hom = Spec.map (CommRingCat.ofHom
      (algebraMap K (TrivSqZeroExt K K))) := by
    apply ptRing_ext (isAffineOpen_top _) (htop _ _) (htop _ _)
    rw [ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top v hvmem (htop _ _), hpv,
      ptRing_congr (Category.comp_id _).symm (htop _ _) (htop _ _),
      ptRing_specMap_comp (isAffineOpen_top _) _ _ (htop _ _)]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, hφ,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    change inl (ev.hom _) + inr (D _) = _
    rw [hκ, inr_zero, add_zero, hevκ, algebraMap_eq_inl]
  let vt : ptR (K := K) (TrivSqZeroExt K K) ⟶ KerN A n := Over.homMk v hvK
  -- its reduction is the unit section
  have hfst : specHom (fstHom K K K) ≫ vt = toUnit _ ≫ MulRigidity.kerUnit A (mulN A n) := by
    apply Over.OverMorphism.ext
    change Spec.map _ ≫ v = Spec.map (CommRingCat.ofHom (algebraMap K K)) ≫ ks A n
    have m1 : (Spec.map (CommRingCat.ofHom ((fstHom K K K : TrivSqZeroExt K K →ₐ[K] K) :
        TrivSqZeroExt K K →+* K)) ≫ v) (IsLocalRing.closedPoint K) ∈ W := by
      show v (Spec.map (CommRingCat.ofHom ((fstHom K K K : TrivSqZeroExt K K →ₐ[K] K) :
        TrivSqZeroExt K K →+* K)) (IsLocalRing.closedPoint K)) ∈ W
      rw [closedPoint_eq]
      exact hvmem
    have m2 := comp_mem_of_subsingleton (ks A n) hz0
      (Spec.map (CommRingCat.ofHom (algebraMap K K))) (IsLocalRing.closedPoint K)
    apply ptRing_ext hW m1 m2
    rw [ptRing_specMap_comp hW _ _ hvmem, ptRing_specMap_comp hW _ _ hz0, hpv]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro t
    rw [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply, hφ,
      CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
    change (inl (ev.hom t) + inr (D t) : TrivSqZeroExt K K).fst = algebraMap K K (ev.hom t)
    rw [fst_add, fst_inl, fst_inr, add_zero, Algebra.algebraMap_self, RingHom.id_apply]
  set u := vt ≫ pullback.fst (mulN A n) η[A.X] with hu
  have hu0 : AtOrigin A u := by
    unfold AtOrigin
    rw [hu, ← Category.assoc, hfst, Category.assoc, MulRigidity.kerUnit, pullback.lift_fst,
      Hom.one_def]
  have huf : u ≫ mulN A n = 1 := by
    rw [hu, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have hu1 : u = 1 := eq_one_of_comp_intCast A ho hU hu0 n hn huf
  have hvt : vt = toUnit _ ≫ MulRigidity.kerUnit A (mulN A n) := by
    apply pullback.hom_ext
    · rw [← hu, hu1, Category.assoc, MulRigidity.kerUnit, pullback.lift_fst, Hom.one_def]
    · exact toUnit_unique _ _
  have hvl : v = Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K K))) ≫ ks A n :=
    congrArg (fun g => g.left) hvt
  have m3 := comp_mem_of_subsingleton (ks A n) hz0
    (Spec.map (CommRingCat.ofHom (algebraMap K (TrivSqZeroExt K K))))
    (IsLocalRing.closedPoint (TrivSqZeroExt K K))
  have key := (ptRing_congr hvl hvmem m3).trans (ptRing_specMap_comp hW _ _ hz0 m3)
  rw [hpv] at key
  intro t
  have := congrArg (fun g => (g.hom t).snd) key
  simp only [hφ, CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.comp_apply] at this
  change (inl (ev.hom t) + inr (D t) : TrivSqZeroExt K K).snd = _ at this
  rw [snd_add, snd_inl, snd_inr, zero_add, algebraMap_eq_inl, snd_inl] at this
  exact this

end KerDer

/-! ## §2. Commutative algebra: no derivations means `P = P²` -/

section Alg

variable {K : Type} [Field K]

/-- If every `K`-derivation `T → K` at `ev` vanishes, the kernel `P` of `ev` satisfies `P ≤ P²`
(a functional on `P / P²` is a derivation). -/
theorem ker_le_sq_of_derivations {T : Type} [CommRing T] (ev : T →+* K) (jK : K →+* T)
    (hevj : ∀ c, ev (jK c) = c)
    (hD : ∀ D : T → K, (∀ a b, D (a + b) = D a + D b) →
      (∀ a b, D (a * b) = ev a * D b + ev b * D a) → (∀ c, D (jK c) = 0) → ∀ t, D t = 0) :
    RingHom.ker ev ≤ (RingHom.ker ev) ^ 2 := by
  intro a ha
  by_contra hna
  letI : Algebra K T := jK.toAlgebra
  have hsmul : ∀ (c : K) (t : T), c • t = jK c * t := fun c t => Algebra.smul_def c t
  set P := RingHom.ker ev with hP
  let P' : Submodule K T := P.restrictScalars K
  let N : Submodule K P' := ((P ^ 2).restrictScalars K).comap P'.subtype
  have hmem : ∀ t, t - jK (ev t) ∈ P' := fun t => by
    change t - jK (ev t) ∈ RingHom.ker ev
    rw [RingHom.mem_ker, map_sub, hevj, sub_self]
  let q : T → P' ⧸ N := fun t => N.mkQ ⟨t - jK (ev t), hmem t⟩
  have hqa : q a ≠ 0 := by
    intro h
    change N.mkQ ⟨a - jK (ev a), hmem a⟩ = 0 at h
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
    apply hna
    have h' : a - jK (ev a) ∈ P ^ 2 := h
    rwa [RingHom.mem_ker.mp ha, map_zero, sub_zero] at h'
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual K (P' ⧸ N), l (q a) ≠ 0 := by
    by_contra h
    push Not at h
    exact hqa ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  have hadd : ∀ x y, l (q (x + y)) = l (q x) + l (q y) := by
    intro x y
    rw [← map_add]
    congr 1
    change N.mkQ _ = N.mkQ _ + N.mkQ _
    rw [← map_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, map_add]
    ring
  have hmul : ∀ x y, l (q (x * y)) = ev x * l (q y) + ev y * l (q x) := by
    intro x y
    suffices hq : q (x * y) = ev x • q y + ev y • q x by
      rw [hq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    change N.mkQ _ = ev x • N.mkQ _ + ev y • N.mkQ _
    rw [← map_smul, ← map_smul, ← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    change ((⟨x * y - jK (ev (x * y)), hmem _⟩ : P') -
      (ev x • ⟨y - jK (ev y), hmem y⟩ + ev y • ⟨x - jK (ev x), hmem x⟩) : P').1 ∈ P ^ 2
    have e1 : ((⟨x * y - jK (ev (x * y)), hmem _⟩ : P') -
        (ev x • ⟨y - jK (ev y), hmem y⟩ + ev y • ⟨x - jK (ev x), hmem x⟩) : P').1 =
        (x - jK (ev x)) * (y - jK (ev y)) := by
      simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, hsmul, map_mul]
      ring
    rw [e1, pow_two]
    exact Ideal.mul_mem_mul (hmem x) (hmem y)
  have hj : ∀ c, l (q (jK c)) = 0 := by
    intro c
    have : q (jK c) = 0 := by
      change N.mkQ _ = 0
      have : (⟨jK c - jK (ev (jK c)), hmem _⟩ : P') = 0 := by
        apply Subtype.ext
        simp [hevj]
      rw [this, map_zero]
    rw [this, map_zero]
  exact hl (hD (fun t => l (q t)) hadd hmul hj a)

end Alg

/-! ## §3. The unit section of `A[n]` is an open immersion -/

section Final

variable {K : Type} [Field K] (A : PkgI3.AbVar K) (n : ℤ)

theorem locallyOfFiniteType_kerN : LocallyOfFiniteType (KerN A n).hom := by
  have h1 : LocallyOfFiniteType (mulN A n).left := by
    have : LocallyOfFiniteType ((mulN A n).left ≫ A.X.hom) := by
      rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ A.X.hom
  have hP := (Over.forget _).map_isPullback (IsPullback.of_hasPullback (mulN A n) η[A.X])
  have h2 : LocallyOfFiniteType (pullback.snd (mulN A n) η[A.X]).left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFiniteType) hP h1
  have h3 : (pullback.snd (mulN A n) η[A.X]).left ≫
      (𝟙_ (Over (Spec (CommRingCat.of K)))).hom = (KerN A n).hom := Over.w _
  rw [← h3]
  change LocallyOfFiniteType (_ ≫ 𝟙 _)
  rw [Category.comp_id]
  exact h2

theorem id_appLE_top (h : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤
    (𝟙 (Spec (CommRingCat.of K))) ⁻¹ᵁ ⊤) :
    Scheme.Hom.appLE (𝟙 (Spec (CommRingCat.of K))) ⊤ ⊤ h = 𝟙 _ := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
  erw [Category.id_comp]
  exact (Spec (CommRingCat.of K)).presheaf.map_id (Opposite.op ⊤)

theorem ptRing_id_top :
    ptRing (Λ := CommRingCat.of K) (𝟙 (Spec (CommRingCat.of K)))
      (show _ ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) from trivial) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
  unfold ptRing
  rw [id_appLE_top, Category.id_comp]

/-- **mul-rigidity's leaf `KerUnitOpen`, proved**: in characteristic `0`, for `n ≠ 0`, the unit
section of `A[n]` is an open immersion. -/
theorem ks_isOpenImmersion [CharZero K] (hn : n ≠ 0) : IsOpenImmersion (ks A n) := by
  set Z := (KerN A n).left with hZ
  obtain ⟨_, ⟨W, hW, rfl⟩, hz0, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ks A n (IsLocalRing.closedPoint K))) isOpen_univ
  haveI := locallyOfFiniteType_kerN A n
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (KerN A n).hom
  haveI : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  set ev := ptRing (Λ := CommRingCat.of K) (ks A n) hz0 with hev
  set κ := (KerN A n).hom.appLE ⊤ W le_top with hκ
  let jK : K →+* Γ(Z, W) := κ.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have htop : ∀ (Λ : CommRingCat.{0}) [IsLocalRing Λ] (p : Spec Λ ⟶ Spec (CommRingCat.of K)),
      p (IsLocalRing.closedPoint Λ) ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) :=
    fun _ _ _ => trivial
  have hevκ : ∀ x, ev.hom (κ.hom x) = (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x := by
    intro x
    have h := ptRing_comp hW (KerN A n).hom (isAffineOpen_top _) le_top (ks A n) hz0
      (htop _ _)
    rw [ptRing_congr (ks_hom A n) _ (htop _ _), ptRing_id_top] at h
    rw [h]
    rfl
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hevj : ∀ c, ev.hom (jK c) = c := by
    intro c
    change ev.hom (κ.hom (eK.symm c)) = c
    rw [hevκ]
    exact eK.apply_symm_apply c
  have hκj : ∀ x, κ.hom x = jK ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom x) := by
    intro x
    change κ.hom x = κ.hom (eK.symm (eK x))
    rw [RingEquiv.symm_apply_apply]
  have hPP := ker_le_sq_of_derivations ev.hom jK hevj (fun D hadd hmul hj =>
    derivation_eq_zero A n hn hW hz0 D hadd hmul (fun x => by rw [hκj]; exact hj _))
  have hidem : IsIdempotentElem (RingHom.ker ev.hom) := by
    unfold IsIdempotentElem
    rw [← pow_two]
    exact le_antisymm (Ideal.pow_le_self two_ne_zero) hPP
  obtain ⟨e, he, hPe⟩ :=
    (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp hidem
  have heP : e ∈ RingHom.ker ev.hom := by
    rw [hPe]; exact Submodule.mem_span_singleton_self e
  set g : Γ(Z, W) := 1 - e with hg
  have hevg : ev.hom g = 1 := by
    rw [hg, map_sub, map_one, RingHom.mem_ker.mp heP, sub_zero]
  -- the origin lies in `D(g)`
  have hle : (⊤ : (Spec (CommRingCat.of K)).Opens) ≤ ks A n ⁻¹ᵁ W :=
    (Scheme.preimage_eq_top_of_closedPoint_mem (ks A n) hz0).ge
  have hz0' : ks A n (IsLocalRing.closedPoint K) ∈ Z.basicOpen g := by
    have hb := Scheme.basicOpen_appLE (ks A n) ⊤ W hle g
    have hu : IsUnit ((ks A n).appLE W ⊤ hle g) := by
      have h1 : eK ((ks A n).appLE W ⊤ hle g) = 1 := hevg
      have : (ks A n).appLE W ⊤ hle g = 1 := by
        rw [← eK.symm_apply_apply ((ks A n).appLE W ⊤ hle g), h1, map_one]
      rw [this]
      exact isUnit_one
    rw [Scheme.basicOpen_of_isUnit _ hu] at hb
    have hmem : IsLocalRing.closedPoint K ∈ (⊤ : (Spec (CommRingCat.of K)).Opens) := trivial
    rw [hb] at hmem
    exact hmem.2
  set W' := Z.basicOpen g with hW'def
  have hW' : IsAffineOpen W' := hW.basicOpen g
  haveI hloc := hW.isLocalization_basicOpen g
  have hge : algebraMap Γ(Z, W) Γ(Z, W') g * algebraMap Γ(Z, W) Γ(Z, W') e = 0 := by
    have hge0 : g * e = 0 := by
      change (1 - e) * e = 0
      rw [sub_mul, _root_.one_mul, he.eq, sub_self]
    rw [← map_mul, hge0, map_zero]
  have hgu : IsUnit (algebraMap Γ(Z, W) Γ(Z, W') g) := IsLocalization.Away.algebraMap_isUnit g
  have hre : algebraMap Γ(Z, W) Γ(Z, W') e = 0 := hgu.mul_right_eq_zero.mp hge
  have hrg : algebraMap Γ(Z, W) Γ(Z, W') g = 1 := by
    have h := map_sub (algebraMap Γ(Z, W) Γ(Z, W')) 1 e
    rw [map_one, hre, sub_zero] at h
    exact h
  have hrP : ∀ t ∈ RingHom.ker ev.hom, algebraMap Γ(Z, W) Γ(Z, W') t = 0 := by
    intro t ht
    rw [hPe] at ht
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    rw [smul_eq_mul, map_mul, hre, MulZeroClass.mul_zero]
  set κ' := (KerN A n).hom.appLE ⊤ W' le_top with hκ'def
  have hκ' : κ' = κ ≫ Z.presheaf.map (homOfLE (Z.basicOpen_le g)).op := by
    rw [hκ'def, hκ]
    exact (Scheme.Hom.appLE_map (KerN A n).hom le_top (homOfLE (Z.basicOpen_le g)).op).symm
  have hsurj : Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ κ').hom := by
    intro y
    obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) y
    obtain ⟨k, hk⟩ := s.2
    refine ⟨ev.hom t, ?_⟩
    have hs1 : algebraMap Γ(Z, W) Γ(Z, W') (s : Γ(Z, W)) = 1 := by
      rw [← hk, map_pow, hrg, one_pow]
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, hs1, _root_.mul_one]
    have hmem : t - jK (ev.hom t) ∈ RingHom.ker ev.hom := by
      rw [RingHom.mem_ker, map_sub, hevj, sub_self]
    have h0 := hrP _ hmem
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, hκ']
    rfl
  let i := hW'.fromSpec
  have hrange : Set.range (ks A n) ⊆ Set.range i := by
    rw [hW'.range_fromSpec]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (IsLocalRing.closedPoint K)]
    exact hz0'
  let s' := IsOpenImmersion.lift i (ks A n) hrange
  have hs' : s' ≫ i = ks A n := IsOpenImmersion.lift_fac _ _ _
  have hiK : i ≫ (KerN A n).hom =
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ κ') := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec (KerN A n).hom (isAffineOpen_top _) hW' le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
    rw [Spec.map_comp]
    exact h.symm
  haveI : FormallyUnramified (i ≫ (KerN A n).hom) := by
    rw [hiK, HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
    exact RingHom.FormallyUnramified.of_surjective hsurj
  have hsec : s' ≫ (i ≫ (KerN A n).hom) = 𝟙 _ := by
    rw [← Category.assoc, hs', ks_hom]
  haveI := MulRigidity.isOpenImmersion_of_section s' (i ≫ (KerN A n).hom) hsec
  rw [← hs']
  infer_instance

end Final

end ZInQ.Contrib.AbVarBC.Tangent
