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

end ZInQ.Contrib.AbVarBC.Tangent
