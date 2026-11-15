import ZInQKernel.Contrib.AbVarBC.Tate

/-!
# Base change of abelian varieties, V: descent of torsion points from finiteness of `[N]`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

* `mem_range_of_isIntegral`: an element of a field `Ω₂ ⊇ K` integral over `K` lies in the image of
  any `K`-embedding `K̄ → Ω₂`.
* `exists_lift_of_isFinite`: for `g : Z → Spec K` finite and `κ : Ω → Ω₂` a `K`-embedding with
  `Ω` algebraically closed, every `Ω₂`-point of `Z` over `K` comes from an `Ω`-point (STANDARD:
  `Z = Spec R`, `R` finite over `K`, and the image of `R → Ω₂` is algebraic over `K`).
* `torsionDescends_of_isFinite`: if `[ℓⁿ] : A → A` is finite for every `n`, then
  `TorsionDescends A κ ℓ` (the `ℓ`-power torsion points of `A_L(L̄)` come from `A(K̄)`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Algebra -/

/-- An element integral over `K` lies in the image of any `K`-embedding of an algebraically
closed field. -/
theorem mem_range_of_isIntegral {K Ω Ω₂ : Type*} [Field K] [Field Ω] [IsAlgClosed Ω] [Field Ω₂]
    [Algebra K Ω] [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) {x : Ω₂} (hx : IsIntegral K x) :
    x ∈ (κ : Ω →+* Ω₂).range := by
  have hf0 : (minpoly K x).map (algebraMap K Ω) ≠ 0 :=
    Polynomial.map_ne_zero (minpoly.ne_zero hx)
  refine Polynomial.Splits.mem_range_of_isRoot (IsAlgClosed.splits _) hf0 ?_
  rw [Polynomial.map_map, κ.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
  exact minpoly.aeval K x

/-! ## §2. Points of a scheme finite over a field -/

/-- **Points of a finite `K`-scheme over an algebraically closed field.** -/
theorem exists_lift_of_isFinite {K : Type} [Field K] {Ω Ω₂ : Type} [Field Ω] [IsAlgClosed Ω]
    [Field Ω₂] [Algebra K Ω] [Algebra K Ω₂] (κ : Ω →ₐ[K] Ω₂) {Z : Scheme.{0}}
    (g : Z ⟶ Spec (CommRingCat.of K)) [IsFinite g] (q : Spec (CommRingCat.of Ω₂) ⟶ Z)
    (hq : q ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Ω₂))) :
    ∃ p : Spec (CommRingCat.of Ω) ⟶ Z,
      Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ p = q ∧
        p ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  haveI : IsAffine Z := isAffine_of_isAffineHom g
  let e := Z.isoSpec
  let φ := Spec.preimage (q ≫ e.hom)
  let θ := Spec.preimage (e.inv ≫ g)
  have hφ : Spec.map φ = q ≫ e.hom := Spec.map_preimage _
  have hθ : Spec.map θ = e.inv ≫ g := Spec.map_preimage _
  have hθfin : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  have hcomp : θ ≫ φ = CommRingCat.ofHom (algebraMap K Ω₂) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hθ, Category.assoc, e.hom_inv_id_assoc, hq]
  -- every element of the image of `φ` is integral over `K`
  have hint : ∀ r, IsIntegral K (φ.hom r) := by
    intro r
    have hr : θ.hom.IsIntegralElem r := hθfin.to_isIntegral r
    obtain ⟨P, hPm, hP⟩ := hr
    refine ⟨P, hPm, ?_⟩
    have := congrArg φ.hom hP
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [Polynomial.eval₂_eq_eval_map] at this ⊢
    have h2 : φ.hom.comp θ.hom = algebraMap K Ω₂ := congrArg CommRingCat.Hom.hom hcomp
    rw [h2] at this
    exact this
  choose ψ0 hψ0 using fun r => mem_range_of_isIntegral κ (hint r)
  have hκinj : Function.Injective (κ : Ω →+* Ω₂) := (κ : Ω →+* Ω₂).injective
  let ψ : Γ(Z, ⊤) →+* Ω :=
    { toFun := ψ0
      map_one' := hκinj (by rw [hψ0, map_one, map_one])
      map_mul' := fun a b => hκinj (by rw [hψ0, map_mul, map_mul, hψ0, hψ0])
      map_zero' := hκinj (by rw [hψ0, map_zero, map_zero])
      map_add' := fun a b => hκinj (by rw [hψ0, map_add, map_add, hψ0, hψ0]) }
  have hψ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (κ : Ω →+* Ω₂) = φ := by
    ext r
    exact hψ0 r
  have hlift : Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫ (Spec.map (CommRingCat.ofHom ψ) ≫
      e.inv) = q := by
    rw [← Category.assoc, ← Spec.map_comp, hψ, hφ, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ e.inv, hlift, ?_⟩
  haveI := epi_spec_map_field (κ : Ω →+* Ω₂)
  apply (cancel_epi (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)))).1
  rw [← Category.assoc, hlift, hq, ← Spec.map_comp, ← CommRingCat.ofHom_comp, κ.comp_algebraMap]

/-! ## §3. Torsion points of a base change -/

section Tors

variable {K : Type} [Field K] (A : PkgI3.AbVar K)

/-- `q ≫ [N] = q ^ N` for `[N] = ((N : ℤ) : End A).hom`. -/
theorem comp_natCast_hom {T : Over (Spec (CommRingCat.of K))} (q : T ⟶ A.X) (N : ℕ) :
    q ≫ (((N : ℤ) : PkgI3.AbVar.End A)).hom = q ^ N := by
  induction N with
  | zero =>
    rw [Nat.cast_zero, Int.cast_zero, PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one, pow_zero]
  | succ N ih =>
    rw [Nat.cast_succ, Int.cast_add, Int.cast_one, PkgI3.AbVar.Hom.hom_add, MonObj.comp_mul, ih,
      pow_succ]
    congr 1

variable {L : Type} [Field L] [Algebra K L]

/-- **Torsion descent from finiteness of `[ℓⁿ]`.** If `[ℓⁿ] : A → A` is a finite morphism for
every `n`, then every `ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`. -/
theorem torsionDescends_of_isFinite (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hfin : ∀ n : ℕ, IsFinite ((((ℓ ^ n : ℕ) : ℤ) : PkgI3.AbVar.End A).hom.left)) :
    TorsionDescends A κ ℓ := by
  intro n q hq
  set N := ℓ ^ n with hN
  set q₀ := bcPt A (AlgebraicClosure L) q with hq₀
  have h0 : q₀ ^ N = 1 := by rw [hq₀, ← map_pow, hq, map_one]
  have h1 : q₀ ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom = 1 := by rw [comp_natCast_hom, h0]
  haveI := hfin n
  let fN : A.X.left ⟶ A.X.left := ((N : ℤ) : PkgI3.AbVar.End A).hom.left
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have hq0 : q₀.left ≫ fN = Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L))) ≫ e := by
    have h2 := congrArg (fun f => f.left) h1
    simp only [Over.comp_left, Hom.one_def] at h2
    exact h2
  have hfN : IsFinite fN := hfin n
  let z : Spec (CommRingCat.of (AlgebraicClosure L)) ⟶ pullback fN e :=
    pullback.lift q₀.left (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L)))) hq0
  obtain ⟨p0, hp0, hp0g⟩ := exists_lift_of_isFinite κ (pullback.snd fN e) z (pullback.lift_snd _ _ _)
  have hfst : pullback.fst fN e ≫ A.X.hom = pullback.snd fN e := by
    have hw : fN ≫ A.X.hom = A.X.hom := Over.w ((N : ℤ) : PkgI3.AbVar.End A).hom
    have he : e ≫ A.X.hom = 𝟙 _ := Over.w η[A.X]
    rw [← hw, ← Category.assoc, pullback.condition, Category.assoc, he, Category.comp_id]
  let p : A.Pt (AlgebraicClosure K) := Over.homMk (p0 ≫ pullback.fst fN e) (by
    change (p0 ≫ pullback.fst fN e) ≫ A.X.hom = _
    rw [Category.assoc, hfst, hp0g]
    rfl)
  refine ⟨p, ?_⟩
  change (bcPt A (AlgebraicClosure L)).symm (extPt A κ p) = q
  rw [MulEquiv.symm_apply_eq]
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (κ : AlgebraicClosure K →+* AlgebraicClosure L)) ≫
    p0 ≫ pullback.fst fN e = q₀.left
  rw [← Category.assoc, hp0]
  exact pullback.lift_fst _ _ _

end Tors

end ZInQ.Contrib.AbVarBC
