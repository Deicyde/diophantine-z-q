import ZInQKernel.Contrib.OneProof.RC.HCMV21.LevelIdealTate

/-! The endomorphisms of `E` act on a placement of `Hom(E, E₀)` on the right.
For a placement `ι` and `γ ∈ End(E)` there is a unique `x ∈ B` with
`ι(α ∘ γ) = ι(α) x` for all `α`. This defines a ring map `End(E) → B` into the
right order of the placed ideal, which carries the level endomorphisms into the
right order of the placed level ideal. It is injective: the Tate maps of
`Hom(E, E₀)` span all `ℤ_p`-maps (with the rank-four basis read off the
placement), so a `γ` with every `α ∘ γ = 0` has `T_p γ = 0`, and then `γ` is
divisible by every power of `p` in the lattice `End(E)`. All proofs are Lean
proofs. -/

noncomputable section

namespace ZInQ.Manuscript.RC.HCMV21

open CategoryTheory AlgebraicGeometry Eichler Adelic PkgI3.AbVar
open scoped CategoryTheory.MonObj

variable {k : Type} [Field k] {a b : ℚ} {E₀ E : PkgI3.AbVar k}
  {S : Order a b} {j : E₀.End ≃+* S.ring}

theorem homPull_postcomp (gam : E.End) (o : E₀.End) (α : Hom E E₀) :
    homPull gam (postcomp o α) = postcomp o (homPull gam α) :=
  Hom.ext' (by simp only [homPull_hom, postcomp_hom, Category.assoc])

theorem homPull_mul (gam δ : E.End) (α : Hom E E₀) :
    homPull (gam * δ) α = homPull δ (homPull gam α) :=
  Hom.ext' (by
    simp only [homPull_hom]
    change (δ.hom ≫ gam.hom) ≫ α.hom = δ.hom ≫ (gam.hom ≫ α.hom)
    rw [Category.assoc])

theorem homPull_one (α : Hom E E₀) : homPull (1 : E.End) α = α :=
  Hom.ext' (by
    simp only [homPull_hom]
    change 𝟙 _ ≫ α.hom = α.hom
    exact Category.id_comp _)

/-- Precomposition `γ ↦ α ∘ γ`, additive in `γ`. -/
def homPullLeft (α : Hom E E₀) : E.End →+ Hom E E₀ where
  toFun gam := homPull gam α
  map_zero' := Hom.ext' (by simp [homPull_hom])
  map_add' gam δ := Hom.ext' (by simp [homPull_hom, MonObj.mul_comp])

@[simp] theorem homPullLeft_apply (α : Hom E E₀) (gam : E.End) :
    homPullLeft α gam = homPull gam α := rfl

theorem homT_homPull {E' : PkgI3.AbVar k} (p : ℕ) [Fact p.Prime] (gam : Hom E E')
    (α : Hom E' E₀) :
    homT (ℓ := p) (homPull gam α) = (homT (ℓ := p) α).comp (homT (ℓ := p) gam) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext n
  change Additive.ofMul (Additive.toMul (x.1 n) ≫ (gam.hom ≫ α.hom)) =
    Additive.ofMul ((Additive.toMul (x.1 n) ≫ gam.hom) ≫ α.hom)
  rw [Category.assoc]

theorem mul_left_cancel_of_ne_zero (ha : a < 0) (hb : b < 0) {y x x' : B a b} (hy : y ≠ 0)
    (h : y * x = y * x') : x = x' := by
  set u := unitOfNeZero ha hb y hy
  have hu : (u : B a b) = y := rfl
  calc x = (↑u⁻¹ : B a b) * ((u : B a b) * x) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = (↑u⁻¹ : B a b) * ((u : B a b) * x') := by rw [hu, h]
    _ = x' := by rw [← mul_assoc, Units.inv_mul, one_mul]

namespace HomPlacement

theorem exists_right (P : HomPlacement S j E) (gam : E.End) :
    ∃ x : B a b, ∀ α, P.emb (homPull gam α) = P.emb α * x :=
  P.exists_mul_right (P.emb.comp (homPull gam)) (fun o α => by
    simp only [AddMonoidHom.comp_apply]
    rw [homPull_postcomp, P.map_postcomp])

theorem right_unique (ha : a < 0) (hb : b < 0) (P : HomPlacement S j E) {x x' : B a b}
    (h : ∀ α, P.emb α * x = P.emb α * x') : x = x' := by
  obtain ⟨y, hy, hy0⟩ := P.ideal.val.exists_ne_zero
  obtain ⟨α, rfl⟩ := P.exists_of_mem hy
  exact mul_left_cancel_of_ne_zero ha hb hy0 (h α)

/-- The element of `B` by which `γ ∈ End(E)` acts on the placed `Hom(E, E₀)`. -/
def endRight (P : HomPlacement S j E) (gam : E.End) : B a b :=
  Classical.choose (P.exists_right gam)

theorem endRight_spec (P : HomPlacement S j E) (gam : E.End) (α : Hom E E₀) :
    P.emb (homPull gam α) = P.emb α * P.endRight gam :=
  Classical.choose_spec (P.exists_right gam) α

theorem endRight_eq (ha : a < 0) (hb : b < 0) (P : HomPlacement S j E) {gam : E.End} {x : B a b}
    (h : ∀ α, P.emb (homPull gam α) = P.emb α * x) : P.endRight gam = x :=
  P.right_unique ha hb fun α => by rw [← P.endRight_spec, h]

/-- The right action of `End(E)` on a placement, as a ring map. -/
def endRightHom (ha : a < 0) (hb : b < 0) (P : HomPlacement S j E) : E.End →+* B a b where
  toFun := P.endRight
  map_one' := P.endRight_eq ha hb fun α => by rw [homPull_one, mul_one]
  map_mul' gam δ := P.endRight_eq ha hb fun α => by
    rw [homPull_mul, P.endRight_spec, P.endRight_spec, mul_assoc]
  map_zero' := P.endRight_eq ha hb fun α => by
    rw [mul_zero, ← homPullLeft_apply, map_zero, map_zero]
  map_add' gam δ := P.endRight_eq ha hb fun α => by
    rw [← homPullLeft_apply, map_add, map_add, homPullLeft_apply, homPullLeft_apply,
      P.endRight_spec, P.endRight_spec, mul_add]

@[simp] theorem endRightHom_apply (ha : a < 0) (hb : b < 0) (P : HomPlacement S j E)
    (gam : E.End) : P.endRightHom ha hb gam = P.endRight gam := rfl

/-- Level endomorphisms act in the right order of the placed level ideal. -/
theorem endRight_mem_levelRight (P : HomPlacement S j E) {C : Subgroup (E.Pt k)}
    {C₀ : Subgroup (E₀.Pt k)} {N : ℕ} (hN : N ≠ 0) (hC₀ : ∀ x ∈ C₀, x ^ N = 1)
    (hC : ∀ x ∈ C, x ^ N = 1) {gam : E.End} (hgam : gam ∈ levelEnd E C) :
    P.endRight gam ∈ (levelIdeal P C₀ hN hC₀ C hC).rightRing := by
  intro y hy
  obtain ⟨α, hα, rfl⟩ := hy
  refine ⟨homPull gam α, ?_, P.endRight_spec gam α⟩
  intro x hx
  change x ≫ (gam.hom ≫ α.hom) ∈ C₀
  rw [← Category.assoc]
  exact hα _ (hgam x hx)

end HomPlacement

theorem int_eq_zero_of_forall_pow_dvd {p : ℕ} (hp : 1 < p) {z : ℤ}
    (h : ∀ n : ℕ, (p : ℤ) ^ n ∣ z) : z = 0 := by
  by_contra hz
  have h1 := Int.natAbs_dvd_natAbs.mpr (h z.natAbs)
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) h1
  have h3 : z.natAbs < p ^ z.natAbs := Nat.lt_pow_self hp
  omega

/-- An endomorphism with vanishing Tate map at a prime invertible in `k` is
zero, given any presentation of `End(E)` as an order. -/
theorem eq_zero_of_homT_eq_zero {a' b' : ℚ} (SE : Order a' b') (jE : E.End ≃+* SE.ring)
    (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0) {gam : E.End} (h : homT (ℓ := p) gam = 0) :
    gam = 0 := by
  have hdiv : ∀ n : ℕ, ∃ g : E.End, gam = (p ^ n : ℕ) • g := fun n =>
    exists_eq_nsmul_of_primeTo_homT_dvd gam p n hp (fun x => ⟨0, by simp [h]⟩)
  apply jE.injective
  rw [map_zero]
  apply SE.basis.repr.injective
  rw [map_zero]
  refine Finsupp.ext fun i => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply]
  apply int_eq_zero_of_forall_pow_dvd (Fact.out : p.Prime).one_lt
  intro n
  obtain ⟨g, hg⟩ := hdiv n
  refine ⟨SE.basis.repr (jE g) i, ?_⟩
  rw [hg, map_nsmul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_pow]

theorem exists_tateEquiv (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0) (hE : E.dim = 1)
    (hE₀ : E₀.dim = 1) : Nonempty (E.T p ≃ₗ[ℤ_[p]] E₀.T p) :=
  ⟨(nonempty_tateBasis p hp E hE).some.equiv (nonempty_tateBasis p hp E₀ hE₀).some
    (Equiv.refl _)⟩

/-- Every Tate map composed with `T_p γ` lies in the span of the Tate maps of
the composites `α ∘ γ`. -/
theorem comp_homT_mem_span (P : HomPlacement S j E) (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    (hE : E.dim = 1) (hE₀ : E₀.dim = 1) (gam : E.End) (M : Submodule ℤ_[p] (E.T p →ₗ[ℤ_[p]] E₀.T p))
    (hM : ∀ α : Hom E E₀, tateHom p E E₀ (homPull gam α) ∈ M)
    (φ : E.T p →ₗ[ℤ_[p]] E₀.T p) : φ.comp (homT (ℓ := p) gam) ∈ M := by
  have hφ : φ ∈ Submodule.span ℤ_[p] (Set.range (tateHom p E E₀)) := by
    rw [span_tateHom_eq_top P hp hE hE₀]
    trivial
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨α, rfl⟩ := hφ
    have h := hM α
    change homT (ℓ := p) (homPull gam α) ∈ M at h
    rw [homT_homPull] at h
    exact h
  | zero => rw [LinearMap.zero_comp]; exact M.zero_mem
  | add φ ψ _ _ h1 h2 => rw [LinearMap.add_comp]; exact M.add_mem h1 h2
  | smul c φ _ h1 => rw [LinearMap.smul_comp]; exact M.smul_mem c h1

theorem homT_eq_zero_of_forall (P : HomPlacement S j E) (p : ℕ) [Fact p.Prime]
    (hp : (p : k) ≠ 0) (hE : E.dim = 1) (hE₀ : E₀.dim = 1) (gam : E.End)
    (h : ∀ α : Hom E E₀, homPull gam α = 0) : homT (ℓ := p) gam = 0 := by
  obtain ⟨β⟩ := exists_tateEquiv p hp hE hE₀
  have h1 := comp_homT_mem_span P p hp hE hE₀ gam ⊥ (fun α => by
    rw [h α, map_zero]; exact Submodule.zero_mem _) β.toLinearMap
  rw [Submodule.mem_bot] at h1
  apply LinearMap.ext
  intro x
  have h2 := congrArg (fun f : E.T p →ₗ[ℤ_[p]] E₀.T p => β.symm (f x)) h1
  simpa using h2

/-- The right action of `End(E)` on a placement is injective. The frame
`(SE, jE)` of `E` enters only to know that `End(E)` is a lattice. -/
theorem endRight_injective (ha : a < 0) (hb : b < 0) (P : HomPlacement S j E)
    (hE : E.dim = 1) (hE₀ : E₀.dim = 1) {a' b' : ℚ} (SE : Order a' b') (jE : E.End ≃+* SE.ring)
    (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0) :
    Function.Injective (P.endRightHom ha hb) := by
  rw [injective_iff_map_eq_zero]
  intro gam hgam
  have hzero : ∀ α, homPull gam α = 0 := fun α => P.injective (by
    rw [P.endRight_spec, show P.endRight gam = 0 from hgam, mul_zero, map_zero])
  exact eq_zero_of_homT_eq_zero SE jE p hp (homT_eq_zero_of_forall P p hp hE hE₀ gam hzero)

end ZInQ.Manuscript.RC.HCMV21
