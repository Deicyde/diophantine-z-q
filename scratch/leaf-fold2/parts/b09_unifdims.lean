/-! ## leaf-fold2: unif-dims and product-unif §3b-§5 over this file's objects (see mk_unifdims.py) -/


/-! ## §3b. metrization's `JacDetDescends`, `productJacobian`, `productUniformizationAnalytic_of`, on the kernel's types

Verbatim copies (only `open PkgI3 (AbVar)` added after each `open … DefFaltings …` line, and
`#print` lines dropped) from `scratch/metrization/`: `part_exists.lean` lines 30-43 (the Prop
`ZInQ.Metrization.JacDetDescends`), `part_jacdet.lean` lines 1-138, `part_jacgerm.lean`,
`part_jacscalar.lean`, `part_jacclass.lean` lines 1-139. There they are stated over the
def-faltings copy in `scratch/metrization/Base.lean`; here over the kernel's `DefFaltings`
(`ZInQKernel/HDecomp/Faltings/Models.lean`, adopted from def-faltings). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- **Glue (the Jacobian descends to the Hodge line).** For an analytic uniformization `Φ` of
`𝒢(ℂ)_τ`, the Jacobian determinant `jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` depends only on the
classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`, is `𝓞_L`-multilinear (through `τ`) and alternating in them, hence is
the value on `1 ⊗ df₁ ∧ ⋯ ∧ df_g` of a `τ`-semilinear map `hodgeSpace g → ℂ`. Why true: `Φ 0 = 1`
lies over `ξ`; the germ `f ∘ Φ` at `0` is independent of the representative of `f` (`dom Φ U`
open); evaluation at a complex point is a ring map, so `(f f') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)` near `0`,
and for `f, f' ∈ 𝔪_ξ` both vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz); a function from
`𝓞_L` acts by the constant `τ(a)`. Then `⋀^g` (universal property) and `L ⊗_{𝓞_L} -` (extension
of scalars along `τ`) give the map. Elementary calculus plus Mathlib's scheme API; unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

end ZInQ.Metrization


/-! ## metrization: `JacDetDescends` reduced to four calculus properties of `jacDet`

The algebra (universal property of `⋀^g`, extension of scalars `L ⊗_{𝓞_L} -` along `τ`) is
proved; what remains (`JacDetMultilinear`) are four statements about the derivative at `0` of
germs composed with `Φ`. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- **Glue (calculus of `jacDet`).** For an analytic uniformization `Φ` of `𝒢(ℂ)_τ`, the map
`f ↦ jacDet Φ f = det(∂(f_i ∘ Φ)/∂z_j(0))` on `g`-tuples of germs in `𝔪_ξ`
(i) depends only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`;
(ii) is additive in each slot;
(iii) scales by `τ(a)` when slot `i` is multiplied by the image of `a ∈ 𝓞_L`;
(iv) vanishes when two slots are equal.
Why true: `Φ 0 = 1` lies over `ξ`, and `dom Φ U` is open, so the germ at `0` of `f ∘ Φ` does not
depend on the representative of `f`, and `(f + f') ∘ Φ = f ∘ Φ + f' ∘ Φ`, `(ff') ∘ Φ = (f ∘ Φ)(f' ∘ Φ)`
and `a ∘ Φ = τ(a)` near `0` (evaluation at a complex point is a ring map); for `f, f' ∈ 𝔪_ξ`,
`f ∘ Φ` and `f' ∘ Φ` vanish at `0`, so `d((ff') ∘ Φ)(0) = 0` (Leibniz), which gives (i); (ii)-(iv)
are row operations on the determinant. Elementary, unproved (needs the compatibility of
`evalAt` with restriction, sums, products and stalks in Mathlib's scheme API). -/
def JacDetMultilinear : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
      (x y : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (x + y)) =
        𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x)) ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g), f i = f j → i ≠ j →
      𝒢.jacDet Φ f = 0)

/-- **`JacDetDescends` from `JacDetMultilinear` (proved).** -/
theorem jacDetDescends_of (h : JacDetMultilinear) : JacDetDescends := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨hcls, hadd, hsmul, halt⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  classical
  letI : Module (𝓞 L) ℂ := Module.compHom ℂ (τ.comp (algebraMap (𝓞 L) L))
  have hsm : ∀ (a : 𝓞 L) (z : ℂ), a • z = τ (algebraMap (𝓞 L) L a) * z := fun _ _ => rfl
  let lift : 𝒢.cotangent → IsLocalRing.maximalIdeal 𝒢.genStalk :=
    Function.surjInv (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective
  have hlift : ∀ v, 𝒢.dCls (lift v) = v := fun v =>
    Function.surjInv_eq (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective v
  have hdadd : ∀ x y, 𝒢.dCls (x + y) = 𝒢.dCls x + 𝒢.dCls y := fun x y =>
    map_add (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent x y
  have hdsmul : ∀ (a : 𝓞 L) x, 𝒢.dCls (𝒢.structMap a • x) = a • 𝒢.dCls x := fun a x =>
    map_smul (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent (𝒢.structMap a) x
  let ψ : 𝒢.cotangent [⋀^Fin g]→ₗ[𝓞 L] ℂ :=
    { toFun := fun v => 𝒢.jacDet Φ (fun i => lift (v i))
      map_update_add' := by
        intro _ v i x y
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x + lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdadd]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        have e2 : 𝒢.jacDet Φ (fun j => lift (Function.update v i y j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift y)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (x + y) j)) =
          𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) +
            𝒢.jacDet Φ (fun j => lift (Function.update v i y j))
        rw [e0, e1, e2]
        convert hadd (fun j => lift (v j)) i (lift x) (lift y)
      map_update_smul' := by
        intro _ v i a x
        have e0 : 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (𝒢.structMap a • lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp [hlift, hdsmul]
          · simp [Function.update_apply, hj]
        have e1 : 𝒢.jacDet Φ (fun j => lift (Function.update v i x j)) =
            𝒢.jacDet Φ (Function.update (fun j => lift (v j)) i (lift x)) := by
          apply hcls
          intro j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_apply, hj]
        show 𝒢.jacDet Φ (fun j => lift (Function.update v i (a • x) j)) =
          a • 𝒢.jacDet Φ (fun j => lift (Function.update v i x j))
        rw [e0, e1, hsm]
        convert hsmul (fun j => lift (v j)) i a (lift x)
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        exact halt (fun k => lift (v k)) i j (by simp only [hv]) hij }
  let Ψ : ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ := exteriorPower.alternatingMapLinearEquiv ψ
  let B : L →ₗ[𝓞 L] ⋀[𝓞 L]^g 𝒢.cotangent →ₗ[𝓞 L] ℂ :=
    LinearMap.mk₂ (𝓞 L) (fun x w => τ x * Ψ w)
      (fun x y w => by rw [map_add, add_mul])
      (fun a x w => by
        rw [hsm, Algebra.smul_def, map_mul, _root_.mul_assoc])
      (fun x w w' => by rw [map_add, mul_add])
      (fun a x w => by
        rw [map_smul, hsm, hsm, mul_left_comm])
  let T : 𝒢.hodgeSpace g →ₗ[𝓞 L] ℂ := TensorProduct.lift B
  have hT : ∀ x w, T (x ⊗ₜ[𝓞 L] w) = τ x * Ψ w := fun x w => rfl
  let c : 𝒢.hodgeSpace g →ₛₗ[τ] ℂ :=
    { toFun := T
      map_add' := T.map_add
      map_smul' := by
        intro y t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul x w =>
          rw [TensorProduct.smul_tmul', hT, hT, smul_eq_mul, map_mul, _root_.mul_assoc]
          rfl
        | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, mul_add] }
  refine ⟨c, fun f => ?_⟩
  show T ((1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g (fun i => 𝒢.dCls (f i))) = 𝒢.jacDet Φ f
  rw [hT, map_one, _root_.one_mul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact hcls _ _ fun i => hlift _

end ZInQ.Metrization


/-! ## metrization: two of the four clauses of `JacDetMultilinear`, proved

`Φ 0 = 1` lies over `ξ` (`zero_mem_dom`); `germAlong Φ t` agrees near `0` with `z ↦ evalAt (Φ z) U s`
for every representative `(U, s)` of `t` (`germAlong_eventuallyEq`); hence slot additivity
(`jacDet_update_add`). Vanishing on equal slots is immediate (`jacDet_eq_zero_of_eq`). What
remains is `JacDetClassScalar` (clauses (i) and (iii)). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Germ

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec ℂ → Spec 𝓞_L` (via `τ`) hits the generic point. -/
theorem ptC_hom_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (GroupModel.ptC (L := L) τ).hom x = genericPt L := by
  haveI : x.asIdeal.IsPrime := x.isPrime
  have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
  apply PrimeSpectrum.ext
  show Ideal.comap (τ.comp (algebraMap (𝓞 L) L)) x.asIdeal = ⊥
  rw [hx]
  exact Ideal.comap_bot_of_injective _
    (τ.injective.comp (IsFractionRing.injective (𝓞 L) L))

/-- The identity complex point lies over `ξ`. -/
theorem one_left_apply (τ : L →+* ℂ) (x : Spec (CommRingCat.of ℂ)) :
    (1 : 𝒢.Pts τ).left x = 𝒢.genericUnit := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left x = 𝒢.unitSection (genericPt L)
  rw [Over.comp_left]
  change (η[𝒢.G]).left ((toUnit (GroupModel.ptC (L := L) τ)).left x) = _
  rw [hw, ptC_hom_apply]
  rfl

/-- For an analytic uniformization, `0 ∈ dom Φ U` whenever `ξ ∈ U`. -/
theorem zero_mem_dom {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := by
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  show ⊤ ≤ (Φ 0).left ⁻¹ᵁ U
  rw [h1]
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ U
  erw [one_left_apply]
  exact m

/-- `evalAt` is compatible with restriction. -/
theorem evalAt_res {τ : L →+* ℂ} (p : 𝒢.Pts τ) {U W : 𝒢.G.left.Opens} (i : W ⟶ U)
    (hW : ⊤ ≤ p.left ⁻¹ᵁ W) (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p W (𝒢.G.left.presheaf.map i.op s) = 𝒢.evalAt p U s := by
  have hU : ⊤ ≤ p.left ⁻¹ᵁ U := hW.trans ((TopologicalSpace.Opens.map p.left.base).map i).le
  unfold GroupModel.evalAt
  rw [dif_pos hW, dif_pos hU, ← Scheme.Hom.map_appLE p.left hW i.op]
  rfl

/-- `evalAt` is additive in the section. -/
theorem evalAt_add {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s + s') = 𝒢.evalAt p U s + 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- **`germAlong Φ t` is, near `0`, the function of any representative of `t`.** -/
theorem germAlong_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U) (s : Γ(𝒢.G.left, U)) :
    𝒢.germAlong Φ (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s) =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) U s := by
  unfold GroupModel.germAlong
  obtain ⟨W, mW, i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit _ m _ s
    (𝒢.exists_rep (𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s)).choose_spec.choose_spec.choose_spec
  filter_upwards [(hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz
  rw [← evalAt_res 𝒢 (Φ z) i₁ hz, ← evalAt_res 𝒢 (Φ z) i₂ hz s, hW]

/-- `germAlong Φ t` is differentiable at `0`. -/
theorem germAlong_differentiableAt {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk) :
    DifferentiableAt ℂ (𝒢.germAlong Φ t) 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep t
  have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) U s) 0 :=
    (hΦ.2.2.2.2 U s).differentiableAt ((hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m))
  exact hd.congr_of_eventuallyEq (germAlong_eventuallyEq 𝒢 hΦ U m s)

/-- `germAlong Φ (x + y) = germAlong Φ x + germAlong Φ y` near `0`. -/
theorem germAlong_add_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x + y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x + 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hsum : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s +
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s +
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_add, TopCat.Presheaf.germ_res_apply]
  rw [hsum]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.add_apply, h1, h2, h3, evalAt_add, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- **Clause (ii) of `JacDetMultilinear`, proved: slot additivity.** -/
theorem jacDet_update_add {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g)
    (x y : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (x + y)) =
      𝒢.jacDet Φ (Function.update f i x) + 𝒢.jacDet Φ (Function.update f i y) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((x + y : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      row (x : 𝒢.genStalk) + row (y : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_add, Pi.add_apply]
    rw [(germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, e, hrow, Matrix.det_updateRow_add]

/-- **Clause (iv) of `JacDetMultilinear`, proved: equal slots give `0`.** -/
theorem jacDet_eq_zero_of_eq {τ : L →+* ℂ} {g : ℕ} (Φ : (Fin g → ℂ) → 𝒢.Pts τ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i j : Fin g) (h : f i = f j)
    (hij : i ≠ j) : 𝒢.jacDet Φ f = 0 := by
  unfold GroupModel.jacDet
  apply Matrix.det_zero_of_row_eq hij
  funext k
  simp [h]

end Germ

/-- **Glue (the two remaining clauses of `JacDetMultilinear`).** (i) `jacDet Φ f` depends only on
the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`; (iii) multiplying slot `i` by the image of `a ∈ 𝓞_L` multiplies
`jacDet` by `τ(a)`. Why true: by `germAlong_eventuallyEq` it suffices that for `f ∈ 𝔪_ξ²` the
function `evalAt (Φ z) U s` of a representative has derivative `0` at `0` (it is a sum of products
of functions vanishing at `0`, as evaluation at a complex point over `ξ` kills `𝔪_ξ`: the induced
map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ` is local), and that the image of `a` evaluates to `τ(a)` (the point
lies over `Spec 𝓞_L` through `τ`). Unproved: needs `evalAt` through `Scheme.Hom.stalkMap` and
`ΓSpecIso`. -/
def JacDetClassScalar : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    (∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f') ∧
    (∀ (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
      (x : IsLocalRing.maximalIdeal 𝒢.genStalk),
      𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
        τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x))

/-- **`JacDetMultilinear` from `JacDetClassScalar` (proved).** -/
theorem jacDetMultilinear_of (h : JacDetClassScalar) : JacDetMultilinear := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  obtain ⟨h1, h3⟩ := h K A L 𝒢 τ g Λ Φ hΦ
  exact ⟨h1, fun f i x y => jacDet_update_add 𝒢 hΦ f i x y, h3,
    fun f i j hij hne => jacDet_eq_zero_of_eq 𝒢 Φ f i j hij hne⟩

end ZInQ.Metrization



/-! ## metrization: clause (iii) of `JacDetMultilinear` (scaling by `τ(a)`), proved -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section Scalar

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `evalAt` is multiplicative in the section. -/
theorem evalAt_mul {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s * s') = 𝒢.evalAt p U s * 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

/-- A function from `𝓞_L` evaluates to `τ(a)` at every complex point. -/
theorem evalAt_structSection {τ : L →+* ℂ} (p : 𝒢.Pts τ) (a : 𝓞 L) :
    𝒢.evalAt p ⊤ (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      τ (algebraMap (𝓞 L) L a) := by
  have htop : ⊤ ≤ p.left ⁻¹ᵁ (⊤ : 𝒢.G.left.Opens) := fun x _ => trivial
  unfold GroupModel.evalAt
  rw [dif_pos htop]
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have h1 : p.left.appLE ⊤ ⊤ htop = p.left.appTop := Scheme.Hom.appLE_eq_app p.left
  have h2 : (p.left.appTop) (𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a)) =
      ((p.left ≫ 𝒢.G.hom).appTop) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) := by
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [h1, h2, hw]
  have h3 := congrArg (fun f => f ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L))))
  simp only [ConcreteCategory.comp_apply] at h3
  refine h3.trans ?_
  simp

/-- `germAlong Φ (structMap a * x) = τ(a) · germAlong Φ x` near `0`. -/
theorem germAlong_structMap_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (a : 𝓞 L)
    (x : 𝒢.genStalk) :
    𝒢.germAlong Φ (𝒢.structMap a * x) =ᶠ[𝓝 0]
      fun z => τ (algebraMap (𝓞 L) L a) * 𝒢.germAlong Φ x z := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  set σa : Γ(𝒢.G.left, ⊤) :=
    𝒢.G.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 L))).inv a) with hσa
  have hprod : 𝒢.structMap a * 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s =
      𝒢.G.left.presheaf.germ U 𝒢.genericUnit m
        (𝒢.G.left.presheaf.map (homOfLE le_top).op σa * s) := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply]
    rfl
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ U m _, germAlong_eventuallyEq 𝒢 hΦ U m s,
    (hΦ.2.2.2.1 U).mem_nhds (zero_mem_dom 𝒢 hΦ U m)] with z h1 h2 hz
  rw [h1, h2, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz, hσa, evalAt_structSection]

/-- **Clause (iii) of `JacDetMultilinear`, proved: scaling by `τ(a)`.** -/
theorem jacDet_update_smul {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk) (i : Fin g) (a : 𝓞 L)
    (x : IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.jacDet Φ (Function.update f i (𝒢.structMap a • x)) =
      τ (algebraMap (𝓞 L) L a) * 𝒢.jacDet Φ (Function.update f i x) := by
  let row : 𝒢.genStalk → Fin g → ℂ := fun t j => fderiv ℂ (𝒢.germAlong Φ t) 0 (Pi.single j 1)
  have hrow : row ((𝒢.structMap a • x : IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.genStalk) =
      τ (algebraMap (𝓞 L) L a) • row (x : 𝒢.genStalk) := by
    funext j
    simp only [row, Submodule.coe_smul, smul_eq_mul, Pi.smul_apply]
    rw [(germAlong_structMap_mul_eventuallyEq 𝒢 hΦ a _).fderiv_eq,
      fderiv_const_mul (germAlong_differentiableAt 𝒢 hΦ _)]
    rfl
  let M : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun k j => row (f k : 𝒢.genStalk) j
  have e : ∀ z : IsLocalRing.maximalIdeal 𝒢.genStalk,
      𝒢.jacDet Φ (Function.update f i z) = (M.updateRow i (row (z : 𝒢.genStalk))).det := by
    intro z
    unfold GroupModel.jacDet
    congr 1
    ext k j
    by_cases hk : k = i
    · subst hk; simp [M, row]
    · simp [M, row, hk]
  rw [e, e, hrow, Matrix.det_updateRow_smul]

end Scalar

/-- **Glue (the last clause of `JacDetMultilinear`: class invariance).** `jacDet Φ f` depends
only on the classes `df_i ∈ 𝔪_ξ/𝔪_ξ²`. Why true: by `germAlong_eventuallyEq` and
`germAlong_add_eventuallyEq` it suffices that `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`, a sum of
products `uv` with `u, v ∈ 𝔪_ξ`; `germAlong Φ (uv) = (germAlong Φ u)(germAlong Φ v)` near `0` (as
for sums, with `evalAt_mul`), and `germAlong Φ u` vanishes at `0` because the identity point
`Spec ℂ → 𝒢` lies over `ξ` (`one_left_apply`) and induces a local map `𝒪_{𝒢,ξ} → 𝒪_{Spec ℂ} = ℂ`,
which kills `𝔪_ξ`; then Leibniz. Unproved (needs `evalAt` through `Scheme.Hom.stalkMap` at the
identity point). -/
def JacDetClassInvariant : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∀ f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk,
      (∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) → 𝒢.jacDet Φ f = 𝒢.jacDet Φ f'

/-- **`JacDetClassScalar` from `JacDetClassInvariant` (proved).** -/
theorem jacDetClassScalar_of (h : JacDetClassInvariant) : JacDetClassScalar := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ
  exact ⟨h K A L 𝒢 τ g Λ Φ hΦ, fun f i a x => jacDet_update_smul 𝒢 hΦ f i a x⟩

end ZInQ.Metrization



/-! ## metrization: clause (i) of `JacDetMultilinear` (class invariance), proved

So `JacDetMultilinear`, hence `JacDetDescends`, is a theorem. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section ClassInv

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- A section whose germ at `ξ` lies in `𝔪_ξ` vanishes at the identity complex point. -/
theorem evalAt_one_eq_zero {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ U)
    (s : Γ(𝒢.G.left, U))
    (hs : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) :
    𝒢.evalAt (1 : 𝒢.Pts τ) U s = 0 := by
  set q := (1 : 𝒢.Pts τ).left with hqdef
  have hq : ∀ x, q x = 𝒢.genericUnit := fun x => by
    rw [hqdef]
    erw [one_left_apply]
  have h : ⊤ ≤ q ⁻¹ᵁ U := by
    intro x _
    show q x ∈ U
    rw [hq]
    exact m
  unfold GroupModel.evalAt
  rw [dif_pos h]
  let q' : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left := q
  have h' : ⊤ ≤ q' ⁻¹ᵁ U := h
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q'.appLE U ⊤ h' s) = 0
  let x : Spec (CommRingCat.of ℂ) := genericPoint (Spec (CommRingCat.of ℂ))
  have hxt : x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := by simp
  have hx : q' x ∈ U := h' hxt
  have key : q'.appLE U ⊤ h' ≫ (Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt =
      𝒢.G.left.presheaf.germ U (q' x) hx ≫ q'.stalkMap x := by
    simp only [Scheme.Hom.appLE, Category.assoc, Scheme.Hom.germ_stalkMap]
    rw [TopCat.Presheaf.germ_res]
  have hmem : ∀ (y : 𝒢.G.left) (hy : y ∈ U), y = 𝒢.genericUnit →
      𝒢.G.left.presheaf.germ U y hy s ∈
        IsLocalRing.maximalIdeal (𝒢.G.left.presheaf.stalk y) := by
    rintro y hy rfl
    exact hs
  have h1 := hmem (q' x) hx (hq x)
  have h2 : (q'.stalkMap x).hom (𝒢.G.left.presheaf.germ U (q' x) hx s) ∈
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) :=
    map_nonunit _ _ ((IsLocalRing.mem_maximalIdeal _).mp h1)
  have hfield : IsField ((Spec (CommRingCat.of ℂ)).presheaf.stalk x) := Field.toIsField _
  rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield] at h2
  have h4 : ((Spec (CommRingCat.of ℂ)).presheaf.germ ⊤ x hxt) (q'.appLE U ⊤ h' s) =
      (q'.stalkMap x) (𝒢.G.left.presheaf.germ U (q' x) hx s) := by
    rw [← ConcreteCategory.comp_apply, key, ConcreteCategory.comp_apply]
  have h5 : q'.appLE U ⊤ h' s = 0 := by
    apply germ_injective_of_isIntegral (U := ⊤) _ x hxt
    rw [map_zero]
    exact h4.trans h2
  rw [h5, map_zero]

/-- `germAlong Φ u` vanishes at `0` for `u ∈ 𝔪_ξ`. -/
theorem germAlong_zero_of_mem {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (u : 𝒢.genStalk)
    (hu : u ∈ IsLocalRing.maximalIdeal 𝒢.genStalk) : 𝒢.germAlong Φ u 0 = 0 := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep u
  have h1 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  rw [(germAlong_eventuallyEq 𝒢 hΦ U m s).eq_of_nhds, h1]
  exact evalAt_one_eq_zero 𝒢 U m s hu

/-- `germAlong Φ (x * y) = germAlong Φ x * germAlong Φ y` near `0`. -/
theorem germAlong_mul_eventuallyEq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (x y : 𝒢.genStalk) :
    𝒢.germAlong Φ (x * y) =ᶠ[𝓝 0] 𝒢.germAlong Φ x * 𝒢.germAlong Φ y := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢.exists_rep x
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep y
  have mm : 𝒢.genericUnit ∈ U ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hprod : 𝒢.G.left.presheaf.germ U 𝒢.genericUnit m s *
      𝒢.G.left.presheaf.germ U' 𝒢.genericUnit m' s' =
      𝒢.G.left.presheaf.germ (U ⊓ U') 𝒢.genericUnit mm
        (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
          𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') := by
    simp only [map_mul, TopCat.Presheaf.germ_res_apply]
  rw [hprod]
  filter_upwards [germAlong_eventuallyEq 𝒢 hΦ (U ⊓ U') mm _,
    germAlong_eventuallyEq 𝒢 hΦ U m s, germAlong_eventuallyEq 𝒢 hΦ U' m' s',
    (hΦ.2.2.2.1 (U ⊓ U')).mem_nhds (zero_mem_dom 𝒢 hΦ (U ⊓ U') mm)] with z h1 h2 h3 hz
  rw [Pi.mul_apply, h1, h2, h3, evalAt_mul, evalAt_res 𝒢 (Φ z) _ hz,
    evalAt_res 𝒢 (Φ z) _ hz]

/-- `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²`. -/
theorem fderiv_germAlong_eq_zero_of_mem_sq {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (t : 𝒢.genStalk)
    (ht : t ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2) :
    fderiv ℂ (𝒢.germAlong Φ t) 0 = 0 := by
  rw [pow_two] at ht
  refine Submodule.mul_induction_on ht (fun u hu v hv => ?_) (fun a b ha hb => ?_)
  · rw [(germAlong_mul_eventuallyEq 𝒢 hΦ u v).fderiv_eq,
      fderiv_mul (germAlong_differentiableAt 𝒢 hΦ u) (germAlong_differentiableAt 𝒢 hΦ v),
      germAlong_zero_of_mem 𝒢 hΦ u hu, germAlong_zero_of_mem 𝒢 hΦ v hv]
    ext v
    simp
  · rw [(germAlong_add_eventuallyEq 𝒢 hΦ a b).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ a) (germAlong_differentiableAt 𝒢 hΦ b), ha, hb,
      add_zero]

/-- **Clause (i) of `JacDetMultilinear`, proved: `jacDet` depends only on the classes `df_i`.** -/
theorem jacDet_congr_dCls {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ)
    (f f' : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk)
    (h : ∀ i, 𝒢.dCls (f i) = 𝒢.dCls (f' i)) : 𝒢.jacDet Φ f = 𝒢.jacDet Φ f' := by
  have hrow : ∀ i, fderiv ℂ (𝒢.germAlong Φ (f i : 𝒢.genStalk)) 0 =
      fderiv ℂ (𝒢.germAlong Φ (f' i : 𝒢.genStalk)) 0 := by
    intro i
    have hsq : ((f i : 𝒢.genStalk) - f' i) ∈ IsLocalRing.maximalIdeal 𝒢.genStalk ^ 2 :=
      (Ideal.toCotangent_eq (IsLocalRing.maximalIdeal 𝒢.genStalk)).mp (h i)
    have hdecomp : (f i : 𝒢.genStalk) = f' i + ((f i : 𝒢.genStalk) - f' i) := by ring
    rw [hdecomp, (germAlong_add_eventuallyEq 𝒢 hΦ _ _).fderiv_eq,
      fderiv_add (germAlong_differentiableAt 𝒢 hΦ _) (germAlong_differentiableAt 𝒢 hΦ _),
      fderiv_germAlong_eq_zero_of_mem_sq 𝒢 hΦ _ hsq, add_zero]
  unfold GroupModel.jacDet
  congr 1
  ext i j
  simp only [Matrix.of_apply, hrow i]

end ClassInv

/-- **`JacDetClassInvariant`, proved.** -/
theorem jacDetClassInvariant : JacDetClassInvariant := by
  intro K _ A L _ _ _ 𝒢 τ g Λ Φ hΦ f f' h
  exact jacDet_congr_dCls 𝒢 hΦ f f' h

/-- **`JacDetDescends`, proved** (no hypotheses). -/
theorem jacDetDescends : JacDetDescends :=
  jacDetDescends_of (jacDetMultilinear_of (jacDetClassScalar_of jacDetClassInvariant))

end ZInQ.Metrization


/-! Further verbatim copies from `scratch/metrization/` (only `open PkgI3 (AbVar)` added, the
declarations after the cut points dropped): `part_prodgeo.lean` up to `ProductLatticeFacts`
(exclusive), `part_prodlat.lean` up to `blockLinearEquiv` (exclusive), `part_produnif.lean` up to
`productUniformization_of` (exclusive), `part_prodsplit.lean` up to `productHodgeCompat_of`
(exclusive), `part_prodjac.lean` up to `productMetrizationGeo_of'''` (exclusive),
`part_produnif2.lean` up to `productMetrizationGeo_of_local` (exclusive). -/


/-! ## metrization (2026-11-13): `ProductMetrizationGeo` reduced

`ProductMetrizationGeo` (P2a-geo) follows from `JacDetDescends` (shared with `MetrizationExists`),
`ProductUniformization` (glue: `Φ₁ × Φ₂` is an analytic uniformization of the product model),
`ProductLatticeFacts` (pure Mathlib glue: `Λ₁ × Λ₂` is a full lattice and covolumes multiply)
and `ProductHodgeCompat` (glue: `⋀^{top}ω_{𝒢P} = ⋀ω₁ ⊗ ⋀ω₂` with the block-diagonal Jacobian). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- The first `g₁` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def leftBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₁ → ℂ) :=
  LinearMap.pi fun i => LinearMap.proj (Fin.castAdd g₂ i)

/-- The last `g₂` coordinates of `ℂ^{g₁+g₂}`. -/
noncomputable def rightBlock (g₁ g₂ : ℕ) : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ) :=
  LinearMap.pi fun j => LinearMap.proj (Fin.natAdd g₁ j)

/-- The product lattice `Λ₁ × Λ₂ ⊂ ℂ^{g₁} × ℂ^{g₂} = ℂ^{g₁+g₂}` (coordinates `Fin.append`). -/
noncomputable def prodLattice {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) : Submodule ℤ (Fin (g₁ + g₂) → ℂ) :=
  Λ₁.comap (leftBlock g₁ g₂).toAddMonoidHom.toIntLinearMap ⊓
    Λ₂.comap (rightBlock g₁ g₂).toAddMonoidHom.toIntLinearMap

/-- The product map `ℂ^{g₁+g₂} → 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ ≅ 𝒢P(ℂ)_τ`, `z ↦ e⁻¹(Φ₁(z'), Φ₂(z''))`. -/
noncomputable def prodPts {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) :
    (Fin (g₁ + g₂) → ℂ) → 𝒢P.Pts τ :=
  fun z => lift (Φ₁ (leftBlock g₁ g₂ z)) (Φ₂ (rightBlock g₁ g₂ z)) ≫ e.inv

end ZInQ.Metrization


/-! ## metrization: `ProductLatticeFacts`, proved (body of ProdLattice.lean, section Proof) -/

namespace ZInQ.Metrization

open MeasureTheory

section Proof

variable {g₁ g₂ : ℕ}

@[simp] theorem leftBlock_apply (z : Fin (g₁ + g₂) → ℂ) (i : Fin g₁) :
    leftBlock g₁ g₂ z i = z (Fin.castAdd g₂ i) := rfl

@[simp] theorem rightBlock_apply (z : Fin (g₁ + g₂) → ℂ) (j : Fin g₂) :
    rightBlock g₁ g₂ z j = z (Fin.natAdd g₁ j) := rfl

theorem mem_prodLattice {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {z : Fin (g₁ + g₂) → ℂ} :
    z ∈ prodLattice Λ₁ Λ₂ ↔ leftBlock g₁ g₂ z ∈ Λ₁ ∧ rightBlock g₁ g₂ z ∈ Λ₂ := Iff.rfl

theorem eq_of_blocks {z w : Fin (g₁ + g₂) → ℂ} (h1 : leftBlock g₁ g₂ z = leftBlock g₁ g₂ w)
    (h2 : rightBlock g₁ g₂ z = rightBlock g₁ g₂ w) : z = w := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · exact congrFun h1 i
  · exact congrFun h2 j

@[simp] theorem leftBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    leftBlock g₁ g₂ (Fin.append x y) = x := by
  funext i; simp

@[simp] theorem rightBlock_append (x : Fin g₁ → ℂ) (y : Fin g₂ → ℂ) :
    rightBlock g₁ g₂ (Fin.append x y) = y := by
  funext j; simp

end Proof

end ZInQ.Metrization


/-! ## metrization: the algebraic half of `ProductUniformization`, proved

`prodPts e Φ₁ Φ₂` is a surjective homomorphism with kernel `Λ₁ × Λ₂` (from `e` and the universal
property of `⊗`); `ProductUniformization` is reduced to `ProductUniformizationAnalytic` (openness
of `dom` and holomorphy). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section ProdPtsAlg

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ}

theorem prodPts_comp_fst (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ fst _ _ = Φ₁ (leftBlock g₁ g₂ z) := by
  simp [prodPts]

theorem prodPts_comp_snd (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ)
    (z : Fin (g₁ + g₂) → ℂ) : prodPts e Φ₁ Φ₂ z ≫ e.hom ≫ snd _ _ = Φ₂ (rightBlock g₁ g₂ z) := by
  simp [prodPts]

theorem pts_ext {p q : 𝒢P.Pts τ} (h1 : p ≫ e.hom ≫ fst _ _ = q ≫ e.hom ≫ fst _ _)
    (h2 : p ≫ e.hom ≫ snd _ _ = q ≫ e.hom ≫ snd _ _) : p = q := by
  rw [← cancel_mono e.hom]
  apply CartesianMonoidalCategory.hom_ext
  · simpa using h1
  · simpa using h2

/-- **The algebraic clauses of `IsAnalyticUniformization` for `prodPts` (proved).** -/
theorem prodPts_alg (hfst : IsMonHom (e.hom ≫ fst _ _)) (hsnd : IsMonHom (e.hom ≫ snd _ _))
    {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
    {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}
    (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁) (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) :
    (∀ z w, prodPts e Φ₁ Φ₂ (z + w) = prodPts e Φ₁ Φ₂ z * prodPts e Φ₁ Φ₂ w) ∧
    (∀ z, prodPts e Φ₁ Φ₂ z = 1 ↔ z ∈ prodLattice Λ₁ Λ₂) ∧
    Function.Surjective (prodPts e Φ₁ Φ₂) := by
  refine ⟨fun z w => ?_, fun z => ?_, fun p => ?_⟩
  · apply pts_ext e
    · rw [MonObj.mul_comp, prodPts_comp_fst, prodPts_comp_fst, prodPts_comp_fst, map_add,
        h₁.1]
    · rw [MonObj.mul_comp, prodPts_comp_snd, prodPts_comp_snd, prodPts_comp_snd, map_add,
        h₂.1]
  · constructor
    · intro h
      have e1 : Φ₁ (leftBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_fst e Φ₁ Φ₂ z, h, MonObj.one_comp]
      have e2 : Φ₂ (rightBlock g₁ g₂ z) = 1 := by
        rw [← prodPts_comp_snd e Φ₁ Φ₂ z, h, MonObj.one_comp]
      exact mem_prodLattice.mpr ⟨(h₁.2.1 _).mp e1, (h₂.2.1 _).mp e2⟩
    · intro hz
      obtain ⟨hz1, hz2⟩ := mem_prodLattice.mp hz
      apply pts_ext e
      · rw [prodPts_comp_fst, MonObj.one_comp, (h₁.2.1 _).mpr hz1]
      · rw [prodPts_comp_snd, MonObj.one_comp, (h₂.2.1 _).mpr hz2]
  · obtain ⟨x, hx⟩ := h₁.2.2.1 (p ≫ e.hom ≫ fst _ _)
    obtain ⟨y, hy⟩ := h₂.2.2.1 (p ≫ e.hom ≫ snd _ _)
    refine ⟨Fin.append x y, pts_ext e ?_ ?_⟩
    · rw [prodPts_comp_fst, leftBlock_append, hx]
    · rw [prodPts_comp_snd, rightBlock_append, hy]

end ProdPtsAlg

/-- **Glue (the analytic half of the product uniformization).** With the hypotheses of
`ProductUniformization`: each `dom (prodPts e Φ₁ Φ₂) U` is open and each regular function on `U`
is holomorphic along `prodPts e Φ₁ Φ₂` there. Why true: as in `ProductUniformization` (basic opens
`D(h)` of products of affine opens; regular functions `a/hⁿ`, `a, h ∈ R₁ ⊗_{𝓞_L} R₂`). STANDARD,
unproved. -/
def ProductUniformizationAnalytic : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G), IsMonHom (e.hom ≫ fst _ _) → IsMonHom (e.hom ≫ snd _ _) →
    ∀ (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
      (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
      (∀ U, IsOpen (𝒢P.dom (prodPts e Φ₁ Φ₂) U)) ∧
      (∀ U (s : Γ(𝒢P.G.left, U)), DifferentiableOn ℂ
        (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) (𝒢P.dom (prodPts e Φ₁ Φ₂) U))

end ZInQ.Metrization


/-! ## metrization: `ProductHodgeCompat` split into an algebraic and an analytic Prop

`pullGerm φ : 𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}` (pull-back of germs along a homomorphism of group models; it
needs `φ(ξ_𝒢) = ξ_ℋ`, proved from `IsMonHom`). `ProductHodgeLattice` (algebra: `s = p₁*s₁ ∧ p₂*s₂`
lies in the lattice with multiplicative index) and `ProductJacobian` (analysis: block-diagonal
Jacobian) give `ProductHodgeCompat` (with `ProductUniformization`). -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

section Pull

variable {K : Type} [Field K] {A C : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A homomorphism of group models maps the identity `ξ` of the generic fibre to `ξ` (proved). -/
theorem map_genericUnit_of_isMonHom {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : φ.left 𝒢.genericUnit = ℋ.genericUnit := by
  have h1 : η[𝒢.G] ≫ φ = η[ℋ.G] := IsMonHom.one_hom φ
  have h2 : (η[𝒢.G]).left ≫ φ.left = (η[ℋ.G]).left := by rw [← Over.comp_left, h1]
  show φ.left ((η[𝒢.G]).left (genericPt L)) = (η[ℋ.G]).left (genericPt L)
  rw [← h2]
  rfl

/-- Pull-back of germs at `ξ` along a homomorphism of group models: `𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}`. -/
noncomputable def pullGerm {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G)
    [IsMonHom φ] : ℋ.genStalk ⟶ 𝒢.genStalk :=
  ℋ.G.left.presheaf.stalkSpecializes
      ((congrArg (fun x => x ⤳ ℋ.genericUnit) (map_genericUnit_of_isMonHom φ)).mpr
        specializes_rfl) ≫
    φ.left.stalkMap 𝒢.genericUnit

end Pull

/-- **Glue (algebra: the Hodge lattice of a product).** For `e : 𝒢P ≅ M₁.model × M₂.model` with
homomorphic components: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line, and there are germ tuples
`f₁, f₂` and their pull-backs `f = (p₁*f₁, p₂*f₂)`, and `a₁, a₂ ∈ L`, such that `sᵢ = aᵢ · 1⊗dfᵢ`
are nonzero elements of `⋀ω_{𝒢ᵢ}`, `s = a₁a₂ · 1⊗df` is a nonzero element of `⋀ω_{𝒢P}`, and
`[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`. Why true (STANDARD): `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` and
`𝔪_ξ/𝔪_ξ² = p₁*C₁ ⊕ p₂*C₂` for a product of smooth group schemes (EGA IV 17.2.3, UNVERIFIED
locator), so `⋀^{g₁+g₂}` is the tensor product of the two lines; for invertible `𝓞_L`-modules
indices multiply (norms of ideals). Unproved (stalks and differentials of fibre products are
not in Mathlib). -/
def ProductHodgeLattice : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂)
    (e : 𝒢P.G ≅ M₁.model.G ⊗ M₂.model.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    Module.finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1 ∧
    ∃ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal M₁.model.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal M₂.model.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk) (a₁ a₂ : L),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) ∧
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) ∧
      a₁ • M₁.model.wedge f₁ ∈ M₁.hodge.lattice ∧ a₁ • M₁.model.wedge f₁ ≠ 0 ∧
      a₂ • M₂.model.wedge f₂ ∈ M₂.hodge.lattice ∧ a₂ • M₂.model.wedge f₂ ≠ 0 ∧
      (a₁ * a₂) • 𝒢P.wedge f ∈ 𝒢P.detLattice (g₁ + g₂) ∧ (a₁ * a₂) • 𝒢P.wedge f ≠ 0 ∧
      secIndex (𝒢P.detLattice (g₁ + g₂)) ((a₁ * a₂) • 𝒢P.wedge f) =
        secIndex M₁.hodge.lattice (a₁ • M₁.model.wedge f₁) *
          secIndex M₂.hodge.lattice (a₂ • M₂.model.wedge f₂)

/-- **Glue (analysis: the Jacobian of the product uniformization is block diagonal).** If
`prodPts e Φ₁ Φ₂` is an analytic uniformization and `f = (p₁*f₁, p₂*f₂)`, then
`jacDet (prodPts e Φ₁ Φ₂) f = jacDet Φ₁ f₁ · jacDet Φ₂ f₂`. Why true: `p₁ ∘ prodPts = Φ₁ ∘ leftBlock`
(`prodPts_comp_fst`), so near `0` the germ `(p₁*f₁ᵢ) ∘ prodPts` is `f₁ᵢ ∘ Φ₁ ∘ leftBlock` (the
representatives agree on an open `V ∋ ξ` and `dom (prodPts) V` is open), whose derivative
vanishes on the last `g₂` coordinates; the matrix is block diagonal (`Matrix.det_fromBlocks_zero₂₁`
after `finSumFinEquiv`). Elementary, unproved (needs the `evalAt`/stalk compatibilities of
`JacDetMultilinear` and functoriality of `evalAt` along morphisms). -/
def ProductJacobian : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _))
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂) →
    ∀ (f₁ : Fin g₁ → IsLocalRing.maximalIdeal 𝒢₁.genStalk)
      (f₂ : Fin g₂ → IsLocalRing.maximalIdeal 𝒢₂.genStalk)
      (f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk),
      (∀ i, (f (Fin.castAdd g₂ i) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ fst _ _)).hom (f₁ i)) →
      (∀ j, (f (Fin.natAdd g₁ j) : 𝒢P.genStalk) = (pullGerm (e.hom ≫ snd _ _)).hom (f₂ j)) →
      𝒢P.jacDet (prodPts e Φ₁ Φ₂) f = 𝒢₁.jacDet Φ₁ f₁ * 𝒢₂.jacDet Φ₂ f₂

end ZInQ.Metrization


/-! ## metrization: `ProductJacobian`, proved (block-diagonal Jacobian of `prodPts`) -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

section ProdJac

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- Pull-back of a germ is the germ of the pulled-back section. -/
theorem pullGerm_germ {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) [IsMonHom φ]
    (U : ℋ.G.left.Opens) (m : ℋ.genericUnit ∈ U) (s : Γ(ℋ.G.left, U)) :
    (pullGerm φ).hom (ℋ.G.left.presheaf.germ U ℋ.genericUnit m s) =
      𝒢.G.left.presheaf.germ (φ.left ⁻¹ᵁ U) 𝒢.genericUnit
        (by show φ.left 𝒢.genericUnit ∈ U; rw [map_genericUnit_of_isMonHom φ]; exact m)
        (φ.left.app U s) := by
  unfold pullGerm
  rw [ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes_apply,
    Scheme.Hom.germ_stalkMap_apply]

/-- `evalAt` along a morphism of models. -/
theorem evalAt_comp {𝒢 : GroupModel C L} {ℋ : GroupModel A L} (φ : 𝒢.G ⟶ ℋ.G) {τ : L →+* ℂ}
    (p : 𝒢.Pts τ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (hp : ⊤ ≤ p.left ⁻¹ᵁ (φ.left ⁻¹ᵁ U)) :
    𝒢.evalAt p (φ.left ⁻¹ᵁ U) (φ.left.app U s) = ℋ.evalAt (p ≫ φ) U s := by
  have hp' : ⊤ ≤ (p ≫ φ).left ⁻¹ᵁ U := hp
  unfold GroupModel.evalAt
  rw [dif_pos hp, dif_pos hp']
  rw [show (p ≫ φ).left.appLE U ⊤ hp' = φ.left.app U ≫ p.left.appLE (φ.left ⁻¹ᵁ U) ⊤ hp from
    Scheme.Hom.comp_appLE p.left φ.left U ⊤ hp']
  rfl

variable {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
  {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)} {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)}
  {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem germAlong_pull_fst_eventuallyEq (hΦ₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₁.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ fst _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₁.germAlong Φ₁ t (leftBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₁.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (leftBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (leftBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₁ hΦ₁ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ fst _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ fst _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₁.germAlong Φ₁ (𝒢₁.G.left.presheaf.germ U 𝒢₁.genericUnit m s) (leftBlock g₁ g₂ z) =
      𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_fst]

theorem germAlong_pull_snd_eventuallyEq (hΦ₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂)
    (hΦP : 𝒢P.IsAnalyticUniformization τ (prodLattice Λ₁ Λ₂) (prodPts e Φ₁ Φ₂))
    (t : 𝒢₂.genStalk) :
    𝒢P.germAlong (prodPts e Φ₁ Φ₂) ((pullGerm (e.hom ≫ snd _ _)).hom t) =ᶠ[𝓝 0]
      fun z => 𝒢₂.germAlong Φ₂ t (rightBlock g₁ g₂ z) := by
  obtain ⟨U, m, s, rfl⟩ := 𝒢₂.exists_rep t
  rw [pullGerm_germ]
  have ht : Filter.Tendsto (rightBlock g₁ g₂) (𝓝 0) (𝓝 0) :=
    (rightBlock g₁ g₂).continuous_of_finiteDimensional.tendsto' 0 0 (map_zero _)
  filter_upwards [germAlong_eventuallyEq 𝒢P hΦP _ _ _,
    (germAlong_eventuallyEq 𝒢₂ hΦ₂ U m s).comp_tendsto ht,
    (hΦP.2.2.2.1 _).mem_nhds (zero_mem_dom 𝒢P hΦP ((e.hom ≫ snd _ _).left ⁻¹ᵁ U)
      (by show (e.hom ≫ snd _ _).left 𝒢P.genericUnit ∈ U
          rw [map_genericUnit_of_isMonHom]; exact m))] with z h1 h2 hz
  have h2' : 𝒢₂.germAlong Φ₂ (𝒢₂.G.left.presheaf.germ U 𝒢₂.genericUnit m s) (rightBlock g₁ g₂ z) =
      𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) U s := h2
  rw [h1, h2', evalAt_comp _ _ _ _ hz, prodPts_comp_snd]

/-- Derivative of `F ∘ ℓ` for a linear `ℓ` on `ℂ^{g₁+g₂}` (chain rule). -/
theorem fderiv_comp_linear {n : ℕ} (ℓ : (Fin (g₁ + g₂) → ℂ) →ₗ[ℂ] (Fin n → ℂ))
    (F : (Fin n → ℂ) → ℂ) (hF : DifferentiableAt ℂ F 0) (w : Fin (g₁ + g₂) → ℂ) :
    fderiv ℂ (fun z => F (ℓ z)) 0 w = fderiv ℂ F 0 (ℓ w) := by
  let ℓc := LinearMap.toContinuousLinearMap ℓ
  have hfun : (fun z => F (ℓ z)) = F ∘ ℓc := by
    funext z; simp [ℓc]
  have hF' : DifferentiableAt ℂ F (ℓc 0) := by rw [map_zero]; exact hF
  rw [hfun, fderiv_comp _ hF' ℓc.differentiableAt, ContinuousLinearMap.fderiv, map_zero]
  simp [ℓc]

end ProdJac

/-- **`ProductJacobian`, proved.** -/
theorem productJacobian : ProductJacobian := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ hΦ₁ hΦ₂ hΦP f₁ f₂ f hf1 hf2
  have hl : ∀ (i : Fin g₁) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.castAdd g₂ i) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (leftBlock g₁ g₂ w) := by
    intro i w
    rw [hf1 i, (germAlong_pull_fst_eventuallyEq e hΦ₁ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (leftBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₁ hΦ₁ _) w
  have hr : ∀ (j : Fin g₂) (w : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f (Fin.natAdd g₁ j) : 𝒢P.genStalk)) 0 w =
        fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ j : 𝒢₂.genStalk)) 0 (rightBlock g₁ g₂ w) := by
    intro j w
    rw [hf2 j, (germAlong_pull_snd_eventuallyEq e hΦ₂ hΦP _).fderiv_eq]
    exact fderiv_comp_linear (rightBlock g₁ g₂) _ (germAlong_differentiableAt 𝒢₂ hΦ₂ _) w
  have hL1 : ∀ j : Fin g₁, leftBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  have hL2 : ∀ j : Fin g₂, leftBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR1 : ∀ j : Fin g₁, rightBlock g₁ g₂ (Pi.single (Fin.castAdd g₂ j) 1) = 0 := by
    intro j; funext k; simp [Pi.single_apply, Fin.ext_iff]; omega
  have hR2 : ∀ j : Fin g₂, rightBlock g₁ g₂ (Pi.single (Fin.natAdd g₁ j) 1) = Pi.single j 1 := by
    intro j; funext k; simp [Pi.single_apply]
  let J₁ : Matrix (Fin g₁) (Fin g₁) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₁.germAlong Φ₁ (f₁ i : 𝒢₁.genStalk)) 0 (Pi.single j 1)
  let J₂ : Matrix (Fin g₂) (Fin g₂) ℂ :=
    Matrix.of fun i j => fderiv ℂ (𝒢₂.germAlong Φ₂ (f₂ i : 𝒢₂.genStalk)) 0 (Pi.single j 1)
  have hblock : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm
      (Matrix.of fun i j : Fin (g₁ + g₂) =>
        fderiv ℂ (𝒢P.germAlong (prodPts e Φ₁ Φ₂) (f i : 𝒢P.genStalk)) 0 (Pi.single j 1)) =
      Matrix.fromBlocks J₁ 0 0 J₂ := by
    ext (i | i) (j | j)
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, Matrix.of_apply, Matrix.fromBlocks_apply₁₁, J₁]
      rw [hl, hL1 j]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
      rw [hl, hL2, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.of_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      rw [hr, hR1, map_zero]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
        finSumFinEquiv_apply_right, Matrix.of_apply, Matrix.fromBlocks_apply₂₂, J₂]
      rw [hr, hR2]
  unfold GroupModel.jacDet
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm, hblock, Matrix.det_fromBlocks_zero₂₁]

end ZInQ.Metrization


/-! ## metrization: `ProductUniformizationAnalytic` reduced to a statement about complex points

`ProductLocalStructure` (pure algebraic geometry, no analysis): near a complex point of
`𝒢₁ × 𝒢₂`, membership in a Zariski open `U` and a regular function on `U` are given, on
`V₁(ℂ) × V₂(ℂ)`, by sums of products of regular functions on opens `V₁ ⊂ 𝒢₁`, `V₂ ⊂ 𝒢₂`. The
analytic consequences (openness of `dom`, holomorphy) are proved. -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings Topology

/-- **Glue (local product structure of `𝒢₁ ×_{𝓞_L} 𝒢₂` at complex points).** For
`e : 𝒢P ≅ 𝒢₁ × 𝒢₂`, an open `U ⊂ 𝒢P`, `s ∈ Γ(U)` and complex points `p₁`, `p₂` with
`e⁻¹(p₁, p₂) ∈ U(ℂ)`, there are opens `V₁ ∋ p₁`, `V₂ ∋ p₂` and regular functions
`a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that `H = Σ c_k ⊗ d_k` does not vanish at `(p₁, p₂)`,
and at every `(p₁', p₂') ∈ V₁(ℂ) × V₂(ℂ)` with `H(p₁', p₂') ≠ 0`: `e⁻¹(p₁', p₂') ∈ U(ℂ)` and
`s(e⁻¹(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`. Why true (STANDARD): take affine
`V₁ = Spec R₁`, `V₂ = Spec R₂` (over the affine `Spec 𝓞_L`), so `V₁ ×_{𝓞_L} V₂ = Spec(R₁ ⊗ R₂)`
is open in the product; choose a basic open `D(h)` of it with `(p₁, p₂) ∈ D(h) ⊆ e(U)`,
`h ∈ R₁ ⊗ R₂`; on `D(h)`, `s = a/h^m` with `a ∈ R₁ ⊗ R₂`; take `H = h^m` and expand `H` and `a`
as sums of pure tensors; a pure tensor `c ⊗ d` evaluates at `(p₁', p₂')` to `c(p₁') d(p₂')`.
Unproved (needs Mathlib's affine opens of pullbacks and sections on basic opens). -/
def ProductLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (τ : L →+* ℂ) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ e.inv).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ e.inv).left ⁻¹ᵁ U ∧
        𝒢P.evalAt (lift p₁' p₂' ≫ e.inv) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

section Local

variable {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L} {𝒢₂ : GroupModel B L}
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) {τ : L →+* ℂ} {g₁ g₂ : ℕ} {Λ₁ : Submodule ℤ (Fin g₁ → ℂ)}
  {Λ₂ : Submodule ℤ (Fin g₂ → ℂ)} {Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ} {Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ}

theorem leftBlock_differentiable : Differentiable ℂ (leftBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (leftBlock g₁ g₂)).differentiable
  simpa using h

theorem rightBlock_differentiable : Differentiable ℂ (rightBlock g₁ g₂) := by
  have h := (LinearMap.toContinuousLinearMap (rightBlock g₁ g₂)).differentiable
  simpa using h

/-- The local statement: every point of `dom (prodPts) U` has an open neighbourhood inside
`dom (prodPts) U` on which `z ↦ s(prodPts z)` is holomorphic. -/
theorem prodPts_local (hLS : ProductLocalStructure) (h₁ : 𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁)
    (h₂ : 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂) (U : 𝒢P.G.left.Opens) (s : Γ(𝒢P.G.left, U))
    (z₀ : Fin (g₁ + g₂) → ℂ) (hz₀ : z₀ ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U) :
    ∃ N : Set (Fin (g₁ + g₂) → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      DifferentiableOn ℂ (fun z => 𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s) N := by
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hLS K A B C L 𝒢P 𝒢₁ 𝒢₂ e τ U s (Φ₁ (leftBlock g₁ g₂ z₀)) (Φ₂ (rightBlock g₁ g₂ z₀)) hz₀
  let O : Set (Fin (g₁ + g₂) → ℂ) :=
    leftBlock g₁ g₂ ⁻¹' 𝒢₁.dom Φ₁ V₁ ∩ rightBlock g₁ g₂ ⁻¹' 𝒢₂.dom Φ₂ V₂
  have hO : IsOpen O :=
    ((h₁.2.2.2.1 V₁).preimage (leftBlock_differentiable).continuous).inter
      ((h₂.2.2.2.1 V₂).preimage (rightBlock_differentiable).continuous)
  have hd1 : ∀ σ : Γ(𝒢₁.G.left, V₁),
      DifferentiableOn ℂ (fun z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ σ) O := fun σ =>
    (h₁.2.2.2.2 V₁ σ).comp (leftBlock_differentiable).differentiableOn (fun z hz => hz.1)
  have hd2 : ∀ σ : Γ(𝒢₂.G.left, V₂),
      DifferentiableOn ℂ (fun z => 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ σ) O := fun σ =>
    (h₂.2.2.2.2 V₂ σ).comp (rightBlock_differentiable).differentiableOn (fun z hz => hz.2)
  let H : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k)
  let Afun : (Fin (g₁ + g₂) → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) * 𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k)
  have hH : DifferentiableOn ℂ H O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (c k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (d k))
      (fun k _ => (hd1 (c k)).mul (hd2 (d k)))
    convert this using 1
    funext z
    simp [H, Finset.sum_apply]
  have hA : DifferentiableOn ℂ Afun O := by
    have := DifferentiableOn.sum (u := Finset.univ)
      (A := fun k z => 𝒢₁.evalAt (Φ₁ (leftBlock g₁ g₂ z)) V₁ (a k) *
        𝒢₂.evalAt (Φ₂ (rightBlock g₁ g₂ z)) V₂ (b k))
      (fun k _ => (hd1 (a k)).mul (hd2 (b k)))
    convert this using 1
    funext z
    simp [Afun, Finset.sum_apply]
  let N := O ∩ H ⁻¹' {0}ᶜ
  have hN : IsOpen N := hH.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton
  have hsub : ∀ z ∈ N, z ∈ 𝒢P.dom (prodPts e Φ₁ Φ₂) U ∧
      𝒢P.evalAt (prodPts e Φ₁ Φ₂ z) U s = Afun z / H z := by
    intro z hz
    obtain ⟨hmem, heq⟩ := hall _ _ hz.1.1 hz.1.2 hz.2
    refine ⟨hmem, ?_⟩
    rw [eq_div_iff hz.2]
    exact heq
  refine ⟨N, hN, ⟨⟨hV₁, hV₂⟩, hne⟩, fun z hz => (hsub z hz).1, ?_⟩
  have hdiv : DifferentiableOn ℂ (fun z => Afun z * (H z)⁻¹) N :=
    (hA.mono Set.inter_subset_left).mul
      ((hH.mono Set.inter_subset_left).inv (fun z hz => hz.2))
  refine hdiv.congr fun z hz => ?_
  rw [(hsub z hz).2, div_eq_mul_inv]

end Local

/-- **`ProductUniformizationAnalytic` from `ProductLocalStructure` (proved).** -/
theorem productUniformizationAnalytic_of (hLS : ProductLocalStructure) :
    ProductUniformizationAnalytic := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ h₁ h₂
  refine ⟨fun U => ?_, fun U s => ?_⟩
  · rw [isOpen_iff_forall_mem_open]
    intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, hsub, -⟩ := prodPts_local e hLS h₁ h₂ U 0 z₀ hz₀
    exact ⟨N, hsub, hN, hz₀N⟩
  · intro z₀ hz₀
    obtain ⟨N, hN, hz₀N, -, hd⟩ := prodPts_local e hLS h₁ h₂ U s z₀ hz₀
    exact ((hd z₀ hz₀N).differentiableAt (hN.mem_nhds hz₀N)).differentiableWithinAt

end ZInQ.Metrization


/-! ## §3c. metrization's glue Prop `JacDetNondegenerate` (verbatim, `part_exists.lean` lines
45-57) -/

namespace ZInQ.Metrization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings

/-- **Glue (local parameters are analytic coordinates).** For `g = dim A` and an analytic
uniformization `Φ` of `𝒢(ℂ)_τ` with a full lattice as kernel, some `f₁, …, f_g ∈ 𝔪_ξ` have
`jacDet Φ f ≠ 0`. Why true (STANDARD): `𝒪_{𝒢,ξ} = 𝒪_{A_L,0}` is regular of dimension `g`
(smoothness); a regular system of parameters `f₁, …, f_g` gives holomorphic coordinates of the
complex manifold `A_τ(ℂ)` at `0` (Serre, GAGA, or the holomorphic implicit function theorem),
and `Φ` is a local biholomorphism at `0`, so `(f_i ∘ Φ)` has invertible Jacobian at `0`.
Unproved (needs the analytic structure of `A_τ(ℂ)`). -/
def JacDetNondegenerate : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∀ (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      IsZLattice ℝ Λ → 𝒢.IsAnalyticUniformization τ Λ Φ →
      ∃ f : Fin g → IsLocalRing.maximalIdeal 𝒢.genStalk, 𝒢.jacDet Φ f ≠ 0

end ZInQ.Metrization

namespace ZInQ.ProductUnif

/-! ## §4. S-alg (`ProductMetrizationOfProductUnif`): reduction to three smaller glue Props

`productMetrizationOfProductUnif_of : HodgeLatticeTheorem → ProductUnifDims → JacDetDescends →
ProductHodgeAdd → ProductMetrizationOfProductUnif` (proved). `HodgeLatticeTheorem` is the kernel's
glue Prop (`ZInQKernel/HDecomp/Faltings/Models.lean`); the other three are new glue. -/

section SAlg

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings ZInQ.ProductHeight

/-- **Glue S-alg-1 (dimensions and nonsingularity in product form).** Let `e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂`
have homomorphic components, and at `τ` let the metrization `MP` (dimension `g`) be in product
form: period lattice `Λ₁ × Λ₂` and coefficient map computed by `Φ₁ × Φ₂`, for full-lattice
analytic uniformizations `Φᵢ : ℂ^{gᵢ} → 𝒢ᵢ(ℂ)_τ`, `g₁ + g₂ = g`. Then `g₁ = dim A`, `g₂ = dim B`,
and both factor Jacobians are nonsingular on some `gᵢ`-tuple of germs.

Why true (STANDARD; algebra and calculus, no AN3). Write `nᵢ` for the `L`-dimension of the
cotangent space `𝔪/𝔪²` of `𝒢ᵢ` at the generic unit. `genStalk` is the local ring of `A_L` at its
origin (regular, smooth generic fibre), so `n₁ = dim A_L = dim A` (dimension of a finite-type
scheme over a field is invariant under field extension; EGA IV 4.1.4, UNVERIFIED locator); `dim A`
is finite since `A.X.left` is nonempty. Since `cot` is an `L`-space and `L` a localization of
`𝓞_L`, `finrank_L (hodgeSpace g) = C(n, g)`. Via `e` (whose components preserve units),
`𝔪_P/𝔪_P² = 𝔪₁/𝔪₁² ⊕ 𝔪₂/𝔪₂²`, so `MP.hodge.finrank_eq_one` gives `g ∈ {0, n₁ + n₂}`.
If `g = 0`, then `g₁ = g₂ = 0`, the `Φᵢ : ℂ⁰ → 𝒢ᵢ(ℂ)_τ` are onto, so `A_τ(ℂ)`, `B_τ(ℂ)` are single
points and `dim A = dim B = 0` (a positive-dimensional variety over `ℂ` has infinitely many
points); `Fin 0` Jacobians are `1`. Otherwise: the wedges `wedge f` span `hodgeSpace` over `L`, so
`MP.hodge.coeff_ne_zero` and the coefficient formula give `f` with `jacDet (Φ₁ × Φ₂) f ≠ 0`. The map
`prodUnif ∘ cast` satisfies the analytic clauses (product-height's `ProductUnifAnalytic`,
metrization's `ProductUniformizationAnalytic`: true, from basic opens `D(h)` of affine products),
so the derivative at `0` of a germ along it depends only on its class in `cot₁ ⊕ cot₂` and the
Jacobian rows are `(D₁x, 0)`, `(0, D₂y)`; nonsingularity forces `g₁ ≤ n₁`, `g₂ ≤ n₂`, hence
equality, and nonsingular diagonal blocks. Unproved. (Reviewed: true for all instances, including
`g = 0` and an `e` incompatible with any generic-fibre product structure.) -/
def ProductUnifDims : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) →
    (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) →
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) →
    (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
      MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    A.dim = g₁ ∧ B.dim = g₂ ∧ (∃ f₁, 𝒢₁.jacDet Φ₁ f₁ ≠ 0) ∧ (∃ f₂, 𝒢₂.jacDet Φ₂ f₂ ≠ 0)

/-- **Glue S-alg-2 (the Jacobian determinant descends to the Hodge line).** For a group model `𝒢`
of `A_L` with `dim A = d` and an analytic uniformization `Φ : ℂ^d → 𝒢(ℂ)_τ`, the map
`f ↦ jacDet Φ f = det(∂(fᵢ ∘ Φ)/∂zⱼ(0))` on `d`-tuples of germs in `𝔪_ξ` is the restriction to
wedges of a `τ`-semilinear map `hodgeSpace d → ℂ`.

Why true (STANDARD; calculus). The derivative at `0` of `germAlong Φ f` does not depend on the
representative (`dom Φ U` is open and contains `0`), is additive in `f`, satisfies
`d(a f) = τ(a) df` for `a ∈ 𝓞_L` and `d(fh) = f(1) dh + h(1) df = 0` for `f, h ∈ 𝔪_ξ` (clause 5,
Leibniz). So `df ↦ d(f ∘ Φ)(0)` is a `τ`-semilinear map on `𝔪/𝔪²`; the determinant is
alternating multilinear, so it factors through `⋀^d_{𝓞_L}`, then through `L ⊗_{𝓞_L} ⋀^d`
(`l ⊗ ω ↦ τ(l) c(ω)`). Unproved. -/
def JacDetDescends : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (d : ℕ), A.dim = d → ∀ (τ : L →+* ℂ) (Λ : Submodule ℤ (Fin d → ℂ))
    (Φ : (Fin d → ℂ) → 𝒢.Pts τ), 𝒢.IsAnalyticUniformization τ Λ Φ →
    ∃ c : 𝒢.hodgeSpace d →ₛₗ[τ] ℂ, ∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f

/-- **Glue S-alg-3 (additivity of the height for a product-form metrization).** Let
`e : MP.model ≅ 𝒢₁ ⊗ 𝒢₂` have homomorphic components, `g₁ + g₂ = g`, and let `D₁`, `D₂` be Hodge
data of the factors with the genuine lattices `⋀^{gᵢ} ω_{𝒢ᵢ}`, such that at every `τ` there are
analytic uniformizations `Φᵢ` of the factors with kernels the periods of `Dᵢ`, computing the
coefficients of `Dᵢ`, while `MP` has periods `D₁.periods × D₂.periods` and coefficients computed
by `Φ₁ × Φ₂`. Then `h(D₁) + h(D₂) ≤ h(MP)`.

Why true (STANDARD; equality holds). First `gᵢ = dim`, as in `ProductUnifDims` (otherwise the
decomposition of `⋀^g` below fails). `ω_{MP} = ω₁ ⊕ ω₂` (unit of a product; this is a statement
about the conormal lattices `omega`, not only the generic cotangent spaces), so
`s = p₁*s₁ ∧ p₂*s₂ ∈ ⋀^g ω_{MP}` for any nonzero `sᵢ ∈ ⋀^{gᵢ} ω_{𝒢ᵢ}` (an invertible
`𝓞_L`-module, not necessarily free) and
`secIndex s = secIndex s₁ · secIndex s₂`; the Jacobian of `Φ₁ × Φ₂` on `p₁*f ∧ p₂*h` is block
diagonal, so the coefficients multiply; `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`
(`prodLattice_facts` of product-height, proved, plus a coordinate permutation `Fin.cast`); then
`modelHeight_add_of` (product-height, proved). Unproved as a whole. -/
def ProductHodgeAdd : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (D₁ : HodgeData L g₁ (𝒢₁.hodgeSpace g₁))
    (D₂ : HodgeData L g₂ (𝒢₂.hodgeSpace g₂)),
    D₁.lattice = 𝒢₁.detLattice g₁ → D₂.lattice = 𝒢₂.detLattice g₂ →
    (∀ τ : L →+* ℂ, ∃ (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ (D₁.periods τ) Φ₁ ∧
      𝒢₂.IsAnalyticUniformization τ (D₂.periods τ) Φ₂ ∧
      (∀ f, D₁.coeff τ (𝒢₁.wedge f) = 𝒢₁.jacDet Φ₁ f) ∧
      (∀ f, D₂.coeff τ (𝒢₂.wedge f) = 𝒢₂.jacDet Φ₂ f) ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔
        (fun i => z (Fin.cast hg i)) ∈ prodLattice (D₁.periods τ) (D₂.periods τ)) ∧
      ∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    D₁.modelHeight + D₂.modelHeight ≤ MP.hodge.modelHeight

theorem natCast_eq_of_dim {K : Type} [Field K] {A : AbVar K} {m n : ℕ} (hm : A.dim = m)
    (hn : A.dim = n) : m = n := by
  have h : ((m : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞) := hm.symm.trans hn
  exact_mod_cast WithBot.coe_injective h

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, `JacDetDescends`, `ProductHodgeAdd`
(proved).** The factor metrizations are built here: dimension `dᵢ = dim` (constant in `τ` by
`ProductUnifDims`), lattice `⋀^{dᵢ} ω_{𝒢ᵢ}` (`HodgeLatticeTheorem`), periods `Λᵢ(τ)`, coefficient
maps from `JacDetDescends`, nonzero by the nonsingular factor Jacobians. -/
theorem productMetrizationOfProductUnif_of (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hJ : JacDetDescends) (hP : ProductHodgeAdd) : ProductMetrizationOfProductUnif := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ hform
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := inferInstance
  obtain ⟨d₁, d₂, hd, Λ₁₀, Λ₂₀, Φ₁₀, Φ₂₀, hl₁₀, hl₂₀, hu₁₀, hu₂₀, hper₀, hco₀⟩ := hform τ₀
  obtain ⟨hA, hB, -, -⟩ :=
    hD K A B C L 𝒢₁ 𝒢₂ g MP e τ₀ d₁ d₂ hd Λ₁₀ Λ₂₀ Φ₁₀ Φ₂₀ hl₁₀ hl₂₀ hu₁₀ hu₂₀ hper₀ hco₀
  have norm : ∀ τ : L →+* ℂ, ∃ (Λ₁ : Submodule ℤ (Fin d₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin d₂ → ℂ))
      (Φ₁ : (Fin d₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin d₂ → ℂ) → 𝒢₂.Pts τ),
      (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) ∧
      (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) ∧
      𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ ∧ 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hd i)) ∈ prodLattice Λ₁ Λ₂) ∧
      (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hd i))) f) ∧
      (∃ f₁, 𝒢₁.jacDet Φ₁ f₁ ≠ 0) ∧ (∃ f₂, 𝒢₂.jacDet Φ₂ f₂ ≠ 0) := by
    intro τ
    obtain ⟨g₁, g₂, hg, Λ₁, Λ₂, Φ₁, Φ₂, hl₁, hl₂, hu₁, hu₂, hper, hco⟩ := hform τ
    obtain ⟨hA', hB', hn₁, hn₂⟩ :=
      hD K A B C L 𝒢₁ 𝒢₂ g MP e τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
    obtain rfl : g₁ = d₁ := natCast_eq_of_dim hA' hA
    obtain rfl : g₂ = d₂ := natCast_eq_of_dim hB' hB
    exact ⟨Λ₁, Λ₂, Φ₁, Φ₂, hl₁, hl₂, hu₁, hu₂, hper, hco, hn₁, hn₂⟩
  choose Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco hn₁ hn₂ using norm
  obtain ⟨hfr₁, hlat₁⟩ := hH K A L 𝒢₁ d₁ hA
  obtain ⟨hfr₂, hlat₂⟩ := hH K B L 𝒢₂ d₂ hB
  choose c₁ hc₁ using fun τ => hJ K A L 𝒢₁ d₁ hA τ (Λ₁ τ) (Φ₁ τ) (hu₁ τ)
  choose c₂ hc₂ using fun τ => hJ K B L 𝒢₂ d₂ hB τ (Λ₂ τ) (Φ₂ τ) (hu₂ τ)
  let D₁ : HodgeData L d₁ (𝒢₁.hodgeSpace d₁) :=
    { lattice := 𝒢₁.detLattice d₁
      finrank_eq_one := hfr₁
      isLattice := hlat₁
      periods := Λ₁
      periods_discrete := fun τ => (hl₁ τ).fst
      periods_isZLattice := fun τ => (hl₁ τ).snd
      coeff := c₁
      coeff_ne_zero := fun τ h => by
        obtain ⟨f, hf⟩ := hn₁ τ
        apply hf
        rw [← hc₁ τ f, h]
        rfl }
  let D₂ : HodgeData L d₂ (𝒢₂.hodgeSpace d₂) :=
    { lattice := 𝒢₂.detLattice d₂
      finrank_eq_one := hfr₂
      isLattice := hlat₂
      periods := Λ₂
      periods_discrete := fun τ => (hl₂ τ).fst
      periods_isZLattice := fun τ => (hl₂ τ).snd
      coeff := c₂
      coeff_ne_zero := fun τ h => by
        obtain ⟨f, hf⟩ := hn₂ τ
        apply hf
        rw [← hc₂ τ f, h]
        rfl }
  let M₁ : MetrizedModel A L d₁ :=
    { model := 𝒢₁, hodge := D₁, lattice_eq := rfl, arch := fun τ => ⟨Φ₁ τ, hu₁ τ, hc₁ τ⟩ }
  let M₂ : MetrizedModel B L d₂ :=
    { model := 𝒢₂, hodge := D₂, lattice_eq := rfl, arch := fun τ => ⟨Φ₂ τ, hu₂ τ, hc₂ τ⟩ }
  refine ⟨d₁, d₂, M₁, M₂, rfl, rfl, ?_⟩
  exact hP K A B C L 𝒢₁ 𝒢₂ g MP e d₁ d₂ hd D₁ D₂ rfl rfl
    (fun τ => ⟨Φ₁ τ, Φ₂ τ, hu₁ τ, hu₂ τ, hc₁ τ, hc₂ τ, hper τ, hco τ⟩)

/-- **Glue S-alg-3a (sections of the Hodge lattices in product form).** Under the hypotheses of
`ProductHodgeAdd`, there are nonzero `s ∈ ⋀^g ω_{MP}`, `sᵢ ∈ ⋀^{gᵢ} ω_{𝒢ᵢ}` whose lattice indices
and coefficients multiply.

Why true (STANDARD). First `gᵢ = nᵢ = dim` (as in `ProductUnifDims`). `ω_{MP} = ω₁ ⊕ ω₂` (pull
back along the projections, restrict along the unit sections of the other factor; `e` preserves
units), so `s = p₁*s₁ ∧ p₂*s₂` generates `⋀^g ω_{MP} = ⋀^{g₁}ω₁ ⊗ ⋀^{g₂}ω₂` locally where the `sᵢ`
do, and `secIndex s = secIndex s₁ · secIndex s₂` (the index of `𝓞_L s₁ ⊗ 𝓞_L s₂` in a tensor
product of invertible modules is multiplicative: norms of fractional ideals). For coefficients:
both sides are `τ`-semilinear in `s₁`, `s₂`, so it suffices to take pure wedges; on
`p₁*f ∧ p₂*h` the Jacobian of `Φ₁ × Φ₂` at `0` is block diagonal (this uses the analytic clauses of
`prodUnif ∘ cast`, which hold although the hypotheses do not state them: product-height's
`ProductUnifAnalytic`), so `coeff_P(s) = coeff₁(s₁) · coeff₂(s₂)`. Reduced below
(`productHodgeSections_of`) to metrization's `ProductUniformizationAnalytic` and
`ProductHodgeLattice`. (Reviewed: true.) -/
def ProductHodgeSections : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (D₁ : HodgeData L g₁ (𝒢₁.hodgeSpace g₁))
    (D₂ : HodgeData L g₂ (𝒢₂.hodgeSpace g₂)),
    D₁.lattice = 𝒢₁.detLattice g₁ → D₂.lattice = 𝒢₂.detLattice g₂ →
    (∀ τ : L →+* ℂ, ∃ (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
      𝒢₁.IsAnalyticUniformization τ (D₁.periods τ) Φ₁ ∧
      𝒢₂.IsAnalyticUniformization τ (D₂.periods τ) Φ₂ ∧
      (∀ f, D₁.coeff τ (𝒢₁.wedge f) = 𝒢₁.jacDet Φ₁ f) ∧
      (∀ f, D₂.coeff τ (𝒢₂.wedge f) = 𝒢₂.jacDet Φ₂ f) ∧
      (∀ z, z ∈ MP.hodge.periods τ ↔
        (fun i => z (Fin.cast hg i)) ∈ prodLattice (D₁.periods τ) (D₂.periods τ)) ∧
      ∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
        MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    ∃ (s : MP.model.hodgeSpace g) (s₁ : 𝒢₁.hodgeSpace g₁) (s₂ : 𝒢₂.hodgeSpace g₂),
      s ∈ MP.hodge.lattice ∧ s ≠ 0 ∧ s₁ ∈ D₁.lattice ∧ s₁ ≠ 0 ∧ s₂ ∈ D₂.lattice ∧ s₂ ≠ 0 ∧
      secIndex MP.hodge.lattice s = secIndex D₁.lattice s₁ * secIndex D₂.lattice s₂ ∧
      ∀ τ, MP.hodge.coeff τ s = D₁.coeff τ s₁ * D₂.coeff τ s₂

/-- The covolume of a lattice in product form, up to the coordinate cast (proved, from
product-height's `prodLattice_facts`). -/
theorem covolume_of_cast {g g₁ g₂ : ℕ} (hg : g₁ + g₂ = g) (Λ : Submodule ℤ (Fin g → ℂ))
    (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) [DiscreteTopology Λ₁]
    [IsZLattice ℝ Λ₁] [DiscreteTopology Λ₂] [IsZLattice ℝ Λ₂]
    (h : ∀ z, z ∈ Λ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) :
    ZLattice.covolume Λ = ZLattice.covolume Λ₁ * ZLattice.covolume Λ₂ := by
  subst hg
  have hΛ : Λ = prodLattice Λ₁ Λ₂ := by
    ext z
    rw [h z]
    rfl
  subst hΛ
  obtain ⟨-, -, hc⟩ := prodLattice_facts Λ₁ Λ₂
  exact hc

/-- **`ProductHodgeAdd` from `ProductHodgeSections` (proved).** The covolumes multiply
(`covolume_of_cast`) and `modelHeight_add_of` gives equality of heights. -/
theorem productHodgeAdd_of (h : ProductHodgeSections) : ProductHodgeAdd := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  obtain ⟨s, s₁, s₂, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hco⟩ :=
    h K A B C L 𝒢₁ 𝒢₂ g MP e g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  have hcov : ∀ τ, ZLattice.covolume (MP.hodge.periods τ) =
      ZLattice.covolume (D₁.periods τ) * ZLattice.covolume (D₂.periods τ) := by
    intro τ
    obtain ⟨-, -, -, -, -, -, hper, -⟩ := hform τ
    have := D₁.periods_discrete τ
    have := D₁.periods_isZLattice τ
    have := D₂.periods_discrete τ
    have := D₂.periods_isZLattice τ
    exact covolume_of_cast hg _ _ _ hper
  subst hg
  exact (modelHeight_add_of MP.hodge D₁ D₂ hs hs0 hs₁ hs₁0 hs₂ hs₂0 hidx hco hcov).ge

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, `JacDetDescends` and
`ProductHodgeSections` (proved).** -/
theorem productMetrizationOfProductUnif_of' (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hJ : JacDetDescends) (hS : ProductHodgeSections) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of hH hD hJ (productHodgeAdd_of hS)

/-- **`JacDetDescends` (S-alg-2), proved**: metrization's `jacDetDescends` (§3b, no dimension
hypothesis needed). -/
theorem jacDetDescends' : JacDetDescends :=
  fun K _ A L _ _ _ 𝒢 d _ τ Λ Φ hΦ => ZInQ.Metrization.jacDetDescends K A L 𝒢 τ d Λ Φ hΦ

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims` and `ProductHodgeSections` (proved).** -/
theorem productMetrizationOfProductUnif_of'' (hH : HodgeLatticeTheorem) (hD : ProductUnifDims)
    (hS : ProductHodgeSections) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of' hH hD jacDetDescends' hS

/-- `prodUnif` (product-height) is metrization's `prodPts` (proved). -/
theorem prodUnif_eq_prodPts {K : Type} [Field K] {A B C : AbVar K} {L : Type} [Field L]
    [NumberField L] [Algebra K L] {𝒢P : GroupModel C L} {𝒢₁ : GroupModel A L}
    {𝒢₂ : GroupModel B L} (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)]
    [IsMonHom (e.hom ≫ snd _ _)] {τ : L →+* ℂ} {g₁ g₂ : ℕ} (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ) :
    prodUnif e Φ₁ Φ₂ = ZInQ.Metrization.prodPts e Φ₁ Φ₂ := by
  funext z
  unfold prodUnif
  rw [MulEquiv.symm_apply_eq]
  apply Prod.ext
  · exact (ZInQ.Metrization.prodPts_comp_fst e Φ₁ Φ₂ z).symm
  · exact (ZInQ.Metrization.prodPts_comp_snd e Φ₁ Φ₂ z).symm

/-- product-height's `prodLattice` is metrization's (proved). -/
theorem prodLattice_eq_metrization {g₁ g₂ : ℕ} (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) :
    prodLattice Λ₁ Λ₂ = ZInQ.Metrization.prodLattice Λ₁ Λ₂ := by
  ext z
  exact Iff.rfl

/-- **`ProductHodgeSections` from metrization's `ProductUniformizationAnalytic` and
`ProductHodgeLattice` (proved).** The factor metrizations are assembled from the hypotheses;
`ProductHodgeLattice` gives the sections and the index; metrization's `productJacobian`
(proved, §3b) gives the multiplicativity of the coefficients, applied to `prodPts = prodUnif`,
which is an analytic uniformization by `prodPts_alg` and `ProductUniformizationAnalytic`. -/
theorem productHodgeSections_of (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductHodgeSections := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e he₁ he₂ g₁ g₂ hg D₁ D₂ hl₁ hl₂ hform
  subst hg
  choose Φ₁ Φ₂ hu₁ hu₂ hc₁ hc₂ hper hco using hform
  let M₁ : MetrizedModel A L g₁ :=
    { model := 𝒢₁, hodge := D₁, lattice_eq := hl₁, arch := fun τ => ⟨Φ₁ τ, hu₁ τ, hc₁ τ⟩ }
  let M₂ : MetrizedModel B L g₂ :=
    { model := 𝒢₂, hodge := D₂, lattice_eq := hl₂, arch := fun τ => ⟨Φ₂ τ, hu₂ τ, hc₂ τ⟩ }
  obtain ⟨-, f₁, f₂, f, a₁, a₂, hf1, hf2, hs₁, hs₁0, hs₂, hs₂0, hs, hs0, hidx⟩ :=
    hL K A B C L MP.model g₁ g₂ M₁ M₂ e he₁ he₂
  refine ⟨(a₁ * a₂) • MP.model.wedge f, a₁ • 𝒢₁.wedge f₁, a₂ • 𝒢₂.wedge f₂, ?_, hs0, hs₁, hs₁0,
    hs₂, hs₂0, ?_, fun τ => ?_⟩
  · rw [MP.lattice_eq]
    exact hs
  · rw [MP.lattice_eq]
    exact hidx
  · obtain ⟨hhom, hker, hsurj⟩ := ZInQ.Metrization.prodPts_alg e he₁ he₂ (hu₁ τ) (hu₂ τ)
    obtain ⟨hopen, hdiff⟩ := hPA K A B C L MP.model 𝒢₁ 𝒢₂ e he₁ he₂ τ g₁ g₂ _ _ (Φ₁ τ) (Φ₂ τ)
      (hu₁ τ) (hu₂ τ)
    have hjac := ZInQ.Metrization.productJacobian K A B C L MP.model 𝒢₁ 𝒢₂ e he₁ he₂ τ g₁ g₂ _ _
      (Φ₁ τ) (Φ₂ τ) (hu₁ τ) (hu₂ τ) ⟨hhom, hker, hsurj, hopen, hdiff⟩ f₁ f₂ f hf1 hf2
    have hfun : (fun z => prodUnif e (Φ₁ τ) (Φ₂ τ) (fun i => z (Fin.cast rfl i))) =
        ZInQ.Metrization.prodPts e (Φ₁ τ) (Φ₂ τ) := by
      rw [← prodUnif_eq_prodPts]
      rfl
    have hc := hco τ f
    rw [hfun] at hc
    rw [map_smulₛₗ, map_smulₛₗ, map_smulₛₗ, hc, hc₁, hc₂, hjac, map_mul]
    simp only [smul_eq_mul]
    ring

/-- **S-alg from `HodgeLatticeTheorem`, `ProductUnifDims`, metrization's
`ProductUniformizationAnalytic` and `ProductHodgeLattice` (proved).** -/
theorem productMetrizationOfProductUnif_of_metrization (hH : HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hPA : ZInQ.Metrization.ProductUniformizationAnalytic)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of'' hH hD (productHodgeSections_of hPA hL)

/-- **The same with `ProductLocalStructure` (metrization's glue, pure algebraic geometry) in place
of `ProductUniformizationAnalytic` (proved, via metrization's `productUniformizationAnalytic_of`).** -/
theorem productMetrizationOfProductUnif_of_local (hH : HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of_metrization hH hD
    (ZInQ.Metrization.productUniformizationAnalytic_of hLS) hL

/-- **Glue S-alg-1a (dimensions in product form).** The hypotheses of `ProductUnifDims`; the
conclusion is its dimension half: `dim A = g₁` and `dim B = g₂`. Why true: as in `ProductUnifDims`
(the nonsingularity half is not needed for it). Unproved. -/
def ProductUnifDimsEq : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L) (g : ℕ) (MP : MetrizedModel C L g)
    (e : MP.model.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (hg : g₁ + g₂ = g) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ))
    (Λ₂ : Submodule ℤ (Fin g₂ → ℂ)) (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ)
    (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    (∃ _ : DiscreteTopology Λ₁, IsZLattice ℝ Λ₁) →
    (∃ _ : DiscreteTopology Λ₂, IsZLattice ℝ Λ₂) →
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    (∀ z, z ∈ MP.hodge.periods τ ↔ (fun i => z (Fin.cast hg i)) ∈ prodLattice Λ₁ Λ₂) →
    (∀ f, MP.hodge.coeff τ (MP.model.wedge f) =
      MP.model.jacDet (fun z => prodUnif e Φ₁ Φ₂ (fun i => z (Fin.cast hg i))) f) →
    A.dim = g₁ ∧ B.dim = g₂

/-- **`ProductUnifDims` from its dimension half and metrization's `JacDetNondegenerate`
(proved).** An alternative to proving the nonsingularity half from the product structure: it
trades that algebra for metrization's complex-geometry glue (local parameters are analytic
coordinates). -/
theorem productUnifDims_of (hE : ProductUnifDimsEq) (hN : ZInQ.Metrization.JacDetNondegenerate) :
    ProductUnifDims := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
  obtain ⟨hA, hB⟩ := hE K A B C L 𝒢₁ 𝒢₂ g MP e τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ hper hco
  obtain ⟨hd₁, hz₁⟩ := hl₁
  obtain ⟨hd₂, hz₂⟩ := hl₂
  exact ⟨hA, hB, hN K A L 𝒢₁ τ g₁ hA Λ₁ Φ₁ hz₁ hu₁, hN K B L 𝒢₂ τ g₂ hB Λ₂ Φ₂ hz₂ hu₂⟩

end SAlg

end ZInQ.ProductUnif


namespace ZInQ.ProductUnif

/-- **P2 from the S-alg reduction (proved).** `ProductModelHeight` (the type of
`GluePieces.productModelHeight`) from `HodgeLatticeTheorem` and the three new glue Props;
`ProductUnifSplits` is now a theorem. -/
theorem productModelHeight_of_salg (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hJ : JacDetDescends) (hP : ProductHodgeAdd) :
    ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits
    (productMetrizationOfProductUnif_of hH hD hJ hP)

/-- **P2 from the finest reduction (proved).** -/
theorem productModelHeight_of_salg' (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hJ : JacDetDescends) (hS : ProductHodgeSections) :
    ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_salg hH hD hJ (productHodgeAdd_of hS)

/-- **P2 from `HodgeLatticeTheorem`, `ProductUnifDims` and `ProductHodgeSections` (proved).** -/
theorem productModelHeight_of_salg'' (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hS : ProductHodgeSections) : ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_salg' hH hD jacDetDescends' hS

/-- **P2 from `HodgeLatticeTheorem`, `ProductUnifDims` and metrization's `ProductLocalStructure`
and `ProductHodgeLattice` (proved).** -/
theorem productModelHeight_of_local (hH : DefFaltings.HodgeLatticeTheorem)
    (hD : ProductUnifDims) (hLS : ZInQ.Metrization.ProductLocalStructure)
    (hL : ZInQ.Metrization.ProductHodgeLattice) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductHeight.productModelHeight_of_splits productUnifSplits
    (productMetrizationOfProductUnif_of_local hH hD hLS hL)

/-- **product-height's glue `ProductUnifAnalytic` from metrization's `ProductLocalStructure`
(proved)**, via `prodUnif = prodPts` and metrization's `productUniformizationAnalytic_of`. -/
theorem productUnifAnalytic_of_local (hLS : ZInQ.Metrization.ProductLocalStructure) :
    ZInQ.ProductHeight.ProductUnifAnalytic := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e h1 h2 τ g₁ g₂ Λ₁ Λ₂ Φ₁ Φ₂ hu₁ hu₂
  rw [prodUnif_eq_prodPts]
  exact ZInQ.Metrization.productUniformizationAnalytic_of hLS K A B C L 𝒢P 𝒢₁ 𝒢₂ e h1 h2 τ g₁ g₂
    Λ₁ Λ₂ Φ₁ Φ₂ hu₁ hu₂

end ZInQ.ProductUnif



namespace ZInQ.Metrization
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
/-- **Leaf (AN3 with its dimension: the uniformization theorem).** For every smooth group model
`𝒢` of `A_L`, every `τ : L → ℂ` and `g = dim A`, there are a full lattice `Λ ⊂ ℂ^g` and an analytic
uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ`. This is def-faltings'
`AnalyticUniformizationExists` with the dimension pinned to `dim A` (`𝒢(ℂ)_τ = A_τ(ℂ)` is a compact
connected complex Lie group of dimension `dim A`, hence `≅ ℂ^g/Λ`: Mumford, *Abelian varieties*,
§1 and §4 (UNVERIFIED locators), with Serre's GAGA for the analytic structure of `A_τ(ℂ)`).
Implies `AnalyticUniformizationExists` (`analyticUniformizationExists_of`). -/
def AnalyticUniformizationOfDim : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) (g : ℕ), A.dim = g →
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Φ : (Fin g → ℂ) → 𝒢.Pts τ),
      ∃ _ : DiscreteTopology Λ, IsZLattice ℝ Λ ∧ 𝒢.IsAnalyticUniformization τ Λ Φ

end ZInQ.Metrization

/-! ## metrization2: `JacDetNondegenerate` from the local structure of morphisms out of a product

Step 1 (linear algebra): if every `jacDet Φ f` vanishes, some `v ≠ 0` is killed by
`d(germAlong Φ t)(0)` for every `t ∈ 𝔪_ξ`. Step 2: then by every regular function near `ξ`
(subtract the pull-back along `𝒢 → Spec 𝓞_L` of its restriction to the unit section). -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

/-- Step 1 (pure linear algebra). If every `g × g` matrix whose rows are taken from a family
`F` of vectors of `ℂ^g` has determinant `0`, a nonzero vector is orthogonal (for the bilinear
pairing `Σ_j x_j y_j`) to every member of the family. -/
theorem exists_null_of_det_eq_zero {J : Type*} {g : ℕ} (F : J → (Fin g → ℂ))
    (h : ∀ f : Fin g → J, (Matrix.of fun i j => F (f i) j).det = 0) :
    ∃ v : Fin g → ℂ, v ≠ 0 ∧ ∀ i, ∑ j, F i j * v j = 0 := by
  by_cases hW : Submodule.span ℂ (Set.range F) = ⊤
  · exfalso
    obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ F
    rw [hW] at hspan
    have : Finite κ := hli.finite
    haveI := Fintype.ofFinite κ
    have hcard : Fintype.card κ = g := by
      rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hspan, finrank_top,
        Module.finrank_fin_fun]
    let eqv : Fin g ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent ℂ ((F ∘ a) ∘ eqv) := hli.comp eqv eqv.injective
    have hU : IsUnit (Matrix.of fun i j => F (a (eqv i)) j) :=
      Matrix.linearIndependent_row_iff_isUnit.mp hli'
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hU).ne_zero (h (a ∘ eqv))
  · obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hW)
    refine ⟨fun j => φ (fun k => if j = k then 1 else 0), ?_, ?_⟩
    · intro hv
      apply hφ0
      refine LinearMap.ext fun x => ?_
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp only [LinearMap.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrFun hv j
      simp only [Pi.zero_apply] at this
      rw [this, smul_zero]
    · intro i
      have h1 := hle (Submodule.subset_span ⟨i, rfl⟩)
      rw [LinearMap.mem_ker, LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [smul_eq_mul] using h1

section Eval

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- The value at the complex point `Spec ℂ → Spec 𝓞_L` (via `τ`) of a function on an open of
`Spec 𝓞_L` (`0` off the open). -/
noncomputable def baseVal (τ : L →+* ℂ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) : ℂ := by
  classical
  exact if h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O then
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x)
  else 0

/-- A function pulled back from `Spec 𝓞_L` takes the same value at every complex point. -/
theorem evalAt_pullback_base {τ : L →+* ℂ} (p : 𝒢.Pts τ) (O : (Spec (CommRingCat.of (𝓞 L))).Opens)
    (x : Γ(Spec (CommRingCat.of (𝓞 L)), O)) :
    𝒢.evalAt p (𝒢.G.hom ⁻¹ᵁ O) (𝒢.G.hom.app O x) = baseVal τ O x := by
  have hw : p.left ≫ 𝒢.G.hom = (GroupModel.ptC τ).hom := Over.w p
  have hpre : p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O := by
    rw [← hw]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ O
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (f : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of (𝓞 L)))
        (hf : f = (GroupModel.ptC (L := L) τ).hom) (e : ⊤ ≤ f ⁻¹ᵁ O),
        f.appLE O ⊤ e x = (GroupModel.ptC (L := L) τ).hom.appLE O ⊤ h x := by
      rintro f rfl e; rfl
    have h'' : ⊤ ≤ (p.left ≫ 𝒢.G.hom) ⁻¹ᵁ O := h'
    refine Eq.trans ?_ (key _ hw h'')
    have hc := Scheme.Hom.comp_appLE p.left 𝒢.G.hom O ⊤ h''
    exact congrArg (fun φ => (ConcreteCategory.hom φ) x) hc.symm
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ (𝒢.G.hom ⁻¹ᵁ O) := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- A complex point factoring as `Spec ℂ → Spec 𝓞_L → 𝒢` evaluates through the section. -/
theorem evalAt_of_left_eq {τ : L →+* ℂ} (p : 𝒢.Pts τ)
    (f : Spec (CommRingCat.of (𝓞 L)) ⟶ 𝒢.G.left) (hp : p.left = (GroupModel.ptC τ).hom ≫ f)
    (V : 𝒢.G.left.Opens) (b : Γ(𝒢.G.left, V)) :
    𝒢.evalAt p V b = baseVal τ (f ⁻¹ᵁ V) (f.app V b) := by
  have hpre : p.left ⁻¹ᵁ V = (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V) := by
    rw [hp]; rfl
  unfold GroupModel.evalAt baseVal
  by_cases h : ⊤ ≤ (GroupModel.ptC (L := L) τ).hom ⁻¹ᵁ (f ⁻¹ᵁ V)
  · have h' : ⊤ ≤ p.left ⁻¹ᵁ V := hpre ▸ h
    rw [dif_pos h', dif_pos h]
    congr 1
    have key : ∀ (q : Spec (CommRingCat.of ℂ) ⟶ 𝒢.G.left)
        (hq : q = (GroupModel.ptC (L := L) τ).hom ≫ f) (e : ⊤ ≤ q ⁻¹ᵁ V),
        q.appLE V ⊤ e b = ((GroupModel.ptC (L := L) τ).hom ≫ f).appLE V ⊤ h b := by
      rintro q rfl e; rfl
    refine (key _ hp h').trans ?_
    have hc := Scheme.Hom.comp_appLE (GroupModel.ptC (L := L) τ).hom f V ⊤ h
    exact congrArg (fun φ => (ConcreteCategory.hom φ) b) hc
  · have h' : ¬ ⊤ ≤ p.left ⁻¹ᵁ V := fun h' => h (hpre ▸ h')
    rw [dif_neg h', dif_neg h]

/-- `(1 : 𝒢(ℂ)_τ)` is `Spec ℂ → Spec 𝓞_L → 𝒢` through the unit section. -/
theorem one_left_eq (τ : L →+* ℂ) :
    (1 : 𝒢.Pts τ).left = (GroupModel.ptC τ).hom ≫ 𝒢.unitSection := by
  have hw : (toUnit (GroupModel.ptC (L := L) τ)).left = (GroupModel.ptC (L := L) τ).hom :=
    (Category.comp_id _).symm.trans (Over.w (toUnit (GroupModel.ptC (L := L) τ)))
  show (toUnit (GroupModel.ptC τ) ≫ η[𝒢.G]).left = _
  rw [Over.comp_left, hw]
  rfl

/-- The unit section is a section of the structure map. -/
theorem unitSection_comp_hom : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  show (η[𝒢.G] : 𝟙_ (Over (Spec (CommRingCat.of (𝓞 L)))) ⟶ 𝒢.G).left ≫ 𝒢.G.hom = 𝟙 _
  rw [Over.w]
  rfl

theorem one_mem_dom (τ : L →+* ℂ) (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W) :
    ⊤ ≤ (1 : 𝒢.Pts τ).left ⁻¹ᵁ W := by
  intro x _
  show (1 : 𝒢.Pts τ).left x ∈ W
  erw [one_left_apply]
  exact m

theorem evalAt_sub {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (s s' : Γ(𝒢.G.left, U)) :
    𝒢.evalAt p U (s - s') = 𝒢.evalAt p U s - 𝒢.evalAt p U s' := by
  unfold GroupModel.evalAt
  split_ifs with h
  · rw [map_sub]
    exact map_sub (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem evalAt_one_sec {τ : L →+* ℂ} (p : 𝒢.Pts τ) (U : 𝒢.G.left.Opens) (h : ⊤ ≤ p.left ⁻¹ᵁ U) :
    𝒢.evalAt p U 1 = 1 := by
  unfold GroupModel.evalAt
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

/-- A section vanishing at the identity complex point has its germ at `ξ` in `𝔪_ξ`. -/
theorem germ_mem_of_evalAt_one {τ : L →+* ℂ} (W : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ W)
    (s : Γ(𝒢.G.left, W)) (h : 𝒢.evalAt (1 : 𝒢.Pts τ) W s = 0) :
    𝒢.G.left.presheaf.germ W 𝒢.genericUnit m s ∈ IsLocalRing.maximalIdeal 𝒢.genStalk := by
  by_contra hn
  obtain ⟨u, hu⟩ := (IsLocalRing.notMem_maximalIdeal.mp hn).exists_right_inv
  obtain ⟨U', m', s', rfl⟩ := 𝒢.exists_rep u
  have mm : 𝒢.genericUnit ∈ W ⊓ U' := TopologicalSpace.Opens.mem_inf.mpr ⟨m, m'⟩
  have hg : 𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm
      (𝒢.G.left.presheaf.map (homOfLE inf_le_left).op s *
        𝒢.G.left.presheaf.map (homOfLE inf_le_right).op s') =
      𝒢.G.left.presheaf.germ (W ⊓ U') 𝒢.genericUnit mm 1 := by
    rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hu, map_one]
  obtain ⟨W'', m'', i₁, i₂, hW⟩ := TopCat.Presheaf.germ_eq _ 𝒢.genericUnit mm mm _ _ hg
  have hd := one_mem_dom 𝒢 τ W'' m''
  have e1 := congrArg (𝒢.evalAt (1 : 𝒢.Pts τ) W'') hW
  rw [map_mul, map_one, evalAt_mul, evalAt_one_sec 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
    evalAt_res 𝒢 _ _ hd] at e1
  rw [evalAt_res 𝒢 (1 : 𝒢.Pts τ) (homOfLE inf_le_left)
    ((one_mem_dom 𝒢 τ _ mm)) s, h, zero_mul] at e1
  exact zero_ne_one e1

end Eval

end ZInQ.Metrization2
/-! ## metrization2: the glue Prop, step 2 (all regular functions) and step 3 (translation) -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

/-- **Glue (local structure of a morphism out of a fibre product, at complex points).** For group
models `𝒢₁`, `𝒢₂`, `ℋ` over `𝓞_L`, a morphism `m : 𝒢₁ ×_{𝓞_L} 𝒢₂ → ℋ` of `𝓞_L`-schemes, an open
`U ⊆ ℋ`, `s ∈ Γ(U, 𝒪_ℋ)` and complex points `p₁`, `p₂` with `m(p₁, p₂) ∈ U(ℂ)`: there are opens
`Vᵢ ∋ pᵢ` and regular functions `a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` such that
`H = Σ c_k(·) d_k(·)` is nonzero at `(p₁, p₂)` and, wherever `H(p₁', p₂') ≠ 0` on
`V₁(ℂ) × V₂(ℂ)`, `m(p₁', p₂') ∈ U(ℂ)` and `s(m(p₁', p₂')) · H(p₁', p₂') = Σ a_k(p₁') b_k(p₂')`.
Why true (STANDARD; pure scheme theory, no analysis): take affine opens `Vᵢ = Spec Rᵢ ∋ pᵢ`;
`V₁ ×_{𝓞_L} V₂ = Spec (R₁ ⊗_{𝓞_L} R₂)` is an open of the product (Mathlib: `pullbackSpecIso`);
choose a basic open `D(h) ∋ (p₁, p₂)` inside `m⁻¹(U) ∩ (V₁ × V₂)`; on it `m^*s = a / h^N`; write
`h^N = Σ c_k ⊗ d_k`, `a = Σ a_k ⊗ b_k`; a complex point `(p₁', p₂')` of `V₁ × V₂` is the ring map
`r₁ ⊗ r₂ ↦ r₁(p₁') r₂(p₂')`, and it lies in `D(h)` iff `h^N(p₁', p₂') ≠ 0`.
Special cases: `m = e.inv` for `e : 𝒢P ≅ 𝒢₁ × 𝒢₂` is metrization's `ProductLocalStructure`
(`productLocalStructure_of`); `m = μ` (the group law) gives `JacDetNondegenerate`
(`jacDetNondegenerate_of`). -/
def ProductMapLocalStructure : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (ℋ : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (m : 𝒢₁.G ⊗ 𝒢₂.G ⟶ ℋ.G) (τ : L →+* ℂ) (U : ℋ.G.left.Opens) (s : Γ(ℋ.G.left, U))
    (p₁ : 𝒢₁.Pts τ) (p₂ : 𝒢₂.Pts τ), ⊤ ≤ (lift p₁ p₂ ≫ m).left ⁻¹ᵁ U →
    ∃ (V₁ : 𝒢₁.G.left.Opens) (V₂ : 𝒢₂.G.left.Opens) (n : ℕ)
      (a c : Fin n → Γ(𝒢₁.G.left, V₁)) (b d : Fin n → Γ(𝒢₂.G.left, V₂)),
      ⊤ ≤ p₁.left ⁻¹ᵁ V₁ ∧ ⊤ ≤ p₂.left ⁻¹ᵁ V₂ ∧
      (∑ k, 𝒢₁.evalAt p₁ V₁ (c k) * 𝒢₂.evalAt p₂ V₂ (d k)) ≠ 0 ∧
      ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), ⊤ ≤ p₁'.left ⁻¹ᵁ V₁ → ⊤ ≤ p₂'.left ⁻¹ᵁ V₂ →
        (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) ≠ 0 →
        ⊤ ≤ (lift p₁' p₂' ≫ m).left ⁻¹ᵁ U ∧
        ℋ.evalAt (lift p₁' p₂' ≫ m) U s *
            (∑ k, 𝒢₁.evalAt p₁' V₁ (c k) * 𝒢₂.evalAt p₂' V₂ (d k)) =
          ∑ k, 𝒢₁.evalAt p₁' V₁ (a k) * 𝒢₂.evalAt p₂' V₂ (b k)

/-- `ProductMapLocalStructure` contains metrization's `ProductLocalStructure` (`m = e.inv`). -/
theorem productLocalStructure_of (h : ProductMapLocalStructure) :
    ZInQ.Metrization.ProductLocalStructure := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e τ U s p₁ p₂ hp
  exact h K A B C L 𝒢P 𝒢₁ 𝒢₂ e.inv τ U s p₁ p₂ hp

section Steps

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

theorem hom_genericUnit : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  show 𝒢.G.hom (𝒢.unitSection (genericPt L)) = genericPt L
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

/-- Step 2. If `d(germAlong Φ t)(0)` kills `v` for every `t ∈ 𝔪_ξ`, then the differential at `0`
of `z ↦ b(Φ z)` kills `v` for every regular function `b` near `ξ`. -/
theorem fderiv_evalAt_apply_eq_zero {τ : L →+* ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {Φ : (Fin g → ℂ) → 𝒢.Pts τ} (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0)
    (V : 𝒢.G.left.Opens) (m : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)) :
    fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0 := by
  set O := 𝒢.unitSection ⁻¹ᵁ V with hO
  set c : Γ(𝒢.G.left, 𝒢.G.hom ⁻¹ᵁ O) := 𝒢.G.hom.app O (𝒢.unitSection.app V b) with hc
  have mO : 𝒢.genericUnit ∈ 𝒢.G.hom ⁻¹ᵁ O := by
    show 𝒢.unitSection (𝒢.G.hom 𝒢.genericUnit) ∈ V
    rw [hom_genericUnit]
    exact m
  set W := V ⊓ 𝒢.G.hom ⁻¹ᵁ O with hW
  have mW : 𝒢.genericUnit ∈ W := TopologicalSpace.Opens.mem_inf.mpr ⟨m, mO⟩
  set b' : Γ(𝒢.G.left, W) := 𝒢.G.left.presheaf.map (homOfLE inf_le_left).op b -
    𝒢.G.left.presheaf.map (homOfLE inf_le_right).op c with hb'
  have h1 : 𝒢.evalAt (1 : 𝒢.Pts τ) W b' = 0 := by
    have hd := one_mem_dom 𝒢 τ W mW
    rw [hb', evalAt_sub, evalAt_res 𝒢 _ _ hd, evalAt_res 𝒢 _ _ hd,
      evalAt_of_left_eq 𝒢 1 𝒢.unitSection (one_left_eq 𝒢 τ) V b, hc, evalAt_pullback_base,
      sub_self]
  have hgerm := germ_mem_of_evalAt_one 𝒢 W mW b' h1
  have hv' := hv ⟨_, hgerm⟩
  have heq : 𝒢.germAlong Φ (𝒢.G.left.presheaf.germ W 𝒢.genericUnit mW b') =ᶠ[𝓝 0]
      fun z => 𝒢.evalAt (Φ z) V b - baseVal τ O (𝒢.unitSection.app V b) := by
    filter_upwards [germAlong_eventuallyEq 𝒢 hΦ W mW b',
      (hΦ.2.2.2.1 W).mem_nhds (zero_mem_dom 𝒢 hΦ W mW)] with z hz1 hz
    rw [hz1, hb', evalAt_sub, evalAt_res 𝒢 _ _ hz, evalAt_res 𝒢 _ _ hz, hc,
      evalAt_pullback_base]
  simp only at hv'
  rw [heq.fderiv_eq, fderiv_sub_const] at hv'
  exact hv'

/-- Step 3 (translation). If every regular function near `ξ` has `d(b ∘ Φ)(0) v = 0`, then for
every regular function `s` on `U` and every `w ∈ Φ⁻¹(U(ℂ))`, `t ↦ s(Φ(w + t v))` has derivative
`0` at `t = 0`: near `0`, `s(Φ w · Φ z) = N(z)/D(z)` with `N`, `D` combinations of regular
functions near `ξ` along `Φ` (`ProductMapLocalStructure` for the group law `μ`). -/
theorem hasDerivAt_line_zero (hML : ProductMapLocalStructure) {τ : L →+* ℂ} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} {Φ : (Fin g → ℂ) → 𝒢.Pts τ}
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) (v : Fin g → ℂ)
    (hv2 : ∀ (V : 𝒢.G.left.Opens) (_ : 𝒢.genericUnit ∈ V) (b : Γ(𝒢.G.left, V)),
      fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V b) 0 v = 0)
    (U : 𝒢.G.left.Opens) (s : Γ(𝒢.G.left, U)) (w : Fin g → ℂ) (hw : w ∈ 𝒢.dom Φ U) :
    HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (w + t • v)) U s) 0 0 := by
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmul : ∀ z, lift (Φ w) (Φ z) ≫ μ[𝒢.G] = Φ (w + z) := fun z => (hΦ.1 w z).symm
  have hU' : ⊤ ≤ (lift (Φ w) (Φ 0) ≫ μ[𝒢.G]).left ⁻¹ᵁ U := by
    rw [hmul, add_zero]; exact hw
  obtain ⟨V₁, V₂, n, a, c, b, d, hV₁, hV₂, hne, hall⟩ :=
    hML K A A A L 𝒢 𝒢 𝒢 μ[𝒢.G] τ U s (Φ w) (Φ 0) hU'
  have mV₂ : 𝒢.genericUnit ∈ V₂ := by
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
    have hx := hV₂ (show x ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
    change (Φ 0).left x ∈ V₂ at hx
    rw [h0] at hx
    erw [one_left_apply] at hx
    exact hx
  set Nf : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (a k) * 𝒢.evalAt (Φ z) V₂ (b k) with hNf
  set Df : (Fin g → ℂ) → ℂ := fun z =>
    ∑ k, 𝒢.evalAt (Φ w) V₁ (c k) * 𝒢.evalAt (Φ z) V₂ (d k) with hDf
  have hdom2 : IsOpen (𝒢.dom Φ V₂) := hΦ.2.2.2.1 V₂
  have h0dom : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ V₂ := hV₂
  have hDcont : ContinuousOn Df (𝒢.dom Φ V₂) := by
    have : DifferentiableOn ℂ Df (𝒢.dom Φ V₂) := by
      simp only [hDf]
      exact DifferentiableOn.fun_sum fun k _ =>
        (hΦ.2.2.2.2 V₂ (d k)).const_mul _
    exact this.continuousOn
  set O := 𝒢.dom Φ V₂ ∩ Df ⁻¹' {0}ᶜ with hO
  have hOopen : IsOpen O := hDcont.isOpen_inter_preimage hdom2 isOpen_compl_singleton
  have hD0 : Df 0 ≠ 0 := hne
  have h0O : (0 : Fin g → ℂ) ∈ O := ⟨h0dom, hD0⟩
  -- derivative along the line of each regular function near `ξ`
  have hline : ∀ (bb : Γ(𝒢.G.left, V₂)),
      HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) V₂ bb) 0 0 := by
    intro bb
    have hd : DifferentiableAt ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0 :=
      (hΦ.2.2.2.2 V₂ bb).differentiableAt (hdom2.mem_nhds h0dom)
    have hF : HasFDerivAt (fun z => 𝒢.evalAt (Φ z) V₂ bb)
        (fderiv ℂ (fun z => 𝒢.evalAt (Φ z) V₂ bb) 0) ((0 : ℂ) • v) := by
      rw [zero_smul]; exact hd.hasFDerivAt
    have := hF.comp_hasDerivAt (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).smul_const v)
    simp only [one_smul, hv2 V₂ mV₂ bb] at this
    exact this
  have hN : HasDerivAt (fun t : ℂ => Nf (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (b k)).const_mul (𝒢.evalAt (Φ w) V₁ (a k))
    simpa [hNf] using this
  have hD : HasDerivAt (fun t : ℂ => Df (t • v)) 0 0 := by
    have := HasDerivAt.fun_sum (u := Finset.univ) fun k _ =>
      (hline (d k)).const_mul (𝒢.evalAt (Φ w) V₁ (c k))
    simpa [hDf] using this
  have hD0' : Df ((0 : ℂ) • v) ≠ 0 := by rw [zero_smul]; exact hD0
  have hq := hN.div hD hD0'
  simp only [zero_mul, mul_zero, sub_zero, zero_div] at hq
  refine hq.congr_of_eventuallyEq ?_
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ O :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hOopen.mem_nhds h0O)
  filter_upwards [hev] with t ht
  obtain ⟨-, heq⟩ := hall (Φ w) (Φ (t • v)) hV₁ ht.1 ht.2
  rw [hmul] at heq
  exact eq_div_of_mul_eq ht.2 heq

end Steps

end ZInQ.Metrization2
/-! ## metrization2: points are determined by their values on an affine open; the assembly -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.Metrization Topology

section Final

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- Two complex points in `U(ℂ)`, `U` affine, with the same values on `Γ(U, 𝒪)` are equal. -/
theorem pts_eq_of_evalAt {τ : L →+* ℂ} (U : 𝒢.G.left.Opens) (hU : IsAffineOpen U)
    (p q : 𝒢.Pts τ) (hp : ⊤ ≤ p.left ⁻¹ᵁ U) (hq : ⊤ ≤ q.left ⁻¹ᵁ U)
    (h : ∀ s : Γ(𝒢.G.left, U), 𝒢.evalAt p U s = 𝒢.evalAt q U s) : p = q := by
  have hTop : IsAffineOpen (⊤ : (Spec (CommRingCat.of ℂ)).Opens) :=
    isAffineOpen_top (Spec (CommRingCat.of ℂ))
  have happ : p.left.appLE U ⊤ hp = q.left.appLE U ⊤ hq := by
    ext s
    have hs := h s
    unfold GroupModel.evalAt at hs
    rw [dif_pos hp, dif_pos hq] at hs
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.injective hs
  have e1 := IsAffineOpen.SpecMap_appLE_fromSpec p.left hU hTop hp
  have e2 := IsAffineOpen.SpecMap_appLE_fromSpec q.left hU hTop hq
  have e3 : hTop.fromSpec ≫ p.left = hTop.fromSpec ≫ q.left :=
    e1.symm.trans ((congrArg (fun φ => Spec.map φ ≫ hU.fromSpec) happ).trans e2)
  have hiso : IsIso hTop.fromSpec := by
    rw [IsAffineOpen.fromSpec_top]; infer_instance
  apply Over.OverMorphism.ext
  exact (cancel_epi hTop.fromSpec).mp e3

end Final

/-- **`JacDetNondegenerate` from `ProductMapLocalStructure` (proved).** If every `jacDet Φ f`
vanished, some `v ≠ 0` would be killed by the differential at `0` of every regular function near
`ξ` along `Φ` (steps 1 and 2), hence, by translation, by the differential at every point
(step 3); so on an affine `U ∋ ξ` every regular function is constant along `t ↦ Φ(t v)` for small
`t`, so `Φ(t v) = Φ 0 = 1` (points of an affine scheme are determined by their values), so
`t v ∈ Λ` for all small `t`, contradicting the discreteness of `Λ`. Neither `A.dim = g` nor
`IsZLattice ℝ Λ` is used. -/
theorem jacDetNondegenerate_of (hML : ProductMapLocalStructure) :
    ZInQ.Metrization.JacDetNondegenerate := by
  intro K _ A L _ _ _ 𝒢 τ g _ Λ hdisc Φ _ hΦ
  by_contra hcon
  push_neg at hcon
  -- step 1
  obtain ⟨v, hv0, hv⟩ := exists_null_of_det_eq_zero
    (fun t : IsLocalRing.maximalIdeal 𝒢.genStalk => fun j =>
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 (Pi.single j 1)) (fun f => hcon f)
  have hsingle : ∀ j : Fin g, (fun k => if j = k then (1 : ℂ) else 0) = Pi.single j 1 := by
    intro j; ext k; simp [Pi.single_apply, eq_comm]
  have hv1 : ∀ t : IsLocalRing.maximalIdeal 𝒢.genStalk,
      fderiv ℂ (𝒢.germAlong Φ (t : 𝒢.genStalk)) 0 v = 0 := by
    intro t
    rw [pi_eq_sum_univ v, map_sum]
    simp only [hsingle, map_smul, smul_eq_mul]
    rw [← hv t]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  -- step 2
  have hv2 := fderiv_evalAt_apply_eq_zero 𝒢 hΦ v hv1
  -- an affine open around `ξ`
  obtain ⟨U, hU, mU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show 𝒢.genericUnit ∈ (⊤ : 𝒢.G.left.Opens) from trivial)
  have hdomU : IsOpen (𝒢.dom Φ U) := hΦ.2.2.2.1 U
  have h0U : (0 : Fin g → ℂ) ∈ 𝒢.dom Φ U := zero_mem_dom 𝒢 hΦ U mU
  have hcont : Continuous fun t : ℂ => t • v := continuous_id.smul continuous_const
  have hBopen : IsOpen {t : ℂ | t • v ∈ 𝒢.dom Φ U} := hdomU.preimage hcont
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hBopen 0 (by simp [h0U])
  -- steps 3-4: every regular function on `U` is constant along the line on the ball
  have hconst : ∀ t ∈ Metric.ball (0 : ℂ) r, Φ (t • v) = Φ 0 := by
    intro t ht
    have hderiv : ∀ (s : Γ(𝒢.G.left, U)), ∀ t₀ ∈ Metric.ball (0 : ℂ) r,
        HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t • v)) U s) 0 t₀ := by
      intro s t₀ ht₀
      have h3 := hasDerivAt_line_zero 𝒢 hML hΦ v hv2 U s (t₀ • v) (hball ht₀)
      have h4 : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + (t - t₀) • v)) U s) 0 t₀ := by
        have h3' : HasDerivAt (fun t : ℂ => 𝒢.evalAt (Φ (t₀ • v + t • v)) U s) 0 (t₀ - t₀) := by
          rw [sub_self]; exact h3
        exact h3'.comp_sub_const t₀ t₀
      refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [← add_smul, add_sub_cancel]
    apply pts_eq_of_evalAt 𝒢 U hU _ _ (hball ht) h0U
    intro s
    have := (Metric.isOpen_ball).is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) r).isPreconnected
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).differentiableAt.differentiableWithinAt)
      (fun t₀ ht₀ => (hderiv s t₀ ht₀).deriv) ht (Metric.mem_ball_self hr)
    simpa using this
  -- step 5: discreteness of `Λ`
  have h0 : Φ 0 = 1 := by
    have h := hΦ.1 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := Φ 0) (by rw [_root_.mul_one]; exact h.symm)
  have hmem : ∀ t ∈ Metric.ball (0 : ℂ) r, t • v ∈ Λ := fun t ht =>
    (hΦ.2.1 _).mp ((hconst t ht).trans h0)
  obtain ⟨u, hu, hpre⟩ := isOpen_induced_iff.mp (isOpen_discrete ({0} : Set Λ))
  have hu0 : (0 : Fin g → ℂ) ∈ u := by
    have : (0 : Λ) ∈ ({0} : Set Λ) := rfl
    rw [← hpre] at this
    exact this
  have hev1 : ∀ᶠ t in 𝓝 (0 : ℂ), t • v ∈ u :=
    hcont.continuousAt.preimage_mem_nhds (by rw [zero_smul]; exact hu.mem_nhds hu0)
  have hev2 : ∀ᶠ t in 𝓝 (0 : ℂ), t ∈ Metric.ball (0 : ℂ) r := Metric.ball_mem_nhds 0 hr
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t • v ∈ u ∧ t ∈ Metric.ball (0 : ℂ) r :=
    nhdsWithin_le_nhds (hev1.and hev2)
  obtain ⟨t, ⟨htu, htb⟩, ht0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hin : (⟨t • v, hmem t htb⟩ : Λ) ∈ Subtype.val ⁻¹' u := htu
  rw [hpre] at hin
  have : t • v = 0 := congrArg Subtype.val hin
  rcases smul_eq_zero.mp this with h | h
  · exact ht0 h
  · exact hv0 h


end ZInQ.Metrization2

/-! ## metrization2: complex points of a group model are complex points of `A_L`

For a group model `𝒢` of `A_L` and `τ : L → ℂ`, `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`,
`q ↦ (Spec ℂ → A_L ≅ 𝒢_L → 𝒢)`, is a group isomorphism (inverse `χ`, built from the monoidal
functor `Over.pullback (Spec L → Spec 𝓞_L)`), and evaluation of `s ∈ Γ(U, 𝒪_𝒢)` at `θ q` is
evaluation of the pulled-back section at `q`. So a uniformization of `A_L(ℂ)_τ` in leaf-push2's
sense gives one of `𝒢(ℂ)_τ` in def-faltings' sense. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings
open ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization UniformizationExists)
open scoped Obj

/-- (leaf-fold2) the two abelian-variety structures of Leaves.lean, field by field (`LeafAdopt.abVarEquiv`). -/
local instance lf2AbVarCoe {K : Type} [Field K] : Coe (AbVar K) (PkgI3.AbVar K) := ⟨fun A => ⟨A.X⟩⟩
open scoped Obj

section Transport

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
variable (𝒢 : GroupModel A L)

/-- `Spec L → Spec 𝓞_L`. -/
noncomputable abbrev jO (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

theorem cpt_comp_jO (τ : L →+* ℂ) :
    (cptObj τ).hom ≫ jO L = (GroupModel.ptC (L := L) τ).hom := by
  show Spec.map (CommRingCat.ofHom τ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) =
    Spec.map (CommRingCat.ofHom (τ.comp (algebraMap (𝓞 L) L)))
  rw [← Spec.map_comp]
  rfl

/-- The projection `𝒢_L → 𝒢`. -/
noncomputable def fstG : (genericFibre L 𝒢.G).left ⟶ 𝒢.G.left := pullback.fst 𝒢.G.hom (jO L)

theorem fstG_comp_hom : fstG 𝒢 ≫ 𝒢.G.hom = (genericFibre L 𝒢.G).hom ≫ jO L :=
  pullback.condition

/-- The morphism `A_L → 𝒢` (through `gen⁻¹ : A_L ≅ 𝒢_L` and the projection `𝒢_L → 𝒢`). -/
noncomputable def toModel : (A.baseChange L).X.left ⟶ 𝒢.G.left := 𝒢.gen.inv.left ≫ fstG 𝒢

theorem toModel_comp_hom :
    (toModel 𝒢) ≫ 𝒢.G.hom = (A.baseChange L).X.hom ≫ jO L := by
  unfold toModel
  rw [Category.assoc, fstG_comp_hom, ← Category.assoc, Over.w 𝒢.gen.inv]

/-- `θ : A_L(ℂ)_τ → 𝒢(ℂ)_τ`. -/
noncomputable def theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : 𝒢.Pts τ :=
  Over.homMk (q.left ≫ (toModel 𝒢))
    ((Category.assoc _ _ _).trans ((congrArg (q.left ≫ ·) (toModel_comp_hom 𝒢)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jO L) (Over.w q)).trans
        (cpt_comp_jO τ)))))

theorem theta_left {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) :
    ((theta 𝒢) q).left = q.left ≫ (toModel 𝒢) := rfl

/-- The base change `(Spec ℂ)_L` of `ptC τ`. -/
noncomputable abbrev ptCL (τ : L →+* ℂ) : Over (Spec (CommRingCat.of L)) :=
  (Over.pullback (jO L)).obj (GroupModel.ptC (L := L) τ)

/-- Its projection to `Spec ℂ` (`ptC τ`'s underlying scheme). -/
noncomputable def fstC (τ : L →+* ℂ) : (ptCL τ).left ⟶ (GroupModel.ptC (L := L) τ).left :=
  pullback.fst (GroupModel.ptC (L := L) τ).hom (jO L)

/-- The section `Spec ℂ → (Spec ℂ)_L` of the base change of `ptC τ`. -/
noncomputable def secC (τ : L →+* ℂ) : cptObj τ ⟶ ptCL τ :=
  Over.homMk (pullback.lift (𝟙 (Spec (CommRingCat.of ℂ))) (cptObj τ).hom
    ((Category.id_comp _).trans (cpt_comp_jO τ).symm))
    (pullback.lift_snd _ _ _)

theorem secC_fstC (τ : L →+* ℂ) : (secC τ).left ≫ fstC τ = 𝟙 _ :=
  pullback.lift_fst _ _ _

theorem secC_snd (τ : L →+* ℂ) : (secC τ).left ≫ (ptCL τ).hom = (cptObj τ).hom :=
  pullback.lift_snd _ _ _

/-- The base change of a complex point `p` of `𝒢`, as a map to `𝒢_L`. -/
noncomputable def mapG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : ptCL τ ⟶ genericFibre L 𝒢.G :=
  (Over.pullback (jO L)).map p

theorem mapG_fstG {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (mapG 𝒢 p).left ≫ fstG 𝒢 = fstC τ ≫ p.left :=
  pullback.lift_fst _ _ _

theorem mapG_snd {τ : L →+* ℂ} (p : 𝒢.Pts τ) :
    (mapG 𝒢 p).left ≫ (genericFibre L 𝒢.G).hom = (ptCL τ).hom :=
  pullback.lift_snd _ _ _

/-- `χ : 𝒢(ℂ)_τ → A_L(ℂ)_τ`. -/
noncomputable def chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : CPts (A.baseChange L) τ :=
  secC τ ≫ mapG 𝒢 p ≫ 𝒢.gen.hom

theorem chi_mul {τ : L →+* ℂ} (p₁ p₂ : 𝒢.Pts τ) : (chi 𝒢) (p₁ * p₂) = (chi 𝒢) p₁ * (chi 𝒢) p₂ := by
  letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
  haveI : IsMonHom 𝒢.gen.hom := 𝒢.gen_hom
  have hm : mapG 𝒢 (p₁ * p₂) = mapG 𝒢 p₁ * mapG 𝒢 p₂ := Functor.map_mul _ _ _
  unfold chi
  rw [hm, MonObj.mul_comp, MonObj.comp_mul]

theorem gen_hom_inv_left : 𝒢.gen.hom.left ≫ 𝒢.gen.inv.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]

theorem gen_inv_hom_left : 𝒢.gen.inv.left ≫ 𝒢.gen.hom.left = 𝟙 _ := by
  rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]

theorem theta_chi {τ : L →+* ℂ} (p : 𝒢.Pts τ) : (theta 𝒢) ((chi 𝒢) p) = p := by
  apply Over.OverMorphism.ext
  rw [theta_left]
  unfold chi toModel
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc 𝒢.gen.hom.left, gen_hom_inv_left, Category.id_comp, mapG_fstG]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p.left) (secC_fstC τ)).trans
    (Category.id_comp _))

theorem chi_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) : (chi 𝒢) ((theta 𝒢) q) = q := by
  apply Over.OverMorphism.ext
  have key : (secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left = q.left ≫ 𝒢.gen.inv.left := by
    apply pullback.hom_ext
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ fstG 𝒢 =
        (q.left ≫ 𝒢.gen.inv.left) ≫ fstG 𝒢
      rw [Category.assoc, mapG_fstG]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ((theta 𝒢) q).left)
        (secC_fstC τ)).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm))
    · change ((secC τ).left ≫ (mapG 𝒢 ((theta 𝒢) q)).left) ≫ (genericFibre L 𝒢.G).hom =
        (q.left ≫ 𝒢.gen.inv.left) ≫ (genericFibre L 𝒢.G).hom
      rw [Category.assoc, mapG_snd, secC_snd, Category.assoc, Over.w 𝒢.gen.inv, Over.w q]
  unfold chi
  simp only [Over.comp_left]
  rw [← Category.assoc, key, Category.assoc, gen_inv_hom_left, Category.comp_id]

theorem theta_mul {τ : L →+* ℂ} (q₁ q₂ : CPts (A.baseChange L) τ) :
    (theta 𝒢) (q₁ * q₂) = (theta 𝒢) q₁ * (theta 𝒢) q₂ := by
  conv_lhs => rw [← (chi_theta 𝒢) q₁, ← (chi_theta 𝒢) q₂, ← chi_mul, theta_chi]

theorem theta_injective {τ : L →+* ℂ} : Function.Injective (theta 𝒢 (τ := τ)) := fun a b h => by
  rw [← (chi_theta 𝒢) a, ← (chi_theta 𝒢) b, h]

theorem theta_surjective {τ : L →+* ℂ} : Function.Surjective (theta 𝒢 (τ := τ)) :=
  fun p => ⟨(chi 𝒢) p, (theta_chi 𝒢) p⟩

theorem theta_one {τ : L →+* ℂ} : (theta 𝒢) (1 : CPts (A.baseChange L) τ) = 1 := by
  have h := theta_mul 𝒢 (τ := τ) 1 1
  rw [_root_.mul_one] at h
  exact mul_left_cancel (a := (theta 𝒢) 1) (by rw [_root_.mul_one]; exact h.symm)

theorem evalAt_theta {τ : L →+* ℂ} (q : CPts (A.baseChange L) τ) (U : 𝒢.G.left.Opens)
    (s : Γ(𝒢.G.left, U)) :
    𝒢.evalAt ((theta 𝒢) q) U s = cEvalAt q ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s) := by
  unfold GroupModel.evalAt cEvalAt
  by_cases h : ⊤ ≤ q.left ⁻¹ᵁ ((toModel 𝒢) ⁻¹ᵁ U)
  · have h' : ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ ((theta 𝒢) q).left ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

end Transport

/-- **`AnalyticUniformizationOfDim` follows from leaf-push2's leaf `UniformizationExists`
(T35), proved.** Apply T35 to `A_L` over `L` at `σ = τ` (`dim A_L = dim A` by g0-dim's
`G0Dim.dim_baseChange`) and transport along `θ`. -/
theorem analyticUniformizationOfDim_of_uniformizationExists
    (hT : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.AnalyticUniformizationOfDim := by
  intro K _ A L _ _ _ 𝒢 τ g hg
  have hgL : (A.baseChange L).dim = (g : WithBot ℕ∞) := by
    rw [← hg]
    exact G0Dim.dim_baseChange L A.X.left A.X.hom
  obtain ⟨Λ, Φ₀, hd, hZ, hmul, hker, hsurj, hopen, hdiff⟩ := hT L (A.baseChange L) τ g hgL
  refine ⟨Λ, fun z => (theta 𝒢) (Φ₀ z), hd, hZ, fun z w => ?_, fun z => ?_, ?_, fun U => ?_,
    fun U s => ?_⟩
  · simp only [hmul, theta_mul]
  · rw [← hker z, ← theta_one 𝒢 (τ := τ)]
    exact (theta_injective 𝒢).eq_iff
  · exact (theta_surjective 𝒢).comp hsurj
  · exact hopen ((toModel 𝒢) ⁻¹ᵁ U)
  · have := hdiff ((toModel 𝒢) ⁻¹ᵁ U) ((toModel 𝒢).app U s)
    refine this.congr fun z _ => ?_
    exact (evalAt_theta 𝒢) (Φ₀ z) U s

end ZInQ.Metrization2

/-! ## metrization2: toward `ProductMapLocalStructure` — evaluation at complex points of schemes,
and sums of products in a pushout of commutative rings -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

/-- The value at a complex point `q : Spec ℂ → X` of `s ∈ Γ(X, U)` (`0` if `q ∉ U(ℂ)`). Same
formula as def-faltings' `GroupModel.evalAt` (which is `ev p.left`). -/
noncomputable def ev {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (s : Γ(X, U)) : ℂ := by
  classical
  exact if h : ⊤ ≤ q ⁻¹ᵁ U then (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ h s)
    else 0

section Ev

variable {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X)

theorem ev_comp (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) :
    ev (q ≫ f) U s = ev q (f ⁻¹ᵁ U) (f.app U s) := by
  unfold ev
  by_cases h : ⊤ ≤ q ⁻¹ᵁ (f ⁻¹ᵁ U)
  · have h' : ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_pos h', dif_pos h]
    congr 1
  · have h' : ¬ ⊤ ≤ (q ≫ f) ⁻¹ᵁ U := h
    rw [dif_neg h', dif_neg h]

theorem ev_res {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ q ⁻¹ᵁ V) (s : Γ(X, U)) :
    ev q V (X.presheaf.map i.op s) = ev q U s := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := hV.trans ((TopologicalSpace.Opens.map q.base).map i).le
  unfold ev
  rw [dif_pos hV, dif_pos hU, ← Scheme.Hom.map_appLE q hV i.op]
  rfl

theorem ev_add (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s + s') = ev q U s + ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_add]
    exact map_add (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_mul (U : X.Opens) (s s' : Γ(X, U)) : ev q U (s * s') = ev q U s * ev q U s' := by
  unfold ev
  split_ifs with h
  · rw [map_mul]
    exact map_mul (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom) _ _
  · simp

theorem ev_zero (U : X.Opens) : ev q U 0 = 0 := by
  unfold ev
  split_ifs with h
  · rw [map_zero]
    exact map_zero (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)
  · rfl

theorem ev_one (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) : ev q U 1 = 1 := by
  unfold ev
  rw [dif_pos h, map_one]
  exact map_one (ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom)

theorem ev_pow (U : X.Opens) (h : ⊤ ≤ q ⁻¹ᵁ U) (s : Γ(X, U)) (n : ℕ) :
    ev q U (s ^ n) = ev q U s ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ev_one q U h]
  | succ n ih => rw [pow_succ, pow_succ, ev_mul, ih]

theorem ev_sum (U : X.Opens) {n : ℕ} (s : Fin n → Γ(X, U)) :
    ev q U (∑ k, s k) = ∑ k, ev q U (s k) := by
  induction n with
  | zero => simp [ev_zero]
  | succ n ih => rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ev_add, ih]

/-- A complex point in `X.basicOpen s` gives `s` a nonzero value. -/
theorem ev_ne_zero_of_mem {U : X.Opens} (s : Γ(X, U)) (h : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s) :
    ev q U s ≠ 0 := by
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le s)).op s) :=
    X.toRingedSpace.isUnit_res_basicOpen s
  rw [← ev_res q (homOfLE (X.basicOpen_le s)) h]
  obtain ⟨u, hu'⟩ := hu
  intro h0
  have h1 := congrArg (ev q (X.basicOpen s)) u.mul_inv
  rw [ev_mul, ev_one q _ h, hu', h0, zero_mul] at h1
  exact zero_ne_one h1

/-- A complex point of `U` at which `s` has a nonzero value lies in `X.basicOpen s`. -/
theorem mem_basicOpen_of_ev_ne_zero {U : X.Opens} (s : Γ(X, U)) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (h : ev q U s ≠ 0) : ⊤ ≤ q ⁻¹ᵁ X.basicOpen s := by
  unfold ev at h
  rw [dif_pos hU] at h
  have hu : IsUnit (q.appLE U ⊤ hU s) := by
    have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appLE U ⊤ hU s)) :=
      isUnit_iff_ne_zero.mpr h
    have := hu'.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    simpa using this
  have hb := (Spec (CommRingCat.of ℂ)).basicOpen_of_isUnit hu
  rw [Scheme.Hom.preimage_basicOpen]
  have he : q.appLE U ⊤ hU s = (Spec (CommRingCat.of ℂ)).presheaf.map (homOfLE hU).op
      (q.app U s) := rfl
  rw [he, Scheme.basicOpen_res] at hb
  rw [← hb]
  exact inf_le_right

end Ev

/-- Finite sums of products `inl(α) · inr(β)`. -/
def IsSumProd {B C P : Type} [CommRing B] [CommRing C] [CommRing P] (inl : B →+* P)
    (inr : C →+* P) (r : P) : Prop :=
  ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k)

theorem isSumProd_add {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r + r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n + m, Fin.append α α', Fin.append β β', ?_⟩
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem isSumProd_mul {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r r' : P} (h : IsSumProd inl inr r) (h' : IsSumProd inl inr r') :
    IsSumProd inl inr (r * r') := by
  obtain ⟨n, α, β, rfl⟩ := h
  obtain ⟨m, α', β', rfl⟩ := h'
  refine ⟨n * m, fun k => α (finProdFinEquiv.symm k).1 * α' (finProdFinEquiv.symm k).2,
    fun k => β (finProdFinEquiv.symm k).1 * β' (finProdFinEquiv.symm k).2, ?_⟩
  rw [Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  show _ = ∑ k, (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))
    (finProdFinEquiv.symm k)
  refine Eq.trans ?_ (Equiv.sum_comp finProdFinEquiv.symm
    (fun p : Fin n × Fin m => inl (α p.1 * α' p.2) * inr (β p.1 * β' p.2))).symm
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [map_mul]
  ring

theorem isSumProd_neg {B C P : Type} [CommRing B] [CommRing C] [CommRing P] {inl : B →+* P}
    {inr : C →+* P} {r : P} (h : IsSumProd inl inr r) : IsSumProd inl inr (-r) := by
  obtain ⟨n, α, β, rfl⟩ := h
  exact ⟨n, fun k => -α k, β, by simp [Finset.sum_neg_distrib]⟩

/-- In a pushout square of commutative rings, every element of the pushout is a finite sum of
products `inl(α) · inr(β)`. -/
theorem exists_sum_of_isPushout {A B C P : CommRingCat.{0}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ P} {inr : C ⟶ P} (h : IsPushout f g inl inr) (r : P) :
    ∃ (n : ℕ) (α : Fin n → B) (β : Fin n → C), r = ∑ k, inl (α k) * inr (β k) := by
  let T : Subring P := Subring.closure (Set.range inl.hom ∪ Set.range inr.hom)
  have hT : ∀ x ∈ T, IsSumProd inl.hom inr.hom x := by
    intro x hx
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨c, rfl⟩
      · exact ⟨1, fun _ => b, fun _ => 1, by simp⟩
      · exact ⟨1, fun _ => 1, fun _ => c, by simp⟩
    | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
    | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
    | add x y _ _ hx hy => exact isSumProd_add hx hy
    | neg x _ hx => exact isSumProd_neg hx
    | mul x y _ _ hx hy => exact isSumProd_mul hx hy
  let jl : B ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inl.hom.codRestrict T fun b => Subring.subset_closure (Or.inl ⟨b, rfl⟩))
  let jr : C ⟶ CommRingCat.of T := CommRingCat.ofHom
    (inr.hom.codRestrict T fun c => Subring.subset_closure (Or.inr ⟨c, rfl⟩))
  have w : f ≫ jl = g ≫ jr := by
    ext a
    exact congrArg (fun φ => (ConcreteCategory.hom φ) a) h.w
  let ι : CommRingCat.of T ⟶ P := CommRingCat.ofHom T.subtype
  have hid : h.desc jl jr w ≫ ι = 𝟙 P := by
    apply h.hom_ext
    · rw [h.inl_desc_assoc, Category.comp_id]; rfl
    · rw [h.inr_desc_assoc, Category.comp_id]; rfl
  have hr : r ∈ T := by
    have : ι (h.desc jl jr w r) = r := by rw [← ConcreteCategory.comp_apply, hid]; rfl
    rw [← this]
    exact ((h.desc jl jr w) r).2
  exact hT r hr

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, proved

The local structure of a fibre product of schemes over an affine base at complex points
(`core_local`): affine opens `Vᵢ`, the affine scheme `Q = V₁ ×_S V₂` (an open of the product
through `j`), whose ring is the pushout `Γ(V₁) ⊗_{Γ(S)} Γ(V₂)` (`isPushout_appTop_of_isPullback`),
a basic open `D(h) ⊆ j⁻¹W` of `Q` and a fraction `t = a/h^N` on it. -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits Opposite

theorem specC_eq (z w : Spec (CommRingCat.of ℂ)) : z = w := by
  have hz : z.asIdeal = ⊥ := by
    haveI := z.isPrime; exact Ideal.eq_bot_of_prime _
  have hw : w.asIdeal = ⊥ := by
    haveI := w.isPrime; exact Ideal.eq_bot_of_prime _
  exact PrimeSpectrum.ext (hz.trans hw.symm)

theorem top_le_of_mem {X : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (U : X.Opens)
    (pt : Spec (CommRingCat.of ℂ)) (h : q pt ∈ U) : ⊤ ≤ q ⁻¹ᵁ U := by
  intro z _
  rw [specC_eq z pt]
  exact h

/-- The section of `X` on `U` corresponding to a global section of `U.toScheme`. -/
noncomputable def secOf {X : Scheme.{0}} (U : X.Opens) (α : Γ(U.toScheme, ⊤)) : Γ(X, U) :=
  (inv (U.ι.appLE U ⊤ U.ι_preimage_self.ge)) α

theorem ev_secOf {X : Scheme.{0}} (U : X.Opens) (y : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (α : Γ(U.toScheme, ⊤)) : ev (y ≫ U.ι) U (secOf U α) = ev y ⊤ α := by
  have h1 : ⊤ ≤ (y ≫ U.ι) ⁻¹ᵁ U := by
    intro z _
    show U.ι (y z) ∈ U
    exact (y z).2
  have h2 : ⊤ ≤ y ⁻¹ᵁ (⊤ : U.toScheme.Opens) := fun _ _ => trivial
  unfold ev
  rw [dif_pos h1, dif_pos h2]
  congr 1
  rw [← Scheme.Hom.appLE_comp_appLE y U.ι U ⊤ ⊤ U.ι_preimage_self.ge h2]
  unfold secOf
  rw [← ConcreteCategory.comp_apply, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

theorem ev_comp_top {X Y : Scheme.{0}} (q : Spec (CommRingCat.of ℂ) ⟶ X) (f : X ⟶ Y)
    (s : Γ(Y, ⊤)) : ev (q ≫ f) ⊤ s = ev q ⊤ (f.appTop s) :=
  ev_comp q f ⊤ s

section Core

variable {S X₁ X₂ : Scheme.{0}} (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S)

/-- **The local structure of a fibre product over an affine base, at complex points.** -/
theorem core_local [IsAffine S] (W : (pullback f₁ f₂).Opens) (t : Γ(pullback f₁ f₂, W))
    (x₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (x₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
    (hx12 : x₁ ≫ f₁ = x₂ ≫ f₂) (hx : ⊤ ≤ (pullback.lift x₁ x₂ hx12) ⁻¹ᵁ W) :
    ∃ (V₁ : X₁.Opens) (V₂ : X₂.Opens) (n : ℕ) (a c : Fin n → Γ(X₁, V₁))
      (b d : Fin n → Γ(X₂, V₂)),
      ⊤ ≤ x₁ ⁻¹ᵁ V₁ ∧ ⊤ ≤ x₂ ⁻¹ᵁ V₂ ∧
      (∑ k, ev x₁ V₁ (c k) * ev x₂ V₂ (d k)) ≠ 0 ∧
      ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
        (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
        (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) ≠ 0 →
        ⊤ ≤ (pullback.lift y₁ y₂ hy) ⁻¹ᵁ W ∧
        ev (pullback.lift y₁ y₂ hy) W t * (∑ k, ev y₁ V₁ (c k) * ev y₂ V₂ (d k)) =
          ∑ k, ev y₁ V₁ (a k) * ev y₂ V₂ (b k) := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of ℂ)) := inferInstance
  have hpt : pt ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) := trivial
  obtain ⟨V₁, hV₁, m₁, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₁ pt ∈ (⊤ : X₁.Opens) from trivial)
  obtain ⟨V₂, hV₂, m₂, -⟩ := exists_isAffineOpen_mem_and_subset
    (show x₂ pt ∈ (⊤ : X₂.Opens) from trivial)
  haveI : IsAffine V₁.toScheme := hV₁
  haveI : IsAffine V₂.toScheme := hV₂
  set g₁ := V₁.ι ≫ f₁ with hg₁
  set g₂ := V₂.ι ≫ f₂ with hg₂
  let j : pullback g₁ g₂ ⟶ pullback f₁ f₂ :=
    pullback.map g₁ g₂ f₁ f₂ V₁.ι V₂.ι (𝟙 S) (by simp [hg₁]) (by simp [hg₂])
  have hj1 : j ≫ pullback.fst f₁ f₂ = pullback.fst g₁ g₂ ≫ V₁.ι := pullback.lift_fst _ _ _
  have hj2 : j ≫ pullback.snd f₁ f₂ = pullback.snd g₁ g₂ ≫ V₂.ι := pullback.lift_snd _ _ _
  -- complex points of `V₁ × V₂` lift to `Q`
  have lift_pt : ∀ (y₁ : Spec (CommRingCat.of ℂ) ⟶ X₁) (y₂ : Spec (CommRingCat.of ℂ) ⟶ X₂)
      (hy : y₁ ≫ f₁ = y₂ ≫ f₂), ⊤ ≤ y₁ ⁻¹ᵁ V₁ → ⊤ ≤ y₂ ⁻¹ᵁ V₂ →
      ∃ yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂, yQ ≫ j = pullback.lift y₁ y₂ hy ∧
        yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι = y₁ ∧ yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι = y₂ := by
    intro y₁ y₂ hy h1 h2
    have r1 : Set.range y₁ ⊆ Set.range V₁.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h1 (show z ∈ ⊤ from trivial)
    have r2 : Set.range y₂ ⊆ Set.range V₂.ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨z, rfl⟩; exact h2 (show z ∈ ⊤ from trivial)
    let z₁ := IsOpenImmersion.lift V₁.ι y₁ r1
    let z₂ := IsOpenImmersion.lift V₂.ι y₂ r2
    have hz₁ : z₁ ≫ V₁.ι = y₁ := IsOpenImmersion.lift_fac _ _ _
    have hz₂ : z₂ ≫ V₂.ι = y₂ := IsOpenImmersion.lift_fac _ _ _
    have hc : z₁ ≫ g₁ = z₂ ≫ g₂ := by
      rw [hg₁, hg₂, ← Category.assoc, hz₁, ← Category.assoc, hz₂, hy]
    refine ⟨pullback.lift z₁ z₂ hc, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hj1, pullback.lift_fst, pullback.lift_fst_assoc, hz₁]
      · rw [Category.assoc, hj2, pullback.lift_snd, pullback.lift_snd_assoc, hz₂]
    · rw [pullback.lift_fst_assoc, hz₁]
    · rw [pullback.lift_snd_assoc, hz₂]
  obtain ⟨xQ, hxQ, -, -⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
    (top_le_of_mem _ _ pt m₂)
  have hxQW : xQ pt ∈ j ⁻¹ᵁ W := by
    have := hx hpt
    rw [← hxQ] at this
    exact this
  obtain ⟨h, hhW, hhx⟩ := (isAffineOpen_top (pullback g₁ g₂)).exists_basicOpen_le
    (V := j ⁻¹ᵁ W) ⟨xQ pt, hxQW⟩ trivial
  -- the fraction
  set tQ : Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) :=
    (pullback g₁ g₂).presheaf.map (homOfLE hhW).op (j.app W t) with htQ
  obtain ⟨⟨a0, ⟨_, N, rfl⟩⟩, heq⟩ := IsLocalization.surj (Submonoid.powers h) tQ
  have hal : ∀ r : Γ(pullback g₁ g₂, ⊤),
      algebraMap Γ(pullback g₁ g₂, ⊤) Γ(pullback g₁ g₂, (pullback g₁ g₂).basicOpen h) r =
        (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op r :=
    fun _ => rfl
  have heq' : tQ * (pullback g₁ g₂).presheaf.map (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op
      (h ^ (N + 1)) = (pullback g₁ g₂).presheaf.map
        (homOfLE ((pullback g₁ g₂).basicOpen_le h)).op (a0 * h) := by
    simp only at heq
    rw [← hal, ← hal, pow_succ, map_mul, map_mul, ← mul_assoc, heq]
  -- sums of products
  have hpo := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g₁ g₂)
  obtain ⟨n₁, α, β, hα⟩ := exists_sum_of_isPushout hpo (a0 * h)
  obtain ⟨n₂, γ, δ, hγ⟩ := exists_sum_of_isPushout hpo (h ^ (N + 1))
  -- evaluation of a sum of products at a lifted point
  have key : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂) {m : ℕ}
      (u : Fin m → Γ(V₁.toScheme, ⊤)) (v : Fin m → Γ(V₂.toScheme, ⊤)),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (secOf V₁ (u k)) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (secOf V₂ (v k))) =
      ev yQ ⊤ (∑ k, (pullback.fst g₁ g₂).appTop (u k) * (pullback.snd g₁ g₂).appTop (v k)) := by
    intro yQ m u v
    rw [ev_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ev_mul, ← Category.assoc, ev_secOf, ← Category.assoc, ev_secOf, ev_comp_top,
      ev_comp_top]
  let a : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append (fun k => secOf V₁ (α k)) 0
  let b : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append (fun k => secOf V₂ (β k)) 0
  let c : Fin (n₁ + n₂) → Γ(X₁, V₁) := Fin.append 0 (fun k => secOf V₁ (γ k))
  let d : Fin (n₁ + n₂) → Γ(X₂, V₂) := Fin.append 0 (fun k => secOf V₂ (δ k))
  have hA : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (a k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (b k)) = ev yQ ⊤ (a0 * h) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [a, b, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [key, hα]
  have hH : ∀ (yQ : Spec (CommRingCat.of ℂ) ⟶ pullback g₁ g₂),
      (∑ k, ev (yQ ≫ pullback.fst g₁ g₂ ≫ V₁.ι) V₁ (c k) *
        ev (yQ ≫ pullback.snd g₁ g₂ ≫ V₂.ι) V₂ (d k)) = ev yQ ⊤ h ^ (N + 1) := by
    intro yQ
    rw [Fin.sum_univ_add]
    simp only [c, d, Fin.append_left, Fin.append_right, Pi.zero_apply, ev_zero, zero_mul,
      Finset.sum_const_zero, zero_add]
    rw [key, ← hγ, ev_pow yQ ⊤ (fun _ _ => trivial)]
  refine ⟨V₁, V₂, n₁ + n₂, a, c, b, d, top_le_of_mem _ _ pt m₁, top_le_of_mem _ _ pt m₂, ?_, ?_⟩
  · obtain ⟨xQ', hxQ', e1, e2⟩ := lift_pt x₁ x₂ hx12 (top_le_of_mem _ _ pt m₁)
      (top_le_of_mem _ _ pt m₂)
    have hxQ'h : ⊤ ≤ xQ' ⁻¹ᵁ (pullback g₁ g₂).basicOpen h := by
      have hjinj : xQ' = xQ := by
        apply pullback.hom_ext
        · apply (cancel_mono V₁.ι).mp
          rw [Category.assoc, Category.assoc, e1, ← hj1, ← Category.assoc, hxQ,
            pullback.lift_fst]
        · apply (cancel_mono V₂.ι).mp
          rw [Category.assoc, Category.assoc, e2, ← hj2, ← Category.assoc, hxQ,
            pullback.lift_snd]
      rw [hjinj]
      exact top_le_of_mem _ _ pt hhx
    rw [← e1, ← e2, hH]
    exact pow_ne_zero _ (ev_ne_zero_of_mem xQ' h hxQ'h)
  · intro y₁ y₂ hy h1 h2 hne
    obtain ⟨yQ, hyQ, e1, e2⟩ := lift_pt y₁ y₂ hy h1 h2
    subst e1 e2
    rw [hH] at hne ⊢
    rw [hA]
    have hev : ev yQ ⊤ h ≠ 0 := fun h0 => hne (by rw [h0, zero_pow (Nat.succ_ne_zero N)])
    have hmem : ⊤ ≤ yQ ⁻¹ᵁ (pullback g₁ g₂).basicOpen h :=
      mem_basicOpen_of_ev_ne_zero yQ h (fun _ _ => trivial) hev
    have hW : ⊤ ≤ yQ ⁻¹ᵁ (j ⁻¹ᵁ W) := hmem.trans ((TopologicalSpace.Opens.map yQ.base).map
      (homOfLE hhW)).le
    refine ⟨?_, ?_⟩
    · rw [← hyQ]; exact hW
    · rw [← hyQ, ev_comp, ← ev_res yQ (homOfLE hhW) hmem, ← htQ,
        ← ev_pow yQ ⊤ (fun _ _ => trivial),
        ← ev_res yQ (homOfLE ((pullback g₁ g₂).basicOpen_le h)) hmem (h ^ (N + 1)),
        ← ev_mul, heq', ev_res yQ _ hmem]

end Core

end ZInQ.Metrization2
/-! ## metrization2: `ProductMapLocalStructure`, hence `JacDetNondegenerate` and
`ProductLocalStructure`, proved -/

namespace ZInQ.Metrization2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

/-- **`ProductMapLocalStructure`, proved** (from `core_local` with `S = Spec 𝓞_L`,
`W = m⁻¹(U)`, `t = m^*s`). -/
theorem productMapLocalStructure : ProductMapLocalStructure := by
  intro K _ A B C L _ _ _ ℋ 𝒢₁ 𝒢₂ m τ U s p₁ p₂ hp
  have hw : ∀ (p₁' : 𝒢₁.Pts τ) (p₂' : 𝒢₂.Pts τ), p₁'.left ≫ 𝒢₁.G.hom = p₂'.left ≫ 𝒢₂.G.hom :=
    fun p₁' p₂' => (Over.w p₁').trans (Over.w p₂').symm
  obtain ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, hall⟩ :=
    core_local 𝒢₁.G.hom 𝒢₂.G.hom (m.left ⁻¹ᵁ U) (m.left.app U s) p₁.left p₂.left (hw p₁ p₂) hp
  refine ⟨V₁, V₂, n, a, c, b, d, h1, h2, hne, fun p₁' p₂' h1' h2' hne' => ?_⟩
  obtain ⟨hmem, heq⟩ := hall p₁'.left p₂'.left (hw p₁' p₂') h1' h2' hne'
  refine ⟨hmem, ?_⟩
  have hev : ℋ.evalAt (lift p₁' p₂' ≫ m) U s =
      ev (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) (m.left ⁻¹ᵁ U) (m.left.app U s) :=
    ev_comp (pullback.lift p₁'.left p₂'.left (hw p₁' p₂')) m.left U s
  rw [hev]
  exact heq

/-- **`JacDetNondegenerate`, proved** (no hypotheses). -/
theorem jacDetNondegenerate : ZInQ.Metrization.JacDetNondegenerate :=
  jacDetNondegenerate_of productMapLocalStructure

/-- **metrization's `ProductLocalStructure`, proved** (no hypotheses). -/
theorem productLocalStructure : ZInQ.Metrization.ProductLocalStructure :=
  productLocalStructure_of productMapLocalStructure

end ZInQ.Metrization2




/-! # unif-dims: the 2-torsion of `ℂ^g/Λ` has `4^g` elements (Mathlib only)

If `Φ : ℂ^g → G` is a surjective homomorphism onto a group with kernel a discrete full `ℤ`-lattice
`Λ`, then `#{p ∈ G | p² = 1} = 2^(2g)`. Hence the dimension `g` of such a "uniformization" is
determined by the abstract group `G`. -/

namespace ZInQ.UnifDims

open Module

variable {G : Type*} [Group G] {g : ℕ}

/-- The additive homomorphism `λ ↦ Φ(λ/2)` from the lattice to `G`. -/
noncomputable def halfHom (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ))
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) : Λ →+ Additive G :=
  AddMonoidHom.mk' (fun l => Additive.ofMul (Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)))) (by
    intro a b
    simp only [Submodule.coe_add, smul_add, hmul]
    rfl)

/-- **The 2-torsion of a uniformized group.** -/
theorem card_twoTorsion (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (hsurj : Function.Surjective Φ) : Nat.card {p : G // p * p = 1} = 2 ^ (2 * g) := by
  set ψ := halfHom Φ Λ hmul
  -- rank of `Λ`
  have hrank : finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ Λ hrank
  -- `Λ ⧸ ker ψ ≃ range ψ ≃ G[2]`
  have hrange : ∀ p : G, p * p = 1 ↔ Additive.ofMul p ∈ ψ.range := by
    intro p
    constructor
    · intro hp
      obtain ⟨z, rfl⟩ := hsurj p
      have h2 : (2 : ℂ) • z ∈ Λ := by
        rw [← hker, two_smul, hmul, hp]
      refine ⟨⟨_, h2⟩, ?_⟩
      show Additive.ofMul (Φ ((1 / 2 : ℂ) • (2 : ℂ) • z)) = _
      rw [smul_smul]
      norm_num
    · rintro ⟨l, hl⟩
      have hl' : Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)) = p := hl
      rw [← hl', ← hmul, ← add_smul]
      norm_num
      exact (hker _).mpr l.2
  have hker' : ψ.ker = (AddSubgroup.pi Set.univ (fun _ : Fin (2 * g) =>
      AddSubgroup.zmultiples (2 : ℤ))).comap b.equivFun.toLinearMap.toAddMonoidHom := by
    ext l
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ,
      true_implies, Int.mem_zmultiples_iff]
    show Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)) = 1 ↔ _
    rw [hker]
    constructor
    · intro h i
      set μ : Λ := ⟨_, h⟩
      have hl : l = (2 : ℤ) • μ := by
        ext1
        simp only [SetLike.val_smul, μ]
        rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        norm_num
      refine ⟨b.equivFun μ i, ?_⟩
      have := congrArg (fun x => b.equivFun x i) hl
      simp only [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at this
      exact this
    · intro h
      choose d hd using h
      let μ : Λ := b.equivFun.symm d
      have hl : l = (2 : ℤ) • μ := by
        apply b.equivFun.injective
        ext i
        simp only [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, μ,
          LinearEquiv.apply_symm_apply]
        exact hd i
      have : (1 / 2 : ℂ) • (l : Fin g → ℂ) = (μ : Fin g → ℂ) := by
        rw [hl, SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        norm_num
      rw [this]
      exact μ.2
  have hidx : ψ.ker.index = 2 ^ (2 * g) := by
    rw [hker', AddSubgroup.index_comap_of_surjective _ b.equivFun.surjective,
      AddSubgroup.index_pi]
    simp [Int.index_zmultiples]
  calc Nat.card {p : G // p * p = 1}
      = Nat.card ψ.range := Nat.card_congr
        (Equiv.subtypeEquiv Additive.ofMul (fun p => hrange p))
    _ = Nat.card (Λ ⧸ ψ.ker) := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv.symm
    _ = 2 ^ (2 * g) := hidx

/-- **The dimension of a uniformization is determined by the group.** -/
theorem dim_eq_of_unif {g g' : ℕ} (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g' → ℂ) → G) (Λ' : Submodule ℤ (Fin g' → ℂ))
    (hd : DiscreteTopology Λ) (hz : IsZLattice ℝ Λ) (hd' : DiscreteTopology Λ')
    (hz' : IsZLattice ℝ Λ')
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (hsurj : Function.Surjective Φ)
    (hmul' : ∀ z w, Φ' (z + w) = Φ' z * Φ' w) (hker' : ∀ z, Φ' z = 1 ↔ z ∈ Λ')
    (hsurj' : Function.Surjective Φ') : g = g' := by
  have h1 := card_twoTorsion Φ Λ hmul hker hsurj
  have h2 := card_twoTorsion Φ' Λ' hmul' hker' hsurj'
  rw [h1] at h2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

end ZInQ.UnifDims


/-! ## unif-dims: `ProductUnifDims` from T35 (`UniformizationExists`)

The dimension half (`ProductUnifDimsEq`) holds because the dimension of an analytic uniformization
of `𝒢(ℂ)_τ` is determined by the group `𝒢(ℂ)_τ` (its 2-torsion has `4^g` elements,
`ZInQ.UnifDims.dim_eq_of_unif`), and T35 supplies one uniformization of dimension `dim A`
(`AnalyticUniformizationOfDim`, metrization2's transport of T35 to group models). The
nonsingularity half is metrization2's `jacDetNondegenerate` (proved, no hypotheses). The product
structure and the metrization `MP` are not used. -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

/-- An abelian variety has finite dimension (copied from metrization's `abVar_dim_finite`). -/
theorem abVar_dim_finite (K : Type) [Field K] (A : AbVar K) :
    ∃ n : ℕ, A.dim = (n : WithBot ℕ∞) := by
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

/-- **The dimension of an analytic uniformization is `dim A`** (from `AnalyticUniformizationOfDim`,
i.e. from T35). Any full-lattice analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` has `g = dim A`. Only
the algebraic clauses (homomorphism, kernel, onto) of the two uniformizations are used. -/
theorem dim_eq_of_isAnalyticUniformization (hU : ZInQ.Metrization.AnalyticUniformizationOfDim)
    {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) → 𝒢.Pts τ) (hd : DiscreteTopology Λ) (hz : IsZLattice ℝ Λ)
    (hΦ : 𝒢.IsAnalyticUniformization τ Λ Φ) : A.dim = (g : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := abVar_dim_finite K A
  obtain ⟨Λ', Φ', hd', hz', hΦ'⟩ := hU K A L 𝒢 τ n hn
  have := dim_eq_of_unif Φ Λ Φ' Λ' hd hz hd' hz' hΦ.1 hΦ.2.1 hΦ.2.2.1 hΦ'.1 hΦ'.2.1 hΦ'.2.2.1
  rw [hn, this]

/-- **`ProductUnifDimsEq` from `AnalyticUniformizationOfDim` (proved).** -/
theorem productUnifDimsEq_of (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductUnif.ProductUnifDimsEq := by
  intro K _ A B C L _ _ _ 𝒢₁ 𝒢₂ g MP e _ _ τ g₁ g₂ hg Λ₁ Λ₂ Φ₁ Φ₂ hl₁ hl₂ hu₁ hu₂ _ _
  obtain ⟨hd₁, hz₁⟩ := hl₁
  obtain ⟨hd₂, hz₂⟩ := hl₂
  exact ⟨dim_eq_of_isAnalyticUniformization hU 𝒢₁ τ Λ₁ Φ₁ hd₁ hz₁ hu₁,
    dim_eq_of_isAnalyticUniformization hU 𝒢₂ τ Λ₂ Φ₂ hd₂ hz₂ hu₂⟩

/-- **`ProductUnifDims` from `AnalyticUniformizationOfDim` (proved).** -/
theorem productUnifDims_of_unifOfDim (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.ProductUnif.ProductUnifDims :=
  ZInQ.ProductUnif.productUnifDims_of (productUnifDimsEq_of hU)
    ZInQ.Metrization2.jacDetNondegenerate

/-- **`ProductUnifDims` from the textbook leaf T35 `UniformizationExists` (proved).** -/
theorem productUnifDims_of_uniformizationExists (hT : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.ProductUnif.ProductUnifDims :=
  productUnifDims_of_unifOfDim
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT)

end ZInQ.UnifDims




/-! # unif-dims: `DetLatticeProd` (determinant lattice of a direct sum), proof attempt -/

namespace ZInQ.UnifDims

open NumberField TensorProduct ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice
open scoped nonZeroDivisors

section Line

variable {K : Type} [Field K] [NumberField K]
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M]

/-- The determinant functional `K ⊗ ⋀^g M → K` of a `K`-basis of `K ⊗ M`. -/
noncomputable def detFun {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) :
    (K ⊗[𝓞 K] ⋀[𝓞 K]^g M) →ₗ[K] K :=
  (exteriorPower.alternatingMapLinearEquiv
    ({ toMultilinearMap := (b.det.toMultilinearMap.restrictScalars (𝓞 K)).compLinearMap
          (fun _ => TensorProduct.mk (𝓞 K) K M 1)
       map_eq_zero_of_eq' := fun v i j hv hij =>
          b.det.map_eq_zero_of_eq (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) (by simp [hv]) hij } :
      M [⋀^Fin g]→ₗ[𝓞 K] K)).liftBaseChange K

theorem detFun_tmul {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) (v : Fin g → M) :
    detFun b ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g v) =
      b.det (fun k => (1 : K) ⊗ₜ[𝓞 K] v k) := by
  simp only [detFun, LinearMap.liftBaseChange_one_tmul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The determinant functional of a basis `1 ⊗ wⱼ` is injective (the Hodge space is the line
spanned by `1 ⊗ ∧w`); steps 2-4 of hodge-lattice's `hodgeLattice_of_lattice`. -/
theorem detFun_injective {g : ℕ} (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)) (w : Fin g → M)
    (hbw : ∀ j, (1 : K) ⊗ₜ[𝓞 K] w j = b j) : Function.Injective (detFun b) := by
  have hclear := exists_clear (K := K) w (fun v => by
    have hr : Set.range (fun j => (1 : K) ⊗ₜ[𝓞 K] w j) = Set.range b := by
      rw [show (fun j => (1 : K) ⊗ₜ[𝓞 K] w j) = b from funext hbw]
    rw [hr, b.span_eq]; exact Submodule.mem_top)
  set s0 : K ⊗[𝓞 K] ⋀[𝓞 K]^g M := (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g w with hs0
  have hone : ∀ x : ⋀[𝓞 K]^g M, (1 : K) ⊗ₜ[𝓞 K] x ∈ Submodule.span K {s0} := by
    intro x
    have hx : x ∈ Submodule.span (𝓞 K) (Set.range (exteriorPower.ιMulti (𝓞 K) g)) := by
      rw [exteriorPower.ιMulti_span]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, rfl⟩ := hy
      exact tmul_ιMulti_mem_span w hclear v
    | zero => rw [TensorProduct.tmul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ r hy
  have htop : Submodule.span K {s0} = ⊤ := by
    rw [eq_top_iff]
    rintro h -
    induction h using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul k x =>
      have : k ⊗ₜ[𝓞 K] x = k • ((1 : K) ⊗ₜ[𝓞 K] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]; exact Submodule.smul_mem _ k (hone x)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have hΨ : detFun b s0 = 1 := by
    rw [hs0, detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] w k) = b from funext hbw,
      Module.Basis.det_self]
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have : x ∈ Submodule.span K {s0} := htop ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp this
  rw [LinearMap.mem_ker, map_smul, hΨ, smul_eq_mul, mul_one] at hx
  rw [hx, zero_smul]
  exact Submodule.zero_mem _

/-- Step 1 of hodge-lattice's `hodgeLattice_of_lattice`: a `K`-basis of `K ⊗ M` of the form
`1 ⊗ wⱼ` with `wⱼ ∈ ω`. -/
theorem exists_basis_of_span {g : ℕ} (ω : Submodule (𝓞 K) M)
    (hrank : Module.rank K (K ⊗[𝓞 K] M) = g)
    (hspan : Submodule.span K (Set.range fun x : ω => (1 : K) ⊗ₜ[𝓞 K] (x : M)) = ⊤) :
    ∃ (w : Fin g → ω) (b : Module.Basis (Fin g) K (K ⊗[𝓞 K] M)),
      ∀ j, (1 : K) ⊗ₜ[𝓞 K] (w j : M) = b j := by
  classical
  set V := K ⊗[𝓞 K] M
  set f : ω → V := fun x => (1 : K) ⊗ₜ[𝓞 K] (x : M) with hf
  have : FiniteDimensional K V := Module.finite_of_rank_eq_nat hrank
  have hfin : Module.finrank K V = g := Module.finrank_eq_of_rank_eq hrank
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range f)
  let bs : Module.Basis s K V := Module.Basis.mk hs_li (by
    rw [Subtype.range_coe, hs_span, hspan])
  let b : Module.Basis (Fin g) K V :=
    bs.reindex (bs.indexEquiv (Module.finBasisOfFinrankEq K V hfin))
  have hmem : ∀ j, ∃ x : ω, f x = b j := fun j => by
    have : (b j : V) ∈ s := by
      simp only [b, Module.Basis.reindex_apply, bs, Module.Basis.coe_mk]
      exact Subtype.mem _
    exact hs_sub this
  choose w hw using hmem
  exact ⟨w, b, hw⟩

/-- `secIndex` is invariant under an injective `K`-linear map. -/
theorem secIndex_map {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (Ψ : V →ₗ[K] K) (hΨ : Function.Injective Ψ)
    (Λ : Submodule (𝓞 K) V) (s : V) :
    secIndex Λ s = secIndex (Λ.map (Ψ.restrictScalars (𝓞 K))) (Ψ s) := by
  unfold secIndex
  have hspan : Submodule.map (Ψ.restrictScalars (𝓞 K)) (Submodule.span (𝓞 K) {s}) =
      Submodule.span (𝓞 K) {Ψ s} := by
    rw [Submodule.map_span, Set.image_singleton]; rfl
  rw [← hspan, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact (AddSubgroup.relIndex_map_map_of_injective _ _
    (f := ((Ψ.restrictScalars (𝓞 K)) : V →+ K)) hΨ).symm

/-- **Indices of `1` multiply** in a product of finitely generated `𝓞_K`-submodules of `K`
containing `1` (through `FractionalIdeal.absNorm` and the kernel's `secIndex_mul_absNorm`). -/
theorem secIndex_one_mul (I J : Submodule (𝓞 K) K) (hI : I.FG) (hJ : J.FG) (h1I : (1 : K) ∈ I)
    (h1J : (1 : K) ∈ J) : secIndex (I * J) 1 = secIndex I 1 * secIndex J 1 := by
  let I' : FractionalIdeal (𝓞 K)⁰ K := ⟨I, FractionalIdeal.isFractional_of_fg hI⟩
  let J' : FractionalIdeal (𝓞 K)⁰ K := ⟨J, FractionalIdeal.isFractional_of_fg hJ⟩
  have hIJ : ((I' * J' : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = I * J :=
    FractionalIdeal.coe_mul _ _
  have h1 : (1 : K) ∈ (I' * J' : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.mem_coe, hIJ, ← mul_one (1 : K)]
    exact Submodule.mul_mem_mul h1I h1J
  have e1 := secIndex_mul_absNorm I' h1I one_ne_zero
  have e2 := secIndex_mul_absNorm J' h1J one_ne_zero
  have e3 := secIndex_mul_absNorm (I' * J') h1 one_ne_zero
  rw [hIJ] at e3
  simp only [map_one, abs_one, map_mul] at e1 e2 e3
  have : (secIndex (I * J) 1 : ℚ) = secIndex I 1 * secIndex J 1 := by
    have hI0 : FractionalIdeal.absNorm I' ≠ 0 := by
      intro h; rw [h, mul_zero] at e1; exact zero_ne_one e1
    have hJ0 : FractionalIdeal.absNorm J' ≠ 0 := by
      intro h; rw [h, mul_zero] at e2; exact zero_ne_one e2
    change (secIndex (I * J) 1 : ℚ) * (FractionalIdeal.absNorm I' * FractionalIdeal.absNorm J')
      = 1 at e3
    change (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I' = 1 at e1
    change (secIndex J 1 : ℚ) * FractionalIdeal.absNorm J' = 1 at e2
    linear_combination (-(secIndex (I * J) 1 : ℚ)) * e1 +
      (-(secIndex (I * J) 1 : ℚ) * secIndex I 1 * FractionalIdeal.absNorm I') * e2 +
      ((secIndex I 1 : ℚ) * secIndex J 1) * e3
  exact_mod_cast this

end Line


section Prod

variable {K : Type} [Field K] [NumberField K]
variable {M₁ M₂ M : Type} [AddCommGroup M₁] [Module (𝓞 K) M₁] [AddCommGroup M₂] [Module (𝓞 K) M₂]
  [AddCommGroup M] [Module (𝓞 K) M]

/-- `K ⊗ M₁ × K ⊗ M₂ ≃ K ⊗ M` from `M₁ × M₂ ≃ M`. -/
noncomputable def sumIso (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) :
    ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M) :=
  (TensorProduct.prodRight (𝓞 K) K K M₁ M₂).symm ≪≫ₗ
    LinearEquiv.baseChange (𝓞 K) K _ _ (LinearEquiv.ofBijective _ hbij)

theorem sumIso_inl (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) (m : M₁) :
    sumIso j₁ j₂ hbij ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m := by
  simp only [sumIso, LinearEquiv.trans_apply]
  rw [show ((1 : K) ⊗ₜ[𝓞 K] m, (0 : K ⊗[𝓞 K] M₂)) = ((1 : K) ⊗ₜ m, (1 : K) ⊗ₜ (0 : M₂)) by
    rw [tmul_zero], prodRight_symm_tmul]
  simp [LinearEquiv.baseChange, AlgebraTensorModule.congr_tmul]

theorem sumIso_inr (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) (m : M₂) :
    sumIso j₁ j₂ hbij (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m := by
  simp only [sumIso, LinearEquiv.trans_apply]
  rw [show ((0 : K ⊗[𝓞 K] M₁), (1 : K) ⊗ₜ[𝓞 K] m) = ((1 : K) ⊗ₜ (0 : M₁), (1 : K) ⊗ₜ m) by
    rw [tmul_zero], prodRight_symm_tmul]
  simp [LinearEquiv.baseChange, AlgebraTensorModule.congr_tmul]

/-- The concatenated basis of `K ⊗ M`. -/
noncomputable def prodBasis {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) :
    Module.Basis (Fin (g₁ + g₂)) K (K ⊗[𝓞 K] M) :=
  ((b₁.prod b₂).map E).reindex finSumFinEquiv

theorem prodBasis_castAdd {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) (i : Fin g₁) :
    prodBasis b₁ b₂ E (Fin.castAdd g₂ i) = E (b₁ i, 0) := by
  simp [prodBasis, Module.Basis.prod_apply]

theorem prodBasis_natAdd {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M)) (i : Fin g₂) :
    prodBasis b₁ b₂ E (Fin.natAdd g₁ i) = E (0, b₂ i) := by
  simp [prodBasis, Module.Basis.prod_apply]

/-- **Block determinant.** -/
theorem det_prodBasis_append {g₁ g₂ : ℕ} (b₁ : Module.Basis (Fin g₁) K (K ⊗[𝓞 K] M₁))
    (b₂ : Module.Basis (Fin g₂) K (K ⊗[𝓞 K] M₂))
    (E : ((K ⊗[𝓞 K] M₁) × (K ⊗[𝓞 K] M₂)) ≃ₗ[K] (K ⊗[𝓞 K] M))
    (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hE1 : ∀ m, E ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m)
    (hE2 : ∀ m, E (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m)
    (u : Fin g₁ → M₁) (v : Fin g₂ → M₂) :
    (prodBasis b₁ b₂ E).det (fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ u) (j₂ ∘ v) k) =
      b₁.det (fun i => (1 : K) ⊗ₜ[𝓞 K] u i) * b₂.det (fun j => (1 : K) ⊗ₜ[𝓞 K] v j) := by
  have h1 : ∀ m, E.symm ((1 : K) ⊗ₜ[𝓞 K] j₁ m) = ((1 : K) ⊗ₜ m, 0) := fun m => by
    rw [LinearEquiv.symm_apply_eq, hE1]
  have h2 : ∀ m, E.symm ((1 : K) ⊗ₜ[𝓞 K] j₂ m) = (0, (1 : K) ⊗ₜ m) := fun m => by
    rw [LinearEquiv.symm_apply_eq, hE2]
  rw [prodBasis, Module.Basis.det_reindex, Module.Basis.det_map, Module.Basis.det_apply,
    Module.Basis.det_apply, Module.Basis.det_apply]
  have hM : (b₁.prod b₂).toMatrix (⇑E.symm ∘
      (fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ u) (j₂ ∘ v) k) ∘ ⇑finSumFinEquiv) =
      Matrix.fromBlocks (b₁.toMatrix (fun i => (1 : K) ⊗ₜ[𝓞 K] u i)) 0 0
        (b₂.toMatrix (fun j => (1 : K) ⊗ₜ[𝓞 K] v j)) := by
    ext (i | i) (j | j) <;>
      simp [Module.Basis.toMatrix_apply, Matrix.fromBlocks, h1, h2,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr]
  rw [hM, Matrix.det_fromBlocks_zero₂₁]

/-- A linearly independent family inside the range of a map from a space of dimension `n` has
at most `n` members. -/
theorem card_le_of_li_range {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] [FiniteDimensional K V] [FiniteDimensional K W] (J : V →ₗ[K] W) {ι : Type*}
    [Fintype ι] (F : ι → W) (hF : LinearIndependent K F) (hr : ∀ i, F i ∈ LinearMap.range J) :
    Fintype.card ι ≤ Module.finrank K V := by
  rw [linearIndependent_iff_card_eq_finrank_span.mp hF]
  calc Module.finrank K (Submodule.span K (Set.range F))
      ≤ Module.finrank K (LinearMap.range J) :=
        Submodule.finrank_mono (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hr i))
    _ ≤ _ := LinearMap.finrank_range_le J

end Prod

/-- **`DetLatticeProd`, proved** (the statement is the body of `ZInQ.UnifDims.DetLatticeProd`). -/
theorem detLatticeProd_aux :
  ∀ (K : Type) [Field K] [NumberField K] (M₁ M₂ M : Type) [AddCommGroup M₁] [Module (𝓞 K) M₁]
    [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M] [Module (𝓞 K) M]
    (ω₁ : Submodule (𝓞 K) M₁) (ω₂ : Submodule (𝓞 K) M₂) (j₁ : M₁ →ₗ[𝓞 K] M)
    (j₂ : M₂ →ₗ[𝓞 K] M) (g₁ g₂ : ℕ),
    Function.Bijective (LinearMap.coprod j₁ j₂) → ω₁.FG → ω₂.FG →
    Module.rank K (K ⊗[𝓞 K] M₁) = g₁ → Module.rank K (K ⊗[𝓞 K] M₂) = g₂ →
    Submodule.span K (Set.range fun x : ω₁ => (1 : K) ⊗ₜ[𝓞 K] (x : M₁)) = ⊤ →
    Submodule.span K (Set.range fun x : ω₂ => (1 : K) ⊗ₜ[𝓞 K] (x : M₂)) = ⊤ →
    ∃ (x₁ : Fin g₁ → M₁) (x₂ : Fin g₂ → M₂) (a₁ a₂ : K),
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ∈ detLat ω₁ g₁ ∧
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ≠ 0 ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ∈ detLat ω₂ g₂ ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ≠ 0 ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ∈ detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂) ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ≠ 0 ∧
      secIndex (detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂))
          ((a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
            (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)))) =
        secIndex (detLat ω₁ g₁) (a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁)) *
          secIndex (detLat ω₂ g₂) (a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂)) := by
  intro K _ _ M₁ M₂ M _ _ _ _ _ _ ω₁ ω₂ j₁ j₂ g₁ g₂ hbij hfg₁ hfg₂ hr₁ hr₂ hsp₁ hsp₂
  classical
  have : FiniteDimensional K (K ⊗[𝓞 K] M₁) := Module.finite_of_rank_eq_nat hr₁
  have : FiniteDimensional K (K ⊗[𝓞 K] M₂) := Module.finite_of_rank_eq_nat hr₂
  obtain ⟨w₁, b₁, hb₁⟩ := exists_basis_of_span ω₁ hr₁ hsp₁
  obtain ⟨w₂, b₂, hb₂⟩ := exists_basis_of_span ω₂ hr₂ hsp₂
  set E := sumIso (K := K) j₁ j₂ hbij
  have hE1 : ∀ m, E ((1 : K) ⊗ₜ[𝓞 K] m, 0) = (1 : K) ⊗ₜ[𝓞 K] j₁ m := sumIso_inl j₁ j₂ hbij
  have hE2 : ∀ m, E (0, (1 : K) ⊗ₜ[𝓞 K] m) = (1 : K) ⊗ₜ[𝓞 K] j₂ m := sumIso_inr j₁ j₂ hbij
  set b := prodBasis b₁ b₂ E
  have : FiniteDimensional K (K ⊗[𝓞 K] M) := Module.Basis.finiteDimensional_of_finite b
  set x₁ : Fin g₁ → M₁ := fun i => (w₁ i : M₁)
  set x₂ : Fin g₂ → M₂ := fun i => (w₂ i : M₂)
  set y : Fin (g₁ + g₂) → M := Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂) with hy
  have hb : ∀ k, (1 : K) ⊗ₜ[𝓞 K] y k = b k := by
    intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [prodBasis_castAdd, ← hb₁, hE1, hy, Fin.append_left]; rfl
    · rw [prodBasis_natAdd, ← hb₂, hE2, hy, Fin.append_right]; rfl
  set ω := ω₁.map j₁ ⊔ ω₂.map j₂ with hω
  have hi₁ := detFun_injective b₁ x₁ hb₁
  have hi₂ := detFun_injective b₂ x₂ hb₂
  have hi := detFun_injective b y hb
  set I₁ := (detLat ω₁ g₁).map ((detFun b₁).restrictScalars (𝓞 K)) with hI₁
  set I₂ := (detLat ω₂ g₂).map ((detFun b₂).restrictScalars (𝓞 K)) with hI₂
  set I := (detLat ω (g₁ + g₂)).map ((detFun b).restrictScalars (𝓞 K)) with hI
  have hblock := det_prodBasis_append b₁ b₂ E j₁ j₂ hE1 hE2
  have happ : ∀ (u : Fin g₁ → ω₁) (v : Fin g₂ → ω₂) (k : Fin (g₁ + g₂)),
      Fin.append (j₁ ∘ fun i => (u i : M₁)) (j₂ ∘ fun i => (v i : M₂)) k ∈ ω := by
    intro u v k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]
      exact Submodule.mem_sup_left (Submodule.mem_map_of_mem (u i).2)
    · rw [Fin.append_right]
      exact Submodule.mem_sup_right (Submodule.mem_map_of_mem (v i).2)
  have hgen₁ : ∀ u : Fin g₁ → ω₁, b₁.det (fun i => (1 : K) ⊗ₜ[𝓞 K] (u i : M₁)) ∈ I₁ := by
    intro u
    rw [← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, rfl⟩)
  have hgen₂ : ∀ u : Fin g₂ → ω₂, b₂.det (fun i => (1 : K) ⊗ₜ[𝓞 K] (u i : M₂)) ∈ I₂ := by
    intro u
    rw [← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨u, rfl⟩)
  have hge : I₁ * I₂ ≤ I := by
    rw [hI₁, hI₂, detLat, detLat, Submodule.map_span, Submodule.map_span, Submodule.span_mul_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, _, ⟨_, ⟨v, rfl⟩, rfl⟩, rfl⟩
    simp only [LinearMap.coe_restrictScalars]
    rw [detFun_tmul, detFun_tmul, ← hblock, ← detFun_tmul]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨fun k => ⟨_, happ u v k⟩, rfl⟩)
  have hle : I ≤ I₁ * I₂ := by
    rw [hI, detLat, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    have hdec : ∀ k, ∃ (a : ω₁) (c : ω₂), (v k : M) = j₁ a + j₂ c := fun k => by
      obtain ⟨y', hy', z, hz, hyz⟩ := Submodule.mem_sup.mp (v k).2
      obtain ⟨a, ha, rfl⟩ := hy'
      obtain ⟨c, hc, rfl⟩ := hz
      exact ⟨⟨a, ha⟩, ⟨c, hc⟩, hyz.symm⟩
    choose a c hac using hdec
    simp only [SetLike.mem_coe, LinearMap.coe_restrictScalars]
    rw [detFun_tmul]
    have hsplit : (fun k => (1 : K) ⊗ₜ[𝓞 K] (v k : M)) = fun k =>
        (1 : K) ⊗ₜ[𝓞 K] j₁ (a k) + (1 : K) ⊗ₜ[𝓞 K] j₂ (c k) := funext fun k => by
      rw [hac, tmul_add]
    rw [hsplit]
    have hexp := (b.det : (K ⊗[𝓞 K] M) [⋀^Fin (g₁ + g₂)]→ₗ[K] K).toMultilinearMap.map_add_univ
      (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k))
    simp only [AlternatingMap.coe_multilinearMap] at hexp
    rw [show (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k) + (1 : K) ⊗ₜ[𝓞 K] j₂ (c k)) =
      (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) + (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k)) from rfl, hexp]
    refine Submodule.sum_mem _ fun T _ => ?_
    set F := T.piecewise (fun k => (1 : K) ⊗ₜ[𝓞 K] j₁ (a k)) (fun k => (1 : K) ⊗ₜ[𝓞 K] j₂ (c k))
      with hF
    show b.det F ∈ _
    by_cases hT : T.card = g₁
    · have hTc : Tᶜ.card = g₂ := by rw [Finset.card_compl, Fintype.card_fin, hT]; omega
      let e1 := T.orderIsoOfFin hT
      let e2 := Tᶜ.orderIsoOfFin hTc
      let σ : Equiv.Perm (Fin (g₁ + g₂)) := finSumFinEquiv.symm.trans
        ((Equiv.sumCongr e1.toEquiv
          (e2.toEquiv.trans (Equiv.subtypeEquivRight (fun x => Finset.mem_compl)))).trans
          (Equiv.sumCompl (· ∈ T)))
      have hσ1 : ∀ i, σ (Fin.castAdd g₂ i) = (e1 i : Fin (g₁ + g₂)) := by
        intro i; simp [σ]
      have hσ2 : ∀ i, σ (Fin.natAdd g₁ i) = (e2 i : Fin (g₁ + g₂)) := by
        intro i; simp [σ]
      have hFσ : F ∘ σ = fun k => (1 : K) ⊗ₜ[𝓞 K] Fin.append (j₁ ∘ fun i => ((a (e1 i)) : M₁))
          (j₂ ∘ fun i => ((c (e2 i)) : M₂)) k := by
        funext k
        refine Fin.addCases (fun i => ?_) (fun i => ?_) k
        · rw [Function.comp_apply, hσ1, Fin.append_left, hF,
            Finset.piecewise_eq_of_mem _ _ _ (e1 i).2]
          rfl
        · rw [Function.comp_apply, hσ2, Fin.append_right, hF,
            Finset.piecewise_eq_of_notMem _ _ _ (Finset.mem_compl.mp (e2 i).2)]
          rfl
      have key : b.det F = (Equiv.Perm.sign σ) • b.det (F ∘ σ) := by
        rw [AlternatingMap.map_perm, smul_smul, Int.units_mul_self, one_smul]
      rw [key, hFσ, hblock]
      have hm := Submodule.mul_mem_mul (hgen₁ fun i => a (e1 i)) (hgen₂ fun i => c (e2 i))
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
      · rw [h, one_smul]; exact hm
      · rw [h, Units.neg_smul, one_smul]; exact neg_mem hm
    · have hnli : ¬ LinearIndependent K F := by
        intro hli
        have h1 : T.card ≤ g₁ := by
          have := card_le_of_li_range (E.toLinearMap ∘ₗ LinearMap.inl K _ _)
            (fun k : T => F k) (hli.comp _ Subtype.val_injective) (fun k =>
              ⟨(1 : K) ⊗ₜ[𝓞 K] (a k : M₁), by
                simp only [LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe, hE1]
                rw [hF, Finset.piecewise_eq_of_mem _ _ _ k.2]⟩)
          rwa [Fintype.card_coe, Module.finrank_eq_of_rank_eq hr₁] at this
        have h2 : Tᶜ.card ≤ g₂ := by
          have := card_le_of_li_range (E.toLinearMap ∘ₗ LinearMap.inr K _ _)
            (fun k : (Tᶜ : Finset _) => F k) (hli.comp _ Subtype.val_injective) (fun k =>
              ⟨(1 : K) ⊗ₜ[𝓞 K] (c k : M₂), by
                simp only [LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe, hE2]
                rw [hF, Finset.piecewise_eq_of_notMem _ _ _ (Finset.mem_compl.mp k.2)]⟩)
          rwa [Fintype.card_coe, Module.finrank_eq_of_rank_eq hr₂] at this
        have h3 : T.card + Tᶜ.card = g₁ + g₂ := by
          rw [Finset.card_add_card_compl, Fintype.card_fin]
        omega
      rw [b.det.map_linearDependent F hnli]
      exact Submodule.zero_mem _
  have hIP : I = I₁ * I₂ := le_antisymm hle hge
  have hΨ1 : detFun b₁ ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] x₁ k) = b₁ from funext hb₁,
      Module.Basis.det_self]
  have hΨ2 : detFun b₂ ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] x₂ k) = b₂ from funext hb₂,
      Module.Basis.det_self]
  have hΨ : detFun b ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂) y) = 1 := by
    rw [detFun_tmul, show (fun k => (1 : K) ⊗ₜ[𝓞 K] y k) = b from funext hb,
      Module.Basis.det_self]
  have hm₁ : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁ ∈ detLat ω₁ g₁ :=
    Submodule.subset_span ⟨w₁, rfl⟩
  have hm₂ : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂ ∈ detLat ω₂ g₂ :=
    Submodule.subset_span ⟨w₂, rfl⟩
  have hm : (1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂) y ∈ detLat ω (g₁ + g₂) :=
    Submodule.subset_span ⟨fun k => ⟨y k, happ w₁ w₂ k⟩, rfl⟩
  have h1I₁ : (1 : K) ∈ I₁ := hΨ1 ▸ Submodule.mem_map_of_mem hm₁
  have h1I₂ : (1 : K) ∈ I₂ := hΨ2 ▸ Submodule.mem_map_of_mem hm₂
  have hne : ∀ {V : Type} [AddCommGroup V] [Module K V] (Ψ : V →ₗ[K] K) (s : V), Ψ s = 1 →
      s ≠ 0 := fun Ψ s h hs => by rw [hs, map_zero] at h; exact zero_ne_one h
  refine ⟨x₁, x₂, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [one_smul]; exact hm₁
  · rw [one_smul]; exact hne _ _ hΨ1
  · rw [one_smul]; exact hm₂
  · rw [one_smul]; exact hne _ _ hΨ2
  · rw [mul_one, one_smul]; exact hm
  · rw [mul_one, one_smul]; exact hne _ _ hΨ
  · rw [mul_one, one_smul, one_smul, one_smul, secIndex_map _ hi, secIndex_map _ hi₁,
      secIndex_map _ hi₂, hΨ, hΨ1, hΨ2]
    change secIndex I 1 = secIndex I₁ 1 * secIndex I₂ 1
    rw [hIP]
    exact secIndex_one_mul I₁ I₂ ((detLat_fg ω₁ hfg₁ g₁).map _) ((detLat_fg ω₂ hfg₂ g₂).map _)
      h1I₁ h1I₂

end ZInQ.UnifDims


/-! ## unif-dims: metrization's `ProductHodgeLattice` reduced

`ProductHodgeLattice` (metrization's glue, copied verbatim above) follows from:
* `ProductCotangent` (new glue, algebraic geometry; proved below as `productCotangent`): the
  cotangent space at the generic unit of a product model is the direct sum of the factors' cotangent spaces, through the pull-backs of germs
  along the two projections, and the conormal lattice `ω` of the product is the sum of the two
  pulled-back lattices;
* `DetLatticeProd` (new glue, pure commutative algebra over `𝓞_K`, no geometry; proved below as
  `detLatticeProd`): for a direct sum of two modules with full lattices `ω₁, ω₂` of ranks `g₁, g₂`,
  the determinant lattice of `ω₁ ⊕ ω₂` has particular sections `s₁, s₂, s = s₁ ∧ s₂` with
  `[⋀ω : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`;
* the kernel's `HodgeLattice.CotangentRank` (already reduced by hodge-lattice to
  `TangentDimAtOrigin`, with `DimBaseChange` proved below from g0-dim);
* `AnalyticUniformizationOfDim` (from T35), only to know `gᵢ = dim` for the metrizations `Mᵢ`.
The kernel's `omegaLocal` (proved) supplies finiteness and fullness of each `ω`. -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice TensorProduct

/-- **Glue (algebraic geometry: the cotangent space and conormal lattice of a product model).**
Let `e : 𝒢P ≅ 𝒢₁ ×_{𝓞_L} 𝒢₂` have homomorphic components `pᵢ`. There are `𝓞_L`-linear maps
`jᵢ : 𝔪ᵢ/𝔪ᵢ² → 𝔪_P/𝔪_P²` (at the generic units `ξ`) such that
* `jᵢ(df) = d(pᵢ* f)` for every germ `f ∈ 𝔪ᵢ` (in particular `pᵢ* f ∈ 𝔪_P`), where `pᵢ*` is
  metrization's `pullGerm`;
* `(x, y) ↦ j₁ x + j₂ y` is bijective;
* `ω_{𝒢P} = j₁(ω_{𝒢₁}) + j₂(ω_{𝒢₂})`.
Why true (STANDARD). `𝒪_{𝒢P,ξ}` is the local ring of `A_L ×_L B_L` at the origin, a localization
of `𝒪_{A_L,0} ⊗_L 𝒪_{B_L,0}`, and `𝔪/𝔪²` of a product of `L`-rational points is the direct sum
(`Ω_{X ×_S Y/S} = p₁*Ω_{X/S} ⊕ p₂*Ω_{Y/S}`; EGA IV 16.4.23 / Stacks, differentials of a fibre
product, UNVERIFIED locators). For the lattices: at every point `s` of `Spec 𝓞_L`, the ideal of the
unit section of `𝒢₁ ×_S 𝒢₂` at `e(s)` is generated by `p₁*I₁ + p₂*I₂` (the section is the
product of the two sections), so `(ω_P)_s = j₁(ω₁)_s ⊕ j₂(ω₂)_s`, and intersecting over `s` in the
direct sum gives the claim. `jᵢ` is `𝓞_L`-linear because `pᵢ` lies over `Spec 𝓞_L`. Proved:
`productCotangent` (`PC.lean`, with infra-stalks' stalk lemmas for fibre products). -/
def ProductCotangent : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    ∃ (j₁ : 𝒢₁.cotangent →ₗ[𝓞 L] 𝒢P.cotangent) (j₂ : 𝒢₂.cotangent →ₗ[𝓞 L] 𝒢P.cotangent),
      (∀ f : IsLocalRing.maximalIdeal 𝒢₁.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ fst _ _)).hom (f : 𝒢₁.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₁ (𝒢₁.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      (∀ f : IsLocalRing.maximalIdeal 𝒢₂.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ snd _ _)).hom (f : 𝒢₂.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₂ (𝒢₂.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      Function.Bijective (LinearMap.coprod j₁ j₂) ∧
      𝒢P.omega = 𝒢₁.omega.map j₁ ⊔ 𝒢₂.omega.map j₂

/-- **Glue (commutative algebra: the determinant lattice of a direct sum).** Let `K` be a number
field, `M₁, M₂, M` modules over `𝓞_K` with `M₁ × M₂ ≅ M` through `(x, y) ↦ j₁ x + j₂ y`, and
`ωᵢ ⊆ Mᵢ` finitely generated submodules spanning `K ⊗ Mᵢ`, which has `K`-rank `gᵢ`. Put
`ω = j₁ω₁ + j₂ω₂`. Then there are `xᵢ ∈ Mᵢ^{gᵢ}` and `aᵢ ∈ K` such that `sᵢ = aᵢ · 1 ⊗ ∧xᵢ` is a
nonzero element of `detLat ωᵢ gᵢ`, `s = a₁a₂ · 1 ⊗ ∧(j₁x₁, j₂x₂)` is a nonzero element of
`detLat ω (g₁+g₂)`, and `[detLat ω : 𝓞s] = [detLat ω₁ : 𝓞s₁]·[detLat ω₂ : 𝓞s₂]`.
Why true (STANDARD). `K ⊗ M = (K ⊗ M₁) ⊕ (K ⊗ M₂)` and the images `Ω̄ᵢ` of `ωᵢ` are full
`𝓞_K`-lattices (projective of rank `gᵢ`); `K ⊗ ⋀^{g₁+g₂} M = ⋀^{g₁}(K⊗M₁) ⊗ ⋀^{g₂}(K⊗M₂)` and
`det(Ω̄₁ ⊕ Ω̄₂) = det Ω̄₁ ⊗ det Ω̄₂` (Bourbaki, Algèbre III §7, UNVERIFIED locator; in coordinates,
generalized Laplace expansion along the first `g₁` columns). Identifying the lines with `K`, the
lattices become fractional ideals `I₁, I₂, I₁I₂`, and the indices multiply because
`[I : 𝓞x] = |N(x)| / N(I)` (the kernel's `secIndex_mul_absNorm`) and both norms are
multiplicative. Take `xᵢ` an `𝓞_K`-family in `ωᵢ` forming a `K`-basis and `aᵢ = 1`. Proved:
`detLatticeProd` (`DetProd.lean`). -/
def DetLatticeProd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (M₁ M₂ M : Type) [AddCommGroup M₁] [Module (𝓞 K) M₁]
    [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M] [Module (𝓞 K) M]
    (ω₁ : Submodule (𝓞 K) M₁) (ω₂ : Submodule (𝓞 K) M₂) (j₁ : M₁ →ₗ[𝓞 K] M)
    (j₂ : M₂ →ₗ[𝓞 K] M) (g₁ g₂ : ℕ),
    Function.Bijective (LinearMap.coprod j₁ j₂) → ω₁.FG → ω₂.FG →
    Module.rank K (K ⊗[𝓞 K] M₁) = g₁ → Module.rank K (K ⊗[𝓞 K] M₂) = g₂ →
    Submodule.span K (Set.range fun x : ω₁ => (1 : K) ⊗ₜ[𝓞 K] (x : M₁)) = ⊤ →
    Submodule.span K (Set.range fun x : ω₂ => (1 : K) ⊗ₜ[𝓞 K] (x : M₂)) = ⊤ →
    ∃ (x₁ : Fin g₁ → M₁) (x₂ : Fin g₂ → M₂) (a₁ a₂ : K),
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ∈ detLat ω₁ g₁ ∧
      a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁) ≠ 0 ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ∈ detLat ω₂ g₂ ∧
      a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂) ≠ 0 ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ∈ detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂) ∧
      (a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
        (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂))) ≠ 0 ∧
      secIndex (detLat (ω₁.map j₁ ⊔ ω₂.map j₂) (g₁ + g₂))
          ((a₁ * a₂) • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) (g₁ + g₂)
            (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)))) =
        secIndex (detLat ω₁ g₁) (a₁ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₁ x₁)) *
          secIndex (detLat ω₂ g₂) (a₂ • ((1 : K) ⊗ₜ[𝓞 K] exteriorPower.ιMulti (𝓞 K) g₂ x₂))

/-- hodge-lattice's `DimBaseChange`, proved (g0-dim's `G0Dim.dim_baseChange`). -/
theorem dimBaseChange : DimBaseChange := fun _ _ A L _ _ =>
  G0Dim.dim_baseChange L A.X.left A.X.hom

/-- `K ⊗ -` turns a direct sum decomposition into a sum of ranks. -/
theorem rank_tensor_of_bijective {K : Type} [Field K] [NumberField K] {M₁ M₂ M : Type}
    [AddCommGroup M₁] [Module (𝓞 K) M₁] [AddCommGroup M₂] [Module (𝓞 K) M₂] [AddCommGroup M]
    [Module (𝓞 K) M] (j₁ : M₁ →ₗ[𝓞 K] M) (j₂ : M₂ →ₗ[𝓞 K] M)
    (hbij : Function.Bijective (LinearMap.coprod j₁ j₂)) {g₁ g₂ : ℕ}
    (h₁ : Module.rank K (K ⊗[𝓞 K] M₁) = g₁) (h₂ : Module.rank K (K ⊗[𝓞 K] M₂) = g₂) :
    Module.rank K (K ⊗[𝓞 K] M) = ((g₁ + g₂ : ℕ) : Cardinal) := by
  let E : (M₁ × M₂) ≃ₗ[𝓞 K] M := LinearEquiv.ofBijective _ hbij
  rw [← (LinearEquiv.baseChange (𝓞 K) K _ _ E).rank_eq,
    (TensorProduct.prodRight (𝓞 K) K K M₁ M₂).rank_eq, rank_prod', h₁, h₂]
  push_cast
  rfl

/-- **`ProductHodgeLattice` from `ProductCotangent`, `DetLatticeProd`, `CotangentRank` and
`AnalyticUniformizationOfDim` (proved).** -/
theorem productHodgeLattice_of (hPC : ProductCotangent) (hDL : DetLatticeProd)
    (hCR : CotangentRank) (hU : ZInQ.Metrization.AnalyticUniformizationOfDim) :
    ZInQ.Metrization.ProductHodgeLattice := by
  intro K _ A B C L _ _ _ 𝒢P g₁ g₂ M₁ M₂ e hfst hsnd
  obtain ⟨j₁, j₂, hc₁, hc₂, hbij, hom⟩ := hPC K A B C L 𝒢P M₁.model M₂.model e hfst hsnd
  obtain ⟨τ⟩ := (inferInstance : Nonempty (L →+* ℂ))
  have hg : ∀ {X : AbVar K} {g : ℕ} (M : MetrizedModel X L g), X.dim = (g : WithBot ℕ∞) := by
    intro X g M
    obtain ⟨Φ, hΦ, -⟩ := M.arch τ
    exact dim_eq_of_isAnalyticUniformization hU M.model τ _ Φ (M.hodge.periods_discrete τ)
      (M.hodge.periods_isZLattice τ) hΦ
  have hr₁ := hCR K A L M₁.model g₁ (hg M₁)
  have hr₂ := hCR K B L M₂.model g₂ (hg M₂)
  have hfg : ∀ {X : AbVar K} (𝒢 : GroupModel X L), 𝒢.omega.FG := fun 𝒢 =>
    omegaFG_of_omegaLocal omegaLocal K _ L 𝒢
  have hsp : ∀ {X : AbVar K} (𝒢 : GroupModel X L), Submodule.span L
      (Set.range fun x : 𝒢.omega => (1 : L) ⊗ₜ[𝓞 L] (x : 𝒢.cotangent)) = ⊤ := fun 𝒢 =>
    omegaSpans_of_omegaLocal omegaLocal K _ L 𝒢
  have hrP := rank_tensor_of_bijective j₁ j₂ hbij hr₁ hr₂
  refine ⟨(hodgeLattice_of_lattice 𝒢P.omega (hfg 𝒢P) hrP (hsp 𝒢P)).1, ?_⟩
  obtain ⟨x₁, x₂, a₁, a₂, h₁, h₁', h₂, h₂', hP, hP', hidx⟩ :=
    hDL L M₁.model.cotangent M₂.model.cotangent 𝒢P.cotangent M₁.model.omega M₂.model.omega
      j₁ j₂ g₁ g₂ hbij (hfg _) (hfg _) hr₁ hr₂ (hsp _) (hsp _)
  choose f₁ hf₁ using fun i => (IsLocalRing.maximalIdeal M₁.model.genStalk).toCotangent_surjective
    (x₁ i)
  choose f₂ hf₂ using fun i => (IsLocalRing.maximalIdeal M₂.model.genStalk).toCotangent_surjective
    (x₂ i)
  choose m₁ hm₁ using fun i => hc₁ (f₁ i)
  choose m₂ hm₂ using fun i => hc₂ (f₂ i)
  let f : Fin (g₁ + g₂) → IsLocalRing.maximalIdeal 𝒢P.genStalk :=
    Fin.append (fun i => ⟨_, m₁ i⟩) (fun j => ⟨_, m₂ j⟩)
  have hw₁ : M₁.model.wedge f₁ = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g₁ x₁ := by
    unfold GroupModel.wedge
    congr 2
    funext i
    exact hf₁ i
  have hw₂ : M₂.model.wedge f₂ = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) g₂ x₂ := by
    unfold GroupModel.wedge
    congr 2
    funext i
    exact hf₂ i
  have hw : 𝒢P.wedge f = (1 : L) ⊗ₜ[𝓞 L] exteriorPower.ιMulti (𝓞 L) (g₁ + g₂)
      (Fin.append (j₁ ∘ x₁) (j₂ ∘ x₂)) := by
    unfold GroupModel.wedge
    congr 2
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [f, Fin.append_left, Function.comp_apply]
      rw [← hm₁ i, ← hf₁ i]
      rfl
    · simp only [f, Fin.append_right, Function.comp_apply]
      rw [← hm₂ j, ← hf₂ j]
      rfl
  have hL₁ : M₁.hodge.lattice = detLat M₁.model.omega g₁ := M₁.lattice_eq
  have hL₂ : M₂.hodge.lattice = detLat M₂.model.omega g₂ := M₂.lattice_eq
  have hLP : 𝒢P.detLattice (g₁ + g₂) =
      detLat (M₁.model.omega.map j₁ ⊔ M₂.model.omega.map j₂) (g₁ + g₂) := by
    rw [detLattice_eq, hom]
  refine ⟨f₁, f₂, f, a₁, a₂, fun i => ?_, fun j => ?_, ?_⟩
  · simp only [f, Fin.append_left]
  · simp only [f, Fin.append_right]
  rw [hw₁, hw₂, hw, hL₁, hL₂, hLP]
  exact ⟨h₁, h₁', h₂, h₂', hP, hP', hidx⟩

/-- **`ProductHodgeLattice` from `ProductCotangent`, `DetLatticeProd`, hodge-lattice's
`TangentDimAtOrigin` and T35 (proved).** -/
theorem productHodgeLattice_of_tangent (hPC : ProductCotangent) (hDL : DetLatticeProd)
    (hT : TangentDimAtOrigin) (hT35 : ZInQ.LeafPush2.UniformizationExists) :
    ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of hPC hDL
    (cotangentRank_of_tangentDim (tangentDim_of_abVar hT dimBaseChange))
    (ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35)

end ZInQ.UnifDims




/-! ## unif-dims: `DetLatticeProd` closed; `ProductHodgeLattice` from `ProductCotangent`,
`TangentDimAtOrigin` and T35 -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- **`DetLatticeProd`, proved** (`detLatticeProd_aux`, `DetProd.lean`). -/
theorem detLatticeProd : DetLatticeProd := detLatticeProd_aux

/-- **`ProductHodgeLattice` from `ProductCotangent`, hodge-lattice's `TangentDimAtOrigin` and T35
(proved).** -/
theorem productHodgeLattice_of_cotangent (hPC : ProductCotangent) (hT : TangentDimAtOrigin)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of_tangent hPC detLatticeProd hT hT35

end ZInQ.UnifDims




/-! ## unif-dims: S-alg and P2 from T35, `ProductCotangent` and `TangentDimAtOrigin` -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice

/-- **S-alg (`ProductMetrizationOfProductUnif`) from T35, `ProductCotangent` and
`TangentDimAtOrigin` (proved).** product-unif's `productMetrizationOfProductUnif_of_local` with
`HodgeLatticeTheorem` from hodge-lattice (`TangentDimAtOrigin`, `DimBaseChange` proved here),
`ProductUnifDims` from T35, metrization2's `productLocalStructure`, and `ProductHodgeLattice`
from `ProductCotangent`. -/
theorem productMetrizationOfProductUnif_of_cotangent (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hPC : ProductCotangent) (hT : TangentDimAtOrigin) :
    ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  ZInQ.ProductUnif.productMetrizationOfProductUnif_of_local
    (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
    (productUnifDims_of_uniformizationExists hT35)
    ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of_cotangent hPC hT hT35)

/-- **Glue piece 5 of `GluePieces` (P2, `ProductModelHeight`) from T35, `ProductCotangent` and
`TangentDimAtOrigin` (proved).** -/
theorem productModelHeight_of_cotangent (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hPC : ProductCotangent) (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  ZInQ.ProductUnif.productModelHeight_of_local (hodgeLatticeTheorem_of_tangent hT dimBaseChange)
    (productUnifDims_of_uniformizationExists hT35) ZInQ.Metrization2.productLocalStructure
    (productHodgeLattice_of_cotangent hPC hT hT35)

end ZInQ.UnifDims



open CategoryTheory Limits

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

variable {K : Type} [Field K] {L : Type} [Field L] [NumberField L] [Algebra K L]

section CotMap

variable {A C : AbVar K} (𝒢 : GroupModel C L) (ℋ : GroupModel A L)

/-- The stalk map at the generic units of a morphism of models preserving them. -/
noncomputable abbrev germMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.genStalk →+* 𝒢.genStalk :=
  (φ.left.stalkMapAt h).hom

/-- A morphism of models over `Spec 𝓞_L` is compatible with the structure maps. -/
theorem germMap_structMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (c : 𝓞 L) : germMap 𝒢 ℋ φ h (ℋ.structMap c) = 𝒢.structMap c := by
  rw [HodgeLattice.structMap_eq, HodgeLattice.structMap_eq, germMap,
    Scheme.Hom.stalkMapAt_germ_top]
  congr 1
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Over.w φ]

/-- **The cotangent map** `cot_ℋ → cot_𝒢`, `df ↦ d(φ* f)`. -/
noncomputable def cotMap (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.cotangent →ₗ[𝓞 L] 𝒢.cotangent := by
  let ρ := germMap 𝒢 ℋ φ h
  letI : Module ℋ.genStalk 𝒢.cotangent := Module.compHom _ ρ
  let f : IsLocalRing.maximalIdeal ℋ.genStalk →ₗ[ℋ.genStalk] 𝒢.cotangent :=
    { toFun := fun x => 𝒢.dCls ⟨ρ x, map_nonunit ρ _ x.2⟩
      map_add' := fun x y => by
        simp only [GroupModel.dCls]
        have e : (⟨ρ ↑(x + y), map_nonunit ρ _ (x + y).2⟩ :
            IsLocalRing.maximalIdeal 𝒢.genStalk) =
            (⟨ρ x, map_nonunit ρ _ x.2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) +
              ⟨ρ y, map_nonunit ρ _ y.2⟩ := Subtype.ext (by simp)
        refine (congrArg (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent e).trans ?_
        exact LinearMap.map_add _ _ _
      map_smul' := fun r x => by
        simp only [GroupModel.dCls, RingHom.id_apply]
        have e : (⟨ρ ↑(r • x), map_nonunit ρ _ (r • x).2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) =
            ρ r • (⟨ρ x, map_nonunit ρ _ x.2⟩ : IsLocalRing.maximalIdeal 𝒢.genStalk) :=
          Subtype.ext (by simp [ρ])
        refine (congrArg (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent e).trans ?_
        exact LinearMap.map_smul _ _ _ }
  let j0 : ℋ.cotangent →ₗ[ℋ.genStalk] 𝒢.cotangent := Ideal.Cotangent.lift f (fun x y => by
    refine (Ideal.toCotangent_eq_zero _ _).mpr ?_
    show ρ (↑x * ↑y) ∈ _
    rw [map_mul, pow_two]
    exact Ideal.mul_mem_mul (map_nonunit ρ _ x.2) (map_nonunit ρ _ y.2))
  exact
    { toFun := j0
      map_add' := j0.map_add
      map_smul' := fun c x => by
        show j0 (ℋ.structMap c • x) = 𝒢.structMap c • j0 x
        rw [j0.map_smul]
        show ρ (ℋ.structMap c) • j0 x = _
        rw [germMap_structMap] }

theorem cotMap_dCls (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (f : IsLocalRing.maximalIdeal ℋ.genStalk) :
    cotMap 𝒢 ℋ φ h (ℋ.dCls f) =
      𝒢.dCls ⟨germMap 𝒢 ℋ φ h f, map_nonunit (germMap 𝒢 ℋ φ h) _ f.2⟩ := by
  rfl


theorem cotMap_comp {B : AbVar K} (𝒦 : GroupModel B L) (φ : 𝒢.G ⟶ ℋ.G) (ψ : ℋ.G ⟶ 𝒦.G)
    (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) (h' : ψ.left ℋ.genericUnit = 𝒦.genericUnit)
    (h'' : (φ ≫ ψ).left 𝒢.genericUnit = 𝒦.genericUnit) :
    cotMap 𝒢 𝒦 (φ ≫ ψ) h'' = cotMap 𝒢 ℋ φ h ∘ₗ cotMap ℋ 𝒦 ψ h' := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒦.genStalk).toCotangent_surjective x
  change cotMap 𝒢 𝒦 (φ ≫ ψ) h'' (𝒦.dCls f) = cotMap 𝒢 ℋ φ h (cotMap ℋ 𝒦 ψ h' (𝒦.dCls f))
  rw [cotMap_dCls, cotMap_dCls, cotMap_dCls]
  congr 2
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ φ ψ) h'' (by rw [← h', ← h]; rfl),
    Scheme.Hom.stalkMapAt_comp φ.left ψ.left h h']
  rfl

theorem cotMap_id (h : (𝟙 𝒢.G : 𝒢.G ⟶ 𝒢.G).left 𝒢.genericUnit = 𝒢.genericUnit) :
    cotMap 𝒢 𝒢 (𝟙 𝒢.G) h = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢.genStalk).toCotangent_surjective x
  change cotMap 𝒢 𝒢 (𝟙 𝒢.G) h (𝒢.dCls f) = 𝒢.dCls f
  rw [cotMap_dCls]
  congr 2
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr (Over.id_left 𝒢.G) h h, Scheme.Hom.stalkMapAt_id]
  rfl

/-- A morphism of models preserving the unit sections maps every `e(s)` to `e(s)`. -/
theorem map_unitSection (φ : 𝒢.G ⟶ ℋ.G) (hφ : η[𝒢.G] ≫ φ = η[ℋ.G])
    (s : Spec (CommRingCat.of (𝓞 L))) : φ.left (𝒢.unitSection s) = ℋ.unitSection s := by
  have h2 : 𝒢.unitSection ≫ φ.left = ℋ.unitSection := by
    unfold GroupModel.unitSection
    rw [← Over.comp_left, hφ]
  rw [← h2]
  rfl

/-- **Functoriality of `ω`.** A morphism of models preserving the unit sections maps
`ω_ℋ` into `ω_𝒢` under the cotangent map. -/
theorem omega_map_le (φ : 𝒢.G ⟶ ℋ.G) (hφ : η[𝒢.G] ≫ φ = η[ℋ.G])
    (h : φ.left 𝒢.genericUnit = ℋ.genericUnit) :
    ℋ.omega.map (cotMap 𝒢 ℋ φ h) ≤ 𝒢.omega := by
  refine le_iInf fun s => (Submodule.map_mono (iInf_le _ s)).trans ?_
  rw [GroupModel.omegaAt, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨f, hf, hfm, rfl⟩, rfl⟩
  have hs := map_unitSection 𝒢 ℋ φ hφ s
  set f' := (φ.left.stalkMapAt hs).hom f with hf'
  have h2 : 𝒢.unitSection ≫ φ.left = ℋ.unitSection := by
    unfold GroupModel.unitSection
    rw [← Over.comp_left, hφ]
  have hker : f' ∈ RingHom.ker (𝒢.unitSection.stalkMap s).hom := by
    rw [RingHom.mem_ker] at hf ⊢
    have e1 := Scheme.Hom.stalkMapAt_comp 𝒢.unitSection φ.left (rfl : 𝒢.unitSection s = _) hs
      (by rw [← hs]; rfl)
    rw [Scheme.Hom.stalkMapAt_congr h2 _ rfl, Scheme.Hom.stalkMapAt_rfl,
      Scheme.Hom.stalkMapAt_rfl] at e1
    rw [hf', ← CommRingCat.comp_apply, ← e1, hf]
  have hspec : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f' =
      germMap 𝒢 ℋ φ h (ℋ.G.left.presheaf.stalkSpecializes (ℋ.specializes_genericUnit s) f) :=
    Scheme.Hom.stalkMapAt_stalkSpecializes φ.left _ _ h hs f
  have hm : 𝒢.G.left.presheaf.stalkSpecializes (𝒢.specializes_genericUnit s) f' ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk := by
    rw [hspec]; exact map_nonunit (germMap 𝒢 ℋ φ h) _ hfm
  apply Submodule.subset_span
  refine ⟨f', hker, hm, ?_⟩
  rw [cotMap_dCls]
  congr 2
  exact hspec.symm

theorem cotMap_congr {φ φ' : 𝒢.G ⟶ ℋ.G} (e : φ = φ') (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (h' : φ'.left 𝒢.genericUnit = ℋ.genericUnit) : cotMap 𝒢 ℋ φ h = cotMap 𝒢 ℋ φ' h' := by
  subst e; rfl

end CotMap

section Helpers

variable {X : AbVar K} (𝒢 : GroupModel X L)

/-- The unit section is a section of the structure morphism (copied from infra-stalks). -/
theorem unitSection_comp_hom : 𝒢.unitSection ≫ 𝒢.G.hom = 𝟙 _ := by
  unfold GroupModel.unitSection
  simpa using Over.w η[𝒢.G]

theorem hom_genericUnit : 𝒢.G.hom 𝒢.genericUnit = genericPt L := by
  unfold GroupModel.genericUnit
  rw [← Scheme.Hom.comp_apply, unitSection_comp_hom]
  rfl

theorem rationalOver_genericUnit : RationalOver 𝒢.G.hom 𝒢.genericUnit :=
  rationalOver_of_section _ _ (unitSection_comp_hom 𝒢) (genericPt L)

omit [Algebra K L] in
/-- The stalk of `Spec 𝓞_L` at its generic point is a field (copied from infra-stalks). -/
theorem maximalIdeal_stalk_genericPt :
    IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (𝓞 L))).presheaf.stalk (genericPt L)) = ⊥ := by
  have h : genericPt L = genericPoint (Spec (CommRingCat.of (𝓞 L))) := by
    rw [genericPoint_eq_bot_of_affine]; rfl
  refine (IsLocalRing.isField_iff_maximalIdeal_eq).mp ?_
  rw [h]
  exact Field.toIsField (Spec (CommRingCat.of (𝓞 L))).functionField

end Helpers

section Trivial

variable {A C : AbVar K} (𝒢 : GroupModel C L) (ℋ : GroupModel A L)

/-- A morphism of models that factors through `Spec 𝓞_L` kills `𝔪` at the generic units. -/
theorem germMap_eq_zero_of_factor (φ : 𝒢.G ⟶ ℋ.G) (h : φ.left 𝒢.genericUnit = ℋ.genericUnit)
    (b : Spec (CommRingCat.of (𝓞 L)) ⟶ ℋ.G.left) (hφ : φ.left = 𝒢.G.hom ≫ b)
    (a : ℋ.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal ℋ.genStalk) : germMap 𝒢 ℋ φ h a = 0 := by
  have h1 : 𝒢.G.hom 𝒢.genericUnit = genericPt L := hom_genericUnit 𝒢
  have h2 : b (genericPt L) = ℋ.genericUnit := by
    rw [← h, hφ, Scheme.Hom.comp_apply, h1]
  simp only [germMap]
  rw [Scheme.Hom.stalkMapAt_congr hφ h (by rw [Scheme.Hom.comp_apply, h1, h2]),
    Scheme.Hom.stalkMapAt_comp 𝒢.G.hom b h1 h2]
  have hz : (b.stalkMapAt h2).hom a = 0 := by
    have hm := map_nonunit (b.stalkMapAt h2).hom a ha
    rw [maximalIdeal_stalk_genericPt] at hm
    exact (Submodule.mem_bot _).mp hm
  rw [CommRingCat.comp_apply, hz, map_zero]

end Trivial

section Product

variable {A B C : AbVar K} (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]

/-- `x ↦ (x, 1)`. -/
noncomputable def inc₁ : 𝒢₁.G ⟶ 𝒢P.G := lift (𝟙 _) (toUnit _ ≫ η[𝒢₂.G]) ≫ e.inv

/-- `y ↦ (1, y)`. -/
noncomputable def inc₂ : 𝒢₂.G ⟶ 𝒢P.G := lift (toUnit _ ≫ η[𝒢₁.G]) (𝟙 _) ≫ e.inv

theorem eta_e : η[𝒢P.G] ≫ e.hom = lift η[𝒢₁.G] η[𝒢₂.G] := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, IsMonHom.one_hom, lift_fst]
  · rw [Category.assoc, IsMonHom.one_hom, lift_snd]

theorem eta_inc₁ : η[𝒢₁.G] ≫ inc₁ 𝒢P 𝒢₁ 𝒢₂ e = η[𝒢P.G] := by
  rw [inc₁, ← Category.assoc, Iso.comp_inv_eq, eta_e]
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem eta_inc₂ : η[𝒢₂.G] ≫ inc₂ 𝒢P 𝒢₁ 𝒢₂ e = η[𝒢P.G] := by
  rw [inc₂, ← Category.assoc, Iso.comp_inv_eq, eta_e]
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem inc₁_p₁ : inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _) = 𝟙 _ := by simp [inc₁]
theorem inc₁_p₂ : inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _) = toUnit _ ≫ η[𝒢₂.G] := by simp [inc₁]
theorem inc₂_p₁ : inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _) = toUnit _ ≫ η[𝒢₁.G] := by simp [inc₂]
theorem inc₂_p₂ : inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _) = 𝟙 _ := by simp [inc₂]

theorem toUnit_eta_left {X Y : AbVar K} (𝒳 : GroupModel X L) (𝒴 : GroupModel Y L) :
    (toUnit 𝒳.G ≫ η[𝒴.G]).left = 𝒳.G.hom ≫ 𝒴.unitSection := rfl

theorem hp₁ : (e.hom ≫ fst _ _).left 𝒢P.genericUnit = 𝒢₁.genericUnit :=
  map_unitSection 𝒢P 𝒢₁ _ (IsMonHom.one_hom _) (genericPt L)
theorem hp₂ : (e.hom ≫ snd _ _).left 𝒢P.genericUnit = 𝒢₂.genericUnit :=
  map_unitSection 𝒢P 𝒢₂ _ (IsMonHom.one_hom _) (genericPt L)
theorem hi₁ : (inc₁ 𝒢P 𝒢₁ 𝒢₂ e).left 𝒢₁.genericUnit = 𝒢P.genericUnit :=
  map_unitSection 𝒢₁ 𝒢P _ (eta_inc₁ 𝒢P 𝒢₁ 𝒢₂ e) (genericPt L)
theorem hi₂ : (inc₂ 𝒢P 𝒢₁ 𝒢₂ e).left 𝒢₂.genericUnit = 𝒢P.genericUnit :=
  map_unitSection 𝒢₂ 𝒢P _ (eta_inc₂ 𝒢P 𝒢₁ 𝒢₂ e) (genericPt L)

/-- A retraction on stalks. -/
theorem retract_apply {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) {x : X}
    {y : Y} (hf : f x = y) (hg : g y = x) (a : X.presheaf.stalk x) :
    (f.stalkMapAt hf).hom ((g.stalkMapAt hg).hom a) = a := by
  subst hf
  have h1 : (f ≫ g).stalkMapAt hg = g.stalkMapAt hg ≫ f.stalkMapAt rfl :=
    Scheme.Hom.stalkMapAt_comp f g rfl hg hg
  rw [← CommRingCat.comp_apply, ← h1]
  have key : ∀ (k : X ⟶ X) (_ : k = 𝟙 X) (h : k x = x), (k.stalkMapAt h).hom a = a := by
    intro k hk h; subst hk; rw [Scheme.Hom.stalkMapAt_id]; rfl
  exact key _ hfg hg

/-- germ-level retraction identities -/
theorem germ_retract₁ (a : 𝒢₁.genStalk) :
    germMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) a) = a :=
  retract_apply _ _ (by rw [← Over.comp_left, inc₁_p₁]; rfl) _ _ a

theorem germ_retract₂ (a : 𝒢₂.genStalk) :
    germMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) a) = a :=
  retract_apply _ _ (by rw [← Over.comp_left, inc₂_p₂]; rfl) _ _ a

theorem germ_cross₁₂ (a : 𝒢₂.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal 𝒢₂.genStalk) :
    germMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) a) = 0 := by
  have hc : (inc₁ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ snd _ _)).left 𝒢₁.genericUnit = 𝒢₂.genericUnit := by
    rw [Over.comp_left, Scheme.Hom.comp_apply, hi₁, hp₂]
  have := germMap_eq_zero_of_factor 𝒢₁ 𝒢₂ _ hc 𝒢₂.unitSection
    (by rw [inc₁_p₂]; rfl) a ha
  simp only [germMap] at this ⊢
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ _ _) hc
    (by rw [Scheme.Hom.comp_apply, hi₁, hp₂]),
    Scheme.Hom.stalkMapAt_comp _ _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)] at this
  exact this

theorem germ_cross₂₁ (a : 𝒢₁.genStalk) (ha : a ∈ IsLocalRing.maximalIdeal 𝒢₁.genStalk) :
    germMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) a) = 0 := by
  have hc : (inc₂ 𝒢P 𝒢₁ 𝒢₂ e ≫ (e.hom ≫ fst _ _)).left 𝒢₂.genericUnit = 𝒢₁.genericUnit := by
    rw [Over.comp_left, Scheme.Hom.comp_apply, hi₂, hp₁]
  have := germMap_eq_zero_of_factor 𝒢₂ 𝒢₁ _ hc 𝒢₁.unitSection
    (by rw [inc₂_p₁]; rfl) a ha
  simp only [germMap] at this ⊢
  rw [Scheme.Hom.stalkMapAt_congr (Over.comp_left _ _ _ _ _) hc
    (by rw [Scheme.Hom.comp_apply, hi₂, hp₁]),
    Scheme.Hom.stalkMapAt_comp _ _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)] at this
  exact this

end Product


section ProductCot

variable {A B C : AbVar K} (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
  (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]

/-- **The generic stalk of a product, modulo `𝔪²`.** For `m ∈ 𝔪_P`:
`m ≡ p₁*(i₁* m) + p₂*(i₂* m) (mod 𝔪_P²)` (infra-stalks' `pullback_stalkGen`,
`maximalIdeal_eq_of_stalkGen`, `exists_sub_mem_maximalIdeal_of_stalkGen`). -/
theorem germ_decomp (m : 𝒢P.genStalk) (hm : m ∈ IsLocalRing.maximalIdeal 𝒢P.genStalk) :
    m - germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) m) -
      germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) (germMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) m) ∈
      IsLocalRing.maximalIdeal 𝒢P.genStalk ^ 2 := by
  set p := (e.hom ≫ fst 𝒢₁.G 𝒢₂.G).left with hpdef
  set q := (e.hom ≫ snd 𝒢₁.G 𝒢₂.G).left with hqdef
  have w : p ≫ 𝒢₁.G.hom = q ≫ 𝒢₂.G.hom := by rw [hpdef, hqdef, Over.w, Over.w]
  have hgen : StalkGen p q 𝒢P.genericUnit :=
    StalkGen.comp_of_isIso e.hom.left (pullback.fst 𝒢₁.G.hom 𝒢₂.G.hom) (pullback.snd _ _) _
      (pullback_stalkGen _ _ _)
  have hrat₁ : RationalOver 𝒢₁.G.hom (p 𝒢P.genericUnit) := by
    rw [hpdef, hp₁]; exact rationalOver_genericUnit 𝒢₁
  have hrat₂ : RationalOver 𝒢₂.G.hom (q 𝒢P.genericUnit) := by
    rw [hqdef, hp₂]; exact rationalOver_genericUnit 𝒢₂
  have hm0 := maximalIdeal_eq_of_stalkGen w hgen hrat₁
  have hmax : IsLocalRing.maximalIdeal 𝒢P.genStalk =
      (IsLocalRing.maximalIdeal 𝒢₁.genStalk).map (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)) ⊔
        (IsLocalRing.maximalIdeal 𝒢₂.genStalk).map (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)) := by
    rw [hm0, stalkIdeal, germMap, germMap, Scheme.Hom.map_stalkMapAt_maximalIdeal,
      Scheme.Hom.map_stalkMapAt_maximalIdeal]
  have hr₂ : ∀ r, ∃ c, r - germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) c ∈
      IsLocalRing.maximalIdeal 𝒢P.genStalk := by
    intro r
    obtain ⟨b, hb⟩ := exists_sub_mem_maximalIdeal_of_stalkGen w hgen hrat₁ r
    obtain ⟨c, hc⟩ := Scheme.Hom.exists_stalkMapAt_eq q (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) b
    exact ⟨c, by rw [germMap, hc]; exact hb⟩
  have hr₁ : ∀ r, ∃ c, r - germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) c ∈
      IsLocalRing.maximalIdeal 𝒢P.genStalk := by
    intro r
    obtain ⟨b, hb⟩ := exists_sub_mem_maximalIdeal_of_stalkGen w.symm hgen.symm hrat₂ r
    obtain ⟨c, hc⟩ := Scheme.Hom.exists_stalkMapAt_eq p (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) b
    exact ⟨c, by rw [germMap, hc]; exact hb⟩
  exact IsLocalRing.sub_mem_maximalIdeal_sq_of_product₂ _ _ _ _ (germ_retract₁ 𝒢P 𝒢₁ 𝒢₂ e)
    (germ_retract₂ 𝒢P 𝒢₁ 𝒢₂ e)
    (fun a ha => by rw [germ_cross₁₂ 𝒢P 𝒢₁ 𝒢₂ e a ha]; exact Ideal.zero_mem _)
    (fun a ha => by rw [germ_cross₂₁ 𝒢P 𝒢₁ 𝒢₂ e a ha]; exact Ideal.zero_mem _) hmax hr₁ hr₂ hm

/-- **The cotangent space of a product.** `x = j₁(ψ₁ x) + j₂(ψ₂ x)`. -/
theorem cot_decomp (x : 𝒢P.cotangent) :
    x = cotMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) (cotMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) x) +
      cotMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) (cotMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) x) := by
  obtain ⟨m, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢P.genStalk).toCotangent_surjective x
  change 𝒢P.dCls m = cotMap 𝒢P 𝒢₁ _ _ (cotMap 𝒢₁ 𝒢P _ _ (𝒢P.dCls m)) +
    cotMap 𝒢P 𝒢₂ _ _ (cotMap 𝒢₂ 𝒢P _ _ (𝒢P.dCls m))
  rw [cotMap_dCls, cotMap_dCls, cotMap_dCls, cotMap_dCls]
  refine ((Ideal.toCotangent_eq _).mpr ?_).trans
    (map_add (IsLocalRing.maximalIdeal 𝒢P.genStalk).toCotangent _ _)
  show (m : 𝒢P.genStalk) - (_ + _) ∈ _
  rw [← sub_sub]
  exact germ_decomp 𝒢P 𝒢₁ 𝒢₂ e m m.2

end ProductCot

end ZInQ.UnifDims



/-! ## unif-dims: `ProductCotangent`, proved -/

namespace ZInQ.UnifDims

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

/-- **`ProductCotangent`, proved** (the statement is the body of `ZInQ.UnifDims.ProductCotangent`).
`jᵢ` is the cotangent map of the projection `pᵢ`; the retractions are the cotangent maps of
`x ↦ (x, 1)` and `y ↦ (1, y)`; `cot_decomp` gives surjectivity, the retractions injectivity, and
`omega_map_le` (functoriality of `ω`) the lattice. -/
theorem productCotangent_aux :
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) (hfst : IsMonHom (e.hom ≫ fst _ _))
    (hsnd : IsMonHom (e.hom ≫ snd _ _)),
    ∃ (j₁ : 𝒢₁.cotangent →ₗ[𝓞 L] 𝒢P.cotangent) (j₂ : 𝒢₂.cotangent →ₗ[𝓞 L] 𝒢P.cotangent),
      (∀ f : IsLocalRing.maximalIdeal 𝒢₁.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ fst _ _)).hom (f : 𝒢₁.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₁ (𝒢₁.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      (∀ f : IsLocalRing.maximalIdeal 𝒢₂.genStalk,
        ∃ h : (ZInQ.Metrization.pullGerm (e.hom ≫ snd _ _)).hom (f : 𝒢₂.genStalk) ∈
          IsLocalRing.maximalIdeal 𝒢P.genStalk, j₂ (𝒢₂.dCls f) = 𝒢P.dCls ⟨_, h⟩) ∧
      Function.Bijective (LinearMap.coprod j₁ j₂) ∧
      𝒢P.omega = 𝒢₁.omega.map j₁ ⊔ 𝒢₂.omega.map j₂ := by
  intro K _ A B C L _ _ _ 𝒢P 𝒢₁ 𝒢₂ e hfst hsnd
  set j₁ := cotMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e) with hj₁
  set j₂ := cotMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e) with hj₂
  set ψ₁ := cotMap 𝒢₁ 𝒢P _ (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) with hψ₁
  set ψ₂ := cotMap 𝒢₂ 𝒢P _ (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) with hψ₂
  have r11 : ∀ a, ψ₁ (j₁ a) = a := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent_surjective a
    change ψ₁ (j₁ (𝒢₁.dCls f)) = 𝒢₁.dCls f
    rw [hψ₁, hj₁, cotMap_dCls, cotMap_dCls]
    congr 1
    exact Subtype.ext (germ_retract₁ 𝒢P 𝒢₁ 𝒢₂ e f)
  have r22 : ∀ a, ψ₂ (j₂ a) = a := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent_surjective a
    change ψ₂ (j₂ (𝒢₂.dCls f)) = 𝒢₂.dCls f
    rw [hψ₂, hj₂, cotMap_dCls, cotMap_dCls]
    congr 1
    exact Subtype.ext (germ_retract₂ 𝒢P 𝒢₁ 𝒢₂ e f)
  have r12 : ∀ c, ψ₁ (j₂ c) = 0 := by
    intro c
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent_surjective c
    change ψ₁ (j₂ (𝒢₂.dCls f)) = 0
    rw [hψ₁, hj₂, cotMap_dCls, cotMap_dCls]
    have h0 : (⟨_, map_nonunit _ _ (map_nonunit _ _ f.2)⟩ :
        IsLocalRing.maximalIdeal 𝒢₁.genStalk) = 0 :=
      Subtype.ext (germ_cross₁₂ 𝒢P 𝒢₁ 𝒢₂ e f f.2)
    exact (congrArg (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent h0).trans (map_zero _)
  have r21 : ∀ a, ψ₂ (j₁ a) = 0 := by
    intro a
    obtain ⟨f, rfl⟩ := (IsLocalRing.maximalIdeal 𝒢₁.genStalk).toCotangent_surjective a
    change ψ₂ (j₁ (𝒢₁.dCls f)) = 0
    rw [hψ₂, hj₁, cotMap_dCls, cotMap_dCls]
    have h0 : (⟨_, map_nonunit _ _ (map_nonunit _ _ f.2)⟩ :
        IsLocalRing.maximalIdeal 𝒢₂.genStalk) = 0 :=
      Subtype.ext (germ_cross₂₁ 𝒢P 𝒢₁ 𝒢₂ e f f.2)
    exact (congrArg (IsLocalRing.maximalIdeal 𝒢₂.genStalk).toCotangent h0).trans (map_zero _)
  have dec : ∀ x, x = j₁ (ψ₁ x) + j₂ (ψ₂ x) := cot_decomp 𝒢P 𝒢₁ 𝒢₂ e
  refine ⟨j₁, j₂, fun f => ⟨map_nonunit (germMap 𝒢P 𝒢₁ _ (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)) _ f.2, ?_⟩,
    fun f => ⟨map_nonunit (germMap 𝒢P 𝒢₂ _ (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)) _ f.2, ?_⟩,
    ⟨?_, ?_⟩, ?_⟩
  · rw [hj₁, cotMap_dCls]; rfl
  · rw [hj₂, cotMap_dCls]; rfl
  · rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [LinearMap.coprod_apply] at h
    have h1 := congrArg ψ₁ h
    have h2 := congrArg ψ₂ h
    simp only [map_add, r11, r12, r21, r22, add_zero, zero_add] at h1 h2
    rw [h1, h2]
  · intro x
    exact ⟨(ψ₁ x, ψ₂ x), by rw [LinearMap.coprod_apply]; exact (dec x).symm⟩
  · refine le_antisymm (fun x hx => ?_) (sup_le ?_ ?_)
    · rw [dec x]
      exact Submodule.add_mem_sup
        (Submodule.mem_map_of_mem (omega_map_le 𝒢₁ 𝒢P _ (eta_inc₁ 𝒢P 𝒢₁ 𝒢₂ e)
          (hi₁ 𝒢P 𝒢₁ 𝒢₂ e) (Submodule.mem_map_of_mem hx)))
        (Submodule.mem_map_of_mem (omega_map_le 𝒢₂ 𝒢P _ (eta_inc₂ 𝒢P 𝒢₁ 𝒢₂ e)
          (hi₂ 𝒢P 𝒢₁ 𝒢₂ e) (Submodule.mem_map_of_mem hx)))
    · exact omega_map_le 𝒢P 𝒢₁ _ (IsMonHom.one_hom _) (hp₁ 𝒢P 𝒢₁ 𝒢₂ e)
    · exact omega_map_le 𝒢P 𝒢₂ _ (IsMonHom.one_hom _) (hp₂ 𝒢P 𝒢₁ 𝒢₂ e)

end ZInQ.UnifDims




/-! ## unif-dims: `ProductCotangent` closed; `ProductHodgeLattice` from `TangentDimAtOrigin` and T35 -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings.HodgeLattice

/-- **`ProductCotangent`, proved** (`productCotangent_aux`, `PC.lean`). -/
theorem productCotangent : ProductCotangent := productCotangent_aux

/-- **metrization's `ProductHodgeLattice` from hodge-lattice's `TangentDimAtOrigin` and the
textbook leaf T35 (proved).** -/
theorem productHodgeLattice_of_tangentDim (hT : TangentDimAtOrigin)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) : ZInQ.Metrization.ProductHodgeLattice :=
  productHodgeLattice_of_cotangent productCotangent hT hT35

end ZInQ.UnifDims




/-! ## unif-dims: S-alg and P2 from T35 and `TangentDimAtOrigin` alone -/

namespace ZInQ.UnifDims

open ZInQ.DefFaltings ZInQ.DefFaltings.HodgeLattice

/-- **S-alg (`ProductMetrizationOfProductUnif`) from T35 and `TangentDimAtOrigin` (proved).** -/
theorem productMetrizationOfProductUnif_of_tangentDim (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hT : TangentDimAtOrigin) : ZInQ.ProductHeight.ProductMetrizationOfProductUnif :=
  productMetrizationOfProductUnif_of_cotangent hT35 productCotangent hT

/-- **Glue piece 5 of `GluePieces` (P2, `ProductModelHeight`) from the textbook leaf T35 and
hodge-lattice's `TangentDimAtOrigin` (proved).** -/
theorem productModelHeight_of_tangentDim (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hT : TangentDimAtOrigin) : ZInQ.H5Neron.ProductModelHeight :=
  productModelHeight_of_cotangent hT35 productCotangent hT

end ZInQ.UnifDims

