import Mathlib

/-!
# Detecting a quasi-isomorphism from its reduction modulo a Jacobson element

Let `R` be a commutative Noetherian ring, let `π : R` be a regular element of the Jacobson
radical, and let `φ : R →+* A` be surjective with kernel `(π)`, so that `A ≅ R/(π)`.
For cochain complexes `P`, `Q` of `R`-modules whose terms are finitely generated and
`π`-torsion-free (for instance finite free), and for a GIVEN chain map `f : P ⟶ Q`,
we prove: if the coefficient extension of that same `f` along `φ` is a quasi-isomorphism,
then `f` is a quasi-isomorphism.

Proof. Let `C` be the mapping cone of `f`. Coefficient extension commutes with mapping cones,
so the extension of `C` is acyclic. Termwise, `A ⊗_R C^n = C^n / π C^n`. A cycle `z` of `C^n`
therefore satisfies `z = d y + π w`; since `π` is regular on `C^(n+1)`, `w` is again a cycle.
Hence the cycles `Z^n` satisfy `Z^n ≤ B^n ⊔ (π) • Z^n`, and `Z^n` is finitely generated
because `C^n` is a finitely generated module over a Noetherian ring. Nakayama's lemma gives
`Z^n ≤ B^n`, i.e. `C` is acyclic, i.e. `f` is a quasi-isomorphism.

No boundedness, inverse-limit or K-flatness statement is used. Because the terms are
`π`-torsion-free, the termwise quotient `C / π C` is the derived reduction
`C ⊗^L_R R/(π)`, computed with the two-term flat resolution `R --π--> R` of `R/(π)`;
this identification is only a remark and is not needed in the proof.

The hypothesis concerns the reduction of the actual map `f`. An abstract isomorphism between
the reductions of `P` and `Q` would not suffice: the two-term complexes `[R --π--> R]` and
`[R --π²--> R]` have isomorphic reductions, but over `ℤ_[2]` with `π = 2` their top
cohomology groups `ℤ/2` and `ℤ/4` differ, so they are not quasi-isomorphic.

The specialisation to `ℤ_[2]` uses the canonical map `PadicInt.toZMod : ℤ_[2] →+* ZMod 2`.
-/

noncomputable section

universe u

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory Limits Pointwise

section Linear

variable {R : Type*} [CommRing R]

/-- **Nakayama step.** Let `M₀ → M₁ → M₂` compose to zero, with `M₁` finitely generated over
a Noetherian ring and `π` regular on `M₂` and in the Jacobson radical. If every cycle is a
boundary modulo `π`, then every cycle is a boundary. -/
theorem ker_le_range_of_exact_mod {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [IsNoetherianRing R] [Module.Finite R M₁]
    (d₀ : M₀ →ₗ[R] M₁) (d₁ : M₁ →ₗ[R] M₂) (hd : ∀ y, d₁ (d₀ y) = 0)
    {π : R} (hreg : IsSMulRegular M₂ π) (hJ : π ∈ (⊥ : Ideal R).jacobson)
    (hred : ∀ z, d₁ z = 0 → ∃ y w, z = d₀ y + π • w) :
    LinearMap.ker d₁ ≤ LinearMap.range d₀ := by
  have hfg : (LinearMap.ker d₁).FG := IsNoetherian.noetherian _
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {π}) hfg ?_ ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hJ
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨y, w, rfl⟩ := hred z hz
    have hw : d₁ w = 0 := by
      apply hreg
      change π • d₁ w = π • 0
      rw [smul_zero, ← map_smul]
      rw [map_add, hd, zero_add] at hz
      exact hz
    exact Submodule.add_mem_sup (LinearMap.mem_range_self d₀ y)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) hw)

variable {A : Type*} [CommRing A] [Algebra R A]

/-- Along a surjective algebra map, every element of `A ⊗[R] M` is of the form `1 ⊗ y`. -/
theorem exists_one_tmul_eq (hsurj : Function.Surjective (algebraMap R A))
    {M : Type*} [AddCommGroup M] [Module R M] (t : TensorProduct R A M) :
    ∃ y : M, (1 : A) ⊗ₜ[R] y = t := by
  induction t using TensorProduct.inductionOn with
  | tmul a m =>
    obtain ⟨r, rfl⟩ := hsurj a
    refine ⟨r • m, ?_⟩
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨y₁, rfl⟩ := h₁
    obtain ⟨y₂, rfl⟩ := h₂
    exact ⟨y₁ + y₂, TensorProduct.tmul_add _ _ _⟩

/-- Along a surjective algebra map with kernel `(π)`, an element `m` with `1 ⊗ m = 0`
in `A ⊗[R] M` is divisible by `π`. -/
theorem exists_eq_smul_of_one_tmul_eq_zero (hsurj : Function.Surjective (algebraMap R A))
    {π : R} (hker : RingHom.ker (algebraMap R A) = Ideal.span {π})
    {M : Type*} [AddCommGroup M] [Module R M] {m : M}
    (hm : (1 : A) ⊗ₜ[R] m = 0) : ∃ w : M, m = π • w := by
  let e := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) hsurj
  have hI : RingHom.ker (Algebra.ofId R A) = Ideal.span {π} := by
    ext x
    rw [RingHom.mem_ker, Algebra.ofId_apply, ← RingHom.mem_ker, hker]
  let L := LinearEquiv.rTensor M e.toLinearEquiv
  have h1 : L ((1 : R ⧸ RingHom.ker (Algebra.ofId R A)) ⊗ₜ[R] m) = (1 : A) ⊗ₜ[R] m := by
    simp [L]
  have h0 : (1 : R ⧸ RingHom.ker (Algebra.ofId R A)) ⊗ₜ[R] m = 0 := by
    apply L.injective
    rw [h1, hm, map_zero]
  have hq := congrArg (TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (Algebra.ofId R A)))
    h0
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero,
    Submodule.Quotient.mk_eq_zero, hI, Submodule.ideal_span_singleton_smul] at hq
  obtain ⟨w, -, hw⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hq
  exact ⟨w, hw.symm⟩

/-- Exactness of the base-changed sequence gives exactness modulo `π`. -/
theorem exists_eq_add_smul_of_baseChange_exact (hsurj : Function.Surjective (algebraMap R A))
    {π : R} (hker : RingHom.ker (algebraMap R A) = Ideal.span {π})
    {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] (d₀ : M₀ →ₗ[R] M₁) (d₁ : M₁ →ₗ[R] M₂)
    (hex : Function.Exact (d₀.baseChange A) (d₁.baseChange A))
    (z : M₁) (hz : d₁ z = 0) : ∃ y w, z = d₀ y + π • w := by
  have h0 : d₁.baseChange A ((1 : A) ⊗ₜ[R] z) = 0 := by
    rw [LinearMap.baseChange_tmul, hz, TensorProduct.tmul_zero]
  obtain ⟨t, ht⟩ := (hex _).1 h0
  obtain ⟨y, rfl⟩ := exists_one_tmul_eq hsurj t
  rw [LinearMap.baseChange_tmul] at ht
  have hm : (1 : A) ⊗ₜ[R] (z - d₀ y) = 0 := by
    rw [TensorProduct.tmul_sub, ← ht, sub_self]
  obtain ⟨w, hw⟩ := exists_eq_smul_of_one_tmul_eq_zero hsurj hker hm
  exact ⟨y, w, by rw [← hw]; abel⟩

end Linear

section Complexes

variable {R : Type u} [CommRing R]

/-- Extension of coefficients is an additive functor. -/
instance extendScalars_additive {A : Type u} [CommRing A] (φ : R →+* A) :
    (ModuleCat.extendScalars.{u, u, u} φ).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    let oneA : (ModuleCat.restrictScalars φ).obj (ModuleCat.of A A) := (1 : A)
    change oneA ⊗ₜ[R] (f.hom x + g.hom x) = _
    exact TensorProduct.tmul_add _ _ _

/-- A chain map of cochain complexes of modules is a quasi-isomorphism precisely when its
mapping cone is acyclic. -/
theorem quasiIso_iff_mappingCone_acyclic {S : Type u} [CommRing S]
    {C D : CochainComplex (ModuleCat.{u} S) ℤ} (f : C ⟶ D) :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff f,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff f,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} S)).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

/-- The terms of a mapping cone are the products of the shifted source and the target. -/
def mappingConeXEquiv {C D : CochainComplex (ModuleCat.{u} R) ℤ} (f : C ⟶ D) (n : ℤ) :
    (CochainComplex.mappingCone f).X n ≃ₗ[R] (C.X (n + 1) × D.X n) :=
  ((HomologicalComplex.homotopyCofiber.XIsoBiprod f n (n + 1) rfl) ≪≫
    ModuleCat.biprodIsoProd (C.X (n + 1)) (D.X n)).toLinearEquiv

/-- Acyclicity of a complex of finitely generated modules, `π`-regular in every degree, is
detected after extension of coefficients to `R/(π)`. -/
theorem acyclic_of_scalarChanged_acyclic [IsNoetherianRing R] {A : Type u} [CommRing A]
    (φ : R →+* A) (hsurj : Function.Surjective φ) {π : R}
    (hker : RingHom.ker φ = Ideal.span {π}) (hJ : π ∈ (⊥ : Ideal R).jacobson)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hfin : ∀ n, Module.Finite R (K.X n))
    (hreg : ∀ n, IsSMulRegular (K.X n) π)
    (hK : (((ModuleCat.extendScalars φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).Acyclic) :
    K.Acyclic := by
  let : Algebra R A := φ.toAlgebra
  intro n
  have hex : Function.Exact ((K.d (n - 1) n).hom.baseChange A)
      ((K.d n (n + 1)).hom.baseChange A) := by
    have h := (((((ModuleCat.extendScalars φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).1 (hK n))
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h
  have hd : ∀ y, (K.d n (n + 1)).hom ((K.d (n - 1) n).hom y) = 0 := fun y => by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]
    rfl
  have := hfin n
  have hle := ker_le_range_of_exact_mod (K.d (n - 1) n).hom (K.d n (n + 1)).hom hd
    (hreg (n + 1)) hJ
    (exists_eq_add_smul_of_baseChange_exact (A := A) hsurj hker _ _ hex)
  apply (K.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).2
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
  rw [LinearMap.exact_iff]
  refine le_antisymm hle ?_
  rintro _ ⟨y, rfl⟩
  exact hd y

/-- **Reduction detects quasi-isomorphisms (general form).** Let `R` be a commutative
Noetherian ring, `π` a regular element of its Jacobson radical and `φ : R →+* A` surjective
with kernel `(π)`. Let `f : P ⟶ Q` be a chain map of cochain complexes of finitely generated
`π`-torsion-free `R`-modules. If the coefficient extension of this same `f` along `φ` is a
quasi-isomorphism, then `f` is a quasi-isomorphism. -/
theorem quasiIso_of_scalarChanged_quasiIso [IsNoetherianRing R] {A : Type u} [CommRing A]
    (φ : R →+* A) (hsurj : Function.Surjective φ) {π : R}
    (hker : RingHom.ker φ = Ideal.span {π}) (hπ : IsRegular π)
    (hJ : π ∈ (⊥ : Ideal R).jacobson)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    [∀ n, Module.Finite R (P.X n)] [∀ n, Module.Finite R (Q.X n)]
    [∀ n, Module.IsTorsionFree R (P.X n)] [∀ n, Module.IsTorsionFree R (Q.X n)]
    (hf : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) :
    QuasiIso f := by
  apply (quasiIso_iff_mappingCone_acyclic f).2
  have hc := (quasiIso_iff_mappingCone_acyclic _).1 hf
  let e := HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f
    (ModuleCat.extendScalars φ)
  have hK : (((ModuleCat.extendScalars φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (CochainComplex.mappingCone f)).Acyclic := by
    intro n
    exact (exactAt_iff_of_quasiIsoAt e.hom n).2 (hc n)
  refine acyclic_of_scalarChanged_acyclic φ hsurj hker hJ _ (fun n => ?_) (fun n => ?_) hK
  · exact Module.Finite.equiv (mappingConeXEquiv f n).symm
  · intro x y hxy
    apply (mappingConeXEquiv f n).injective
    have h := congrArg (mappingConeXEquiv f n) hxy
    change mappingConeXEquiv f n (π • x) = mappingConeXEquiv f n (π • y) at h
    rw [map_smul, map_smul] at h
    exact Prod.ext (hπ.isSMulRegular (congrArg Prod.fst h))
      (hπ.isSMulRegular (congrArg Prod.snd h))

/-- **Reduction detects quasi-isomorphisms (finite free form).** -/
theorem quasiIso_of_scalarChanged_quasiIso_free [IsNoetherianRing R] {A : Type u} [CommRing A]
    (φ : R →+* A) (hsurj : Function.Surjective φ) {π : R}
    (hker : RingHom.ker φ = Ideal.span {π}) (hπ : IsRegular π)
    (hJ : π ∈ (⊥ : Ideal R).jacobson)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    [∀ n, Module.Free R (P.X n)] [∀ n, Module.Finite R (P.X n)]
    [∀ n, Module.Free R (Q.X n)] [∀ n, Module.Finite R (Q.X n)]
    (hf : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) :
    QuasiIso f :=
  quasiIso_of_scalarChanged_quasiIso φ hsurj hker hπ hJ f hf

end Complexes

section TwoAdic

/-- The canonical reduction `ℤ_[2] → ZMod 2` is surjective. -/
theorem toZMod_two_surjective : Function.Surjective (PadicInt.toZMod (p := 2)) :=
  ZMod.ringHom_surjective _

/-- The kernel of the canonical reduction `ℤ_[2] → ZMod 2` is generated by `2`. -/
theorem ker_toZMod_two : RingHom.ker (PadicInt.toZMod (p := 2)) = Ideal.span {(2 : ℤ_[2])} := by
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
  norm_num

/-- `2` is a regular element of `ℤ_[2]`. -/
theorem isRegular_two : IsRegular (2 : ℤ_[2]) :=
  isRegular_iff_ne_zero.2 two_ne_zero

/-- `2` lies in the Jacobson radical of `ℤ_[2]`. -/
theorem two_mem_jacobson : (2 : ℤ_[2]) ∈ (⊥ : Ideal ℤ_[2]).jacobson := by
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
  exact_mod_cast Ideal.mem_span_singleton_self ((2 : ℕ) : ℤ_[2])

/-- **Mod-two detection over `ℤ_[2]`.** For cochain complexes `P`, `Q` of finite free
`ℤ_[2]`-modules and a given chain map `f : P ⟶ Q`, if the reduction of this same `f` along the
canonical map `ℤ_[2] → ZMod 2` is a quasi-isomorphism, then `f` is a quasi-isomorphism. -/
theorem quasiIso_of_modTwo_quasiIso {P Q : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ}
    (f : P ⟶ Q)
    [∀ n, Module.Free ℤ_[2] (P.X n)] [∀ n, Module.Finite ℤ_[2] (P.X n)]
    [∀ n, Module.Free ℤ_[2] (Q.X n)] [∀ n, Module.Finite ℤ_[2] (Q.X n)]
    (hf : QuasiIso (((ModuleCat.extendScalars (PadicInt.toZMod (p := 2))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) :
    QuasiIso f :=
  quasiIso_of_scalarChanged_quasiIso_free (PadicInt.toZMod (p := 2)) toZMod_two_surjective
    ker_toZMod_two isRegular_two two_mem_jacobson f hf

end TwoAdic

end ZInQ.Contrib.RC53Assist.IntegralDuality
