import ZInQKernel.Contrib.RC53Assist.IntegralDuality.ReductionDetection

/-!
# Detecting acyclicity modulo a Jacobson element under finiteness of cohomology

This file strengthens the termwise-finite criterion of
`IntegralDuality.ReductionDetection`: the terms of the complexes need not be finitely
generated; only the cohomology is assumed finitely generated.

Let `R` be a commutative Noetherian ring, `π : R` an element of the Jacobson radical and
`φ : R →+* A` surjective with kernel `(π)`. Let `C` be a cochain complex of `R`-modules on whose
terms `π` acts injectively. If the coefficient extension of `C` along `φ` is acyclic, then for
every cycle `z` of `C^n` we may write `z = d y + π w` with `w` again a cycle (injectivity of `π`
on `C^(n+1)`). Hence multiplication by `π` is surjective on the cohomology group
`H^n(C) = ker d / im d`, written literally as a quotient of the kernel. If `H^n(C)` is finitely
generated, Nakayama's lemma applied to `H^n(C)` itself gives `H^n(C) = 0`. No finiteness of
cycles or of the terms is used.

Applied to the mapping cone of a given chain map `f : P ⟶ Q` between complexes with
`π`-torsion-free terms, this shows: if the cone of `f` has finitely generated cohomology and the
coefficient extension of this same `f` along `φ` is a quasi-isomorphism, then `f` is a
quasi-isomorphism. Over a Noetherian ring, finite generation of the cohomology of the cone
follows from that of `P` and `Q` by the long exact sequence of the cone. The finiteness of
cohomology is an explicit hypothesis; it is not derived from any statement about the terms.
-/

noncomputable section

universe u

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

open CategoryTheory Limits

section Linear

variable {R : Type*} [CommRing R]

/-- **Nakayama on cohomology.** Let `M₀ → M₁ → M₂` compose to zero, let `π` be regular on
`M₂` and lie in the Jacobson radical, and suppose every cycle is a boundary modulo `π`. If the
cohomology `ker d₁ / im d₀` is a finitely generated module, then it vanishes: every cycle is a
boundary. -/
theorem surjective_toCycles_of_exact_mod {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    (d₀ : M₀ →ₗ[R] M₁) (d₁ : M₁ →ₗ[R] M₂) (hd : ∀ y, d₀ y ∈ LinearMap.ker d₁)
    {π : R} (hreg : IsSMulRegular M₂ π) (hJ : π ∈ (⊥ : Ideal R).jacobson)
    (hred : ∀ z, d₁ z = 0 → ∃ y w, z = d₀ y + π • w)
    (hfin : Module.Finite R
      (LinearMap.ker d₁ ⧸ LinearMap.range (d₀.codRestrict (LinearMap.ker d₁) hd))) :
    Function.Surjective (d₀.codRestrict (LinearMap.ker d₁) hd) := by
  set T := d₀.codRestrict (LinearMap.ker d₁) hd
  set H := LinearMap.ker d₁ ⧸ LinearMap.range T
  have htop : (⊤ : Submodule R H) ≤ Ideal.span {π} • ⊤ := by
    intro h _
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range T) h
    rw [LinearMap.mem_ker] at hz
    obtain ⟨y, w, hzw⟩ := hred z hz
    have hw : d₁ w = 0 := by
      apply hreg
      change π • d₁ w = π • 0
      rw [smul_zero, ← map_smul]
      have h0 := hz
      rw [hzw, map_add, LinearMap.mem_ker.1 (hd y), zero_add] at h0
      exact h0
    have hmk : (Submodule.Quotient.mk ⟨z, hz⟩ : H) =
        π • Submodule.Quotient.mk (⟨w, hw⟩ : LinearMap.ker d₁) := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      refine ⟨y, ?_⟩
      apply Subtype.ext
      change d₀ y = z - π • w
      rw [hzw]
      abel
    rw [hmk]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self π) Submodule.mem_top
  have hbot : (⊤ : Submodule R H) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfin.fg_top htop
      (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hJ)
  intro z
  have hz : (Submodule.Quotient.mk z : H) = 0 := by
    have : (Submodule.Quotient.mk z : H) ∈ (⊤ : Submodule R H) := Submodule.mem_top
    rw [hbot, Submodule.mem_bot] at this
    exact this
  rw [Submodule.Quotient.mk_eq_zero] at hz
  obtain ⟨y, hy⟩ := hz
  exact ⟨y, hy⟩

end Linear

section Complexes

variable {R : Type u} [CommRing R]

/-- The cohomology of a cochain complex of modules in degree `n`, as the explicit quotient of
the kernel of `d : C^n → C^(n+1)` by the image of `d : C^(n-1) → C^n`. -/
def homologyLinearEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    K.homology n ≃ₗ[R] (K.sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.H :=
  (ShortComplex.homologyMapIso (K.isoSc' (n - 1) n (n + 1) (by simp) (by simp)) ≪≫
    (K.sc' (n - 1) n (n + 1)).moduleCatHomologyIso).toLinearEquiv

/-- **Acyclicity is detected modulo `π` when cohomology is finitely generated.** Let `R` be a
commutative Noetherian ring, `π` in its Jacobson radical and `φ : R →+* A` surjective with
kernel `(π)`. A cochain complex of `R`-modules on whose terms `π` acts injectively, with
finitely generated cohomology, is acyclic as soon as its coefficient extension along `φ` is
acyclic. The terms themselves need not be finitely generated. -/
theorem acyclic_of_scalarChanged_acyclic_of_homology_finite {A : Type u} [CommRing A]
    (φ : R →+* A) (hsurj : Function.Surjective φ) {π : R}
    (hker : RingHom.ker φ = Ideal.span {π}) (hJ : π ∈ (⊥ : Ideal R).jacobson)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hreg : ∀ n, IsSMulRegular (K.X n) π)
    (hfin : ∀ n, Module.Finite R (K.homology n))
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
  have hH : Module.Finite R (K.sc' (n - 1) n (n + 1)).moduleCatLeftHomologyData.H := by
    have := hfin n
    exact Module.Finite.equiv (homologyLinearEquiv K n)
  apply (K.exactAt_iff' (n - 1) n (n + 1) (by simp) (by simp)).2
  rw [ShortComplex.exact_iff_surjective_moduleCatToCycles]
  exact surjective_toCycles_of_exact_mod (K.d (n - 1) n).hom (K.d n (n + 1)).hom
    (K.sc' (n - 1) n (n + 1)).moduleCat_zero_apply (hreg (n + 1)) hJ
    (exists_eq_add_smul_of_baseChange_exact (A := A) hsurj hker _ _ hex) hH

/-- **Reduction detects quasi-isomorphisms under finiteness of the cone cohomology.** Let `R`
be a commutative Noetherian ring, `π` a regular element of its Jacobson radical and
`φ : R →+* A` surjective with kernel `(π)`. Let `f : P ⟶ Q` be a chain map of cochain
complexes with `π`-torsion-free terms (no finiteness of the terms is required) whose mapping
cone has finitely generated cohomology in every degree. If the coefficient extension of this
same `f` along `φ` is a quasi-isomorphism, then `f` is a quasi-isomorphism. -/
theorem quasiIso_of_scalarChanged_quasiIso_of_cone_homology_finite {A : Type u} [CommRing A]
    (φ : R →+* A) (hsurj : Function.Surjective φ) {π : R}
    (hker : RingHom.ker φ = Ideal.span {π}) (hπ : IsRegular π)
    (hJ : π ∈ (⊥ : Ideal R).jacobson)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    [∀ n, Module.IsTorsionFree R (P.X n)] [∀ n, Module.IsTorsionFree R (Q.X n)]
    (hfin : ∀ n, Module.Finite R ((CochainComplex.mappingCone f).homology n))
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
  refine acyclic_of_scalarChanged_acyclic_of_homology_finite φ hsurj hker hJ _
    (fun n => ?_) hfin hK
  intro x y hxy
  apply (mappingConeXEquiv f n).injective
  have h := congrArg (mappingConeXEquiv f n) hxy
  change mappingConeXEquiv f n (π • x) = mappingConeXEquiv f n (π • y) at h
  rw [map_smul, map_smul] at h
  exact Prod.ext (hπ.isSMulRegular (congrArg Prod.fst h))
    (hπ.isSMulRegular (congrArg Prod.snd h))

/-- Over a Noetherian ring, the mapping cone of a chain map between complexes with finitely
generated cohomology has finitely generated cohomology. This uses the exact sequence
`H^n(Q) → H^n(Cone f) → H^n(P[1]) = H^(n+1)(P)` of the degreewise split short exact sequence
`0 → Q → Cone f → P[1] → 0`. -/
theorem mappingCone_homology_finite [IsNoetherianRing R]
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (hP : ∀ n, Module.Finite R (P.homology n)) (hQ : ∀ n, Module.Finite R (Q.homology n))
    (n : ℤ) : Module.Finite R ((CochainComplex.mappingCone f).homology n) := by
  let S := CochainComplex.mappingCone.triangleRotateShortComplex f
  have hS : S.ShortExact := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun i => (CochainComplex.mappingCone.triangleRotateShortComplexSplitting f i).shortExact)
  have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
    (hS.homology_exact₂ n)
  have h₁ : Module.Finite R (S.X₁.homology n) := hQ n
  have h₃ : Module.Finite R (S.X₃.homology n) := by
    let e := (CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} R) 1 n (1 + n) rfl).app P
    have : Module.Finite R
        ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) _ (1 + n)).obj P) :=
      hP (1 + n)
    exact Module.Finite.equiv e.toLinearEquiv.symm
  let g := (HomologicalComplex.homologyMap S.g n).hom
  have hg : Module.Finite R (LinearMap.range g) := inferInstance
  have hfin : Module.Finite R (S.X₂.homology n) :=
    Module.Finite.of_exact (f := (HomologicalComplex.homologyMap S.f n).hom) (g := g.rangeRestrict)
      (fun y => by
        rw [← hex y]
        constructor
        · intro h
          exact congrArg Subtype.val h
        · intro h
          exact Subtype.ext h)
      g.surjective_rangeRestrict
  exact hfin

/-- **Reduction detects quasi-isomorphisms under finiteness of cohomology.** Let `R` be a
commutative Noetherian ring, `π` a regular element of its Jacobson radical and
`φ : R →+* A` surjective with kernel `(π)`. Let `f : P ⟶ Q` be a chain map of cochain
complexes with `π`-torsion-free terms and finitely generated cohomology (the terms may be of
arbitrary size). If the coefficient extension of this same `f` along `φ` is a
quasi-isomorphism, then `f` is a quasi-isomorphism. -/
theorem quasiIso_of_scalarChanged_quasiIso_of_homology_finite [IsNoetherianRing R]
    {A : Type u} [CommRing A]
    (φ : R →+* A) (hsurj : Function.Surjective φ) {π : R}
    (hker : RingHom.ker φ = Ideal.span {π}) (hπ : IsRegular π)
    (hJ : π ∈ (⊥ : Ideal R).jacobson)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    [∀ n, Module.IsTorsionFree R (P.X n)] [∀ n, Module.IsTorsionFree R (Q.X n)]
    (hP : ∀ n, Module.Finite R (P.homology n)) (hQ : ∀ n, Module.Finite R (Q.homology n))
    (hf : QuasiIso (((ModuleCat.extendScalars φ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) :
    QuasiIso f :=
  quasiIso_of_scalarChanged_quasiIso_of_cone_homology_finite φ hsurj hker hπ hJ f
    (mappingCone_homology_finite f hP hQ) hf

end Complexes

section TwoAdic

/-- **Mod-two detection over `ℤ_[2]` under finiteness of the cone cohomology.** For a given
chain map `f : P ⟶ Q` of cochain complexes of torsion-free `ℤ_[2]`-modules (of arbitrary rank)
whose mapping cone has finitely generated cohomology, if the reduction of this same `f` along
`ℤ_[2] → ZMod 2` is a quasi-isomorphism, then `f` is a quasi-isomorphism. -/
theorem quasiIso_of_modTwo_quasiIso_of_cone_homology_finite
    {P Q : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ} (f : P ⟶ Q)
    [∀ n, Module.IsTorsionFree ℤ_[2] (P.X n)] [∀ n, Module.IsTorsionFree ℤ_[2] (Q.X n)]
    (hfin : ∀ n, Module.Finite ℤ_[2] ((CochainComplex.mappingCone f).homology n))
    (hf : QuasiIso (((ModuleCat.extendScalars (PadicInt.toZMod (p := 2))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) :
    QuasiIso f :=
  quasiIso_of_scalarChanged_quasiIso_of_cone_homology_finite (PadicInt.toZMod (p := 2))
    toZMod_two_surjective ker_toZMod_two isRegular_two two_mem_jacobson f hfin hf

/-- **Mod-two detection over `ℤ_[2]` under finiteness of cohomology.** For a given chain map
`f : P ⟶ Q` of cochain complexes of torsion-free `ℤ_[2]`-modules (of arbitrary rank) with
finitely generated cohomology, if the reduction of this same `f` along `ℤ_[2] → ZMod 2` is a
quasi-isomorphism, then `f` is a quasi-isomorphism. -/
theorem quasiIso_of_modTwo_quasiIso_of_homology_finite
    {P Q : CochainComplex (ModuleCat.{0} ℤ_[2]) ℤ} (f : P ⟶ Q)
    [∀ n, Module.IsTorsionFree ℤ_[2] (P.X n)] [∀ n, Module.IsTorsionFree ℤ_[2] (Q.X n)]
    (hP : ∀ n, Module.Finite ℤ_[2] (P.homology n)) (hQ : ∀ n, Module.Finite ℤ_[2] (Q.homology n))
    (hf : QuasiIso (((ModuleCat.extendScalars (PadicInt.toZMod (p := 2))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f)) :
    QuasiIso f :=
  quasiIso_of_scalarChanged_quasiIso_of_homology_finite (PadicInt.toZMod (p := 2))
    toZMod_two_surjective ker_toZMod_two isRegular_two two_mem_jacobson f hP hQ hf

end TwoAdic

end ZInQ.Contrib.RC53Assist.IntegralDuality
