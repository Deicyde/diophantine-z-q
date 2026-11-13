import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import ZInQKernel.HDecomp.Objects

/-! # t10-etale: T10 over Mathlib's `ℓ`-adic cohomology

Mathlib v4.35 defines `Scheme.EllAdicCohomology X ℓ n` (pro-étale cohomology with coefficients in
the sheaf `U ↦ C(U, ℤ_ℓ)`, Bhatt–Scholze 2015 Def. 6.8.1) as an abelian group only. This file
1. gives it its `ℤ_ℓ`-module structure (multiplication by `a ∈ ℤ_ℓ` on the coefficient sheaf,
   applied through the functoriality `Sheaf.H.map` of sheaf cohomology);
2. checks the structure is the expected one: `H⁰(X, ℤ_ℓ) ≃ₗ[ℤ_ℓ] C(X, ℤ_ℓ)`;
3. states T10 as a `ℤ_ℓ`-linear isomorphism `H¹(A_K̄, ℤ_ℓ) ≃ₗ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)`.
-/

open CategoryTheory Limits AlgebraicGeometry


universe u
namespace T10Etale

section Coh

set_option backward.isDefEq.respectTransparency.types false

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

noncomputable abbrev F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u+1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj (X.ellAdicSheaf ℓ)

/-- The sections of the coefficient sheaf are `ULift C(U, ℤ_ℓ)` (by `rfl`). -/
example (U : X.ProEt) : ((F X ℓ).obj.obj (Opposite.op U) : Type (u+1)) = ULift.{u+1} C(U.left, ℤ_[ℓ]) := rfl

/-- multiplication by `a` on `ULift C(U, ℤ_ℓ)`. -/
noncomputable def smulHom (U : Scheme.{u}) (a : ℤ_[ℓ]) :
    ULift.{u+1} C(U, ℤ_[ℓ]) →+ ULift.{u+1} C(U, ℤ_[ℓ]) where
  toFun x := ⟨ContinuousMap.const U a * x.down⟩
  map_zero' := by ext1; simp
  map_add' x y := by ext1; simp [mul_add]

noncomputable def smulEnd (a : ℤ_[ℓ]) : F X ℓ ⟶ F X ℓ :=
  ObjectProperty.homMk
  { app U := AddCommGrpCat.ofHom (smulHom ℓ U.unop.left a)
    naturality U V f := by
      ext x
      rfl }


@[simp] lemma smulHom_apply (U : Scheme.{u}) (a : ℤ_[ℓ]) (x : ULift.{u+1} C(U, ℤ_[ℓ])) :
    smulHom ℓ U a x = ⟨ContinuousMap.const U a * x.down⟩ := rfl

lemma smulHom_one (U : Scheme.{u}) : smulHom ℓ U 1 = AddMonoidHom.id _ := by
  ext x : 2; simp

lemma smulHom_mul (U : Scheme.{u}) (a b : ℤ_[ℓ]) :
    smulHom ℓ U (a * b) = (smulHom ℓ U a).comp (smulHom ℓ U b) := by
  refine AddMonoidHom.ext fun x => ULift.ext (ContinuousMap.ext fun p => ?_)
  simp [mul_assoc]

lemma smulHom_add (U : Scheme.{u}) (a b : ℤ_[ℓ]) :
    smulHom ℓ U (a + b) = smulHom ℓ U a + smulHom ℓ U b := by
  refine AddMonoidHom.ext fun x => ULift.ext (ContinuousMap.ext fun p => ?_)
  simp [add_mul]

lemma smulHom_zero (U : Scheme.{u}) : smulHom ℓ U 0 = 0 := by
  ext x : 2; simp

lemma smulEnd_one : smulEnd X ℓ 1 = 𝟙 _ := by
  apply Sheaf.hom_ext; ext U : 2; apply AddCommGrpCat.hom_ext; exact smulHom_one ℓ _

lemma smulEnd_mul (a b : ℤ_[ℓ]) : smulEnd X ℓ (a * b) = smulEnd X ℓ b ≫ smulEnd X ℓ a := by
  apply Sheaf.hom_ext; ext U : 2; apply AddCommGrpCat.hom_ext; exact smulHom_mul ℓ _ a b

lemma smulEnd_add (a b : ℤ_[ℓ]) : smulEnd X ℓ (a + b) = smulEnd X ℓ a + smulEnd X ℓ b := by
  apply Sheaf.hom_ext; ext U : 2; apply AddCommGrpCat.hom_ext; exact smulHom_add ℓ _ a b

lemma smulEnd_zero : smulEnd X ℓ 0 = 0 := by
  apply Sheaf.hom_ext; ext U : 2; apply AddCommGrpCat.hom_ext; exact smulHom_zero ℓ _


/-- The `ℤ_ℓ`-module structure on `Hⁿ_proet(X, ℤ_ℓ)`: `a` acts through the sheaf endomorphism
"multiplication by `a`" of the coefficient sheaf `U ↦ C(U, ℤ_ℓ)`. -/
noncomputable instance (n : ℕ) : Module ℤ_[ℓ] (X.EllAdicCohomology ℓ n) where
  smul a x := Sheaf.H.map (smulEnd X ℓ a) n x
  one_smul x := by
    change Sheaf.H.map (smulEnd X ℓ 1) n x = x
    rw [smulEnd_one]; exact Sheaf.H.map_id_apply _
  mul_smul a b x := by
    change Sheaf.H.map (smulEnd X ℓ (a * b)) n x =
      Sheaf.H.map (smulEnd X ℓ a) n (Sheaf.H.map (smulEnd X ℓ b) n x)
    rw [smulEnd_mul]; exact Sheaf.H.map_comp_apply _ _ _
  smul_zero a := map_zero (Sheaf.H.map (smulEnd X ℓ a) n)
  smul_add a x y := map_add (Sheaf.H.map (smulEnd X ℓ a) n) x y
  add_smul a b x := by
    change Sheaf.H.map (smulEnd X ℓ (a + b)) n x =
      Sheaf.H.map (smulEnd X ℓ a) n x + Sheaf.H.map (smulEnd X ℓ b) n x
    rw [smulEnd_add]; exact Sheaf.H.map_add_apply _ _ _
  zero_smul x := by
    change Sheaf.H.map (smulEnd X ℓ 0) n x = 0
    rw [smulEnd_zero]
    have h := Sheaf.H.map_add_apply (0 : F X ℓ ⟶ F X ℓ) 0 (x : (F X ℓ).H n)
    rw [add_zero] at h
    simpa using h


lemma smul_def {n : ℕ} (a : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ n) :
    a • x = Sheaf.H.map (smulEnd X ℓ a) n x := rfl

/-! ## Sanity check: `H⁰(X, ℤ_ℓ) = C(X, ℤ_ℓ)` as `ℤ_ℓ`-modules -/

/-- `X → X` is the terminal object of the pro-étale site of `X`. -/
noncomputable def terminalProEt : X.ProEt :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem _ X)

noncomputable def isTerminalProEt : IsTerminal (terminalProEt X) :=
  MorphismProperty.Over.mkIdTerminal @WeaklyEtale X

/-- **`H⁰(X, ℤ_ℓ) ≃ₗ[ℤ_ℓ] C(X, ℤ_ℓ)`.** The global sections of the coefficient sheaf, with
`ℤ_ℓ` acting by multiplication. This shows the module structure above is the expected one, and
that `EllAdicCohomology` is not trivially zero. -/
noncomputable def H0Equiv : X.EllAdicCohomology ℓ 0 ≃ₗ[ℤ_[ℓ]] C(X, ℤ_[ℓ]) where
  __ := (Sheaf.H.equiv₀ (F X ℓ) (isTerminalProEt X)).trans
    (AddEquiv.ulift : ULift.{u+1} C(X, ℤ_[ℓ]) ≃+ C(X, ℤ_[ℓ]))
  map_smul' a x := by
    change (show ULift.{u+1} C(X, ℤ_[ℓ]) from
        (Sheaf.H.equiv₀ (F X ℓ) (isTerminalProEt X)) (Sheaf.H.map (smulEnd X ℓ a) 0 x)).down
      = ContinuousMap.const X a *
        (show ULift.{u+1} C(X, ℤ_[ℓ]) from (Sheaf.H.equiv₀ (F X ℓ) (isTerminalProEt X)) x).down
    rw [← Sheaf.H.equiv₀_naturality]
    rfl

/-- `H⁰` of a nonempty scheme is a nonzero `ℤ_ℓ`-module. -/
lemma nontrivial_H0 [Nonempty X] : Nontrivial (X.EllAdicCohomology ℓ 0) :=
  (H0Equiv X ℓ).toEquiv.nontrivial

/-- The `ℤ_ℓ`-action on `H⁰` is the multiplication of functions. -/
lemma H0Equiv_smul (a : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ 0) :
    H0Equiv X ℓ (a • x) = ContinuousMap.const X a * H0Equiv X ℓ x :=
  (H0Equiv X ℓ).map_smul a x


end Coh

/-! ## Transport along scheme isomorphisms (for the Galois action) -/

section Transport

set_option backward.isDefEq.respectTransparency.types false

open Scheme Opposite

variable {X Y : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime]

/-- `π_X : X.ProEt ⥤ Scheme`, `(U → X) ↦ U`. -/
abbrev piX (X : Scheme.{u}) : X.ProEt ⥤ Scheme.{u} := Scheme.ProEt.forget X ⋙ Over.forget X

/-- **Lemma A.** A sieve on `U` in the small pro-étale site of `X` covers iff its image in
`Scheme` is a pro-étale covering sieve of `U.left`. -/
lemma mem_topology_iff {U : X.ProEt} (S : Sieve U) :
    S ∈ Scheme.ProEt.topology X U ↔ S.functorPushforward (piX X) ∈ proetaleTopology U.left := by
  have h2 : Scheme.ProEt.topology X =
      (Scheme.ProEt.forget X).restrictedTopology (proetaleTopology.over X) :=
    MorphismProperty.toGrothendieck_comap_forget_eq_restrictedTopology (P := @WeaklyEtale) (S := X)
      _ proetalePrecoverage_le_precoverage_weaklyEtale
  rw [h2, Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff,
    Sieve.functorPushforward_comp]
  rfl


/-- `WeaklyEtale` holds for isomorphisms. -/
lemma weaklyEtale_hom (e : X ≅ Y) : (@WeaklyEtale : MorphismProperty Scheme.{u}) e.hom :=
  (inferInstance : WeaklyEtale e.hom)

/-- The functor `X.ProEt ⥤ Y.ProEt`, `(U → X) ↦ (U → X → Y)`, for a scheme isomorphism `e`. -/
noncomputable def proEtMap (e : X ≅ Y) : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map ⊤ (weaklyEtale_hom e)

/-- The equivalence of small pro-étale sites induced by a scheme isomorphism. -/
noncomputable def proEtEquiv (e : X ≅ Y) : X.ProEt ≌ Y.ProEt :=
  CategoryTheory.Equivalence.mk (proEtMap e) (proEtMap e.symm)
    ((MorphismProperty.Over.mapId ⊤ X).symm ≪≫
      MorphismProperty.Over.mapComp ⊤ (weaklyEtale_hom e) (weaklyEtale_hom e.symm) (𝟙 X) (by simp))
    ((MorphismProperty.Over.mapComp ⊤ (weaklyEtale_hom e.symm) (weaklyEtale_hom e) (𝟙 Y)
      (by simp)).symm ≪≫ MorphismProperty.Over.mapId ⊤ Y)

instance (e : X ≅ Y) : (proEtEquiv e).inverse.IsDenseSubsite (Scheme.ProEt.topology Y)
    (Scheme.ProEt.topology X) where
  functorPushforward_mem_iff {U S} := by
    rw [mem_topology_iff, mem_topology_iff, ← Sieve.functorPushforward_comp]
    rfl

/-- The equivalence of categories of abelian sheaves on the pro-étale sites. -/
noncomputable def sheafEquiv (e : X ≅ Y) :
    Sheaf (Scheme.ProEt.topology X) Ab.{u+1} ≌ Sheaf (Scheme.ProEt.topology Y) Ab.{u+1} :=
  (proEtEquiv e).sheafCongr _ _ _

instance (e : X ≅ Y) : (sheafEquiv e).functor.Additive where
  map_add := by intros; apply Sheaf.hom_ext; rfl



/-- The sheaf equivalence carries the `ℓ`-adic coefficient sheaf of `X` to that of `Y`
(componentwise the identity of `ULift C(U, ℤ_ℓ)`). -/
noncomputable def ellIso (e : X ≅ Y) : (sheafEquiv e).functor.obj (F X ℓ) ≅ F Y ℓ :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- The sheaf equivalence carries constant sheaves to constant sheaves (uniqueness of left
adjoints of the global-sections functor). -/
noncomputable def constIso (e : X ≅ Y) (A : Ab.{u+1}) :
    (sheafEquiv e).functor.obj ((constantSheaf (Scheme.ProEt.topology X) Ab.{u+1}).obj A) ≅
      (constantSheaf (Scheme.ProEt.topology Y) Ab.{u+1}).obj A :=
  let hT' : IsTerminal ((proEtEquiv e).functor.obj (terminalProEt X)) :=
    (isTerminalProEt X).isTerminalObj _
  let adj1 := (constantSheafAdj (Scheme.ProEt.topology X) Ab.{u+1} (isTerminalProEt X)).comp
    (sheafEquiv e).toAdjunction
  let adj2 := constantSheafAdj (Scheme.ProEt.topology Y) Ab.{u+1} hT'
  let iso : (sheafEquiv e).inverse ⋙ (sheafSections _ _).obj (op (terminalProEt X)) ≅
      (sheafSections _ _).obj (op ((proEtEquiv e).functor.obj (terminalProEt X))) :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => by
      simp only [Iso.refl_hom]; rfl)
  (Adjunction.leftAdjointUniq (adj1.ofNatIsoRight iso) adj2).app A

/-- **Transport of `ℓ`-adic cohomology along a scheme isomorphism** `e : X ≅ Y`
(`e_* = (e⁻¹)^*`). -/
noncomputable def transport (e : X ≅ Y) (n : ℕ) :
    X.EllAdicCohomology ℓ n →+ Y.EllAdicCohomology ℓ n :=
  ((Abelian.Ext.mk₀ (constIso e _).inv).precomp _ (zero_add n)).comp
    (((Abelian.Ext.mk₀ (ellIso ℓ e).hom).postcomp _ (add_zero n)).comp
      ((sheafEquiv e).functor.mapExtAddHom _ _ n))

lemma ellIso_smulEnd (e : X ≅ Y) (a : ℤ_[ℓ]) :
    (sheafEquiv e).functor.map (smulEnd X ℓ a) ≫ (ellIso ℓ e).hom =
      (ellIso ℓ e).hom ≫ smulEnd Y ℓ a := by
  apply Sheaf.hom_ext; ext U : 2; rfl

/-- Transport is `ℤ_ℓ`-linear. -/
lemma transport_smul (e : X ≅ Y) (n : ℕ) (a : ℤ_[ℓ]) (x : X.EllAdicCohomology ℓ n) :
    transport ℓ e n (a • x) = a • transport ℓ e n x := by
  change (Abelian.Ext.mk₀ (constIso e _).inv).comp
      ((((x : (F X ℓ).H n).comp (Abelian.Ext.mk₀ (smulEnd X ℓ a)) (add_zero n)).mapExactFunctor
        (sheafEquiv e).functor).comp (Abelian.Ext.mk₀ (ellIso ℓ e).hom) (add_zero n)) (zero_add n) =
    ((Abelian.Ext.mk₀ (constIso e _).inv).comp
      (((x : (F X ℓ).H n).mapExactFunctor (sheafEquiv e).functor).comp
        (Abelian.Ext.mk₀ (ellIso ℓ e).hom) (add_zero n)) (zero_add n)).comp
      (Abelian.Ext.mk₀ (smulEnd Y ℓ a)) (add_zero n)
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, ellIso_smulEnd,
    ← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- Transport as a `ℤ_ℓ`-linear map. -/
noncomputable def transportₗ (e : X ≅ Y) (n : ℕ) :
    X.EllAdicCohomology ℓ n →ₗ[ℤ_[ℓ]] Y.EllAdicCohomology ℓ n where
  __ := transport ℓ e n
  map_smul' a x := transport_smul ℓ e n a x

end Transport

/-! ## T10 as a `ℤ_ℓ`-linear isomorphism -/

section AbVarSec

open PkgI3 MonoidalCategory CartesianMonoidalCategory MonObj

/-- **T10, `ℤ_ℓ`-linear form (textbook leaf; not yet Galois-equivariant).** For an abelian variety
`A` over a field `K` and a prime `ℓ ≠ char K`, `H¹(A_K̄, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)` as
`ℤ_ℓ`-modules, where `H¹` is Mathlib's pro-étale `ℓ`-adic cohomology with the module structure
`instModule…` above. A consequence of Milne 1986 (Cornell–Silverman), Thm 15.1(a)
(`H¹_et(A_K̄, ℤ_ℓ) ≅ Hom(T_ℓ A, ℤ_ℓ)`; UNVERIFIED number) and of the comparison of pro-étale and
classical `ℓ`-adic cohomology for schemes of finite type over an algebraically closed field
(Bhatt–Scholze 2015, §5.6; UNVERIFIED number), both `ℤ_ℓ`-linear. -/
def T10_linIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    Nonempty ((A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
      Module.Dual ℤ_[ℓ] (A.T ℓ))

/-- leaf-push2's group form (copied verbatim from scratch/leaf-push2/LeafPush2.lean). -/
def T10_groupIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    Nonempty ((A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃+
      Module.Dual ℤ_[ℓ] (A.T ℓ))

/-- The linear form implies leaf-push2's group form. -/
theorem T10_groupIso_of_linIso (h : T10_linIso) : T10_groupIso := by
  intro K _ A ℓ _ hℓ
  obtain ⟨e⟩ := h K A ℓ hℓ
  exact ⟨e.toAddEquiv⟩

/-- `T_ℓ` of the zero abelian variety is zero. -/
instance subsingleton_T_zero (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton ((AbVar.zero K).T ℓ) := by
  have : Subsingleton (Additive ((AbVar.zero K).Pt (AlgebraicClosure K))) :=
    ⟨fun P Q => CartesianMonoidalCategory.toUnit_unique (Additive.toMul P) (Additive.toMul Q)⟩
  constructor
  intro x y
  apply Subtype.ext
  funext n
  exact Subsingleton.elim _ _

/-- **Content check.** At the zero abelian variety `T10_linIso` says
`H¹_proet(Spec K̄ ×_K Spec K, ℤ_ℓ) = 0`: a true statement (`Spec K̄` is w-contractible,
Bhatt–Scholze 2015 §2.4; UNVERIFIED number) that is not provable from the definitions by
unfolding. -/
theorem T10_linIso_zero (h : T10_linIso) (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : (ℓ : K) ≠ 0) :
    Subsingleton (((AbVar.zero K).baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1) := by
  obtain ⟨e⟩ := h K (AbVar.zero K) ℓ hℓ
  exact e.toEquiv.subsingleton

/-! ## The Galois action on `H¹(A_K̄, ℤ_ℓ)` and the equivariant form of T10 -/

/-- `Spec K̄ → Spec K`. -/
noncomputable abbrev specAlg (K : Type) [Field K] :
    Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

/-- `Spec(σ) : Spec K̄ → Spec K̄`. -/
noncomputable def specAut {K : Type} [Field K] (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    Spec (CommRingCat.of (AlgebraicClosure K)) ⟶ Spec (CommRingCat.of (AlgebraicClosure K)) :=
  Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K))

lemma specAut_comp {K : Type} [Field K] (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    specAut σ ≫ specAlg K = specAlg K := by
  simp only [specAut, specAlg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp

lemma specAut_mul {K : Type} [Field K] (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    specAut (σ * τ) = specAut σ ≫ specAut τ := by
  simp only [specAut, ← Spec.map_comp]
  congr 1

lemma specAut_one {K : Type} [Field K] :
    specAut (1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) = 𝟙 _ := by
  rw [specAut, show CommRingCat.ofHom ((1 : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    AlgebraicClosure K →+* AlgebraicClosure K) = 𝟙 _ from by ext; rfl]
  exact Spec.map_id _

/-- `A_K̄ = A ×_K Spec K̄` as a scheme (definitionally `(A.baseChange K̄).X.left`). -/
noncomputable abbrev AKbar {K : Type} [Field K] (A : AbVar K) : Scheme :=
  pullback A.X.hom (specAlg K)

example {K : Type} [Field K] (A : AbVar K) : (A.baseChange (AlgebraicClosure K)).X.left = AKbar A :=
  rfl

/-- `1 × Spec(σ)` on `A_K̄ = A ×_K Spec K̄`. -/
noncomputable def galAut {K : Type} [Field K] (A : AbVar K)
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : AKbar A ⟶ AKbar A :=
  pullback.map A.X.hom (specAlg K) A.X.hom (specAlg K) (𝟙 _) (specAut σ) (𝟙 _)
    (by simp) (by rw [Category.comp_id, specAut_comp])

lemma galAut_mul {K : Type} [Field K] (A : AbVar K)
    (σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    galAut A (σ * τ) = galAut A σ ≫ galAut A τ := by
  simp only [galAut, pullback.map_comp, specAut_mul, Category.comp_id]

lemma galAut_one {K : Type} [Field K] (A : AbVar K) : galAut A 1 = 𝟙 _ := by
  simp only [galAut, specAut_one]
  exact pullback.map_id

/-- `1 × Spec(σ)` as an automorphism of the scheme `A_K̄`. -/
noncomputable def galIso {K : Type} [Field K] (A : AbVar K) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
    AKbar A ≅ AKbar A where
  hom := galAut A σ
  inv := galAut A σ⁻¹
  hom_inv_id := by rw [← galAut_mul, mul_inv_cancel, galAut_one]
  inv_hom_id := by rw [← galAut_mul, inv_mul_cancel, galAut_one]

/-- **The Galois action on `H¹(A_K̄, ℤ_ℓ)`**, by transport of structure: `σ` acts by `s_*`,
`s = 1 × Spec(σ⁻¹)` (`s_σ ∘ s_τ = s_{στ}`, so this is a left action once functoriality of
`transport` is proved). -/
noncomputable def galH {K : Type} [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K) :
    (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 →ₗ[ℤ_[ℓ]]
      (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 :=
  transportₗ ℓ (galIso A (σ⁻¹ : Field.absoluteGaloisGroup K)) 1

/-- **T10, Galois-equivariant form (textbook leaf).** For an abelian variety `A/K` and a prime
`ℓ ≠ char K` there is a `ℤ_ℓ`-linear isomorphism `φ : H¹(A_K̄, ℤ_ℓ) ≅ Hom_{ℤ_ℓ}(T_ℓ A, ℤ_ℓ)`
intertwining the Galois action `galH` on `H¹` with the contragredient action
`σ · f = f ∘ σ⁻¹` on the dual of `T_ℓ A` (`A.galT σ` acts on points by `P ↦ P ∘ Spec σ`).
Equivalently `V_ℓ(A) ≅ H¹(A_K̄, ℚ_ℓ)^∨` as `G_K`-representations after `⊗ ℚ_ℓ`.
A consequence of Milne 1986 (Cornell–Silverman), Thm 15.1(a) (UNVERIFIED number) and the
pro-étale/étale comparison (Bhatt–Scholze 2015 §5.6; UNVERIFIED number), both natural in the
scheme, hence compatible with transport along `1 × Spec(σ⁻¹)`. -/
def T10_TateDuality : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∃ φ : (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
        Module.Dual ℤ_[ℓ] (A.T ℓ),
      ∀ (σ : Field.absoluteGaloisGroup K) x,
        φ (galH A ℓ σ x) = (A.galT (ℓ := ℓ) σ⁻¹).dualMap (φ x)

theorem T10_linIso_of_tateDuality (h : T10_TateDuality) : T10_linIso := by
  intro K _ A ℓ _ hℓ
  obtain ⟨φ, -⟩ := h K A ℓ hℓ
  exact ⟨φ⟩

end AbVarSec

end T10Etale

#print axioms T10Etale.H0Equiv
#print axioms T10Etale.T10_groupIso_of_linIso
#print axioms T10Etale.T10_linIso_zero
#print axioms T10Etale.transport_smul
#print axioms T10Etale.galIso
#print axioms T10Etale.T10_linIso_of_tateDuality
