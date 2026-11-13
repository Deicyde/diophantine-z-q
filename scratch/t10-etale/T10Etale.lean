import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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

end AbVarSec

end T10Etale

#print axioms T10Etale.H0Equiv
#print axioms T10Etale.T10_groupIso_of_linIso
#print axioms T10Etale.T10_linIso_zero
