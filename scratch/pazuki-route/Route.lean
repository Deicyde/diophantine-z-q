import ZInQKernel.Contrib.OneProof.PazukiInputs
import ZInQKernel.Contrib.OneProof.PicLocFinType

/-!
# pazuki-route: the core `SymmPrincipalDefinedOver` reduced to two smaller statements

Task pazuki-route (2026-11-17), docs/research/pazuki-route.md. Development copy of
`ZInQKernel/Contrib/OneProof/PazukiRoute.lean`.

No `sorry`, no `axiom`.
-/

set_option linter.style.haveILetI false

noncomputable section

namespace PazukiRoute

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory MonObj Opposite
open AvSplit.HomLatticeAN3 (bcC)
open PazukiDict (IsSymmPrincipal specMap_comp_eq)
open PazukiInputs (bcMap bcMap' bcMap_isPullback)

/-! ## §1. `h⁰` through the structure field and along `bcMap` -/

variable {K K' : Type} [Field K] [Field K'] [Algebra K K']

section H0

open Scheme.Modules

/-- For a proper geometrically integral `k`-scheme, `dim_{Γ(X,𝒪)} Γ(X, M) = h⁰(X, M)` (over `k`): the constants
`k → Γ(X, 𝒪)` are bijective. -/
theorem finrank_Γ_eq_finrankH {k : Type} [Field k] {X : Scheme.{0}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [GeometricallyIntegral (X ↘ Spec (.of k))] (M : X.Modules) :
    Module.finrank Γ(X, ⊤) Γ(M, ⊤) = M.finrankH k 0 := by
  have hb : Function.Bijective (Scheme.globalSectionsRingHom k (X := X)) :=
    (bijective_appTop_of_isProper_of_geometricallyIntegral (X ↘ Spec (.of k))).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv)
  have hr := rank_eq_of_equiv_equiv (R := k) (R' := Γ(X, ⊤)) (M := M.H 0) (M₁ := M.H 0)
    (Scheme.globalSectionsRingHom k (X := X)) (AddEquiv.refl _) hb (fun c x => rfl)
  rw [← (H.zeroLinearEquiv M).finrank_eq]
  unfold finrankH Module.finrank
  rw [hr]

/-- `finrankH` only depends on the structure morphism. -/
theorem finrankH_congr_over {k : Type} [Field k] {X : Scheme.{0}} {f g : X ⟶ Spec (.of k)} (h : f = g)
    (M : X.Modules) (q : ℕ) :
    (letI : X.Over (Spec (.of k)) := ⟨f⟩; M.finrankH k q) =
      (letI : X.Over (Spec (.of k)) := ⟨g⟩; M.finrankH k q) := by
  subst h; rfl

/-- The cartesian square of `bcMap` as an isomorphism `A_ℂ ≅ A_{K'} ×_{K', σ'} ℂ`. -/
abbrev bcIso (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ) :
    (bcC A σ).X.left ≅ pullback (A.baseChange K').X.hom (Spec.map (CommRingCat.ofHom σ')) :=
  (bcMap_isPullback A σ σ' hσ).isoPullback

theorem bcIso_hom_fst (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) :
    (bcIso A σ σ' hσ).hom ≫ pullback.fst _ _ = bcMap A σ σ' hσ :=
  (bcMap_isPullback A σ σ' hσ).isoPullback_hom_fst

theorem bcIso_hom_snd (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) :
    (bcIso A σ σ' hσ).hom ≫ pullback.snd _ _ = (bcC A σ).X.hom :=
  (bcMap_isPullback A σ σ' hσ).isoPullback_hom_snd

/-- **`h⁰` along `bcMap` (proved, flat base change):** `dim Γ(A_ℂ, bcMap^* M) = dim Γ(A_{K'}, M)`, each over the
global functions of its scheme. -/
theorem finrank_bcMap (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ)
    (M : (A.baseChange K').X.left.Pic) :
    Module.finrank Γ((bcC A σ).X.left, ⊤)
        Γ((fromSkeleton (bcC A σ).X.left.Modules).obj (Scheme.Pic.map (bcMap A σ σ' hσ) M).val, ⊤) =
      Module.finrank Γ((A.baseChange K').X.left, ⊤)
        Γ((fromSkeleton (A.baseChange K').X.left.Modules).obj M.val, ⊤) := by
  let X' := (A.baseChange K').X.left
  let Y := (bcC A σ).X.left
  let N := (fromSkeleton X'.Modules).obj M.val
  let e := bcIso A σ σ' hσ
  let g := pullback.snd (A.baseChange K').X.hom (Spec.map (CommRingCat.ofHom σ'))
  letI iX : X'.Over (Spec (.of K')) := ⟨(A.baseChange K').X.hom⟩
  haveI : IsProper (X' ↘ Spec (.of K')) := inferInstanceAs (IsProper (A.baseChange K').X.hom)
  haveI : GeometricallyIntegral (X' ↘ Spec (.of K')) :=
    inferInstanceAs (GeometricallyIntegral (A.baseChange K').X.hom)
  haveI : QuasiCompact (X' ↘ Spec (.of K')) := inferInstanceAs (QuasiCompact (A.baseChange K').X.hom)
  haveI : QuasiSeparated (X' ↘ Spec (.of K')) := inferInstanceAs (QuasiSeparated (A.baseChange K').X.hom)
  -- the right side
  rw [finrank_Γ_eq_finrankH (k := K') N]
  -- the left side
  letI iY : Y.Over (Spec (.of ℂ)) := ⟨(bcC A σ).X.hom⟩
  haveI : IsProper (Y ↘ Spec (.of ℂ)) := inferInstanceAs (IsProper (bcC A σ).X.hom)
  haveI : GeometricallyIntegral (Y ↘ Spec (.of ℂ)) :=
    inferInstanceAs (GeometricallyIntegral (bcC A σ).X.hom)
  rw [finrank_Γ_eq_finrankH (k := ℂ)]
  let iE : (fromSkeleton Y.Modules).obj (Scheme.Pic.map (bcMap A σ σ' hσ) M).val ≅
      (Scheme.Modules.pullback (bcMap A σ σ' hσ)).obj N :=
    Scheme.Pic.mkIso ((Scheme.Modules.pullback (bcMap A σ σ' hσ)).obj N)
  rw [finrankH_congr ℂ iE]
  rw [← bcIso_hom_fst A σ σ' hσ]
  rw [finrankH_congr ℂ ((Scheme.Modules.pullbackComp e.hom (pullback.fst _ _)).app N).symm]
  have h1 := finrankH_pullback_of_isIso (k := ℂ) e.hom g
    ((Scheme.Modules.pullback (pullback.fst (A.baseChange K').X.hom
      (Spec.map (CommRingCat.ofHom σ')))).obj N) 0
  have h2 := finrankH_congr_over (bcIso_hom_snd A σ σ' hσ).symm
    ((Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback (pullback.fst (A.baseChange K').X.hom
      (Spec.map (CommRingCat.ofHom σ')))).obj N)) 0
  letI : Algebra K' ℂ := σ'.toAlgebra
  haveI : N.IsQuasicoherent := SheafOfModules.IsInvertible.isQuasicoherent M.isInvertible
  have h3 := finrankH_pullback (k := K') ℂ N 0
  exact h2.trans (h1.trans h3)

end H0

/-! ## §2. Ampleness descends along a field extension (LEAF) -/

/-- **LEAF (descent of ampleness along a field extension).** For a proper morphism `f : X → Spec k`, a field
extension `τ : k → k'` and `L ∈ Pic(X)`: if the pullback of `L` to `X_{k'} = X ×_k k'` is ample, then `L` is ample.
Published: EGA IV₂, Cor. 2.7.2 (descent of `f`-ampleness along a faithfully flat quasi-compact base change, here
`Spec k' → Spec k`), with EGA II 4.6.6 (over an affine base, `f`-ample is ample, the sense of `T09Pic.IsAmple`,
Stacks 01PS); locators UNVERIFIED. Restricted to proper `f` (the print only needs `f` quasi-compact). -/
def AmpleDescendsFieldExt : Prop :=
  ∀ (k k' : Type) [Field k] [Field k'] (τ : k →+* k') (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)),
    IsProper f → ∀ L : X.Pic,
      T09Pic.IsAmple (pullback f (Spec.map (CommRingCat.ofHom τ)))
        (Scheme.Pic.map (pullback.fst f (Spec.map (CommRingCat.ofHom τ))) L) →
      T09Pic.IsAmple X L

/-- Ampleness along `bcMap` descends (from the leaf and the isomorphism `bcIso`). -/
theorem isAmple_of_bcMap (hA : AmpleDescendsFieldExt) (A : PkgI3.AbVar K) (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    (hσ : σ'.comp (algebraMap K K') = σ) (M : (A.baseChange K').X.left.Pic)
    (h : T09Pic.IsAmple (bcC A σ).X.left (Scheme.Pic.map (bcMap A σ σ' hσ) M)) :
    T09Pic.IsAmple (A.baseChange K').X.left M := by
  refine hA K' ℂ σ' _ (A.baseChange K').X.hom inferInstance M ?_
  have h' := PazukiAlg.isAmple_map (bcIso A σ σ' hσ).inv _ h
  rw [← bcIso_hom_fst A σ σ' hσ, Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, Iso.inv_hom_id,
    Scheme.Pic.map_id] at h'
  exact h'

/-! ## §3. The class-level core and the reduction of `SymmPrincipalDefinedOver` -/

/-- **GLUE (composite; the class-level core).** For an abelian variety `A` over a number field `K`, `σ : K → ℂ` and
a symmetric principal polarization `L` of `A_ℂ`, there are a number field `K'`, `σ' : K' → ℂ` over `σ` and a
*symmetric* class `M ∈ Pic(A_{K'})` with `bcMap^* M = L`. This is `PazukiInputs.SymmPrincipalDefinedOver` without
the ampleness and `h⁰` of `M` (they descend: `symmPrincipalDefinedOver_of_class`). Reduced below
(`symmClassDefinedOver_of_countable`) to `SymmetricClassesCountable` and `CountablePointsDefinedOver`. -/
def SymmClassDefinedOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ) (L : (bcC A σ).X.left.Pic),
    IsSymmPrincipal (bcC A σ) L →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (σ' : K' →+* ℂ)
      (hσ : σ'.comp (algebraMap K K') = σ) (M : (A.baseChange K').X.left.Pic),
      Scheme.Pic.map (GrpObj.inv (X := (A.baseChange K').X)).left M = M ∧
        Scheme.Pic.map (bcMap A σ σ' hσ) M = L

/-- **Glue (proved): `SymmPrincipalDefinedOver` from the class-level core and the descent of ampleness.** `h⁰`
descends by flat base change (`finrank_bcMap`). -/
theorem symmPrincipalDefinedOver_of_class (hC : SymmClassDefinedOver) (hA : AmpleDescendsFieldExt) :
    PazukiInputs.SymmPrincipalDefinedOver := by
  intro K _ _ A σ L hL
  obtain ⟨K', iF, iN, iA, σ', hσ, M, hsym, rfl⟩ := hC K A σ L hL
  refine ⟨K', iF, iN, iA, σ', hσ, M, ⟨isAmple_of_bcMap hA A σ σ' hσ M hL.1, hsym, ?_⟩, rfl⟩
  rw [← finrank_bcMap A σ σ' hσ M]
  exact hL.2.2

/-! ## §4. The class-level core from countability of the symmetric classes -/

/-- **GLUE (composite; Néron–Severi and `Pic⁰[2]`): the symmetric classes of `A_ℂ` form a countable set.** For an
abelian variety `A` over a number field `K` and `σ : K → ℂ`, the classes `L ∈ Pic(A_ℂ)` with `[-1]^*L ≅ L` are
countably many. Why true (locators UNVERIFIED): `L ↦ φ_L` maps `Pic(A_ℂ)` to `Hom(A_ℂ, Â_ℂ)`, which is free of
finite rank (Mumford, *Abelian varieties*, §19, Thm 3), with kernel `Pic⁰(A_ℂ)` (Mumford §8); a symmetric class in
`Pic⁰` is `2`-torsion (`[-1]^* = (·)⁻¹` on `Pic⁰`, Mumford §8 (iv)), and `Pic⁰(A_ℂ)[2] = Â[2](ℂ)` is finite (§4,
Application 2). So the symmetric classes with a given `φ_L` are finitely many. Not one printed theorem. -/
def SymmetricClassesCountable : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ),
    Set.Countable {L : (bcC A σ).X.left.Pic | Scheme.Pic.map (GrpObj.inv (X := (bcC A σ).X)).left L = L}

/-- **GLUE (algebraic geometry; no literature input): a scheme locally of finite type over a number field with
countably many complex points has all its complex points defined over number fields.** For `Z` locally of finite
type over a number field `K` and `σ : K → ℂ`, if the `ℂ`-points of `Z` over `σ` are countably many, every such point
`x` factors as `Spec ℂ → Spec K' → Z` through a number field `K'` with `σ' : K' → ℂ` over `σ`. Why true: the image
of `x` is a point `z` with residue field `κ(z)` finitely generated over `K`; if `κ(z)` had positive transcendence
degree, the `K`-embeddings `κ(z) → ℂ` over `σ` would be uncountably many (`ℂ` has uncountable transcendence degree
over the countable field `σ(K)`), each giving a different complex point of `Z`; so `κ(z)` is algebraic, hence
finite over `K`, and `x` factors through `Spec κ(z)`. -/
def CountablePointsDefinedOver : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (Z : Over (Spec (CommRingCat.of K))),
    LocallyOfFiniteType Z.hom →
    Set.Countable {x : Spec (CommRingCat.of ℂ) ⟶ Z.left | x ≫ Z.hom = Spec.map (CommRingCat.ofHom σ)} →
    ∀ x : Spec (CommRingCat.of ℂ) ⟶ Z.left, x ≫ Z.hom = Spec.map (CommRingCat.ofHom σ) →
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (σ' : K' →+* ℂ)
      (_ : σ'.comp (algebraMap K K') = σ) (y : Spec (CommRingCat.of K') ⟶ Z.left),
      y ≫ Z.hom = Spec.map (CommRingCat.ofHom (algebraMap K K')) ∧
        x = Spec.map (CommRingCat.ofHom σ') ≫ y

section Compose

open T09Pic PicDict PkgI3

/-- The `K`-scheme `Spec F` for `τ : K → F`. -/
abbrev ptOf {F : Type} [Field F] (τ : K →+* F) : Over (Spec (CommRingCat.of K)) :=
  Over.mk (Spec.map (CommRingCat.ofHom τ))

/-- Over a field point every class is normalized (`Pic(Spec F)` is trivial). -/
theorem mem_nrm {F : Type} [Field F] (A : AbVar K) (τ : K →+* F)
    (c : (pullback A.X.hom (ptOf τ).hom).Pic) : c ∈ (Nrm A).obj (op (ptOf τ)) := by
  change Scheme.Pic.map _ c = 1
  exact Subsingleton.elim (α := (Spec (CommRingCat.of F)).Pic) _ _

/-- Kleiman 9.2.5 at a field point: classes on `A_F` inject into the Picard sheaf. -/
theorem toPic_injective {F : Type} [Field F] (A : AbVar K) (τ : K →+* F) :
    Function.Injective ((toPicardFunctor A.X.hom).app (op (ptOf τ))) := by
  intro c d h
  have := Θ_inj pushforwardUnitUniversal (A := A) (x := ⟨c, mem_nrm A τ c⟩) (y := ⟨d, mem_nrm A τ d⟩) h
  exact congrArg Subtype.val this

/-- Kleiman 9.2.5 at a field point: every element of the Picard sheaf is a class on `A_F`. -/
theorem toPic_surjective {F : Type} [Field F] (A : AbVar K) (τ : K →+* F) :
    Function.Surjective ((toPicardFunctor A.X.hom).app (op (ptOf τ))) := by
  intro e
  obtain ⟨x, hx⟩ := ((Θ A pushforwardUnitUniversal).app (op (ptOf τ))).toEquiv.surjective e
  exact ⟨x.1, hx⟩

/-- `[-1] × id` on `A ×_K F` is the inverse of the base change `A_F`. -/
theorem famMap_inv_eq (A : AbVar K) (F : Type) [Field F] [Algebra K F] :
    famMap (GrpObj.inv (X := A.X)) (ptOf (algebraMap K F)) = (GrpObj.inv (X := (A.baseChange F).X)).left := by
  have e : (GrpObj.inv (X := (A.baseChange F).X)) =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K F)))).map (GrpObj.inv (X := A.X)) := rfl
  rw [e]
  apply pullback.hom_ext <;> simp [Over.pullback, famMap]

/-- `bcMap` is the base-change map of `Spec σ' : Spec ℂ → Spec K'`. -/
theorem bcMap_eq_baseChangeMap {K' : Type} [Field K'] [Algebra K K'] (A : AbVar K) (σ : K →+* ℂ)
    (σ' : K' →+* ℂ) (hσ : σ'.comp (algebraMap K K') = σ) :
    JacobianChallenge.baseChangeMap A.X.hom
        (Over.homMk (Spec.map (CommRingCat.ofHom σ')) (specMap_comp_eq σ σ' hσ) :
          ptOf σ ⟶ ptOf (algebraMap K K')) = bcMap A σ σ' hσ := by
  apply pullback.hom_ext <;> simp [JacobianChallenge.baseChangeMap, bcMap, bcMap']

/-- The class of `f^* c` is `f^∨` of the class of `c`. -/
theorem homEquiv_symm_famMap {P : Over (Spec (CommRingCat.of K))} {A : AbVar K}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (f : A.X ⟶ A.X) {T : Over (Spec (CommRingCat.of K))}
    (c : (pullback A.X.hom T.hom).Pic) :
    rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T) c) ≫ dualP rep f =
      rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op T) (Scheme.Pic.map (famMap f T) c)) := by
  rw [comp_dualP, Equiv.apply_symm_apply]
  congr 1
  have h := congrArg (fun τ => τ.app (op T) c) (toPicardFunctor_comp_dualSheafMap f)
  simp only [NatTrans.comp_app] at h
  exact h

/-- **Glue (proved): the class-level core from the two statements above** and the representability of the Picard
functor (`PicRepresentableAbVar`, an existing LEAF field). The symmetric locus `Z = {x ∈ P : [-1]^∨ x = x}` of the
Picard scheme `P` is locally of finite type (`picLocFinType_proof`); its complex points are the symmetric classes
of `A_ℂ` (Kleiman 9.2.5, `pushforwardUnitUniversal`), countably many; so the point of `L` comes from a `K'`-point of
`Z`, i.e. from a symmetric class on `A_{K'}`. -/
theorem symmClassDefinedOver_of_countable (hRep : PicRepresentableAbVar) (hS : SymmetricClassesCountable)
    (hC : CountablePointsDefinedOver) : SymmClassDefinedOver := by
  intro K _ _ A σ L hL
  obtain ⟨P, ⟨rep⟩⟩ := hRep K A
  haveI hLFT : LocallyOfFiniteType P.hom := PicLFT.picLocFinType_proof K A P rep
  let iv : P ⟶ P := dualP rep (GrpObj.inv (X := A.X))
  let l : P.left ⟶ pullback P.hom P.hom := pullback.lift (𝟙 _) iv.left (by simp)
  let d : P.left ⟶ pullback P.hom P.hom := pullback.diagonal P.hom
  let q : pullback l d ⟶ P.left := pullback.fst l d
  let Z : Over (Spec (CommRingCat.of K)) := Over.mk (q ≫ P.hom)
  have hfix : q ≫ iv.left = q := by
    have h := pullback.condition (f := l) (g := d)
    have h1 := congrArg (· ≫ pullback.fst P.hom P.hom) h
    have h2 := congrArg (· ≫ pullback.snd P.hom P.hom) h
    simp only [Category.assoc, l, d, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd, Category.comp_id] at h1 h2
    rw [h2, ← h1]
  haveI : LocallyOfFiniteType d := by
    haveI : LocallyOfFiniteType (d ≫ pullback.fst P.hom P.hom) := by
      rw [pullback.diagonal_fst]; infer_instance
    exact locallyOfFiniteType_of_comp d (pullback.fst P.hom P.hom)
  haveI : LocallyOfFiniteType Z.hom := by
    change LocallyOfFiniteType (q ≫ P.hom); infer_instance
  -- the point of a class over a field point
  let pt : ∀ {F : Type} [Field F] (τ : K →+* F), (pullback A.X.hom (ptOf τ).hom).Pic → (ptOf τ ⟶ P) :=
    fun τ c => rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op (ptOf τ)) c)
  -- `L` as a class on `A ×_K Spec ℂ`
  let L₀ : (pullback A.X.hom (ptOf σ).hom).Pic := L
  have hLsym : Scheme.Pic.map (famMap (GrpObj.inv (X := A.X)) (ptOf σ)) L₀ = L₀ := by
    letI := σ.toAlgebra
    have h := famMap_inv_eq A ℂ
    exact (congrArg (fun f => Scheme.Pic.map f L₀) h).trans hL.2.1
  have hxL : pt σ L₀ ≫ iv = pt σ L₀ :=
    (homEquiv_symm_famMap rep _ L₀).trans
      (congrArg (fun c => rep.homEquiv.symm ((toPicardFunctor A.X.hom).app (op (ptOf σ)) c)) hLsym)
  have hxL' : (pt σ L₀).left ≫ l = (pt σ L₀).left ≫ d := by
    apply pullback.hom_ext
    · simp [l, d]
    · simp only [Category.assoc, l, d, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      rw [← Over.comp_left, hxL]
  let z : Spec (CommRingCat.of ℂ) ⟶ Z.left := pullback.lift (pt σ L₀).left (pt σ L₀).left hxL'
  have hz : z ≫ Z.hom = Spec.map (CommRingCat.ofHom σ) := by
    change pullback.lift _ _ hxL' ≫ q ≫ P.hom = _
    rw [← Category.assoc, pullback.lift_fst]
    exact Over.w (pt σ L₀)
  -- the complex points of `Z` are countably many
  let S := {x : Spec (CommRingCat.of ℂ) ⟶ Z.left | x ≫ Z.hom = Spec.map (CommRingCat.ofHom σ)}
  have hmk : ∀ x ∈ S, (x ≫ q) ≫ P.hom = (ptOf σ).hom := fun x hx => by
    rw [Category.assoc]; exact hx
  have hpt : ∀ x (hx : x ∈ S), ∃ c : (pullback A.X.hom (ptOf σ).hom).Pic,
      pt σ c = Over.homMk (U := ptOf σ) (V := P) (x ≫ q) (hmk x hx) := by
    intro x hx
    obtain ⟨c, hc⟩ := toPic_surjective A σ (rep.homEquiv (Over.homMk (U := ptOf σ) (V := P) (x ≫ q) (hmk x hx)))
    exact ⟨c, by simp only [pt, hc, Equiv.symm_apply_apply]⟩
  have hcount : S.Countable := by
    classical
    let cls : (Spec (CommRingCat.of ℂ) ⟶ Z.left) → (pullback A.X.hom (ptOf σ).hom).Pic := fun x =>
      if hx : x ∈ S then (hpt x hx).choose else 1
    have hsymS : ∀ x ∈ S, Scheme.Pic.map (famMap (GrpObj.inv (X := A.X)) (ptOf σ)) (cls x) = cls x := by
      intro x hx
      have hc := (hpt x hx).choose_spec
      simp only [cls, hx, ↓reduceDIte]
      apply toPic_injective A σ
      apply rep.homEquiv.symm.injective
      refine (homEquiv_symm_famMap rep _ _).symm.trans ?_
      change pt σ _ ≫ iv = pt σ _
      rw [hc]
      ext1
      simp only [Over.comp_left, Over.homMk_left, Category.assoc, hfix]
    refine Set.MapsTo.countable_of_injOn (f := cls) (t := {L : (bcC A σ).X.left.Pic |
      Scheme.Pic.map (GrpObj.inv (X := (bcC A σ).X)).left L = L}) ?_ ?_ (hS K A σ)
    · intro x hx
      letI := σ.toAlgebra
      have h := famMap_inv_eq A ℂ
      exact (congrArg (fun f => Scheme.Pic.map f (cls x)) h).symm.trans (hsymS x hx)
    · intro x hx y hy hxy
      have hcx := (hpt x hx).choose_spec
      have hcy := (hpt y hy).choose_spec
      simp only [cls, hx, hy, ↓reduceDIte] at hxy
      rw [hxy] at hcx
      have := congrArg CommaMorphism.left (hcx.symm.trans hcy)
      simp only [Over.homMk_left] at this
      exact (cancel_mono q).1 this
  -- descend
  obtain ⟨K', iF, iN, iA, σ', hσ, y, hy, hzy⟩ := hC K σ Z inferInstance hcount z hz
  have hy' : (y ≫ q) ≫ P.hom = (ptOf (algebraMap K K')).hom := by rw [Category.assoc]; exact hy
  let y' : ptOf (algebraMap K K') ⟶ P := Over.homMk (y ≫ q) hy'
  obtain ⟨M, hM⟩ := toPic_surjective A (algebraMap K K') (rep.homEquiv y')
  have hMy : pt (algebraMap K K') M = y' := by simp only [pt, hM, Equiv.symm_apply_apply]
  refine ⟨K', iF, iN, iA, σ', hσ, M, ?_, ?_⟩
  · have h := famMap_inv_eq A K'
    refine (congrArg (fun f => Scheme.Pic.map f M) h).symm.trans ?_
    apply toPic_injective A (algebraMap K K')
    apply rep.homEquiv.symm.injective
    refine (homEquiv_symm_famMap rep _ _).symm.trans ?_
    change pt _ M ≫ iv = pt _ M
    rw [hMy]
    ext1
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, y', hfix]
  · let g : ptOf σ ⟶ ptOf (algebraMap K K') :=
      Over.homMk (Spec.map (CommRingCat.ofHom σ')) (specMap_comp_eq σ σ' hσ)
    have h1 : g ≫ pt (algebraMap K K') M = pt σ L₀ := by
      rw [hMy]
      ext1
      simp only [Over.comp_left, Over.homMk_left, g, y', ← Category.assoc, ← hzy, z]
      exact pullback.lift_fst _ _ _
    have h2 : Scheme.Pic.map (JacobianChallenge.baseChangeMap A.X.hom g) M = L₀ := by
      apply toPic_injective A σ
      apply rep.homEquiv.symm.injective
      exact (comp_classify rep g _).symm.trans h1
    have h3 := bcMap_eq_baseChangeMap A σ σ' hσ
    exact (congrArg (fun f => Scheme.Pic.map f M) h3).symm.trans h2

end Compose

/-! ## §5. The field -/

/-- `PazukiInputs.SymmPrincipalDefinedOver` from the two smaller statements, the descent of ampleness and the
existing field `PicRepresentableAbVar`. -/
theorem symmPrincipalDefinedOver_of_route (hRep : T09Pic.PicRepresentableAbVar) (hA : AmpleDescendsFieldExt)
    (hS : SymmetricClassesCountable) (hC : CountablePointsDefinedOver) :
    PazukiInputs.SymmPrincipalDefinedOver :=
  symmPrincipalDefinedOver_of_class (symmClassDefinedOver_of_countable hRep hS hC) hA

/-- **Main theorem: the field `pazukiCor13Upper`** from the existing fields `GAGAMorphism` and
`PicRepresentableAbVar`, Pazuki's printed corollary for algebraic `(A, L)` (`PazukiCor13UpperPP`, LEAF), Riemann's
theorem for `Ω ∈ 𝔥₂` (`RiemannPPAV`, composite), the descent of ampleness (`AmpleDescendsFieldExt`, LEAF), the
countability of symmetric classes (`SymmetricClassesCountable`, composite) and the countable-points lemma
(`CountablePointsDefinedOver`, algebraic-geometry glue). -/
theorem pazukiCor13Upper_of_route (hG : ZInQ.HomLattice.GAGAMorphism) (hP : PazukiDict.PazukiCor13UpperPP)
    (hR : PazukiAlg.RiemannPPAV) (hRep : T09Pic.PicRepresentableAbVar) (hA : AmpleDescendsFieldExt)
    (hS : SymmetricClassesCountable) (hC : CountablePointsDefinedOver) :
    ZInQ.HeightSplit.PazukiCor13Upper :=
  PazukiInputs.pazukiCor13Upper_of_definedOver hG hP hR (symmPrincipalDefinedOver_of_route hRep hA hS hC)

end PazukiRoute
