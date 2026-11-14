import ZInQKernel.OneProof.H.TailE
import ZInQKernel.Contrib.Dim.HodgeLattice
import ZInQKernel.Contrib.HodgeBC2.ExtFrac
import ZInQKernel.Contrib.TwistDescent.GaloisDescent
import ZInQKernel.Contrib.FrobPieces.SmoothGeomConnIntegral
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Maximal
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Unramified.Existence
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.InertiaDegree
import ZInQKernel.Contrib.TauCeti.NumberTheory.LocalField.Padic
import ZInQKernel.OneProof.H.LF3Cot
import ZInQKernel.Contrib.HeightBC.HodgeBCInjective
import ZInQKernel.Contrib.HeightBC.OmegaBC
import ZInQKernel.Contrib.FrobChain.LinkedStatement

-- op-compact: aliases `HDec.T.x := T.x` for the copies deleted by op-dedupe (first used here)
namespace HDec.ZInQ export _root_.ZInQ (HeightBC.FF HeightBC.OmegaLocalization HeightBC.algebraMap_FF HeightBC.algebraMap_ringOfIntegers_coe HeightBC.bcCotBasis HeightBC.bcCotBasis.congr_simp HeightBC.bcCotBasis_apply HeightBC.bcCot_core HeightBC.bcCot_linearIndependent HeightBC.bcCot_smulL HeightBC.bcCot_smul_genStalk HeightBC.bcCot_span HeightBC.bcMap_φL HeightBC.cotL HeightBC.cotL_isScalarTower HeightBC.cotL_smul HeightBC.exists_act HeightBC.exists_mem_not_mem_of_sat HeightBC.finite_of_isClosed_not_genericPt HeightBC.genericPt_eq_genericPoint HeightBC.hodgeBCInjective HeightBC.hom_genericUnit' HeightBC.hom_unitSection HeightBC.locSub HeightBC.mapCotangent_injective_of_isIso HeightBC.mapCotangent_smul' HeightBC.mem_locSub HeightBC.mem_of_forall_locSub HeightBC.omegaAt_bc_local HeightBC.omegaAt_full HeightBC.omegaAt_open HeightBC.omegaAt_sat HeightBC.omegaBaseChange HeightBC.omegaBaseChange_of_localization HeightBC.omegaLocalization HeightBC.spec_mem_of_ker HeightBC.stalkMapAt_germ' HeightBC.stalkSpec_comp_apply HeightBC.stalkSpec_self_apply HeightBC.structMap_eq_spec HeightBC.toCotangent_mul HeightBC.unitSection_stalkMapAt_hom HeightBC.σFF HeightBC.φL HeightBC.φL_algebraMap) end HDec.ZInQ
namespace HDec.UnramTate export _root_.UnramTate (tmOf) end HDec.UnramTate

namespace HDec

-- op-compact: these names are not aliased by `export` (an alias would shadow a declared `HDec` name)
open _root_.ZInQ (Contrib.AbVarBC.G0FibreSimple.MulIsogeny Contrib.AbVarBC.MulRigidity.CotangentMulN Contrib.AbVarBC.MulRigidity.KerUnitOpen Contrib.AbVarBC.MulRigidity.KerUnitOpenOfCotangentSurj Contrib.AbVarBC.MulRigidity.MulEtale Contrib.AbVarBC.MulRigidity.MulUnramified Contrib.AbVarBC.MulRigidity.O0 Contrib.AbVarBC.MulRigidity.QuasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.charZero_residueField Contrib.AbVarBC.MulRigidity.cotangentMap Contrib.AbVarBC.MulRigidity.diagonal_isPullback Contrib.AbVarBC.MulRigidity.diffKer Contrib.AbVarBC.MulRigidity.formallyUnramified_of_kerUnit Contrib.AbVarBC.MulRigidity.isIsogenyMor_of_lqf_of_isOpenMap Contrib.AbVarBC.MulRigidity.isOpenImmersion_of_section Contrib.AbVarBC.MulRigidity.isProper_left Contrib.AbVarBC.MulRigidity.kerUnit Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_cotangent Contrib.AbVarBC.MulRigidity.kerUnitOpen_of_mulEtale Contrib.AbVarBC.MulRigidity.locallyQuasiFinite_of_formallyUnramified Contrib.AbVarBC.MulRigidity.map_origin Contrib.AbVarBC.MulRigidity.mulIsogeny_of_cotangent Contrib.AbVarBC.MulRigidity.mulIsogeny_of_kerUnitOpen Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulEtale Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified Contrib.AbVarBC.MulRigidity.mulIsogeny_of_mulUnramified' Contrib.AbVarBC.MulRigidity.mulUnramified_of_kerUnitOpen Contrib.AbVarBC.MulRigidity.mulUnramified_of_mulEtale Contrib.AbVarBC.MulRigidity.ne_of_specializes_of_lqf Contrib.AbVarBC.MulRigidity.origin Contrib.AbVarBC.MulRigidity.quasiFiniteEndSurjective Contrib.AbVarBC.MulRigidity.stalkEndo Contrib.AbVarBC.MulRigidity.surjective_of_lqf_self) -- op-dedupe

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

section G0A2_c10_burnside
-- (leaf-fold3) scratch/g0-assemble3/parts/d10_burnside.lean verbatim (rv-gluepieces2 checks/c11_burnside.lean)
-- (g0-assemble3: scratch/rv-gluepieces2/checks/c11_burnside.lean, verbatim minus its #print line: BurnsideAbsIrred proved from Mathlib)
/-! ## rv-gluepieces2 check (k): field 15 (`BurnsideAbsIrred`, a claimed textbook leaf) PROVED from Mathlib
(Schur's lemma `IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed` and Jacobson density
`Module.Finite.toModuleEnd_moduleEnd_surjective`, then a dimension count after base change to
`AlgebraicClosure F`). Body of scratch/rv-gluepieces2/Burnside.lean, then the bridge. -/


/-! # rv-gluepieces2: Burnside's theorem over an algebraically closed field (scratch)

Step 1 of a proof of `G0Galois.BurnsideAbsIrred` from Mathlib (Schur + Jacobson density). -/

namespace RvBurnside

open Module

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The subalgebra of `End_k V` generated by a set `T`; `V` is a module over it. -/
abbrev Alg (T : Set (Module.End k V)) : Subalgebra k (Module.End k V) := Algebra.adjoin k T

/-- A `k`-subspace stable under every element of `T` is stable under `Alg T`. -/
theorem mem_of_stable (T : Set (Module.End k V)) (p : Submodule k V)
    (hp : ∀ t ∈ T, ∀ v ∈ p, t v ∈ p) : ∀ s ∈ Alg T, ∀ v ∈ p, s v ∈ p := by
  intro s hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx => exact hp x hx
  | algebraMap r => intro v hv; simpa using p.smul_mem r hv
  | add x y _ _ hx hy => intro v hv; simpa using p.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy => intro v hv; exact hx _ (hy v hv)

/-- **Burnside over an algebraically closed field.** If the only `T`-stable subspaces of the
finite-dimensional nonzero `V` are `⊥` and `⊤`, then `T` generates `End_k V` as a `k`-algebra. -/
theorem adjoin_eq_top_of_algClosed [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
    (T : Set (Module.End k V))
    (hirr : ∀ p : Submodule k V, (∀ t ∈ T, ∀ v ∈ p, t v ∈ p) → p = ⊥ ∨ p = ⊤) :
    Alg T = ⊤ := by
  set S := Alg T
  haveI : IsSimpleModule S V := by
    rw [isSimpleModule_iff]
    haveI : Nontrivial (Submodule S V) := (Submodule.nontrivial_iff S).mpr inferInstance
    refine ⟨fun N => ?_⟩
    rcases hirr (N.restrictScalars k) (fun t ht v hv => by
        have : (⟨t, Algebra.subset_adjoin ht⟩ : S) • v ∈ N := N.smul_mem _ hv
        exact this) with h | h
    · left
      ext v
      have := congrArg (fun q : Submodule k V => v ∈ q) h
      simpa using this
    · right
      ext v
      have := congrArg (fun q : Submodule k V => v ∈ q) h
      simpa using this
  haveI : Module.Finite (Module.End S V) V := Module.Finite.of_restrictScalars_finite k _ V
  have hsurj := Module.Finite.toModuleEnd_moduleEnd_surjective (R := S) (M := V)
  have hschur := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k (A := S) (V := V)).2
  rw [eq_top_iff]
  intro f _
  have hcomm : ∀ (e : Module.End S V) (v : V), f (e v) = e (f v) := by
    intro e v
    obtain ⟨c, hc⟩ := hschur e
    rw [← hc]
    simp [Module.algebraMap_end_apply]
  let f' : Module.End (Module.End S V) V :=
    { toFun := f, map_add' := f.map_add, map_smul' := fun e v => hcomm e v }
  obtain ⟨s, hs⟩ := hsurj f'
  have hsf : (s : Module.End k V) = f := by
    ext v
    exact congrArg (fun φ : Module.End (Module.End S V) V => φ v) hs
  rw [← hsf]
  exact s.2

open TensorProduct
open scoped Pointwise

/-- **Step 2 (descent).** If the base changes `t_{F'}` (`t ∈ T`) to an algebraically closed `F'`
have only trivial common invariant subspaces, then `T` generates `End_F W`. -/
theorem adjoin_eq_top_of_baseChange {F : Type*} [Field F] {W : Type*} [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] (F' : Type*) [Field F'] [Algebra F F'] [IsAlgClosed F']
    (T : Set (Module.End F W)) [Nontrivial (F' ⊗[F] W)]
    (hirr : ∀ p : Submodule F' (F' ⊗[F] W),
      (∀ t ∈ T, ∀ v ∈ p, t.baseChange F' v ∈ p) → p = ⊥ ∨ p = ⊤) :
    Algebra.adjoin F T = ⊤ := by
  set S := Algebra.adjoin F T
  set T' : Set (Module.End F' (F' ⊗[F] W)) := (fun t => t.baseChange F') '' T
  have h1 : Algebra.adjoin F' T' = ⊤ := adjoin_eq_top_of_algClosed T' (by
    intro p hp
    apply hirr p
    intro t ht v hv
    exact hp _ ⟨t, ht, rfl⟩ v hv)
  set Sb : Set (Module.End F' (F' ⊗[F] W)) :=
    (fun s : Module.End F W => s.baseChange F') '' (S : Set (Module.End F W))
  set U := Submodule.span F' Sb
  have hSb : Sb * Sb ⊆ Sb := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨x * y, S.mul_mem hx hy, ?_⟩
    simp only [Module.End.mul_eq_comp, LinearMap.baseChange_comp]
  have hmul : ∀ x ∈ U, ∀ y ∈ U, x * y ∈ U := by
    intro x hx y hy
    have : x * y ∈ U * U := Submodule.mul_mem_mul hx hy
    rw [Submodule.span_mul_span] at this
    exact Submodule.span_mono hSb this
  have hone : (1 : Module.End F' (F' ⊗[F] W)) ∈ U :=
    Submodule.subset_span ⟨1, S.one_mem, by simp [Module.End.one_eq_id, LinearMap.baseChange_id]⟩
  have hle : ∀ x ∈ Algebra.adjoin F' T', x ∈ U := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact Submodule.subset_span ⟨t, Algebra.subset_adjoin ht, rfl⟩
    | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact U.smul_mem r hone
    | add x y _ _ hx hy => exact U.add_mem hx hy
    | mul x y _ _ hx hy => exact hmul x hx y hy
  have hU : U = ⊤ := eq_top_iff.mpr fun x _ => hle x (h1 ▸ Algebra.mem_top)
  -- dimension count
  let b := Module.finBasis F S
  let ψ : S →ₗ[F] Module.End F' (F' ⊗[F] W) :=
    ((LinearMap.baseChangeHom F F' W W).restrictScalars F) ∘ₗ S.toSubmodule.subtype
  have hspan : U ≤ Submodule.span F' (Set.range fun i => ψ (b i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ψ ⟨x, hx⟩ ∈ Submodule.span F (Set.range fun i => ψ (b i)) := by
      have := Submodule.mem_map_of_mem (f := ψ) (b.mem_span ⟨x, hx⟩)
      rwa [Submodule.map_span, ← Set.range_comp] at this
    exact Submodule.span_le_restrictScalars F F' _ hx'
  have hdim : Module.finrank F' (Module.End F' (F' ⊗[F] W)) ≤ Module.finrank F S := by
    calc Module.finrank F' (Module.End F' (F' ⊗[F] W))
        = Module.finrank F' (⊤ : Submodule F' (Module.End F' (F' ⊗[F] W))) := finrank_top _ _ |>.symm
      _ = Module.finrank F' U := by rw [hU]
      _ ≤ Module.finrank F' (Submodule.span F' (Set.range fun i => ψ (b i))) :=
          Submodule.finrank_mono hspan
      _ ≤ Fintype.card (Fin (Module.finrank F S)) := finrank_range_le_card _
      _ = Module.finrank F S := Fintype.card_fin _
  have hEnd : Module.finrank F' (Module.End F' (F' ⊗[F] W)) =
      Module.finrank F (Module.End F W) := by
    rw [Module.finrank_linearMap, Module.finrank_linearMap, Module.finrank_baseChange]
  have hS : Module.finrank F S = Module.finrank F (Module.End F W) :=
    le_antisymm (Submodule.finrank_le (Subalgebra.toSubmodule S)) (hEnd ▸ hdim)
  exact Subalgebra.toSubmodule_injective
    (by rw [Algebra.top_toSubmodule]; exact Submodule.eq_top_of_finrank_eq hS)

end RvBurnside

namespace RvGP2

open TensorProduct in
/-- **Field 15 of `GluePieces2` is a theorem** (no leaf needed). -/
theorem burnsideAbsIrred : G0Galois.BurnsideAbsIrred := by
  intro F _ G _ W _ _ _ n b ρ h
  set F' := AlgebraicClosure F
  haveI hI := h F'
  have hρ : Algebra.adjoin F (Set.range ρ) = ⊤ := by
    haveI : Nontrivial (F' ⊗[F] W) := by
      by_contra hc
      rw [not_nontrivial_iff_subsingleton] at hc
      exact (bot_ne_top : (⊥ : Subrepresentation (GlueI3.repBaseChange F' ρ)) ≠ ⊤)
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
    refine RvBurnside.adjoin_eq_top_of_baseChange F' (Set.range ρ) (fun p hp => ?_)
    let σ : Subrepresentation (GlueI3.repBaseChange F' ρ) :=
      ⟨p, fun g v hv => hp (ρ g) ⟨g, rfl⟩ v hv⟩
    rcases eq_bot_or_eq_top σ with h' | h'
    · left; exact congrArg Subrepresentation.toSubmodule h'
    · right; exact congrArg Subrepresentation.toSubmodule h'
  have hmap := AlgHom.map_adjoin (LinearMap.toMatrixAlgEquiv b).toAlgHom (Set.range ρ)
  rw [hρ, ← Set.range_comp] at hmap
  have he : ((LinearMap.toMatrixAlgEquiv b).toAlgHom ∘ ρ) = fun g => LinearMap.toMatrix b b (ρ g) := by
    funext g; ext i j
    simp [LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  rw [he] at hmap
  rw [← hmap, eq_top_iff]
  intro M _
  exact ⟨(LinearMap.toMatrixAlgEquiv b).symm M, Algebra.mem_top, by simp⟩

end RvGP2



end G0A2_c10_burnside

section G0A2_c20_cpts
-- (leaf-fold3) scratch/cpts-transport/CPtsTransport.lean lines 7-end (after its import and #check lines)

noncomputable section

namespace HSyn

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace FibreQM

-- op-dedupe was: open ZInQ.LeafPush2 (CPts cptObj IsUniformization cDom cEvalAt)
open _root_.ZInQ.LeafPush2 (CPts cptObj IsUniformization cDom cEvalAt) -- op-dedupe
open scoped CategoryTheory.Obj

namespace CPtsT

/-- `appLE` along a factorization `f = x ≫ T`. -/
theorem appLE_of_eq {X Y Z : Scheme} (f : X ⟶ Z) (x : X ⟶ Y) (T : Y ⟶ Z) (h : f = x ≫ T)
    (U : Z.Opens) (hf : ⊤ ≤ f ⁻¹ᵁ U) (hx : ⊤ ≤ x ⁻¹ᵁ (T ⁻¹ᵁ U)) (s : Γ(Z, U)) :
    f.appLE U ⊤ hf s = x.appLE (T ⁻¹ᵁ U) ⊤ hx (T.app U s) := by
  subst h
  rw [Scheme.Hom.comp_appLE]
  rfl

/-- Values of regular functions along a factorization of complex points. -/
theorem cEvalAt_of_eq {K K' : Type} [Field K] [Field K'] {A : PkgI3.AbVar K}
    {B : PkgI3.AbVar K'} {σ : K →+* ℂ} {τ : K' →+* ℂ} (p : CPts A σ) (x : CPts B τ)
    (T : B.X.left ⟶ A.X.left) (h : p.left = x.left ≫ T) (U : A.X.left.Opens)
    (s : Γ(A.X.left, U)) :
    (⊤ ≤ p.left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ (T ⁻¹ᵁ U)) ∧
      (⊤ ≤ x.left ⁻¹ᵁ (T ⁻¹ᵁ U) → cEvalAt p U s = cEvalAt x (T ⁻¹ᵁ U) (T.app U s)) := by
  have hpre : p.left ⁻¹ᵁ U = x.left ⁻¹ᵁ (T ⁻¹ᵁ U) := by rw [h]; rfl
  refine ⟨⟨fun hh => le_of_le_of_eq hh hpre, fun hh => le_of_le_of_eq hh hpre.symm⟩, fun hx => ?_⟩
  have hp : ⊤ ≤ p.left ⁻¹ᵁ U := hpre ▸ hx
  simp only [cEvalAt, dif_pos hp, dif_pos hx]
  rw [appLE_of_eq p.left x.left T h U hp hx s]
  rfl

end CPtsT

namespace CPtsT

/-- **Complex points of a pullback (proved).** If `T0 : Q → A` makes `Q/ℂ` a pullback of `A/K`
along `σ : K → ℂ`, then `Q(ℂ) ≃* A(ℂ)_σ` compatibly with regular functions. The group isomorphism
is `x ↦ (x ≫ φ)` followed by the adjunction bijection `bcPt`, where `φ = E - E(0)` for the scheme
isomorphism `E : Q ≅ A_ℂ` of the two pullbacks; `φ` is a homomorphism by rigidity
(`G0FibreSimple.rigidityHom`). -/
theorem cPts_of_isPullback {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Q : PkgI3.AbVar ℂ) (T0 : Q.X.left ⟶ A.X.left)
    (S : IsPullback T0 Q.X.hom A.X.hom (Spec.map (CommRingCat.ofHom σ))) :
    ∃ ψ : CPts Q (RingHom.id ℂ) ≃* CPts A σ,
      ∀ (U : A.X.left.Opens) (s : Γ(A.X.left, U)),
        ∃ (U' : Q.X.left.Opens) (s' : Γ(Q.X.left, U')),
          ∀ x : CPts Q (RingHom.id ℂ), (⊤ ≤ (ψ x).left ⁻¹ᵁ U ↔ ⊤ ≤ x.left ⁻¹ᵁ U') ∧
            (⊤ ≤ x.left ⁻¹ᵁ U' → cEvalAt (ψ x) U s = cEvalAt x U' s') := by
  letI iC : Algebra K ℂ := σ.toAlgebra
  let B : PkgI3.AbVar ℂ := A.baseChange ℂ
  have S4 : IsPullback (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ)) :
      B.X.left ⟶ A.X.left) B.X.hom A.X.hom (Spec.map (CommRingCat.ofHom σ)) :=
    IsPullback.of_hasPullback _ _
  let E0 : Q.X.left ≅ B.X.left := S.isoIsPullback _ _ S4
  let E : Q.X ≅ B.X := Over.isoMk E0 (S.isoIsPullback_hom_snd _ _ S4)
  -- recentre at the identity and apply rigidity
  let b : 𝟙_ (Over (Spec (CommRingCat.of ℂ))) ⟶ B.X := η[Q.X] ≫ E.hom
  let φ : Q.X ⟶ B.X := E.hom * (toUnit Q.X ≫ b⁻¹)
  let φ' : B.X ⟶ Q.X := (𝟙 B.X * (toUnit B.X ≫ b)) ≫ E.inv
  have hu : η[Q.X] ≫ toUnit Q.X = 𝟙 _ := toUnit_unique _ _
  have h1 : φ ≫ φ' = 𝟙 Q.X := by
    simp only [φ, φ']
    rw [← Category.assoc, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, toUnit_unique ((E.hom * (toUnit Q.X ≫ b⁻¹)) ≫ toUnit B.X) (toUnit Q.X),
      _root_.mul_assoc, ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one,
      E.hom_inv_id]
  have h2 : φ' ≫ φ = 𝟙 B.X := by
    have k1 : φ' ≫ E.hom = 𝟙 B.X * (toUnit B.X ≫ b) := by
      simp only [φ']
      rw [Category.assoc, E.inv_hom_id, Category.comp_id]
    have k2 : φ' ≫ toUnit Q.X ≫ b⁻¹ = toUnit B.X ≫ b⁻¹ := by
      rw [← Category.assoc, toUnit_unique (φ' ≫ toUnit Q.X) (toUnit B.X)]
    simp only [φ]
    rw [MonObj.comp_mul, k1, k2, _root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel,
      MonObj.comp_one, _root_.mul_one]
  have h3 : η[Q.X] ≫ φ = η[B.X] := by
    simp only [φ]
    rw [MonObj.comp_mul, ← Category.assoc, hu, Category.id_comp, mul_inv_cancel,
      MonObj.one_eq_one]
  haveI hφ : IsMonHom φ := G0FibreSimple.rigidityHom ℂ Q B φ h3
  let m : CPts Q (RingHom.id ℂ) ≃* CPts B (RingHom.id ℂ) :=
    { toFun := fun x => x ≫ φ
      invFun := fun y => y ≫ φ'
      left_inv := fun x => (Category.assoc x φ φ').trans (by rw [h1, Category.comp_id])
      right_inv := fun y => (Category.assoc y φ' φ).trans (by rw [h2, Category.comp_id])
      map_mul' := fun x y => MonObj.mul_comp x y φ }
  let bc : CPts B (RingHom.id ℂ) ≃* CPts A σ :=
    @UnramTate.bcPt K ℂ _ _ iC A ℂ _ (Algebra.id ℂ) iC IsScalarTower.right
  let T : Q.X.left ⟶ A.X.left := φ.left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ))
  have hT : ∀ x : CPts Q (RingHom.id ℂ), (bc (m x)).left = x.left ≫ T := by
    intro x
    show 𝟙 _ ≫ (x ≫ φ).left ≫ pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom σ)) = _
    rw [Category.id_comp]
    rfl
  exact ⟨m.trans bc, fun U s =>
    ⟨T ⁻¹ᵁ U, T.app U s, fun x => cEvalAt_of_eq _ x T (hT x) U s⟩⟩

end CPtsT

open CPtsT in
/-- **`CPtsTransport` holds** (proved from `cPts_of_isPullback` by pasting pullback squares). -/
theorem cPtsTransport_proof : CPtsTransport := by
  intro K A emb P hiso ιe Q hQ
  obtain ⟨e⟩ := hiso
  obtain ⟨g, hpb, -, -⟩ := hQ
  letI iQ : Algebra K.K Qbar := emb.toAlgebra
  have S2 : IsPullback e.inv.left P.A.X.hom (A.baseChange Qbar).X.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have S3 : IsPullback (pullback.fst A.X.hom (Spec.map (CommRingCat.ofHom emb)) :
      (A.baseChange Qbar).X.left ⟶ A.X.left) (A.baseChange Qbar).X.hom A.X.hom
      (Spec.map (CommRingCat.ofHom emb)) :=
    IsPullback.of_hasPullback _ _
  have S := hpb.paste_horiz (S2.paste_horiz S3)
  have hσ : Spec.map (CommRingCat.ofHom ιe) ≫ 𝟙 _ ≫ Spec.map (CommRingCat.ofHom emb) =
      Spec.map (CommRingCat.ofHom (ιe.comp emb)) := by
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hσ] at S
  exact cPts_of_isPullback (LeafAdopt.abVarEquiv K.K A) (ιe.comp emb) Q.A _ S

end FibreQM

end G0Split

end HSyn



end
end G0A2_c20_cpts

section G0A2_c30_homunify
-- (leaf-fold3) written here: HomLatticeCorr verbatim from ZInQKernel/Contrib/HomUnify/Corr.lean, with its two proofs
/-! ## leaf-fold3: hom-unify's single leaf `HomLatticeCorr` (ZInQKernel/Contrib/HomUnify/Corr.lean)

The definition is `ZInQ.HomUnify.HomLatticeCorr` of `ZInQKernel/Contrib/HomUnify/Corr.lean`, verbatim; here it is
over this file's `PkgI3.AbVar`, `ZInQ.LeafPush2.CPts` and `ZInQ.LeafPush2.IsUniformization` (as in hom-unify's
own assembly, `scratch/hom-unify/parts/H20_bundle.lean`). The two consequences are Corr.lean's proofs, verbatim:
`HomLinearLift` is its first clause and leaf-push2's `T11a_RiemannEnd` (T11(a)) its two clauses at `B = A`. -/

section HomUnifyLF3

namespace HomUnify

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3
-- op-dedupe was: open ZInQ.LeafPush2 (CPts IsUniformization)
open _root_.ZInQ.LeafPush2 (CPts IsUniformization) -- op-dedupe

/-- **The analytic representation of homomorphisms (textbook LEAF; the single leaf proposed by
hom-unify for T11(a) in `Hom` form).** Let `A`, `B` be abelian varieties over a field `K`,
`σ : K → ℂ`, and `Φ_A : ℂ^g → A(ℂ)_σ`, `Φ_B : ℂ^h → B(ℂ)_σ` analytic uniformizations with kernels
`Λ_A`, `Λ_B` (`g = dim A`, `h = dim B`).
1. (lifting) every homomorphism `f : A → B` lifts to a `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `Φ_B(Mz) = f(Φ_A(z))`;
2. (realization, over `ℂ`) if `K = ℂ` and `σ = id`, every `ℂ`-linear `M : ℂ^g → ℂ^h` with
   `MΛ_A ⊆ Λ_B` is induced in this way by a unique homomorphism `f : A → B`.

Together: `Hom(A_ℂ, B_ℂ) ≅ {M ∈ Hom_ℂ(ℂ^g, ℂ^h) : MΛ_A ⊆ Λ_B}`, `f ↦ ρ_a(f)`, and for general `K`
the analytic representation of `f` is that of `f_ℂ`. Sources (all UNVERIFIED numbers):
Birkenhake–Lange, *Complex abelian varieties*, §1.2 (Prop. 1.2.1: homomorphisms of complex tori
`ℂ^g/Λ → ℂ^h/Λ'` are exactly the maps induced by `ℂ`-linear `M` with `MΛ ⊆ Λ'`, and the analytic
representation is injective); Mumford, *Abelian varieties*, §1 (the complex torus `A(ℂ)`) and
§3 (`A ↦ A^an` is fully faithful on abelian varieties); Serre, GAGA (1956) / Chow, for
"holomorphic ⇒ algebraic" in 2.; holomorphy of algebraic morphisms for 1. -/
def HomLatticeCorr : Prop :=
  (∀ (K : Type) [Field K] (A B : PkgI3.AbVar K) (σ : K →+* ℂ) (g h : ℕ)
    (ΛA : Submodule ℤ (Fin g → ℂ)) (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A σ) (ΦB : (Fin h → ℂ) → CPts B σ),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization σ ΛA ΦA → IsUniformization σ ΛB ΦB →
    ∀ f : PkgI3.AbVar.Hom A B, ∃ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ),
      ∀ z, ΦB (M z) = ΦA z ≫ f.hom) ∧
  (∀ (A B : PkgI3.AbVar ℂ) (g h : ℕ) (ΛA : Submodule ℤ (Fin g → ℂ))
    (ΛB : Submodule ℤ (Fin h → ℂ))
    (ΦA : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) (ΦB : (Fin h → ℂ) → CPts B (RingHom.id ℂ)),
    A.dim = (g : WithBot ℕ∞) → B.dim = (h : WithBot ℕ∞) →
    IsUniformization (RingHom.id ℂ) ΛA ΦA → IsUniformization (RingHom.id ℂ) ΛB ΦB →
    ∀ M : (Fin g → ℂ) →ₗ[ℂ] (Fin h → ℂ), (∀ z ∈ ΛA, M z ∈ ΛB) →
      ∃! f : PkgI3.AbVar.Hom A B, ∀ z, ΦB (M z) = ΦA z ≫ f.hom)

/-- **`HomLinearLift` from `HomLatticeCorr` (proved):** its first clause, verbatim. -/
theorem homLinearLift_of_corr (h : HomLatticeCorr) : G0Galois.HomLinearLift := h.1

/-- **leaf-push2's `T11a_RiemannEnd` from `HomLatticeCorr` (proved):** both clauses at `B = A`,
`Φ_B = Φ_A`, `K = ℂ`, `σ = id` (`End A` is `Hom A A`). -/
theorem t11a_riemannEnd_of_corr (h : HomLatticeCorr) : ZInQ.LeafPush2.T11a_RiemannEnd :=
  fun A g Λ Φ hA hU =>
    ⟨fun M hM => h.2 A A g g Λ Λ Φ Φ hA hA hU hU M hM,
     fun f => h.1 ℂ A A (RingHom.id ℂ) g g Λ Λ Φ Φ hA hA hU hU f⟩

end HomUnify

end HomUnifyLF3

end G0A2_c30_homunify

section G0A2_c40_kfglue
-- (leaf-fold3) scratch/g0-assemble3/parts/d20_kfglue.lean lines 1-15 and 431-1391 (lines 16-430 duplicate part a75)
/-! ## g0-assemble3: kf-glue (scratch/kf-glue/KfGlue.lean), generated by mk/mk_d20.py
KfGlue.lean is kernel-field's `KernelField.lean` (newer than part a75's copy) + mul-rigidity + `Points.lean` + kf-glue's
`New.lean`. Copied verbatim here: L5090-5264 (§6.10 `OMaxSec`: `oMaximal'`); from `EndEqOSec` (L5266-5272 header,
L5281-5282 `oMaximal`, L5386-5449 `kernelFieldExists_of_final` … `kernelFieldExists_of_final'`, with kf-glue's
`hR1.2.2.2.1` fix for the six-clause `R1fpProps`); `RigCopy` L5458-5462, L5474-5500 (its copy L5463-5473 of
`G0FibreSimple.RigidityHom`, = part 40, dropped); `RigProof` L5502-5634; `Points.lean` L6226-6349; `New.lean` part
L6351-end, minus its theorem `G0FibreSimple.rigidityHom` (= part a15). Dropped as duplicates of part a75: `OMaximal`,
`endEqOFibre_of`, `kernelFieldExists_of_split''` (L5273-5280 docstring/def, L5283-5385). `#print` lines dropped. -/
noncomputable section

-- (g0-assemble3) the file-level opens of KfGlue.lean active from its L4741 and L4907 on (part a75 keeps them inside sections):
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open scoped Quaternion TensorProduct

/-! # Part PTS. scratch/kf-glue/Points.lean (new; the two point lemmas from Mathlib) -/
section PartPoints

/-! # kf-glue: the two point lemmas (prototype; copied into New.lean) -/

noncomputable section

namespace KfGluePoints

open CategoryTheory AlgebraicGeometry Limits

abbrev Qb : Type := AlgebraicClosure ℚ

/-- The ring of a finite affine scheme over `Spec ℚ̄`, and its structure map from `ℚ̄`. -/
def phi (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) :
    CommRingCat.of Qb ⟶ Γ(P, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of Qb)).inv ≫ q.appTop

theorem q_eq (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb)) :
    q = P.isoSpec.hom ≫ Spec.map (phi P q) := by
  have h := Scheme.isoSpec_hom_naturality q
  rw [Scheme.isoSpec_Spec_hom] at h
  rw [phi, Spec.map_comp, ← Category.assoc, h, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.comp_id]

theorem phi_finite (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q] :
    (phi P q).hom.Finite := by
  rw [phi, CommRingCat.hom_comp]
  exact RingHom.Finite.comp (Scheme.Hom.finite_appTop q)
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)

/-- Sections of `q` correspond to ring maps `ψ : Γ(P) → ℚ̄` with `ψ ∘ φ = id`. -/
theorem section_iff (P : Scheme.{0}) [IsAffine P] (q : P ⟶ Spec (CommRingCat.of Qb))
    (ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb) :
    (Spec.map ψ ≫ P.isoSpec.inv) ≫ q = 𝟙 _ ↔ phi P q ≫ ψ = 𝟙 _ := by
  have hq := q_eq P q
  have e : (Spec.map ψ ≫ P.isoSpec.inv) ≫ q = Spec.map (phi P q ≫ ψ) := by
    conv_lhs => rw [hq]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp]
  rw [e, ← Spec.map_id]
  exact Spec.map_injective.eq_iff

/-- **A nonempty finite scheme over `Spec ℚ̄` has a section.** -/
theorem exists_section (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q]
    [Nonempty P] : ∃ s : Spec (CommRingCat.of Qb) ⟶ P, s ≫ q = 𝟙 _ := by
  have : IsAffine P := isAffine_of_isAffineHom q
  have hB : Nontrivial Γ(P, ⊤) := by
    rw [← PrimeSpectrum.nonempty_iff_nontrivial]
    exact ⟨P.isoSpec.hom (Classical.arbitrary P)⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(P, ⊤)
  let f : Qb →+* (Γ(P, ⊤) ⧸ m) := (Ideal.Quotient.mk m).comp (phi P q).hom
  have hf : f.IsIntegral :=
    (RingHom.Finite.comp (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective)
      (phi_finite P q)).to_isIntegral
  have : m.IsMaximal := hm
  have hbij := IsAlgClosed.ringHom_bijective_of_isIntegral f hf
  let e := RingEquiv.ofBijective f hbij
  let ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb :=
    CommRingCat.ofHom ((e.symm : (Γ(P, ⊤) ⧸ m) →+* Qb).comp (Ideal.Quotient.mk m))
  refine ⟨Spec.map ψ ≫ P.isoSpec.inv, (section_iff P q ψ).mpr ?_⟩
  ext r
  change e.symm (f r) = r
  exact e.symm_apply_apply r

/-- **A finite scheme over `Spec ℚ̄` has finitely many sections.** -/
theorem finite_sections (P : Scheme.{0}) (q : P ⟶ Spec (CommRingCat.of Qb)) [IsFinite q] :
    {s : Spec (CommRingCat.of Qb) ⟶ P | s ≫ q = 𝟙 _}.Finite := by
  have : IsAffine P := isAffine_of_isAffineHom q
  letI : Algebra Qb Γ(P, ⊤) := (phi P q).hom.toAlgebra
  have : Module.Finite Qb Γ(P, ⊤) := phi_finite P q
  have hpre : ∀ s : Spec (CommRingCat.of Qb) ⟶ P, ∃ ψ : Γ(P, ⊤) ⟶ CommRingCat.of Qb,
      Spec.map ψ = s ≫ P.isoSpec.hom := fun s => Spec.map_surjective _
  choose ψ hψ using hpre
  have hs : ∀ s, s = Spec.map (ψ s) ≫ P.isoSpec.inv := fun s => by
    rw [hψ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let g : {s : Spec (CommRingCat.of Qb) ⟶ P | s ≫ q = 𝟙 _} → (Γ(P, ⊤) →ₐ[Qb] Qb) := fun s =>
    { toRingHom := (ψ s.1).hom
      commutes' := fun r => by
        have h1 : phi P q ≫ ψ s.1 = 𝟙 _ := by
          rw [← section_iff P q, ← hs]; exact s.2
        exact congrArg (fun k : CommRingCat.of Qb ⟶ CommRingCat.of Qb => k.hom r) h1 }
  have hg : Function.Injective g := by
    intro s t hst
    apply Subtype.ext
    rw [hs s.1, hs t.1]
    have : ψ s.1 = ψ t.1 := by
      ext x; exact congrArg (fun k : Γ(P, ⊤) →ₐ[Qb] Qb => k x) hst
    rw [this]
  exact Set.finite_coe_iff.mp (Finite.of_injective g hg)

/-- **`LiftQbarPoints`'s content.** -/
theorem liftQbar (X Y : Scheme.{0}) (F : X ⟶ Y) (hF : IsFinite F) (hs : Surjective F)
    (y : Spec (CommRingCat.of Qb) ⟶ Y) : ∃ x : Spec (CommRingCat.of Qb) ⟶ X, x ≫ F = y := by
  have : IsFinite F := hF
  have : Surjective F := hs
  have : Nonempty (Limits.pullback F y : Scheme.{0}) := by
    obtain ⟨p, -⟩ := (pullback.snd F y).surjective (Classical.arbitrary _)
    exact ⟨p⟩
  obtain ⟨s, hs'⟩ := exists_section (pullback F y) (pullback.snd F y)
  refine ⟨s ≫ pullback.fst F y, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs', Category.id_comp]

/-- **`FiniteFibreQbarPoints`'s content.** -/
theorem finiteFibreQbar (X Y : Scheme.{0}) (F : X ⟶ Y) (hF : IsFinite F)
    (y : Spec (CommRingCat.of Qb) ⟶ Y) :
    {x : Spec (CommRingCat.of Qb) ⟶ X | x ≫ F = y}.Finite := by
  have : IsFinite F := hF
  have := (finite_sections (pullback F y) (pullback.snd F y)).to_subtype
  let ℓ : {x : Spec (CommRingCat.of Qb) ⟶ X | x ≫ F = y} →
      {s : Spec (CommRingCat.of Qb) ⟶ pullback F y | s ≫ pullback.snd F y = 𝟙 _} := fun x =>
    ⟨pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]), pullback.lift_snd _ _ _⟩
  have hℓ : Function.Injective ℓ := by
    intro x x' h
    apply Subtype.ext
    have h1 : pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]) =
        pullback.lift x'.1 (𝟙 _) (by rw [x'.2, Category.id_comp]) := congrArg Subtype.val h
    have h2 := congrArg (fun t : Spec (CommRingCat.of Qb) ⟶ pullback F y => t ≫ pullback.fst F y) h1
    simpa using h2
  exact Set.finite_coe_iff.mp (Finite.of_injective ℓ hℓ)

end KfGluePoints
end -- closes Points.lean's noncomputable section
end PartPoints

/-! # kf-glue, part 1: `EndTransport` (scratch/kernel-field/New.lean, statement unchanged)

`EndTransport` is defined above (verbatim from scratch/kernel-field). kernel-field proved
`endTransport_of : EndTransportBC → EndTransport` and
`endTransportBC_of_rigidity : RigidityHom → EndTransportBC`; mul-rigidity proved `RigidityHom`
from Mathlib (`MulRigidity.isMonHom_of_geometricallyIntegral`). -/

section KfGlueEndTransport

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj


/-- **`EndTransport` is a theorem** (no hypotheses). -/
theorem G0ModField.KernelField.endTransport : G0ModField.KernelField.EndTransport :=
  G0ModField.KernelField.endTransport_of
    (G0ModField.KernelField.endTransportBC_of_rigidity G0FibreSimple.rigidityHom)

/-- `KernelFieldExists` with `RigidityHom` discharged: five leaves and two glue Props. -/
theorem G0ModField.KernelField.kernelFieldExists_of_five (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hG : G0ModField.KernelField.ConjIsogMaps) :
    G0ModField.KernelFieldExists :=
  G0ModField.KernelField.kernelFieldExists_of_rigidity hHFF hNOS hRay hTors t27
    G0FibreSimple.rigidityHom h5 hG

end KfGlueEndTransport



/-! # kf-glue, part 2: `ConjIsogMaps`, level 1 — the points bookkeeping (proved)

`ConjIsogMaps` (verbatim above, from scratch/kernel-field) asks for maps `m_σ` on `A_L(ℚ̄)`. We
prove it from `SemilinearIsogMaps`, the same statement one level down: σ-semilinear finite
surjective scheme endomorphisms `F_σ` of `A_L` (the conjugacy isogenies `μ_σ` composed with the
identification of `^σA_L` and `A_L` as schemes), respecting the group law and the `𝒪`-action,
inflated from `Gal(L/ℚ)`, with discrepancy in `End_L(A_L)` up to an integer; plus two general
glue facts about `ℚ̄`-points of finite morphisms. Then `m_σ(x) = F_σ ∘ x ∘ Spec σ`. -/

section KfGlueLevel1

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- **Glue (general scheme theory; Stacks, finite morphisms and points over algebraically closed
fields).** A finite surjective morphism of schemes is surjective on `ℚ̄`-points: the fibre over the
image point `y` of `Spec ℚ̄ → Y` is nonempty, and for `x` in it `κ(x)/κ(y)` is algebraic, so the
embedding `κ(y) → ℚ̄` extends to `κ(x)` (`ℚ̄` algebraically closed). -/
def LiftQbarPoints : Prop :=
  ∀ (X Y : Scheme.{0}) (F : X ⟶ Y), IsFinite F → Surjective F →
    ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y, ∃ x : Spec (CommRingCat.of Qbar) ⟶ X, x ≫ F = y

/-- **Glue (general scheme theory).** The `ℚ̄`-points of `X` over a fixed `ℚ̄`-point of `Y` under a
finite morphism form a finite set: the fibre is finite and each `κ(x)/κ(y)` is a finite extension,
which has finitely many `κ(y)`-embeddings into `ℚ̄`. -/
def FiniteFibreQbarPoints : Prop :=
  ∀ (X Y : Scheme.{0}) (F : X ⟶ Y), IsFinite F →
    ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y,
      {x : Spec (CommRingCat.of Qbar) ⟶ X | x ≫ F = y}.Finite

/-- **The σ-semilinear conjugacy isogenies on `A/L` (geometric clauses).** For each `σ ∈ G_ℚ` a
morphism of schemes `F_σ : A → A` with:
* `F_σ` lies over `Spec(σ⁻¹|_L)` on `Spec L` and respects the group law (it is `μ_σ ∘ c_σ`,
  `c_σ : A ≅ ^σA` the identification of underlying schemes, `μ_σ : ^σA → A` a homomorphism);
* `F_σ` commutes with `ι'(𝒪)` (`μ_σ` is `𝒪`-linear: A7 + Skolem–Noether);
* `F_σ` is finite and surjective (`μ_σ` an isogeny);
* `F_k = id` for `k ∈ G_L` and `F` is constant on double cosets of `G_L` (`μ` inflated from
  `Gal(L/ℚ)`, defined over `L`);
* `F_τ ≫ F_σ ≫ [e] = F_{στ} ≫ δ` with `e ≠ 0` and `δ ∈ End_L(A)` (`δ = μ_σ ^σμ_τ ψ_{στ}` with
  `ψ_{στ} μ_{στ} = [e]` a quasi-inverse, Mumford §8). -/
def SemilinearIsogAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (F : GQ → (A.X.left ⟶ A.X.left)) : Prop :=
  ∀ σ : GQ,
    (∃ τ : L ≃+* L, (∀ x : L, (τ x : Qbar) = act σ⁻¹ x) ∧
      ∃ hτ : F σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ F σ =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom (F σ) (F σ)
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ F σ = F σ ≫ (ι' a).hom.left) ∧
    IsFinite (F σ) ∧ Surjective (F σ) ∧
    (∀ k ∈ GQL L, F k = 𝟙 _ ∧ F (σ * k) = F σ ∧ F (k * σ) = F σ) ∧
    (∀ τ : GQ, ∃ e : ℤ, e ≠ 0 ∧ ∃ δ : PkgI3.AbVar.End A,
      F τ ≫ F σ ≫ (e : PkgI3.AbVar.End A).hom.left = F (σ * τ) ≫ δ.hom.left)

/-- **`ConjIsogMaps` one level down (geometric glue).** Same context as `ConjIsogMaps`; asks for
the σ-semilinear isogenies `F_σ` of `SemilinearIsogAt` on `A_L` for `ι_L = endBC ∘ PK.q.iota`. -/
def SemilinearIsogMaps : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ F : GQ → ((@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left ⟶
            (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left),
          SemilinearIsogAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) F

/-- `Spec σ` for `σ ∈ G_ℚ`. -/
noncomputable abbrev specA (σ : GQ) : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of Qbar) :=
  Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar))

theorem specA_mul (σ τ : GQ) : specA (σ * τ) = specA σ ≫ specA τ := by
  rw [specA, specA, specA, ← Spec.map_comp]; rfl

theorem specA_one : specA 1 = 𝟙 _ := by
  rw [specA, ← Spec.map_id]; rfl

theorem specA_inv (σ : GQ) : specA σ ≫ specA σ⁻¹ = 𝟙 _ := by
  rw [← specA_mul, mul_inv_cancel, specA_one]

theorem specA_inv' (σ : GQ) : specA σ⁻¹ ≫ specA σ = 𝟙 _ := by
  rw [← specA_mul, inv_mul_cancel, specA_one]

instance (σ : GQ) : IsIso (specA σ) := ⟨⟨specA σ⁻¹, specA_inv σ, specA_inv' σ⟩⟩

section Pts

variable {L : IF} (A : PkgI3.AbVar L)

/-- The underlying morphism `Spec ℚ̄ → A` of a point. -/
noncomputable def ptl (x : A.Pt Qbar) : Spec (CommRingCat.of Qbar) ⟶ A.X.left := x.left

theorem ptl_w (x : A.Pt Qbar) :
    ptl A x ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := Over.w x

theorem ptl_ext {x y : A.Pt Qbar} (h : ptl A x = ptl A y) : x = y := Over.OverMorphism.ext h

theorem ptl_mul (x y : A.Pt Qbar) :
    ptl A (x * y) = pullback.lift (ptl A x) (ptl A y) ((ptl_w A x).trans (ptl_w A y).symm) ≫
      μ[A.X].left := by
  unfold ptl
  rw [Hom.mul_def, Over.comp_left, Over.lift_left]
  exact rfl

/-- The group-law clause for a semilinear `G` over `Spec τ`. -/
def SemMul (τ : L ≃+* L) (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L))) : Prop :=
  μ[A.X].left ≫ G =
    pullback.map A.X.hom A.X.hom A.X.hom A.X.hom G G
      (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hG.symm hG.symm ≫ μ[A.X].left

/-- The image of a point under a σ-semilinear map. -/
noncomputable def semPt (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (x : A.Pt Qbar) : A.Pt Qbar :=
  Over.homMk (specA σ ≫ ptl A x ≫ G) (by
    have hw : (specA σ ≫ ptl A x ≫ G) ≫ A.X.hom =
        Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
      rw [Category.assoc, Category.assoc, hG, ← Category.assoc (ptl A x), ptl_w, specA,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext z
      change act σ ((τ z : L) : Qbar) = (z : Qbar)
      rw [hτσ z, ← act_mul, mul_inv_cancel]; rfl
    exact hw)

theorem semPt_ptl (σ : GQ) (τ : L ≃+* L) (hτσ) (G : A.X.left ⟶ A.X.left) (hG)
    (x : A.Pt Qbar) : ptl A (semPt A σ τ hτσ G hG x) = specA σ ≫ ptl A x ≫ G := rfl

theorem semPt_mul (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) (x y : A.Pt Qbar) :
    semPt A σ τ hτσ G hG (x * y) = semPt A σ τ hτσ G hG x * semPt A σ τ hτσ G hG y := by
  apply ptl_ext
  have hμ' : μ[A.X].left ≫ G = pullback.map A.X.hom A.X.hom A.X.hom A.X.hom G G
      (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hG.symm hG.symm ≫ μ[A.X].left := hμ
  rw [semPt_ptl, ptl_mul, ptl_mul, Category.assoc, hμ', ← Category.assoc, ← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp [semPt_ptl]
  · simp [semPt_ptl]

/-- `semPt` as a group homomorphism of `A(ℚ̄)`. -/
noncomputable def semHom (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) : PtQ L A →+ PtQ L A :=
  MonoidHom.toAdditive (MonoidHom.mk' (semPt A σ τ hτσ G hG) (semPt_mul A σ τ hτσ G hG hμ))

/-- The underlying morphism of a point of `PtQ`. -/
noncomputable abbrev ptq (x : PtQ L A) : Spec (CommRingCat.of Qbar) ⟶ A.X.left := ptl A (Additive.toMul x)

theorem ptq_ext {x y : PtQ L A} (h : ptq A x = ptq A y) : x = y :=
  Additive.toMul.injective (ptl_ext A h)

theorem semHom_ptq (σ : GQ) (τ : L ≃+* L) (hτσ : ∀ x : L, (τ x : Qbar) = act σ⁻¹ x)
    (G : A.X.left ⟶ A.X.left)
    (hG : G ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)))
    (hμ : SemMul A τ G hG) (x : PtQ L A) :
    ptq A (semHom A σ τ hτσ G hG hμ x) = specA σ ≫ ptq A x ≫ G := rfl

theorem endPt_ptq (f : PkgI3.AbVar.End A) (x : PtQ L A) :
    ptq A (endPt A Qbar f x) = ptq A x ≫ f.hom.left := rfl

theorem zsmul_ptq (e : ℤ) (x : PtQ L A) :
    ptq A (e • x) = ptq A x ≫ (e : PkgI3.AbVar.End A).hom.left := by
  have h1 : endPt A Qbar (e : PkgI3.AbVar.End A) x = e • x := by
    rw [map_intCast, AddMonoid.End.intCast_apply]
  rw [← h1, endPt_ptq]

theorem galAct_ptq (σ' : Qbar ≃ₐ[L] Qbar) (x : PtQ L A) :
    ptq A (MonoidHom.toAdditive (A.galAct σ') x) =
      Spec.map (CommRingCat.ofHom (σ' : Qbar →+* Qbar)) ≫ ptq A x := rfl

end Pts

/-- **Level 1 (proved): the points bookkeeping.** σ-semilinear isogenies on `A/L` give the maps
`m_σ(x) = F_σ ∘ x ∘ Spec σ` with all clauses of `ConjIsogMapsAt`. -/
theorem conjIsogMapsAt_of_semilinear (hLift : LiftQbarPoints) (hFib : FiniteFibreQbarPoints)
    (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (F : GQ → (A.X.left ⟶ A.X.left)) (hF : SemilinearIsogAt L A ι' F) :
    ∃ m : GQ → (PtQ L A →+ PtQ L A), ConjIsogMapsAt L A ι' m := by
  choose τ hτσ hτ hμ using fun σ => (hF σ).1
  let m : GQ → (PtQ L A →+ PtQ L A) := fun σ => semHom A σ (τ σ) (hτσ σ) (F σ) (hτ σ) (hμ σ)
  have hm : ∀ σ x, ptq A (m σ x) = specA σ ≫ ptq A x ≫ F σ := fun σ x => rfl
  refine ⟨m, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- clause 1: the Galois action on `G_L`
    intro σ σ' hσ'
    have hσL : σ ∈ GQL L := mem_GQL.mpr fun x hx => by
      rw [← hσ' x]; exact σ'.commutes ⟨x, hx⟩
    refine AddMonoidHom.ext fun x => ptq_ext A ?_
    have hσσ : specA σ = Spec.map (CommRingCat.ofHom (σ' : Qbar →+* Qbar)) := by
      rw [specA]; congr 1; ext z; exact (hσ' z).symm
    rw [hm, galAct_ptq, ((hF σ).2.2.2.2.1 σ hσL).1, Category.comp_id, hσσ]
  · -- clause 2: inflation
    intro σ k hk
    obtain ⟨h1, h2, h3⟩ := (hF σ).2.2.2.2.1 k hk
    refine ⟨AddMonoidHom.ext fun x => ptq_ext A ?_, AddMonoidHom.ext fun x => ptq_ext A ?_⟩
    · show ptq A (m (σ * k) x) = ptq A (m σ (m k x))
      rw [hm, hm, hm, h2, h1, specA_mul]
      simp only [Category.assoc, Category.comp_id]
    · show ptq A (m (k * σ) x) = ptq A (m k (m σ x))
      rw [hm, hm, hm, h3, h1, specA_mul]
      simp only [Category.assoc, Category.comp_id]
  · -- clause 3: `𝒪`-linearity
    intro σ a
    refine AddMonoidHom.ext fun x => ptq_ext A ?_
    show ptq A (m σ (endPt A Qbar (ι' a) x)) = ptq A (endPt A Qbar (ι' a) (m σ x))
    rw [hm, endPt_ptq, endPt_ptq, hm]
    simp only [Category.assoc]
    rw [(hF σ).2.1 a]
  · -- clause 4: surjective with finite kernel
    intro σ
    obtain ⟨-, -, hfin, hsurj, -, -⟩ := hF σ
    refine ⟨fun y => ?_, ?_⟩
    · obtain ⟨x', hx'⟩ := hLift _ _ (F σ) hfin hsurj (ptq A y)
      have hiso : IsIso (Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L))) :=
        ⟨⟨Spec.map (CommRingCat.ofHom ((τ σ).symm : L →+* L)), by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z; simp,
          by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z;
             simp⟩⟩
      have hy : x' ≫ A.X.hom ≫ Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L)) =
          Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
        rw [← hτ σ, ← Category.assoc, hx']; exact ptl_w A _
      have hx'' : x' ≫ A.X.hom = Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) ≫
          inv (Spec.map (CommRingCat.ofHom ((τ σ : L ≃+* L) : L →+* L))) := by
        rw [← hy]; simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have hw : (specA σ⁻¹ ≫ x') ≫ A.X.hom =
          Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
        rw [Category.assoc, hx'', ← Category.assoc, IsIso.comp_inv_eq, specA, ← Spec.map_comp,
          ← Spec.map_comp]
        congr 1
        ext z
        change act σ⁻¹ (z : Qbar) = ((τ σ z : L) : Qbar)
        rw [hτσ σ z]
      refine ⟨Additive.ofMul (Over.homMk (specA σ⁻¹ ≫ x') hw), ptq_ext A ?_⟩
      rw [hm]
      change specA σ ≫ (specA σ⁻¹ ≫ x') ≫ F σ = _
      rw [← Category.assoc, ← Category.assoc, specA_inv, Category.id_comp, hx']
    · have hsub : ((m σ).ker : Set (PtQ L A)) ⊆
          (fun x : PtQ L A => specA σ ≫ ptq A x) ⁻¹'
            {x' | x' ≫ F σ = ptq A (0 : PtQ L A)} := by
        intro x hx
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker] at hx
        simp only [Set.mem_preimage, Set.mem_ofPred_eq]
        rw [Category.assoc, ← hm, hx]
      refine Set.Finite.subset (Set.Finite.preimage ?_ (hFib _ _ (F σ) hfin _)) hsub
      intro x _ x₂ _ h
      exact ptq_ext A ((cancel_epi (specA σ)).mp h)
  · -- clause 5: the discrepancy
    intro σ τ'
    obtain ⟨e, he, δ, hδ⟩ := (hF σ).2.2.2.2.2 τ'
    refine ⟨e, he, δ, AddMonoidHom.ext fun x => ptq_ext A ?_⟩
    show ptq A (e • m σ (m τ' x)) = ptq A (endPt A Qbar δ (m (σ * τ') x))
    rw [zsmul_ptq, endPt_ptq, hm, hm, hm, specA_mul]
    simp only [Category.assoc]
    rw [hδ]
  · -- clause 6: algebraicity
    exact ⟨F, fun σ => ⟨(hF σ).2.2.1, (hF σ).2.2.2.1, fun x => hm σ x⟩⟩

/-- **`ConjIsogMaps` from `SemilinearIsogMaps` and the two point lemmas (proved).** -/
theorem conjIsogMaps_of_semilinear (hLift : LiftQbarPoints) (hFib : FiniteFibreQbarPoints)
    (h : SemilinearIsogMaps) : ConjIsogMaps := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨F, hF⟩ := h Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact conjIsogMapsAt_of_semilinear hLift hFib L _ _ F hF

/-- **`LiftQbarPoints` holds** (proved from Mathlib, `scratch/kf-glue/Points.lean`: the pullback of
`F` along `y` is a nonempty finite scheme `Spec B` over `Spec ℚ̄`; a maximal quotient of `B` is a
finite field extension of `ℚ̄`, hence `ℚ̄`, giving a section). -/
theorem liftQbarPoints : LiftQbarPoints := fun X Y F hF hs y =>
  KfGluePoints.liftQbar X Y F hF hs y

/-- **`FiniteFibreQbarPoints` holds** (proved from Mathlib: the points over `y` inject into the
sections of the finite `Spec B → Spec ℚ̄`, i.e. into `B →ₐ[ℚ̄] ℚ̄`, finite by Mathlib's
`Finite.algHom`). -/
theorem finiteFibreQbarPoints : FiniteFibreQbarPoints := fun X Y F hF y =>
  KfGluePoints.finiteFibreQbar X Y F hF y

/-- **`ConjIsogMaps` from `SemilinearIsogMaps` alone (proved).** -/
theorem conjIsogMaps_of_semilinearIsogMaps (h : SemilinearIsogMaps) : ConjIsogMaps :=
  conjIsogMaps_of_semilinear liftQbarPoints finiteFibreQbarPoints h

/-- `KernelFieldExists` with `ConjIsogMaps` replaced by `SemilinearIsogMaps`. -/
theorem kernelFieldExists_of_semilinear (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hS : SemilinearIsogMaps) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_semilinearIsogMaps hS)

end G0ModField.KernelField

end KfGlueLevel1

/-! # kf-glue, part 3: `SemilinearIsogMaps`, level 2 — Skolem–Noether, the isogeny `ι(b)`, the
quasi-inverse and the discrepancy (proved)

`SemilinearIsogMaps` is proved from `SemilinearTwistIsos`: σ-semilinear scheme *automorphisms*
`E_σ` of `A/L` preserving the origin and the group law and twisting `ι` by some `α_σ ∈ Aut(𝒪)`
(A7's twisted QM isomorphisms `(A, ι∘α) ≅ (^σA, ^σι)`, descended to `L`), plus `MulIsogeny`
(mul-rigidity: from `KerUnitOpen` or two cotangent glue statements) and `RigidityHom` (proved).
Then `F_σ = E_σ ≫ ι(b_σ)` with `b_σ ∈ 𝒪` from Skolem–Noether (`aut_O_inner`), `ι(b)` is an isogeny
with quasi-inverse `ι(N b⁻¹)` (so no quasi-inverse leaf is needed), and the discrepancy is
`δ = ι(b_σ) ι(α_σ b_τ) D ι(c)` with `D = E_{στ}⁻¹ E_τ E_σ ∈ End_L(A)` (rigidity). -/

section KfGlueLevel2

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

/- `G0FibreSimple.MulIsogeny` is in Part MR (MulRigidity.lean L321-323, verbatim). -/

namespace G0ModField.KernelField

open G0ModField

/-- **The core geometric glue: A7's twisted isomorphisms, descended to `L`, as σ-semilinear
automorphisms.** For each `σ ∈ G_ℚ` an automorphism `E_σ` of the scheme `A` lying over
`Spec(σ⁻¹|_L)`, preserving the group law and the origin, with `ι(a) E_σ = E_σ ι(α_σ a)` for an
`α_σ ∈ Aut(𝒪)`; `E_k = id`, `α_k = id` on `G_L`, and `E`, `α` constant on cosets of `G_L`. -/
def SemilinearTwistAt (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A)
    (E : GQ → (A.X.left ⟶ A.X.left)) (α : GQ → (O ≃+* O)) : Prop :=
  ∀ σ : GQ,
    IsIso (E σ) ∧
    (∃ τ : L ≃+* L, (∀ x : L, (τ x : Qbar) = act σ⁻¹ x) ∧
      ∃ hτ : E σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ E σ =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom (E σ) (E σ)
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left ∧
        η[A.X].left ≫ E σ = Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ η[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ E σ = E σ ≫ (ι' (α σ a)).hom.left) ∧
    (∀ k ∈ GQL L, E k = 𝟙 _ ∧ α k = RingEquiv.refl O ∧ E (σ * k) = E σ ∧ E (k * σ) = E σ ∧
      α (σ * k) = α σ ∧ α (k * σ) = α σ)

/-- **`SemilinearIsogMaps` one level down (geometric glue).** Same context as `ConjIsogMaps`. -/
def SemilinearTwistIsos : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ (j₀ : ℚ) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P → π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar j₀) →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (PK : QML3 K), RationalFibre Y Φ P K PK →
      ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L),
        (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K PK.A σ = 1) →
        ∃ (E : GQ → ((@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left ⟶
            (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)).X.left)) (α : GQ → (O ≃+* O)),
          SemilinearTwistAt L (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
            ((@endBC K _ PK.A L _ (incAlg hKL)).comp PK.q.iota) E α

/-! ### Algebra in `𝒪` -/

/-- Skolem–Noether, linear form: for `α ∈ Aut 𝒪` there is `b ≠ 0` with `b α(a) = a b`. -/
theorem exists_b (α : O ≃+* O) : ∃ b : O, b ≠ 0 ∧ ∀ a : O, b * α a = a * b := by
  obtain ⟨u, hu⟩ := aut_O_inner α
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O ((u⁻¹ : Bˣ) : B)
  let b : O := ⟨(N : B) * (u⁻¹ : Bˣ), hmem⟩
  refine ⟨b, fun hb => ?_, fun a => ?_⟩
  · have h0 := congrArg Subtype.val hb
    change (N : B) * (u⁻¹ : Bˣ) = 0 at h0
    have h1 := congrArg (· * (u : B)) h0
    simp only [_root_.mul_assoc, Units.inv_mul, _root_.mul_one, zero_mul] at h1
    have h2 := congrArg QuaternionAlgebra.re h1
    simp at h2
    omega
  · apply Subtype.ext
    rw [Subring.coe_mul, Subring.coe_mul, hu a]
    show (N : B) * (u⁻¹ : Bˣ) * (u * a * (u⁻¹ : Bˣ)) = a * ((N : B) * (u⁻¹ : Bˣ))
    have hc : ((u⁻¹ : Bˣ) : B) * (u * a * (u⁻¹ : Bˣ)) = a * (u⁻¹ : Bˣ) := by
      rw [← _root_.mul_assoc, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
    rw [_root_.mul_assoc, hc, ← _root_.mul_assoc, (Nat.cast_commute N (a : B)).eq,
      _root_.mul_assoc]

/-- A quasi-inverse in `𝒪`: for `b ≠ 0` there are `c` and `N > 0` with `c b = N = b c`. -/
theorem exists_quasi_inv {b : O} (hb : b ≠ 0) :
    ∃ c : O, ∃ N : ℕ, 0 < N ∧ c * b = (N : O) ∧ b * c = (N : O) := by
  have hb' : (b : B) ≠ 0 := fun h => hb (Subtype.ext h)
  obtain ⟨v, hv⟩ := G0FibreSimple.B6_isUnit (b : B) hb'
  obtain ⟨N, hN, hmem⟩ := exists_nat_mul_mem_O ((v⁻¹ : Bˣ) : B)
  refine ⟨⟨(N : B) * (v⁻¹ : Bˣ), hmem⟩, N, hN, Subtype.ext ?_, Subtype.ext ?_⟩
  · rw [Subring.coe_mul]
    show (N : B) * (v⁻¹ : Bˣ) * b = ((N : O) : B)
    rw [← hv, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]; rfl
  · rw [Subring.coe_mul]
    show (b : B) * ((N : B) * (v⁻¹ : Bˣ)) = ((N : O) : B)
    rw [← hv, ← _root_.mul_assoc, (Nat.cast_commute N (v : B)).eq.symm, _root_.mul_assoc,
      Units.mul_inv, _root_.mul_one]; rfl

/-- **`ι(b)` is an isogeny for `b ≠ 0`** (from `MulIsogeny`; `ι(c) ι(b) = [N] = ι(b) ι(c)`). -/
theorem iota_isogeny (hMul : G0FibreSimple.MulIsogeny) {k : Type} [Field k] [CharZero k]
    {A : PkgI3.AbVar k} (ι' : O →+* PkgI3.AbVar.End A) {b : O} (hb : b ≠ 0) :
    IsFinite (ι' b).hom.left ∧ Surjective (ι' b).hom.left := by
  obtain ⟨c, N, hN, hcb, hbc⟩ := exists_quasi_inv hb
  have hNz : ((N : ℤ) : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨hfin, hsurj⟩ := hMul k A (N : ℤ) hNz
  have e1 : (ι' b).hom.left ≫ (ι' c).hom.left = ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
    have : ι' c * ι' b = ((N : ℤ) : PkgI3.AbVar.End A) := by
      rw [← map_mul, hcb, Int.cast_natCast, map_natCast]
    rw [← this]; rfl
  have e2 : (ι' c).hom.left ≫ (ι' b).hom.left = ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
    have : ι' b * ι' c = ((N : ℤ) : PkgI3.AbVar.End A) := by
      rw [← map_mul, hbc, Int.cast_natCast, map_natCast]
    rw [← this]; rfl
  refine ⟨?_, ?_⟩
  · have : IsFinite ((ι' b).hom.left ≫ (ι' c).hom.left) := by rw [e1]; exact hfin
    have : IsSeparated (ι' c).hom.left := by
      have : IsSeparated ((ι' c).hom.left ≫ A.X.hom) := by rw [Over.w]; infer_instance
      exact IsSeparated.of_comp (ι' c).hom.left A.X.hom
    exact IsFinite.of_comp (ι' b).hom.left (ι' c).hom.left
  · have hs : Surjective ((ι' c).hom.left ≫ (ι' b).hom.left) := by rw [e2]; exact hsurj
    refine ⟨fun z => ?_⟩
    obtain ⟨w, hw⟩ := ((ι' c).hom.left ≫ (ι' b).hom.left).surjective z
    exact ⟨(ι' c).hom.left w, by rw [← Scheme.Hom.comp_apply]; exact hw⟩

/-! ### The assembly -/

theorem spec_comp_spec {L : IF} (a b c : L ≃+* L) (h : ∀ x, c x = a (b x)) :
    Spec.map (CommRingCat.ofHom (a : L →+* L)) ≫ Spec.map (CommRingCat.ofHom (b : L →+* L)) =
      Spec.map (CommRingCat.ofHom (c : L →+* L)) := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  show a (b x) = c x
  exact (h x).symm

/-- **Level 2 (proved).** `SemilinearTwistAt` + `MulIsogeny` + `RigidityHom` ⟹ `SemilinearIsogAt`. -/
theorem semilinearIsogAt_of_twist (hMul : G0FibreSimple.MulIsogeny)
    (hR : G0FibreSimple.RigidityHom) (L : IF) (A : PkgI3.AbVar L)
    (ι' : O →+* PkgI3.AbVar.End A) (E : GQ → (A.X.left ⟶ A.X.left)) (α : GQ → (O ≃+* O))
    (h : SemilinearTwistAt L A ι' E α) : ∃ F : GQ → (A.X.left ⟶ A.X.left), SemilinearIsogAt L A ι' F := by
  classical
  choose bOf hbOf0 hbOf using exists_b
  let b : GQ → O := fun σ => if α σ = RingEquiv.refl O then 1 else bOf (α σ)
  have hb0 : ∀ σ, b σ ≠ 0 := fun σ => by
    by_cases hσ : α σ = RingEquiv.refl O
    · simp only [b, hσ, ite_true]; exact O_nontrivial
    · simp only [b, hσ, ite_false]; exact hbOf0 _
  have hb : ∀ σ a, b σ * α σ a = a * b σ := fun σ a => by
    by_cases hσ : α σ = RingEquiv.refl O
    · simp only [b, hσ, ite_true, RingEquiv.refl_apply, _root_.one_mul, _root_.mul_one]
    · simp only [b, hσ, ite_false]; exact hbOf _ a
  choose hiso τ hτσ hτ hμ hη using fun σ => And.intro (h σ).1 (h σ).2.1
  have htw := fun σ => (h σ).2.2.1
  have hk := fun σ => (h σ).2.2.2
  let F : GQ → (A.X.left ⟶ A.X.left) := fun σ => E σ ≫ (ι' (b σ)).hom.left
  have hFτ : ∀ σ, F σ ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ σ : L →+* L)) :=
    fun σ => by
      simp only [F, Category.assoc]
      rw [Over.w (ι' (b σ)).hom, hτ σ]
  -- twist relation, pushed through `ι(x)`
  have htwx : ∀ σ (x : O), (ι' x).hom.left ≫ E σ = E σ ≫ (ι' (α σ x)).hom.left := fun σ x =>
    htw σ x
  -- composite of `ι`'s
  have hcomp : ∀ x y : O, (ι' x).hom.left ≫ (ι' y).hom.left = (ι' (y * x)).hom.left := by
    intro x y; rw [map_mul]; rfl
  refine ⟨F, fun σ => ⟨⟨τ σ, hτσ σ, hFτ σ, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- group law
    have hf : μ[A.X].left ≫ (ι' (b σ)).hom.left =
        ((ι' (b σ)).hom ⊗ₘ (ι' (b σ)).hom).left ≫ μ[A.X].left := by
      rw [← Over.comp_left, IsMonHom.mul_hom, Over.comp_left]
    show μ[A.X].left ≫ E σ ≫ (ι' (b σ)).hom.left = _
    rw [← Category.assoc, hμ σ, Category.assoc, hf, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simp [F, Over.tensorHom_left]
    · simp [F, Over.tensorHom_left]
  · -- `𝒪`-linearity
    intro a
    show (ι' a).hom.left ≫ E σ ≫ (ι' (b σ)).hom.left = (E σ ≫ (ι' (b σ)).hom.left) ≫ (ι' a).hom.left
    rw [← Category.assoc, htwx, Category.assoc, Category.assoc, hcomp, hcomp, hb]
  · -- finite
    haveI := hiso σ
    haveI := (iota_isogeny hMul ι' (hb0 σ)).1
    show IsFinite (E σ ≫ (ι' (b σ)).hom.left)
    infer_instance
  · -- surjective
    haveI := hiso σ
    haveI := (iota_isogeny hMul ι' (hb0 σ)).2
    show Surjective (E σ ≫ (ι' (b σ)).hom.left)
    infer_instance
  · -- inflation from `Gal(L/ℚ)`
    intro k hkL
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hk σ k hkL
    have hbk : b k = 1 := by simp only [b, h2, ite_true]
    have hbσk : b (σ * k) = b σ := by simp only [b, h5]
    have hbkσ : b (k * σ) = b σ := by simp only [b, h6]
    refine ⟨?_, ?_, ?_⟩
    · show E k ≫ (ι' (b k)).hom.left = 𝟙 _
      rw [h1, hbk, map_one, Category.id_comp]; rfl
    · show E (σ * k) ≫ (ι' (b (σ * k))).hom.left = E σ ≫ (ι' (b σ)).hom.left
      rw [h3, hbσk]
    · show E (k * σ) ≫ (ι' (b (k * σ))).hom.left = E σ ≫ (ι' (b σ)).hom.left
      rw [h4, hbkσ]
  · -- the discrepancy
    intro ρ
    haveI := hiso (σ * ρ)
    -- `E_ρ E_σ` lies over `Spec τ_{σρ}`
    have hsp : Spec.map (CommRingCat.ofHom (τ ρ : L →+* L)) ≫
        Spec.map (CommRingCat.ofHom (τ σ : L →+* L)) =
          Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L)) := by
      apply spec_comp_spec
      intro x
      apply Subtype.ext
      change ((τ (σ * ρ) x : L) : Qbar) = ((τ ρ (τ σ x) : L) : Qbar)
      rw [hτσ, hτσ, hτσ, mul_inv_rev, act_mul]
    haveI : IsIso (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) :=
      ⟨⟨Spec.map (CommRingCat.ofHom ((τ (σ * ρ)).symm : L →+* L)), by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z; simp,
        by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]; congr 2; ext z;
           simp⟩⟩
    let Dl : A.X.left ⟶ A.X.left := inv (E (σ * ρ)) ≫ E ρ ≫ E σ
    have hDw : Dl ≫ A.X.hom = A.X.hom := by
      have e1 : inv (E (σ * ρ)) ≫ A.X.hom =
          A.X.hom ≫ inv (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) := by
        rw [IsIso.eq_comp_inv, Category.assoc, ← hτ, IsIso.inv_hom_id_assoc]
      simp only [Dl, Category.assoc]
      rw [hτ σ, reassoc_of% (hτ ρ), hsp, reassoc_of% e1, IsIso.inv_hom_id, Category.comp_id]
    let D : A.X ⟶ A.X := Over.homMk Dl hDw
    have hDη : η[A.X] ≫ D = η[A.X] := by
      apply Over.OverMorphism.ext
      have e2 : η[A.X].left ≫ inv (E (σ * ρ)) =
          inv (Spec.map (CommRingCat.ofHom (τ (σ * ρ) : L →+* L))) ≫ η[A.X].left := by
        rw [IsIso.comp_inv_eq, Category.assoc, hη, IsIso.inv_hom_id_assoc]
      rw [Over.comp_left]
      show η[A.X].left ≫ inv (E (σ * ρ)) ≫ E ρ ≫ E σ = η[A.X].left
      rw [reassoc_of% e2, reassoc_of% (hη ρ), hη σ, reassoc_of% hsp, IsIso.inv_hom_id_assoc]
    haveI : IsMonHom D := hR L A A D hDη
    let Dm : PkgI3.AbVar.End A := PkgI3.AbVar.Hom.mk' D
    obtain ⟨c, N, hN, hcb, hbc⟩ := exists_quasi_inv (hb0 (σ * ρ))
    let Y : PkgI3.AbVar.End A := ι' (b σ) * ι' (α σ (b ρ)) * Dm
    refine ⟨(N : ℤ), by exact_mod_cast hN.ne', Y * ι' c, ?_⟩
    -- left side: `E_ρ ι(b_ρ) E_σ ι(b_σ) [N] = E_{σρ} D ι(α_σ b_ρ) ι(b_σ) [N]`
    have hL : F ρ ≫ F σ = E (σ * ρ) ≫ Y.hom.left := by
      show (E ρ ≫ (ι' (b ρ)).hom.left) ≫ E σ ≫ (ι' (b σ)).hom.left = _
      have hY : Y.hom.left = Dl ≫ (ι' (α σ (b ρ))).hom.left ≫ (ι' (b σ)).hom.left := rfl
      rw [hY, Category.assoc, reassoc_of% (htwx σ (b ρ))]
      simp only [Dl, Category.assoc, IsIso.hom_inv_id_assoc]
    have hNc : ((N : ℤ) : PkgI3.AbVar.End A) = ι' c * ι' (b (σ * ρ)) := by
      rw [← map_mul, hcb, Int.cast_natCast, map_natCast]
    have hcomm : Y * ((N : ℤ) : PkgI3.AbVar.End A) = ((N : ℤ) : PkgI3.AbVar.End A) * Y :=
      (Int.cast_commute (N : ℤ) Y).eq.symm
    show F ρ ≫ F σ ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom.left =
      (E (σ * ρ) ≫ (ι' (b (σ * ρ))).hom.left) ≫ (Y * ι' c).hom.left
    have e3 : ((N : ℤ) : PkgI3.AbVar.End A).hom.left ≫ Y.hom.left =
        Y.hom.left ≫ ((N : ℤ) : PkgI3.AbVar.End A).hom.left := by
      show (Y * ((N : ℤ) : PkgI3.AbVar.End A)).hom.left =
        (((N : ℤ) : PkgI3.AbVar.End A) * Y).hom.left
      rw [hcomm]
    rw [← Category.assoc, hL, Category.assoc, ← e3, hNc]
    show E (σ * ρ) ≫ ((ι' (b (σ * ρ))).hom.left ≫ (ι' c).hom.left) ≫ Y.hom.left = _
    simp only [Category.assoc]
    rfl

/-- `SemilinearIsogMaps` from `SemilinearTwistIsos`, `MulIsogeny` and `RigidityHom` (proved). -/
theorem semilinearIsogMaps_of_twist (hMul : G0FibreSimple.MulIsogeny)
    (hR : G0FibreSimple.RigidityHom) (h : SemilinearTwistIsos) : SemilinearIsogMaps := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨E, α, hE⟩ := h Y Φ π hR1 hR2 j₀ y P hy hπ K PK hPK L hKL hfix
  exact semilinearIsogAt_of_twist hMul hR L _ _ E α hE

/-- **`ConjIsogMaps` from `SemilinearTwistIsos` and `MulIsogeny` (proved; `RigidityHom` and the
point lemmas are theorems).** -/
theorem conjIsogMaps_of_twist (hMul : G0FibreSimple.MulIsogeny) (h : SemilinearTwistIsos) :
    ConjIsogMaps :=
  conjIsogMaps_of_semilinearIsogMaps
    (semilinearIsogMaps_of_twist hMul G0FibreSimple.rigidityHom h)

/-- `KernelFieldExists` from the five leaves, FS5, `MulIsogeny` and `SemilinearTwistIsos`. -/
theorem kernelFieldExists_of_twist (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny)
    (hS : SemilinearTwistIsos) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_twist hMul hS)

end G0ModField.KernelField

end KfGlueLevel2

/-! # kf-glue, part 4: `SemilinearTwistIsos`, level 3 — A7 on the conjugates (proved)

`SemilinearTwistIsos` is proved from `TwistDescent`, a statement with no moduli content: for an
abelian variety `B` with a ring map `ι : 𝒪 → End B` over a Galois number field `K ⊆ ℚ̄` and a Hom
field `L ⊇ K` (`G_L` fixes every homomorphism between the conjugates `B_e = B ×_{K,e} ℚ̄`), if any
two conjugates are isomorphic over `ℚ̄` by an isomorphism twisting `ι` by some `α ∈ Aut 𝒪`, then
`B_L` has σ-semilinear twisted automorphisms `E_σ` (`SemilinearTwistAt`). This is Galois descent
from `ℚ̄` to `L` plus the bookkeeping of conjugate varieties. The hypothesis is proved for the
rational fibre `PK`: A7 in the manuscript's form (`LeafQM.AV.conj_iso_of_rational`, from R1fp and
R2fp) gives twisted QM isomorphisms between the base changes `Q_e` of `PK` along `e`, and
`IsBaseChangeOf` + rigidity (`rigidityHom`) identify `Q_e` with the conjugate `B_e` as abelian
varieties with `𝒪`-action. -/

section KfGlueLevel3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField.KernelField

open G0ModField

/-- Base change of an endomorphism of `B/K` to the conjugate `B_e = B ×_{K,e} ℚ̄`. -/
noncomputable def bcEnd (K : IF) (B : PkgI3.AbVar K) (e : K →ₐ[ℚ] Qbar)
    (f : PkgI3.AbVar.End B) : PkgI3.AbVar.End ((G4WeilRes.conjData K B).A e) :=
  @PkgI3.AbVar.Hom.mk' Qbar _ ((G4WeilRes.conjData K B).A e) ((G4WeilRes.conjData K B).A e)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (e : K →+* Qbar)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (e : K →+* Qbar))))
      (f := f.hom))

/-- **Glue (Galois descent of twisted isomorphisms; no moduli content).** For `B/K` with
`ι : 𝒪 → End B`, `K ⊆ L ⊆ ℚ̄` finite Galois with `L` a Hom field of `B` (`G_L` acts trivially on
the Hom lattice of the conjugates), if any two conjugates `B_{e₁}`, `B_{e₂}` are isomorphic over `ℚ̄`
by an isomorphism `φ` with `ι_{e₁}(α a) φ = φ ι_{e₂}(a)` for some `α ∈ Aut 𝒪`, then `B_L` has the
σ-semilinear twisted automorphisms of `SemilinearTwistAt` for `ι_L = endBC ∘ ι`.
*Argument* (model check): for `σ ∈ G_ℚ` let `Ē_σ = φ ≫ cmp_σ` on `B_{ℚ̄} = B_{K.val}` (`φ` the
twisted isomorphism `B_{K.val} → B_{σ⁻¹ K.val}`, chosen on representatives of `G_ℚ/G_L` with
`φ = id` on `G_L`, and `cmp` the comparison of `G4Conj` over `Spec σ⁻¹`); it is σ-semilinear,
preserves the group law and the origin, and twists `ι`. Since `L` is a Hom field, `φ` is fixed by
conjugation through `G_L`, so `Ē_σ` commutes with the descent datum of `B_{ℚ̄}/B_L`; Galois descent
for morphisms (Mathlib: the fpqc topology is subcanonical, `Sites/Fpqc.lean`, with
`morphismsDescend` to reach a finite Galois `L'/L`) gives `E_σ` on `B_L`. -/
def TwistDescent : Prop :=
  ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K] (B : PkgI3.AbVar K)
    (ιB : O →+* PkgI3.AbVar.End B) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hKL : K ≤ L),
    (∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1) →
    (∀ e₁ e₂ : K →ₐ[ℚ] Qbar, ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₂) ((G4WeilRes.conjData K B).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K B e₁ (ιB (α a))).hom ≫ φ.hom = φ.hom ≫ (bcEnd K B e₂ (ιB a)).hom) →
    ∃ (E : GQ → ((@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left)) (α : GQ → (O ≃+* O)),
      SemilinearTwistAt L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) E α

/-- **Transport (proved, rigidity).** A base change `Q` of `PK` along `e : K → ℚ̄`
(`IsBaseChangeOf`, a pullback square compatible with `ι` and `η`) is isomorphic to the conjugate
`B_e` as an abelian variety with `𝒪`-action. -/
theorem bc_transport (hR : G0FibreSimple.RigidityHom) {K : IF} (PK : QML3 K)
    (e : K →ₐ[ℚ] Qbar) (Q : QML3 Qbar) (hb : IsBaseChangeOf (e : K →+* Qbar) PK Q) :
    ∃ (θ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e) Q.A)
      (θ' : PkgI3.AbVar.Hom Q.A ((G4WeilRes.conjData K PK.A).A e)),
      θ.hom ≫ θ'.hom = 𝟙 _ ∧ θ'.hom ≫ θ.hom = 𝟙 _ ∧
      ∀ a : O, (bcEnd K PK.A e (PK.q.iota a)).hom ≫ θ.hom = θ.hom ≫ (Q.q.iota a).hom := by
  obtain ⟨g, hpb, hι, hη⟩ := hb
  let s := Spec.map (CommRingCat.ofHom (e : K →+* Qbar))
  let Ae : PkgI3.AbVar Qbar := (G4WeilRes.conjData K PK.A).A e
  have hpb0 : IsPullback (pullback.fst PK.A.X.hom s) (pullback.snd PK.A.X.hom s) PK.A.X.hom s :=
    IsPullback.of_hasPullback _ _
  let θ : pullback PK.A.X.hom s ≅ Q.A.X.left := hpb0.isoIsPullback _ _ hpb
  have hθfst : θ.hom ≫ g = pullback.fst PK.A.X.hom s := hpb0.isoIsPullback_hom_fst _ _ hpb
  have hθsnd : θ.hom ≫ Q.A.X.hom = pullback.snd PK.A.X.hom s :=
    hpb0.isoIsPullback_hom_snd _ _ hpb
  let h : Ae.X ⟶ Q.A.X := Over.homMk θ.hom hθsnd
  let hinv : Q.A.X ⟶ Ae.X := Over.homMk θ.inv ((Iso.inv_comp_eq θ).mpr hθsnd.symm)
  have hhi : h ≫ hinv = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.hom_inv_id
  have hih : hinv ≫ h = 𝟙 _ := by
    apply Over.OverMorphism.ext; exact θ.inv_hom_id
  have hu : ∀ {R : Type} [Field R] {U : Over (Spec (CommRingCat.of R))},
      (toUnit U).left = U.hom := fun {R _ U} => by
    have := Over.w (toUnit U); simpa using this
  have hid : ∀ (R : Type) [Field R], Spec.map (CommRingCat.ofHom (algebraMap R R)) = 𝟙 _ :=
    fun R _ => by rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hηQ : η[Q.A.X].left ≫ g = s ≫ η[PK.A.X].left := by
    have := hη 0
    have h0Q : Additive.toMul (Q.e.eta 0) = 1 := by rw [map_zero]; rfl
    have h0P : Additive.toMul (PK.e.eta 0) = 1 := by rw [map_zero]; rfl
    rw [h0Q, h0P] at this
    change (toUnit (PkgI3.AbVar.ptObj (K := Qbar) Qbar) ≫ η[Q.A.X]).left ≫ g =
      s ≫ (toUnit (PkgI3.AbVar.ptObj (K := K) K) ≫ η[PK.A.X]).left at this
    rw [Over.comp_left, Over.comp_left, hu, hu] at this
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, hid, Category.assoc] at this
    erw [Category.id_comp, Category.id_comp] at this
    exact this
  have hηW : η[Ae.X].left ≫ pullback.fst PK.A.X.hom s = s ≫ η[PK.A.X].left := by
    have e1 := G4Conj.one_left_fst s PK.A.X
    erw [e1]
  have hunit : η[Ae.X] ≫ h = η[Q.A.X] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    apply hpb.hom_ext
    · have hh : h.left ≫ g = pullback.fst PK.A.X.hom s := hθfst
      rw [Category.assoc, hh, hηW, hηQ]
    · rw [Category.assoc, Over.w h, Over.w η[Ae.X], Over.w η[Q.A.X]]
  have hunit' : η[Q.A.X] ≫ hinv = η[Ae.X] := by
    rw [← hunit, Category.assoc, hhi, Category.comp_id]
  haveI hmh : IsMonHom h := hR Qbar Ae Q.A h hunit
  haveI hmi : IsMonHom hinv := hR Qbar Q.A Ae hinv hunit'
  refine ⟨PkgI3.AbVar.Hom.mk' h, PkgI3.AbVar.Hom.mk' hinv, hhi, hih, fun a => ?_⟩
  apply Over.OverMorphism.ext
  rw [Over.comp_left, Over.comp_left]
  apply hpb.hom_ext
  · change ((Over.pullback s).map (PK.q.iota a).hom).left ≫ θ.hom ≫ g =
      θ.hom ≫ (Q.q.iota a).hom.left ≫ g
    rw [hι a, hθfst, ← Category.assoc θ.hom g, hθfst]
    exact pullback.lift_fst _ _ _
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [Over.w h, Over.w (Q.q.iota a).hom, Over.w h]
    exact Over.w (bcEnd K PK.A e (PK.q.iota a)).hom

/-- **A7 on the conjugates (proved).** For a `K`-point `yK` with object `PK` and rational
`π`-value, any two conjugates `PK.A_{e₁}`, `PK.A_{e₂}` are isomorphic over `ℚ̄` by an
isomorphism twisting `ι` by some `α ∈ Aut 𝒪`. -/
theorem conjTwist_of_rational (hR : G0FibreSimple.RigidityHom)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (hR1 : R1fpProps Y Φ) (hR2 : R2fpProps Y Φ π) {K : IF} (yK : fieldPt K ⟶ Y) (PK : QML3 K)
    (hyK : Φ K yK = M3.mk PK) (j₀ : ℚ)
    (hj : π.val (K := K) yK.left = OnePoint.some (algebraMap ℚ K j₀))
    (e₁ e₂ : K →ₐ[ℚ] Qbar) : ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e₁) ((G4WeilRes.conjData K PK.A).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K PK.A).A e₂) ((G4WeilRes.conjData K PK.A).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K PK.A e₁ (PK.q.iota (α a))).hom ≫ φ.hom =
          φ.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom := by
  obtain ⟨Q₁, Q₂, hb₁, hb₂, α, ⟨f⟩⟩ := conj_iso_of_rational hR1 hR2 yK PK hyK j₀ hj e₁ e₂
  obtain ⟨θ₁, θ₁', h11, h12, hι1⟩ := bc_transport hR PK e₁ Q₁ hb₁
  obtain ⟨θ₂, θ₂', h21, h22, hι2⟩ := bc_transport hR PK e₂ Q₂ hb₂
  have hι2' : ∀ a : O, (Q₂.q.iota a).hom ≫ θ₂'.hom = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom :=
    fun a => by
      calc (Q₂.q.iota a).hom ≫ θ₂'.hom
          = θ₂'.hom ≫ θ₂.hom ≫ (Q₂.q.iota a).hom ≫ θ₂'.hom := by rw [reassoc_of% h22]
        _ = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom ≫ θ₂.hom ≫ θ₂'.hom := by
            rw [reassoc_of% (hι2 a)]
        _ = θ₂'.hom ≫ (bcEnd K PK.A e₂ (PK.q.iota a)).hom := by rw [h21, Category.comp_id]
  refine ⟨α, PkgI3.AbVar.Hom.mk' (θ₁.hom ≫ f.φ.hom ≫ θ₂'.hom),
    PkgI3.AbVar.Hom.mk' (θ₂.hom ≫ f.ψ.hom ≫ θ₁'.hom), ?_, ?_, fun a => ?_⟩
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h22, reassoc_of% f.left, h11]
  · simp only [PkgI3.AbVar.Hom.hom_mk', Category.assoc]
    rw [reassoc_of% h12, reassoc_of% f.right, h21]
  · simp only [PkgI3.AbVar.Hom.hom_mk']
    have hf : (Q₁.q.iota (α a)).hom ≫ f.φ.hom = f.φ.hom ≫ (Q₂.q.iota a).hom := f.equivariant a
    simp only [Category.assoc]
    rw [reassoc_of% (hι1 (α a)), reassoc_of% hf, hι2' a]

/-- **`SemilinearTwistIsos` from `TwistDescent` (proved; A7 and rigidity).** -/
theorem semilinearTwistIsos_of_descent (hD : TwistDescent) : SemilinearTwistIsos := by
  intro Y Φ π hR1 hR2 j₀ y P hy hπ K _ _ PK hPK L _ _ hKL hfix
  obtain ⟨⟨yK, hyK, hyKP⟩, -⟩ := hPK
  have hyy : fieldMap K.val ≫ yK = y := (Φ Qbar).injective (hyKP.trans hy.symm)
  have hj : π.val (K := K) yK.left = OnePoint.some (algebraMap ℚ K j₀) := by
    have h2 : (π.val (K := K) yK.left).map (K.val : K →+* Qbar) =
        OnePoint.some (algebraMap ℚ Qbar j₀) := by
      have h1 := π.val_comp ((K.val : K →ₐ[ℚ] Qbar) : K →+* Qbar) yK.left
      rw [← hyy] at hπ
      exact h1.symm.trans hπ
    generalize π.val (K := K) yK.left = v at h2 ⊢
    induction v using OnePoint.rec with
    | infty => simp at h2
    | coe x =>
      rw [OnePoint.map_some] at h2
      have h3 : (K.val : K →+* Qbar) x = (K.val : K →+* Qbar) (algebraMap ℚ K j₀) := by
        rw [OnePoint.coe_eq_coe] at h2
        rw [h2]; exact (K.val.commutes j₀).symm
      rw [RingHom.injective _ h3]
  exact hD K PK.A PK.q.iota L hKL hfix
    (conjTwist_of_rational G0FibreSimple.rigidityHom hR1 hR2 yK PK hyK j₀ hj)

/-- **`ConjIsogMaps` from `TwistDescent` and `MulIsogeny` (proved).** -/
theorem conjIsogMaps_of_descent (hMul : G0FibreSimple.MulIsogeny) (hD : TwistDescent) :
    ConjIsogMaps :=
  conjIsogMaps_of_twist hMul (semilinearTwistIsos_of_descent hD)

/-- `KernelFieldExists` from the five leaves, FS5, `MulIsogeny` and `TwistDescent`. -/
theorem kernelFieldExists_of_descent (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny)
    (hD : TwistDescent) : KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_descent hMul hD)

/-- **`ConjIsogMaps` from mul-rigidity's leaf `KerUnitOpen` and `TwistDescent` (proved).** -/
theorem conjIsogMaps_of_kerUnitOpen (hK : MulRigidity.KerUnitOpen) (hD : TwistDescent) :
    ConjIsogMaps :=
  conjIsogMaps_of_descent (MulRigidity.mulIsogeny_of_kerUnitOpen hK) hD

/-- **`ConjIsogMaps` from glue only (proved):** mul-rigidity's two cotangent glue statements and
`TwistDescent`. -/
theorem conjIsogMaps_of_cotangent (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) (hD : TwistDescent) : ConjIsogMaps :=
  conjIsogMaps_of_descent (MulRigidity.mulIsogeny_of_cotangent h1 h2) hD

/-- **`KernelFieldExists`, final form (proved).** Leaves: `HomFreeFinite` (T6),
`NeronOggShafarevich`, `RaynaudCriterion`, `TorsionStructure`, `QMDichotomyYu` (T27),
`KerUnitOpen` (mul-rigidity; implied by the published `MulEtale`). Glue: FS5 `FibreComTrivial`
(g0-fibresimple) and `TwistDescent` (Galois descent). -/
theorem kernelFieldExists_of_kerUnitOpen (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hK : MulRigidity.KerUnitOpen) (hD : TwistDescent) :
    KernelFieldExists :=
  kernelFieldExists_of_five hHFF hNOS hRay hTors t27 h5 (conjIsogMaps_of_kerUnitOpen hK hD)

end G0ModField.KernelField

end KfGlueLevel3


end -- noncomputable section (g0-assemble3)


end G0A2_c40_kfglue

section G0A2_c50_twistdescent
-- (leaf-fold3) scratch/twist-descent/Part{XC,HFD,Main,Final}.lean verbatim (PartGDM omitted: the unused GaloisDescentMor of kf-glue is not defined in the kf-glue port of g0-assemble3)
/-! # twist-descent, part XC: comparison maps between base changes along different bases

Generic category theory (any `C` with pullbacks), generalizing `G4Conj.cmp` (one base `T`) to two
bases: for `f₂ = s ≫ f₁` with `s : T₂ ⟶ T₁`, the comparison `X ×_{S,f₂} T₂ → X ×_{S,f₁} T₁`
(`xc`), its pullback square, composition, and compatibility with base-changed endomorphisms,
units and multiplications. -/

section TwistDescentXC

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Obj

namespace TwistDescentXC

variable {C : Type*} [Category C] [HasPullbacks C] {S : C} (X : Over S)

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

/-- `X ×_{f₂} T₂ → X ×_{f₁} T₁` over `s`, for `f₂ = s ≫ f₁`. -/
noncomputable def xc {T₁ T₂ : C} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    pullback X.hom f₂ ⟶ pullback X.hom f₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ s)
    (by rw [pullback.condition, h, Category.assoc])

variable {T₁ T₂ T₃ : C} {f₁ : T₁ ⟶ S} {f₂ : T₂ ⟶ S} {f₃ : T₃ ⟶ S}

@[reassoc (attr := simp)]
theorem xc_fst (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc X s h ≫ pullback.fst X.hom f₁ = pullback.fst X.hom f₂ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xc_snd (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc X s h ≫ pullback.snd X.hom f₁ = pullback.snd X.hom f₂ ≫ s := pullback.lift_snd _ _ _

/-- The comparison square over `s` is a pullback. -/
theorem xc_isPullback (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    IsPullback (xc X s h) (pullback.snd X.hom f₂) (pullback.snd X.hom f₁) s := by
  have sq : IsPullback (pullback.fst X.hom f₂) (pullback.snd X.hom f₂) X.hom (s ≫ f₁) := by
    rw [← h]; exact IsPullback.of_hasPullback _ _
  have e : xc X s h = (IsPullback.of_hasPullback X.hom f₁).lift (pullback.fst X.hom f₂)
      (pullback.snd X.hom f₂ ≫ s) (by rw [sq.w, Category.assoc]) := by
    apply pullback.hom_ext
    · rw [xc_fst]; exact (IsPullback.lift_fst _ _ _ _).symm
    · rw [xc_snd]; exact (IsPullback.lift_snd _ _ _ _).symm
  rw [e]
  exact IsPullback.of_right' sq (IsPullback.of_hasPullback X.hom f₁)

theorem xc_comp (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (s' : T₃ ⟶ T₂) (h' : f₃ = s' ≫ f₂)
    (h'' : f₃ = (s' ≫ s) ≫ f₁) : xc X s' h' ≫ xc X s h = xc X (s' ≫ s) h'' := by
  apply pullback.hom_ext <;> simp

theorem xc_comp_eq (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (s' : T₃ ⟶ T₂) (h' : f₃ = s' ≫ f₂)
    (t : T₃ ⟶ T₁) (ht : f₃ = t ≫ f₁) (hst : s' ≫ s = t) :
    xc X s' h' ≫ xc X s h = xc X t ht := by
  subst hst; exact xc_comp X s h s' h' ht

theorem xc_congr {s s' : T₂ ⟶ T₁} (hs : s = s') (h : f₂ = s ≫ f₁) (h' : f₂ = s' ≫ f₁) :
    xc X s h = xc X s' h' := by
  subst hs; rfl

theorem xc_self (s : T₁ ⟶ T₁) (hs : s = 𝟙 T₁) (h : f₁ = s ≫ f₁) : xc X s h = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · rw [xc_snd, hs, Category.comp_id, Category.id_comp]

/-- `xc` intertwines base-changed endomorphisms. -/
theorem xc_map (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) (f : X ⟶ X) :
    ((Over.pullback f₂).map f).left ≫ xc X s h = xc X s h ≫ ((Over.pullback f₁).map f).left := by
  apply pullback.hom_ext
  · simp only [Category.assoc, xc_fst, Over.pullback_map_left, pullback.lift_fst, xc_fst_assoc]
  · simp only [Category.assoc, xc_snd, Over.pullback_map_left, pullback.lift_snd,
      pullback.lift_snd_assoc]

/-- `xc` on the self-products. -/
noncomputable def xc2 (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    ((Over.pullback f₂).obj X ⊗ (Over.pullback f₂).obj X).left ⟶
      ((Over.pullback f₁).obj X ⊗ (Over.pullback f₁).obj X).left :=
  pullback.lift (pullback.fst _ _ ≫ xc X s h) (pullback.snd _ _ ≫ xc X s h) (by
    show (pullback.fst _ _ ≫ xc X s h) ≫ pullback.snd X.hom f₁ =
      (pullback.snd _ _ ≫ xc X s h) ≫ pullback.snd X.hom f₁
    simp only [Category.assoc, xc_snd]
    exact pullback.condition_assoc s)

@[reassoc (attr := simp)]
theorem xc2_fst (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc2 X s h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ xc X s h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem xc2_snd (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    xc2 X s h ≫ pullback.snd _ _ = pullback.snd _ _ ≫ xc X s h :=
  pullback.lift_snd _ _ _

/-- **`xc` respects the multiplications.** -/
theorem xc_mul [MonObj X] (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    (μ[(Over.pullback f₂).obj X]).left ≫ xc X s h =
      xc2 X s h ≫ (μ[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, xc_fst, Category.assoc, G4Conj.mul_left_fst, G4Conj.mul_left_fst,
      ← Category.assoc (xc2 X s h)]
    congr 1
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, xc2_fst_assoc, xc_fst]
    · simp only [Category.assoc, pullback.lift_snd, xc2_snd_assoc, xc_fst]
  · rw [Category.assoc, xc_snd, Category.assoc]
    have h2 := Over.w (μ[(Over.pullback f₂).obj X])
    have h1 := Over.w (μ[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    show (pullback.fst _ _ ≫ pullback.snd X.hom f₂) ≫ s =
      xc2 X s h ≫ (pullback.fst _ _ ≫ pullback.snd X.hom f₁)
    rw [xc2_fst_assoc, xc_snd, Category.assoc]

/-- **`xc` respects the units.** -/
theorem xc_one [MonObj X] (s : T₂ ⟶ T₁) (h : f₂ = s ≫ f₁) :
    (η[(Over.pullback f₂).obj X]).left ≫ xc X s h = s ≫ (η[(Over.pullback f₁).obj X]).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, xc_fst, G4Conj.one_left_fst, Category.assoc, G4Conj.one_left_fst, h,
      Category.assoc]
  · rw [Category.assoc, xc_snd, Category.assoc]
    have h2 := Over.w (η[(Over.pullback f₂).obj X])
    have h1 := Over.w (η[(Over.pullback f₁).obj X])
    erw [← Category.assoc, h2, h1]
    simp

end TwistDescentXC

end TwistDescentXC


/-! # twist-descent, part HFD: descent of `G_L`-invariant morphisms between conjugates

For a field `K ⊆ ℚ̄`, `K`-schemes `X` (quasi-compact, quasi-separated) and `Y` (locally of finite
presentation), a number field `L ⊆ ℚ̄` and two embeddings `e₁L, e₂L : K → L`, a `ℚ̄`-morphism
`φ : X ×_{K,e₁} ℚ̄ → Y ×_{K,e₂} ℚ̄` (`eᵢ = (L ↪ ℚ̄) ∘ eᵢL`) that commutes with the Galois translates
by `G_L` is the base change of a morphism `X ×_{K,e₁L} L → Y ×_{K,e₂L} L` (`hfd`). Proof: EGA IV₃ 8.8.2 (`MorphDescend.exists_descend`,
proved) descends `φ` to a finite `L₁ ⊇ L`; pass to the normal closure `L'` of `L₁`; the descended
morphism is `Gal(L'/L)`-invariant (checked after the epimorphism `B_{ℚ̄} → B_{L'}`), so it descends
to `L` by `TwistDescentGD.descend` (Galois descent along `L'/L`, from Mathlib's fpqc descent). -/

section TwistDescentHFD

open CategoryTheory AlgebraicGeometry Limits
open TwistDescentXC

namespace TwistDescentHFD

/-- `Spec` of a ring map. -/
noncomputable abbrev sp {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom f)

theorem sp_comp_eq {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (s : R₁ →+* R₂)
    (t : R₂ →+* R₃) (u : R₁ →+* R₃) (h : ∀ x, t (s x) = u x) : sp t ≫ sp s = sp u := by
  rw [sp, sp, sp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact h x

theorem sp_eq {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (s : R₁ →+* R₂)
    (t : R₂ →+* R₃) (u : R₁ →+* R₃) (h : ∀ x, t (s x) = u x) : sp u = sp t ≫ sp s :=
  (sp_comp_eq s t u h).symm

theorem sp_id_eq {R : Type} [CommRing R] (t : R →+* R) (h : ∀ x, t x = x) : sp t = 𝟙 _ := by
  rw [sp, ← Spec.map_id]
  congr 1
  ext x
  exact h x

abbrev Qb : Type := AlgebraicClosure ℚ

variable {K : IntermediateField ℚ Qb} (X Y : Over (Spec (CommRingCat.of K)))

/-- `ℚ̄ → B_{L'}` comparisons are epimorphisms (flat surjective quasi-compact base change). -/
theorem xc_epi {L : IntermediateField ℚ Qb} (eL : K →+* L) (e : K →+* Qb)
    (h : sp e = sp (algebraMap L Qb) ≫ sp eL) : Epi (xc X (sp (algebraMap L Qb)) h) :=
  TwistDescentGD.epi_of_isPullback_field (xc_isPullback X _ h)

/-- **Hom-field descent.** -/
theorem hfd [QuasiCompact X.hom] [QuasiSeparated X.hom] [LocallyOfFinitePresentation Y.hom]
    {L : IntermediateField ℚ Qb} [FiniteDimensional ℚ L]
    (e₁L e₂L : K →+* L) (e₁ e₂ : K →+* Qb)
    (h₁ : sp e₁ = sp (algebraMap L Qb) ≫ sp e₁L) (h₂ : sp e₂ = sp (algebraMap L Qb) ≫ sp e₂L)
    (he₁ : ∀ x, (e₁L x : Qb) = e₁ x) (he₂ : ∀ x, (e₂L x : Qb) = e₂ x)
    (φ : pullback X.hom (sp e₁) ⟶ pullback Y.hom (sp e₂))
    (hφ : φ ≫ pullback.snd _ _ = pullback.snd _ _)
    (hinv : ∀ k : Qb ≃ₐ[ℚ] Qb, k ∈ L.fixingSubgroup →
      ∀ (k₁ : sp e₁ = sp (k : Qb →+* Qb) ≫ sp e₁) (k₂ : sp e₂ = sp (k : Qb →+* Qb) ≫ sp e₂),
        xc X (sp (k : Qb →+* Qb)) k₁ ≫ φ = φ ≫ xc Y (sp (k : Qb →+* Qb)) k₂) :
    ∃ φL : pullback X.hom (sp e₁L) ⟶ pullback Y.hom (sp e₂L),
      xc X (sp (algebraMap L Qb)) h₁ ≫ φL = φ ≫ xc Y (sp (algebraMap L Qb)) h₂ := by
  have hm₁ : ∀ x, e₁ x ∈ L := fun x => he₁ x ▸ (e₁L x).2
  have hm₂ : ∀ x, e₂ x ∈ L := fun x => he₂ x ▸ (e₂L x).2
  obtain ⟨L₁, ψ, hψ⟩ := MorphDescend.exists_descend L X Y e₁ e₂ hm₁ hm₂ φ hφ
  obtain ⟨L₁, hfin₁, hLL₁⟩ := L₁
  let L' : IntermediateField ℚ Qb := IntermediateField.normalClosure ℚ L₁ Qb
  have hL₁L' : L₁ ≤ L' := IntermediateField.le_normalClosure L₁
  have hLL' : L ≤ L' := hLL₁.trans hL₁L'
  let _ : Algebra L L' := G0ModField.incAlg hLL'
  have : IsScalarTower ℚ L L' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : FiniteDimensional ℚ L₁ := hfin₁
  have : FiniteDimensional ℚ L' := inferInstance
  have : IsGalois ℚ L' := inferInstance
  have : FiniteDimensional L L' := FiniteDimensional.right ℚ L L'
  have : IsGalois L L' := IsGalois.tower_top_of_isGalois ℚ L L'
  -- the maps at level `L'`
  let e₁' : K →+* L' := (algebraMap L L').comp e₁L
  have hq : sp e₁' = sp (algebraMap L L') ≫ sp e₁L := sp_eq _ _ _ fun _ => rfl
  let q : pullback X.hom (sp e₁') ⟶ pullback X.hom (sp e₁L) := xc X (sp (algebraMap L L')) hq
  have hpb := xc_isPullback X (sp (algebraMap L L')) hq
  let r₁ := MorphDescend.restrL L e₁ hm₁ ⟨L₁, hfin₁, hLL₁⟩
  let r₂ := MorphDescend.restrL L e₂ hm₂ ⟨L₁, hfin₁, hLL₁⟩
  have ha : sp e₁' = sp (IntermediateField.inclusion hL₁L' : L₁ →+* L') ≫ sp r₁ :=
    sp_eq _ _ _ fun x => Subtype.ext (he₁ x).symm
  have hb : sp r₂ = sp (IntermediateField.inclusion hLL₁ : L →+* L₁) ≫ sp e₂L :=
    sp_eq _ _ _ fun x => Subtype.ext (he₂ x)
  let f : pullback X.hom (sp e₁') ⟶ pullback Y.hom (sp e₂L) :=
    xc X (sp (IntermediateField.inclusion hL₁L' : L₁ →+* L')) ha ≫ ψ ≫
      xc Y (sp (IntermediateField.inclusion hLL₁ : L →+* L₁)) hb
  have hQ' : sp e₁ = sp (algebraMap L' Qb) ≫ sp e₁' := sp_eq _ _ _ fun x => (he₁ x)
  have hepi : Epi (xc X (sp (algebraMap L' Qb)) hQ') := xc_epi X e₁' e₁ hQ'
  -- `f` after `ℚ̄ → L'` is `φ ≫ (ℚ̄ → L)`
  have hfQ : xc X (sp (algebraMap L' Qb)) hQ' ≫ f = φ ≫ xc Y (sp (algebraMap L Qb)) h₂ := by
    have c1 : xc X (sp (algebraMap L' Qb)) hQ' ≫
        xc X (sp (IntermediateField.inclusion hL₁L' : L₁ →+* L')) ha =
        MorphDescend.cmp L X e₁ hm₁ ⟨L₁, hfin₁, hLL₁⟩ :=
      xc_comp_eq X _ _ _ _ (sp (algebraMap L₁ Qb)) (sp_eq _ _ _ fun _ => rfl)
        (sp_comp_eq _ _ _ fun _ => rfl)
    have c2 : MorphDescend.cmp L Y e₂ hm₂ ⟨L₁, hfin₁, hLL₁⟩ ≫
        xc Y (sp (IntermediateField.inclusion hLL₁ : L →+* L₁)) hb =
        xc Y (sp (algebraMap L Qb)) h₂ :=
      xc_comp_eq Y _ _ (sp (algebraMap L₁ Qb)) (sp_eq _ _ _ fun _ => rfl) _ _
        (sp_comp_eq _ _ _ fun _ => rfl)
    simp only [f]
    rw [← Category.assoc, c1, ← reassoc_of% hψ, c2]
  obtain ⟨φL, hφL⟩ := TwistDescentGD.descend hpb f (fun g => by
    have hc : sp e₁' = sp (g : L' →+* L') ≫ sp e₁' :=
      sp_eq _ _ _ fun x => g.commutes (e₁L x)
    refine ⟨xc X (sp (g : L' →+* L')) hc, ?_, xc_snd _ _ _, ?_⟩
    · exact xc_comp_eq X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun y => g.commutes y)
    · -- lift `g` to `k ∈ G_ℚ`
      obtain ⟨k, hk⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := L') (E := Qb)
        (g.restrictScalars ℚ)
      have hkx : ∀ x : L', k (x : Qb) = (g x : Qb) := fun x => by
        rw [← AlgEquiv.restrictNormalHom_apply L' k x, hk]; rfl
      have hkL : k ∈ L.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro y hy
        have := hkx (algebraMap L L' ⟨y, hy⟩)
        rw [g.commutes] at this
        exact this
      have hkL' : ∀ y : L, k (y : Qb) = y := fun y =>
        (IntermediateField.mem_fixingSubgroup_iff L k).mp hkL y y.2
      have k₁ : sp e₁ = sp (k : Qb →+* Qb) ≫ sp e₁ :=
        sp_eq _ _ _ fun x => by rw [← he₁ x]; exact hkL' _
      have k₂ : sp e₂ = sp (k : Qb →+* Qb) ≫ sp e₂ :=
        sp_eq _ _ _ fun x => by rw [← he₂ x]; exact hkL' _
      have hu : sp e₁ = sp ((algebraMap L' Qb).comp (g : L' →+* L')) ≫ sp e₁' :=
        sp_eq _ _ _ fun x => by
          show ((g (algebraMap L L' (e₁L x)) : L') : Qb) = e₁ x
          rw [g.commutes]; exact he₁ x
      have c4 : xc X (sp (algebraMap L' Qb)) hQ' ≫ xc X (sp (g : L' →+* L')) hc =
          xc X (sp (k : Qb →+* Qb)) k₁ ≫ xc X (sp (algebraMap L' Qb)) hQ' :=
        (xc_comp_eq X _ _ _ _ _ hu (sp_comp_eq _ _ _ fun _ => rfl)).trans
          (xc_comp_eq X _ _ _ _ _ hu (sp_comp_eq _ _ _ fun x => hkx x)).symm
      have c5 : xc Y (sp (k : Qb →+* Qb)) k₂ ≫ xc Y (sp (algebraMap L Qb)) h₂ =
          xc Y (sp (algebraMap L Qb)) h₂ :=
        xc_comp_eq Y _ _ _ _ _ _ (sp_comp_eq _ _ _ fun y => hkL' y)
      rw [← cancel_epi (xc X (sp (algebraMap L' Qb)) hQ'), ← Category.assoc, c4,
        Category.assoc, hfQ, ← Category.assoc, hinv k hkL k₁ k₂, Category.assoc, c5])
  refine ⟨φL, ?_⟩
  have c3 : xc X (sp (algebraMap L Qb)) h₁ = xc X (sp (algebraMap L' Qb)) hQ' ≫ q :=
    (xc_comp_eq X _ _ _ _ _ _ (sp_comp_eq _ _ _ fun _ => rfl)).symm
  rw [c3, Category.assoc, hφL, hfQ]

end TwistDescentHFD

end TwistDescentHFD


/-! # twist-descent, part MAIN: `TwistDescent` (kf-glue) proved

For `σ ∈ G_ℚ` with restriction `ρ = σ|_L`: the hypothesis gives a twisted isomorphism
`φ : B_{e₀} ≅ B_{σ⁻¹e₀}` over `ℚ̄` (`e₀ : K ↪ ℚ̄`); it is `G_L`-invariant (`L` is a Hom field,
`td_hom_inv`), so it descends to `φ_L : B_L → B ×_{K,τ∘(K↪L)} L` (`hfd`, `τ = σ⁻¹|_L`); then
`E = φ_L ≫ c_τ`, with `c_τ` the comparison over `Spec τ`. `φ_L` is a homomorphism by rigidity
(`G0FibreSimple.rigidityHom`, proved in kf-glue). `E` and `α` are chosen as functions of `σ|_L`,
with `E = 𝟙`, `α = id` on the trivial class (`twistDescent`). -/

section TwistDescentMain

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q
open TwistDescentXC TwistDescentHFD

namespace G0ModField.KernelField

open G0ModField

/-- **`G_L` fixes homomorphisms between conjugates** (from the Hom-field hypothesis of
`TwistDescent`): `k ∘ φ = φ ∘ k` for `k ∈ G_L` and `φ : B_{e₁} → B_{e₂}`. -/
theorem td_hom_inv {K : IF} [IsGalois ℚ K] (B : PkgI3.AbVar K) {L : IF} (hKL : K ≤ L)
    (hHF : ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1)
    (e₁ e₂ : K →ₐ[ℚ] Qbar)
    (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
    (k : Qbar ≃ₐ[ℚ] Qbar) (hk : k ∈ L.fixingSubgroup)
    (k₁ : sp (e₁ : K →+* Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (e₁ : K →+* Qbar))
    (k₂ : sp (e₂ : K →+* Qbar) = sp (k : Qbar →+* Qbar) ≫ sp (e₂ : K →+* Qbar)) :
    xc B.X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.hom.left =
      φ.hom.left ≫ xc B.X (sp (k : Qbar →+* Qbar)) k₂ := by
  classical
  have hs : ∀ e : K →ₐ[ℚ] Qbar, (G4WeilRes.embAct K k).symm e = e := by
    intro e
    ext x
    have hx : e x ∈ L :=
      hKL ((SetLike.ext_iff.mp (AlgHom.fieldRange_of_normal e) (e x)).mp ⟨x, rfl⟩)
    exact (IntermediateField.mem_fixingSubgroup_iff L _).mp (inv_mem hk) _ hx
  let m : G4WeilRes.HomLattice (G4WeilRes.conjData K B).A := Pi.single (e₁, e₂) φ
  have hm : G4WeilRes.conjAct K B k m = m := LinearEquiv.congr_fun (hHF k hk) m
  have h0 := G4WeilRes.conjAct_isConjAction K B k m e₁ e₂
  dsimp only at h0
  rw [hm] at h0
  have hme : m (e₁, e₂) = φ := Pi.single_eq_same _ _
  rw [hme] at h0
  have gen : ∀ (x y : K →ₐ[ℚ] Qbar) (hx : x = e₁) (hy : y = e₂)
      (p₁ : G4WeilRes.specEmb K e₁ = G4WeilRes.specGal k ≫ G4WeilRes.specEmb K x)
      (p₂ : G4WeilRes.specEmb K e₂ = G4WeilRes.specGal k ≫ G4WeilRes.specEmb K y),
      φ.hom.left ≫ G4Conj.cmp B.X (G4WeilRes.specGal k) p₂ =
        G4Conj.cmp B.X (G4WeilRes.specGal k) p₁ ≫ (m (x, y)).hom.left →
      xc B.X (sp (k : Qbar →+* Qbar)) k₁ ≫ φ.hom.left =
        φ.hom.left ≫ xc B.X (sp (k : Qbar →+* Qbar)) k₂ := by
    intro x y hx hy p₁ p₂ h
    subst hx hy
    rw [hme] at h
    exact h.symm
  exact gen _ _ (hs e₁) (hs e₂) (G4WeilRes.specEmb_symm K k e₁) (G4WeilRes.specEmb_symm K k e₂) h0

/-- The clauses of `SemilinearTwistAt` at one `σ`, in terms of `ρ = σ|_L`. -/
def TwistClause (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A) (ρ : L ≃ₐ[ℚ] L)
    (E : A.X.left ⟶ A.X.left) (α : O ≃+* O) : Prop :=
  IsIso E ∧
    (∃ τ : L ≃+* L, (∀ x : L, τ x = ρ⁻¹ x) ∧
      ∃ hτ : E ≫ A.X.hom = A.X.hom ≫ Spec.map (CommRingCat.ofHom (τ : L →+* L)),
        μ[A.X].left ≫ E =
          pullback.map A.X.hom A.X.hom A.X.hom A.X.hom E E
            (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm ≫ μ[A.X].left ∧
        η[A.X].left ≫ E = Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ η[A.X].left) ∧
    (∀ a : O, (ι' a).hom.left ≫ E = E ≫ (ι' (α a)).hom.left)

/-- `Spec ℚ̄ → Spec L` is an epimorphism. -/
theorem specQbar_epi (L : IF) : Epi (sp (algebraMap L Qbar)) := by
  obtain ⟨h1, h2, h3⟩ := TwistDescentGD.spec_field_props L Qbar
  infer_instance

/-- The trivial class: `E = 𝟙`, `α = id`. -/
theorem twistClause_one (L : IF) (A : PkgI3.AbVar L) (ι' : O →+* PkgI3.AbVar.End A) :
    TwistClause L A ι' 1 (𝟙 _) (RingEquiv.refl O) := by
  have hid : Spec.map (CommRingCat.ofHom ((RingEquiv.refl L : L ≃+* L) : L →+* L)) = 𝟙 _ := by
    rw [← Spec.map_id]; rfl
  refine ⟨inferInstance, ⟨RingEquiv.refl _, fun x => rfl, ?_, ?_, ?_⟩, fun a => ?_⟩
  · rw [hid, Category.id_comp, Category.comp_id]
  · rw [Category.comp_id]
    symm
    refine Eq.trans (congrArg (fun m => m ≫ μ[A.X].left) ?_) (Category.id_comp _)
    apply pullback.hom_ext <;> simp
  · rw [hid, Category.id_comp, Category.comp_id]
  · simp

set_option maxHeartbeats 1000000 in
/-- **The construction at one `σ`** (`E = φ_L ≫ c_τ`, `α = α_φ⁻¹`). -/
theorem td_construct {K : IF} [FiniteDimensional ℚ K] [IsGalois ℚ K] (B : PkgI3.AbVar K)
    (ιB : O →+* PkgI3.AbVar.End B) {L : IF} [FiniteDimensional ℚ L] [IsGalois ℚ L] (hKL : K ≤ L)
    (hHF : ∀ σ ∈ L.fixingSubgroup, G4WeilRes.conjAction K B σ = 1)
    (hTw : ∀ e₁ e₂ : K →ₐ[ℚ] Qbar, ∃ (α : O ≃+* O)
        (φ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₁) ((G4WeilRes.conjData K B).A e₂))
        (ψ : PkgI3.AbVar.Hom ((G4WeilRes.conjData K B).A e₂) ((G4WeilRes.conjData K B).A e₁)),
        φ.hom ≫ ψ.hom = 𝟙 _ ∧ ψ.hom ≫ φ.hom = 𝟙 _ ∧
        ∀ a : O, (bcEnd K B e₁ (ιB (α a))).hom ≫ φ.hom = φ.hom ≫ (bcEnd K B e₂ (ιB a)).hom)
    (σ : Qbar ≃ₐ[ℚ] Qbar) :
    ∃ (E : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) (α : O ≃+* O),
      TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) (AlgEquiv.restrictNormalHom L σ) E α := by
  letI : Algebra K L := incAlg hKL
  let e₀ : K →ₐ[ℚ] Qbar := K.val
  let e₂ : K →ₐ[ℚ] Qbar := G4WeilRes.embAct K σ⁻¹ e₀
  obtain ⟨α, φ, ψ, hφψ, hψφ, htw⟩ := hTw e₀ e₂
  let τ : L ≃+* L := (AlgEquiv.restrictNormalHom L σ⁻¹ : L ≃ₐ[ℚ] L).toRingEquiv
  have hτx : ∀ x : L, (τ x : Qbar) = σ⁻¹ x := fun x => AlgEquiv.restrictNormalHom_apply L σ⁻¹ x
  let e₁L : K →+* L := algebraMap K L
  let e₂L : K →+* L := (τ : L →+* L).comp e₁L
  have he₁ : ∀ x, (e₁L x : Qbar) = (e₀ : K →+* Qbar) x := fun x => rfl
  have he₂ : ∀ x, (e₂L x : Qbar) = (e₂ : K →+* Qbar) x := fun x => hτx _
  have h₁ : sp (e₀ : K →+* Qbar) = sp (algebraMap L Qbar) ≫ sp e₁L := sp_eq _ _ _ he₁
  have h₂ : sp (e₂ : K →+* Qbar) = sp (algebraMap L Qbar) ≫ sp e₂L := sp_eq _ _ _ he₂
  let φ₀ : pullback B.X.hom (sp (e₀ : K →+* Qbar)) ⟶ pullback B.X.hom (sp (e₂ : K →+* Qbar)) :=
    φ.hom.left
  let ψ₀ : pullback B.X.hom (sp (e₂ : K →+* Qbar)) ⟶ pullback B.X.hom (sp (e₀ : K →+* Qbar)) :=
    ψ.hom.left
  have hφs : φ₀ ≫ pullback.snd B.X.hom (sp (e₂ : K →+* Qbar)) =
      pullback.snd B.X.hom (sp (e₀ : K →+* Qbar)) := Over.w φ.hom
  have hψs : ψ₀ ≫ pullback.snd B.X.hom (sp (e₀ : K →+* Qbar)) =
      pullback.snd B.X.hom (sp (e₂ : K →+* Qbar)) := Over.w ψ.hom
  obtain ⟨φL, hφL⟩ := hfd B.X B.X e₁L e₂L _ _ h₁ h₂ he₁ he₂ φ₀ hφs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₀ e₂ φ k hk k₁ k₂)
  obtain ⟨ψL, hψL⟩ := hfd B.X B.X e₂L e₁L _ _ h₂ h₁ he₂ he₁ ψ₀ hψs
    (fun k hk k₁ k₂ => td_hom_inv B hKL hHF e₂ e₀ ψ k hk k₁ k₂)
  have ep₁ := xc_epi B.X e₁L _ h₁
  have ep₂ := xc_epi B.X e₂L _ h₂
  have hφψ' : φ₀ ≫ ψ₀ = 𝟙 _ := congrArg Over.Hom.left hφψ
  have hψφ' : ψ₀ ≫ φ₀ = 𝟙 _ := congrArg Over.Hom.left hψφ
  have hφψL : φL ≫ ψL = 𝟙 _ := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁), ← Category.assoc, hφL,
      Category.assoc, hψL, ← Category.assoc, hφψ', Category.id_comp, Category.comp_id]
  have hψφL : ψL ≫ φL = 𝟙 _ := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₂), ← Category.assoc, hψL,
      Category.assoc, hφL, ← Category.assoc, hψφ', Category.id_comp, Category.comp_id]
  have hφLs : φL ≫ pullback.snd B.X.hom (sp e₂L) = pullback.snd B.X.hom (sp e₁L) := by
    rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁), ← Category.assoc, hφL,
      Category.assoc, xc_snd, ← Category.assoc, hφs, xc_snd]
  have hc : sp e₂L = sp (τ : L →+* L) ≫ sp e₁L := sp_eq _ _ _ fun _ => rfl
  have hci : sp e₁L = sp (τ.symm : L →+* L) ≫ sp e₂L :=
    sp_eq _ _ _ fun x => τ.symm_apply_apply _
  let c := xc B.X (sp (τ : L →+* L)) hc
  let cinv := xc B.X (sp (τ.symm : L →+* L)) hci
  have hcc : c ≫ cinv = 𝟙 _ := by
    rw [xc_comp_eq B.X _ _ _ _ (sp (RingHom.id L)) (sp_eq _ _ _ fun _ => rfl)
      (sp_comp_eq _ _ _ fun x => τ.apply_symm_apply x)]
    exact xc_self B.X _ (sp_id_eq _ fun _ => rfl) _
  have hcc' : cinv ≫ c = 𝟙 _ := by
    rw [xc_comp_eq B.X _ _ _ _ (sp (RingHom.id L)) (sp_eq _ _ _ fun _ => rfl)
      (sp_comp_eq _ _ _ fun x => τ.symm_apply_apply x)]
    exact xc_self B.X _ (sp_id_eq _ fun _ => rfl) _
  -- `φ_L` is a homomorphism (rigidity)
  let A₂ : PkgI3.AbVar L := G4WeilRes.bcAlong B e₂L
  let φL' : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X ⟶ A₂.X := Over.homMk φL hφLs
  haveI := specQbar_epi L
  have o1 := xc_one B.X (sp (algebraMap L Qbar)) h₁
  have o2 := xc_one B.X (sp (algebraMap L Qbar)) h₂
  have o3 : η[((G4WeilRes.conjData K B).A e₀).X].left ≫ φ₀ =
      η[((G4WeilRes.conjData K B).A e₂).X].left := by
    show (η[((G4WeilRes.conjData K B).A e₀).X] ≫ φ.hom).left = _
    rw [IsMonHom.one_hom]
  have hηL : η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
      η[A₂.X].left := by
    have eq : sp (algebraMap L Qbar) ≫
        η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
        sp (algebraMap L Qbar) ≫ η[A₂.X].left :=
      (Category.assoc _ _ _).symm.trans <|
        (congrArg (· ≫ φL) o1.symm).trans <|
          (Category.assoc _ _ _).trans <|
            (congrArg (η[((G4WeilRes.conjData K B).A e₀).X].left ≫ ·) hφL).trans <|
              (Category.assoc _ _ _).symm.trans <|
                (congrArg (· ≫ xc B.X (sp (algebraMap L Qbar)) h₂) o3).trans o2
    exact (cancel_epi (sp (algebraMap L Qbar))).mp eq
  have hη : η[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X] ≫ φL' = η[A₂.X] :=
    Over.OverMorphism.ext hηL
  have hmon : IsMonHom φL' := G0FibreSimple.rigidityHom L _ _ φL' hη
  have hiso : IsIso (φL ≫ c) :=
    ⟨⟨cinv ≫ ψL, by rw [Category.assoc, reassoc_of% hcc, hφψL],
      by rw [Category.assoc, reassoc_of% hψφL, hcc']⟩⟩
  have hτ : (φL ≫ c) ≫ pullback.snd B.X.hom (sp e₁L) =
      pullback.snd B.X.hom (sp e₁L) ≫ sp (τ : L →+* L) := by
    rw [Category.assoc, xc_snd, reassoc_of% hφLs]
  have m1 : μ[(@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X].left ≫ φL =
      (φL' ⊗ₘ φL').left ≫ μ[A₂.X].left :=
    congrArg Over.Hom.left (IsMonHom.mul_hom (f := φL'))
  have m2 := xc_mul B.X (sp (τ : L →+* L)) hc
  have m3 : (φL' ⊗ₘ φL').left ≫ xc2 B.X (sp (τ : L →+* L)) hc =
      pullback.map (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom
        (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.hom (φL ≫ c) (φL ≫ c)
        (Spec.map (CommRingCat.ofHom (τ : L →+* L))) hτ.symm hτ.symm := by
    have f1 := xc2_fst B.X (sp (τ : L →+* L)) hc
    have f2 := Over.tensorHom_left_fst (pullback.snd B.X.hom (sp e₂L)) (pullback.snd B.X.hom (sp e₂L)) φL' φL'
    have g1 := xc2_snd B.X (sp (τ : L →+* L)) hc
    have g2 := Over.tensorHom_left_snd (pullback.snd B.X.hom (sp e₂L)) (pullback.snd B.X.hom (sp e₂L)) φL' φL'
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans <| (congrArg _ f1).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ c) f2).trans <|
          (Category.assoc _ _ _).trans (pullback.lift_fst _ _ _).symm
    · exact (Category.assoc _ _ _).trans <| (congrArg _ g1).trans <|
        (Category.assoc _ _ _).symm.trans <| (congrArg (· ≫ c) g2).trans <|
          (Category.assoc _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨φL ≫ c, α.symm, hiso, ⟨τ, fun x => ?_, hτ, ?_, ?_⟩, fun a => ?_⟩
  · rw [← map_inv]; rfl
  · exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ c) m1).trans <|
        (Category.assoc _ _ _).trans <|
          (congrArg ((φL' ⊗ₘ φL').left ≫ ·) m2).trans <|
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) m3)
  · exact (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ c) hηL).trans (xc_one B.X (sp (τ : L →+* L)) hc)
  · have hmap : ∀ f₁ f₂ : B.X ⟶ B.X,
        ((Over.pullback (sp (e₀ : K →+* Qbar))).map f₁).left ≫ φ₀ =
          φ₀ ≫ ((Over.pullback (sp (e₂ : K →+* Qbar))).map f₂).left →
        ((Over.pullback (sp e₁L)).map f₁).left ≫ φL =
          φL ≫ ((Over.pullback (sp e₂L)).map f₂).left := by
      intro f₁ f₂ h
      rw [← cancel_epi (xc B.X (sp (algebraMap L Qbar)) h₁)]
      calc xc B.X (sp (algebraMap L Qbar)) h₁ ≫ ((Over.pullback (sp e₁L)).map f₁).left ≫ φL
          = ((Over.pullback (sp (e₀ : K →+* Qbar))).map f₁).left ≫ φ₀ ≫
              xc B.X (sp (algebraMap L Qbar)) h₂ := by
            rw [← Category.assoc, ← xc_map B.X _ h₁ f₁, Category.assoc, hφL]
        _ = φ₀ ≫ xc B.X (sp (algebraMap L Qbar)) h₂ ≫
              ((Over.pullback (sp e₂L)).map f₂).left := by
            rw [← Category.assoc, h, Category.assoc, xc_map B.X _ h₂ f₂]
        _ = _ := by rw [← Category.assoc, ← hφL, Category.assoc]
    have ht := htw (α.symm a)
    rw [RingEquiv.apply_symm_apply] at ht
    have ht' := congrArg Over.Hom.left ht
    rw [Over.comp_left, Over.comp_left] at ht'
    have key := hmap (ιB a).hom (ιB (α.symm a)).hom ht'
    change ((Over.pullback (sp e₁L)).map (ιB a).hom).left ≫ φL ≫ c =
      (φL ≫ c) ≫ ((Over.pullback (sp e₁L)).map (ιB (α.symm a)).hom).left
    rw [← Category.assoc, key, Category.assoc, xc_map B.X _ hc, Category.assoc]

/-- **`TwistDescent` holds** (kf-glue's glue Prop, statement verbatim; no hypotheses). -/
theorem twistDescent : TwistDescent := by
  intro K _ _ B ιB L _ _ hKL hHF hTw
  classical
  have key : ∀ ρ : L ≃ₐ[ℚ] L, ∃ (E : (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
      (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) (α : O ≃+* O),
      TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
        ((@endBC K _ B L _ (incAlg hKL)).comp ιB) ρ E α := by
    intro ρ
    obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := L) (E := Qbar) ρ
    exact td_construct B ιB hKL hHF hTw σ
  let G : (L ≃ₐ[ℚ] L) → ((@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left ⟶
      (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL)).X.left) :=
    fun ρ => if ρ = 1 then 𝟙 _ else (key ρ).choose
  let Gα : (L ≃ₐ[ℚ] L) → (O ≃+* O) :=
    fun ρ => if ρ = 1 then RingEquiv.refl O else (key ρ).choose_spec.choose
  have hG : ∀ ρ, TwistClause L (@PkgI3.AbVar.baseChange K _ B L _ (incAlg hKL))
      ((@endBC K _ B L _ (incAlg hKL)).comp ιB) ρ (G ρ) (Gα ρ) := by
    intro ρ
    by_cases h : ρ = 1
    · subst h
      simp only [G, Gα, if_pos rfl]
      exact twistClause_one L _ _
    · simp only [G, Gα, if_neg h]
      exact (key ρ).choose_spec.choose_spec
  let r : GQ → (L ≃ₐ[ℚ] L) := fun σ => AlgEquiv.restrictNormalHom L (act σ)
  have hr : ∀ k ∈ GQL L, r k = 1 := by
    intro k hk
    ext x
    show ((AlgEquiv.restrictNormalHom L (act k) x : L) : Qbar) = (x : Qbar)
    rw [AlgEquiv.restrictNormalHom_apply]
    exact mem_GQL.mp hk x x.2
  refine ⟨fun σ => G (r σ), fun σ => Gα (r σ), fun σ => ?_⟩
  obtain ⟨h1, ⟨τ, hτ, hrest⟩, h3⟩ := hG (r σ)
  refine ⟨h1, ⟨τ, fun x => ?_, hrest⟩, h3, fun k hk => ?_⟩
  · rw [hτ x, ← map_inv, AlgEquiv.restrictNormalHom_apply]
    rfl
  · have e1 : r (σ * k) = r σ := by
      show AlgEquiv.restrictNormalHom L (act σ * act k) = _
      rw [map_mul]
      exact (congrArg (r σ * ·) (hr k hk)).trans (mul_one _)
    have e2 : r (k * σ) = r σ := by
      show AlgEquiv.restrictNormalHom L (act k * act σ) = _
      rw [map_mul]
      exact (congrArg (· * r σ) (hr k hk)).trans (one_mul _)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · show G (r k) = 𝟙 _
      rw [hr k hk]; exact if_pos rfl
    · show Gα (r k) = RingEquiv.refl O
      rw [hr k hk]; exact if_pos rfl
    · show G (r (σ * k)) = G (r σ); rw [e1]
    · show G (r (k * σ)) = G (r σ); rw [e2]
    · show Gα (r (σ * k)) = Gα (r σ); rw [e1]
    · show Gα (r (k * σ)) = Gα (r σ); rw [e2]

end G0ModField.KernelField

end TwistDescentMain


/-! # twist-descent, part FINAL: consequences (kf-glue's reductions with `TwistDescent` discharged) -/

section TwistDescentFinal

namespace G0ModField.KernelField

/-- **`ConjIsogMaps` from `MulIsogeny` alone** (kf-glue's `conjIsogMaps_of_descent` with
`twistDescent`). -/
theorem conjIsogMaps_of_mulIsogeny (hMul : G0FibreSimple.MulIsogeny) : ConjIsogMaps :=
  conjIsogMaps_of_descent hMul twistDescent

/-- **`ConjIsogMaps` from mul-rigidity's leaf `KerUnitOpen` alone.** -/
theorem conjIsogMaps_of_kerUnitOpen' (hK : MulRigidity.KerUnitOpen) : ConjIsogMaps :=
  conjIsogMaps_of_kerUnitOpen hK twistDescent

/-- **`ConjIsogMaps` from mul-rigidity's two cotangent glue statements alone.** -/
theorem conjIsogMaps_of_cotangent' (h1 : MulRigidity.KerUnitOpenOfCotangentSurj)
    (h2 : MulRigidity.CotangentMulN) : ConjIsogMaps :=
  conjIsogMaps_of_cotangent h1 h2 twistDescent

/-- **`KernelFieldExists` without `TwistDescent`.** Leaves: T6, NOS, Raynaud, TorsionStructure,
T27, `KerUnitOpen`; glue: FS5 `FibreComTrivial`. -/
theorem kernelFieldExists_of_kerUnitOpen' (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hK : MulRigidity.KerUnitOpen) :
    KernelFieldExists :=
  kernelFieldExists_of_kerUnitOpen hHFF hNOS hRay hTors t27 h5 hK twistDescent

/-- **`KernelFieldExists` without `TwistDescent`**, with `MulIsogeny`. -/
theorem kernelFieldExists_of_mulIsogeny (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hMul : G0FibreSimple.MulIsogeny) :
    KernelFieldExists :=
  kernelFieldExists_of_descent hHFF hNOS hRay hTors t27 h5 hMul twistDescent

end G0ModField.KernelField

end TwistDescentFinal



end G0A2_c50_twistdescent

section G0A2_c60_hodgebc2
-- (leaf-fold3) scratch/hodge-bc2/hbc_proof.lean.part and omega_proof.lean.part verbatim

/-! # hodge-bc2: `HodgeBCInjective` proved

* `cotL`: the `L`-vector space structure on `ω_{A_L} = 𝔪_ξ/𝔪_ξ²`, through
  `φ : L ≅ κ(η) → 𝒪_{𝒢,ξ}` (`η` the generic point of `Spec 𝓞_L`, `κ(η)` its function field);
* `bcCot_smulL`: `π^*` is semilinear over `L → L'`;
* `bcCot_core`: `π^*` maps `L`-independent vectors to `𝓞_{L'}`-independent vectors
  (`cotangent_baseChange_injective` of infra-stalks at the generic unit, flatness of `κ(η')/κ(η)`);
* `bcCot_basis`: an `L`-basis `b` of `ω_{A_L}` gives the `L'`-basis `π^* ∘ b` of `ω_{A_{L'}}`
  (with `cotangentSpanBC`);
* `hodgeBCInjective`: `ψ = bcHodge` maps the basis `1 ⊗ ιMulti_family b` of the Hodge space
  (`extFracBasis`) to the basis `1 ⊗ ιMulti_family (π^* ∘ b)`, hence is injective and preserves
  `finrank`. -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open scoped TensorProduct

section HodgeBC2

variable {K : Type} [Field K] {A : AbVar K}

variable {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}

end HodgeBC2

end ZInQ.HeightBC





/-! # hodge-bc2: `OmegaBaseChange` from the localization property of `omegaAt`

* Step A (`mem_of_forall_locSub`): a vector lies in a submodule `N` over a ring `R` if for every
  maximal ideal `P` some `d ∉ P` has `d • v ∈ N`.
* Step B (`omegaAt_bc_local`, conormal base change at a point `s'` of `Spec 𝓞_{L'}`): every
  `v ∈ (ω_{𝒢'})_{s'}` has a multiple `d • v`, `d ∉ s'`, in `𝓞_{L'} · π^*((ω_𝒢)_{s})`, `s` the image
  of `s'`. From infra-stalks' `pullback_stalkGen`: `I'_{e'(s')} = π^*(I_{e(s)}) · 𝒪_{𝒢',e'(s')}`.
* `OmegaLocalization` (named Prop, one group model): `(ω_𝒢)_s` is the localization of `ω_𝒢` at `s`.
* `omegaBaseChange_of_localization : OmegaLocalization → OmegaBaseChange`. -/

namespace ZInQ.HeightBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open scoped TensorProduct

/-! ### Step A: local–global for submodules -/

/-! ### Dedekind lemmas -/

section OmegaBC

variable {K : Type} [Field K] {A : AbVar K}

/-! ### Sections and stalks -/

variable {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']
    {𝒢 : GroupModel A L} {𝒢' : GroupModel A L'} {e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G}

/-! ### Toward `OmegaLocalization`: properties of the local lattices of one model -/

end OmegaBC

end ZInQ.HeightBC



end G0A2_c60_hodgebc2

section G0A2_c70_linkedtate
-- (leaf-fold3) scratch/g0-assemble3/parts/c10-c15 verbatim (linked-tate parts 95, 97, 98b, 98c, 98d, 98)
-- (g0-assemble3: scratch/linked-tate/parts/95_linked.lean, verbatim except `hdata.2.….2` (11×) → `….2.1` twice, for G7Data's added last clause)
/-! ## linked-tate: g0-assemble's joint glue Props `ModelG3G6` and `LinkedTateData`, reduced

Task linked-tate (2026-11-13). Both Props are g0-assemble's (`scratch/g0-assemble/parts/87_afterg7.lean`,
copied verbatim above with `LocalRamWild`, `G15RamWild`, `g15RamG_of_wild`, `afterG7_of`). Nothing
in them is changed. Over the pin-applied `Leaves.lean` (`R1fpProps` with `R1famProps`,
`R1univProps`).

* `ModelG3G6` is proved (`modelG3G6_of`) from
  - `HSyn.G0Split.FibreSimple` (an existing `GluePieces` field, G5-G6 on any number-field model of
    the fibre; g0-fibresimple reduced it to leaves, FS1b and FS5), for the `EndDivision` half of
    `G6Out`;
  - the new named glue Prop `QMModelG3` (G3: inertia at `p ∉ {3, ℓ}` acts trivially on
    `ℚ̄_ℓ ⊗ V_ℓ` of a base change of a `QML3` object), for the two `G3Out`;
  - and a proof (no input) of the noncommutativity half of `G6Out`: the QM structure `ι` of the
    `QML3` object and base change on endomorphisms are injective ring maps, and `𝒪` is not
    commutative (`oI_oH_ne`).
* `LinkedTateData` is proved (`linkedTateData_of`) from the leaf T7 (`PkgI3.CharPolyIndepOfEll`,
  Mumford §19 Thm 4; `TextbookLeaves.t7`) and the new named glue Prop `LinkedTateCore`:
  `G7Out` data at `ℓ = 5` and `ℓ = 3` whose scalars are the images `j_ℓ ∘ a`, `j_ℓ ∘ β` of one pair
  `a, β : G_ℚ → ℚ̄` (the scalar link), with g14-trace's `FrobTraceLink` for the two operator
  families and the wild-ramification clauses for the descended operators `ρ_ℓ` themselves
  (`RhoRamWild`). `G14TraceCompat` is then g14-trace's `g14TraceCompat_of_link` (T7), and
  `G15RamWild` for every `r_ℓ` with G8's output is transported from `ρ_ℓ` through G8's
  intertwiner (`localRamWild_of_rho`).
-/

section LinkedTateSec

noncomputable section

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-! ### §1 Base change on endomorphisms (copied from `scratch/bp-qmmoduli/QMAbVar.lean` L533-575:
`endBC` as unram-tate copied it, `specMap_flat`, `specMap_surjective`, `endBC_injective`) -/

section BaseChangeEnd

variable {K : Type} [Field K]

open scoped CategoryTheory.Obj in
/-- **Base change on endomorphisms** (copied verbatim from bp-qmmoduli's `endBC`):
`End_K(A) → End_L(A_L)`, `f ↦ (Over.pullback (Spec L → Spec K)).map f`, a ring homomorphism
(functoriality, and `Functor.map_mul` for the monoidal functor `Over.pullback`). -/
noncomputable def endBC (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    PkgI3.AbVar.End A →+* PkgI3.AbVar.End (A.baseChange L) where
  toFun f := @PkgI3.AbVar.Hom.mk' L _ (A.baseChange L) (A.baseChange L)
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map f.hom)
    (Functor.map.instIsMonHom (F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L))))
      (f := f.hom))
  map_one' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (𝟙 A.X) = 𝟙 _
    exact (Over.pullback _).map_id _
  map_mul' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (g.hom ≫ f.hom) = _
    rw [Functor.map_comp]; rfl
  map_zero' := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (1 : A.X ⟶ A.X) = 1
    exact Functor.map_one _
  map_add' f g := by
    apply PkgI3.AbVar.Hom.ext'
    change (Over.pullback _).map (f.hom * g.hom) = _
    rw [Functor.map_mul]; rfl

/-- `Spec L → Spec K` is flat, surjective and quasi-compact, so `Over.pullback` along it is
faithful (Mathlib, `Morphisms/FlatDescent.lean`). -/
instance specMap_flat (L : Type) [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

instance specMap_surjective (L : Type) [Field L] [Algebra K L] :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  ⟨fun _ => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩

/-- Base change on endomorphisms is injective. -/
theorem endBC_injective (A : PkgI3.AbVar K) (L : Type) [Field L] [Algebra K L] :
    Function.Injective (endBC A L) := by
  intro f g h
  apply PkgI3.AbVar.Hom.ext'
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map_injective
    (congrArg PkgI3.AbVar.Hom.hom h)

end BaseChangeEnd

/-! ### §2 The noncommutativity half of `G6Out` (proved) -/

/-- `i = ofInt ![0,1,0,0] ∈ 𝒪`. -/
def oI : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩

/-- `(1 + j)/2 = ofInt ![0,0,1,0] ∈ 𝒪`. -/
def oH : LeafQM.O := ⟨LeafQM.ofInt ![0, 0, 1, 0], ⟨_, rfl⟩⟩

/-- `𝒪` is not commutative: `i · (1+j)/2 = (i+k)/2 ≠ (i−k)/2 = (1+j)/2 · i`. -/
theorem oI_oH_ne : oI * oH ≠ oH * oI := by
  intro h
  have h1 : ((oI * oH : LeafQM.O) : LeafQM.B) =
      LeafQM.ofInt (LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0]) := LeafQM.ofInt_mul _ _
  have h2 : ((oH * oI : LeafQM.O) : LeafQM.B) =
      LeafQM.ofInt (LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0]) := LeafQM.ofInt_mul _ _
  have h0 : ((oI * oH : LeafQM.O) : LeafQM.B) = ((oH * oI : LeafQM.O) : LeafQM.B) :=
    congrArg Subtype.val h
  rw [h1, h2] at h0
  have h3 := congrArg QuaternionAlgebra.imK h0
  have e1 : LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0] 3 = 1 := by decide
  have e2 : LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0] 3 = -1 := by decide
  have h4 : ((LeafQM.mulCoord ![0, 1, 0, 0] ![0, 0, 1, 0] 3 : ℤ) : ℚ) / 2 =
      ((LeafQM.mulCoord ![0, 0, 1, 0] ![0, 1, 0, 0] 3 : ℤ) : ℚ) / 2 := h3
  rw [e1, e2] at h4
  norm_num at h4

/-- **`End` of a twice base-changed `QML3` surface is not commutative** (proved): the images of
`i` and `(1+j)/2` under `endBC ∘ endBC ∘ ι` do not commute (both base changes and `ι` are
injective ring maps). -/
theorem noncomm_baseChange2 {K : Type} [Field K] (PK : LeafQM.AV.QML3 K) (L : Type) [Field L] [Algebra K L]
    (L' : Type) [Field L'] [Algebra L L'] :
    ∃ x y : PkgI3.AbVar.End ((PK.A.baseChange L).baseChange L'), x * y ≠ y * x := by
  let f := (endBC (PK.A.baseChange L) L').comp ((endBC PK.A L).comp PK.q.iota)
  have hf : Function.Injective f :=
    (endBC_injective _ L').comp ((endBC_injective _ L).comp PK.q.injective)
  refine ⟨f oI, f oH, fun h => oI_oH_ne (hf ?_)⟩
  rw [map_mul, map_mul]
  exact h

/-! ### §3 The `EndDivision` half of `G6Out`, from `FibreSimple` (proved) -/

/-- **`EndDivision` for every number-field model of the fibre, from the glue piece
`FibreSimple`** (proved): a model `A'/L'` of `P`'s surface (`IsModelOver`) at a fibre context
gives `FibreOver` for `(abVarEquiv L').symm A'` with the inclusion `L' ⊆ ℚ̄`. -/
theorem endDivision_of_fibreSimple (hFS : HSyn.G0Split.FibreSimple)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : LeafQM.AV.PtEquiv Y} {π : LeafQM.AV.ToP1 Y.left} {u : ℚ}
    {P : LeafQM.AV.QML3 Qbar} (hctx : FibreCtx Y Φ π u P) (L' : IF) [FiniteDimensional ℚ L']
    (A' : PkgI3.AbVar L') (hA' : IsModelOver L' A' P) : PkgI3.EndDivision A' := by
  obtain ⟨h1, h2, hu, y, hy, hπ⟩ := hctx
  haveI : NumberField L' := numberField_of_fd L'
  exact hFS Y Φ π h1 h2 u hu ⟨L'⟩ ((LeafAdopt.abVarEquiv L').symm A')
    ⟨algebraMap L' Qbar, y, P, hy, hπ, hA'⟩

/-! ### §4 G3 on the model: the named glue Prop `QMModelG3` -/

/-- **Glue G3 on base changes of `QML3` objects** (linked-tate; G3 = Lemma PR(ii), h-decomposition
§3 G3, with R7a; N5 L524-529 and h-trust A6, C6). For a `QML3` object `PK` over `K ⊆ ℚ̄` and a
tower `K ≤ L ≤ L'` with `L'/ℚ` finite, every inertia element of `G_{L'}` at a place above a prime
`p ∉ {3, ℓ}` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ((PK.A)_{L,L'})` (`G0Galois.G3Out … ℓ {3}`). Route
(STANDARD; the Lean parts SPECULATIVE): `PK.A` has good reduction at every DVR with `3` a unit
(`LeafQM.AV.QML3.goodReduction`, proved in `Leaves.lean` from NOS, Raynaud and
`TorsionStructure`), good reduction is preserved by base change, and Néron–Ogg–Shafarevich
(R7a, (a) ⇒ (b), `PkgI2.inertiaTrivial_of_goodReduction`) makes inertia trivial on `A[ℓⁿ]`; the
open part is the transport from PkgI2's points and valuation rings of `\bar{L'}` to `ℚ̄_ℓ ⊗ V_ℓ`
and to places of `ℚ̄` (`resQ`). GLUE. -/
def QMModelG3 : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (PK : LeafQM.AV.QML3 K)
    (ℓ : ℕ) [Fact ℓ.Prime],
    letI : NumberField L' := numberField_of_fd L'
    G0Galois.G3Out (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ {3}

/-- **Glue: good reduction away from `3` gives `G3Out` on base changes** (linked-tate; the
transport half of G3/G11, given the leaf R7a = Néron–Ogg–Shafarevich, Serre–Tate 1968 Thm 1,
`PkgI2.NeronOggShafarevich`). If `A/K` (`K ⊆ ℚ̄`) has good reduction (PkgI2's
`HasGoodReduction`, an abelian scheme over the DVR) at every discrete valuation ring of `K` in
which `3` is a unit, then for every tower `K ≤ L ≤ L'` with `L'/ℚ` finite and every prime `ℓ`,
inertia of `G_{L'}` at places above `p ∉ {3, ℓ}` acts trivially on `ℚ̄_ℓ ⊗ V_ℓ(A_{L,L'})`.
Proof route (STANDARD): `v ∩ K` is such a DVR; NOS (a) ⇒ (b) over `K` makes inertia at `v`
trivial on every `A[ℓⁿ](K̄)`; inertia of `G_{L'}` restricts into it; triviality on all `A[ℓⁿ]`
is triviality on `T_ℓ`, hence on `ℚ̄_ℓ ⊗ V_ℓ`; base change does not change the points over
`\bar K = \bar{L'}` (`bcPt`, unram-tate). Only definitions are transported; no new literature
input. GLUE. -/
def GoodRedG3Bridge : Prop :=
  PkgI2.NeronOggShafarevich.{0} →
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (A : PkgI3.AbVar K),
    (∀ (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov], IsUnit (3 : Ov) →
      PkgI2.HasGoodReduction (ObjBridge.toGrp A) Ov) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      letI : NumberField L' := numberField_of_fd L'
      G0Galois.G3Out (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ {3}

/-- **`QMModelG3`, proved** from the leaves R6 (Raynaud), R7a (NOS), T5 (`TorsionStructure`)
through `LeafQM.AV.QML3.goodReduction` (proved in `Leaves.lean`: a `QML3` object has good
reduction at every DVR with `3` a unit) and the glue `GoodRedG3Bridge`. -/
theorem qmModelG3_of (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (hB : GoodRedG3Bridge) : QMModelG3 :=
  fun K L L' _ hKL hLL' PK ℓ _ => hB hNOS K L L' hKL hLL' PK.A
    (fun Ov _ h3 => LeafQM.AV.QML3.goodReduction (P := PK) hNOS hRay hTors Ov h3) ℓ

/-- `3 ∈ T(u)` (`3 ∈ S_mul`). -/
theorem three_mem_T (u : ℚ) : 3 ∈ T u :=
  Finset.mem_union_left _ (ZInQ.Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- `G3Out` is monotone in `T`. -/
theorem g3Out_mono {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {ℓ : ℕ}
    [Fact ℓ.Prime] {T₁ T₂ : Finset ℕ} (hT : T₁ ⊆ T₂) (h : G0Galois.G3Out A ℓ T₁) :
    G0Galois.G3Out A ℓ T₂ :=
  fun p hp hpT hpl v hv σ' hσ => h p hp (fun h' => hpT (hT h')) hpl v hv σ' hσ

/-- **`ModelG3G6`, proved** from the glue pieces `FibreSimple` (EndDivision) and `QMModelG3`
(G3); the noncommutativity of `End(A_{L'})` is proved (`noncomm_baseChange2`). -/
theorem modelG3G6_of (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3) :
    HSyn.G0AssembleMod.ModelG3G6 := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  have hT : ({3} : Finset ℕ) ⊆ T u := Finset.singleton_subset_iff.mpr (three_mem_T u)
  refine ⟨⟨endDivision_of_fibreSimple hFS hctx L' _ hmod, ?_⟩, ?_, ?_⟩
  · exact @noncomm_baseChange2 K _ PK L _ (incAlg hKL) L' _ (incAlg hLL')
  · exact g3Out_mono hT (hG3 K L L' hKL hLL' PK 5)
  · exact g3Out_mono hT (hG3 K L L' hKL hLL' PK 3)

/-! ### §5 `G15RamWild` from the descended operators (proved) -/

/-- **Glazer's wild-ramification clauses (i)-(ii) for an operator family `ρ` on `V`** (the form of
`LocalRamWild` on the descended `ρ_ℓ = β_ℓ⁻¹ a_ℓ Tm_ℓ` instead of on G8's `r_ℓ`; N5 L819-852,
D1-D4): for `p ≤ D` the absolute upper ramification groups `G_{ℚ_p}^t`, `t > U₀`, act trivially
through `decomp p`; for `p > D` wild inertia does. -/
def RhoRamWild (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V) : Prop :=
  letI : Fact p.Prime := ⟨hp⟩
  ((p : ℝ) ≤ (ZInQ.heightD : ℝ) →
      ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs p t, ρ (PkgI4.decomp p σ) = 1) ∧
    ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
      ρ (PkgI4.decomp p σ) = 1)

/-- If `e` intertwines `ρ` with `r ⊕ r` and `ρ(g) = 1`, then `r(g) = 1` (proved). -/
theorem toHom_eq_one_of_intertwines {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*} [AddCommGroup V]
    [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V)
    (r : PkgI4.GaloisRep ℓ 2)
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : G0Galois.Intertwines ρ r.mat e) (g : PkgI4.GQ) (hg : ρ g = 1) : r.toHom g = 1 := by
  have hmv : ∀ x : Fin 2 → PadicAlgCl ℓ, (r.mat g).mulVec x = x := by
    intro x
    have hx := h g (e.symm (x, 0))
    rw [hg] at hx
    change e (e.symm (x, 0)) = _ at hx
    rw [LinearEquiv.apply_symm_apply] at hx
    exact (congrArg Prod.fst hx).symm
  apply Units.ext
  rw [Units.val_one]
  change r.mat g = 1
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  rw [Matrix.toLin'_apply, hmv x, Matrix.toLin'_one, LinearMap.id_apply]

/-- **`LocalRamWild` for `r` from `RhoRamWild` for `ρ`** (proved), when G8's `e` intertwines `ρ`
with `r ⊕ r`. -/
theorem localRamWild_of_rho (p : ℕ) (hp : p.Prime) {ℓ : ℕ} [Fact ℓ.Prime] {V : Type*}
    [AddCommGroup V] [Module (PadicAlgCl ℓ) V] (ρ : PkgI4.GQ → Module.End (PadicAlgCl ℓ) V)
    (r : PkgI4.GaloisRep ℓ 2)
    (e : V ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (h : G0Galois.Intertwines ρ r.mat e) (hR : RhoRamWild p hp ρ) :
    @HSyn.G0AssembleMod.LocalRamWild p ⟨hp⟩ ℓ _ r := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨fun hp' t ht σ hσ => ?_, fun hp' σ hσ => ?_⟩
  · exact toHom_eq_one_of_intertwines ρ r e h _ (hR.1 hp' t ht σ hσ)
  · exact toHom_eq_one_of_intertwines ρ r e h _ (hR.2 hp' σ hσ)

/-! ### §6 `LinkedTateData` from T7 and the named glue Prop `LinkedTateCore` -/

/-- **Glue: linked Tate data on G7's model, at the level of the descended operators**
(linked-tate; the content of g0-assemble's `LinkedTateData` minus what is proved here). For every
fibre context and G7 data: one pair of scalar functions `a, β : G_ℚ → ℚ̄` and embeddings
`j₅ : ℚ̄ → ℚ̄₅`, `j₃ : ℚ̄ → ℚ̄₃` (N5 L719-722: the scalars `a_σ = deg(μ_σ)^{-1/4}`, `β_σ` lie in one
number field and are mapped to `ℚ̄_ℓ` by embeddings), and operator data at `ℓ = 5` and `ℓ = 3`
with
* g0-mod-galois' `G7Out` at each `ℓ` for the scalars `j_ℓ ∘ a`, `j_ℓ ∘ β` (the Tate functor applied
  to one family `m_σ = μ_σ ∘ σ`; g0-mod-field's `TateBridge`, which unram-tate proved for each `ℓ`
  separately from I3.M0, plus `dim A_{L'} = 2` and `rank_ℤ End(A_{L'}) = 4`);
* g14-trace's `FrobTraceLink` for the two operator families (N5 L777-786: reduction at a
  Frobenius, the relative Frobenius composed with `μ̄_τ`);
* Glazer's wild-ramification clauses (i)-(ii) for the descended operators `ρ₅` at `p ≠ 5` and
  `ρ₃` at `p = 5` (`RhoRamWild`; N5 L819-852, D1-D4).
GLUE. -/
def LinkedTateCore : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (a b : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (a g)) (fun g => j5 (b g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (a g)) (fun g => j3 (b g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₅ (fun g => j5 (a g)) (fun g => j5 (b g)))) ∧
        (p = 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₃ (fun g => j3 (a g)) (fun g => j3 (b g))))

/-- **Glue: the endomorphism ring of the QM model has rank 4** (linked-tate; G5-G6 + A9, N5
L564-577). For a `QML3` object `PK` over `K ⊆ ℚ̄` and a tower `K ≤ L ≤ L'` (`L'/ℚ` finite), if every
nonzero endomorphism of `A' = (PK.A)_{L,L'}` is an isogeny (`EndDivision`, which `FibreSimple`
supplies for the fibre), then `End_{L'}(A')` is a free `ℤ`-module of rank 4. Route (STANDARD,
UNVERIFIED numbering): `End(A')` is finitely generated and torsion-free (Mumford §19 Thm 3:
`End ⊗ ℤ_ℓ ↪ End T_ℓ`), so free; `End⁰(A')` is a division algebra containing `ι(B)`, `B = (2,−3)`
of dimension 4, and by Albert's classification for simple abelian surfaces in characteristic 0
(Mumford §21) it is `ℚ`, real quadratic, CM quartic or an indefinite quaternion algebra over `ℚ`;
only the last contains `B`, so `End⁰(A') = B`. GLUE (literature-backed). -/
def QMEndRank : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (PK : LeafQM.AV.QML3 K),
    PkgI3.EndDivision (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL'))) = 4

/-- **Glue: `LinkedTateCore` given `dim A_{L'} = 2` and `rank End(A_{L'}) = 4`** (linked-tate; the
same conclusion as `LinkedTateCore`, under the two hypotheses that g0-mod-field's `TateBridge`
also assumes). GLUE. -/
def LinkedTateCoreDR : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    letI : NumberField L' := numberField_of_fd L'
    ∃ (a b : PkgI4.GQ → PkgI4.Qbar) (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
      (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3)
      (Tm₅ : PkgI4.GQ → Module.End (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (c₅ ε₅ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 5)
      (u₅ : GlueDescent.MatrixUnits2 (PadicAlgCl 5)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5))
      (Tm₃ : PkgI4.GQ → Module.End (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3))
      (c₃ ε₃ : PkgI4.GQ → PkgI4.GQ → PadicAlgCl 3)
      (u₃ : GlueDescent.MatrixUnits2 (PadicAlgCl 3)
        (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3)),
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 5 Tm₅ c₅ ε₅
        (fun g => j5 (a g)) (fun g => j5 (b g)) u₅ ∧
      G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) 3 Tm₃ c₃ ε₃
        (fun g => j3 (a g)) (fun g => j3 (b g)) u₃ ∧
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) Tm₅ Tm₃ ∧
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₅ (fun g => j5 (a g)) (fun g => j5 (b g)))) ∧
        (p = 5 → RhoRamWild p hp
          (GlueDescent.rho Tm₃ (fun g => j3 (a g)) (fun g => j3 (b g))))

/-- **`LinkedTateCore`, proved** from `FibreSimple` (EndDivision of the model), `QMEndRank` and
`LinkedTateCoreDR`; `dim A_{L'} = 2` is proved (`QML3.surface` and g0-dim's
`pkgI3_dim_baseChange`, twice). -/
theorem linkedTateCore_of (hFS : HSyn.G0Split.FibreSimple) (hR : QMEndRank)
    (hDR : LinkedTateCoreDR) : LinkedTateCore := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  have hmod := hdata.2.2.2.2.2.2.2.2.2.2.2.1
  have hdata' := hdata
  obtain ⟨K, hKL, PK, -, rfl⟩ := hdata.1
  have hdim : (@PkgI3.AbVar.baseChange L _ (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL))
      L' _ (incAlg hLL')).dim = 2 := by
    rw [@G0Dim.pkgI3_dim_baseChange L _ L' _ (incAlg hLL'),
      @G0Dim.pkgI3_dim_baseChange K _ L _ (incAlg hKL)]
    exact PK.surface
  exact hDR Y Φ π u P hctx L _ ε N χ β L' hLL' hdata' hdim
    (hR K L L' hKL hLL' PK (endDivision_of_fibreSimple hFS hctx L' _ hmod))

/-- **`LinkedTateData`, proved** from the leaf T7 (`PkgI3.CharPolyIndepOfEll`) and the glue Prop
`LinkedTateCore`: for G8's `r₅`, `r₃` on the linked data and any `ι₅ = j₅ ∘ γ` (`exists_comp_eq`),
`ι₃ := j₃ ∘ γ` makes the traces compatible (g14-trace's `g14TraceCompat_of_link`), and
`G15RamWild` holds because G8's intertwiner carries `RhoRamWild` from `ρ_ℓ` to `r_ℓ`. -/
theorem linkedTateData_of (hM : PkgI3.CharPolyIndepOfEll) (hC : LinkedTateCore) :
    HSyn.G0AssembleMod.LinkedTateData := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hdata
  letI : NumberField L' := numberField_of_fd L'
  obtain ⟨a, b, j5, j3, Tm₅, c₅, ε₅, u₅, Tm₃, c₃, ε₃, u₃, h5, h3, hF, hR⟩ :=
    hC Y Φ π u P hctx L A ε N χ β L' hLL' hdata
  refine ⟨Tm₅, c₅, ε₅, fun g => j5 (a g), fun g => j5 (b g), u₅,
    Tm₃, c₃, ε₃, fun g => j3 (a g), fun g => j3 (b g), u₃, h5, h3, ?_⟩
  intro r₅ r₃ h8₅ h8₃ i ιC ι5
  obtain ⟨gm, hgm⟩ := G14Trace.exists_comp_eq ι5 j5
  refine ⟨j3.comp gm, ?_, ?_⟩
  · exact G14Trace.g14TraceCompat_of_link hM ⟨i, ιC, ι5, j3.comp gm, r₅, r₃⟩ j5 j3 gm hgm rfl a b
      Tm₅ Tm₃ h8₅ h8₃ hF
  · obtain ⟨-, e5, he5, -⟩ := h8₅
    obtain ⟨-, e3, he3, -⟩ := h8₃
    intro p hp
    exact ⟨fun h => localRamWild_of_rho p hp _ r₅ e5 he5 ((hR p hp).1 h),
      fun h => localRamWild_of_rho p hp _ r₃ e3 he3 ((hR p hp).2 h)⟩

/-! ### §7 `AfterG7` with the two joint Props replaced (proved) -/

/-- **`AfterG7` (G8-G16)** from g0-assemble's inputs of `afterG7_of` with `ModelG3G6` replaced by
`FibreSimple` and `QMModelG3`, and `LinkedTateData` by `LinkedTateCore` (T7 is `t.t7`). -/
theorem afterG7_of_linked (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : G0Galois.GaloisPieces) (hDF : G0ModNewform.DirichletOfFinite)
    (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hFS : HSyn.G0Split.FibreSimple) (hG3 : QMModelG3) (hC : LinkedTateCore) : AfterG7 :=
  HSyn.G0AssembleMod.afterG7_of r t m hDF hCar hSw hL8 hAd (modelG3G6_of hFS hG3)
    (linkedTateData_of t.t7 hC)

/-- **`AfterG7` with G3 reduced to the bundle's R6, R7a, T5 and `GoodRedG3Bridge`, and
`LinkedTateCore` to `QMEndRank` and `LinkedTateCoreDR`.** -/
theorem afterG7_of_linked' (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : G0Galois.GaloisPieces) (hDF : G0ModNewform.DirichletOfFinite)
    (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hFS : HSyn.G0Split.FibreSimple) (hB : GoodRedG3Bridge) (hR : QMEndRank)
    (hDR : LinkedTateCoreDR) : AfterG7 :=
  afterG7_of_linked r t m hDF hCar hSw hL8 hAd hFS (qmModelG3_of r.r7a r.r6 t.t5 hB)
    (linkedTateCore_of hFS hR hDR)

end HSyn.LinkedTate

end

end LinkedTateSec



-- (g0-assemble3: scratch/linked-tate/parts/97_linkeddata.lean, verbatim)
/-! ## linked-tate: the linked Tate data are constructed; `LinkedTateCoreDR` reduced to `LinkedFrobRam`

unram-tate proved g0-mod-field's `TateBridge` (copied above, `UnramTate.tateBridge_of_tateModuleFree`)
by applying the Tate functor `opV` to the points-level descent datum `m_σ = μ_σ ∘ σ`:
`Tm g = opV(Θ ∘ m_{hgh⁻¹} ∘ Θ⁻¹)`, `a = 1`, `β' g = γ(hgh⁻¹)`, separately for each `ℓ`.
Here the same construction is run once for `ℓ = 5` and `ℓ = 3` with **one** scalar function
`γ₀ : G_ℚ → ℚ̄` (`scalarTransferQ`, unram-tate's `scalarTransfer` with target `ℚ̄`), mapped to
`ℚ̄_ℓ` by embeddings `j_ℓ : ℚ̄ → ℚ̄_ℓ`. So the scalar link of g14-trace (finding F1) holds by
construction, and the existence half of `LinkedTateCoreDR` is proved (from the leaf I3.M0
through `TateCont`). What is left is the named glue Prop `LinkedFrobRam`: `FrobTraceLink` and
`RhoRamWild` for these canonical operators (`tmOf`), for every choice of the data that the
construction uses.
-/

section LinkedDataSec

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **`ScalarTransfer` with target `ℚ̄`, tied to `β/a`** (proved; unram-tate's `scalarTransfer`
with `PadicAlgCl ℓ` replaced by `ℚ̄`): `γ_ℂ = β/a` takes algebraic values (unram-tate's argument),
so for an embedding `κ : ℚ̄ → ℂ` every value has a preimage `γ₀(σ)`; injectivity of `κ` transfers
`∂γ_ℂ = n/d` to `γ₀`. -/
theorem scalarTransferQ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (a : GQ → ℝ)
    (β : GQ → ℂˣ) (ε : GQ → GQ → ℂˣ) (n d : GQ → GQ → ℤ)
    (hd : ∀ σ τ, d σ τ ≠ 0)
    (hna : ∀ σ τ, (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) =
      (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ))
    (hβe : ∀ σ τ, β σ * β τ = ε σ τ * β (σ * τ))
    (ha0 : ∀ σ, 0 < a σ)
    (hcos : ∀ σ, ∀ k ∈ GQL L', a (σ * k) = a σ ∧ β (σ * k) = β σ)
    (hone : ∀ k ∈ GQL L', a k = 1 ∧ β k = 1) :
    ∃ (gam : GQ → PkgI4.Qbar) (κ : PkgI4.Qbar →ₐ[ℚ] ℂ),
      (∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) ∧ (∀ σ, gam σ ≠ 0) ∧
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) ∧
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) ∧ (∀ k ∈ GQL L', gam k = 1) := by
  let gC : GQ → ℂ := fun σ => (β σ : ℂ) / ((a σ : ℝ) : ℂ)
  let q : GQ → GQ → ℚ := fun σ τ => (n σ τ : ℚ) / d σ τ
  have ha0' : ∀ σ, ((a σ : ℝ) : ℂ) ≠ 0 := fun σ => Complex.ofReal_ne_zero.mpr (ha0 σ).ne'
  have hq : ∀ σ τ, gC σ * gC τ = (q σ τ : ℂ) * gC (σ * τ) := by
    intro σ τ
    have h1 := hna σ τ
    have h2 : (β σ : ℂ) * β τ = ε σ τ * β (σ * τ) := by
      rw [← Units.val_mul, hβe σ τ, Units.val_mul]
    have hdC : (d σ τ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hd σ τ)
    have hε : (ε σ τ : ℂ) = (((a σ * a τ * ((n σ τ : ℝ) / d σ τ)) : ℝ) : ℂ) / ((a (σ * τ) : ℝ) : ℂ) := by
      rw [h1, mul_div_cancel_right₀ _ (ha0' _)]
    have hA := ha0' σ
    have hB := ha0' τ
    have hAB := ha0' (σ * τ)
    simp only [gC, q]
    rw [div_mul_div_comm, h2, hε]
    push_cast
    field_simp
  have hgcos : ∀ σ, ∀ k ∈ GQL L', gC (σ * k) = gC σ := by
    intro σ k hk; simp only [gC]; rw [(hcos σ k hk).1, (hcos σ k hk).2]
  have hg1 : ∀ k ∈ GQL L', gC k = 1 := by
    intro k hk; simp only [gC]; rw [(hone k hk).1, (hone k hk).2]; simp
  have hg0 : ∀ σ, gC σ ≠ 0 := fun σ => div_ne_zero (Units.ne_zero _) (ha0' σ)
  have hpow : ∀ (σ : GQ) (k : ℕ), ∃ r : ℚ, gC σ ^ k = (r : ℂ) * gC (σ ^ k) := by
    intro σ k
    induction k with
    | zero => exact ⟨1, by rw [pow_zero, pow_zero, hg1 1 (one_mem _)]; simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * q (σ ^ k) σ, ?_⟩
      rw [pow_succ, hr, _root_.mul_assoc, hq, pow_succ]
      push_cast; ring
  have hfin : ∀ σ : GQ, ∃ r : ℕ, 0 < r ∧ σ ^ r ∈ GQL L' := by
    intro σ
    let σ' : Qbar ≃ₐ[ℚ] Qbar := σ
    let s := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' σ'
    have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
    refine ⟨orderOf s, hs.orderOf_pos, ?_⟩
    have h1 : AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := Qbar) L' (σ' ^ orderOf s) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    rw [mem_GQL]
    intro x hx
    exact (AlgEquiv.restrictNormal_eq_one_iff L' _).mp h1 x hx
  have halg : ∀ σ, IsIntegral ℚ (gC σ) := by
    intro σ
    obtain ⟨r, hr0, hr⟩ := hfin σ
    obtain ⟨t, ht⟩ := hpow σ r
    rw [hg1 _ hr, _root_.mul_one] at ht
    refine ⟨Polynomial.X ^ r - Polynomial.C t, Polynomial.monic_X_pow_sub_C t hr0.ne', ?_⟩
    simp [Polynomial.eval₂_sub, ht]
  let κ : PkgI4.Qbar →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hpre : ∀ σ, ∃ y : PkgI4.Qbar, κ y = gC σ := by
    intro σ
    have hint := halg σ
    set P := minpoly ℚ (gC σ) with hP
    have hP0 : P.map (algebraMap ℚ PkgI4.Qbar) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : ((P.map (algebraMap ℚ PkgI4.Qbar)).map (κ : PkgI4.Qbar →+* ℂ)).IsRoot (gC σ) := by
      rw [Polynomial.map_map, κ.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        minpoly.aeval]
    obtain ⟨y, hy⟩ :=
      (IsAlgClosed.splits (P.map (algebraMap ℚ PkgI4.Qbar))).mem_range_of_isRoot hP0 hroot
    exact ⟨y, hy⟩
  choose gam hgam using hpre
  have hκ : Function.Injective κ := κ.toRingHom.injective
  refine ⟨gam, κ, hgam, ?_, ?_, ?_, ?_⟩
  · intro σ h0
    apply hg0 σ
    rw [← hgam, h0, map_zero]
  · intro σ τ
    apply hκ
    rw [map_mul, map_mul, hgam, hgam, map_div₀, map_intCast, map_intCast, hgam, hq]
    simp only [q]
    push_cast
    ring
  · intro σ k hk
    apply hκ
    rw [hgam, hgam, hgcos σ k hk]
  · intro k hk
    apply hκ
    rw [hgam, map_one, hg1 k hk]

/-- **Glue: the Frobenius trace link and Glazer's wild ramification for the canonical
operators** (linked-tate; the remaining content of `LinkedTateCoreDR`). For every fibre context
and G7 data, every transport `(Θ, h)` with unram-tate's `TatePoints` property, every
points-level descent datum `(m, a, n, d)` of `A` for `ε` (the clauses of g0-mod-field's
`DescentDatum`, with the rational discrepancy `n/d` as functions), every `γ₀ : G_ℚ → ℚ̄` with
`∂γ₀ = n/d`, constant on `G_{L'}`-cosets and `1` on `G_{L'}`, and all embeddings `j₅`, `j₃`:
* g14-trace's `FrobTraceLink` for `tmOf … 5`, `tmOf … 3` (N5 L777-786: at a Frobenius `τ` above
  `p ∉ S`, `N·Tm_ℓ(τ)` is `V_ℓ` of `N·μ̄ ∘ F` on the reduction, at `ℓ = 3` and `ℓ = 5`);
* `RhoRamWild` for `ρ₅ = (j₅∘β')⁻¹ Tm₅` at `p ≠ 5` and `ρ₃` at `p = 5` (`β' g = γ₀(hgh⁻¹)`,
  `a = 1`; N5 L819-852, D1-D4).
GLUE (AV reduction theory, Néron/Serre–Tate, and the conductor bounds of G15). -/
def LinkedFrobRam : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∀ (gam : GQ → PkgI4.Qbar),
      (∃ κ : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) →
      (∀ σ, gam σ ≠ 0) →
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) →
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) → (∀ k ∈ GQL L', gam k = 1) →
    ∀ (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3),
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))
        (tmOf hLL' A Θ h m 5) (tmOf hLL' A Θ h m 3) ∧
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 5) (fun _ => j5 1)
            (fun g => j5 (gam (h * g * h⁻¹))))) ∧
        (p = 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 3) (fun _ => j3 1)
            (fun g => j3 (gam (h * g * h⁻¹)))))

/-- **Glue: the Frobenius trace link for the canonical operators** (linked-tate; N5 L777-786).
For every fibre context and G7 data, every transport `(Θ, h)` with unram-tate's `TatePoints`
property and every points-level descent datum `(m, a, n, d)` of `A` for `ε` (the clauses of
g0-mod-field's `DescentDatum`, the discrepancy `n/d` as functions): g14-trace's `FrobTraceLink`
holds for `tmOf … 5` and `tmOf … 3`: outside a finite set of primes, at every arithmetic Frobenius
`τ` there are an abelian variety `Ā` over a field of characteristic `p`, `α' ∈ End(Ā)` and
`N ≠ 0` with `N·Tm_ℓ(τ)` conjugate to `V_ℓ(α')` at `ℓ = 3` and `ℓ = 5` (Glazer: `Ā` the
reduction of `A_{L'}`, `α' = N·μ̄ ∘ F`; Néron mapping property and Serre–Tate). GLUE. -/
def LinkedFrob : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
      G14Trace.FrobTraceLink (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))
        (tmOf hLL' A Θ h m 5) (tmOf hLL' A Θ h m 3)

/-- **Glue: Glazer's wild ramification for the canonical descended operators** (linked-tate;
N5 L819-852, D1-D4). Same data as `LinkedFrob`, and every `γ₀ : G_ℚ → ℚ̄` that is `β/a` under some embedding `ℚ̄ → ℂ` (the
scalars of G7, N5 L719-722), with `∂γ₀ = n/d`, constant on `G_{L'}`-cosets and `1` on `G_{L'}`, and
all embeddings `j₅`, `j₃`: `RhoRamWild` for
`ρ₅ = (j₅∘β')⁻¹ Tm₅` at `p ≠ 5` and for `ρ₃` at `p = 5` (`β' g = γ₀(hgh⁻¹)`, `a = 1`). GLUE. -/
def LinkedRam : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left)
    (u : ℚ) (P : LeafQM.AV.QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    letI : NumberField L' := numberField_of_fd L'
    ∀ (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ),
      (∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x)) →
    ∀ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ) (n d : GQ → GQ → ℤ),
      (∀ σ, 0 < a σ) →
      (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) →
      (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) →
      (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) →
      (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) →
      (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) →
      (∀ σ τ, n σ τ ≠ 0 ∧ d σ τ ≠ 0 ∧ d σ τ • (m σ).comp (m τ) = n σ τ • m (σ * τ) ∧
        (((a σ * a τ * ((n σ τ : ℝ) / d σ τ) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) →
      (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ) →
    ∀ (gam : GQ → PkgI4.Qbar),
      (∃ κ : PkgI4.Qbar →ₐ[ℚ] ℂ, ∀ σ, κ (gam σ) = (β σ : ℂ) / ((a σ : ℝ) : ℂ)) →
      (∀ σ, gam σ ≠ 0) →
      (∀ σ τ, gam σ * gam τ = ((n σ τ : PkgI4.Qbar) / (d σ τ : PkgI4.Qbar)) * gam (σ * τ)) →
      (∀ σ, ∀ k ∈ GQL L', gam (σ * k) = gam σ) → (∀ k ∈ GQL L', gam k = 1) →
    ∀ (j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5) (j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3),
      ∀ p : ℕ, ∀ hp : p.Prime,
        (p ≠ 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 5) (fun _ => j5 1)
            (fun g => j5 (gam (h * g * h⁻¹))))) ∧
        (p = 5 → HSyn.LinkedTate.RhoRamWild p hp
          (GlueDescent.rho (tmOf hLL' A Θ h m 3) (fun _ => j3 1)
            (fun g => j3 (gam (h * g * h⁻¹)))))

/-- `LinkedFrobRam` is the conjunction of `LinkedFrob` and `LinkedRam` (proved). -/
theorem linkedFrobRam_of (hF : LinkedFrob) (hR : LinkedRam) : LinkedFrobRam := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8
    gam g0 g1 g2 g3 g4 j5 j3
  exact ⟨hF Y Φ π u P hctx L A ε N χ β L' hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8,
    hR Y Φ π u P hctx L A ε N χ β L' hLL' hD Θ h hΘ m a n d h1 h2 h3 h4 h5 h6 h7 h8 gam g0 g1 g2 g3 g4
      j5 j3⟩

set_option maxHeartbeats 1000000 in
/-- **`LinkedTateCoreDR`, proved** from the leaf I3.M0 (`PkgI3.TateModuleFree`, through
unram-tate's `tateCont_of_tateModuleFree`) and the glue `LinkedFrobRam`. The data: unram-tate's
`Θ, h` (`tatePoints`), the descent datum of `G7Data`, `γ₀` from `scalarTransferQ`, `a = 1`,
`β' g = γ₀(hgh⁻¹)`, `j_ℓ = IsAlgClosed.lift : ℚ̄ → ℚ̄_ℓ`; `G7Out` at each `ℓ` by unram-tate's
assembly (`tateBridge_of_pieces`) run with the scalars `j_ℓ ∘ 1`, `j_ℓ ∘ β'`. -/
theorem linkedTateCoreDR_of (hT : PkgI3.TateModuleFree) (hFR : LinkedFrobRam) :
    HSyn.LinkedTate.LinkedTateCoreDR := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD hdim hrank
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hD' := hD
  obtain ⟨hQM, hDD, -, -, -, -, -, hβe, hL', -, -, -⟩ := hD
  obtain ⟨hεc, hinf, h11, m, a, ha0, haL, hmL, hmLL, hmEnd, hmsf, hmc, hmF⟩ := hDD
  choose n d hn hd hnd hna using hmc
  obtain ⟨iot⟩ : Nonempty (LeafQM.O →+* PkgI3.AbVar.End A) := by
    obtain ⟨K, hKL, PK, -, rfl⟩ := hQM
    exact ⟨(endBaseChange K L hKL PK.A).some.comp PK.q.iota⟩
  obtain ⟨Θ, h, hΘ⟩ := tatePoints L L' hLL' A
  have hLL'G : ∀ k, k ∈ GQL L' → k ∈ GQL L := fun k hk => ((hL' k).mp hk).1
  have hβL' : ∀ k, k ∈ GQL L' → β k = 1 := fun k hk => ((hL' k).mp hk).2
  obtain ⟨gam, κ, hκgam, hgam0, hgamc, hgamcos, hgam1⟩ := scalarTransferQ L' a β ε n d hd hna hβe ha0
    (fun σ k hk => ⟨(haL σ k (hLL'G k hk)).2.1, by
      have := hβe σ k
      rw [hβL' k hk, _root_.mul_one, eps_right_one L ε hεc hinf h11 σ k (hLL'G k hk),
        _root_.one_mul] at this
      exact this.symm⟩)
    (fun k hk => ⟨(haL 1 k (hLL'G k hk)).1, hβL' k hk⟩)
  have hC := tateCont_of_tateModuleFree hT
  have hR := resQEmbedding
  let cj : PkgI4.GQ → GQ := fun g => h * g * h⁻¹
  have hcj : ∀ g g₂, cj (g * g₂) = cj g * cj g₂ := fun g g₂ => by
    show h * (g * g₂) * h⁻¹ = (h * g * h⁻¹) * (h * g₂ * h⁻¹)
    group
  -- `G_{L'}` is normal
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hres : ∀ σ : Field.absoluteGaloisGroup L',
      cj (@GaloisCopy.resQ L' _ hNF σ) ∈ GQL L' := by
    intro σ
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  -- one coefficient prime, with the scalars `j ∘ 1`, `j ∘ γ₀ ∘ cj`
  have key : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ),
      ∃ (c : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ)
        (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
          (G0Galois.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
        G0Galois.G7Out (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
          (tmOf hLL' A Θ h m ℓ) c c (fun _ => j 1) (fun g => j (gam (h * g * h⁻¹))) uu := by
    intro ℓ _ j
    let R : AddMonoid.End (PtQ L A) →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      (opVHom (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ).comp (conjE Θ)
    let m' : GQ → AddMonoid.End (PtQ L A) := m
    let Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) := fun g => R (m' (cj g))
    let c' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ := fun g g₂ =>
      ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ))
    let a' : PkgI4.GQ → PadicAlgCl ℓ := fun _ => j 1
    let β' : PkgI4.GQ → PadicAlgCl ℓ := fun g => j (gam (cj g))
    -- matrix units
    let QM : LeafQM.O →+* Module.End (PadicAlgCl ℓ) (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ) :=
      R.comp ((LeafQM.AV.endPt A Qbar).comp iot)
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (2 : PadicAlgCl ℓ) (by norm_num : 0 < 2)
    have hI : QM iO * QM iO = (2 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, iO_sq, map_add, map_one, two_smul]
    have hJ : QM jO * QM jO = (-3 : PadicAlgCl ℓ) • (1 : Module.End (PadicAlgCl ℓ) _) := by
      rw [← map_mul, jO_sq, map_neg, map_add, map_add, map_one]
      module
    have hIJ : QM iO * QM jO = -(QM jO * QM iO) := by
      rw [← map_mul, iO_jO, map_neg, map_mul]
    obtain ⟨uu, huu⟩ := matrixUnits_of_quat s hs two_ne_zero three_ne_zero _ _ hI hJ hIJ
    have hcomm : ∀ (g : PkgI4.GQ) (o : LeafQM.O), Commute (Tm g) (QM o) := by
      intro g o
      apply Commute.map _ R
      exact hmEnd (cj g) (iot o)
    -- the relations
    have hT : ∀ g g₂, Tm g * Tm g₂ = c' g g₂ • Tm (g * g₂) := by
      intro g g₂
      have h0 : d (cj g) (cj g₂) • (m' (cj g) * m' (cj g₂)) = n (cj g) (cj g₂) • m' (cj g * cj g₂) :=
        hnd (cj g) (cj g₂)
      have h1 := congrArg R h0
      rw [map_zsmul, map_zsmul, ← hcj] at h1
      have h1' : d (cj g) (cj g₂) • (Tm g * Tm g₂) = n (cj g) (cj g₂) • Tm (g * g₂) := by
        show d (cj g) (cj g₂) • (R (m' (cj g)) * R (m' (cj g₂))) = _
        rw [← map_mul]; exact h1
      have h2 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) • (Tm g * Tm g₂) =
          (n (cj g) (cj g₂) : PadicAlgCl ℓ) • Tm (g * g₂) :=
        (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).trans
          (h1'.trans (Int.cast_smul_eq_zsmul (PadicAlgCl ℓ) _ _).symm)
      have hd0 : (d (cj g) (cj g₂) : PadicAlgCl ℓ) ≠ 0 := Int.cast_ne_zero.mpr (hd _ _)
      show _ = ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) • _
      rw [div_eq_inv_mul, ← smul_smul, ← h2, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    have ha : ∀ g g₂, a' g * a' g₂ * c' g g₂ = c' g g₂ * a' (g * g₂) := by
      intro g g₂; simp only [a', map_one, _root_.one_mul, _root_.mul_one]
    have hβ : ∀ g g₂, β' g * β' g₂ = c' g g₂ * β' (g * g₂) := by
      intro g g₂
      show j (gam (cj g)) * j (gam (cj g₂)) =
        ((n (cj g) (cj g₂) : PadicAlgCl ℓ) / (d (cj g) (cj g₂) : PadicAlgCl ℓ)) *
          j (gam (cj (g * g₂)))
      rw [← map_mul, hgamc, map_mul, map_div₀, map_intCast, map_intCast, hcj]
    have hβ0 : ∀ g, β' g ≠ 0 := fun g => (map_ne_zero j).mpr (hgam0 _)
    have hTres : ∀ σ : Field.absoluteGaloisGroup L',
        Tm (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      have hτ := hres σ
      let σ' : Qbar ≃ₐ[L] Qbar :=
        AlgEquiv.ofRingEquiv (f := (act (cj (@GaloisCopy.resQ L' _ hNF σ))).toRingEquiv)
          (fun x => (mem_GQL.mp (hLL'G _ hτ)) x x.2)
      have hm := hmL (cj (@GaloisCopy.resQ L' _ hNF σ)) σ' (fun x => rfl)
      rw [tate_eq_opV]
      show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ (conjE Θ (m' (cj _))) = _
      congr 1
      refine DFunLike.ext _ _ fun x => ?_
      show Θ (m (cj (@GaloisCopy.resQ L' _ hNF σ)) (Θ.symm x)) = _
      rw [hm]
      show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
      rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]
    have hrho1 : ∀ σ : Field.absoluteGaloisGroup L',
        GlueDescent.rho Tm a' β' (@GaloisCopy.resQ L' _ hNF σ) = GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
      intro σ
      unfold GlueDescent.rho
      rw [hTres σ]
      simp only [β', a', hgam1 _ (hres σ), map_one, inv_one, _root_.mul_one, one_smul]
    refine ⟨c', uu, hdim, hrank, hT, ha, hβ, hβ0,
      fun σ => ⟨hTres σ, map_one j, by
        show j (gam (cj (@GaloisCopy.resQ L' _ hNF σ))) = 1
        rw [hgam1 _ (hres σ), map_one]⟩,
      fun g i j => huu i j (Tm g) (hcomm g iO) (hcomm g jO), ?_⟩
    -- continuity
    intro f v
    rw [continuous_iff_continuousAt]
    intro g₀
    let e₀ : Field.absoluteGaloisGroup L' → PkgI4.GQ := fun σ => g₀ * @GaloisCopy.resQ L' _ hNF σ
    have he₀ : Topology.IsOpenEmbedding e₀ :=
      (Homeomorph.mulLeft g₀).isOpenEmbedding.comp (hR L')
    have he₀1 : e₀ 1 = g₀ := by simp only [e₀, map_one, _root_.mul_one]
    have hcomp : (fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀ =
        fun σ => (f ∘ₗ GlueDescent.rho Tm a' β' g₀) (GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ v) := by
      funext σ
      simp only [Function.comp_apply, e₀, LinearMap.comp_apply]
      rw [← GlueDescent.rho_map_mul Tm c' c' a' β' hT ha hβ hβ0, hrho1, Module.End.mul_apply]
    have hc : ContinuousAt ((fun g => f (GlueDescent.rho Tm a' β' g v)) ∘ e₀) 1 := by
      rw [hcomp]; exact (hC L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ v).continuousAt
    rw [he₀.continuousAt_iff, he₀1] at hc
    exact hc
  let j5 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5 := IsAlgClosed.lift
  let j3 : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 3 := IsAlgClosed.lift
  obtain ⟨c5, u5, h5⟩ := key 5 j5
  obtain ⟨c3, u3, h3⟩ := key 3 j3
  obtain ⟨hF, hRam⟩ := hFR Y Φ π u P hctx L A ε N χ β L' hLL' hD' Θ h hΘ m a n d ha0 haL hmL
    hmLL hmEnd hmsf (fun σ τ => ⟨hn σ τ, hd σ τ, hnd σ τ, hna σ τ⟩) hmF gam ⟨κ, hκgam⟩ hgam0 hgamc hgamcos
    hgam1 j5 j3
  exact ⟨fun _ => 1, fun g => gam (h * g * h⁻¹), j5, j3, tmOf hLL' A Θ h m 5, c5, c5, u5,
    tmOf hLL' A Θ h m 3, c3, c3, u3, h5, h3, hF, hRam⟩

end UnramTate

/-- **`LinkedTateData`, proved** from the leaves T7 (`PkgI3.CharPolyIndepOfEll`) and I3.M0
(`PkgI3.TateModuleFree`) and the glue Props `FibreSimple`, `QMEndRank`, `LinkedFrobRam`. -/
theorem HSyn.LinkedTate.linkedTateData_of_frobRam (hM : PkgI3.CharPolyIndepOfEll)
    (hT : PkgI3.TateModuleFree) (hFS : HSyn.G0Split.FibreSimple)
    (hR : HSyn.LinkedTate.QMEndRank) (hFR : UnramTate.LinkedFrobRam) :
    HSyn.G0AssembleMod.LinkedTateData :=
  HSyn.LinkedTate.linkedTateData_of hM
    (HSyn.LinkedTate.linkedTateCore_of hFS hR (UnramTate.linkedTateCoreDR_of hT hFR))

/-- **`AfterG7` (G8-G16) with both joint Props of g0-assemble reduced** (proved): g0-assemble's
inputs of `afterG7_of` (leaf bundles, `GaloisPieces`, `DirichletOfFinite`, `CarayolR17'`, the
three LadicCond glue Props) with `ModelG3G6` and `LinkedTateData` replaced by the glue Props
`FibreSimple` (already a `GluePieces` field), `GoodRedG3Bridge`, `QMEndRank`, `LinkedFrob`,
`LinkedRam`; the leaves used are the bundles' R6, R7a, T5 (G3), T7 (G14) and T26 = I3.M0. -/
theorem HSyn.LinkedTate.afterG7_of_final (r : HSyn.ResearchLeaves) (t : HSyn.TextbookLeaves)
    (m : G0Galois.GaloisPieces) (hDF : G0ModNewform.DirichletOfFinite)
    (hCar : LadicCond.CarayolR17')
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral)
    (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hFS : HSyn.G0Split.FibreSimple) (hB : HSyn.LinkedTate.GoodRedG3Bridge)
    (hR : HSyn.LinkedTate.QMEndRank) (hF : UnramTate.LinkedFrob) (hRam : UnramTate.LinkedRam) :
    G0ModField.AfterG7 :=
  HSyn.G0AssembleMod.afterG7_of r t m hDF hCar hSw hL8 hAd
    (HSyn.LinkedTate.modelG3G6_of hFS (HSyn.LinkedTate.qmModelG3_of r.r7a r.r6 t.t5 hB))
    (HSyn.LinkedTate.linkedTateData_of_frobRam t.t7 t.t26 hFS hR
      (UnramTate.linkedFrobRam_of hF hRam))

end

end LinkedDataSec



-- (g0-assemble3: scratch/linked-tate/parts/98b_ram.lean, verbatim)
/-! ## linked-tate: `LinkedRam` reduced to a field statement about `L'`, G3, and the prime `3`

For the canonical data, `ρ_ℓ(g) = β'(g)⁻¹ Tm(g)` is the Tate action on `G_{L'}` (`β' = 1` there,
`tmOf_resQ`). So clauses (i)-(ii) of `RhoRamWild` follow once the relevant local elements land in
`G_{L'}` (`KernelFieldBreaks`, a statement about the field `L'` alone) and act trivially through
the Tate module: away from `3` this is G3 (`QMModelG3`, already reduced), with local inertia
landing in a global inertia group (`LocalInertiaGlobal`, `UpperAbsInertia`, definitions only);
at `p = 3` (only for `ρ₅`) it is `TateRamAtThree`.

**Caveat (linked-tate finding).** g0-mod-field's `G7Data` does not record `[L:ℚ] ≤ D` (its `G4Out`
does). For `G7Data` with an oversized `L` (e.g. `L ⊇ ℚ(ζ_{2^k})` with `k > U₀ + 1`, allowed when
`M_{S_mul}(u)` is large), `KernelFieldBreaks` (i) fails: `G_{ℚ_2}^t ⊄ G_L ⊇ G_{L'}` for `U₀ < t <
k − 1`; `TateRamAtThree` is likewise only justified for small `K`. `linkedRam_of` is a valid
implication, but its premises are expected to hold only under `[L:ℚ] ≤ D`; `GluePieces3` therefore
keeps `LinkedRam` itself as the field. -/

section LinkedRamSec

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace UnramTate

open G0ModField

/-- **The canonical operators are the Tate action on `G_{L'}`** (proved; the step `hTres` of
unram-tate's assembly, for any `(Θ, h)` with the `TatePoints` property and any `m` equal to the
Galois action on `G_L`). -/
theorem tmOf_resQ {L L' : IF} [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (A : PkgI3.AbVar L)
    (Θ : PtQ L A ≃+ PtA (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) (h : PkgI4.GQ)
    (hΘ : ∀ (σ : Field.absoluteGaloisGroup L') (σ' : Qbar ≃ₐ[L] Qbar),
        (∀ x, σ' x = (h * (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) * h⁻¹) x) →
        ∀ x, Θ (MonoidHom.toAdditive (A.galAct σ') x) =
          MonoidHom.toAdditive ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).galAct σ)
            (Θ x))
    (m : GQ → (PtQ L A →+ PtQ L A))
    (hmL : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup L') :
    tmOf hLL' A Θ h m ℓ (@GaloisCopy.resQ L' _ (numberField_of_fd L') σ) =
      GaloisCopy.tate (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ σ := by
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  have hτ : h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹ ∈ GQL L' := by
    have : (@GaloisCopy.resQ L' _ hNF σ) ∈ L'.fixingSubgroup := by
      rw [← resQRange L']; exact ⟨σ, rfl⟩
    exact hnorm.conj_mem _ this h
  have hτL : h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹ ∈ GQL L :=
    mem_GQL.mpr (fun x hx => mem_GQL.mp hτ x (hLL' hx))
  let σ' : Qbar ≃ₐ[L] Qbar :=
    AlgEquiv.ofRingEquiv (f := (act (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹)).toRingEquiv)
      (fun x => (mem_GQL.mp hτL) x x.2)
  have hm := hmL (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹) σ' (fun x => rfl)
  rw [tate_eq_opV]
  show opV (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ
    (conjE Θ (m (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹))) = _
  congr 1
  refine DFunLike.ext _ _ fun x => ?_
  show Θ (m (h * (@GaloisCopy.resQ L' _ hNF σ) * h⁻¹) (Θ.symm x)) = _
  rw [hm]
  show Θ (MonoidHom.toAdditive (A.galAct σ') (Θ.symm x)) = _
  rw [hΘ σ σ' (fun x => rfl) (Θ.symm x), AddEquiv.apply_symm_apply]

/-- **Glue: the ramification of the kernel field `L'`** (linked-tate; the field half of N5
L819-852, D1 and D3). For every G7 data: for `p ≤ D`, every element of an absolute upper
ramification group `G_{ℚ_p}^t`, `t > U₀`, maps into `G_{L'}` (the upper breaks of `L'` at `p` are
`≤ U₀`); for `p > D`, wild inertia maps into `G_{L'}` (`L'` is tame at `p`: `[L:ℚ] ≤ D < p`, and
`L'/L` is cut out by `β|_{G_L}` with `β² = χ` of order prime to `p` at `p`). GLUE. -/
def KernelFieldBreaks : Prop :=
  ∀ (u : ℚ) (P : LeafQM.AV.QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∀ (p : ℕ) (hp : p.Prime),
      letI : Fact p.Prime := ⟨hp⟩
      ((p : ℝ) ≤ (ZInQ.heightD : ℝ) → ∀ t : ℝ, G0ModNewform.U0 < t →
          ∀ σ ∈ LadicCond.upperAbs p t, PkgI4.decomp p σ ∈ GQL L') ∧
        ((ZInQ.heightD : ℝ) < p → ∀ σ ∈ (LadicCond.wildSet : Set (PkgI4.GQp p)),
          PkgI4.decomp p σ ∈ GQL L')

/-- **Glue (definitions): local inertia lands in a global inertia group.** For `σ` in the
inertia set of `G_{ℚ_p}`, `decomp p σ` lies in the inertia group of the place `v` of `ℚ̄` induced
by the embedding `ℚ̄ → ℚ̄_p` that `decomp` uses (`v` lies over `p`). GLUE (Mathlib-level). -/
def LocalInertiaGlobal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : PkgI4.GQp p), σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p)) →
    ∃ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p ∧
      ∃ τ ∈ v.inertiaSubgroup ℚ, ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = PkgI4.decomp p σ

/-- **Glue (definitions): upper ramification groups of positive index lie in inertia.** For
`t > 0`, `upperAbs p t ⊆ inertiaSet` (`G^t(L) ⊆ G_0(L)` for each finite Galois `L/ℚ_p`, and every
integral `x ∈ ℚ̄_p` lies in such an `L`). GLUE (Mathlib-level). -/
def UpperAbsInertia : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (t : ℝ), 0 < t →
    LadicCond.upperAbs p t ⊆ (LadicCond.inertiaSet : Set (PkgI4.GQp p))

/-- **Glue: the Tate module of the QM model at `p = 3`** (linked-tate; N5 L819-852, D1-D2 at the
prime `3`, where the model may have bad reduction). For a `QML3` object `PK` over `K ≤ L ≤ L'`
(`L'/ℚ` finite Galois) and `t > U₀`, every `σ' ∈ G_{L'}` whose image is an element of
`G_{ℚ_3}^t` acts trivially on `ℚ̄₅ ⊗ V₅((PK.A)_{L,L'})` (QM surfaces have potentially good
reduction; the inertia image is finite, cut out by a field whose upper breaks at `3` are `≤ U₀`).
GLUE. -/
def TateRamAtThree : Prop :=
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L')
    (PK : LeafQM.AV.QML3 K),
    letI : NumberField L' := numberField_of_fd L'
    ∀ t : ℝ, G0ModNewform.U0 < t → ∀ σ ∈ LadicCond.upperAbs 3 t,
      ∀ σ' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ' = PkgI4.decomp 3 σ →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) 5 σ' = 1

/-- G3 at a local inertia element (proved from `LocalInertiaGlobal`). -/
theorem tate_trivial_of_g3 (hLI : LocalInertiaGlobal) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {ℓ : ℕ} [Fact ℓ.Prime] (h : G0Galois.G3Out A ℓ {3}) (p : ℕ)
    [Fact p.Prime] (hp3 : p ≠ 3) (hpl : p ≠ ℓ) (σ : PkgI4.GQp p)
    (hσ : σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p))) (σ'' : Field.absoluteGaloisGroup K)
    (hσ'' : G0Galois.resQ K σ'' = PkgI4.decomp p σ) : G0Galois.tate A ℓ σ'' = 1 := by
  obtain ⟨v, hv, τ, hτ, hτeq⟩ := hLI p σ hσ
  exact h p Fact.out (by simpa using hp3) hpl v hv σ'' ⟨τ, hτ, hτeq.trans hσ''.symm⟩

/-- `0 ≤ U₀`. -/
theorem U0_nonneg : 0 ≤ G0ModNewform.U0 := by
  unfold G0ModNewform.U0; positivity

/-- `3 ≤ D`. -/
theorem three_le_heightD : (3 : ℝ) ≤ (ZInQ.heightD : ℝ) := by
  exact_mod_cast G0ModField.le_heightD_of_mem_S_mul
    (ZInQ.Mult.mem_S_mul_of_le Nat.prime_three (by norm_num))

/-- **`LinkedRam`, proved** from `QMModelG3` (G3), `KernelFieldBreaks`, `LocalInertiaGlobal`,
`UpperAbsInertia` and `TateRamAtThree`. -/
theorem linkedRam_of (hG3 : HSyn.LinkedTate.QMModelG3) (hK : KernelFieldBreaks)
    (hLI : LocalInertiaGlobal) (hUI : UpperAbsInertia) (h3 : TateRamAtThree) : LinkedRam := by
  intro Y Φ π u P hctx L _ _ A ε N _ χ β L' _ _ hLL' hD Θ h hΘ m a n d h1 h2 hmL h4 h5 h6 h7 h8
    gam g0 g1 g2 g3 hgam1 j5 j3
  haveI hNF : NumberField L' := numberField_of_fd L'
  have hK' := hK u P L A ε N χ β L' hLL' hD
  obtain ⟨K, hKL, PK, -, rfl⟩ := hD.1
  have hnorm : (L'.fixingSubgroup).Normal :=
    (InfiniteGalois.normal_iff_isGalois L').mpr inferInstance
  -- on `G_{L'}`, `ρ` is the Tate action
  have hρ : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (j : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl ℓ) (g : PkgI4.GQ),
      g ∈ GQL L' →
      (∀ σ'' : Field.absoluteGaloisGroup L', G0Galois.resQ L' σ'' = g →
        G0Galois.tate (@PkgI3.AbVar.baseChange L _
          (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1) →
      GlueDescent.rho (tmOf hLL' _ Θ h m ℓ) (fun _ => j 1) (fun g => j (gam (h * g * h⁻¹))) g
        = 1 := by
    intro ℓ _ j g hg ht
    obtain ⟨σ'', hσ''⟩ : g ∈ (@GaloisCopy.resQ L' _ hNF).range := by
      rw [resQRange L']; exact hg
    subst hσ''
    have hcj : h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹ ∈ GQL L' := hnorm.conj_mem _ hg h
    unfold GlueDescent.rho
    rw [tmOf_resQ hLL' _ Θ h hΘ m hmL ℓ σ'']
    have ht' : GaloisCopy.tate (@PkgI3.AbVar.baseChange L _
        (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL')) ℓ σ'' = 1 :=
      ht σ'' rfl
    have hγ : gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹) = 1 := hgam1 _ hcj
    rw [ht']
    show ((j (gam (h * (@GaloisCopy.resQ L' _ hNF σ'') * h⁻¹)))⁻¹ * j 1) • (1 : Module.End _ _) = 1
    rw [hγ, map_one, inv_one, _root_.one_mul, one_smul]
  intro p hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hG5 := hG3 K L L' hKL hLL' PK 5
  have hG3' := hG3 K L L' hKL hLL' PK 3
  refine ⟨fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩,
    fun hp5 => ⟨fun hpD t ht σ hσ => ?_, fun hpD σ hσ => ?_⟩⟩
  · -- `ρ₅`, `p ≠ 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    refine hρ 5 j5 _ ((hK' p hp).1 hpD t ht σ hσ) (fun σ'' hσ'' => ?_)
    by_cases hp3 : p = 3
    · subst hp3
      exact h3 K L L' hKL hLL' PK t ht σ hσ σ'' hσ''
    · exact tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ''
  · -- `ρ₅`, `p ≠ 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by
      intro h3'
      subst h3'
      have := three_le_heightD
      push_cast at hpD
      linarith
    exact hρ 5 j5 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG5 p hp3 hp5 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p ≤ D`
    have hσI := hUI p t (lt_of_le_of_lt U0_nonneg ht) hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).1 hpD t ht σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')
  · -- `ρ₃`, `p = 5`, `p > D`
    have hσI := LadicCond.wildSet_subset_inertiaSet hσ
    have hp3 : p ≠ 3 := by omega
    exact hρ 3 j3 _ ((hK' p hp).2 hpD σ hσ)
      (fun σ'' hσ'' => tate_trivial_of_g3 hLI hG3' p hp3 hp3 σ hσI σ'' hσ'')

end UnramTate

end

end LinkedRamSec



-- (g0-assemble3: scratch/linked-tate/parts/98c_inertia.lean, verbatim)
/-! ## linked-tate: `LocalInertiaGlobal` proved (Mathlib)

The place is the comap `v` of the valuation `‖·‖` of `ℚ̄_p` along the embedding `ℚ̄ → ℚ̄_p` that
`decomp` uses (`embP`, with `embP ∘ decomp σ = σ ∘ embP`, Mathlib's `restrictNormal_commutes`):
`decomp σ` preserves `v` (`σ` is an isometry, `PkgI4.norm_gqp_apply`), `p ∈ v.nonunits`
(`‖p‖ = p⁻¹`), and for `σ` in the inertia set `decomp σ` acts trivially on the residue field of
`v` (`‖σx − x‖ < 1` for `‖x‖ ≤ 1`). First compiled standalone over Mathlib
(`scratch/linked-tate/test/LocalInertia.lean`). -/

section LocalInertiaSec

noncomputable section

open scoped Pointwise

namespace UnramTate

variable (p : ℕ) [Fact p.Prime]

/-- The embedding `ℚ̄ → ℚ̄_p` that `decomp` uses. -/
def embP : PkgI4.Qbar →+* PadicAlgCl p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

theorem embP_decomp (σ : PkgI4.GQp p) (x : PkgI4.Qbar) : embP p (PkgI4.decomp p σ x) = σ (embP p x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem localInertiaGlobal_at (σ : PkgI4.GQp p) (hσ : σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p))) :
    ∃ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p ∧
      ∃ τ ∈ v.inertiaSubgroup ℚ, ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = PkgI4.decomp p σ := by
  let w : Valuation PkgI4.Qbar NNReal := (Valued.v : Valuation (PadicAlgCl p) NNReal).comap (embP p)
  let v := w.valuationSubring
  have hmem : ∀ x, x ∈ v ↔ ‖embP p x‖ ≤ 1 := by
    intro x
    show Valued.v (embP p x) ≤ 1 ↔ _
    rw [← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hnorm : ∀ (g : PkgI4.GQp p) (x : PkgI4.Qbar), ‖embP p (PkgI4.decomp p g x)‖ = ‖embP p x‖ := by
    intro g x; rw [embP_decomp, PkgI4.norm_gqp_apply]
  have hτv : PkgI4.decomp p σ ∈ v.decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hmem, hmem, ← map_inv]
    exact iff_of_eq (congrArg (· ≤ (1 : ℝ)) (hnorm σ⁻¹ x))
  have hnu : ∀ x : PkgI4.Qbar, ‖embP p x‖ < 1 → x ∈ v.nonunits := by
    intro x hx
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases h0 : x = 0
    · exact Or.inl h0
    · right
      rw [hmem, map_inv₀, norm_inv]
      have hpos : 0 < ‖embP p x‖ := norm_pos_iff.mpr ((map_ne_zero _).mpr h0)
      intro h
      have := (inv_le_one₀ hpos).mp h
      linarith
  refine ⟨v, ?_, ⟨⟨PkgI4.decomp p σ, hτv⟩, ?_, rfl⟩⟩
  · apply hnu
    rw [map_natCast]
    have : ‖((p : ℚ_[p]) : PadicAlgCl p)‖ = ‖(p : ℚ_[p])‖ := PadicAlgCl.norm_extends p _
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  · rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨PkgI4.decomp p σ, hτv⟩ : v.decompositionSubgroup ℚ) • IsLocalRing.residue v a =
      IsLocalRing.residue v a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    apply hnu
    show ‖embP p (PkgI4.decomp p σ (a : PkgI4.Qbar) - a)‖ < 1
    rw [map_sub, embP_decomp]
    exact hσ _ ((hmem a).mp a.2)

/-- **`LocalInertiaGlobal`, proved.** -/
theorem localInertiaGlobal : LocalInertiaGlobal := fun p _ σ hσ => localInertiaGlobal_at p σ hσ

end UnramTate

end

end LocalInertiaSec



-- (g0-assemble3: scratch/linked-tate/parts/98d_upperabs.lean, verbatim)
/-! ## linked-tate: `UpperAbsInertia` proved (Mathlib)

For `t > 0`, the lower index `sInf {u ≥ −1 | t ≤ φ_L(u)}` is `≥ 0` (`φ_L ≤ 0` on `u ≤ 0`, an
integral of a nonnegative function), so `G^t(L) ⊆ G_0(L)`: `‖σx − x‖ ≤ ‖ϖ‖^{n+1} < 1` on the unit
ball of `L`. Every `x ∈ ℚ̄_p` lies in the finite Galois normal closure of `ℚ_p(x)`. First compiled
standalone over Mathlib (`scratch/linked-tate/test/UpperAbs.lean`). -/

section UpperAbsSec

noncomputable section

namespace UnramTate

variable {p : ℕ} [Fact p.Prime]

theorem phiAt_nonpos (L : LadicCond.Fld p) {u : ℝ} (hu : u ≤ 0) : LadicCond.phiAt L u ≤ 0 := by
  unfold LadicCond.phiAt
  rw [intervalIntegral.integral_symm]
  have : 0 ≤ ∫ t in u..(0 : ℝ), (LadicCond.ramCardR L t : ℝ) / (LadicCond.ramCard L 0 : ℝ) :=
    intervalIntegral.integral_nonneg hu (fun _ _ => by positivity)
  linarith

theorem sInf_nonneg_of_pos (L : LadicCond.Fld p) {t : ℝ} (ht : 0 < t) :
    0 ≤ sInf {u : ℝ | -1 ≤ u ∧ t ≤ LadicCond.phiAt L u} := by
  rcases Set.eq_empty_or_nonempty {u : ℝ | -1 ≤ u ∧ t ≤ LadicCond.phiAt L u} with h | h
  · rw [h, Real.sInf_empty]
  · apply le_csInf h
    rintro u ⟨-, hu⟩
    by_contra hneg
    push Not at hneg
    have := phiAt_nonpos L hneg.le
    linarith

theorem upperSet_sub (L : LadicCond.Fld p) {t : ℝ} (ht : 0 < t) (σ : PkgI4.GQp p) (hσ : σ ∈ LadicCond.upperSet L t) :
    ∀ x ∈ L, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  have h0 := sInf_nonneg_of_pos L ht
  unfold LadicCond.upperSet LadicCond.ramSetR at hσ
  rw [if_neg (show ¬ _ ≤ (-1 : ℝ) by linarith)] at hσ
  obtain ⟨ϖ, hϖ, hle⟩ := hσ
  intro x hx hx1
  refine lt_of_le_of_lt (hle x hx hx1) ?_
  exact pow_lt_one₀ (norm_nonneg _) hϖ.2.1 (Nat.succ_ne_zero _)

theorem upperAbs_subset_inertiaSet' (t : ℝ) (ht : 0 < t) :
    LadicCond.upperAbs p t ⊆ (LadicCond.inertiaSet : Set (PkgI4.GQp p)) := by
  intro σ hσ x hx
  let K : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] {x}
  haveI hKfin : FiniteDimensional ℚ_[p] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let L : LadicCond.Fld p := IntermediateField.normalClosure ℚ_[p] K (LadicCond.Kbar p)
  have hL : LadicCond.IsFinGal L := ⟨inferInstance, inferInstance⟩
  have hxL : x ∈ L := IntermediateField.le_normalClosure K (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)
  exact upperSet_sub L ht σ (hσ L hL) x hxL hx

/-- **`UpperAbsInertia`, proved.** -/
theorem upperAbsInertia : UpperAbsInertia := fun _ _ t ht => upperAbs_subset_inertiaSet' t ht

end UnramTate

end

end UpperAbsSec



-- (g0-assemble3: scratch/linked-tate/parts/98_g3tate.lean, verbatim)
/-! ## linked-tate: `GoodRedG3Bridge` reduced to its torsion-point form `GoodRedTorsion`

`G3Out` asks that inertia act trivially on `ℚ̄_ℓ ⊗ V_ℓ`. Triviality on every `A[ℓⁿ](K̄)` implies
it, because `T_ℓ(A)` consists of compatible sequences of `ℓⁿ`-torsion points
(`tate_eq_one_of_torsion`, proved). What remains of G3's transport is the statement at the level
of points, where NOS itself speaks (`PkgI2.InertiaTrivialOn`). -/

section LinkedTateG3Sec

noncomputable section

namespace HSyn.LinkedTate

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-- **Inertia acting trivially on all `ℓ`-power torsion acts trivially on `ℚ̄_ℓ ⊗ V_ℓ`**
(proved): each coordinate `xₙ` of `x ∈ T_ℓ(A)` is `ℓⁿ`-torsion. -/
theorem tate_eq_one_of_torsion {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (σ : Field.absoluteGaloisGroup K)
    (h : ∀ (n : ℕ) (x : A.Pt (AlgebraicClosure K)), x ^ (ℓ ^ n) = 1 → A.galAct σ x = x) :
    G0Galois.tate A ℓ σ = 1 := by
  have hT : A.galT (ℓ := ℓ) σ = LinearMap.id := by
    apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    have hx : (ℓ ^ n) • x.1 n = 0 := PkgI3.Tate.pow_smul_eq_zero x.2 n
    have hx' : (Additive.toMul (x.1 n)) ^ (ℓ ^ n) = 1 := by
      rw [← toMul_nsmul, hx]; rfl
    show Additive.ofMul (A.galAct σ (Additive.toMul (x.1 n))) = x.1 n
    rw [h n _ hx']; rfl
  have hR : A.galRep ℓ σ = 1 := by
    change (A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ] = LinearMap.id
    rw [hT, LinearMap.baseChange_id]
  change (A.galRep ℓ σ).baseChange (PadicAlgCl ℓ) = LinearMap.id
  rw [hR, Module.End.one_eq_id, LinearMap.baseChange_id]

/-- **Glue: good reduction away from `3` makes inertia trivial on torsion points of the base
change** (linked-tate; the point-level transport half of G3, given the leaf R7a). Same hypotheses
as `GoodRedG3Bridge`. Conclusion: for `p ∉ {3}`, `p ≠ ℓ`, and an element `σ'` of `G_{L'}` whose
image `resQ σ'` lies in the inertia group of a place `v` of `ℚ̄` above `p`, `σ'` fixes every
`ℓⁿ`-torsion point of `A_{L,L'}(\bar{L'})`. Route (STANDARD): `v ∩ K` is a DVR of `K` with `3` a
unit; NOS (a) ⇒ (b) over `K` (PkgI2's `InertiaTrivialOn` on `A(K̄)[ℓⁿ]` at a valuation ring of
`K̄` over `v ∩ K`); transport along `\bar{L'} ≅ K̄` over `K` (`resQ`'s embedding `ℚ̄ → \bar{L'}`) and
`A_{L,L'}(\bar{L'}) = A(\bar{L'})` (unram-tate's `bcPt`). GLUE (definitions only; no new
literature). -/
def GoodRedTorsion : Prop :=
  PkgI2.NeronOggShafarevich.{0} →
  ∀ (K L L' : IF) [FiniteDimensional ℚ L'] (hKL : K ≤ L) (hLL' : L ≤ L') (A : PkgI3.AbVar K),
    (∀ (Ov : ValuationSubring K) [IsDiscreteValuationRing Ov], IsUnit (3 : Ov) →
      PkgI2.HasGoodReduction (ObjBridge.toGrp A) Ov) →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime],
      letI : NumberField L' := numberField_of_fd L'
      ∀ p : ℕ, p.Prime → p ∉ ({3} : Finset ℕ) → p ≠ ℓ →
        ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
        ∀ σ' : Field.absoluteGaloisGroup L',
          (∃ σ ∈ v.inertiaSubgroup ℚ,
            ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = G0Galois.resQ L' σ') →
          ∀ (n : ℕ) (x : (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).Pt
              (AlgebraicClosure L')),
            x ^ (ℓ ^ n) = 1 →
            (@PkgI3.AbVar.baseChange L _
              (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct σ' x = x

/-- **`GoodRedG3Bridge`, proved** from `GoodRedTorsion` (`tate_eq_one_of_torsion`). -/
theorem goodRedG3Bridge_of_torsion (h : GoodRedTorsion) : GoodRedG3Bridge := by
  intro hNOS K L L' _ hKL hLL' A hA ℓ _
  letI : NumberField L' := numberField_of_fd L'
  intro p hp hpT hpl v hv σ' hσ
  exact tate_eq_one_of_torsion _ ℓ σ' (h hNOS K L L' hKL hLL' A hA ℓ p hp hpT hpl v hv σ' hσ)

end HSyn.LinkedTate

end

end LinkedTateG3Sec



end G0A2_c70_linkedtate

section G0A2_c75_ltgoodred
-- (leaf-fold3) scratch/lt-goodred/integ/99d_proofs.lean verbatim (made by its make_proofs.py from its parts 10, 20, 40, 50)
/-! ## lt-goodred (integration copy): neron-lg's DVR classification (from parts/10_copies.lean) -/

section LTGoodRedNLGSec

noncomputable section

namespace LTGoodRed.NLG

open NumberField

/-- The discrete valuation ring `𝓞_{L,v}` of a nonzero prime `v` of `𝓞_L`, as a valuation subring
of `L` (the ring of the `v`-adic valuation). -/
noncomputable def dvrAt {L : Type} [Field L] [NumberField L]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) : ValuationSubring L :=
  (v.valuation L).valuationSubring

instance {L : Type} [Field L] [NumberField L] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :
    IsDiscreteValuationRing (dvrAt v) := by
  unfold dvrAt; infer_instance

section Restrict

variable {K : Type} [Field K] [NumberField K]

/-- Every valuation subring of a number field contains `𝓞_K` (it is integrally closed). -/
theorem ringOfIntegers_mem (O : ValuationSubring K) (x : 𝓞 K) : (x : K) ∈ O := by
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1
    (show IsIntegral O (x : K) from x.isIntegral_coe.tower_top)
  exact hy ▸ y.2

/-- The inclusion `𝓞_K → O`. -/
def toO (O : ValuationSubring K) : 𝓞 K →+* O :=
  (algebraMap (𝓞 K) K).codRestrict O.toSubring (ringOfIntegers_mem O)

theorem toO_coe (O : ValuationSubring K) (x : 𝓞 K) : ((toO O x : O) : K) = algebraMap (𝓞 K) K x :=
  rfl

/-- The center of a valuation subring `O ≠ ⊤` of a number field on `𝓞_K`: a nonzero prime. -/
def center' (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 K) where
  asIdeal := (IsLocalRing.maximalIdeal O).comap (toO O)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy⟩ : ∃ y : K, y ∉ O := by
      by_contra h
      push_neg at h
      exact hO (eq_top_iff.2 fun y _ => h y)
    have hy0 : y ≠ 0 := fun h => hy (h ▸ O.zero_mem)
    have hyi : y⁻¹ ∈ O := (O.mem_or_inv_mem y).resolve_left hy
    let x : O := ⟨y⁻¹, hyi⟩
    have hx : x ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu'⟩ := hu
      apply hy
      have : ((u⁻¹ : Oˣ) : O) * x = 1 := by rw [← hu']; exact u.inv_mul
      have h2 : ((((u⁻¹ : Oˣ) : O) : K)) * y⁻¹ = 1 := congrArg Subtype.val this
      have h3 : y = (((u⁻¹ : Oˣ) : O) : K) := by
        field_simp at h2
        exact h2.symm
      rw [h3]; exact (((u⁻¹ : Oˣ) : O)).2
    have hx0 : x ≠ 0 := fun h => inv_ne_zero hy0 (congrArg Subtype.val h)
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (𝓞 K) (x : K)
    have hb0 : algebraMap (𝓞 K) K b ≠ 0 := by
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]
      exact nonZeroDivisors.ne_zero hb
    have ha : toO O a = x * toO O b := by
      apply Subtype.ext
      rw [toO_coe, Subring.coe_mul, toO_coe, ← hab, div_mul_cancel₀ _ hb0]
    intro hbot
    have hmem : a ∈ (IsLocalRing.maximalIdeal O).comap (toO O) := by
      rw [Ideal.mem_comap, ha]; exact Ideal.mul_mem_right _ _ hx
    rw [hbot, Ideal.mem_bot] at hmem
    apply hx0
    apply Subtype.ext
    rw [← hab, hmem, map_zero, zero_div]; rfl

/-- **Every valuation subring `O ≠ ⊤` of a number field is `𝓞_{K,v}` (proved).** -/
theorem dvrAt_center' (O : ValuationSubring K) (hO : O ≠ ⊤) : dvrAt (center' O hO) = O := by
  apply ValuationSubring.eq_of_le_of_ne_top _ _ hO
  intro x hx
  obtain ⟨n, d, hnd⟩ :=
    IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (center' O hO) x hx
  have hd : IsUnit (toO O d) := by
    by_contra h
    exact d.2 ((IsLocalRing.mem_maximalIdeal _).2 h)
  have hvd : O.valuation (algebraMap (𝓞 K) K d) = 1 := (O.valuation_eq_one_iff _).1 hd
  apply O.mem_of_valuation_le_one
  have h2 := congrArg O.valuation hnd
  rw [map_mul, hvd, _root_.mul_one] at h2
  rw [h2]
  exact O.valuation_le_one (toO O n)

/-- Every valuation subring `O ≠ ⊤` of a number field is a DVR. -/
theorem isDiscreteValuationRing_of_ne_top (O : ValuationSubring K) (hO : O ≠ ⊤) :
    IsDiscreteValuationRing O := by
  rw [← dvrAt_center' O hO]
  infer_instance

end Restrict

end LTGoodRed.NLG

end

end LTGoodRedNLGSec

/-! ## lt-goodred §2: `GoodRedTorsion` (copied verbatim) and its proof

`GoodRedTorsion` is copied verbatim from `scratch/linked-tate/parts/98_g3tate.lean` (L33-62).
Proof (`goodRedTorsion`): with `Ω = \bar{L'}`,
* `g = qEmbRing L' : ℚ̄ → Ω` is bijective and `g ∘ resQ σ' = σ' ∘ g` (`resQ_spec`);
* `τ : Ω ≃ₐ[K] \bar K` (both are algebraic closures of `K`); `ψ = g⁻¹ ∘ τ⁻¹ : \bar K ≃ ℚ̄`;
* `w = ψ^*(v)`, a valuation ring of `\bar K`, and `O = w ∩ K`, a valuation ring of the number field
  `K` with `p ∈ 𝔪_O`, hence `≠ K` and a DVR (neron-lg's classification); `3` and `ℓⁿ` are units
  in `O` because they are prime to `p`;
* `σ_K = τ σ' τ⁻¹` lies in the inertia group of `w` (transport of the inertia condition of
  `resQ σ'` at `v` along `ψ`, using `ψ ∘ σ_K = resQ σ' ∘ ψ`);
* NOS (a) ⇒ (b) at `(O, w)` makes `σ_K` fix `A(\bar K)[ℓⁿ]`;
* the points: `E = trPt τ ∘ bcPt ∘ bcPt : A_{L,L'}(Ω) ≃* A(\bar K)` is multiplicative and carries the
  action of `σ'` to that of `σ_K` (`bcPt_galAct` twice, `trPt_galAct`). -/

section LTGoodRedSec

set_option linter.style.haveILetI false

noncomputable section

open scoped Pointwise

-- (`HSyn.LinkedTate.GoodRedTorsion` is linked-tate's own definition here)

namespace LTGoodRed

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField

/-! ### Valuation rings: nonunits, coprime integers, inertia (Mathlib only) -/

section Val

variable {F₁ F₂ : Type} [Field F₁] [Field F₂]

/-- Nonunits of a pulled-back valuation ring. -/
theorem mem_nonunits_comap (A : ValuationSubring F₂) (ψ : F₁ ≃+* F₂) (x : F₁) :
    x ∈ (A.comap (ψ : F₁ →+* F₂)).nonunits ↔ ψ x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap]
  have h0 : x = 0 ↔ ψ x = 0 := (map_eq_zero_iff ψ ψ.injective).symm
  have h1 : (ψ : F₁ →+* F₂) x⁻¹ = (ψ x)⁻¹ := map_inv₀ ψ x
  rw [h1, h0]

/-- An integer prime to `p` is a unit in a valuation ring in which `p` is not. -/
theorem natCast_notMem_nonunits (A : ValuationSubring F₁) {p m : ℕ}
    (hp : (p : F₁) ∈ A.nonunits) (hm : Nat.Coprime m p) : (m : F₁) ∉ A.nonunits := by
  intro hmn
  have hp' : (p : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; simpa using hp
  have hm' : (m : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; simpa using hmn
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hm
  have hsum : (u : A) * (m : A) + (w : A) * (p : A) = 1 := by
    have := congrArg (Int.cast : ℤ → A) huw
    push_cast at this
    exact this
  have h1 : (1 : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← hsum]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hp')
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- The inverse of a nonzero element outside the nonunits lies in the ring. -/
theorem inv_mem_of_notMem_nonunits (A : ValuationSubring F₁) {x : F₁} (hx : x ∉ A.nonunits) :
    x ≠ 0 ∧ x⁻¹ ∈ A := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hx
  exact hx

variable (K : Type) [Field K] {L : Type} [Field L] [Algebra K L]

/-- The concrete form of an inertia element: it preserves `A` and acts trivially modulo the
maximal ideal. -/
theorem of_mem_inertia (A : ValuationSubring L) (σ : A.decompositionSubgroup K)
    (hσ : σ ∈ A.inertiaSubgroup K) :
    (∀ x, (σ : L ≃ₐ[K] L) x ∈ A ↔ x ∈ A) ∧
      ∀ a ∈ A, (σ : L ≃ₐ[K] L) a - a ∈ A.nonunits := by
  have hs : (σ : L ≃ₐ[K] L) • A = A := σ.2
  constructor
  · intro x
    have key : ∀ y, y ∈ A ↔ ((σ : L ≃ₐ[K] L)⁻¹ • y) ∈ A := fun y => by
      conv_lhs => rw [← hs]
      exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem
    rw [key ((σ : L ≃ₐ[K] L) x)]
    rw [show ((σ : L ≃ₐ[K] L)⁻¹ • (σ : L ≃ₐ[K] L) x) = x by
      rw [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]]
  · intro a ha
    have h0 : (σ • IsLocalRing.residue A ⟨a, ha⟩ : IsLocalRing.ResidueField A) =
        IsLocalRing.residue A ⟨a, ha⟩ :=
      DFunLike.congr_fun (MonoidHom.mem_ker.mp hσ) (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff] at h0
    exact h0

/-- Conversely, the concrete conditions give PkgI2's `IsInertia`. -/
theorem isInertia_of (A : ValuationSubring L) (σ : L ≃ₐ[K] L)
    (h1 : ∀ x, σ x ∈ A ↔ x ∈ A) (h2 : ∀ a ∈ A, σ a - a ∈ A.nonunits) :
    PkgI2.IsInertia A σ := by
  have hd : σ ∈ A.decompositionSubgroup K := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h1 (σ⁻¹ • x)]
    rw [show σ (σ⁻¹ • x) = x by
      rw [AlgEquiv.smul_def, ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]]
  refine ⟨hd, ?_⟩
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  ext r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ, hd⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a =
    IsLocalRing.residue A a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
  exact h2 a a.2

end Val

/-! ### The proof of `GoodRedTorsion` -/

set_option maxHeartbeats 1000000 in
/-- **`GoodRedTorsion`, proved** (Mathlib, the copied `bcPt`/`trPt` and neron-lg's DVR
classification; NOS enters as the hypothesis of the Prop). -/
theorem goodRedTorsion : HSyn.LinkedTate.GoodRedTorsion := by
  intro hNOS K L L' _ hKL hLL' A hA ℓ _
  letI hNF : NumberField L' := numberField_of_fd L'
  intro p hp hp3 hpl v hv σ' hσ n x hx
  -- `K` is a number field
  haveI hKfd : FiniteDimensional ℚ K := FiniteDimensional.of_injective
    (IntermediateField.inclusion (hKL.trans hLL')).toLinearMap
    (IntermediateField.inclusion (hKL.trans hLL')).toRingHom.injective
  haveI hKNF : NumberField K := numberField_of_fd K
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  letI iKL' : Algebra K L' := incAlg (hKL.trans hLL')
  haveI tKLL' : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI tLΩ : IsScalarTower L L' (AlgebraicClosure L') := inferInstance
  haveI tKL'Ω : IsScalarTower K L' (AlgebraicClosure L') := inferInstance
  haveI tKLΩ : IsScalarTower K L (AlgebraicClosure L') := IsScalarTower.of_algebraMap_eq
    (fun y => by
      rw [IsScalarTower.algebraMap_apply K L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply L L' (AlgebraicClosure L'),
        IsScalarTower.algebraMap_apply K L L'])
  -- `Ω = \bar{L'}` is an algebraic closure of `K`
  haveI tQKL' : IsScalarTower ℚ K L' := IsScalarTower.of_algebraMap_eq (fun q => by
    rw [eq_ratCast (algebraMap ℚ L') q, eq_ratCast (algebraMap ℚ K) q, map_ratCast])
  haveI : Algebra.IsAlgebraic ℚ L' := Algebra.IsAlgebraic.of_finite ℚ L'
  haveI : Algebra.IsAlgebraic K L' := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : Algebra.IsAlgebraic L' (AlgebraicClosure L') := AlgebraicClosure.isAlgebraic L'
  haveI : Algebra.IsAlgebraic K (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans K L' (AlgebraicClosure L')
  haveI : IsAlgClosure K (AlgebraicClosure L') := ⟨inferInstance, inferInstance⟩
  let τ : AlgebraicClosure L' ≃ₐ[K] AlgebraicClosure K :=
    IsAlgClosure.equiv K (AlgebraicClosure L') (AlgebraicClosure K)
  -- `g : ℚ̄ → Ω` is bijective
  let g : PkgI4.Qbar →ₐ[ℚ] AlgebraicClosure L' := (G0Galois.qEmbRing L').toRatAlgHom
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L') :=
    Algebra.IsAlgebraic.trans ℚ L' (AlgebraicClosure L')
  have hgbij : Function.Bijective g := by
    letI : Algebra PkgI4.Qbar (AlgebraicClosure L') := g.toAlgebra
    haveI : IsScalarTower ℚ PkgI4.Qbar (AlgebraicClosure L') :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L') := inferInstance
    haveI : Algebra.IsIntegral PkgI4.Qbar (AlgebraicClosure L') := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ge : PkgI4.Qbar ≃+* AlgebraicClosure L' := RingEquiv.ofBijective (G0Galois.qEmbRing L') hgbij
  have hge : ∀ z, ge z = G0Galois.qEmbRing L' z := fun _ => rfl
  -- the transport `ψ : \bar K ≃ ℚ̄`, the place `w` of `\bar K` and `O = w ∩ K`
  let ψ : AlgebraicClosure K ≃+* PkgI4.Qbar := τ.symm.toRingEquiv.trans ge.symm
  have hψ : ∀ y, ψ y = ge.symm (τ.symm y) := fun _ => rfl
  let w : ValuationSubring (AlgebraicClosure K) := v.comap (ψ : AlgebraicClosure K →+* PkgI4.Qbar)
  let O : ValuationSubring K := w.comap (algebraMap K (AlgebraicClosure K))
  -- `p ∈ 𝔪_w`
  have hpw : ((p : ℕ) : AlgebraicClosure K) ∈ w.nonunits := by
    rw [mem_nonunits_comap v ψ, map_natCast]; exact hv
  -- integers prime to `p` are units of `O`
  have hunit : ∀ m : ℕ, Nat.Coprime m p → IsUnit (m : O) := by
    intro m hm
    obtain ⟨hm0, hmi⟩ := inv_mem_of_notMem_nonunits w (natCast_notMem_nonunits w hpw hm)
    have hm0K : (m : K) ≠ 0 := by
      intro h; apply hm0
      rw [← map_natCast (algebraMap K (AlgebraicClosure K)), h, map_zero]
    have hmO : (m : K)⁻¹ ∈ O := by
      rw [ValuationSubring.mem_comap, map_inv₀, map_natCast]; exact hmi
    refine isUnit_iff_exists_inv.mpr ⟨⟨(m : K)⁻¹, hmO⟩, Subtype.ext ?_⟩
    push_cast
    exact mul_inv_cancel₀ hm0K
  -- `O ≠ K`: `p⁻¹ ∉ O`
  have hOtop : O ≠ ⊤ := by
    intro htop
    have hpi : ((p : K))⁻¹ ∈ O := by rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap, map_inv₀, map_natCast] at hpi
    rw [ValuationSubring.mem_nonunits_iff_or] at hpw
    rcases hpw with h | h
    · exact hp.ne_zero (by exact_mod_cast h)
    · exact h hpi
  haveI hODVR : IsDiscreteValuationRing O := NLG.isDiscreteValuationRing_of_ne_top O hOtop
  -- `3` and `ℓⁿ` are units in `O`
  have hp3' : p ≠ 3 := fun h => hp3 (by rw [h]; exact Finset.mem_singleton_self 3)
  have h3 : IsUnit (3 : O) := by
    have := hunit 3 ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3'))
    exact_mod_cast this
  have hℓp : Nat.Coprime (ℓ ^ n) p :=
    Nat.Coprime.pow_left n ((Nat.coprime_primes (Fact.out : ℓ.Prime) hp).mpr (Ne.symm hpl))
  -- NOS (a) ⇒ (b) at `(O, w)`
  have htriv := ((hNOS K O w rfl (ObjBridge.toGrp A)).1.mp (hA O h3)) (ℓ ^ n)
    (pow_pos (Fact.out : ℓ.Prime).pos n) (by exact_mod_cast hunit (ℓ ^ n) hℓp)
  -- the inertia element `σ_K = τ σ' τ⁻¹` at `w`
  obtain ⟨σ, hσI, hσeq⟩ := hσ
  obtain ⟨hv1, hv2⟩ := of_mem_inertia ℚ v σ hσI
  rw [hσeq] at hv1 hv2
  let s' : AlgebraicClosure L' ≃ₐ[L'] AlgebraicClosure L' := σ'
  let σK : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    (τ.symm.trans (s'.restrictScalars K)).trans τ
  have hσK : ∀ y, σK y = τ (s' (τ.symm y)) := fun _ => rfl
  have hres : ∀ y, ψ (σK y) = (G0Galois.resQ L' σ') (ψ y) := by
    intro y
    apply ge.injective
    show ge (ge.symm (τ.symm (σK y))) = ge ((G0Galois.resQ L' σ') (ge.symm (τ.symm y)))
    rw [RingEquiv.apply_symm_apply, hσK, AlgEquiv.symm_apply_apply]
    have hspec := G0Galois.resQ_spec L' σ' (ge.symm (τ.symm y))
    rw [← hge, ← hge, RingEquiv.apply_symm_apply] at hspec
    exact hspec.symm
  have hI : PkgI2.IsInertia w σK := by
    refine isInertia_of K w σK (fun y => ?_) (fun a ha => ?_)
    · show ψ (σK y) ∈ v ↔ ψ y ∈ v
      rw [hres]; exact hv1 (ψ y)
    · rw [mem_nonunits_comap v ψ, map_sub, hres]
      exact hv2 (ψ a) ha
  -- the points
  let E := (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
    (AlgebraicClosure L')).trans ((UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')).trans
      (UnramTate.trPt A τ))
  have hE : ∀ y, E ((@PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y) =
      A.galAct σK (E y) := by
    intro y
    show UnramTate.trPt A τ (UnramTate.bcPt (K := K) (L := L) A (AlgebraicClosure L')
        (UnramTate.bcPt (K := L) (L := L') (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL))
          (AlgebraicClosure L')
          ((@PkgI3.AbVar.baseChange L _
            (@PkgI3.AbVar.baseChange K _ A L _ (incAlg hKL)) L' _ (incAlg hLL')).galAct s' y))) = _
    rw [UnramTate.bcPt_galAct, UnramTate.bcPt_galAct]
    exact UnramTate.trPt_galAct A τ _ σK (fun z => by rw [hσK, AlgEquiv.symm_apply_apply]; rfl) _
  have hEx : E x ^ (ℓ ^ n) = 1 := by rw [← map_pow, hx, map_one]
  have hfix : A.galAct σK (E x) = E x := htriv σK hI (E x) hEx
  apply E.injective
  exact (hE x).trans hfix

end LTGoodRed

end

end LTGoodRedSec


/-! ## lt-goodred §4: `QMEndRank` reduced to I3.M1, T27 and one algebraic glue Prop

* `rank ≥ 4` (proved, `four_le_finrank`): `𝒪 ≅ ℤ⁴` (`ofIntHom`) and `endBC ∘ endBC ∘ ι` is an
  injective ring map `𝒪 → End(A')`; `End(A')` is finite over `ℤ` by I3.M1.
* `rank ≤ rank End(A'_Ω)` (proved, `finrank_le_baseChange`): `endBC` is injective, I3.M1.
* T27 at `A'' = A'_Ω`, `Ω = \bar{L'}`: its hypotheses are proved here: `dim A'' = 2`
  (`pkgI3_dim_baseChange`, three times), `B = (2,−3)` is a division algebra (`quatB6_isUnit`: the
  norm form `x₀² − 2x₁² + 3x₂² − 6x₃²` is anisotropic over `ℚ`, 3-adic descent), and
  `B →ₐ[ℚ] End⁰(A'')` (`quatEmbed`, from `ι` and base change).
* Case `End⁰(A'') ≅ B`: `rank End(A'') = dim_ℚ End⁰(A'') = 4` (proved).
* Case `End⁰(A'') ≅ M₂(ℚ(√d))`, `d < 0`: the named glue Prop `QMSplitCaseRank`. -/

section LTQMRankSec

set_option linter.style.haveILetI false

noncomputable section

namespace LTGoodRed.QM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open G0ModField LeafQM
open scoped Quaternion TensorProduct

/-! ### `𝒪 ≅ ℤ⁴` and the lower bound -/

theorem ofInt_injective : Function.Injective ofInt := by
  intro n m h
  have h0 := congrArg QuaternionAlgebra.re h
  have h1 := congrArg QuaternionAlgebra.imI h
  have h2 := congrArg QuaternionAlgebra.imJ h
  have h3 := congrArg QuaternionAlgebra.imK h
  simp only [ofInt] at h0 h1 h2 h3
  have e2 : (n 2 : ℚ) = m 2 := by linarith
  have e3 : (n 3 : ℚ) = m 3 := by linarith
  have e0 : (n 0 : ℚ) = m 0 := by linarith
  have e1 : (n 1 : ℚ) = m 1 := by linarith
  funext i
  fin_cases i
  · exact_mod_cast e0
  · exact_mod_cast e1
  · exact_mod_cast e2
  · exact_mod_cast e3

/-- `n ↦ ofInt n`, an additive bijection `ℤ⁴ → 𝒪`. -/
def ofIntHom : (Fin 4 → ℤ) →+ O where
  toFun n := ⟨ofInt n, n, rfl⟩
  map_zero' := Subtype.ext ofInt_zero
  map_add' n m := Subtype.ext (ofInt_add n m).symm

theorem ofIntHom_injective : Function.Injective ofIntHom :=
  fun n m h => ofInt_injective (congrArg Subtype.val h)

/-- **`rank End(A) ≥ 4` for a QM abelian variety** (proved; I3.M1 for finiteness). -/
theorem four_le_finrank (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k] (A : PkgI3.AbVar k)
    (φ : O →+* PkgI3.AbVar.End A) (hφ : Function.Injective φ) :
    4 ≤ Module.finrank ℤ (PkgI3.AbVar.End A) := by
  obtain ⟨-, hfin, -, -⟩ := hM1 k A A
  let F : (Fin 4 → ℤ) →+ PkgI3.AbVar.End A := φ.toAddMonoidHom.comp ofIntHom
  have hF : Function.Injective F := hφ.comp ofIntHom_injective
  have := LinearMap.finrank_le_finrank_of_injective (f := F.toIntLinearMap) hF
  rwa [Module.finrank_fin_fun] at this

/-- **`rank End(A) ≤ rank End(A_Ω)`** (proved; `endBC` is injective, I3.M1). -/
theorem finrank_le_baseChange (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k]
    (A : PkgI3.AbVar k) (Ω : Type) [Field Ω] [Algebra k Ω] :
    Module.finrank ℤ (PkgI3.AbVar.End A) ≤
      Module.finrank ℤ (PkgI3.AbVar.End (A.baseChange Ω)) := by
  obtain ⟨-, hfin, -, -⟩ := hM1 Ω (A.baseChange Ω) (A.baseChange Ω)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (HSyn.LinkedTate.endBC A Ω).toAddMonoidHom.toIntLinearMap)
    (HSyn.LinkedTate.endBC_injective A Ω)

/-- `rank_ℤ End(A) = dim_ℚ End⁰(A)` (I3.M1: `End(A)` is free). -/
theorem finrank_end0 (hM1 : PkgI3.HomFreeFinite) {k : Type} [Field k] (A : PkgI3.AbVar k) :
    Module.finrank ℚ (PkgI3.AbVar.End0 A) = Module.finrank ℤ (PkgI3.AbVar.End A) := by
  obtain ⟨hfree, -, -, -⟩ := hM1 k A A
  exact Module.finrank_baseChange

/-! ### `B = (2, −3)` is a division algebra -/

theorem mod3_step (a b e : ℤ) (h : a ^ 2 - 2 * b ^ 2 + 3 * e = 0) : 3 ∣ a ∧ 3 ∣ b := by
  have h3 : (3 : ZMod 3) = 0 := rfl
  have hc := congrArg (Int.cast : ℤ → ZMod 3) h
  push_cast at hc
  have h' : ((a : ZMod 3)) ^ 2 + ((b : ZMod 3)) ^ 2 = 0 := by
    linear_combination hc + ((b : ZMod 3) ^ 2 - (e : ZMod 3)) * h3
  have key : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
  obtain ⟨ha, hb⟩ := key _ _ h'
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd a 3).mp ha, (ZMod.intCast_zmod_eq_zero_iff_dvd b 3).mp hb⟩

theorem pow3_dvd (k : ℕ) : ∀ a b c d : ℤ, a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0 →
    3 ^ k ∣ a ∧ 3 ^ k ∣ b ∧ 3 ^ k ∣ c ∧ 3 ^ k ∣ d := by
  induction k with
  | zero => intro a b c d _; simp
  | succ k ih =>
    intro a b c d h
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := mod3_step a b (c ^ 2 - 2 * d ^ 2) (by linear_combination h)
    have h' : (3 : ℤ) * (c ^ 2 - 2 * d ^ 2 + 3 * (a' ^ 2 - 2 * b' ^ 2)) = 0 := by
      linear_combination h
    obtain ⟨⟨c', rfl⟩, ⟨d', rfl⟩⟩ := mod3_step c d (a' ^ 2 - 2 * b' ^ 2)
      ((mul_eq_zero.mp h').resolve_left (by norm_num))
    have h'' : (9 : ℤ) * (a' ^ 2 - 2 * b' ^ 2 + 3 * c' ^ 2 - 6 * d' ^ 2) = 0 := by
      linear_combination h
    obtain ⟨h1, h2, h3, h4⟩ := ih a' b' c' d' ((mul_eq_zero.mp h'').resolve_left (by norm_num))
    rw [pow_succ']
    exact ⟨mul_dvd_mul_left 3 h1, mul_dvd_mul_left 3 h2, mul_dvd_mul_left 3 h3,
      mul_dvd_mul_left 3 h4⟩

theorem eq_zero_of_pow3_dvd (a : ℤ) (h : ∀ k : ℕ, 3 ^ k ∣ a) : a = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h a.natAbs)
  rw [Int.natAbs_pow]
  exact Nat.lt_pow_self (by norm_num)

/-- The norm form of `B` is anisotropic over `ℤ`. -/
theorem norm6_int (a b c d : ℤ) (h : a ^ 2 - 2 * b ^ 2 + 3 * c ^ 2 - 6 * d ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 :=
  ⟨eq_zero_of_pow3_dvd a fun k => (pow3_dvd k a b c d h).1,
    eq_zero_of_pow3_dvd b fun k => (pow3_dvd k a b c d h).2.1,
    eq_zero_of_pow3_dvd c fun k => (pow3_dvd k a b c d h).2.2.1,
    eq_zero_of_pow3_dvd d fun k => (pow3_dvd k a b c d h).2.2.2⟩

/-- The norm form of `B` is anisotropic over `ℚ`. -/
theorem norm6_rat (q0 q1 q2 q3 : ℚ) (h : q0 ^ 2 - 2 * q1 ^ 2 + 3 * q2 ^ 2 - 6 * q3 ^ 2 = 0) :
    q0 = 0 ∧ q1 = 0 ∧ q2 = 0 ∧ q3 = 0 := by
  have hd0 : (q0.den : ℚ) ≠ 0 := by exact_mod_cast q0.den_nz
  have hd1 : (q1.den : ℚ) ≠ 0 := by exact_mod_cast q1.den_nz
  have hd2 : (q2.den : ℚ) ≠ 0 := by exact_mod_cast q2.den_nz
  have hd3 : (q3.den : ℚ) ≠ 0 := by exact_mod_cast q3.den_nz
  set D : ℚ := q0.den * q1.den * q2.den * q3.den with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact mul_ne_zero (mul_ne_zero (mul_ne_zero hd0 hd1) hd2) hd3
  have e0 : ((q0.num * q1.den * q2.den * q3.den : ℤ) : ℚ) = q0 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q0]; ring
  have e1 : ((q1.num * q0.den * q2.den * q3.den : ℤ) : ℚ) = q1 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q1]; ring
  have e2 : ((q2.num * q0.den * q1.den * q3.den : ℤ) : ℚ) = q2 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q2]; ring
  have e3 : ((q3.num * q0.den * q1.den * q2.den : ℤ) : ℚ) = q3 * D := by
    push_cast; rw [← Rat.mul_den_eq_num q3]; ring
  have hZ := norm6_int (q0.num * q1.den * q2.den * q3.den) (q1.num * q0.den * q2.den * q3.den)
    (q2.num * q0.den * q1.den * q3.den) (q3.num * q0.den * q1.den * q2.den) (by
      have : (((q0.num * q1.den * q2.den * q3.den : ℤ) : ℚ)) ^ 2
          - 2 * (((q1.num * q0.den * q2.den * q3.den : ℤ) : ℚ)) ^ 2
          + 3 * (((q2.num * q0.den * q1.den * q3.den : ℤ) : ℚ)) ^ 2
          - 6 * (((q3.num * q0.den * q1.den * q2.den : ℤ) : ℚ)) ^ 2 = 0 := by
        rw [e0, e1, e2, e3]; linear_combination D ^ 2 * h
      exact_mod_cast this)
  obtain ⟨z0, z1, z2, z3⟩ := hZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e0; rw [z0, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e1; rw [z1, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e2; rw [z2, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0
  · have := e3; rw [z3, Int.cast_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_right hD0

/-- **`B = (2,−3)_ℚ` is a division algebra** (proved): `x · x̄ = n(x)` with `n` anisotropic. -/
theorem quatB6_isUnit : ∀ x : ℍ[ℚ, 2, -3], x ≠ 0 → IsUnit x := by
  intro x hx
  have hn : (x * star x).re = x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 := by
    simp [QuaternionAlgebra.re_mul]; ring
  have hn0 : (x * star x).re ≠ 0 := by
    intro h0
    rw [hn] at h0
    obtain ⟨z0, z1, z2, z3⟩ := norm6_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext z0 z1 z2 z3)
  set n := (x * star x).re with hndef
  have hxs : x * star x = (n : ℍ[ℚ, 2, -3]) := QuaternionAlgebra.mul_star_eq_coe x
  have hsx : star x * x = (n : ℍ[ℚ, 2, -3]) := by rw [← hxs]; exact (star_comm_self' x)
  have hinv : (n⁻¹ : ℚ) • (n : ℍ[ℚ, 2, -3]) = 1 := by
    rw [← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul, inv_mul_cancel₀ hn0,
      QuaternionAlgebra.coe_one]
  refine isUnit_iff_exists.mpr ⟨n⁻¹ • star x, ?_, ?_⟩
  · rw [mul_smul_comm, hxs, hinv]
  · rw [smul_mul_assoc, hsx, hinv]

/-! ### `B →ₐ[ℚ] End⁰(A)` from a QM structure -/

/-- `i ∈ 𝒪`. -/
def oI' : O := ⟨ofInt ![0, 1, 0, 0], _, rfl⟩
/-- `j = 2·(1+j)/2 − 1 ∈ 𝒪`. -/
def oJ' : O := ⟨ofInt ![-1, 0, 2, 0], _, rfl⟩

theorem oI'_mul_oI' : oI' * oI' = 2 := by
  apply Subtype.ext
  show ofInt ![0, 1, 0, 0] * ofInt ![0, 1, 0, 0] = 2
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oJ'_mul_oJ' : oJ' * oJ' = -3 := by
  apply Subtype.ext
  show ofInt ![-1, 0, 2, 0] * ofInt ![-1, 0, 2, 0] = -3
  ext <;> simp [ofInt, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat,
    QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num

theorem oJ'_mul_oI' : oJ' * oI' = -(oI' * oJ') := by
  apply Subtype.ext
  show ofInt ![-1, 0, 2, 0] * ofInt ![0, 1, 0, 0] = -(ofInt ![0, 1, 0, 0] * ofInt ![-1, 0, 2, 0])
  ext <;> simp [ofInt] <;> norm_num

/-- **`B →ₐ[ℚ] End⁰(A)` from a ring map `𝒪 → End(A)`** (proved: `i ↦ 1 ⊗ φ(i)`, `j ↦ 1 ⊗ φ(j)`,
Mathlib's `QuaternionAlgebra.Basis.liftHom`). -/
theorem quatEmbed {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : O →+* PkgI3.AbVar.End A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) := by
  let ψ : O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] PkgI3.AbVar.End0 A).toRingHom.comp φ
  refine ⟨QuaternionAlgebra.Basis.liftHom
    { i := ψ oI', j := ψ oJ', k := ψ oI' * ψ oJ',
      i_mul_i := ?_, j_mul_j := ?_, i_mul_j := rfl, j_mul_i := ?_ }⟩
  · rw [← map_mul, oI'_mul_oI', map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
      map_ofNat]
  · rw [← map_mul, oJ'_mul_oJ', map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
      map_ofNat]
  · rw [← map_mul, oJ'_mul_oI', map_neg, map_mul, zero_smul, zero_sub]

/-! ### The reduction -/

/-- **Glue (algebra; Albert's classification for simple abelian surfaces in characteristic 0,
Mumford §21, numbering UNVERIFIED): the split geometric case.** For an abelian surface `A` over a
field `k` of characteristic `0` with an injective ring map `ι : 𝒪 → End_k(A)` and `EndDivision A`,
if `End⁰(A_Ω) ≅ M₂(ℚ(√d))` (`d < 0`) for an algebraically closed `Ω ⊇ k`, then
`rank_ℤ End_k(A) ≤ 4`. Route (STANDARD): `End⁰(A)` embeds in `End⁰(A_Ω)` (`endBC`, flatness of
`ℚ/ℤ`) as a subalgebra `S ⊇ ι(B)`; `S` is a left `B`-vector space, so `dim_ℚ S ∈ {4, 8}`; if
`dim S = 8` then `S = M₂(ℚ(√d))` contains a nonzero nilpotent, whose integer multiple in
`End(A)` is a nonzero nilpotent endomorphism; a nilpotent endomorphism of a positive-dimensional
abelian variety is not surjective, contradicting `EndDivision`. GLUE. -/
def QMSplitCaseRank : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] (φ : O →+* PkgI3.AbVar.End A), Function.Injective φ → A.dim = 2 →
    PkgI3.EndDivision A → ∀ d : ℚ, d < 0 →
    Nonempty (PkgI3.AbVar.End0 (A.baseChange Ω) ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    Module.finrank ℤ (PkgI3.AbVar.End A) ≤ 4

/-- **`QMEndRank`, proved** from the leaves I3.M1 (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3) and
T27 (`PkgI3.QMDichotomyYu`, Yu 2013 Thm 1.1) and the glue `QMSplitCaseRank`. -/
theorem qmEndRank_of (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu)
    (hS : QMSplitCaseRank) : HSyn.LinkedTate.QMEndRank := by
  intro K L L' _ hKL hLL' PK hdiv
  letI iKL : Algebra K L := incAlg hKL
  letI iLL' : Algebra L L' := incAlg hLL'
  set A' : PkgI3.AbVar L' := @PkgI3.AbVar.baseChange L _
      (@PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)) L' _ (incAlg hLL') with hA'
  let φ : O →+* PkgI3.AbVar.End A' :=
    (HSyn.LinkedTate.endBC (PK.A.baseChange L) L').comp
      ((HSyn.LinkedTate.endBC PK.A L).comp PK.q.iota)
  have hφ : Function.Injective φ :=
    (HSyn.LinkedTate.endBC_injective _ L').comp
      ((HSyn.LinkedTate.endBC_injective _ L).comp PK.q.injective)
  have hdimA' : A'.dim = 2 := by
    rw [hA', G0Dim.pkgI3_dim_baseChange, G0Dim.pkgI3_dim_baseChange]
    exact PK.surface
  refine le_antisymm ?_ (four_le_finrank hM1 A' φ hφ)
  -- the geometric endomorphism algebra
  let Ω := AlgebraicClosure L'
  let A'' : PkgI3.AbVar Ω := A'.baseChange Ω
  have hdimA'' : A''.dim = 2 := by
    show (A'.baseChange Ω).dim = 2
    rw [G0Dim.pkgI3_dim_baseChange]; exact hdimA'
  let φ'' : O →+* PkgI3.AbVar.End A'' := (HSyn.LinkedTate.endBC A' Ω).comp φ
  rcases hT27 Ω A'' hdimA'' 2 (-3) PkgI3.quatIndefinite_two_neg_three quatB6_isUnit
      (quatEmbed A'' φ'') with he | ⟨d, hd, he⟩
  · obtain ⟨e⟩ := he
    calc Module.finrank ℤ (PkgI3.AbVar.End A')
        ≤ Module.finrank ℤ (PkgI3.AbVar.End A'') := finrank_le_baseChange hM1 A' Ω
      _ = Module.finrank ℚ (PkgI3.AbVar.End0 A'') := (finrank_end0 hM1 A'').symm
      _ = Module.finrank ℚ ℍ[ℚ, 2, -3] := e.toLinearEquiv.finrank_eq
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  · exact hS L' A' Ω φ hφ hdimA' hdiv d hd he

end LTGoodRed.QM

end

end LTQMRankSec


/-! ## lt-goodred §5: `QMSplitCaseRank`, proved from I3.M1

Suppose `rank End(A) > 4`. Then (all proved below):
* `End⁰(A) ↪ End⁰(A_Ω) ≅ M₂(ℚ(√d))`, a `ℚ`-algebra embedding (`endBC` injective, `ℚ` flat over
  `ℤ`); so `dim_ℚ End⁰(A) ≤ 8`;
* `B →ₐ[ℚ] End⁰(A)` (`quatEmbed`) and `B` is a division algebra, so for `s ∉ θ(B)` the map
  `(b, b') ↦ θ(b) + θ(b')·s` is injective: `dim End⁰(A) ≥ 8` (`eight_le_finrank`);
* hence `End⁰(A) ≅ M₂(ℚ(√d))`, and the preimage `x` of `E₁₂` is a nonzero element with `x² = 0`;
* clearing denominators, `n·x = 1 ⊗ m` with `m ∈ End(A)`, `m ≠ 0`, `m² = 0` (`End(A)` is free,
  I3.M1, so `m ↦ 1 ⊗ m` is injective);
* a nonzero `m` is an isogeny (`EndDivision`), so `m ∘ m = 0` is surjective; but the zero
  endomorphism factors through `Spec k`, a point, so `A` would be a point, against `dim A = 2`
  (`eq_zero_of_mul_self_eq_zero`). -/

section LTSplitSec

set_option linter.style.haveILetI false

noncomputable section

namespace LTGoodRed.QM

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM
open scoped Quaternion TensorProduct

/-! ### A square-zero endomorphism of an `EndDivision` surface is zero -/

/-- **A square-zero endomorphism of a positive-dimensional `EndDivision` abelian variety is zero**
(proved): otherwise it is surjective (an isogeny), so its square, the zero endomorphism, is
surjective; the zero endomorphism factors through `Spec k`, so `A` is a point, of dimension `≤ 0`. -/
theorem eq_zero_of_mul_self_eq_zero {k : Type} [Field k] (A : PkgI3.AbVar k)
    (hdiv : PkgI3.EndDivision A) (hdim : A.dim = 2) (m : PkgI3.AbVar.End A) (hm : m * m = 0) :
    m = 0 := by
  by_contra hm0
  obtain ⟨-, hsurj⟩ := hdiv m hm0
  have hcomp : (m * m).hom = m.hom ≫ m.hom := rfl
  have h1 : m.hom ≫ m.hom = (1 : A.X ⟶ A.X) := by rw [← hcomp, hm]; rfl
  have hs : Surjective (m.hom ≫ m.hom).left := by
    rw [Over.comp_left]; infer_instance
  rw [h1, Hom.one_def, Over.comp_left] at hs
  haveI hsub : Subsingleton A.X.left := by
    constructor
    intro y1 y2
    obtain ⟨x1, rfl⟩ := hs.surj y1
    obtain ⟨x2, rfl⟩ := hs.surj y2
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    congr 1
    exact Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _
  have hle : A.dim ≤ 0 := topologicalKrullDim_zero_of_discreteTopology A.X.left
  rw [hdim] at hle
  exact absurd hle (by decide)

/-! ### `ℚ ⊗ M` for a free `ℤ`-module `M` -/

section Tensor

variable {M : Type} [Ring M]

theorem intCast_smul_one_tmul (c : ℤ) (m : M) :
    ((c : ℚ)) • ((1 : ℚ) ⊗ₜ[ℤ] m) = (1 : ℚ) ⊗ₜ[ℤ] (c • m) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one,
    show ((c : ℤ) : ℚ) = c • (1 : ℚ) by simp, TensorProduct.smul_tmul]

/-- Every element of `ℚ ⊗ M` has an integer multiple of the form `1 ⊗ m`. -/
theorem exists_smul_eq_tmul (x : ℚ ⊗[ℤ] M) :
    ∃ (n : ℤ) (m : M), n ≠ 0 ∧ (n : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] m := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q m =>
    refine ⟨q.den, q.num • m, by exact_mod_cast q.den_nz, ?_⟩
    rw [TensorProduct.smul_tmul', smul_eq_mul,
      show ((q.den : ℤ) : ℚ) * q = ((q.num : ℤ) : ℚ) by
        rw [Int.cast_natCast, mul_comm]; exact Rat.mul_den_eq_num q,
      show ((q.num : ℤ) : ℚ) = q.num • (1 : ℚ) by simp, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨n, m, hn, h⟩ := hx
    obtain ⟨n', m', hn', h'⟩ := hy
    refine ⟨n * n', n' • m + n • m', mul_ne_zero hn hn', ?_⟩
    rw [smul_add, Int.cast_mul, mul_comm, mul_smul, h, mul_comm, mul_smul, h',
      intCast_smul_one_tmul, intCast_smul_one_tmul, TensorProduct.tmul_add]

/-- `m ↦ 1 ⊗ m` is injective for a free `ℤ`-module (flatness). -/
theorem one_tmul_injective [Module.Free ℤ M] :
    Function.Injective (fun m : M => (1 : ℚ) ⊗ₜ[ℤ] m) := by
  have hinj : Function.Injective ((Algebra.linearMap ℤ ℚ).rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (fun a b h => by simpa using h)
  intro m m' h
  apply (TensorProduct.lid ℤ M).symm.injective
  apply hinj
  simpa [TensorProduct.lid_symm_apply] using h

end Tensor

/-! ### A copy of `B` and an element outside it give dimension `≥ 8` -/

theorem eight_le_finrank {R : Type} [Ring R] [Algebra ℚ R] [FiniteDimensional ℚ R]
    (θ : ℍ[ℚ, 2, -3] →ₐ[ℚ] R) (h4 : 4 < Module.finrank ℚ R) : 8 ≤ Module.finrank ℚ R := by
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    rw [Module.finrank_zero_of_subsingleton] at h4
    omega
  have hr : Module.finrank ℚ (LinearMap.range θ.toLinearMap) ≤ 4 := by
    calc _ ≤ Module.finrank ℚ ℍ[ℚ, 2, -3] := LinearMap.finrank_range_le _
      _ = 4 := QuaternionAlgebra.finrank_eq_four (R := ℚ) _ _ _
  obtain ⟨s, hs⟩ : ∃ s, s ∉ LinearMap.range θ.toLinearMap := by
    by_contra h
    push_neg at h
    have htop : LinearMap.range θ.toLinearMap = ⊤ := eq_top_iff.mpr fun x _ => h x
    rw [htop, finrank_top] at hr
    omega
  have hunit : ∀ b : ℍ[ℚ, 2, -3], b ≠ 0 → ∃ c, θ c * θ b = 1 := by
    intro b hb
    obtain ⟨u, rfl⟩ := quatB6_isUnit b hb
    exact ⟨↑u⁻¹, by rw [← map_mul, Units.inv_mul, map_one]⟩
  let Lm : (ℍ[ℚ, 2, -3] × ℍ[ℚ, 2, -3]) →ₗ[ℚ] R :=
    θ.toLinearMap.comp (LinearMap.fst ℚ _ _) +
      ((LinearMap.mulRight ℚ s).comp θ.toLinearMap).comp (LinearMap.snd ℚ _ _)
  have hLm : ∀ b b', Lm (b, b') = θ b + θ b' * s := fun _ _ => rfl
  have hinj : Function.Injective Lm := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨b, b'⟩ h
    rw [hLm] at h
    by_cases hb' : b' = 0
    · subst hb'
      rw [map_zero, zero_mul, add_zero] at h
      by_cases hb : b = 0
      · rw [hb]; rfl
      · obtain ⟨c, hc⟩ := hunit b hb
        rw [h, mul_zero] at hc
        exact absurd hc zero_ne_one
    · exfalso
      obtain ⟨c, hc⟩ := hunit b' hb'
      apply hs
      refine ⟨-(c * b), ?_⟩
      show θ (-(c * b)) = s
      have : s = θ c * (θ b' * s) := by rw [← _root_.mul_assoc, hc, _root_.one_mul]
      rw [this, eq_neg_of_add_eq_zero_right h, map_neg, map_mul, mul_neg]
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, QuaternionAlgebra.finrank_eq_four (R := ℚ) 2 0 (-3)] at this

/-! ### The proof -/

/-- **`QMSplitCaseRank`, proved** from I3.M1 (`PkgI3.HomFreeFinite`). -/
theorem qmSplitCaseRank (hM1 : PkgI3.HomFreeFinite) : QMSplitCaseRank := by
  intro k _ _ A Ω _ _ _ φ _ hdim hdiv d _ he
  obtain ⟨e⟩ := he
  obtain ⟨hfreeM, hfinM, -, -⟩ := hM1 k A A
  obtain ⟨hfreeN, hfinN, -, -⟩ := hM1 Ω (A.baseChange Ω) (A.baseChange Ω)
  by_contra hlt
  push_neg at hlt
  -- `F = ℚ(√d)`, `dim_ℚ M₂(F) = 8`
  have hf : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero (by norm_num) d
  have hF : Module.finrank ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) = 2 := by
    rw [(AdjoinRoot.powerBasis hf).finrank, AdjoinRoot.powerBasis_dim,
      Polynomial.natDegree_X_pow_sub_C]
  haveI : Module.Finite ℚ (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) :=
    (AdjoinRoot.powerBasis hf).finite
  haveI : Nontrivial (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    rw [Module.finrank_zero_of_subsingleton] at hF
    omega
  have h8 : Module.finrank ℚ
      (Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) = 8 := by
    rw [Module.finrank_matrix, hF]; rfl
  -- `End⁰(A) ↪ End⁰(A_Ω)`
  let β : PkgI3.AbVar.End A →ₐ[ℤ] PkgI3.AbVar.End (A.baseChange Ω) :=
    (HSyn.LinkedTate.endBC A Ω).toIntAlgHom
  let Φ₀ : PkgI3.AbVar.End0 A →ₐ[ℚ] PkgI3.AbVar.End0 (A.baseChange Ω) :=
    Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) β
  haveI : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  have hΦ₀ : Function.Injective Φ₀ := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := ℚ) β.toLinearMap
      (HSyn.LinkedTate.endBC_injective A Ω)
    have heq : ⇑Φ₀ = ⇑(β.toLinearMap.lTensor ℚ) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul q m => simp [Φ₀, Algebra.TensorProduct.map_tmul, LinearMap.lTensor_tmul]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [heq]; exact h
  let Φ := e.toAlgHom.comp Φ₀
  have hΦ : Function.Injective Φ := e.injective.comp hΦ₀
  -- dimensions
  have hrank : Module.finrank ℚ (PkgI3.AbVar.End0 A) = Module.finrank ℤ (PkgI3.AbVar.End A) :=
    finrank_end0 hM1 A
  obtain ⟨θ⟩ := quatEmbed A φ
  have hge : 8 ≤ Module.finrank ℚ (PkgI3.AbVar.End0 A) :=
    eight_le_finrank θ (by rw [hrank]; exact hlt)
  have hle : Module.finrank ℚ (PkgI3.AbVar.End0 A) ≤ 8 := by
    rw [← h8]; exact LinearMap.finrank_le_finrank_of_injective (f := Φ.toLinearMap) hΦ
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ.toLinearMap)
      (by rw [h8]; omega)).mp hΦ
  -- the preimage of `E₁₂`
  let E : Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d)) := !![0, 1; 0, 0]
  have hE0 : E ≠ 0 := by
    intro h
    have := congrFun (congrFun h 0) 1
    simp [E] at this
  have hEE : E * E = 0 := by
    simp only [E, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨x, hx⟩ := hsurj E
  have hx0 : x ≠ 0 := by rintro rfl; exact hE0 (by rw [← hx, map_zero])
  have hxx : x * x = 0 := hΦ (by rw [map_mul, hx, hEE, map_zero])
  -- clearing denominators
  obtain ⟨n, m, hn, hnm⟩ := exists_smul_eq_tmul x
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [TensorProduct.tmul_zero, smul_eq_zero] at hnm
    rcases hnm with h | h
    · exact hn (by exact_mod_cast h)
    · exact hx0 h
  have hmm : m * m = 0 := by
    apply one_tmul_injective (M := PkgI3.AbVar.End A)
    show (1 : ℚ) ⊗ₜ[ℤ] (m * m) = (1 : ℚ) ⊗ₜ[ℤ] (0 : PkgI3.AbVar.End A)
    rw [TensorProduct.tmul_zero, ← _root_.mul_one (1 : ℚ), ← Algebra.TensorProduct.tmul_mul_tmul,
      ← hnm, smul_mul_smul_comm, hxx, smul_zero]
  exact hm0 (eq_zero_of_mul_self_eq_zero A hdiv hdim m hmm)

/-- **`QMEndRank` from the leaves I3.M1 and T27 alone** (proved). -/
theorem qmEndRank_of_leaves (hM1 : PkgI3.HomFreeFinite) (hT27 : PkgI3.QMDichotomyYu) :
    HSyn.LinkedTate.QMEndRank :=
  qmEndRank_of hM1 hT27 (qmSplitCaseRank hM1)

end LTGoodRed.QM

end

end LTSplitSec



end G0A2_c75_ltgoodred

end HDec
