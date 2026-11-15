import ZInQKernel.Contrib.OneProof.ShimuraSplit2

noncomputable section

namespace QMRecPrinted

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV NumberField IsDedekindDomain
open ShimuraCFT RayClassCFT
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.LeafPush2 (CPts IsUniformization)
open scoped TensorProduct FiniteAdeleExtension MonObj

section Defs

variable {E : Type} [Field E] [NumberField E] {g : ℕ}

def cmVec (Φ : Fin g → E →+* ℂ) : E →+ (Fin g → ℂ) where
  toFun x i := Φ i x
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp

def cmLat (Φ : Fin g → E →+* ℂ) (𝔞 : AddSubgroup E) : Submodule ℤ (Fin g → ℂ) :=
  (𝔞.map (cmVec Φ)).toIntSubmodule

def latHat (𝔞 : AddSubgroup E) : AddSubgroup (AQ ⊗[ℚ] E) :=
  AddSubgroup.closure {w | ∃ c ∈ ZhatQ, ∃ x ∈ 𝔞, w = c ⊗ₜ x}

def latAct (t : AQ ⊗[ℚ] E) (𝔞 : AddSubgroup E) : AddSubgroup E :=
  (latHat 𝔞).comap ((AddMonoidHom.mulLeft t).comp
    (Algebra.TensorProduct.includeRight : E →ₐ[ℚ] AQ ⊗[ℚ] E).toRingHom.toAddMonoidHom)

variable {Er : Type} [Field Er] [NumberField Er] {n : ℕ}

def rhoA (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) :
    AQ ⊗[ℚ] Er →ₐ[AQ] Matrix (Fin n) (Fin n) (AQ ⊗[ℚ] E) :=
  AlgHom.liftEquiv ℚ AQ Er _
    (((Algebra.TensorProduct.includeRight : E →ₐ[ℚ] AQ ⊗[ℚ] E).mapMatrix).comp ρ)

def reflexNorm (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) :
    (FiniteAdeleRing (𝓞 Er) Er)ˣ →* (AQ ⊗[ℚ] E)ˣ :=
  Units.map (Matrix.detMonoidHom.comp ((rhoA ρ).toMonoidHom.comp
    ((finiteAdeleBaseChangeAlgEquiv ℚ Er).symm.toMonoidHom)))

def IsReflexModel (Φ : Fin g → E →+* ℂ) (κr : Er →+* ℂ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E)
    (j : (Fin n → E) →+ (Fin g → ℂ)) : Prop :=
  (∀ (e : E) (v : Fin n → E), j (e • v) = fun i => Φ i e * j v i) ∧
  (∀ (a : Er) (v : Fin n → E), j ((ρ a).mulVec v) = κr a • j v) ∧
  Submodule.span ℂ (Set.range j) = ⊤ ∧
  n * Module.finrank ℚ E = g * Module.finrank ℚ Er

def IsOfType (Φ : Fin g → E →+* ℂ) (𝔞 : AddSubgroup E) {A : PkgI3.AbVar ℂ}
    (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)) : Prop :=
  ∀ e : E, (∀ x ∈ 𝔞, e * x ∈ 𝔞) →
    ∃ α : PkgI3.AbVar.End A, ∀ w, θ (fun i => Φ i e * w i) = θ w ≫ α.hom

end Defs

def MainTheoremCM : Prop :=
  ∃ ε : ℤˣ,
  ∀ (E : Type) [Field E] [NumberField E] (g : ℕ) (Φ : Fin g → E →+* ℂ),
    Module.finrank ℚ E = 2 * g →
    Function.Injective (Sum.elim Φ fun i => (starRingEnd ℂ).comp (Φ i)) →
  ∀ (Er : Type) [Field Er] [NumberField Er] (κr : Er →+* ℂ),
    κr.fieldRange = Subfield.closure (Set.range fun e : E => ∑ i, Φ i e) →
  ∀ (n : ℕ) (ρ : Er →ₐ[ℚ] Matrix (Fin n) (Fin n) E) (j : (Fin n → E) →+ (Fin g → ℂ)),
    IsReflexModel Φ κr ρ j →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 Er) Er), ArtinCondC κr σ s →
  ∀ (A : PkgI3.AbVar ℂ), A.dim = (g : WithBot ℕ∞) →
  ∀ (𝔞 : AddSubgroup E) (θ : (Fin g → ℂ) → CPts A (RingHom.id ℂ)),
    IsUniformization (RingHom.id ℂ) (cmLat Φ 𝔞) θ → IsOfType Φ 𝔞 θ →
  ∀ (A' : PkgI3.AbVar ℂ) (h : A'.X.left ⟶ A.X.left),
    IsPullback h A'.X.hom A.X.hom (Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ))) →
    (1 : CPts A' (RingHom.id ℂ)).left ≫ h =
      Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (1 : CPts A (RingHom.id ℂ)).left →
  ∃ θ' : (Fin g → ℂ) → CPts A' (RingHom.id ℂ),
    IsUniformization (RingHom.id ℂ)
      (cmLat Φ (latAct ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) :
        (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) 𝔞)) θ' ∧
    ∀ x y : E,
      ((reflexNorm ρ (IdeleGroup.toFiniteIdele (𝓞 Er) Er s) ^ (ε : ℤ) : (AQ ⊗[ℚ] E)ˣ) : AQ ⊗[ℚ] E) *
          (1 ⊗ₜ y) - 1 ⊗ₜ x ∈ latHat 𝔞 →
        (θ' (cmVec Φ y)).left ≫ h = Spec.map (CommRingCat.ofHom (σ : ℂ →+* ℂ)) ≫ (θ (cmVec Φ x)).left

end QMRecPrinted
