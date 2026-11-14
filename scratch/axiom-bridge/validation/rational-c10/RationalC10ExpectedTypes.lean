import NativeEndTrace
import ZInQKernel.HDecomp.C10.Link

/-
UNCOMPILED PRIVATE INDEPENDENT SPECIFICATION.

This module does NOT import RationalC10Link or use its declaration metadata.
The three large literal propositions below are derived from the exact OLD
Link source29445B/SHA0c72f9e57e7557aa61dd7c1fc847111f639d7b86105b9939aabb46e1e7e81b55:
remove only (hM : CharPolyIndepOfEll), keep every other binder and conclusion.
The two auxiliary targets follow the new pre-exposure contract1627766522155457.
Compile separately so all specification auxiliaries exist in the fresh environment.
No integer-polynomial result or unprovided arithmetic input is asserted here.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj TensorProduct
open GlueDescent GlueC10 PkgI3 GlueC10Link

namespace RationalC10Checks

/-- Old supplier data; the negation is in Q before any coefficient-field cast. -/
def expectedRationalTrace {k : Type} [Field k] (A : AbVar k)
    (α : AbVar.End A) : ℚ :=
  -(AxiomBridge.NativeEndTrace.rationalCharPoly A α).nextCoeff

def expectedTraceT : Prop :=
  ∀ {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    ∀ {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
      [FiniteDimensional E V] (Tσ : Module.End E V) (N : ℕ),
      FrobCompare ℓ Tσ α N →
        (N : E) * LinearMap.trace E V Tσ = (expectedRationalTrace A α : E)

def expectedTraceRL : Prop :=
  ∀ {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    ∀ {G C E V : Type} [Group G] [Field C] [CharZero C] [Field E]
      [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
      (c ε : G → G → C) (a β : G → C)
      (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
      (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
      (ha1 : a 1 = 1) (hβ1 : β 1 = 1) (emb : C →+* E)
      (T : G → Module.End E V)
      (hT : ∀ g h, T g * T h = emb (c g h) • T (g * h)) (hT1 : T 1 = 1)
      (u : MatrixUnits2 E V) (hu : ∀ g i j, Commute (T g) (u.e i j))
      (σ : G) (N : ℕ), N ≠ 0 → FrobCompare ℓ (T σ) α N →
      LinearMap.trace E u.W
        (rL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ) =
          emb ((β σ)⁻¹ * a σ * ((expectedRationalTrace A α : C) / N) / 2)

def expectedThreeFive : Prop :=
  ∀ (S : Finset ℕ) (h3S : 3 ∈ S)
    (h5S : 5 ∈ S) {G C : Type} [Group G] [Field C] [CharZero C]
    (c ε : G → G → C) (a β : G → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1)
    {k₅ V₅ : Type} [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] (ι₅ : C →+* k₅) (T₅ : G → Module.End k₅ V₅)
    (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h)) (hT₅1 : T₅ 1 = 1)
    (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    {k₃ V₃ : Type} [Field k₃] [Algebra ℚ_[3] k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] (ι₃ : C →+* k₃) (T₃ : G → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (g : G) (p : ℕ) (hp : p.Prime) (hpS : p ∉ S)
    (hFrob : ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (A : AbVar k) (α : AbVar.End A) (N : ℕ),
      N ≠ 0 ∧ FrobCompare 3 (T₃ g) α N ∧ FrobCompare 5 (T₅ g) α N),
    ∃ x : C,
      LinearMap.trace k₃ u₃.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g) = ι₃ x ∧
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) = ι₅ x

def expectedC10TraceLink : Prop :=
  ∀ (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1) (af : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃] [TopologicalSpace k₃]
    [IsTopologicalRing k₃] [T2Space k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃) (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h))
    (hT₃1 : T₃ 1 = 1) (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃) (ρ₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g =>
      LinearMap.toMatrix bV bV (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) ρ₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₃ W₃ (ρ₃ g) = ι₃ (af p))
    (hFrob : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (k : Type) (_ : Field k), CharP k p ∧ ∃ (A : AbVar k) (α : AbVar.End A) (N : ℕ),
        N ≠ 0 ∧ FrobCompare 3 (T₃ g) α N ∧ FrobCompare 5 (T₅ g) α N),
    Nonempty ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
      ρ₃.asModule)

def expectedC10Squares : Prop :=
  ∀ (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C) (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0) (ha1 : a 1 = 1)
    (hβ1 : β 1 = 1) (af : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅) (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h))
    (hT₅1 : T₅ 1 = 1) (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
        LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃] [TopologicalSpace k₃]
    [IsTopologicalRing k₃] [T2Space k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃) (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h))
    (hT₃1 : T₃ 1 = 1) (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃) (ρ₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g =>
      LinearMap.toMatrix bV bV (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) ρ₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p → LinearMap.trace k₃ W₃ (ρ₃ g) = ι₃ (af p))
    (hSq : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
        ∃ (A Aσ : AbVar L) (mu : AbVar.Hom Aσ A) (Ab Ab' : AbVar k) (F : AbVar.Hom Ab Ab')
          (mub : AbVar.Hom Ab' Ab) (N : ℕ), N ≠ 0 ∧
          FrobSquares 3 mu F mub (T₃ g) N ∧ FrobSquares 5 mu F mub (T₅ g) N),
    Nonempty ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
      ρ₃.asModule)

end RationalC10Checks
