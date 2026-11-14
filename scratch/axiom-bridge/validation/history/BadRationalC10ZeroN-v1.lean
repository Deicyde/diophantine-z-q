import RationalC10Link

/-
UNCOMPILED PRIVATE NEGATIVE CONTROL: N=0 must not satisfy the original nonzero
N input of the DIVISION/rL link. Preserve all actual original typed descent,
matrix-unit and FrobCompare data. Accept only decide rejecting (0:Nat) != 0,
with no unrelated parser/typeclass/import error. Do not infer that the separate
NONDIVISION N*trace identity rejects N=0.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj TensorProduct
open PkgI3 GlueDescent GlueC10Link
open AxiomBridge.NativeEndTrace

example {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {G C E V : Type} [Group G] [Field C] [CharZero C] [Field E]
    [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (c ε : G → G → C) (a β : G → C)
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (ha1 : a 1 = 1) (hβ1 : β 1 = 1) (emb : C →+* E)
    (T : G → Module.End E V)
    (hT : ∀ g h, T g * T h = emb (c g h) • T (g * h)) (hT1 : T 1 = 1)
    (u : MatrixUnits2 E V) (hu : ∀ g i j, Commute (T g) (u.e i j))
    (σ : G) (hcmp : FrobCompare ℓ (T σ) α 0) :
    LinearMap.trace E u.W
      (rL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ) =
        emb ((β σ)⁻¹ * a σ * ((rationalTrace A α : C) / 0) / 2) :=
  AxiomBridge.RationalC10Link.trace_rL_of_frobCompare A α ℓ hℓ
    c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ 0 (by decide) hcmp
