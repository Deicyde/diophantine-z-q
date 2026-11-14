import NativeEndTrace
import ZInQKernel.HDecomp.C10.Link

/-
UNCOMPILED PRIVATE CONSUMER ADAPTER.

The exact original C10 trace-link/squares conclusions are retained, with only
CharPolyIndepOfEll removed. The checked RATIONAL trace of the SAME original
endomorphism supplies the scalar needed by this consumer. This does not prove
an integer polynomial or construct any Frobenius/reduction/descent square,
coefficient field, modular trace, continuity or semisimplicity input.

Reuse the original Link's rL/rhoL, trace-halving and squares algebra. No original
Objects, theorem, root/default target, package pin or checker is edited here.
The imported original Link source/destination pairing must be separately bound.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj TensorProduct
open GlueDescent GlueC10 PkgI3 GlueC10Link
open AxiomBridge.NativeEndTrace

namespace AxiomBridge.RationalC10Link

/-- The SAME original endomorphism's rational trace under the actual supplied
Frobenius comparison. Characteristic zero of E comes from its genuine Q_ell
algebra, not an added caller assumption. -/
theorem trace_T_of_frobCompare {k : Type} [Field k] (A : AbVar k)
    (α : AbVar.End A) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {E V : Type} [Field E] [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (Tσ : Module.End E V) (N : ℕ)
    (hcmp : FrobCompare ℓ Tσ α N) :
    (N : E) * LinearMap.trace E V Tσ = (rationalTrace A α : E) := by
  letI : CharZero E :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[ℓ] E).injective
  obtain ⟨Φ, hΦ⟩ := hcmp
  have ht := trace_homT_scalar_extension A α ℓ hℓ E
  change LinearMap.trace E (E ⊗[ℚ_[ℓ]] A.V ℓ) (endE α ℓ E) =
    (rationalTrace A α : E) at ht
  rw [← ht, ← hΦ, LinearMap.trace_conj', map_smul, smul_eq_mul]

/-- Reuse the actual original descended rL and matrix units. The trace is the
image of one rationally defined coefficient, not an integer-trace witness. -/
theorem trace_rL_of_frobCompare {k : Type} [Field k] (A : AbVar k)
    (α : AbVar.End A) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    {G C E V : Type} [Group G] [Field C] [CharZero C] [Field E]
    [Algebra ℚ_[ℓ] E] [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (c ε : G → G → C) (a β : G → C)
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (ha1 : a 1 = 1) (hβ1 : β 1 = 1) (emb : C →+* E)
    (T : G → Module.End E V)
    (hT : ∀ g h, T g * T h = emb (c g h) • T (g * h)) (hT1 : T 1 = 1)
    (u : MatrixUnits2 E V) (hu : ∀ g i j, Commute (T g) (u.e i j))
    (σ : G) (N : ℕ) (hN : N ≠ 0) (hcmp : FrobCompare ℓ (T σ) α N) :
    LinearMap.trace E u.W
      (rL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu σ) =
        emb ((β σ)⁻¹ * a σ * ((rationalTrace A α : C) / N) / 2) := by
  letI : CharZero E := charZero_of_injective_ringHom emb.injective
  have hNT := trace_T_of_frobCompare A α ℓ hℓ (T σ) N hcmp
  have h2 := trace_eq_two_mul_trace_subRep u
    (rhoL c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1)
    (rhoL_commute c ε a β ha hβ hβ0 ha1 hβ1 emb T hT hT1 u hu) σ
  rw [rhoL_apply, trace_rho] at h2
  change LinearMap.trace E u.W (subRep u _ _ σ) = _
  have hNE : (N : E) ≠ 0 := by
    rw [← map_natCast emb]
    exact (map_ne_zero emb).mpr (Nat.cast_ne_zero.mpr hN)
  have h2E : (2 : E) ≠ 0 := by
    rw [← map_ofNat emb 2]
    exact (map_ne_zero emb).mpr two_ne_zero
  rw [map_div₀, map_mul, map_mul, map_inv₀, map_div₀, map_ratCast,
    map_natCast, map_ofNat, ← hNT, mul_div_cancel_left₀ _ hNE, h2,
    mul_div_cancel_left₀ _ h2E]

/-- EXACT original trace_link_three_five conclusion and remaining hypotheses,
with only the integer-polynomial premise removed. Both comparisons still use
one original A, alpha and nonzero N; the original excluded-prime guards remain. -/
theorem trace_link_three_five (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    {G C : Type} [Group G] [Field C] [CharZero C]
    (c ε : G → G → C) (a β : G → C)
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (ha1 : a 1 = 1) (hβ1 : β 1 = 1)
    {k₅ V₅ : Type} [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] (ι₅ : C →+* k₅) (T₅ : G → Module.End k₅ V₅)
    (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h)) (hT₅1 : T₅ 1 = 1)
    (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    {k₃ V₃ : Type} [Field k₃] [Algebra ℚ_[3] k₃] [AddCommGroup V₃] [Module k₃ V₃]
    [FiniteDimensional k₃ V₃] (ι₃ : C →+* k₃) (T₃ : G → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (g : G) (p : ℕ) (hp : p.Prime) (hpS : p ∉ S)
    (hFrob : ∃ (k : Type) (_ : Field k), CharP k p ∧
      ∃ (A : AbVar k) (α : AbVar.End A) (N : ℕ),
        N ≠ 0 ∧ FrobCompare 3 (T₃ g) α N ∧ FrobCompare 5 (T₅ g) α N) :
    ∃ x : C,
      LinearMap.trace k₃ u₃.W
        (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g) = ι₃ x ∧
      LinearMap.trace k₅ u₅.W
        (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) = ι₅ x := by
  obtain ⟨k, hkField, hkChar, A, α, N, hN, h3, h5⟩ := hFrob
  letI : Field k := hkField
  letI : CharP k p := hkChar
  have h3k : ((3 : ℕ) : k) ≠ 0 :=
    cast_ne_zero_of_charP hp Nat.prime_three (fun h => hpS (h ▸ h3S))
  have h5k : ((5 : ℕ) : k) ≠ 0 :=
    cast_ne_zero_of_charP hp (by norm_num) (fun h => hpS (h ▸ h5S))
  refine ⟨(β g)⁻¹ * a g * ((rationalTrace A α : C) / N) / 2, ?_, ?_⟩
  · exact trace_rL_of_frobCompare A α 3 h3k c ε a β ha hβ hβ0 ha1 hβ1
      ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g N hN h3
  · exact trace_rL_of_frobCompare A α 5 h5k c ε a β ha hβ hβ0 ha1 hβ1
      ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g N hN h5

/-- EXACT original c10_of_trace_link conclusion and remaining telescope, with
only hM removed. This still requires the ACTUAL descent/Frobenius/common modular
trace/continuity/semisimplicity inputs, and is not an unconditional C10 result. -/
theorem c10_of_trace_link (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C)
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (ha1 : a 1 = 1) (hβ1 : β 1 = 1) (af : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅)
    (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h)) (hT₅1 : T₅ 1 = 1)
    (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W
        (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
          LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃]
    [TopologicalSpace k₃] [IsTopologicalRing k₃] [T2Space k₃]
    [AddCommGroup V₃] [Module k₃ V₃] [FiniteDimensional k₃ V₃]
    [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃)
    (ρ₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) ρ₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₃ W₃ (ρ₃ g) = ι₃ (af p))
    (hFrob : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (k : Type) (_ : Field k), CharP k p ∧
        ∃ (A : AbVar k) (α : AbVar.End A) (N : ℕ),
          N ≠ 0 ∧ FrobCompare 3 (T₃ g) α N ∧ FrobCompare 5 (T₅ g) α N) :
    Nonempty
      ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
        ρ₃.asModule) := by
  refine GlueC10.c10 hC hBN S C af af k₅ u₅.W W₅ ι₅
    (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅) ρ₅ h₅
    (fun g p hp hpS hg => (h₅ g p hp hpS hg).trans (hρ₅ g p hp hpS hg)) hρ₅
    k₃ u₃.W W₃ ιI κ ι₃ bV bW
    (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃) ρ₃ hrc hρc hr hρ ?_ hρ₃
  intro g p hp hpS hg
  obtain ⟨x, hx₃, hx₅⟩ := trace_link_three_five S h3S h5S c ε a β ha hβ hβ0 ha1 hβ1
    ι₅ T₅ hT₅ hT₅1 u₅ hu₅ ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g p hp hpS (hFrob g p hp hpS hg)
  have hxa : x = af p :=
    ι₅.injective (hx₅.symm.trans ((h₅ g p hp hpS hg).trans (hρ₅ g p hp hpS hg)))
  rw [hx₃, hxa]

/-- EXACT original c10_of_squares conclusion/telescope minus only hM.
The same A, A_sigma, mu, special fibres, F, mu-bar and nonzero N are retained
across3and5. Their squares are hypotheses, not constructed by this adapter. -/
theorem c10_of_squares (hC : ChebotarevExists) (hBN : BrauerNesbittChar0)
    (S : Finset ℕ) (h3S : 3 ∈ S) (h5S : 5 ∈ S)
    (C : Type) [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C)
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (ha1 : a 1 = 1) (hβ1 : β 1 = 1) (af : ℕ → C)
    (k₅ V₅ W₅ : Type) [Field k₅] [Algebra ℚ_[5] k₅] [AddCommGroup V₅] [Module k₅ V₅]
    [FiniteDimensional k₅ V₅] [AddCommGroup W₅] [Module k₅ W₅] (ι₅ : C →+* k₅)
    (T₅ : GQ → Module.End k₅ V₅)
    (hT₅ : ∀ g h, T₅ g * T₅ h = ι₅ (c g h) • T₅ (g * h)) (hT₅1 : T₅ 1 = 1)
    (u₅ : MatrixUnits2 k₅ V₅) (hu₅ : ∀ g i j, Commute (T₅ g) (u₅.e i j))
    (ρ₅ : Representation k₅ GQ W₅)
    (h₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ u₅.W
        (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₅ T₅ hT₅ hT₅1 u₅ hu₅ g) =
          LinearMap.trace k₅ W₅ (ρ₅ g))
    (hρ₅ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₅ W₅ (ρ₅ g) = ι₅ (af p))
    (k₃ V₃ W₃ ιI κ : Type) [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃]
    [TopologicalSpace k₃] [IsTopologicalRing k₃] [T2Space k₃]
    [AddCommGroup V₃] [Module k₃ V₃] [FiniteDimensional k₃ V₃]
    [AddCommGroup W₃] [Module k₃ W₃] [FiniteDimensional k₃ W₃]
    [Fintype ιI] [DecidableEq ιI] [Fintype κ] [DecidableEq κ] (ι₃ : C →+* k₃)
    (T₃ : GQ → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    (bV : Module.Basis ιI k₃ u₃.W) (bW : Module.Basis κ k₃ W₃)
    (ρ₃ : Representation k₃ GQ W₃)
    (hrc : Continuous fun g => LinearMap.toMatrix bV bV
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃ g))
    (hρc : Continuous fun g => LinearMap.toMatrix bW bW (ρ₃ g))
    (hr : IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule)
    (hρ : IsSemisimpleModule (MonoidAlgebra k₃ GQ) ρ₃.asModule)
    (hρ₃ : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace k₃ W₃ (ρ₃ g) = ι₃ (af p))
    (hSq : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      ∃ (L : Type) (_ : Field L) (k : Type) (_ : Field k), CharP k p ∧
        ∃ (A Aσ : AbVar L) (mu : AbVar.Hom Aσ A)
          (Ab Ab' : AbVar k) (F : AbVar.Hom Ab Ab') (mub : AbVar.Hom Ab' Ab) (N : ℕ),
            N ≠ 0 ∧ FrobSquares 3 mu F mub (T₃ g) N ∧ FrobSquares 5 mu F mub (T₅ g) N) :
    Nonempty
      ((rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule ≃ₗ[MonoidAlgebra k₃ GQ]
        ρ₃.asModule) := by
  refine c10_of_trace_link hC hBN S h3S h5S C c ε a β ha hβ hβ0 ha1 hβ1 af
    k₅ V₅ W₅ ι₅ T₅ hT₅ hT₅1 u₅ hu₅ ρ₅ h₅ hρ₅
    k₃ V₃ W₃ ιI κ ι₃ T₃ hT₃ hT₃1 u₃ hu₃ bV bW ρ₃ hrc hρc hr hρ hρ₃ ?_
  intro g p hp hpS hg
  obtain ⟨L, _, k, _, hk, A, Aσ, mu, Ab, Ab', F, mub, N, hN, h3, h5⟩ :=
    hSq g p hp hpS hg
  exact ⟨k, inferInstance, hk, Ab, homComp F mub, N, hN,
    frobCompare_of_frobSquares 3 mu F mub (T₃ g) N h3,
    frobCompare_of_frobSquares 5 mu F mub (T₅ g) N h5⟩

end AxiomBridge.RationalC10Link

#print axioms AxiomBridge.RationalC10Link.trace_T_of_frobCompare
#print axioms AxiomBridge.RationalC10Link.trace_rL_of_frobCompare
#print axioms AxiomBridge.RationalC10Link.trace_link_three_five
#print axioms AxiomBridge.RationalC10Link.c10_of_trace_link
#print axioms AxiomBridge.RationalC10Link.c10_of_squares
