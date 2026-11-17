import ZInQKernel.Contrib.OneProof.R16Split
import ZInQKernel.Contrib.OneProof.CharPolyLattice

/-! # charpoly-charp: `r16` from `R16CoreY` with Mumford §19 Thm 4 only over fields that embed into `ℂ`

Task charpoly-charp (2026-11-16), report `docs/research/charpoly-charp.md`.

`R16Split.r16_of_printed` reads the bundle field `charPolyIndepOfEllAlgClosed` only at abelian varieties over `ℚ`
(`R16Split.trace_endV_rat`, `hCP ℚ A e`). This file re-proves `trace_endV_rat`, `rank_two_of_dim` and `r16_of_coreY`
verbatim from `R16Split` with the binder `hCP : PkgI3.CharPolyIndepOfEll` narrowed to degpoly-proof's
`CharPolyLattice.CharPolyIndepOfEllC` (T7 over fields with a ring homomorphism to `ℂ`, proved there from
`uniformizationLeafAll` and `mumfordTorsionAlgClosed`), used at `ℚ` with `Rat.castHom ℂ`, and states
`r16_of_printedC : R16CoreY → UniformizationLeafAll → MumfordTorsionAlgClosed → R16_EichlerShimuraJ1'`.
No `sorry`, no `axiom`. -/

noncomputable section

set_option linter.unusedSectionVars false

namespace R16Split

open Module

section KernelC

open PkgI3 PkgI3.AbVar LeafModCurves
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **T7 at abelian varieties over `ℚ`**: the body of `PkgI3.CharPolyIndepOfEll` at `k = ℚ` (the only field at which
`R16Split.trace_endV_rat` applies it). -/
def CharPolyIndepOfEllAtQ : Prop :=
  ∀ (A : AbVar ℚ) (φ : AbVar.End A), ∃ P : Polynomial ℤ, P.Monic ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : ℚ) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
          P.map (Int.castRingHom ℚ_[ℓ])

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Rational traces (from Mumford §19 Thm 4 over `ℚ`, `CharPolyIndepOfEllC`; copy of `trace_endV_rat`).** Every element of
`End⁰(A)` has rational trace on `V_ℓ(A)`. -/
theorem trace_endV_ratC (hCP : CharPolyIndepOfEllAtQ) (A : AbVar ℚ)
    [Module.Finite ℚ_[ℓ] (A.V ℓ)] (x : A.End0) :
    ∃ r : ℚ, LinearMap.trace ℚ_[ℓ] (A.V ℓ) (endV ℓ A x) = (r : ℚ_[ℓ]) := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul q e =>
    have : Module.Free ℚ_[ℓ] (A.V ℓ) := Module.Free.of_divisionRing ℚ_[ℓ] (A.V ℓ)
    obtain ⟨P, -, hP⟩ := hCP A e
    have h : LinearMap.trace ℚ_[ℓ] (A.V ℓ) ((homT (ℓ := ℓ) e).baseChange ℚ_[ℓ]) =
        ((-P.nextCoeff : ℤ) : ℚ_[ℓ]) := by
      rw [LinearMap.trace_eq_matrix_trace ℚ_[ℓ] (Module.finBasis ℚ_[ℓ] (A.V ℓ)),
        Matrix.trace_eq_neg_charpoly_nextCoeff,
        hP ℓ (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero) _ _,
        Polynomial.nextCoeff_map (Int.castRingHom ℚ_[ℓ]).injective_int]
      simp
    refine ⟨q * ((-P.nextCoeff : ℤ) : ℚ), ?_⟩
    rw [endV_tmul, map_smul, homVAdd_apply, h, smul_eq_mul]
    push_cast; rfl
  | add x y hx hy =>
    obtain ⟨r, hr⟩ := hx
    obtain ⟨r', hr'⟩ := hy
    exact ⟨r + r', by rw [map_add, map_add, hr, hr', Rat.cast_add]⟩

/-- **Glue (proved): the rank-two clause from the dimension clause.** If a number field `F` acts on
`A` through `θ` and `dim A = [F : ℚ]`, then every `ι`-eigenfunctional space of `V_ℓ(A)` has
dimension `2`. Uses `PkgI3.TateModuleFree` and `PkgI3.CharPolyIndepOfEll` (Mumford §19 Thm 4). -/
theorem rank_two_of_dimC (hT : PkgI3.TateModuleFree) (hCP : CharPolyIndepOfEllAtQ)
    (A : AbVar ℚ) {F : Type} [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] (θ : F →+* A.End0)
    (hdim : A.dim = ((Module.finrank ℚ F : ℕ) : WithBot ℕ∞)) (emb : F →+* PadicAlgCl ℓ) :
    Module.finrank (PadicAlgCl ℓ) (eigenFun ℓ A θ emb) = 2 := by
  obtain ⟨hfree, hfin, hrk⟩ := hT ℚ A ℓ (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
  have := hfree; have := hfin
  set P := precompHom (Ω := PadicAlgCl ℓ) (rhoV ℓ A θ) with hPdef
  set d : (F →ₐ[ℚ] PadicAlgCl ℓ) → ℕ := fun κ => Module.finrank (PadicAlgCl ℓ)
    (jointEig P κ.toRingHom) with hd
  -- all weights equal
  have hrat : ∀ a : F, ∃ r : ℚ, ∑ κ : F →ₐ[ℚ] PadicAlgCl ℓ, (d κ : PadicAlgCl ℓ) * κ a =
      (r : PadicAlgCl ℓ) := by
    intro a
    obtain ⟨r, hr⟩ := trace_endV_ratC ℓ hCP A (θ a)
    refine ⟨r, ?_⟩
    rw [← trace_eq_sum_jointEig P a, hPdef, trace_precompHom]
    change algebraMap ℚ_[ℓ] (PadicAlgCl ℓ) (LinearMap.trace ℚ_[ℓ] (A.V ℓ) (endV ℓ A (θ a))) = _
    rw [hr, map_ratCast]
  have heq := weights_eq_of_rational d hrat
  -- the sum of the weights
  have hV : Module.finrank ℚ_[ℓ] (A.V ℓ) = Module.finrank ℤ_[ℓ] (A.T ℓ) :=
    Module.finrank_baseChange
  have hW : Module.finrank (PadicAlgCl ℓ) (A.V ℓ →ₗ[ℚ_[ℓ]] PadicAlgCl ℓ) =
      Module.finrank ℚ_[ℓ] (A.V ℓ) := Module.finrank_linearMap_self _ _ _
  have hs := sum_finrank_jointEig (F := F) (Ω := PadicAlgCl ℓ) P
  rw [hdim] at hrk
  have hT2 : Module.finrank ℤ_[ℓ] (A.T ℓ) = 2 * Module.finrank ℚ F := by
    have h' : (((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * Module.finrank ℚ F : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrk]; push_cast; rfl
    exact Nat.cast_injective (WithBot.coe_injective h')
  let κ := emb.toRatAlgHom
  have hκ : κ.toRingHom = emb := RingHom.toRatAlgHom_toRingHom emb
  have hc : ∑ κ' : F →ₐ[ℚ] PadicAlgCl ℓ, d κ' = ∑ _κ' : F →ₐ[ℚ] PadicAlgCl ℓ, d κ :=
    Finset.sum_congr rfl fun κ' _ => heq κ' κ
  rw [hc, Finset.sum_const, Finset.card_univ, AlgHom.card, smul_eq_mul, hW, hV, hT2] at hs
  have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have h2 : d κ = 2 := by
    have := Nat.eq_of_mul_eq_mul_left hpos (hs.trans (mul_comm _ _))
    exact this
  rw [eigenFun_eq, ← hκ]
  exact h2

end KernelC

section CoreC

open scoped MatrixGroups ModularForm
open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff HasNebentypus IsNormalizedEigenform scaleH
  oldSpace IsNewform)
open LeafModCurves
open WeierstrassCurve AlgebraicGeometry
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar

/-- **R16 from its core without the rank-two clause, `TateModuleFree` and Mumford §19 Thm 4.** -/
theorem r16_of_coreYC (hC : R16CoreY) (hT : PkgI3.TateModuleFree)
    (hCP : CharPolyIndepOfEllAtQ) : LeafModCurves.R16_EichlerShimuraJ1' := by
  intro N χ f J hN hf hJ
  obtain ⟨hfin, A, π, θ, hs, hdim, hgal⟩ := hC N χ f J hN hf hJ
  exact ⟨hfin, A, π, θ, hs, hdim, fun ℓ _ emb =>
    ⟨rank_two_of_dimC ℓ hT hCP A θ hdim emb, hgal ℓ emb⟩⟩

/-- **`r16` from `R16CoreY`, `uniformizationLeafAll` and `mumfordTorsionAlgClosed`** (no
`charPolyIndepOfEllAlgClosed`): as `r16_of_printed`, with T7 at `ℚ` from degpoly-proof's
`CharPolyLattice.charPolyIndepOfEllC`. -/
theorem r16_of_printedC (hC : R16CoreY) (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hM : AvSplit.MumfordTorsionAlgClosed) : LeafModCurves.R16_EichlerShimuraJ1' :=
  r16_of_coreYC hC
    (T5Torsion.TateFree.tateModuleFree_of_torsionStructure (AvSplit.torsionStructure_of_mumford hM))
    (fun A φ => ZInQ.Contrib.OneProof.CharPolyLattice.charPolyIndepOfEllC HL hM ℚ (Rat.castHom ℂ) A φ)

end CoreC

end R16Split
