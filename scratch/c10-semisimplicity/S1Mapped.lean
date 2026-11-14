/-
S1 mapped to the ACTUAL original C10 consumer. Private isolated source, scaled/semisimplicity.

What this file does, and only this:
  * applies the S1 scalar-twist lattice fact (`S1Twist.lean`) to the ORIGINAL objects of
    `GlueC10Link` — `rhoL`, `rL`, `MatrixUnits2.W`, `GlueDescent.rho`, the coefficient map
    `ι₃ : C →+* k₃`, the original `T₃`, `a`, `β` — with the original group `GlueC10.GQ`;
  * takes the Faltings input in its genuine form (`PkgI3.FaltingsSemisimple` on the actual
    `PkgI3.AbVar.galRep`) and the proved #62 coefficient-extension glue
    (`GlueI3.semisimpleBaseChange`);
  * takes the finite-index restriction step (S2, relative Maschke) as an explicitly named
    premise `RelativeMaschke`, because that is a separate writer's task. No averaging argument
    appears in this file.

What this file does NOT do:
  * it does not assume semisimplicity of `rL`, of `ρ₃`, or of anything else that is the goal;
  * it does not assume `μ_σ` is a unit of `B`, nor that any image is finite, nor continuity;
  * it does not edit, weaken or re-state the original consumer `c10_of_squares`, and it does not
    hoist `L`, `A` or `Ψ` out of `hSq` — the single number field, single abelian variety and
    single global comparison `Ψ` enter as EXPLICIT NEW SUPPLIER PREMISES of this helper;
  * it does not prove C10.

Pinned environment: Lean 4.35.0; Mathlib 56a005855ea1 (read-only, prebuilt);
`ZInQKernel.HDecomp.{Objects, Descent.ProjRep, C10.C10, C10.Trace}` oleans of checkout 95b1ff71;
`ZInQKernel.HDecomp.C10.Link` and `ZInQKernel.HDecomp.I3Linalg.C2` compiled privately from the
byte-exact #62 blobs (sha256 0c72f9e5…, 365d409c…). No new dependency.
-/

import S1Twist
import ZInQKernel.HDecomp.C10.Link
import ZInQKernel.HDecomp.I3Linalg.C2

noncomputable section

open GlueDescent GlueC10 GlueC10Link PkgI3
open scoped TensorProduct

namespace ScaledS1Mapped

/-! ## The S2 interface (NOT proved here)

`RelativeMaschke` is the finite-index restriction step: a separate writer's task. It is stated
here only so that the caller binding is explicit. It is a statement about *every* representation,
not about `rL`, so taking it as a premise assumes nothing about the object in question. -/

/-- **S2, relative Maschke (interface only).** -/
def RelativeMaschke : Prop :=
  ∀ (k G V : Type) [Field k] [Group G] [AddCommGroup V] [Module k V]
    (H : Subgroup G) (ρ : Representation k G V),
    ((H.index : k) ≠ 0) →
    Representation.IsSemisimpleRepresentation (ρ.comp H.subtype) →
    ρ.IsSemisimpleRepresentation

/-! ## The mapped statement -/

/-- **`hr` of the original `GlueC10Link.c10_of_squares`, from `PkgI3.FaltingsSemisimple`.**

The new supplier premises are exactly: one number field `L`, one abelian variety `A : AbVar L`,
one group map `jj : Gal(L̄/L) → G_ℚ` of finite index, one **global** `k₃`-linear comparison
`Ψ : V₃ ≃ k₃ ⊗_{ℚ₃} V₃(A)` — the same shape as the `Ψ` inside `FrobSquares`, and intended to be
the same map — and one nowhere-zero scalar `χ` with

  `Ψ ∘ T₃ (jj σ) = χ σ • (ρ_{A,3,k₃}(σ) ∘ Ψ)`   for every `σ ∈ Gal(L̄/L)`,

i.e. on `G_L` the descent operator `T₃ = μ_σ ∘ σ` is the actual Tate–Galois action up to a
nonzero scalar. `χ ≡ 1` is the case `μ_σ = 1` on `G_L`.

Nothing about `a` is assumed: `ι₃ (a g) ≠ 0` is derived from the fact that `rhoL` is a
representation of a group (`ScaledS1.scalar_ne_zero_of_group_rep`). -/
theorem semisimple_rL_of_globalTateComparison
    (hRM : RelativeMaschke)
    (hS : PkgI3.FaltingsSemisimple) (hTF : PkgI3.TateModuleFree)
    {C : Type} [Field C] [CharZero C]
    (c ε : GQ → GQ → C) (a β : GQ → C)
    (ha : ∀ g h, a g * a h * c g h = ε g h * a (g * h))
    (hβ : ∀ g h, β g * β h = ε g h * β (g * h)) (hβ0 : ∀ g, β g ≠ 0)
    (ha1 : a 1 = 1) (hβ1 : β 1 = 1)
    {k₃ V₃ : Type} [Field k₃] [Algebra ℚ_[3] k₃] [CharZero k₃]
    [AddCommGroup V₃] [Module k₃ V₃]
    (ι₃ : C →+* k₃) (T₃ : GQ → Module.End k₃ V₃)
    (hT₃ : ∀ g h, T₃ g * T₃ h = ι₃ (c g h) • T₃ (g * h)) (hT₃1 : T₃ 1 = 1)
    (u₃ : MatrixUnits2 k₃ V₃) (hu₃ : ∀ g i j, Commute (T₃ g) (u₃.e i j))
    {L : Type} [Field L] [NumberField L] (A : PkgI3.AbVar L)
    (jj : Field.absoluteGaloisGroup L →* GQ)
    (hidx : (((MonoidHom.range jj).index : ℕ) : k₃) ≠ 0)
    (Ψ : V₃ ≃ₗ[k₃] TensorProduct ℚ_[3] k₃ (A.V 3))
    (χ : Field.absoluteGaloisGroup L → k₃) (hχ : ∀ σ, χ σ ≠ 0)
    (hΨ : ∀ σ, Ψ.toLinearMap ∘ₗ T₃ (jj σ) =
      χ σ • ((GlueI3.repBaseChange k₃ (A.galRep 3) σ) ∘ₗ Ψ.toLinearMap)) :
    IsSemisimpleModule (MonoidAlgebra k₃ GQ)
      (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule := by
  classical
  set ρ := rhoL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 with hρdef
  -- the carrier may be trivial; that case is semisimple outright
  rcases subsingleton_or_nontrivial V₃ with hss | hnt
  · have hw : Subsingleton (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule := by
      change Subsingleton (u₃.W)
      infer_instance
    have : Subsingleton (Submodule (MonoidAlgebra k₃ GQ)
        (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).asModule) := by
      infer_instance
    exact (isSemisimpleModule_iff _ _).mpr Subsingleton.instComplementedLattice
  -- (0) `V₃(A)` is finite-dimensional over `ℚ₃` (leaf I3.M0, as in C2.lean)
  have h3L : ((3 : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  obtain ⟨-, hfin, -⟩ := hTF L A 3 h3L
  have hFD : FiniteDimensional ℚ_[3] (A.V 3) := inferInstance
  -- (1) Faltings, on the actual `galRep`
  have h1 : (A.galRep 3).IsSemisimpleRepresentation := hS L A 3
  -- (2) coefficient extension (proved #62 glue; characteristic 0, arbitrary extension)
  have h2 : (GlueI3.repBaseChange k₃ (A.galRep 3)).IsSemisimpleRepresentation :=
    GlueI3.semisimpleBaseChange ℚ_[3] k₃ (Field.absoluteGaloisGroup L) (A.V 3) (A.galRep 3) h1
  -- (3) transport along the global comparison `Ψ`
  set τ : Representation k₃ (Field.absoluteGaloisGroup L) V₃ :=
    ScaledS1.transport Ψ (GlueI3.repBaseChange k₃ (A.galRep 3)) with hτ
  have h3 : τ.IsSemisimpleRepresentation := by
    refine GlueI3.isSemisimple_of_surjective (GlueI3.repBaseChange k₃ (A.galRep 3)) τ h2
      Ψ.symm.toLinearMap Ψ.symm.surjective ?_
    intro σ v
    simp [hτ]
  -- (4) the twist: on `G_L`, `ρ ∘ jj` is a nonzero scalar multiple of `τ`
  have hT : ∀ σ, T₃ (jj σ) = χ σ • τ σ := by
    intro σ
    apply LinearMap.ext
    intro v
    apply Ψ.injective
    have h := LinearMap.congr_fun (hΨ σ) v
    simpa [hτ] using h
  have hsmul : ∀ σ, (ρ.comp jj) σ = (((ι₃ (β (jj σ)))⁻¹ * ι₃ (a (jj σ))) * χ σ) • τ σ := by
    intro σ
    show ρ (jj σ) = _
    rw [hρdef, rhoL_apply]
    show ((ι₃ (β (jj σ)))⁻¹ * ι₃ (a (jj σ))) • T₃ (jj σ) = _
    rw [hT σ, smul_smul]
  -- (5) the scalar never vanishes (derived, not assumed)
  have hprod : ∀ g : GQ, ((ι₃ (β g))⁻¹ * ι₃ (a g)) ≠ 0 :=
    ScaledS1.scalar_ne_zero_of_group_rep ρ T₃ (fun g => (ι₃ (β g))⁻¹ * ι₃ (a g)) (fun g => rfl)
  have hs0 : ∀ σ, (((ι₃ (β (jj σ)))⁻¹ * ι₃ (a (jj σ))) * χ σ) ≠ 0 :=
    fun σ => mul_ne_zero (hprod (jj σ)) (hχ σ)
  -- (6) S1
  have h4 : Representation.IsSemisimpleRepresentation (ρ.comp jj) :=
    ScaledS1.isSemisimpleRepresentation_of_smul_twist (ρ.comp jj) τ _ hs0 hsmul h3
  -- (7) move from `jj` to the subgroup `range jj`
  have hcomp : ρ.comp jj = (ρ.comp (MonoidHom.range jj).subtype).comp jj.rangeRestrict := rfl
  have h5 : Representation.IsSemisimpleRepresentation (ρ.comp (MonoidHom.range jj).subtype) :=
    ScaledS1.isSemisimpleRepresentation_of_comp_surjective jj.rangeRestrict
      (MonoidHom.rangeRestrict_surjective jj) (ρ.comp (MonoidHom.range jj).subtype)
      (hcomp ▸ h4)
  -- (8) S2 (separate writer): finite index, index invertible in `k₃` (free from `CharZero k₃`)
  have h6 : ρ.IsSemisimpleRepresentation :=
    hRM k₃ GQ V₃ (MonoidHom.range jj) ρ hidx h5
  -- (9) the matrix-unit projection onto `W = range (e₀₀)`: `rL` is an equivariant image of `ρ`
  have h7 : (rL c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃).IsSemisimpleRepresentation := by
    refine GlueI3.isSemisimple_of_surjective ρ _ h6
      (LinearMap.fst k₃ u₃.W u₃.W ∘ₗ u₃.splitEquiv.toLinearMap) ?_ ?_
    · intro w
      exact ⟨u₃.splitEquiv.symm (w, 0), by simp⟩
    · intro g v
      have := u₃.splitEquiv_intertwines ρ
        (rhoL_commute c ε a β ha hβ hβ0 ha1 hβ1 ι₃ T₃ hT₃ hT₃1 u₃ hu₃) g v
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearMap.fst_apply]
      rw [this]
      rfl
  -- (10) the consumer's `asModule` form
  exact (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp h7

end ScaledS1Mapped
