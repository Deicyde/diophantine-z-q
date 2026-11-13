import ZInQKernel.Contrib.G9.BdREmb

/-!
# G9: N5's appendix lemma — `r` is de Rham with Hodge–Tate weights `0, −1`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Glue step G9 of `docs/research/h-decomposition.md` (N5, Lemma `lem:de-rham-descent`,
`diophantine_zq.tex` L10939-11000), at `K = ℚ_p` with `F/ℚ_p` finite Galois (the case N5 uses:
`docs/research/h-trust.md` C3, "Galois choice of the field").

**`g9_deRham`.** Hypotheses: the leaf R10 (`PkgI4.DeRhamComparison`, restated verbatim in
`I4Layer.lean`) and G8's output localized at `p`: a finite Galois `F/ℚ_p`, an abelian surface
`A/F` (pkg-I3/I4's `AbVar`, `dim A = 2`), a finite `C/ℚ_p`, `r : G_{ℚ_p} → GL₂(C)` and a
`C`-linear isomorphism `e : C ⊗_{ℚ_p} V_p(A) ≅ C² × C²` intertwining `G_F` (acting through
pkg-I4's `gfToGqp`) with `r|G_F ⊕ r|G_F` (the form of G8's output in
`PkgI3.C2_absolutelyIrreducible`). Conclusion: `IsDeRham p r`, `htMult p r 0 = 1` and
`htMult p r (−1) = 1`.

T23 (Fontaine's closure properties) and T10 (Tate duality, an `opaque` placeholder) are not
used: R10's Lean form is already about `V_p(A)`, the subquotient step is a dimension count
(`overF_count`), and the finite descent is Speiser's lemma through `ℚ̄_p ⊆ B_dR^+`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 Module Ideal
open scoped TensorProduct

noncomputable section

section Emb

variable (p : ℕ) [Fact p.Prime]

/-- `B_dR^+` as a `ℚ_p`-algebra through pkg-I4's `ℚ_p ⊆ B_dR^+` (`ofLoc ∘ qpToLoc`). -/
@[instance_reducible] def algPlus : Algebra ℚ_[p] (BDeRhamPlus 𝓞_ℂ_[p] p) := (qpToPlus p).toAlgebra

attribute [local instance] algPlus

/-- `θ⁺ : B_dR^+ → ℂ_p` as a `ℚ_p`-algebra map. -/
def thetaAlg : BDeRhamPlus 𝓞_ℂ_[p] p →ₐ[ℚ_[p]] ℂ_[p] :=
  { BdrKer.Cp.thetaPlusCp p with commutes' := fun c => thetaPlusCp_qpToPlus p c }

theorem thetaAlg_apply (y : BDeRhamPlus 𝓞_ℂ_[p] p) :
    thetaAlg p y = BdrKer.Cp.thetaPlusCp p y := rfl

/-- `σ` acting on `B_dR^+`, as a `ℚ_p`-algebra map. -/
def sPlus (σ : GQp p) : BDeRhamPlus 𝓞_ℂ_[p] p →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p :=
  { DR.bdrPlusMap p (oAct p σ) with commutes' := fun c => bdrPlusMap_qpToPlus p σ c }

theorem ker_thetaAlg : RingHom.ker (thetaAlg p).toRingHom =
    span {BdrKer.ofPlus _ p (BdrKer.Cp.xi' p)} := BdrKer.Cp.ker_thetaPlusCp p

instance henselian_thetaAlg :
    HenselianRing (BDeRhamPlus 𝓞_ℂ_[p] p) (RingHom.ker (thetaAlg p).toRingHom) := by
  rw [ker_thetaAlg]
  infer_instance

theorem isUnit_of_thetaAlg_ne_zero (y : BDeRhamPlus 𝓞_ℂ_[p] p) (hy : thetaAlg p y ≠ 0) :
    IsUnit y := by
  by_contra hnu
  have hm : y ∈ IsLocalRing.maximalIdeal (BDeRhamPlus 𝓞_ℂ_[p] p) := hnu
  rw [BdrKer.Cp.maximalIdeal_BDeRhamPlus, ← BdrKer.Cp.ker_thetaPlusCp] at hm
  exact hy (RingHom.mem_ker.mp hm)

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]

theorem exists_iotaPlus : ∃ ι₀ : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p,
    ∀ x, thetaAlg p (ι₀ x) = iotaCp p F x :=
  exists_hensel_lift (thetaAlg p) (BdrKer.Cp.thetaPlusCp_surjective p)
    (isUnit_of_thetaAlg_ne_zero p) (iotaCp p F)

/-- **`F' ⊆ B_dR^+`**: the Hensel lift of `F' ⊆ ℚ̄_p ⊆ ℂ_p` through `θ⁺`. -/
def iotaPlus : fieldF p F →ₐ[ℚ_[p]] BDeRhamPlus 𝓞_ℂ_[p] p := (exists_iotaPlus p F).choose

theorem thetaAlg_iotaPlus (x : fieldF p F) : thetaAlg p (iotaPlus p F x) = iotaCp p F x :=
  (exists_iotaPlus p F).choose_spec x

theorem bdrPlusMap_iotaPlus (σ : GQp p) (x : fieldF p F) :
    DR.bdrPlusMap p (oAct p σ) (iotaPlus p F x) = iotaPlus p F (gammaF p F σ x) :=
  hensel_lift_natural (thetaAlg p) (iotaCp p F) (iotaPlus p F) (thetaAlg_iotaPlus p F)
    (sPlus p σ) (gammaF p F σ : fieldF p F ≃ₐ[ℚ_[p]] fieldF p F).toAlgHom (fun y => by
      change BdrKer.Cp.thetaPlusCp p (DR.bdrPlusMap p (oAct p σ) (iotaPlus p F y)) = _
      rw [thetaPlusCp_bdrPlusMap, ← thetaAlg_apply, thetaAlg_iotaPlus, cpAct_iotaCp]
      rfl) x

/-- **`F' ⊆ B_dR`**, a `ℚ_p`-algebra map for pkg-I4's `ℚ_p ⊆ B_dR`. -/
def iotaDR : fieldF p F →ₐ[ℚ_[p]] BdR p :=
  { (algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p)).comp (iotaPlus p F).toRingHom with
    commutes' := fun c => by
      change algebraMap _ (BdR p) (iotaPlus p F (algebraMap ℚ_[p] _ c)) = qpToBdR p c
      rw [AlgHom.commutes]
      rfl }

theorem iotaDR_apply (x : fieldF p F) :
    iotaDR p F x = algebraMap (BDeRhamPlus 𝓞_ℂ_[p] p) (BdR p) (iotaPlus p F x) := rfl

/-- **Equivariance**: `σ(ι x) = ι(σ x)` in `B_dR`. -/
theorem bdrAct_iotaDR (σ : GQp p) (x : fieldF p F) :
    bdrAct p σ (iotaDR p F x) = iotaDR p F (gammaF p F σ x) := by
  rw [iotaDR_apply, iotaDR_apply, bdrAct, DR.bdrMap, IsLocalization.map_eq, bdrPlusMap_iotaPlus]

theorem bdrActHom_semi (σ : GQp p) (x : fieldF p F) (b : BdR p) :
    bdrActHom p σ (iotaDR p F x * b) = iotaDR p F (gammaF p F σ x) * bdrActHom p σ b := by
  rw [bdrActHom_apply, bdrActHom_apply, map_mul, bdrAct_iotaDR]

end Emb

section DeRham

variable (p : ℕ) [Fact p.Prime]

theorem ddrSpace_eq_Dsp {C : Type*} [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    {n : ℕ} (r : GQp p →* GL (Fin n) C) :
    ddrSpace p r = Dsp (bdrActHom p) (rRep p r) Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

theorem ddrSpaceOver_eq_Dsp (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    ddrSpaceOver p ρ = Dsp ((bdrActHom p).comp (gfToGqp p F)) ρ Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

/-- **G9, de Rham part.** Same hypotheses as `htMult_eq_one_of_R10`; conclusion `IsDeRham p r`. -/
theorem isDeRham_of_R10 (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r := by
  obtain ⟨hdr, -, -⟩ := hR10 p F A 2 hA
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hC : 0 < finrank ℚ_[p] C := Module.finrank_pos
  have hV : finrank ℚ_[p] (A.V p) = 4 := by
    have h := e.finrank_eq
    rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h
    exact h
  set act := bdrActHom p
  have hnV : finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ) =
      finrank ℚ_[p] F * 4 := by
    rw [← ddrSpaceOver_eq_Dsp, ← hV]
    exact hdr
  have hpos : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ) := by
    rw [hnV]; positivity
  have hd := descended_finrank p F (A.galRep p) C r e he act (iotaDR p F)
    (bdrActHom_semi p F) hpos
  rw [hnV] at hd
  rw [IsDeRham, ddrSpace_eq_Dsp]
  have : finrank ℚ_[p] F * 2 * (2 * finrank ℚ_[p] C) =
      finrank ℚ_[p] F * 2 * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
    linarith [hd]
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm

/-- **G9 (N5's appendix lemma at `K = ℚ_p`, `F/ℚ_p` Galois).** From the leaf R10 and G8's output
localized at `p`: `r` is de Rham, with Hodge–Tate multiplicity `1` at the weights `0` and `−1`. -/
theorem g9_deRham (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r ∧ htMult p r 0 = 1 ∧ htMult p r (-1) = 1 :=
  ⟨isDeRham_of_R10 p hR10 F A hA C r e he, htMult_eq_one_of_R10 p hR10 F A hA C r e he⟩

/-- **G9 in the `ℚ̄_p`-valued form used by `PanBerger`** (`LocalIsDeRham`): if the coefficient
field is a finite `E ⊆ ℚ̄_p` and `ρ` is `r` viewed in `GL₂(ℚ̄_p)`, then `ρ` is de Rham. -/
theorem g9_localIsDeRham (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (r : GQp p →* GL (Fin 2) E) (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p))
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (r σ) = ρ σ)
    (e : E ⊗[ℚ_[p]] A.V p ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ v, e (GlueI3.repBaseChange E (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).2)) :
    LocalIsDeRham p 2 ρ :=
  ⟨E, inferInstance, r, hρ, isDeRham_of_R10 p hR10 F A hA E r e he⟩

end DeRham

end

end ZInQ.Contrib.G9
