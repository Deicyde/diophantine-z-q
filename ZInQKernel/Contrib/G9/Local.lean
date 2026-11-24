import ZInQKernel.Contrib.G9.Galois
import ZInQKernel.Contrib.G9.OverF
import ZInQKernel.Contrib.G9.I3Layer

/-!
# G9: the local count (Hodge–Tate part, and the de Rham part modulo `ℚ̄_p ⊆ B_dR`)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

pkg-I4's spaces `htSpace`, `htSpaceOver`, `ddrSpace`, `ddrSpaceOver` are the spaces `Dsp` of
`Descent.lean` for the actions `σ ↦ χ(σ)^i · σ` on `ℂ_p` and `σ ↦ σ` on `B_dR`. From R10 over a
finite Galois `F/ℚ_p`, the decomposition `C ⊗ V_p(A) ≅ r|G_F ⊕ r|G_F` (G8's output), the count
`overF_count` and the descent `descent_finrank` give the conclusions of N5's Lemma
`lem:de-rham-descent` at `K = ℚ_p`.

Main results here:
* `htMult_eq_one_of_R10` (G9, Hodge–Tate part): `htMult p r 0 = 1` and `htMult p r (-1) = 1`.
* `isDeRham_of_R10_of_emb` (G9, de Rham part) under two hypotheses on `B_dR` that are proved in
  `BdREmb.lean`: `bdrAct` is multiplicative, and `F' ⊆ ℚ̄_p` embeds `G_{ℚ_p}`-equivariantly in
  `B_dR`.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 Module
open scoped TensorProduct

noncomputable section

/-! `GlueI3.repBaseChange` (Leaves.lean, section `PkgI3Sec`) comes from `I3Layer.lean`, the
verbatim restatement of that section. -/

/-! ### A divisibility lemma -/

/-- If `ι : L → B` commutes with the action of `S`, then `Dsp act ρ S` is an `L`-space, so its
`K`-dimension is divisible by `[L:K]`. -/
theorem finrank_dvd_Dsp_of_emb {K G B V L : Type*} [Field K] [Group G] [CommRing B] [Algebra K B]
    [AddCommGroup V] [Module K V] [Field L] [Algebra K L]
    (act : G → B →ₗ[K] B) (ρ : G → V →ₗ[K] V) (S : Set G) (ι : L →ₐ[K] B)
    (hlin : ∀ g ∈ S, ∀ x b, act g (ι x * b) = ι x * act g b) :
    finrank K L ∣ finrank K (Dsp act ρ S) := by
  let _ : Algebra L B := ι.toRingHom.toAlgebra
  have : IsScalarTower K L B := IsScalarTower.of_algebraMap_eq (fun k => (ι.commutes k).symm)
  have hLsmul : ∀ (x : L) (b : B), x • b = ι x * b := fun _ _ => rfl
  let DL : Submodule L (V →ₗ[K] B) :=
    { carrier := {φ | φ ∈ Dsp act ρ S}
      zero_mem' := (Dsp act ρ _).zero_mem
      add_mem' := fun ha hb => (Dsp act ρ _).add_mem ha hb
      smul_mem' := by
        intro x φ hφ g hg v
        simp only [Set.mem_ofPred_eq] at hφ
        simp only [LinearMap.smul_apply, hLsmul, hφ g hg v, hlin g hg] }
  have hDL : DL.restrictScalars K = Dsp act ρ S := Submodule.ext fun _ => Iff.rfl
  have e2 : finrank K DL = finrank K (Dsp act ρ S) := by rw [← hDL]; rfl
  have : Module.Free L DL := Module.Free.of_divisionRing L DL
  rw [← e2, ← Module.finrank_mul_finrank K L DL]
  exact dvd_mul_right _ _

section Actions

variable (p : ℕ) [Fact p.Prime]

theorem cpAct_mul (σ τ : GQp p) (x : ℂ_[p]) : cpAct p (σ * τ) x = cpAct p σ (cpAct p τ x) := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _)
      ((continuous_cpAct p σ).comp (continuous_cpAct p τ))
  | ih a => rw [cpAct_coe, cpAct_coe, cpAct_coe]; rfl

theorem cpAct_one (x : ℂ_[p]) : cpAct p 1 x = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (continuous_cpAct p _) continuous_id
  | ih a => rw [cpAct_coe]; rfl

theorem cpAct_smul (σ : GQp p) (c : ℚ_[p]) (x : ℂ_[p]) : cpAct p σ (c • x) = c • cpAct p σ x := by
  rw [Algebra.smul_def, map_mul, cpAct_algebraMap, ← Algebra.smul_def]

theorem cyc_mul (σ τ : GQp p) : cyc p (σ * τ) = cyc p σ * cyc p τ := by
  simp only [cyc]
  rw [← map_mul]
  rfl

theorem cyc_one : cyc p 1 = 1 := by
  simp only [cyc]
  rw [← map_one (cyclotomicCharacter (PadicAlgCl p) p)]
  rfl

theorem cycPow_mul (σ τ : GQp p) (i : ℤ) :
    cycPow p (σ * τ) i = cycPow p σ i * cycPow p τ i := by
  simp only [cycPow, cyc_mul, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem cycPow_one (i : ℤ) : cycPow p 1 i = 1 := by
  simp [cycPow, cyc_one]

/-- `x ↦ χ(σ)^i · σ(x)` on `ℂ_p`, `ℚ_p`-linear. -/
def cpActL (i : ℤ) (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun x := cycPow p σ i • cpAct p σ x
  map_add' x y := by rw [map_add, smul_add]
  map_smul' c x := by
    rw [cpAct_smul, smul_comm]
    rfl

theorem cpActL_apply (i : ℤ) (σ : GQp p) (x : ℂ_[p]) :
    cpActL p i σ x = cycPow p σ i • cpAct p σ x := rfl

/-- The twisted action `σ ↦ χ(σ)^i · σ` as a representation on `ℂ_p`. -/
def cpActHom (i : ℤ) : GQp p →* (ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p]) where
  toFun := cpActL p i
  map_one' := by
    refine LinearMap.ext fun x => ?_
    rw [cpActL_apply, cpAct_one, cycPow_one, one_smul]
    rfl
  map_mul' σ τ := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, cpActL_apply, cpActL_apply, cpActL_apply, cpAct_mul, cpAct_smul,
      cycPow_mul, mul_smul]

variable {C : Type*} [Field C] [Algebra ℚ_[p] C] {n : ℕ}

/-- `r : G_{ℚ_p} → GL_n(C)` as a `ℚ_p`-linear representation on `Cⁿ`. -/
def rRep (r : GQp p →* GL (Fin n) C) : Representation ℚ_[p] (GQp p) (Fin n → C) where
  toFun σ := (Matrix.mulVecLin (r σ : Matrix (Fin n) (Fin n) C)).restrictScalars ℚ_[p]
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' σ τ := by
    refine LinearMap.ext fun v => ?_
    simp [Matrix.mulVec_mulVec]

theorem rRep_apply (r : GQp p →* GL (Fin n) C) (σ : GQp p) (v : Fin n → C) :
    rRep p r σ v = Matrix.mulVec (r σ : Matrix (Fin n) (Fin n) C) v := rfl

variable [FiniteDimensional ℚ_[p] C]

theorem htSpace_eq_DspAct (r : GQp p →* GL (Fin n) C) (i : ℤ) :
    htSpace p r i = Dsp (cpActHom p i) (rRep p r) Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

theorem htSpaceOver_eq_DspAct (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    htSpaceOver p ρ i = Dsp ((cpActHom p i).comp (gfToGqp p F)) ρ Set.univ := by
  ext φ
  exact ⟨fun h g _ v => h g v, fun h g v => h g trivial v⟩

/-- `Dsp` over the kernel of `G_{ℚ_p} → Gal(F'/ℚ_p)` is `Dsp` over `G_F`. -/
theorem Dsp_ker_gammaF (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] {B W : Type*} [AddCommGroup B] [Module ℚ_[p] B] [AddCommGroup W]
    [Module ℚ_[p] W] (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ρ : Representation ℚ_[p] (GQp p) W) :
    Dsp act ρ ((gammaF p F).ker : Set (GQp p)) =
      Dsp (act.comp (gfToGqp p F)) (ρ.comp (gfToGqp p F)) Set.univ := by
  ext φ
  rw [← range_gfToGqp]
  constructor
  · intro h σ _ v
    exact h _ ⟨σ, rfl⟩ v
  · rintro h _ ⟨σ, rfl⟩ v
    exact h σ trivial v

/-- `F' → ℂ_p`. -/
def iotaCp (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] :
    fieldF p F →ₐ[ℚ_[p]] ℂ_[p] :=
  (IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).comp (fieldF p F).val

theorem cpAct_iotaCp (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] (σ : GQp p) (x : fieldF p F) :
    cpAct p σ (iotaCp p F x) = iotaCp p F (gammaF p F σ x) := by
  simp only [iotaCp, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
  rw [← PadicComplex.coe_eq, ← PadicComplex.coe_eq, cpAct_coe]
  congr 1
  exact (gammaF_apply_coe p F σ x).symm

theorem cpActHom_semi (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] (i : ℤ) (σ : GQp p) (x : fieldF p F) (b : ℂ_[p]) :
    cpActHom p i σ (iotaCp p F x * b) = iotaCp p F (gammaF p F σ x) * cpActHom p i σ b := by
  change cpActL p i σ _ = _ * cpActL p i σ b
  rw [cpActL_apply, cpActL_apply, map_mul, cpAct_iotaCp, mul_smul_comm]

end Actions

/-! ### G9, Hodge–Tate part -/

section HT

variable (p : ℕ) [Fact p.Prime]

/-- From the counts: if `dim Dsp_{G_F}(V) = 2[F:ℚ_p]·m`-type data hold, conclude. The core
arithmetic of both parts: `c · d_V = 2 · d_U`, `d_U = [F:ℚ_p] · d_G` give `d_G`. -/
theorem descended_finrank (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    [IsGalois ℚ_[p] F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
    (ρV : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] V ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C ρV σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2))
    {B : Type*} [CommRing B] [Algebra ℚ_[p] B] (act : GQp p →* (B →ₗ[ℚ_[p]] B))
    (ι : fieldF p F →ₐ[ℚ_[p]] B)
    (hsemi : ∀ σ x b, act σ (ι x * b) = ι (gammaF p F σ x) * act σ b)
    (hpos : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) ρV Set.univ)) :
    finrank ℚ_[p] C * finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) ρV Set.univ) =
      2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ)) := by
  have hcount := overF_count (act.comp (gfToGqp p F)) (C := C) (fun σ => ρV σ)
    (fun σ => rRep p r (gfToGqp p F σ)) Set.univ e (fun σ x => he σ x) hpos
  have hdes := descent_finrank act (rRep p r) ι (gammaF p F) (gammaF_surjective p F) hsemi
  rw [Dsp_ker_gammaF, finrank_fieldF] at hdes
  rw [hcount, ← hdes]
  rfl

/-- **G9, Hodge–Tate part.** Hypotheses: R10 (`PkgI4.DeRhamComparison`) and G8's output localized
at `p`: a finite Galois `F/ℚ_p`, an abelian surface `A/F`, a finite `C/ℚ_p`,
`r : G_{ℚ_p} → GL₂(C)` and a `C`-linear `G_F`-equivariant `C ⊗ V_p(A) ≅ r|G_F ⊕ r|G_F`.
Conclusion: `r` has Hodge–Tate multiplicity `1` at the weights `0` and `−1`. -/
theorem htMult_eq_one_of_R10 (hR10 : DeRhamComparison) (F : Type) [Field F] [Algebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    htMult p r 0 = 1 ∧ htMult p r (-1) = 1 := by
  obtain ⟨-, h0, h1⟩ := hR10 p F A 2 hA
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hC : 0 < finrank ℚ_[p] C := Module.finrank_pos
  -- the common computation, for `i = -w`
  have key : ∀ w : ℤ, htMultOver p (A.galRep p) w = 2 → htMult p r w = 1 := by
    intro w hw
    set i := -w
    set act := cpActHom p i
    set nV := finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ)
    have hnV : finrank ℚ_[p] (htSpaceOver p (A.galRep p) i) = nV := by
      rw [htSpaceOver_eq_DspAct]
    have hdvd : finrank ℚ_[p] F ∣ nV := by
      have := finrank_dvd_Dsp_of_emb (act.comp (gfToGqp p F)) (fun σ => A.galRep p σ) Set.univ
        (iotaCp p F) (fun σ _ x b => by
          have hk : gfToGqp p F σ ∈ (gammaF p F).ker := by
            rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
          rw [MonoidHom.mem_ker] at hk
          change act (gfToGqp p F σ) _ = _
          rw [cpActHom_semi, hk]
          rfl)
      rwa [finrank_fieldF] at this
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : k = 2 := by
      have : htMultOver p (A.galRep p) w = k := by
        rw [htMultOver, hnV, hk, Nat.mul_div_cancel_left _ hF]
      rw [← this, hw]
    have hpos : 0 < nV := by rw [hk, hk2]; positivity
    have hd : finrank ℚ_[p] C * nV =
        2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ)) :=
      descended_finrank p F (A.galRep p) C r e he act (iotaCp p F) (cpActHom_semi p F i) hpos
    rw [hk, hk2] at hd
    have hG : finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) = finrank ℚ_[p] C := by
      have : finrank ℚ_[p] F * 2 * finrank ℚ_[p] C =
          finrank ℚ_[p] F * 2 * finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
        linarith [hd]
      exact (Nat.eq_of_mul_eq_mul_left (by positivity) this).symm
    rw [htMult, htSpace_eq_DspAct, hG, Nat.div_self hC]
  exact ⟨key 0 h0, key (-1) h1⟩

end HT

end

end ZInQ.Contrib.G9
