import ZInQKernel.Contrib.G9.Galois
import ZInQKernel.Contrib.G9.OverF
import ZInQKernel.Contrib.G9.BdRAct

/-!
# G9, the local core: descent of de Rham and Hodge–Tate data from `F` to `ℚ_p`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

Setting of N5's Lemma `lem:de-rham-descent` after the choice of the local field (h-trust C3,
Galois choice): `F/ℚ_p` finite Galois, `V` a `ℚ_p`-linear representation of `G_F`,
`E ⊆ ℚ̄_p` a finite coefficient field, `ρE : G_{ℚ_p} → GL₂(E)`, and an `E`-linear
`E ⊗_{ℚ_p} V ≅ E² × E²` intertwining `V|G_F` with `ρE|G_F ⊕ ρE|G_F`.

* `core_ht`: if `V` has Hodge–Tate multiplicities (over `F`, pkg-I4's `htMultOver`) `2` at `0`,
  `2` at `−1` and `0` elsewhere, then `ρE` has Hodge–Tate weights `{0, −1}` (pkg-I4's
  `HasHTWeights`).
* `core_dR`: if `V` is de Rham over `F` (pkg-I4's `IsDeRhamOver`) and `ℚ̄_p` embeds
  `G_{ℚ_p}`-equivariantly into `B_dR` (Fontaine; here a hypothesis), then `ρE` is de Rham
  (pkg-I4's `IsDeRham`).

Proof: count dimensions of spaces of equivariant maps through `E ⊗ V ≅ U ⊕ U`
(`overF_count_gen`), then descend from `G_F` to `G_{ℚ_p}` (`descent_finrank`, Speiser's lemma),
using `F' ⊆ ℚ̄_p ⊆ ℂ_p` (resp. `⊆ B_dR`); divisibility of `dim_{ℚ_p}` by `[F:ℚ_p]` comes from
the `F'`-structure. No closure property of de Rham representations (T23) is used.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 Module
open scoped TensorProduct

noncomputable section

/-! ### Counting through `C ⊗ V ≅ U × U`, without finiteness hypotheses -/

section Count

variable {K : Type*} [Field K] {G : Type*} [Group G] {B : Type*} [AddCommGroup B] [Module K B]
  (act : G → B →ₗ[K] B)

theorem map_arrowCongr_Dsp {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    (Dsp act ρ S).map ((LinearEquiv.arrowCongr e (LinearEquiv.refl K B) :
      (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B)) : (V →ₗ[K] B) →ₗ[K] (V' →ₗ[K] B)) = Dsp act ρ' S := by
  set L : (V →ₗ[K] B) ≃ₗ[K] (V' →ₗ[K] B) := LinearEquiv.arrowCongr e (LinearEquiv.refl K B)
  have hL : ∀ φ v', L φ v' = φ (e.symm v') := fun _ _ => rfl
  have hL' : ∀ φ' v, L.symm φ' v = φ' (e v) := fun _ _ => rfl
  ext φ'
  constructor
  · rintro ⟨φ, hφ, rfl⟩ g hg v'
    have h1 : e.symm (ρ' g v') = ρ g (e.symm v') := by
      apply e.injective
      rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    change L φ (ρ' g v') = act g (L φ v')
    rw [hL, hL, h1, hφ g hg]
  · intro hφ'
    refine ⟨L.symm φ', ?_, by simp⟩
    intro g hg v
    rw [hL', hL', he, hφ' g hg]

/-- An equivariant isomorphism `V ≅ V'` gives `Dsp(V) ≅ Dsp(V')`. -/
def dspCongr {V V' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] (ρ : G → V →ₗ[K] V) (ρ' : G → V' →ₗ[K] V') (S : Set G) (e : V ≃ₗ[K] V')
    (he : ∀ g v, e (ρ g v) = ρ' g (e v)) : Dsp act ρ S ≃ₗ[K] Dsp act ρ' S :=
  ((LinearEquiv.arrowCongr e (LinearEquiv.refl K B)).submoduleMap (Dsp act ρ S)).trans
    (LinearEquiv.ofEq _ _ (map_arrowCongr_Dsp act ρ ρ' S e he))

/-- `Dsp(V^ι) ≅ Dsp(V)^ι`. -/
def dspPi {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V)
    (S : Set G) (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Dsp act (piRep ρ ι) S ≃ₗ[K] (ι → Dsp act ρ S) :=
  have hsingle : ∀ g i (v : V), piRep ρ ι g (Pi.single i v) = Pi.single i (ρ g v) := by
    intro g i v
    funext j
    rw [piRep_apply]
    by_cases hij : j = i
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  { toFun := fun φ i => ⟨(φ : (ι → V) →ₗ[K] B) ∘ₗ LinearMap.single K (fun _ => V) i, by
        intro g hg v
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
        rw [← hsingle, φ.2 g hg]⟩
    map_add' := fun φ ψ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    map_smul' := fun c φ => by funext i; apply Subtype.ext; exact LinearMap.ext fun v => rfl
    invFun := fun ψ => ⟨∑ i, ((ψ i : Dsp act ρ S) : V →ₗ[K] B) ∘ₗ LinearMap.proj i, by
        intro g hg v
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [piRep_apply, (ψ i).2 g hg]⟩
    left_inv := fun φ => by
        apply Subtype.ext
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
          LinearMap.single_apply]
        rw [← map_sum, Finset.univ_sum_single v]
    right_inv := fun ψ => by
        funext i
        apply Subtype.ext
        refine LinearMap.ext fun v => ?_
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
          LinearMap.single_apply]
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji, map_zero]
        · intro h; exact absurd (Finset.mem_univ i) h }

/-- `Dsp(U × U) ≅ Dsp(U) × Dsp(U)`. -/
def dspProd {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G) :
    Dsp act (fun g => (ρ g).prodMap (ρ g)) S ≃ₗ[K] (Dsp act ρ S × Dsp act ρ S) :=
  { toFun := fun φ => (⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inl K V V, by
        intro g hg v
        have := φ.2 g hg (v, 0)
        simpa using this⟩,
      ⟨(φ : V × V →ₗ[K] B) ∘ₗ LinearMap.inr K V V, by
        intro g hg v
        have := φ.2 g hg (0, v)
        simpa using this⟩)
    map_add' := fun φ ψ => by ext <;> simp
    map_smul' := fun c φ => by ext <;> simp
    invFun := fun ψ => ⟨(ψ.1 : V →ₗ[K] B).coprod (ψ.2 : V →ₗ[K] B), by
      intro g hg v
      simp only [LinearMap.coprod_apply, LinearMap.prodMap_apply, map_add]
      rw [ψ.1.2 g hg, ψ.2.2 g hg]⟩
    left_inv := fun φ => by
      apply Subtype.ext
      ext v <;> simp
    right_inv := fun ψ => by
      ext v <;> simp }

/-- `d · dim X = 2 · dim Y` from `X^d ≅ Y × Y` (`d > 0`), finite-dimensional or not. -/
theorem finrank_of_pi_equiv_prod {X Y : Type*} [AddCommGroup X] [Module K X] [AddCommGroup Y]
    [Module K Y] (d : ℕ) (hd : 0 < d) (Φ : (Fin d → X) ≃ₗ[K] Y × Y) :
    d * finrank K X = 2 * finrank K Y := by
  by_cases hX : FiniteDimensional K X
  · have h1 : FiniteDimensional K (Y × Y) := LinearEquiv.finiteDimensional Φ
    have h2 : FiniteDimensional K Y :=
      Module.Finite.of_surjective (LinearMap.fst K Y Y) LinearMap.fst_surjective
    have := Φ.finrank_eq
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, Module.finrank_prod] at this
    omega
  · have hY : ¬ FiniteDimensional K Y := by
      intro hY
      have h1 : FiniteDimensional K (Y × Y) := inferInstance
      have h2 : FiniteDimensional K (Fin d → X) := LinearEquiv.finiteDimensional Φ.symm
      exact hX (Module.Finite.of_surjective (LinearMap.proj (R := K) (φ := fun _ : Fin d => X)
        ⟨0, hd⟩) (fun x => ⟨fun _ => x, rfl⟩))
    rw [Module.finrank_of_not_finite hX, Module.finrank_of_not_finite hY]
    simp

/-- **Counting through `C ⊗_K V ≅ U × U`** (no finiteness hypothesis). -/
theorem overF_count_gen {C : Type*} [Field C] [Algebra K C] [FiniteDimensional K C]
    {V U : Type*} [AddCommGroup V] [Module K V] [AddCommGroup U] [Module C U] [Module K U]
    [IsScalarTower K C U]
    (ρV : G → V →ₗ[K] V) (ρU : G → U →ₗ[K] U) (S : Set G)
    (e : C ⊗[K] V ≃ₗ[C] U × U)
    (he : ∀ g x, e ((ρV g).baseChange C x) = ((ρU g).prodMap (ρU g)) (e x)) :
    finrank K C * finrank K (Dsp act ρV S) = 2 * finrank K (Dsp act ρU S) := by
  classical
  let bC := Module.finBasis K C
  let ρCV : G → (C ⊗[K] V) →ₗ[K] (C ⊗[K] V) := fun g => ((ρV g).baseChange C).restrictScalars K
  let Φ1 : Dsp act ρCV S ≃ₗ[K] Dsp act (piRep ρV (Fin (finrank K C))) S :=
    dspCongr act ρCV _ S (tensorPiEquiv bC) (fun g x => tensorPiEquiv_baseChange bC (ρV g) x)
  let Φ2 : Dsp act ρCV S ≃ₗ[K] Dsp act (fun g => (ρU g).prodMap (ρU g)) S :=
    dspCongr act ρCV _ S (e.restrictScalars K) (fun g x => he g x)
  let Φ : (Fin (finrank K C) → Dsp act ρV S) ≃ₗ[K] Dsp act ρU S × Dsp act ρU S :=
    ((dspPi act ρV S (Fin (finrank K C))).symm.trans Φ1.symm).trans (Φ2.trans (dspProd act ρU S))
  exact finrank_of_pi_equiv_prod (finrank K C) Module.finrank_pos Φ

/-- If `L` acts on `B` through `ι`, commuting with `act g` for `g ∈ S`, then `[L:K]` divides
`dim_K Dsp(S)`. -/
theorem finrank_dvd_Dsp {B : Type*} [CommRing B] [Algebra K B] (act : G → B →ₗ[K] B)
    {V : Type*} [AddCommGroup V] [Module K V] (ρ : G → V →ₗ[K] V) (S : Set G)
    {L : Type*} [Field L] [Algebra K L] (ι : L →ₐ[K] B)
    (h : ∀ g ∈ S, ∀ x b, act g (ι x * b) = ι x * act g b) :
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
        simp only [LinearMap.smul_apply, hLsmul, hφ g hg v, h g hg] }
  have e2 : finrank K DL = finrank K (Dsp act ρ S) := rfl
  haveI : Module.Free L DL := Module.Free.of_divisionRing L DL
  rw [← e2, ← Module.finrank_mul_finrank K L DL]
  exact Dvd.intro _ rfl

end Count

/-! ### The local setting -/

section Local

variable (p : ℕ) [Fact p.Prime]

/-- `σ ↦ (v ↦ ρE(σ) v)` on `Eⁿ`, as `ℚ_p`-linear maps. -/
def matRep {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)} (ρE : GQp p →* GL (Fin n) E) :
    GQp p →* ((Fin n → E) →ₗ[ℚ_[p]] (Fin n → E)) where
  toFun σ := (Matrix.mulVecLin (ρE σ : Matrix (Fin n) (Fin n) E)).restrictScalars ℚ_[p]
  map_one' := LinearMap.ext fun v => by simp
  map_mul' σ τ := LinearMap.ext fun v => by simp [Matrix.mulVec_mulVec]

theorem matRep_apply {n : ℕ} {E : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (ρE : GQp p →* GL (Fin n) E) (σ : GQp p) (v : Fin n → E) :
    matRep p ρE σ v = Matrix.mulVec (ρE σ : Matrix (Fin n) (Fin n) E) v := rfl

variable {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E] {n : ℕ}

theorem ddrSpace_eq_Dsp (ρE : GQp p →* GL (Fin n) E) :
    ddrSpace p ρE = Dsp (drAct p) (matRep p ρE) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

theorem htSpace_eq_Dsp (ρE : GQp p →* GL (Fin n) E) (i : ℤ) :
    htSpace p ρE i = Dsp (htAct p i) (matRep p ρE) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

variable (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

theorem ddrSpaceOver_eq_Dsp (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) :
    ddrSpaceOver p ρ = Dsp (fun σ => drAct p (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

theorem htSpaceOver_eq_Dsp (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (i : ℤ) :
    htSpaceOver p ρ i = Dsp (fun σ => htAct p i (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ :=
  Submodule.ext fun _ => ⟨fun h σ _ v => h σ v, fun h σ v => h σ trivial v⟩

variable [IsGalois ℚ_[p] F]

theorem gammaF_gfToGqp (σ : Field.absoluteGaloisGroup F) : gammaF p F (gfToGqp p F σ) = 1 := by
  have : gfToGqp p F σ ∈ (gammaF p F).ker := by
    rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
  exact this

theorem Dsp_gf_eq {B : Type*} [AddCommGroup B] [Module ℚ_[p] B]
    {U : Type*} [AddCommGroup U] [Module ℚ_[p] U]
    (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ρU : GQp p →* (U →ₗ[ℚ_[p]] U)) :
    Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρU (gfToGqp p F σ)) Set.univ =
      Dsp act ρU ((gammaF p F).ker : Set (GQp p)) := by
  ext φ
  constructor
  · intro h τ hτ v
    rw [SetLike.mem_coe, ← range_gfToGqp] at hτ
    obtain ⟨σ, rfl⟩ := hτ
    exact h σ trivial v
  · intro h σ _ v
    exact h _ (by rw [SetLike.mem_coe, ← range_gfToGqp]; exact ⟨σ, rfl⟩) v

/-- **The count.** For an action `act` of `G_{ℚ_p}` on a `ℚ_p`-algebra `B` containing `ℚ̄_p`
equivariantly: `[E:ℚ_p] · dim D_F(V) = 2 [F:ℚ_p] · dim D_{ℚ_p}(ρE)` and
`[F:ℚ_p] ∣ dim D_F(V)`. -/
theorem core_count {B : Type*} [CommRing B] [Algebra ℚ_[p] B]
    (act : GQp p →* (B →ₗ[ℚ_[p]] B)) (ι : PadicAlgCl p →ₐ[ℚ_[p]] B)
    (hι : ∀ σ x b, act σ (ι x * b) = ι (σ x) * act σ b)
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V) (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x)) :
    finrank ℚ_[p] E * finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ)
      = 2 * (finrank ℚ_[p] F * finrank ℚ_[p] (Dsp act (matRep p ρE) Set.univ)) ∧
    finrank ℚ_[p] F ∣
      finrank ℚ_[p] (Dsp (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ) Set.univ) := by
  let ι' : fieldF p F →ₐ[ℚ_[p]] B := ι.comp (fieldF p F).val
  have hsemi : ∀ g x b, act g (ι' x * b) = ι' (gammaF p F g x) * act g b := by
    intro g x b
    simp only [ι', AlgHom.comp_apply, IntermediateField.coe_val, hι, gammaF_apply_coe]
  constructor
  · have h1 := overF_count_gen (fun σ => act (gfToGqp p F σ)) (fun σ => ρ σ)
      (fun σ => matRep p ρE (gfToGqp p F σ)) Set.univ eE he
    rw [h1, Dsp_gf_eq p F act (matRep p ρE),
      descent_finrank act (matRep p ρE) ι' (gammaF p F) (gammaF_surjective p F) hsemi,
      finrank_fieldF]
  · rw [← finrank_fieldF p F]
    refine finrank_dvd_Dsp _ _ _ ι' fun σ _ x b => ?_
    rw [hsemi, gammaF_gfToGqp]
    rfl

/-- `ℚ̄_p → ℂ_p`. -/
def cpEmb : PadicAlgCl p →ₐ[ℚ_[p]] ℂ_[p] := IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]

theorem htAct_semi (i : ℤ) (σ : GQp p) (x : PadicAlgCl p) (b : ℂ_[p]) :
    htAct p i σ (cpEmb p x * b) = cpEmb p (σ x) * htAct p i σ b := by
  rw [htAct_apply, htAct_apply, map_mul, mul_smul_comm]
  congr 2
  change cpAct p σ ((x : ℂ_[p])) = ((σ x : PadicAlgCl p) : ℂ_[p])
  exact cpAct_coe p σ x

theorem finrank_V_of_eE (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E)) :
    finrank ℚ_[p] V = 4 := by
  have := eE.finrank_eq
  rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at this
  omega

theorem count_two_zero : Multiset.count (0 : ℤ) {0, -1} = 1 := by decide
theorem count_two_neg_one : Multiset.count (-1 : ℤ) {0, -1} = 1 := by decide
theorem count_two_other (w : ℤ) (h0 : w ≠ 0) (h1 : w ≠ -1) : Multiset.count w {0, -1} = 0 := by
  simp [h0, h1]

/-- **G9 local core, Hodge–Tate part.** -/
theorem core_ht (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (h0 : htMultOver p ρ 0 = 2) (h1 : htMultOver p ρ (-1) = 2)
    (hw : ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p ρ w = 0) :
    HasHTWeights p ρE {0, -1} := by
  have hd : 0 < finrank ℚ_[p] E := Module.finrank_pos
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  -- the multiplicity at `w` is `M_w = dim H_{-w}(V) / [F:ℚ_p]`; then `htMult ρE w = M_w / 2`
  have key : ∀ w : ℤ, ∀ M : ℕ, htMultOver p ρ w = M →
      htMult p ρE w * 2 = M ∨ finrank ℚ_[p] E * M = 2 * finrank ℚ_[p] (htSpace p ρE (-w)) := by
    intro w M hM
    right
    obtain ⟨hc, hdvd⟩ := core_count p F (htAct p (-w)) (cpEmb p) (htAct_semi p (-w)) ρ ρE eE he
    rw [htMultOver, htSpaceOver_eq_Dsp] at hM
    rw [htSpace_eq_Dsp]
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_cancel_left _ hf] at hM
    subst hM
    rw [hk] at hc
    have : finrank ℚ_[p] F * (finrank ℚ_[p] E * k) =
        finrank ℚ_[p] F * (2 * finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ)) := by
      rw [← mul_assoc, mul_comm (finrank ℚ_[p] F), mul_assoc, hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hf this
  intro w
  have hdiv : ∀ M : ℕ, finrank ℚ_[p] E * (2 * M) = 2 * finrank ℚ_[p] (htSpace p ρE (-w)) →
      htMult p ρE w = M := by
    intro M hM
    have : finrank ℚ_[p] (htSpace p ρE (-w)) = finrank ℚ_[p] E * M := by
      have := hM; rw [mul_left_comm] at this; omega
    rw [htMult, this, Nat.mul_div_cancel_left _ hd]
  by_cases hw0 : w = 0
  · subst hw0
    rw [count_two_zero]
    rcases key 0 2 h0 with h | h
    · omega
    · exact hdiv 1 (by simpa using h)
  by_cases hw1 : w = -1
  · subst hw1
    rw [count_two_neg_one]
    rcases key (-1) 2 h1 with h | h
    · omega
    · exact hdiv 1 (by simpa using h)
  rw [count_two_other w hw0 hw1]
  rcases key w 0 (hw w hw0 hw1) with h | h
  · omega
  · exact hdiv 0 (by simpa using h)

/-- **G9 local core, de Rham part** (given an equivariant `ℚ̄_p → B_dR`). -/
theorem core_dR (ιB : PadicAlgCl p →ₐ[ℚ_[p]] BdR p)
    (hιB : ∀ (σ : GQp p) (x : PadicAlgCl p), bdrAct p σ (ιB x) = ιB (σ x))
    (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (hdR : IsDeRhamOver p ρ) :
    IsDeRham p ρE := by
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  have hsemi : ∀ σ x b, drAct p σ (ιB x * b) = ιB (σ x) * drAct p σ b := by
    intro σ x b
    rw [drAct_apply, drAct_apply, map_mul, hιB]
  obtain ⟨hc, -⟩ := core_count p F (drAct p) ιB hsemi ρ ρE eE he
  rw [IsDeRhamOver, ddrSpaceOver_eq_Dsp, finrank_V_of_eE p eE] at hdR
  rw [IsDeRham, ddrSpace_eq_Dsp]
  rw [hdR] at hc
  have : finrank ℚ_[p] F * (finrank ℚ_[p] (Dsp (drAct p) (matRep p ρE) Set.univ)) =
      finrank ℚ_[p] F * (2 * finrank ℚ_[p] E) := by
    have := hc; ring_nf at this ⊢; omega
  exact Nat.eq_of_mul_eq_mul_left hf this

end Local

end

end ZInQ.Contrib.G9
