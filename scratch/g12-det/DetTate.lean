import Mathlib
import ZInQKernel.HDecomp.Objects

/-! # g12-det: `DetTate` (`det V_ℓ(A) = χ_ℓ^{dim A}`)

`DetTate` is copied verbatim from scratch/g0-mod-galois/part_det.lean, with its dependencies
`PkgI4.Qbar`, `PkgI4.GQ` (Split.lean L3940-3943), `GlueI3.repBaseChange` (Split.lean L2144),
`G0Galois.resQ`, `qEmbRing`, `resQ_spec`, `Vb`, `tate` (part_galois.lean), `toRingEquivQ`,
`cycQ` (part_det.lean). `PkgI3.AbVar`, `V`, `galRep`, `dim` come from
`ZInQKernel/HDecomp/Objects.lean`, whose PkgI3 section is the one of Split.lean L2418-2764 up to
whitespace (VERIFIED by `diff`).

Result: `detTate_of : TateGSp → SympSimDet → DetTate` and
`sympSimDet_of_darboux : Darboux → SympSimDet` (Mathlib's `SymplecticGroup.det_eq_one` does the
Pfaffian sign), so `DetTate` rests on
* `TateGSp` (GLUE: the `ℓ`-adic Weil pairing of a polarization on `V_ℓ(A)`, from T9),
* `Darboux` (GLUE, pure linear algebra: symplectic bases).
The comparison of the cyclotomic characters of `K̄` and `ℚ̄` along `resQ` is proved here
(`cyc_eq_of_intertwines`). -/

namespace PkgI4

abbrev Qbar := AlgebraicClosure ℚ

abbrev GQ := Qbar ≃ₐ[ℚ] Qbar

end PkgI4

noncomputable section

namespace GlueI3

open Representation

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Base change `ρ_E` of a representation along a field extension `E/k`. -/
def repBaseChange (E : Type*) [Field E] [Algebra k E] (ρ : Representation k G V) :
    Representation E G (TensorProduct k E V) where
  toFun g := (ρ g).baseChange E
  map_one' := by
    change (ρ 1).baseChange E = LinearMap.id
    rw [map_one, Module.End.one_eq_id, LinearMap.baseChange_id]
  map_mul' g h := by
    change (ρ (g * h)).baseChange E = (ρ g).baseChange E ∘ₗ (ρ h).baseChange E
    rw [map_mul, Module.End.mul_eq_comp, LinearMap.baseChange_comp]

end GlueI3

namespace G0Galois

open scoped Matrix

/-- The restriction map `G_K → G_ℚ` for a number field `K` (Mathlib's
`Field.absoluteGaloisGroup.map` along `ℚ → K`). Its image is `G_K` inside `G_ℚ` for the
embedding `K ↪ ℚ̄` that the map chooses. -/
def resQ (K : Type) [Field K] [NumberField K] : Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- The embedding `ℚ̄ → K̄` that `Field.absoluteGaloisGroup.map` chooses (`IsAlgClosed.lift`). -/
def qEmbRing (K : Type) [Field K] [NumberField K] : AlgebraicClosure ℚ →+* AlgebraicClosure K :=
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom

/-- `qEmb K ∘ resQ K τ = τ ∘ qEmb K` (Mathlib's `restrictNormal_commutes`, unfolding `map`). -/
lemma resQ_spec (K : Type) [Field K] [NumberField K]
    (τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) (x : AlgebraicClosure ℚ) :
    qEmbRing K (resQ K τ x) = τ (qEmbRing K x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

/-- `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- `σ ↦ σ` as ring automorphisms of `ℚ̄`. -/
def toRingEquivQ : PkgI4.GQ →* (PkgI4.Qbar ≃+* PkgI4.Qbar) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The `ℓ`-adic cyclotomic character `χ_ℓ : G_ℚ → ℤ_ℓ^× ⊆ ℚ̄_ℓ^×` (Mathlib's
`cyclotomicCharacter` on `ℚ̄`, as `PkgI4.cyc` on `G_{ℚ_p}`). -/
def cycQ (ℓ : ℕ) [Fact ℓ.Prime] : PkgI4.GQ →* (PadicAlgCl ℓ)ˣ :=
  (Units.map ((algebraMap ℚ_[ℓ] (PadicAlgCl ℓ)).comp PadicInt.Coe.ringHom).toMonoidHom).comp
    ((cyclotomicCharacter PkgI4.Qbar ℓ).comp toRingEquivQ)

/-- **`det V_ℓ(A) = χ_ℓ^{dim A}` (GLUE, unproved; from T9, the Weil pairing of a polarization:
`G_K` acts on `V_ℓ(A)` through `GSp_{2g}` with multiplier `χ_ℓ`, Mumford §20, §23, STANDARD).** -/
def DetTate : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ),
    A.dim = g → ∀ σ, LinearMap.det (tate A ℓ σ) = ((cycQ ℓ (resQ K σ) : PadicAlgCl ℓ)) ^ g

/-! ## The named pieces -/

/-- **Symplectic (Darboux) bases (GLUE, pure linear algebra; STANDARD: Bourbaki, Algèbre IX §5
no. 1, Artin, *Geometric algebra*, Thm 3.7; numbering UNVERIFIED).** A nondegenerate alternating
bilinear form on a space of dimension `2n` over a field has a basis, indexed by `Fin n ⊕ Fin n`,
in which its Gram matrix is Mathlib's `Matrix.J`. -/
def Darboux : Prop :=
  ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (n : ℕ), B.Nondegenerate → (∀ x, B x x = 0) →
    Module.finrank F V = 2 * n →
    ∃ b : Module.Basis (Fin n ⊕ Fin n) F V, LinearMap.BilinForm.toMatrix b B = Matrix.J (Fin n) F

/-- **Determinant of a symplectic similitude (GLUE, pure linear algebra; STANDARD: the Pfaffian
identity `Pf(MᵀGM) = det M · Pf G`, Bourbaki, Algèbre IX §5 no. 2; numbering UNVERIFIED).** If `f`
multiplies a nondegenerate alternating form on a `2n`-dimensional space by `c ≠ 0`, then
`det f = cⁿ`. Proved below from `Darboux` (`sympSimDet_of_darboux`). -/
def SympSimDet : Prop :=
  ∀ (F V : Type) [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (f : V →ₗ[F] V) (c : F) (n : ℕ), B.Nondegenerate →
    (∀ x, B x x = 0) → Module.finrank F V = 2 * n → c ≠ 0 →
    (∀ x y, B (f x) (f y) = c * B x y) → LinearMap.det f = c ^ n

/-- **The `ℓ`-adic Weil pairing on `V_ℓ(A)` (GLUE; from T9 = Mumford §20, §23 and T26 =
Mumford §18-19, as restated in scratch/weil-pairing).** For an abelian variety `A` of dimension
`g` over a number field `K` and a prime `ℓ`: `V_ℓ(A)` has dimension `2g` and carries a
nondegenerate alternating `ℚ_ℓ`-bilinear form `B` with `B(σx, σy) = χ_ℓ(σ) B(x, y)` for
`σ ∈ G_K`, `χ_ℓ` the cyclotomic character of `G_K` on `K̄`. (`B = E^λ` for a polarization `λ`
over `K`, composed with a coordinate `T_ℓ(μ) ≅ ℤ_ℓ`.) scratch/weil-pairing proves, from the leaves
`T09_SymmIsogenyExists`, `IsogenyQuasiInverse`, `TateModuleFree`, `DivisiblePoints`, the
`ℤ_ℓ`-level pairing `tatePairing` on `T_ℓ A` (alternating `tatePairing_self`, multiplier
`tatePairing_cyclotomic`, trivial left kernel `tatePairing_left_ker`) and the coordinate
`tmuCoordLin`; what is left is the extension of scalars to `V_ℓ = ℚ_ℓ ⊗ T_ℓ` (nondegeneracy over
the fraction field from the trivial kernel on a free module of finite rank) and
`dim V_ℓ = rank T_ℓ = 2g` (T26). -/
def TateGSp : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (g : ℕ),
    A.dim = g →
    ∃ (_ : FiniteDimensional ℚ_[ℓ] (A.V ℓ)) (B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ)),
      Module.finrank ℚ_[ℓ] (A.V ℓ) = 2 * g ∧ B.Nondegenerate ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Field.absoluteGaloisGroup K) (x y : A.V ℓ),
        B (A.galRep ℓ σ x) (A.galRep ℓ σ y) =
          (((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) :
            ℚ_[ℓ]) * B x y

/-! ## Proofs -/

/-- `Dᵀ J D = c⁻¹ J` for `D = diag(1, c⁻¹)`. -/
lemma J_conj_diag {F : Type*} [Field F] (n : ℕ) (c : F) :
    (Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ *
        Matrix.J (Fin n) F * Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) = c⁻¹ • Matrix.J (Fin n) F := by
  simp [Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_smul]

/-- **`SympSimDet` from `Darboux`** (and Mathlib's `Matrix.symplecticGroup.det_eq_one`). -/
theorem sympSimDet_of_darboux (hD : Darboux) : SympSimDet := by
  intro F V _ _ _ _ B f c n hB halt hdim hc hf
  classical
  obtain ⟨b, hb⟩ := hD F V B n hB halt hdim
  set M := LinearMap.toMatrix b b f with hM
  have hcomp : B.comp f f = c • B := by
    ext x y
    simp [hf]
  have h1 := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hcomp, map_smul, hb] at h1
  -- `h1 : c • J = Mᵀ * J * M`
  set D : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F := Matrix.fromBlocks 1 0 0 (c⁻¹ • 1) with hDdef
  have hsymp : M * D ∈ Matrix.symplecticGroup (Fin n) F := by
    rw [SymplecticGroup.mem_iff']
    calc (M * D)ᵀ * Matrix.J (Fin n) F * (M * D)
        = Dᵀ * (Mᵀ * Matrix.J (Fin n) F * M) * D := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = c • (Dᵀ * Matrix.J (Fin n) F * D) := by
          rw [← h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = Matrix.J (Fin n) F := by
          rw [hDdef, J_conj_diag, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have hdet1 := SymplecticGroup.det_eq_one hsymp
  have hDdet : D.det = c⁻¹ ^ n := by
    rw [hDdef, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin]
    ring
  rw [Matrix.det_mul, hDdet] at hdet1
  rw [← LinearMap.det_toMatrix b f, ← hM]
  have hcn : c ^ n ≠ 0 := pow_ne_zero n hc
  rw [inv_pow] at hdet1
  exact (mul_inv_eq_one₀ hcn).1 hdet1

/-- The cyclotomic characters of two fields agree on automorphisms intertwined by a ring
homomorphism (both fields containing all `ℓ`-power roots of unity). -/
lemma cyc_eq_of_intertwines {L L' : Type*} [Field L] [Field L'] (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ k, HasEnoughRootsOfUnity L (ℓ ^ k)] [∀ k, HasEnoughRootsOfUnity L' (ℓ ^ k)]
    (i : L →+* L') (g : L ≃+* L) (g' : L' ≃+* L') (h : ∀ x, i (g x) = g' (i x)) :
    cyclotomicCharacter L ℓ g = cyclotomicCharacter L' ℓ g' := by
  apply Units.ext
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  rw [cyclotomicCharacter.toZModPow, cyclotomicCharacter.toZModPow]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have ht' : Units.map i.toMonoidHom t ∈ rootsOfUnity (ℓ ^ n) L' := by
    rw [mem_rootsOfUnity] at ht ⊢
    rw [← map_pow, ht, map_one]
  have := modularCyclotomicCharacter.spec L'
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity L' (ℓ ^ n)) g' ht'
  apply i.injective
  rw [h, map_pow]
  simpa using this

/-- `χ_ℓ(resQ σ)` on `ℚ̄` is `χ_ℓ(σ)` on `K̄`. -/
lemma cycQ_resQ (K : Type) [Field K] [NumberField K] (ℓ : ℕ) [Fact ℓ.Prime]
    (σ : Field.absoluteGaloisGroup K) :
    cyclotomicCharacter PkgI4.Qbar ℓ (toRingEquivQ (resQ K σ)) =
      cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv :=
  cyc_eq_of_intertwines ℓ (qEmbRing K) _ _ (fun x => resQ_spec K σ x)

/-- **`DetTate` from `TateGSp` and `SympSimDet`.** -/
theorem detTate_of (hW : TateGSp) (hS : SympSimDet) : DetTate := by
  intro K _ _ A ℓ _ g hdim σ
  obtain ⟨hfd, B, hrank, hB, halt, hmult⟩ := hW K A ℓ g hdim
  set c : ℚ_[ℓ] := (((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) :
    ℤ_[ℓ]) : ℚ_[ℓ]) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, PadicInt.coe_ne_zero]
    exact Units.ne_zero _
  have hdet : LinearMap.det (A.galRep ℓ σ) = c ^ g :=
    hS ℚ_[ℓ] (A.V ℓ) B (A.galRep ℓ σ) c g hB halt hrank hc0 (hmult σ)
  change LinearMap.det ((A.galRep ℓ σ).baseChange (PadicAlgCl ℓ)) = _
  rw [LinearMap.det_baseChange, hdet, map_pow]
  congr 1
  simp only [cycQ, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, RingHom.coe_comp]
  rw [cycQ_resQ]
  rfl

/-- **`DetTate` from `TateGSp` and `Darboux`.** -/
theorem detTate_of_darboux (hW : TateGSp) (hD : Darboux) : DetTate :=
  detTate_of hW (sympSimDet_of_darboux hD)


/-! ## `Darboux`, proved (same proof as scratch/g12-det/Darboux.lean) -/

section DarbouxProof

open Module LinearMap LinearMap.BilinForm

variable {F : Type} [Field F]

lemma skew_of_alt {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) (x y : V) : B y x = - B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  linear_combination h

lemma isRefl_of_alt {V : Type} [AddCommGroup V] [Module F V] (B : LinearMap.BilinForm F V)
    (halt : ∀ x, B x x = 0) : B.IsRefl := by
  intro x y h
  rw [skew_of_alt B halt x y, h, neg_zero]

/-- A family with Gram matrix `J` is linearly independent. -/
lemma linearIndependent_of_gram {V : Type} [AddCommGroup V] [Module F V]
    (B : LinearMap.BilinForm F V) (n : ℕ) (v : Fin n ⊕ Fin n → V)
    (hv : ∀ i j, B (v i) (v j) = Matrix.J (Fin n) F i j) : LinearIndependent F v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : Matrix.vecMul g (Matrix.J (Fin n) F) = 0 := by
    funext j
    have := congrArg (fun x => B x (v j)) hg
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hv, smul_eq_mul,
      map_zero, LinearMap.zero_apply] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have h2 := congrArg (fun w => Matrix.vecMul w (Matrix.J (Fin n) F)) h1
  simp only [Matrix.vecMul_vecMul, Matrix.J_squared, Matrix.zero_vecMul] at h2
  intro i
  have := congrFun h2 i
  simpa [Matrix.vecMul_neg] using this

/-- The family version of Darboux, by induction. -/
lemma exists_gram_J : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V), B.Nondegenerate → (∀ x, B x x = 0) → finrank F V = 2 * n →
    ∃ v : Fin n ⊕ Fin n → V, ∀ i j, B (v i) (v j) = Matrix.J (Fin n) F i j := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ B _ _ _
    exact ⟨fun i => by rcases i with i | i <;> exact i.elim0, fun i => by
      rcases i with i | i <;> exact i.elim0⟩
  | succ n ih =>
    intro V _ _ _ B hB halt hdim
    have hrefl := isRefl_of_alt B halt
    have hpos : 0 < finrank F V := by rw [hdim]; omega
    haveI : Nontrivial V := Module.finrank_pos_iff.mp hpos
    obtain ⟨e, he⟩ := exists_ne (0 : V)
    have : ∃ y, B e y ≠ 0 := by
      by_contra h
      push Not at h
      exact he (hB.1 e h)
    obtain ⟨y, hy⟩ := this
    set f := (B e y)⁻¹ • y with hfdef
    have hef : B e f = 1 := by
      rw [hfdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hy]
    have hfe : B f e = -1 := by rw [skew_of_alt B halt, hef]
    have hee : B e e = 0 := halt e
    have hff : B f f = 0 := halt f
    set H : Submodule F V := Submodule.span F {e, f} with hH
    set W : Submodule F V := B.orthogonal H with hW
    -- elements of `H`
    have hmemH : ∀ x ∈ H, ∃ a b : F, a • e + b • f = x := fun x hx =>
      Submodule.mem_span_pair.mp hx
    have heH : e ∈ H := Submodule.subset_span (by simp)
    have hfH : f ∈ H := Submodule.subset_span (by simp)
    -- `H ∩ H^⊥ = 0`
    have hdisj : Disjoint H W := by
      rw [Submodule.disjoint_def]
      intro x hx hxW
      obtain ⟨a, b, rfl⟩ := hmemH x hx
      have h1 : B e (a • e + b • f) = 0 := hxW e heH
      have h2 : B f (a • e + b • f) = 0 := hxW f hfH
      simp only [map_add, map_smul, smul_eq_mul, hee, hef, hfe, hff] at h1 h2
      have ha : a = 0 := by linear_combination -h2
      have hb : b = 0 := by linear_combination h1
      simp [ha, hb]
    have hcompl : IsCompl H W :=
      isCompl_orthogonal_of_restrict_nondegenerate hrefl
        (B.nondegenerate_restrict_of_disjoint_orthogonal hrefl hdisj)
    -- `finrank H = 2`
    have hli : LinearIndependent F ![e, f] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg (B e) hst
      have h2 := congrArg (B f) hst
      simp only [map_add, map_smul, smul_eq_mul, hee, hef, hfe, hff, map_zero] at h1 h2
      constructor
      · linear_combination -h2
      · linear_combination h1
    have hH2 : finrank F H = 2 := by
      have := finrank_span_eq_card hli
      rw [Matrix.range_cons_cons_empty, Fintype.card_fin] at this
      exact this
    have hW2 : finrank F W = 2 * n := by
      rw [hW, finrank_orthogonal hB, hdim, hH2]; omega
    -- the restriction to `W` is nondegenerate and alternating
    have hBW : (B.restrict W).Nondegenerate := by
      have hsplit : ∀ z : V, ∃ h ∈ H, ∃ w ∈ W, h + w = z := fun z =>
        Submodule.mem_sup.mp (hcompl.sup_eq_top ▸ Submodule.mem_top)
      constructor
      · intro m hm
        apply Subtype.ext
        apply hB.1
        intro z
        obtain ⟨h, hh, w, hw, rfl⟩ := hsplit z
        rw [map_add, hrefl _ _ (m.2 h hh)]
        have := hm ⟨w, hw⟩
        simpa using this
      · intro m hm
        apply Subtype.ext
        apply hB.2
        intro z
        obtain ⟨h, hh, w, hw, rfl⟩ := hsplit z
        rw [LinearMap.map_add₂, m.2 h hh]
        have := hm ⟨w, hw⟩
        simpa using this
    have haltW : ∀ x, B.restrict W x x = 0 := fun x => halt x
    obtain ⟨w, hw⟩ := ih W (B.restrict W) hBW haltW hW2
    have hfw : ∀ x : W, B f x = 0 := fun x => x.2 f hfH
    have hew : ∀ x : W, B e x = 0 := fun x => x.2 e heH
    have hwf : ∀ x : W, B x f = 0 := fun x => hrefl _ _ (hfw x)
    have hwe : ∀ x : W, B x e = 0 := fun x => hrefl _ _ (hew x)
    have hww : ∀ i j, B (w i) (w j) = Matrix.J (Fin n) F i j := hw
    let v : Fin (n + 1) ⊕ Fin (n + 1) → V :=
      Sum.elim (Fin.cons f fun j => (w (Sum.inl j) : V))
        (Fin.cons e fun j => (w (Sum.inr j) : V))
    refine ⟨v, ?_⟩
    intro i j
    rcases i with i | i <;> rcases j with j | j <;>
      induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [v, Matrix.J, hef, hfe, hee, hff, hfw, hew, hwf, hwe, hww, Matrix.one_apply,
        Fin.succ_ne_zero, Fin.succ_inj]
    all_goals exact (Fin.succ_ne_zero _).symm

/-- **`Darboux`, proved.** -/
theorem darboux : Darboux := by
  intro F V _ _ _ _ B n hB halt hdim
  classical
  obtain ⟨v, hv⟩ := exists_gram_J n V B hB halt hdim
  have hli := linearIndependent_of_gram B n v hv
  have hcard : Fintype.card (Fin n ⊕ Fin n) = finrank F V := by
    rw [Fintype.card_sum, Fintype.card_fin, hdim]; ring
  refine ⟨basisOfLinearIndependentOfCardEqFinrank' v hli hcard, ?_⟩
  refine Matrix.ext fun i j => ?_
  rw [LinearMap.BilinForm.toMatrix_apply, coe_basisOfLinearIndependentOfCardEqFinrank', hv]

end DarbouxProof

/-- **`DetTate` from `TateGSp` alone** (`Darboux` and `SympSimDet` are proved). -/
theorem detTate_of_tateGSp (hW : TateGSp) : DetTate :=
  detTate_of_darboux hW darboux


/-! ## `TateGSp` from the `ℤ_ℓ`-level Weil pairing (scratch/weil-pairing) and T26 -/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **The `ℓ`-adic Weil pairing on `T_ℓ(A)`, `ℤ_ℓ`-valued (GLUE, proved in scratch/weil-pairing
from leaves, up to restatement).** There is an alternating `ℤ_ℓ`-bilinear form on `T_ℓ(A)` with
trivial left kernel and multiplier the cyclotomic character of `G_K` on `K̄`. In
scratch/weil-pairing this is `B = (tatePairing D lam hℓ).compr₂ (tmuCoordLin hg)` for a
polarization `S.lam` (leaf `T09_SymmIsogenyExists`), with `tatePairing_self` (alternating),
`tatePairing_cyclotomic` (multiplier), and `tatePairing_left_ker` + `tmuCoordLin_injective`
(trivial left kernel; leaves `IsogenyQuasiInverse`, `DivisiblePoints`), exactly as in the proof
of `det_galRep_sq` / `g12_detInput_of_leaves` there (VERIFIED by reading WeilPairing.lean
L969-1148). The statement below is not compiled against that file (scratch files cannot import
each other); its `B` is theirs. -/
def TatePairingZl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime],
    ∃ B : LinearMap.BilinForm ℤ_[ℓ] (A.T ℓ), B.SeparatingLeft ∧ (∀ x, B x x = 0) ∧
      ∀ (σ : Field.absoluteGaloisGroup K) (x y : A.T ℓ),
        B (A.galT σ x) (A.galT σ y) =
          ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * B x y

lemma skew_of_alt' {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (B : LinearMap.BilinForm R V) (halt : ∀ x, B x x = 0) (x y : V) : B y x = - B x y := by
  have h := halt (x + y)
  simp only [map_add, LinearMap.add_apply, halt x, halt y, zero_add, add_zero] at h
  linear_combination h

/-- **`TateGSp` from `TatePairingZl` and T26 (`PkgI3.TateModuleFree`, leaf I3 of Objects).** The
form on `V_ℓ = ℚ_ℓ ⊗ T_ℓ` is the one with the same Gram matrix in the base-changed basis. -/
theorem tateGSp_of_zl (hZ : TatePairingZl) (hT : PkgI3.TateModuleFree) : TateGSp := by
  intro K _ _ A ℓ _ g hdim
  classical
  obtain ⟨B0, hsep, halt0, hmult⟩ := hZ K A ℓ
  have hℓ : (ℓ : K) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓ
  have hrank : Module.finrank ℤ_[ℓ] (A.T ℓ) = 2 * g := by
    rw [hdim] at hrk
    have h3 : (((Module.finrank ℤ_[ℓ] (A.T ℓ) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        (((2 * g : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [hrk]; push_cast; rfl
    exact_mod_cast WithBot.coe_injective h3
  let b := Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)
  let bV : Module.Basis _ ℚ_[ℓ] (A.V ℓ) := Algebra.TensorProduct.basis ℚ_[ℓ] b
  have hnd0 : B0.Nondegenerate := LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft hsep
  have hdet0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 hnd0
  set G := LinearMap.BilinForm.toMatrix b B0 with hG
  let φ := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  have hφ : Function.Injective φ := IsFractionRing.injective ℤ_[ℓ] ℚ_[ℓ]
  set G' := G.map φ with hG'
  let B : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) := Matrix.toBilin bV G'
  have hBG : LinearMap.BilinForm.toMatrix bV B = G' := LinearMap.BilinForm.toMatrix_toBilin _ _
  haveI : FiniteDimensional ℚ_[ℓ] (A.V ℓ) := Module.Finite.of_basis bV
  refine ⟨inferInstance, B, ?_, ?_, ?_, ?_⟩
  · rw [Module.finrank_baseChange, hrank]
  · rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero bV, hBG, hG', show G.map φ = φ.mapMatrix G from rfl, ← RingHom.map_det]
    exact fun h => hdet0 (hφ (by rw [h, map_zero]))
  · -- alternating: the Gram matrix is alternating, and `2 ≠ 0`
    have hskew : ∀ i j, G' j i = - G' i j := by
      intro i j
      simp only [hG', hG, Matrix.map_apply, LinearMap.BilinForm.toMatrix_apply]
      rw [skew_of_alt' B0 halt0, map_neg]
    intro x
    have hsum : B x x = ∑ i, ∑ j, bV.repr x i * G' i j * bV.repr x j := Matrix.toBilin_apply bV G' x x
    have hsum' : B x x = - B x x := by
      conv_rhs => rw [hsum, Finset.sum_comm]
      rw [hsum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hskew j i]
      ring
    have h2 : (2 : ℚ_[ℓ]) * B x x = 0 := by linear_combination hsum'
    exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
  · intro σ
    set c0 := ((cyclotomicCharacter (AlgebraicClosure K) ℓ σ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ])
    have hc0 : B0.comp (A.galT σ) (A.galT σ) = c0 • B0 := by
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      change B0 (A.galT σ x) (A.galT σ y) = c0 * B0 x y
      rw [hmult σ x y]
    set M := LinearMap.toMatrix b b (A.galT σ) with hM
    have h1 := LinearMap.BilinForm.toMatrix_comp b b B0 (A.galT σ) (A.galT σ)
    rw [hc0, map_smul] at h1
    -- `h1 : c0 • G = Mᵀ * G * M`
    have hfM : LinearMap.toMatrix bV bV (A.galRep ℓ σ) = M.map φ :=
      LinearMap.toMatrix_baseChange ℚ_[ℓ] (A.galT σ) b b
    have hcomp : B.comp (A.galRep ℓ σ) (A.galRep ℓ σ) = (φ c0) • B := by
      apply (LinearMap.BilinForm.toMatrix bV).injective
      rw [LinearMap.BilinForm.toMatrix_comp bV bV, hfM, hBG, map_smul, hBG, hG']
      have h2 := congrArg (fun X => X.map φ) h1
      simp only [Matrix.map_mul, Matrix.transpose_map] at h2
      rw [← hG] at h2
      exact h2.symm
    intro x y
    have := congrArg (fun C : LinearMap.BilinForm ℚ_[ℓ] (A.V ℓ) => C x y) hcomp
    simpa [φ] using this

/-- **`DetTate` from the `ℤ_ℓ`-level Weil pairing and T26.** -/
theorem detTate_of_zl (hZ : TatePairingZl) (hT : PkgI3.TateModuleFree) : DetTate :=
  detTate_of_tateGSp (tateGSp_of_zl hZ hT)

end G0Galois

end

#print axioms G0Galois.sympSimDet_of_darboux
#print axioms G0Galois.cycQ_resQ
#print axioms G0Galois.detTate_of
#print axioms G0Galois.detTate_of_darboux
#print axioms G0Galois.darboux
#print axioms G0Galois.detTate_of_tateGSp
#print axioms G0Galois.tateGSp_of_zl
#print axioms G0Galois.detTate_of_zl
