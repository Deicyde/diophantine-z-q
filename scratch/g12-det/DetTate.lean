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

end G0Galois

end

#print axioms G0Galois.sympSimDet_of_darboux
#print axioms G0Galois.cycQ_resQ
#print axioms G0Galois.detTate_of
#print axioms G0Galois.detTate_of_darboux
