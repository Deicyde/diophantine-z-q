import ZInQKernel.Contrib.OneProof.RC.KummerMaps.TateLevel

/-!
# Lane RC29 (Kummer maps), item 3(e): `A_i ⊗_ℤ E(K_S)[2^i] ≅ A_i ⊗_{ℤ₂} T₂E`, `M_i = (T₂E ⊗ A_i)(α)`

Manuscript `diophantine_zq.tex` (11/5 version), tex 2723–2726:

> The actual finite coefficients are `A_i=(ℤ/2^iℤ)[t]/t^i`, `M_i=(T_2E⊗A_i)(χ_hΨ_i)`,

with `T = T₂E` the Tate module of the fixed curve `E/ℚ` (tex 2836–2837) and `α_i = χ_hΨ_i` the
character of tex 2790–2791.

Lane RC28 built `M_i` as `Mcoef K S W i α = CoefMod (Acoef i) α (TorsS K S W (2^i))`, i.e.
`(A_i ⊗_ℤ E(K_S)[2^i])(α)` with `σ` acting by `α(σ) · (1 ⊗ σ)` (the form the text itself uses at
tex 3207–3208, `(E[2^m] ⊗ A)(θ)`), and recorded as its DEPARTURE 1 that tex 2726's
`T₂E ⊗_{ℤ₂} A_i` had been replaced by `A_i ⊗_ℤ E[2^i]` without a formal identification. This file
supplies the identification, for any `ℤ/2^i`-algebra `A` (in particular `A_i = Acoef i`, and also
the binary coefficient ring `A_i[G]` of tex 2790):

* `tateZ2Algebra i A`: the `ℤ₂`-algebra structure `ℤ₂ → ℤ/2^i → A` of a `ℤ/2^i`-algebra; it is
  the only ring map `ℤ₂ → A` (`tateZ2_ringHom_eq`), so no choice is involved.
* `TateCoef i A E = A ⊗_{ℤ₂} T₂E` (an `A`-module), with `tateCoefMk a x = a ⊗ x`,
  `tateCoefRep i A E g = 1 ⊗ ρ_T(g)` (`ρ_T = tateRep E 2`, lanes RC9/RC17), and the `A`-basis
  `tateCoefBasis` (`1 ⊗ b_j`, `b = tateBasis E`), on which `1 ⊗ ρ_T(g)` has the matrix
  `tateMatrix E g` reduced into `A` (`tateCoefRep_basis`).
* `tateLevelCoefEquiv i A E : A ⊗_ℤ E(ℚ̄)[2^i] ≃ₗ[A] A ⊗_{ℤ₂} T₂E`, `a ⊗ proj_i(x) ↦ a ⊗ x`
  (`tateLevelCoefEquiv_tmul_proj`).
* **`tateCoefEquiv S E e i A α hW : CoefMod A α (E(K_S)[2^i]) ≃ₗ[A] A ⊗_{ℤ₂} T₂E`** under
  `FullTorsion` (GLUE, lane RC28), `a ⊗ P ↦ a ⊗ x` for any `x ∈ T₂E` lifting the image of `P` in
  `E(ℚ̄)[2^i]` (`tateCoefEquiv_tmul_lift`), and **`tateCoefEquiv_smul`**: for `σ ∈ G_{K,S}` and
  any lift `σ' ∈ Gal(K̄/K)`, `Φ(σ m) = α(σ) · (1 ⊗ ρ_T(e σ' e⁻¹)) Φ(m)`. So the
  `A[G_{K,S}]`-module `(A ⊗_ℤ E(K_S)[2^i])(α)` *is* `(T₂E ⊗ A)(α)` of tex 2726: the `G_{K,S}`-action
  is `α ⊗ ρ_T`, read through any lift (the result does not depend on the lift).
* `tateMcoefEquiv`, `tateMcoefEquiv_smul`, `tateMcoefBasis_smul`: the same for the actual `M_i =
  Mcoef K S (E⁄K) i α` over `A_i = Acoef i`; in the basis `Φ⁻¹(1 ⊗ b_j)` the matrix of `σ` is
  `α(σ) · (tateMatrix E (e σ' e⁻¹) mod 2^i)`.

This removes lane RC28's DEPARTURE 1, up to the GLUE `FullTorsion K S (E⁄K) (2^i)`
(Néron–Ogg–Shafarevich: Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., VII.7.1;
Serre–Tate, Ann. of Math. 88 (1968), Thm. 1), which is non-vacuous (`tate_fullTorsion_zero`,
`tate_fullTorsion_ecurve`) and is exactly the statement that the `G_K`-module `T₂E/2^i` is a
`G_{K,S}`-module.

Kinds: definitions and PROVED. DEPARTURES (form): the text's `T₂E ⊗ A_i` is written
`A_i ⊗_{ℤ₂} T₂E` (scalars on the left, Mathlib's base-change convention; the two differ by the
symmetry of `⊗`); the text's `G_K ⊂ G_ℚ` is the map `tateGalToQ e` for a chosen `e : K̄ ≃ₐ[ℚ] ℚ̄`
(see `TateLevel.lean`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain WeierstrassCurve TensorProduct
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.TateWiring (tateMatrix)
open scoped WeierstrassCurve

/-! ### `A ⊗_{ℤ₂} T₂E` for a `ℤ/2^i`-algebra `A` -/

section Coef

variable (i : ℕ) (A : Type) [CommRing A] [Algebra (ZMod (2 ^ i)) A]

/-- **The `ℤ₂`-algebra structure of a `ℤ/2^i`-algebra**: `ℤ₂ → ℤ/2^i → A` (reduction mod `2^i`,
then the structure map). -/
abbrev tateZ2Algebra : Algebra ℤ_[2] A :=
  ((algebraMap (ZMod (2 ^ i)) A).comp (PadicInt.toZModPow i)).toAlgebra

variable (E : WeierstrassCurve ℚ)

/-- **`A ⊗_{ℤ₂} T₂E`** (tex 2726's `T₂E ⊗ A_i`, scalars on the left), for the `ℤ₂`-algebra
structure `tateZ2Algebra i A`. -/
def TateCoef : Type :=
  @TensorProduct ℤ_[2] _ A (TateMod E 2) _ _ (tateZ2Algebra i A).toModule _

instance : AddCommGroup (TateCoef i A E) :=
  @TensorProduct.addCommGroup ℤ_[2] _ A (TateMod E 2) _ _ (tateZ2Algebra i A).toModule _

instance : Module A (TateCoef i A E) :=
  @TensorProduct.leftModule ℤ_[2] A _ _ A (TateMod E 2) _ _ _ (tateZ2Algebra i A).toModule _
    (@Algebra.to_smulCommClass ℤ_[2] A _ _ (tateZ2Algebra i A))

/-- The pure tensor `a ⊗ x` of `A ⊗_{ℤ₂} T₂E`. -/
def tateCoefMk (a : A) (x : TateMod E 2) : TateCoef i A E :=
  letI := tateZ2Algebra i A
  a ⊗ₜ[ℤ_[2]] x

theorem tateCoefMk_smul (a b : A) (x : TateMod E 2) :
    a • tateCoefMk i A E b x = tateCoefMk i A E (a * b) x := by
  let _ := tateZ2Algebra i A
  exact smul_tmul' a b x

/-- `a ⊗ (c x) = (c mod 2^i) · (a ⊗ x)` for `c ∈ ℤ₂`. Kind: PROVED. -/
theorem tateCoefMk_smul_right (a : A) (c : ℤ_[2]) (x : TateMod E 2) :
    tateCoefMk i A E a (c • x) =
      algebraMap (ZMod (2 ^ i)) A (PadicInt.toZModPow i c) • tateCoefMk i A E a x := by
  let _ := tateZ2Algebra i A
  change a ⊗ₜ[ℤ_[2]] (c • x) = algebraMap (ZMod (2 ^ i)) A (PadicInt.toZModPow i c) • a ⊗ₜ[ℤ_[2]] x
  rw [tmul_smul, smul_tmul', smul_tmul']
  rfl

theorem tateCoefMk_add_right (a : A) (x y : TateMod E 2) :
    tateCoefMk i A E a (x + y) = tateCoefMk i A E a x + tateCoefMk i A E a y := by
  let _ := tateZ2Algebra i A
  exact tmul_add a x y

/-- Induction on `A ⊗_{ℤ₂} T₂E` over pure tensors. -/
theorem tateCoef_induction {P : TateCoef i A E → Prop} (m : TateCoef i A E)
    (hmk : ∀ a x, P (tateCoefMk i A E a x)) (hadd : ∀ m₁ m₂, P m₁ → P m₂ → P (m₁ + m₂)) :
    P m := by
  let _ := tateZ2Algebra i A
  exact TensorProduct.inductionOn (motive := P) m hmk hadd

theorem tate_zmod_smul {M : Type} [AddCommGroup M] [Module (ZMod (2 ^ i)) M] (z : ZMod (2 ^ i))
    (y : M) : z • y = z.val • y := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact Nat.cast_smul_eq_nsmul _ _ _

/-- **The `ℤ₂`-algebra structure is the only one**: every ring map `ℤ₂ → A` is `ℤ₂ → ℤ/2^i → A`
(it kills `2^i`, and `ker(ℤ₂ → ℤ/2^i) = 2^i ℤ₂`). So `A ⊗_{ℤ₂} T₂E` involves no choice.
Kind: PROVED. -/
theorem tateZ2_ringHom_eq (f : ℤ_[2] →+* A) :
    f = (algebraMap (ZMod (2 ^ i)) A).comp (PadicInt.toZModPow i) := by
  have h0 : (2 : ZMod (2 ^ i)) ^ i = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ i)
  have h2 : f (((2 : ℕ) : ℤ_[2]) ^ i) = 0 := by
    rw [map_pow, map_natCast, Nat.cast_ofNat, ← map_ofNat (algebraMap (ZMod (2 ^ i)) A) 2,
      ← map_pow, h0, map_zero]
  ext c
  have hker : c - ((PadicInt.toZModPow i c).val : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow i) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
  obtain ⟨d, hd⟩ := hker
  have hc : c = ((2 : ℕ) : ℤ_[2]) ^ i * d + ((PadicInt.toZModPow i c).val : ℤ_[2]) := by
    rw [← hd, sub_add_cancel]
  rw [RingHom.comp_apply, hc, map_add, map_mul, h2, zero_mul, zero_add, map_natCast, map_add,
    map_mul, map_natCast, ZMod.natCast_zmod_val, map_pow, map_natCast, Nat.cast_ofNat, h0,
    zero_mul, zero_add, ← map_natCast (algebraMap (ZMod (2 ^ i)) A), ZMod.natCast_zmod_val]

theorem tateZ2_smul (c : ℤ_[2]) (a : A) :
    (letI := tateZ2Algebra i A; c • a) = PadicInt.toZModPow i c • a := by
  let _ := tateZ2Algebra i A
  rw [Algebra.smul_def, Algebra.smul_def]
  rfl

/-- The `A`-basis `1 ⊗ b_j` of `A ⊗_{ℤ₂} T₂E`, `b = tateBasis E` (lane RC9). -/
def tateCoefBasis [E.IsElliptic] : Module.Basis (Fin 2) A (TateCoef i A E) :=
  letI := tateZ2Algebra i A
  Algebra.TensorProduct.basis A (tateBasis E)

theorem tateCoefBasis_apply [E.IsElliptic] (j : Fin 2) :
    tateCoefBasis i A E j = tateCoefMk i A E 1 (tateBasis E j) := by
  let _ := tateZ2Algebra i A
  exact Algebra.TensorProduct.basis_apply (tateBasis E) j

/-- **`1 ⊗ ρ_T(g)`** on `A ⊗_{ℤ₂} T₂E`, `ρ_T = tateRep E 2` (lanes RC9/RC17). -/
def tateCoefRep (g : GalQ) : TateCoef i A E →ₗ[A] TateCoef i A E :=
  letI := tateZ2Algebra i A
  LinearMap.baseChange A (tateRep E 2 g)

theorem tateCoefRep_mk (g : GalQ) (a : A) (x : TateMod E 2) :
    tateCoefRep i A E g (tateCoefMk i A E a x) = tateCoefMk i A E a (tateRep E 2 g x) := by
  let _ := tateZ2Algebra i A
  exact LinearMap.baseChange_tmul _ a x

/-- **The matrix of `1 ⊗ ρ_T(g)` in the basis `1 ⊗ b_j`** is lane RC17's `tateMatrix E g`
reduced into `A` (through `ℤ₂ → ℤ/2^i → A`). Kind: PROVED. -/
theorem tateCoefRep_basis [E.IsElliptic] (g : GalQ) (j : Fin 2) :
    tateCoefRep i A E g (tateCoefBasis i A E j) =
      ∑ k, algebraMap (ZMod (2 ^ i)) A (PadicInt.toZModPow i (tateMatrix E g k j)) •
        tateCoefBasis i A E k := by
  rw [tateCoefBasis_apply, tateCoefRep_mk, tateRep_tateBasis, Fin.sum_univ_two,
    Fin.sum_univ_two, tateCoefMk_add_right, tateCoefMk_smul_right, tateCoefMk_smul_right,
    tateCoefBasis_apply, tateCoefBasis_apply]

/-! ### `A ⊗_ℤ E(ℚ̄)[2^i] ≃ A ⊗_{ℤ₂} T₂E` -/

/-- `a ⊗ x ↦ a ⊗ proj_i(x)`, `A ⊗_{ℤ₂} T₂E → A ⊗_ℤ E(ℚ̄)[2^i]` (well defined: `ℤ₂` acts on
`E(ℚ̄)[2^i]` and on `A` through `ℤ/2^i`). -/
def tateCoefToLevel [E.IsElliptic] : TateCoef i A E →ₗ[A] A ⊗[ℤ] TateLevel E i :=
  letI := tateZ2Algebra i A
  AlgebraTensorModule.lift
    (LinearMap.mk₂' A ℤ_[2] (fun (a : A) (x : TateMod E 2) => a ⊗ₜ[ℤ] tateProj E i x)
      (fun a b x => add_tmul a b _)
      (fun c a x => (smul_tmul' c a _).symm)
      (fun a x y => by rw [map_add, tmul_add])
      (fun c a x => by
        rw [smul_tmul', tateZ2_smul, TauCeti.TateModule.proj_smul, tate_zmod_smul,
          tate_zmod_smul, ← natCast_zsmul, ← natCast_zsmul, smul_tmul]))

theorem tateCoefToLevel_mk [E.IsElliptic] (a : A) (x : TateMod E 2) :
    tateCoefToLevel i A E (tateCoefMk i A E a x) = a ⊗ₜ[ℤ] tateProj E i x := by
  let _ := tateZ2Algebra i A
  exact AlgebraTensorModule.lift_tmul _ a x

/-- `1 ⊗ (2^i y) = 0` in `A ⊗_{ℤ₂} T₂E`. -/
theorem tatePowSub_le_ker_mk :
    letI := tateZ2Algebra i A
    tatePowSub E i ≤ LinearMap.ker (TensorProduct.mk ℤ_[2] A (TateMod E 2) 1) := by
  let _ := tateZ2Algebra i A
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_tatePowSub_iff E i).1 hx
  rw [LinearMap.mem_ker, TensorProduct.mk_apply, ← smul_tmul, tateZ2_smul, map_pow, map_ofNat]
  have h0 : (2 : ZMod (2 ^ i)) ^ i = 0 := by exact_mod_cast ZMod.natCast_self (2 ^ i)
  rw [h0, zero_smul, zero_tmul]

/-- `y ↦ 1 ⊗ x` for any lift `x ∈ T₂E` of `y ∈ E(ℚ̄)[2^i]` (through `T₂E/2^i T₂E ≃ E(ℚ̄)[2^i]`). -/
def tateLevelToCoef1 [E.IsElliptic] : TateLevel E i →+ TateCoef i A E :=
  letI := tateZ2Algebra i A
  ((tatePowSub E i).liftQ (TensorProduct.mk ℤ_[2] A (TateMod E 2) 1)
      (tatePowSub_le_ker_mk i A E)).toAddMonoidHom.comp (tateQuotEquiv E i).symm.toAddMonoidHom

theorem tateLevelToCoef1_proj [E.IsElliptic] (x : TateMod E 2) :
    tateLevelToCoef1 i A E (tateProj E i x) = tateCoefMk i A E 1 x := by
  let _ := tateZ2Algebra i A
  have h : (tateQuotEquiv E i).symm (tateProj E i x) = Submodule.Quotient.mk x :=
    (tateQuotEquiv E i).symm_apply_eq.2 (tateQuotEquiv_mk E i x).symm
  change (tatePowSub E i).liftQ (TensorProduct.mk ℤ_[2] A (TateMod E 2) 1)
    (tatePowSub_le_ker_mk i A E) ((tateQuotEquiv E i).symm (tateProj E i x)) =
      (1 : A) ⊗ₜ[ℤ_[2]] x
  rw [h, Submodule.liftQ_apply, TensorProduct.mk_apply]

/-- `a ⊗ y ↦ a ⊗ x` for any lift `x` of `y`, `A ⊗_ℤ E(ℚ̄)[2^i] → A ⊗_{ℤ₂} T₂E`. -/
def tateLevelToCoef [E.IsElliptic] : A ⊗[ℤ] TateLevel E i →ₗ[A] TateCoef i A E :=
  AlgebraTensorModule.lift
    (LinearMap.mk₂' A ℤ (fun (a : A) (y : TateLevel E i) => a • tateLevelToCoef1 i A E y)
      (fun a b y => add_smul a b _)
      (fun c a y => mul_smul c a _)
      (fun a y z => by rw [map_add, smul_add])
      (fun c a y => by rw [map_zsmul, smul_comm]))

theorem tateLevelToCoef_tmul [E.IsElliptic] (a : A) (y : TateLevel E i) :
    tateLevelToCoef i A E (a ⊗ₜ[ℤ] y) = a • tateLevelToCoef1 i A E y :=
  AlgebraTensorModule.lift_tmul _ a y

theorem tateLevelToCoef_tateCoefToLevel [E.IsElliptic] (m : TateCoef i A E) :
    tateLevelToCoef i A E (tateCoefToLevel i A E m) = m := by
  induction m using tateCoef_induction with
  | hmk a x =>
    rw [tateCoefToLevel_mk, tateLevelToCoef_tmul, tateLevelToCoef1_proj, tateCoefMk_smul, mul_one]
  | hadd m₁ m₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

theorem tateCoefToLevel_tateLevelToCoef [E.IsElliptic] (m : A ⊗[ℤ] TateLevel E i) :
    tateCoefToLevel i A E (tateLevelToCoef i A E m) = m := by
  induction m using TensorProduct.inductionOn with
  | tmul a y =>
    obtain ⟨x, rfl⟩ := tateProj_surjective E i y
    rw [tateLevelToCoef_tmul, tateLevelToCoef1_proj, tateCoefMk_smul, mul_one, tateCoefToLevel_mk]
  | add m₁ m₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]

/-- **`A ⊗_ℤ E(ℚ̄)[2^i] ≃ₗ[A] A ⊗_{ℤ₂} T₂E`** for a `ℤ/2^i`-algebra `A` (`2^i A = 0` and
`T₂E/2^i T₂E ≃ E(ℚ̄)[2^i]`, lane RC28's DEPARTURE 1 at `ℚ̄`). Kind: definition, both
compositions PROVED to be the identity. -/
def tateLevelCoefEquiv [E.IsElliptic] : (A ⊗[ℤ] TateLevel E i) ≃ₗ[A] TateCoef i A E :=
  LinearEquiv.ofLinearMap (tateLevelToCoef i A E) (tateCoefToLevel i A E)
    (LinearMap.ext (tateLevelToCoef_tateCoefToLevel i A E))
    (LinearMap.ext (tateCoefToLevel_tateLevelToCoef i A E))

theorem tateLevelCoefEquiv_tmul_proj [E.IsElliptic] (a : A) (x : TateMod E 2) :
    tateLevelCoefEquiv i A E (a ⊗ₜ[ℤ] tateProj E i x) = tateCoefMk i A E a x := by
  change tateLevelToCoef i A E _ = _
  rw [tateLevelToCoef_tmul, tateLevelToCoef1_proj, tateCoefMk_smul, mul_one]

/-- `y ↦ 1 ⊗ (lift of y)` intertwines `g` on `E(ℚ̄)[2^i]` with `1 ⊗ ρ_T(g)`. Kind: PROVED. -/
theorem tateLevelToCoef1_act [E.IsElliptic] (g : GalQ) (y : TateLevel E i) :
    tateLevelToCoef1 i A E (tateLevelAct E i g y) =
      tateCoefRep i A E g (tateLevelToCoef1 i A E y) := by
  obtain ⟨x, rfl⟩ := tateProj_surjective E i y
  rw [← tateProj_tateRep, tateLevelToCoef1_proj, tateLevelToCoef1_proj, tateCoefRep_mk]

end Coef

/-! ### The coefficient modules: `(A ⊗_ℤ E(K_S)[2^i])(α) ≃ (A ⊗_{ℤ₂} T₂E)(α)` -/

section CoefS

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
  (A : Type) [CommRing A] [Algebra (ZMod (2 ^ i)) A] (α : GKS K S →* Aˣ)

/-- **(e) `(A ⊗_ℤ E(K_S)[2^i])(α) ≃ₗ[A] A ⊗_{ℤ₂} T₂E`** (lane RC28's `CoefMod`), under
`FullTorsion K S (E⁄K) (2^i)` (GLUE, lane RC28): `a ⊗ P ↦ a ⊗ x` for any `x ∈ T₂E` lifting the
image of `P` in `E(ℚ̄)[2^i]` (`tateCoefEquiv_tmul_lift`). With `tateCoefEquiv_smul` it identifies
the `A[G_{K,S}]`-module `CoefMod A α (E(K_S)[2^i])` with `(T₂E ⊗ A)(α)` of tex 2726. -/
def tateCoefEquiv (hW : FullTorsion K S (E⁄K) (2 ^ i)) :
    CoefMod A α (TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) ≃ₗ[A] TateCoef i A E :=
  (CoefMod.equiv A α _).symm ≪≫ₗ
    LinearEquiv.baseChange ℤ A _ _ (tateTorsEquiv S E e i hW).toIntLinearEquiv ≪≫ₗ
      tateLevelCoefEquiv i A E

theorem tateCoefEquiv_tmul (hW : FullTorsion K S (E⁄K) (2 ^ i)) (a : A)
    (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) :
    tateCoefEquiv S E e i A α hW (CoefMod.equiv A α _ (a ⊗ₜ[ℤ] P)) =
      a • tateLevelToCoef1 i A E (tateTorsMap S E e i P) := by
  change tateLevelToCoef i A E (LinearEquiv.baseChange ℤ A _ _
    (tateTorsEquiv S E e i hW).toIntLinearEquiv (a ⊗ₜ[ℤ] P)) = _
  rw [LinearEquiv.baseChange_tmul, tateLevelToCoef_tmul]
  rfl

/-- **(e) On pure tensors**: `a ⊗ P ↦ a ⊗ x` for any `x ∈ T₂E` with `proj_i(x)` the image of `P`
in `E(ℚ̄)[2^i]`. Kind: PROVED. -/
theorem tateCoefEquiv_tmul_lift (hW : FullTorsion K S (E⁄K) (2 ^ i)) (a : A)
    (P : TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ)) (x : TateMod E 2)
    (hx : tateProj E i x = tateTorsMap S E e i P) :
    tateCoefEquiv S E e i A α hW (CoefMod.equiv A α _ (a ⊗ₜ[ℤ] P)) = tateCoefMk i A E a x := by
  rw [tateCoefEquiv_tmul, ← hx, tateLevelToCoef1_proj, tateCoefMk_smul, mul_one]

/-- **(e) Equivariance: the `G_{K,S}`-action on `(A ⊗_ℤ E(K_S)[2^i])(α)` is `α ⊗ ρ_T`** on
`A ⊗_{ℤ₂} T₂E`: for `σ ∈ G_{K,S}` and **any** lift `σ' ∈ Gal(K̄/K)` of `σ`,
`Φ(σ m) = α(σ) · (1 ⊗ ρ_T(tateGalToQ e σ')) Φ(m)` (tex 2726, `M_i = (T₂E ⊗ A_i)(α_i)`).
Kind: PROVED (from the GLUE `FullTorsion`, through `tateTorsMap_smul`). -/
theorem tateCoefEquiv_smul (hW : FullTorsion K S (E⁄K) (2 ^ i)) (σ : GKS K S)
    (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x))
    (m : CoefMod A α (TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ))) :
    tateCoefEquiv S E e i A α hW (σ • m) =
      ((α σ : Aˣ) : A) • tateCoefRep i A E (tateGalToQ e σ') (tateCoefEquiv S E e i A α hW m) := by
  obtain ⟨m, rfl⟩ := (CoefMod.equiv A α _).surjective m
  induction m using TensorProduct.inductionOn with
  | tmul a P =>
    rw [CoefMod.smul_tmul, tateCoefEquiv_tmul, tateCoefEquiv_tmul,
      tateTorsMap_smul S E e i σ σ' hσ', tateLevelToCoef1_act, map_smul, smul_smul]
  | add m₁ m₂ h₁ h₂ => rw [map_add, smul_add, map_add, h₁, h₂, map_add, map_add, smul_add]

/-- The basis `Φ⁻¹(1 ⊗ b_j)` of `(A ⊗_ℤ E(K_S)[2^i])(α)` (under `FullTorsion`, GLUE). -/
def tateCoefModBasis (hW : FullTorsion K S (E⁄K) (2 ^ i)) :
    Module.Basis (Fin 2) A (CoefMod A α (TorsS K S (E⁄K) ((2 ^ i : ℕ) : ℤ))) :=
  (tateCoefBasis i A E).map (tateCoefEquiv S E e i A α hW).symm

/-- **The matrix of `σ ∈ G_{K,S}` on `(A ⊗_ℤ E(K_S)[2^i])(α)`** in the basis `Φ⁻¹(1 ⊗ b_j)` is
`α(σ) · (tateMatrix E (e σ' e⁻¹) reduced into A)`, for any lift `σ'` of `σ`. Kind: PROVED. -/
theorem tateCoefModBasis_smul (hW : FullTorsion K S (E⁄K) (2 ^ i)) (σ : GKS K S)
    (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x)) (j : Fin 2) :
    σ • tateCoefModBasis S E e i A α hW j =
      ∑ k, (((α σ : Aˣ) : A) *
        algebraMap (ZMod (2 ^ i)) A (PadicInt.toZModPow i (tateMatrix E (tateGalToQ e σ') k j))) •
          tateCoefModBasis S E e i A α hW k := by
  apply (tateCoefEquiv S E e i A α hW).injective
  rw [tateCoefEquiv_smul S E e i A α hW σ σ' hσ', map_sum, tateCoefModBasis,
    Module.Basis.map_apply, LinearEquiv.apply_symm_apply, tateCoefRep_basis, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, smul_smul]

end CoefS

/-! ### The actual coefficient modules `M_i = Mcoef K S (E⁄K) i α` -/

section Mcoef

variable {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
  (E : WeierstrassCurve ℚ) [E.IsElliptic] (e : AlgebraicClosure K ≃ₐ[ℚ] Qbar) (i : ℕ)
  (α : GKS K S →* (Acoef i)ˣ)

/-- **(e) for the actual `M_i`: `M_i = Mcoef K S (E⁄K) i α ≃ₗ[A_i] A_i ⊗_{ℤ₂} T₂E`** (tex 2726;
`A_i = Acoef i`, lane RC10/RC28), under `FullTorsion K S (E⁄K) (2^i)` (GLUE). This removes lane
RC28's DEPARTURE 1. -/
def tateMcoefEquiv (hW : FullTorsion K S (E⁄K) (2 ^ i)) :
    Mcoef K S (E⁄K) i α ≃ₗ[Acoef i] TateCoef i (Acoef i) E :=
  tateCoefEquiv S E e i (Acoef i) α hW

/-- **(e) `M_i = (T₂E ⊗ A_i)(α)` as `A_i[G_{K,S}]`-modules** (tex 2726): for `σ ∈ G_{K,S}` and any
lift `σ'`, `Φ(σ m) = α(σ) · (1 ⊗ ρ_T(tateGalToQ e σ')) Φ(m)`. Kind: PROVED (GLUE `FullTorsion`). -/
theorem tateMcoefEquiv_smul (hW : FullTorsion K S (E⁄K) (2 ^ i)) (σ : GKS K S)
    (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x))
    (m : Mcoef K S (E⁄K) i α) :
    tateMcoefEquiv S E e i α hW (σ • m) =
      ((α σ : (Acoef i)ˣ) : Acoef i) •
        tateCoefRep i (Acoef i) E (tateGalToQ e σ') (tateMcoefEquiv S E e i α hW m) :=
  tateCoefEquiv_smul S E e i (Acoef i) α hW σ σ' hσ' m

/-- **The matrix of `σ` on `M_i`** in the basis `Φ⁻¹(1 ⊗ b_j)`: `α_i(σ) · ρ_T(e σ' e⁻¹) mod 2^i`
(lane RC17's `tateMatrix`). Kind: PROVED (GLUE `FullTorsion`). -/
theorem tateMcoefBasis_smul (hW : FullTorsion K S (E⁄K) (2 ^ i)) (σ : GKS K S)
    (σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ' : ∀ x : KS K S, σ' (inclS K S x) = inclS K S (galS K S σ x)) (j : Fin 2) :
    σ • tateCoefModBasis S E e i (Acoef i) α hW j =
      ∑ k, (((α σ : (Acoef i)ˣ) : Acoef i) * algebraMap (ZMod (2 ^ i)) (Acoef i)
        (PadicInt.toZModPow i (tateMatrix E (tateGalToQ e σ') k j))) •
          tateCoefModBasis S E e i (Acoef i) α hW k :=
  tateCoefModBasis_smul S E e i (Acoef i) α hW σ σ' hσ' j

/-- Non-vacuity: for the manuscript's `E_ℓ` at `i = 1`, every `K`, `S` and every character `α`,
the identification `M_1 ≃ A_1 ⊗_{ℤ₂} T₂E_ℓ` exists (with `e = tateAlgEquiv K`). -/
example {ℓ : ℕ} (hℓ : 0 < ℓ) (α : GKS K S →* (Acoef 1)ˣ) :
    haveI := ecurve_isElliptic hℓ
    Nonempty (Mcoef K S ((ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)⁄K) 1 α ≃ₗ[Acoef 1]
      TateCoef 1 (Acoef 1) (ZInQ.Contrib.CloudB3RC53.Ecurve ℓ)) :=
  haveI := ecurve_isElliptic hℓ
  ⟨tateMcoefEquiv S _ (tateAlgEquiv K) 1 α (tate_fullTorsion_ecurve hℓ)⟩

end Mcoef

end ZInQ.Manuscript.RC.KummerMaps
