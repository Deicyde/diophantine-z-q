import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerAnn
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthKummer

/-!
# Lane RC29 (round 2, item 1): the decomposition data for the actual Kummer conditions

Manuscript `diophantine_zq.tex`, tex 2724–2726 (`A_i = (ℤ/2^i)[t]/t^i`, `M_i = (E[2^i] ⊗ A_i)(α)`),
tex 3429–3432 ("derived coefficient extension defines the scalar `A_i` condition").

`KummerAnn.lean` proves the exact annihilator for an extended Kummer condition from the one for
`B[2^i]`, given decomposition data of the coefficient modules along a family of scalars. This file
constructs those data for the actual modules `M_i(α) = (A_i ⊗ E(K_S)[2^i])(α)` at a place `v`
where `α = χ_h` on the decomposition group:

* `kannZSmul`, `kannCoordTens`: the `ℤ/m`-coordinates `a ⊗ x ↦ c(a) • x` on `A ⊗_ℤ T` for an
  `m`-torsion group `T`; `kannCoordTens_recon`: `x = ∑_k b_k • (1 ⊗ c_k(x))` for a basis `b` of
  `A` over `ℤ/m` with coordinate functions `c_k`.
* `kannPB`: the power basis `1, t, …, t^{i−1}` of `A_i` over `ℤ/2^i`.

Kinds: all declarations are definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open scoped TensorProduct

/-! ### `ℤ/m`-coordinates on `A ⊗_ℤ T` -/

section Coord

variable {m : ℕ} [NeZero m]

/-- Definition. The action `z • y = z.val • y` of `ℤ/m` on an `m`-torsion group, as a biadditive
map. -/
def kannZSmul {D : Type} [AddCommGroup D] (hD : ∀ y : D, m • y = 0) : ZMod m →+ D →+ D where
  toFun z :=
    { toFun := fun y => z.val • y
      map_zero' := nsmul_zero _
      map_add' := fun y y' => nsmul_add _ _ _ }
  map_zero' := by
    ext y
    simp
  map_add' z z' := by
    ext y
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.add_apply]
    rw [ZMod.val_add, ← nsmul_eq_mod_nsmul _ (hD y), add_nsmul]

theorem kannZSmul_apply {D : Type} [AddCommGroup D] (hD : ∀ y : D, m • y = 0) (z : ZMod m)
    (y : D) : kannZSmul hD z y = z.val • y :=
  rfl

variable {A : Type} [CommRing A] {T D : Type} [AddCommGroup T] [AddCommGroup D]

/-- Definition. **The coordinate map** `A ⊗_ℤ T → D`, `a ⊗ x ↦ c(a) • f(x)`, for an additive
`c : A → ℤ/m`, an additive `f : T → D` and an `m`-torsion group `D`. -/
def kannCoordTens (hD : ∀ y : D, m • y = 0) (c : A →+ ZMod m) (f : T →+ D) : A ⊗[ℤ] T →+ D :=
  TensorProduct.liftAddHom
    { toFun := fun a => (kannZSmul hD (c a)).comp f
      map_zero' := by
        ext x
        simp
      map_add' := fun a a' => by
        ext x
        simp only [map_add, AddMonoidHom.comp_apply, AddMonoidHom.add_apply] }
    (fun r a x => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.comp_apply, map_zsmul,
        AddMonoidHom.zsmul_apply])

theorem kannCoordTens_tmul (hD : ∀ y : D, m • y = 0) (c : A →+ ZMod m) (f : T →+ D) (a : A)
    (x : T) : kannCoordTens hD c f (a ⊗ₜ x) = (c a).val • f x :=
  rfl

/-- PROVED. **Reconstruction from the coordinates**: for a basis `b` of `A` over `ℤ/m` and an
`m`-torsion group `T`, every `x ∈ A ⊗_ℤ T` is `∑_k b_k • (1 ⊗ c_k(x))`, `c_k` the coordinate
functions of `b`. -/
theorem kannCoordTens_recon [Algebra (ZMod m) A] {ιb : Type} [Fintype ιb]
    (b : Module.Basis ιb (ZMod m) A) (hT : ∀ y : T, m • y = 0) (x : A ⊗[ℤ] T) :
    ∑ k, b k • ((1 : A) ⊗ₜ[ℤ] kannCoordTens hT (b.coord k).toAddMonoidHom (AddMonoidHom.id T) x) =
      x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, TensorProduct.tmul_add, smul_add, Finset.sum_add_distrib, hx, hy]
  | tmul a t =>
    simp only [kannCoordTens_tmul, AddMonoidHom.id_apply]
    have hn : ∀ (n : ℕ) (x : A) (y : T), x ⊗ₜ[ℤ] (n • y) = (n • x) ⊗ₜ[ℤ] y := by
      intro n x y
      induction n with
      | zero => simp
      | succ n ih => rw [succ_nsmul, succ_nsmul, TensorProduct.tmul_add, TensorProduct.add_tmul, ih]
    have hz : ∀ (z : ZMod m) (x : A), z.val • x = z • x := by
      intro z x
      rw [nsmul_eq_mul, Algebra.smul_def, ← map_natCast (algebraMap (ZMod m) A),
        ZMod.natCast_zmod_val]
    have h1 : ∀ k, b k • ((1 : A) ⊗ₜ[ℤ] (((b.coord k).toAddMonoidHom a).val • t)) =
        ((b.coord k a) • b k) ⊗ₜ[ℤ] t := by
      intro k
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hn, hz]
      rfl
    simp only [h1, ← TensorProduct.sum_tmul, Module.Basis.coord_apply, Module.Basis.sum_repr]

end Coord

/-! ### The power basis of `A_i` -/

open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef) in
/-- Definition (tex 2724–2725). **The power basis `1, t, …, t^{i−1}` of `A_i = (ℤ/2^i)[t]/t^i`**
over `ℤ/2^i` (Mathlib's `AdjoinRoot.powerBasis'` for the monic `t^i`). -/
def kannPB (i : ℕ) : PowerBasis (ZMod (2 ^ i)) (Acoef i) :=
  AdjoinRoot.powerBasis' (Polynomial.monic_X_pow i)

/-! ### The actual modules at a place where `α = χ_h` -/

section Actual

open NumberField IsDedekindDomain
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (v : Places K S)

/-- Definition. **The identification `e = j⁻¹ ∘ φ_q : B(K̄_v)[2^i] ≃ E(K_{S₀})[2^i]`** underlying the
Kummer coefficient map (`ι_v t = 1 ⊗ e t`, `kummerIotaBase`). -/
def kannE : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) ≃+
    TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) :=
  (twistTors (W.baseChange (v.1.adicCompletion K)) (algebraMap K (v.1.adicCompletion K) h)
      two_ne_zero (localSqrt_ne_zero s hs0 v.1) (localSqrt_sq s hs v.1) (2 ^ i)).trans
    (compTorsEquiv W (2 ^ i) hFull v.1).symm

/-- PROVED. The Kummer coefficient map is `t ↦ 1 ⊗ e t`. -/
theorem kummerIotaBase_eq_kannE (α' : GKS K S₀ →* (Acoef i)ˣ)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kummerIotaBase (S := S₀) W i s hs hs0 α' hFull v.1 t =
      oneTmul (Acoef i) α' (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) (kannE W i s hs hs0 hFull v t) :=
  rfl

/-- PROVED. **Equivariance of `e`**: `e(σ t) = χ_h(σ) · p_v(σ) e(t)` (from `twistTors_smul`,
`compTorsEquiv_symm_smul`, `twistSign_localSqrt`). -/
theorem kannE_smul (σ : Gloc K v.1)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kannE W i s hs hs0 hFull v (σ • t) =
      ((quadChar s hs hs0 (locMap K S₀ v.1 σ) : ℤˣ) : ℤ) •
        (locMap K S₀ v.1 σ • kannE W i s hs hs0 hFull v t) := by
  change (compTorsEquiv W (2 ^ i) hFull v.1).symm (twistTors _ _ _ _ _ (2 ^ i) (σ • t)) = _
  rw [twistTors_smul, map_zsmul, compTorsEquiv_symm_smul, twistSign_localSqrt s hs hs0 v.1 σ]
  rfl

/-- PROVED. **Equivariance of `e⁻¹`**: `e⁻¹(p_v(σ) y) = χ_h(σ) · σ e⁻¹(y)`. -/
theorem kannE_symm_smul (σ : Gloc K v.1) (y : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    (kannE W i s hs hs0 hFull v).symm (locMap K S₀ v.1 σ • y) =
      ((quadChar s hs hs0 (locMap K S₀ v.1 σ) : ℤˣ) : ℤ) •
        (σ • (kannE W i s hs hs0 hFull v).symm y) := by
  apply (kannE W i s hs hs0 hFull v).injective
  rw [AddEquiv.apply_symm_apply, map_zsmul, kannE_smul, AddEquiv.apply_symm_apply, smul_smul,
    ← Units.val_mul, ← sq, Int.units_sq, Units.val_one, one_smul]

/-- PROVED. `E(K_{S₀})[2^i]` is killed by `2^i`. -/
theorem kann_torsS_nsmul (y : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) : (2 ^ i) • y = 0 :=
  Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.1 y.2)

/-- Definition. **The coordinate maps of `M_i(α')`**:
`π_k : (A_i ⊗ E(K_{S₀})[2^i])(α') → B(K̄_v)[2^i]`, `a ⊗ x ↦ e⁻¹(c_k(a) x)`, for the coordinate
functions `c_k` of the power basis of `A_i`. -/
def kannPiBase (α' : GKS K S₀ →* (Acoef i)ˣ) (k : Fin (kannPB i).dim) :
    Mcoef K S₀ W i α' →+ TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) :=
  (kannE W i s hs hs0 hFull v).symm.toAddMonoidHom.comp
    ((kannCoordTens (kann_torsS_nsmul W i) ((kannPB i).basis.coord k).toAddMonoidHom
        (AddMonoidHom.id _)).comp
      (CoefMod.equiv (Acoef i) α' (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))).symm.toLinearMap.toAddMonoidHom)

theorem kannPiBase_tmul (α' : GKS K S₀ →* (Acoef i)ˣ) (k : Fin (kannPB i).dim) (a : Acoef i)
    (y : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    kannPiBase W i s hs hs0 hFull v α' k (CoefMod.equiv (Acoef i) α' _ (a ⊗ₜ y)) =
      ((kannPB i).basis.coord k a).val • (kannE W i s hs hs0 hFull v).symm y := by
  change (kannE W i s hs hs0 hFull v).symm (((kannPB i).basis.coord k a).val • y) = _
  rw [map_nsmul]

/-- PROVED. `B(K̄_v)[2^i]` is killed by `2^i`. -/
theorem kann_torsAlg_nsmul {F : Type} [Field F] {B : WeierstrassCurve F} {m : ℕ}
    (t : TorsAlg F B m) : m • t = 0 :=
  Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.1 t.2)

/-- PROVED. **Equivariance of the coordinate maps** on the decomposition group, where the
character `α'` of `M_i(α')` is `χ_h` (`IsLocallyQuadAt`): `π_k(p_v(σ) x) = σ π_k(x)`. The two signs
`χ_h(σ)` (from `α'` and from `e⁻¹`) cancel. -/
theorem kannPiBase_smul (α' : GKS K S₀ →* (Acoef i)ˣ)
    (hα' : IsLocallyQuadAt (S := S₀) i α' (quadChar s hs hs0) v.1) (k : Fin (kannPB i).dim)
    (σ : Gloc K v.1) (x : Mcoef K S₀ W i α') :
    kannPiBase W i s hs hs0 hFull v α' k (locMap K S₀ v.1 σ • x) =
      σ • kannPiBase W i s hs hs0 hFull v α' k x := by
  obtain ⟨x', rfl⟩ : ∃ x' : Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ),
      CoefMod.equiv (Acoef i) α' _ x' = x := ⟨x, rfl⟩
  induction x' using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul a y =>
    rw [CoefMod.smul_tmul, kannPiBase_tmul, kannPiBase_tmul, hα' σ, kannE_symm_smul]
    set χ : ℤ := ((quadChar s hs hs0 (locMap K S₀ v.1 σ) : ℤˣ) : ℤ) with hχ
    have hχ2 : χ * χ = 1 := by
      rw [hχ, ← Units.val_mul, ← sq, Int.units_sq, Units.val_one]
    have hcoef : (kannPB i).basis.coord k
        (((intUnitsTo (Acoef i) (quadChar s hs hs0 (locMap K S₀ v.1 σ)) : (Acoef i)ˣ) :
          Acoef i) * a) = χ • (kannPB i).basis.coord k a := by
      rw [← map_zsmul]
      congr 1
      rw [zsmul_eq_mul]
      rfl
    rw [hcoef]
    have hD := kann_torsAlg_nsmul (F := v.1.adicCompletion K) (B := localTwist W h v.1)
      (m := 2 ^ i)
    have h1 : (χ • (kannPB i).basis.coord k a).val •
        (χ • σ • (kannE W i s hs hs0 hFull v).symm y) =
        kannZSmul hD (χ • (kannPB i).basis.coord k a)
          (χ • σ • (kannE W i s hs hs0 hFull v).symm y) := rfl
    rw [h1]
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_smul, hχ2, one_smul]
    rw [kannZSmul_apply, smul_comm]

/-- Definition. The coordinate maps on the local module `M_i(α')` (inflated from `S₀`, with
`G_{K_v}` acting through `p_v`): the same maps as `kannPiBase`. -/
def kannPi (α' : GKS K S₀ →* (Acoef i)ˣ) (k : Fin (kannPB i).dim) :
    ResMod (locMap K S v.1) (MinS hS W i α') →+
      TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) :=
  kannPiBase W i s hs hs0 hFull v α' k

/-- PROVED. **The coordinate maps are `G_{K_v}`-equivariant** on the local module (lane RC26's
`locMap_compat`). -/
theorem kannPi_smul (α' : GKS K S₀ →* (Acoef i)ˣ)
    (hα' : IsLocallyQuadAt (S := S₀) i α' (quadChar s hs hs0) v.1) (k : Fin (kannPB i).dim)
    (σ : Gloc K v.1) (x : ResMod (locMap K S v.1) (MinS hS W i α')) :
    kannPi hS W i s hs hs0 hFull v α' k (σ • x) = σ • kannPi hS W i s hs hs0 hFull v α' k x := by
  change kannPiBase W i s hs hs0 hFull v α' k (inflMap K hS (locMap K S v.1 σ) •
    (show Mcoef K S₀ W i α' from x)) = _
  rw [locMap_compat K hS v.1 σ]
  exact kannPiBase_smul W i s hs hs0 hFull v α' hα' k σ x

/-- PROVED. **Reconstruction**: `x = ∑_k t^k • ι_v(π_k x)` on the local module `M_i(α')`. -/
theorem kannPi_recon (α' : GKS K S₀ →* (Acoef i)ˣ)
    (x : ResMod (locMap K S v.1) (MinS hS W i α')) :
    ∑ k, (kannPB i).basis k • kummerIotaS hS W i s hs hs0 α' hFull v
      (kannPi hS W i s hs hs0 hFull v α' k x) = x := by
  refine Eq.trans ?_ (kannCoordTens_recon (kannPB i).basis (kann_torsS_nsmul W i)
    (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x))
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  change oneTmul (Acoef i) α' _ ((kannE W i s hs hs0 hFull v)
    ((kannE W i s hs hs0 hFull v).symm _)) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- PROVED. `π_k ∘ ι_v` is multiplication by the integer `c_k(1)`. -/
theorem kannPi_iota (α' : GKS K S₀ →* (Acoef i)ˣ) (k : Fin (kannPB i).dim)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kannPi hS W i s hs hs0 hFull v α' k (kummerIotaS hS W i s hs hs0 α' hFull v t) =
      (((kannPB i).basis.coord k 1).val : ℤ) • t := by
  change kannPiBase W i s hs hs0 hFull v α' k
    (CoefMod.equiv (Acoef i) α' _ ((1 : Acoef i) ⊗ₜ kannE W i s hs hs0 hFull v t)) = _
  rw [kannPiBase_tmul, AddEquiv.symm_apply_apply, natCast_zsmul]

variable (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))

/-- PROVED. **The coordinates of the Weil pairing, left slot** (RC28's `weilA_tmul`):
`c_k(weilA(1 ⊗ y, x)) = weilS(y, c_k(x))`. -/
theorem kann_coord_weilA_left (k : Fin (kannPB i).dim) (y : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))
    (x : Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    (kannPB i).basis.coord k (weilA (S := S₀) W hμ₀ (Acoef i) ((1 : Acoef i) ⊗ₜ y) x) =
      weilS (S := S₀) W hμ₀ y (kannCoordTens (kann_torsS_nsmul W i)
        ((kannPB i).basis.coord k).toAddMonoidHom (AddMonoidHom.id _) x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul a t =>
    rw [weilA_tmul, one_mul, kannCoordTens_tmul, AddMonoidHom.id_apply, map_nsmul, mul_comm,
      ← Algebra.smul_def, map_smul, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact mul_comm _ _

/-- PROVED. **The coordinates of the Weil pairing, right slot**:
`c_k(weilA(x, 1 ⊗ y)) = weilS(c_k(x), y)`. -/
theorem kann_coord_weilA_right (k : Fin (kannPB i).dim) (y : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))
    (x : Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    (kannPB i).basis.coord k (weilA (S := S₀) W hμ₀ (Acoef i) x ((1 : Acoef i) ⊗ₜ y)) =
      weilS (S := S₀) W hμ₀ (kannCoordTens (kann_torsS_nsmul W i)
        ((kannPB i).basis.coord k).toAddMonoidHom (AddMonoidHom.id _) x) y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply, hx, hx']
  | tmul a t =>
    rw [weilA_tmul, mul_one, kannCoordTens_tmul, AddMonoidHom.id_apply, map_nsmul,
      AddMonoidHom.nsmul_apply, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, nsmul_eq_mul,
      ZMod.natCast_zmod_val]
    exact mul_comm _ _

/-- Definition. **The coefficient pairing `ψ₀` on `B(K̄_v)[2^i]`**: `ψ₀(t₁, t₂) = weilS(e t₁, e t₂)`
(RC28's `weilS`, the Weil pairing over `K̄` read in `ℤ/2^i` through `ζ`), with values in
`ℤ/2^i(1)`. -/
def kannPsi0 : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →ₗ[ℤ]
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →ₗ[ℤ] ZMod (2 ^ i) :=
  LinearMap.mk₂ ℤ
    (fun t₁ t₂ => weilS (S := S₀) W hμ₀ (kannE W i s hs hs0 hFull v t₁)
      (kannE W i s hs hs0 hFull v t₂))
    (fun t₁ t₁' t₂ => by simp only [map_add, AddMonoidHom.add_apply])
    (fun c t₁ t₂ => by simp only [map_zsmul, AddMonoidHom.zsmul_apply])
    (fun t₁ t₂ t₂' => by simp only [map_add])
    (fun c t₁ t₂ => by simp only [map_zsmul])

theorem kannPsi0_apply (t₁ t₂ : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kannPsi0 W i s hs hs0 hFull v hμ₀ t₁ t₂ =
      weilS (S := S₀) W hμ₀ (kannE W i s hs hs0 hFull v t₁) (kannE W i s hs hs0 hFull v t₂) :=
  rfl

/-- Definition. `ψ₀` with values in the local module `ℤ/2^i(1)` (inflated from `S₀`). -/
def kannPsi : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →ₗ[ℤ]
    TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) →ₗ[ℤ]
      ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀)) :=
  kannPsi0 W i s hs hs0 hFull v hμ₀

/-- Definition. **The coordinate maps of `A_i(1)`**: `τ_k = c_k : A_i(1) → ℤ/2^i(1)`. -/
def kannTau (k : Fin (kannPB i).dim) :
    ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) →+
      ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀)) :=
  ((kannPB i).basis.coord k).toAddMonoidHom

/-- PROVED. The coordinate maps of `A_i(1)` are equivariant (the cyclotomic action is by
scalars of `ℤ/2^i`). -/
theorem kannTau_smul (k : Fin (kannPB i).dim) (σ : Gloc K v.1)
    (w : ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) :
    kannTau hS i v hμ₀ k (σ • w) = σ • kannTau hS i v hμ₀ k w := by
  change (kannPB i).basis.coord k
      (algebraMap (ZMod (2 ^ i)) (Acoef i) (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
        (show Acoef i from w)) =
    algebraMap (ZMod (2 ^ i)) (ZMod (2 ^ i)) (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
      (kannPB i).basis.coord k (show Acoef i from w)
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rfl

/-- Definition. **The inclusion `j : ℤ/2^i(1) → A_i(1)`** (`algebraMap`). -/
def kannJ : ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀)) →+
    ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) :=
  (algebraMap (ZMod (2 ^ i)) (Acoef i)).toAddMonoidHom

/-- PROVED. `j` is equivariant. -/
theorem kannJ_smul (σ : Gloc K v.1)
    (w : ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀))) :
    kannJ hS i v hμ₀ (σ • w) = σ • kannJ hS i v hμ₀ w := by
  change algebraMap (ZMod (2 ^ i)) (Acoef i)
      (algebraMap (ZMod (2 ^ i)) (ZMod (2 ^ i)) (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
        (show ZMod (2 ^ i) from w)) =
    algebraMap (ZMod (2 ^ i)) (Acoef i) (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
      algebraMap (ZMod (2 ^ i)) (Acoef i) (show ZMod (2 ^ i) from w)
  rw [map_mul]
  rfl

/-- PROVED. **Reconstruction in `A_i(1)`**: `w = ∑_k t^k • j(τ_k w)`. -/
theorem kannTau_recon (w : ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) :
    ∑ k, (kannPB i).basis k • kannJ hS i v hμ₀ (kannTau hS i v hμ₀ k w) = w := by
  change ∑ k, (kannPB i).basis k * algebraMap (ZMod (2 ^ i)) (Acoef i)
      ((kannPB i).basis.coord k (show Acoef i from w)) = (show Acoef i from w)
  conv_rhs => rw [← (kannPB i).basis.sum_repr (show Acoef i from w)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← Algebra.smul_def, Module.Basis.coord_apply]

/-- Definition. **The local Weil pairing at `v`** on the actual modules:
`M_i(α) × M_i(α⁻¹) → A_i(1)` (lane RC28's `weilPairingM`, inflated from `S₀`, with `G_{K_v}`
acting through `p_v`) — the coefficient pairing of the local cup product `orthUrPair` at `v`. -/
abbrev kannBeta (α : GKS K S₀ →* (Acoef i)ˣ) :=
  resPairing (Acoef i) (GKS K S) (orthInflPair hS (Acoef i) (weilPairingM (S := S₀) W hμ₀ (Acoef i) α))
    (locMap K S v.1)

/-- PROVED. The local Weil pairing is `G_{K_v}`-equivariant. -/
theorem kannBeta_smul (α : GKS K S₀ →* (Acoef i)ˣ) (σ : Gloc K v.1)
    (a : ResMod (locMap K S v.1) (MinS hS W i α))
    (b : ResMod (locMap K S v.1) (MinS hS W i (charInv α))) :
    kannBeta hS W i v hμ₀ α (σ • a) (σ • b) = σ • kannBeta hS W i v hμ₀ α a b :=
  weilPairingM_smul (S := S₀) W hμ₀ (Acoef i) α (inflMap K hS (locMap K S v.1 σ)) a b

/-- PROVED. `τ_k(β(ι t, x)) = ψ₀(t, π_k x)` (the compatibility `hτβ` of `KummerAnn.lean`). -/
theorem kannTau_beta_left (α : GKS K S₀ →* (Acoef i)ˣ) (k : Fin (kannPB i).dim)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i))
    (x : ResMod (locMap K S v.1) (MinS hS W i (charInv α))) :
    kannTau hS i v hμ₀ k (kannBeta hS W i v hμ₀ α (kummerIotaS hS W i s hs hs0 α hFull v t) x) =
      kannPsi hS W i s hs hs0 hFull v hμ₀ t (kannPi hS W i s hs hs0 hFull v (charInv α) k x) := by
  change (kannPB i).basis.coord k (weilA (S := S₀) W hμ₀ (Acoef i)
      ((1 : Acoef i) ⊗ₜ kannE W i s hs hs0 hFull v t)
      (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x)) =
    weilS (S := S₀) W hμ₀ (kannE W i s hs hs0 hFull v t) (kannE W i s hs hs0 hFull v
      ((kannE W i s hs hs0 hFull v).symm (kannCoordTens (kann_torsS_nsmul W i)
        ((kannPB i).basis.coord k).toAddMonoidHom (AddMonoidHom.id _)
          (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x))))
  rw [AddEquiv.apply_symm_apply]
  exact kann_coord_weilA_left W i hμ₀ k _ _

/-- PROVED. `τ_k(β(x, ι' t)) = ψ₀(π_k x, t)` (the compatibility `hτβ'` of `KummerAnn.lean`). -/
theorem kannTau_beta_right (α : GKS K S₀ →* (Acoef i)ˣ) (k : Fin (kannPB i).dim)
    (x : ResMod (locMap K S v.1) (MinS hS W i α))
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    kannTau hS i v hμ₀ k (kannBeta hS W i v hμ₀ α x
        (kummerIotaS hS W i s hs hs0 (charInv α) hFull v t)) =
      kannPsi hS W i s hs hs0 hFull v hμ₀ (kannPi hS W i s hs hs0 hFull v α k x) t := by
  change (kannPB i).basis.coord k (weilA (S := S₀) W hμ₀ (Acoef i)
      (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x)
      ((1 : Acoef i) ⊗ₜ kannE W i s hs hs0 hFull v t)) =
    weilS (S := S₀) W hμ₀ (kannE W i s hs hs0 hFull v
      ((kannE W i s hs hs0 hFull v).symm (kannCoordTens (kann_torsS_nsmul W i)
        ((kannPB i).basis.coord k).toAddMonoidHom (AddMonoidHom.id _)
          (show Acoef i ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x))))
      (kannE W i s hs hs0 hFull v t)
  rw [AddEquiv.apply_symm_apply]
  exact kann_coord_weilA_right W i hμ₀ k _ _

variable [DecidableEq (v.1.adicCompletion K)] [(localTwist W h v.1).IsElliptic]

/-- PROVED (tex 3423, 3429–3432, 3439–3445). **The exact annihilator for the actual Kummer
conditions at `v`** (the direction lane RC29's per-place duality uses): if the Kummer image of
`B(K_v)` (`B = E^{(h)}` over `K_v`) is its own annihilator for the flipped coefficient pairing
`ψ₀ᵗ` (hypothesis `hannF`, trace-free form), then a `1`-cocycle `y` of `C^•_cont(G_{K_v}, M_i(α))`
whose cup products `y ∪ ι'_v(κ_Q)` with the Kummer cocycles of the dual condition are all
coboundaries lies in the degree-one term `kummerZ' ⊔ B¹` of the actual Kummer condition. -/
theorem kannActual_ann (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (hannF : ∀ y : contCochain ℤ (Gloc K v.1)
        (TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) 1,
      contD ℤ _ _ 1 y = 0 →
      (∀ P : (localTwist W h v.1).toAffine.Point,
        contCup (kannPsi hS W i s hs hs0 hFull v hμ₀).flip
          (kann_contPair (kannPsi hS W i s hs hs0 hFull v hμ₀).flip) 1 1 2 rfl
          (kummerCocycle _ _ (2 ^ i) P) y ∈
            LinearMap.range (contD ℤ (Gloc K v.1)
              (ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀))) 1)) →
      ∃ P : (localTwist W h v.1).toAffine.Point,
        y - kummerCocycle _ _ (2 ^ i) P ∈ contB1 ℤ (Gloc K v.1) _)
    (y : contCochain (Acoef i) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W i α)) 1)
    (hy : contD (Acoef i) (Gloc K v.1) _ 1 y = 0)
    (hcup : ∀ Q : (localTwist W h v.1).toAffine.Point,
      contCup (kannBeta hS W i v hμ₀ α) (kann_contPair (kannBeta hS W i v hμ₀ α)) 1 1 2 rfl y
        (kummerCocycleIn (kummerIotaS hS W i s hs hs0 (charInv α) hFull v) (1 : Acoef i) Q) ∈
          LinearMap.range (contD (Acoef i) (Gloc K v.1)
            (ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) 1)) :
    y ∈ kummerZ' (Acoef i) (kummerIotaS hS W i s hs hs0 α hFull v) ⊔
      contB1 (Acoef i) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W i α)) :=
  kannCoef_ann_left (kannBeta hS W i v hμ₀ α) (kannPsi hS W i s hs hs0 hFull v hμ₀)
    (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
    (kannPB i).basis hannF (kannBeta_smul hS W i v hμ₀ α)
    (kummerIotaS_smul hS W i s hs hs0 α hFull v hα)
    (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα))
    (kannPi hS W i s hs hs0 hFull v α) (fun k σ x => kannPi_smul hS W i s hs hs0 hFull v α hα k σ x)
    (kannPi_recon hS W i s hs hs0 hFull v α) (kannTau hS i v hμ₀)
    (fun k σ w => kannTau_smul hS i v hμ₀ k σ w)
    (fun k x t => kannTau_beta_right hS W i s hs hs0 hFull v hμ₀ α k x t) y hy hcup

/-- PROVED (tex 3423, 3439–3445). **Isotropy of the actual Kummer conditions at `v`**: if the
Kummer image of `B(K_v)` is isotropic for `ψ₀` (hypothesis `hiso₀`), the cup product of any
element of the degree-one term of the actual Kummer condition of `M_i(α)` with any element of that
of `M_i(α⁻¹)` is a coboundary. -/
theorem kannActual_iso (α : GKS K S₀ →* (Acoef i)ˣ) [IsOpenKer α]
    (hα : IsLocallyQuadAt (S := S₀) i α (quadChar s hs hs0) v.1)
    (hiso₀ : ∀ P Q : (localTwist W h v.1).toAffine.Point,
      contCup (kannPsi hS W i s hs hs0 hFull v hμ₀)
        (kann_contPair (kannPsi hS W i s hs hs0 hFull v hμ₀)) 1 1 2 rfl
        (kummerCocycle _ _ (2 ^ i) P) (kummerCocycle _ _ (2 ^ i) Q) ∈
          LinearMap.range (contD ℤ (Gloc K v.1)
            (ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀))) 1))
    {u : contCochain (Acoef i) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W i α)) 1}
    (hu : u ∈ kummerZ' (Acoef i) (kummerIotaS hS W i s hs hs0 α hFull v) ⊔
      contB1 (Acoef i) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W i α)))
    {u' : contCochain (Acoef i) (Gloc K v.1)
      (ResMod (locMap K S v.1) (MinS hS W i (charInv α))) 1}
    (hu' : u' ∈ kummerZ' (Acoef i) (kummerIotaS hS W i s hs hs0 (charInv α) hFull v) ⊔
      contB1 (Acoef i) (Gloc K v.1) (ResMod (locMap K S v.1) (MinS hS W i (charInv α)))) :
    contCup (kannBeta hS W i v hμ₀ α) (kann_contPair (kannBeta hS W i v hμ₀ α)) 1 1 2 rfl u u' ∈
      LinearMap.range (contD (Acoef i) (Gloc K v.1)
        (ResMod (locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) 1) :=
  kannCoef_iso (kannBeta hS W i v hμ₀ α) (kannPsi hS W i s hs hs0 hFull v hμ₀)
    (kummerIotaS hS W i s hs hs0 α hFull v) (kummerIotaS hS W i s hs hs0 (charInv α) hFull v)
    (kannPB i).basis hiso₀ (kannBeta_smul hS W i v hμ₀ α)
    (kummerIotaS_smul hS W i s hs hs0 α hFull v hα)
    (kummerIotaS_smul hS W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα))
    (kannPi hS W i s hs hs0 hFull v (charInv α))
    (fun k σ x => kannPi_smul hS W i s hs hs0 hFull v (charInv α) (isLocallyQuadAt_charInv hα) k σ x)
    (fun k => (((kannPB i).basis.coord k 1).val : ℤ))
    (fun k t => kannPi_iota hS W i s hs hs0 hFull v (charInv α) k t)
    (kannTau hS i v hμ₀)
    (fun k t x => kannTau_beta_left hS W i s hs hs0 hFull v hμ₀ α k t x)
    (kannJ hS i v hμ₀) (kannJ_smul hS i v hμ₀) (kannTau_recon hS i v hμ₀) hu hu'

end Actual

end ZInQ.Manuscript.RC.KummerMaps
