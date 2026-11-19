import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerMilne
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Binary

/-!
# Lane RC29 (round 3): Kummer annihilators over a coefficient ring with a finite basis

Manuscript `diophantine_zq.tex` (11/5):

* tex 2724–2730: "`A_i = (ℤ/2^iℤ)[t]/t^i`, `M_i = (T_2E ⊗ A_i)(χ_hΨ_i)`. For a fixed binary group
  `G`, use `A_i[G]` and the universal quadratic character."
* tex 2790–2793: "Let `R_i = A_i` in the scalar construction and `R_i = A_i[G]` in the binary
  construction. Write `α_i = χ_hΨ_i`, respectively `α_i = χ_0εΨ_i`."
* Lemma `ex:arith-local-kummer`, tex 3418–3421: "Its Kummer image is its exact local annihilator,
  and the comparison has integral isotropy homotopies. At `v ∣ 2N`, triviality of the moving
  character and the common old quadratic type identify the scalar and binary versions by derived
  coefficient extension"; tex 3437–3439: "The `A_i[G]` Kummer condition and its null-homotopy are
  consequently derived scalar extensions of the fixed local data"; tex 3442–3444: "The local finite
  dualities [Milne I.2.3, I.3.2–I.3.5] make the Kummer map adjoint to
  `H¹(F, B[2^a]) → H¹(F, B)[2^a]`. The latter has Kummer image as kernel, so the Kummer image is
  its exact annihilator."

Round 2 of this lane proved the exact annihilator and the isotropy of the actual Kummer conditions
for the scalar ring `A_i` (`kannActual_ann`, `kannActual_iso` in `KummerAnnActual.lean`), from the
abstract coefficient-extension theorems `kannCoef_ann_left`, `kannCoef_iso` (`KummerAnn.lean`,
generic in the coefficient ring) and the decomposition of `M_i` along the power basis
`1, t, …, t^{i−1}` of `A_i` over `ℤ/2^i`. The text needs the same statements over the binary ring
`A_i[G]` (tex 3437–3439). This file proves them for **any commutative `ℤ/2^i`-algebra `R` with a
finite `ℤ/2^i`-basis `b`** and any character `α : G_{K,S₀} → R^×` equal to `χ_h` on the
decomposition group at `v` (round 2's `IsLocallyQuadAtGen`), for the Kummer conditions over `R`
of round 2 (`genKummerAtS`, coefficient map `genIotaS = 1 ⊗ e`, `e = j⁻¹ ∘ φ_q` the landed
`kannE`). Since `e` is the same map for every coefficient ring, the coefficient pairing on
`B(K̄_v)[2^i]` is round 2's `kannPsi` (`ψ₀(t₁, t₂) = weilS(e t₁, e t₂)`), and round 2's
`kummerExactAnn_kannPsi` (from Milne's print) applies verbatim (`BinaryDuality.lean`).

* `binAPiBase`, `binAPi`: **the coordinate maps** `π_k : (R ⊗ E(K_{S₀})[2^i])(α) → B(K̄_v)[2^i]`,
  `a ⊗ y ↦ e⁻¹(c_k(a) y)`, `c_k` the coordinate functions of `b`; `binAPiBase_smul`,
  `binAPi_smul`: **`G_{K_v}`-equivariant** when `α = χ_h` on the decomposition group (the signs
  `χ_h(σ)` from `α` and from `e⁻¹` cancel; for `R = A_i[G]` and `α = χ_0εΨ_i` this is
  `ε ∘ p_v = 1`, `Ψ_i ∘ p_v = 1`, `Binary.lean`); `binAPi_recon`: `x = ∑_k b_k • ι_v(π_k x)`;
  `binAPi_iota`: `π_k ∘ ι_v = c_k(1)`.
* `binA_coord_weilA_left`, `binA_coord_weilA_right`: the coordinates of lane RC28's `R`-bilinear
  Weil pairing `weilA`.
* `binATau`, `binAJ`: the coordinates `R(1) → ℤ/2^i(1)` and the inclusion `ℤ/2^i(1) → R(1)`,
  equivariant (`binATau_smul`, `binAJ_smul`); `binATau_recon`.
* `binABeta`: the local Weil pairing `M(α) × M(α⁻¹) → R(1)` at `v` (lane RC28's `weilPairingM`
  over `R`, inflated from `S₀`); `binABeta_smul`; `binATau_beta_left`, `binATau_beta_right`:
  `τ_k ∘ β ∘ (ι × 1) = ψ₀ ∘ (1 × π_k)` and its mirror.
* **`binA_ann`** (PROVED): the exact annihilator for the Kummer conditions over `R` at `v`, from
  the exact annihilator of the Kummer image of `B(K_v)` for `ψ₀ᵗ`.
* **`binA_iso`** (PROVED): the isotropy of the degree-one terms of the Kummer conditions over `R`
  for `α` and `α⁻¹`, from the isotropy of the Kummer image for `ψ₀`.
* `binA_genIotaBase_eq`: round 2's coefficient map is `1 ⊗ e` (`rfl`); `binAPiBase_acoef`,
  `binATau_acoef`, `binAJ_acoef`: for `R = A_i` and the power basis the data are round 2's
  `kannPiBase`, `kannTau`, `kannJ` (`rfl`).

Kinds: definitions and PROVED (from lane RC28's GLUE `FullTorsion` as in rounds 1 and 2; the
hypotheses `hannF`, `hiso₀` on `ψ₀` are discharged from Milne's print in `BinaryDuality.lean`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open scoped TensorProduct
open NumberField IsDedekindDomain

section Coef

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (v : Places K S)
  (R : Type) [CommRing R] [Algebra (ZMod (2 ^ i)) R] {ιb : Type} [Fintype ιb]
  (b : Module.Basis ιb (ZMod (2 ^ i)) R)

omit [Algebra (ZMod (2 ^ i)) R] in
/-- PROVED. **The Kummer coefficient map over `R` at level `2^i` is `t ↦ 1 ⊗ e t`**, with round 2's
`e = j⁻¹ ∘ φ_q` (`kannE`), the same map for every coefficient ring. -/
theorem binA_genIotaBase_eq (α : GKS K S₀ →* Rˣ)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    genIotaBase (S := S₀) R W (2 ^ i) s hs hs0 α hFull v.1 t =
      oneTmul R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) (kannE W i s hs hs0 hFull v t) :=
  rfl

/-- Definition. **The coordinate maps of `(R ⊗ E(K_{S₀})[2^i])(α)`**:
`π_k : a ⊗ y ↦ e⁻¹(c_k(a) y)`, for the coordinate functions `c_k` of the basis `b` of `R` over
`ℤ/2^i`. -/
def binAPiBase (α : GKS K S₀ →* Rˣ) (k : ιb) :
    CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) →+
      TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) :=
  (kannE W i s hs hs0 hFull v).symm.toAddMonoidHom.comp
    ((kannCoordTens (kann_torsS_nsmul W i) (b.coord k).toAddMonoidHom (AddMonoidHom.id _)).comp
      (CoefMod.equiv R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))).symm.toLinearMap.toAddMonoidHom)

omit [Fintype ιb] in
/-- PROVED. The coordinate maps on pure tensors. -/
theorem binAPiBase_tmul (α : GKS K S₀ →* Rˣ) (k : ιb) (a : R)
    (y : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    binAPiBase W i s hs hs0 hFull v R b α k (CoefMod.equiv R α _ (a ⊗ₜ y)) =
      (b.coord k a).val • (kannE W i s hs hs0 hFull v).symm y := by
  change (kannE W i s hs hs0 hFull v).symm ((b.coord k a).val • y) = _
  rw [map_nsmul]

omit [Fintype ιb] in
/-- PROVED (tex 3429–3437). **Equivariance of the coordinate maps** on the decomposition group,
where the character `α` is `χ_h` (`IsLocallyQuadAtGen`): `π_k(p_v(σ) x) = σ π_k(x)`. The two signs
`χ_h(σ)` (from `α` and from `e⁻¹`) cancel. -/
theorem binAPiBase_smul (α : GKS K S₀ →* Rˣ)
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1) (k : ιb)
    (σ : Gloc K v.1) (x : CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))) :
    binAPiBase W i s hs hs0 hFull v R b α k (locMap K S₀ v.1 σ • x) =
      σ • binAPiBase W i s hs hs0 hFull v R b α k x := by
  obtain ⟨x', rfl⟩ : ∃ x' : R ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ),
      CoefMod.equiv R α _ x' = x := ⟨x, rfl⟩
  induction x' using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, smul_add, map_add, hx, hy, map_add, smul_add]
  | tmul a y =>
    rw [CoefMod.smul_tmul, binAPiBase_tmul, binAPiBase_tmul, hα σ, kannE_symm_smul]
    set χ : ℤ := ((quadChar s hs hs0 (locMap K S₀ v.1 σ) : ℤˣ) : ℤ) with hχ
    have hχ2 : χ * χ = 1 := by
      rw [hχ, ← Units.val_mul, ← sq, Int.units_sq, Units.val_one]
    have hcoef : b.coord k
        (((intUnitsTo R (quadChar s hs hs0 (locMap K S₀ v.1 σ)) : Rˣ) : R) * a) =
        χ • b.coord k a := by
      rw [← map_zsmul]
      congr 1
      rw [zsmul_eq_mul]
      rfl
    rw [hcoef]
    have hD := kann_torsAlg_nsmul (F := v.1.adicCompletion K) (B := localTwist W h v.1)
      (m := 2 ^ i)
    have h1 : (χ • b.coord k a).val •
        (χ • σ • (kannE W i s hs hs0 hFull v).symm y) =
        kannZSmul hD (χ • b.coord k a)
          (χ • σ • (kannE W i s hs hs0 hFull v).symm y) := rfl
    rw [h1]
    simp only [map_zsmul, AddMonoidHom.zsmul_apply, smul_smul, hχ2, one_smul]
    rw [kannZSmul_apply, smul_comm]

/-- Definition. The coordinate maps on the local module `(R ⊗ E(K_{S₀})[2^i])(α)` (inflated from
`S₀`, with `G_{K_v}` acting through `p_v`): the same maps as `binAPiBase`. -/
def binAPi (α : GKS K S₀ →* Rˣ) (k : ιb) :
    ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)))) →+
      TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i) :=
  binAPiBase W i s hs hs0 hFull v R b α k

omit [Fintype ιb] in
/-- PROVED. **The coordinate maps are `G_{K_v}`-equivariant** on the local module (lane RC26's
`locMap_compat`). -/
theorem binAPi_smul (α : GKS K S₀ →* Rˣ)
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1) (k : ιb) (σ : Gloc K v.1)
    (x : ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))) :
    binAPi hS W i s hs hs0 hFull v R b α k (σ • x) =
      σ • binAPi hS W i s hs hs0 hFull v R b α k x := by
  change binAPiBase W i s hs hs0 hFull v R b α k (inflMap K hS (locMap K S v.1 σ) •
    (show CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) from x)) = _
  rw [locMap_compat K hS v.1 σ]
  exact binAPiBase_smul W i s hs hs0 hFull v R b α hα k σ x

/-- PROVED. **Reconstruction**: `x = ∑_k b_k • ι_v(π_k x)` on the local module. -/
theorem binAPi_recon (α : GKS K S₀ →* Rˣ)
    (x : ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))) :
    ∑ k, b k • genIotaS hS R W (2 ^ i) s hs hs0 α hFull v
      (binAPi hS W i s hs hs0 hFull v R b α k x) = x := by
  refine Eq.trans ?_ (kannCoordTens_recon b (kann_torsS_nsmul W i)
    (show R ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x))
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  change oneTmul R α _ ((kannE W i s hs hs0 hFull v)
    ((kannE W i s hs hs0 hFull v).symm _)) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

omit [Fintype ιb] in
/-- PROVED. `π_k ∘ ι_v` is multiplication by the integer `c_k(1)`. -/
theorem binAPi_iota (α : GKS K S₀ →* Rˣ) (k : ιb)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    binAPi hS W i s hs hs0 hFull v R b α k (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v t) =
      ((b.coord k 1).val : ℤ) • t := by
  change binAPiBase W i s hs hs0 hFull v R b α k
    (CoefMod.equiv R α _ ((1 : R) ⊗ₜ kannE W i s hs hs0 hFull v t)) = _
  rw [binAPiBase_tmul, AddEquiv.symm_apply_apply, natCast_zsmul]

variable (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))

omit [Fintype ιb] in
/-- PROVED. **The coordinates of the `R`-bilinear Weil pairing, left slot** (lane RC28's
`weilA_tmul`): `c_k(weilA(1 ⊗ y, x)) = weilS(y, c_k(x))`. -/
theorem binA_coord_weilA_left (k : ιb) (y : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))
    (x : R ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    b.coord k (weilA (S := S₀) W hμ₀ R ((1 : R) ⊗ₜ y) x) =
      weilS (S := S₀) W hμ₀ y (kannCoordTens (kann_torsS_nsmul W i)
        (b.coord k).toAddMonoidHom (AddMonoidHom.id _) x) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  | tmul a t =>
    rw [weilA_tmul, one_mul, kannCoordTens_tmul, AddMonoidHom.id_apply, map_nsmul, mul_comm,
      ← Algebra.smul_def, map_smul, smul_eq_mul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact mul_comm _ _

omit [Fintype ιb] in
/-- PROVED. **The coordinates of the `R`-bilinear Weil pairing, right slot**:
`c_k(weilA(x, 1 ⊗ y)) = weilS(c_k(x), y)`. -/
theorem binA_coord_weilA_right (k : ιb) (y : TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))
    (x : R ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)) :
    b.coord k (weilA (S := S₀) W hμ₀ R x ((1 : R) ⊗ₜ y)) =
      weilS (S := S₀) W hμ₀ (kannCoordTens (kann_torsS_nsmul W i)
        (b.coord k).toAddMonoidHom (AddMonoidHom.id _) x) y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, AddMonoidHom.add_apply, hx, hx']
  | tmul a t =>
    rw [weilA_tmul, mul_one, kannCoordTens_tmul, AddMonoidHom.id_apply, map_nsmul,
      AddMonoidHom.nsmul_apply, mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, nsmul_eq_mul,
      ZMod.natCast_zmod_val]
    exact mul_comm _ _

/-- Definition. **The coordinate maps of `R(1)`**: `τ_k = c_k : R(1) → ℤ/2^i(1)`. -/
def binATau (k : ιb) :
    ResMod (locMap K S v.1) (InflMod hS (Tate1 R hμ₀)) →+
      ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀)) :=
  (b.coord k).toAddMonoidHom

omit [Fintype ιb] in
/-- PROVED. The coordinate maps of `R(1)` are equivariant (the cyclotomic action is by scalars of
`ℤ/2^i`). -/
theorem binATau_smul (k : ιb) (σ : Gloc K v.1)
    (w : ResMod (locMap K S v.1) (InflMod hS (Tate1 R hμ₀))) :
    binATau hS i v R b hμ₀ k (σ • w) = σ • binATau hS i v R b hμ₀ k w := by
  change b.coord k
      (algebraMap (ZMod (2 ^ i)) R (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
        (show R from w)) =
    algebraMap (ZMod (2 ^ i)) (ZMod (2 ^ i)) (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
      b.coord k (show R from w)
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rfl

/-- Definition. **The inclusion `j : ℤ/2^i(1) → R(1)`** (`algebraMap`). -/
def binAJ : ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀)) →+
    ResMod (locMap K S v.1) (InflMod hS (Tate1 R hμ₀)) :=
  (algebraMap (ZMod (2 ^ i)) R).toAddMonoidHom

/-- PROVED. `j` is equivariant. -/
theorem binAJ_smul (σ : Gloc K v.1)
    (w : ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀))) :
    binAJ hS i v R hμ₀ (σ • w) = σ • binAJ hS i v R hμ₀ w := by
  change algebraMap (ZMod (2 ^ i)) R
      (algebraMap (ZMod (2 ^ i)) (ZMod (2 ^ i)) (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
        (show ZMod (2 ^ i) from w)) =
    algebraMap (ZMod (2 ^ i)) R (cycS hμ₀ (inflMap K hS (locMap K S v.1 σ))) *
      algebraMap (ZMod (2 ^ i)) R (show ZMod (2 ^ i) from w)
  rw [map_mul]
  rfl

/-- PROVED. **Reconstruction in `R(1)`**: `w = ∑_k b_k • j(τ_k w)`. -/
theorem binATau_recon (w : ResMod (locMap K S v.1) (InflMod hS (Tate1 R hμ₀))) :
    ∑ k, b k • binAJ hS i v R hμ₀ (binATau hS i v R b hμ₀ k w) = w := by
  change ∑ k, b k * algebraMap (ZMod (2 ^ i)) R (b.coord k (show R from w)) = (show R from w)
  conv_rhs => rw [← b.sum_repr (show R from w)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm, ← Algebra.smul_def, Module.Basis.coord_apply]

/-- Definition (tex 2798–2805). **The local Weil pairing at `v` over `R`**:
`M(α) × M(α⁻¹) → R(1)` (lane RC28's `weilPairingM` over the `ℤ/2^i`-algebra `R`, inflated from
`S₀`, with `G_{K_v}` acting through `p_v`). -/
abbrev binABeta (α : GKS K S₀ →* Rˣ) :=
  resPairing R (GKS K S) (orthInflPair hS R (weilPairingM (S := S₀) W hμ₀ R α)) (locMap K S v.1)

/-- PROVED. The local Weil pairing over `R` is `G_{K_v}`-equivariant. -/
theorem binABeta_smul (α : GKS K S₀ →* Rˣ) (σ : Gloc K v.1)
    (a : ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)))))
    (c : ResMod (locMap K S v.1)
      (InflMod hS (CoefMod R (charInv α) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))) :
    binABeta hS W i v R hμ₀ α (σ • a) (σ • c) = σ • binABeta hS W i v R hμ₀ α a c :=
  weilPairingM_smul (S := S₀) W hμ₀ R α (inflMap K hS (locMap K S v.1 σ)) a c

omit [Fintype ιb] in
/-- PROVED. `τ_k(β(ι t, x)) = ψ₀(t, π_k x)` (the compatibility `hτβ` of `KummerAnn.lean`). -/
theorem binATau_beta_left (α : GKS K S₀ →* Rˣ) (k : ιb)
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i))
    (x : ResMod (locMap K S v.1)
      (InflMod hS (CoefMod R (charInv α) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))) :
    binATau hS i v R b hμ₀ k
        (binABeta hS W i v R hμ₀ α (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v t) x) =
      kannPsi hS W i s hs hs0 hFull v hμ₀ t
        (binAPi hS W i s hs hs0 hFull v R b (charInv α) k x) := by
  change b.coord k (weilA (S := S₀) W hμ₀ R
      ((1 : R) ⊗ₜ kannE W i s hs hs0 hFull v t)
      (show R ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x)) =
    weilS (S := S₀) W hμ₀ (kannE W i s hs hs0 hFull v t) (kannE W i s hs hs0 hFull v
      ((kannE W i s hs hs0 hFull v).symm (kannCoordTens (kann_torsS_nsmul W i)
        (b.coord k).toAddMonoidHom (AddMonoidHom.id _)
          (show R ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x))))
  rw [AddEquiv.apply_symm_apply]
  exact binA_coord_weilA_left W i R b hμ₀ k _ _

omit [Fintype ιb] in
/-- PROVED. `τ_k(β(x, ι' t)) = ψ₀(π_k x, t)` (the compatibility `hτβ'` of `KummerAnn.lean`). -/
theorem binATau_beta_right (α : GKS K S₀ →* Rˣ) (k : ιb)
    (x : ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)))))
    (t : TorsAlg (v.1.adicCompletion K) (localTwist W h v.1) (2 ^ i)) :
    binATau hS i v R b hμ₀ k (binABeta hS W i v R hμ₀ α x
        (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v t)) =
      kannPsi hS W i s hs hs0 hFull v hμ₀ (binAPi hS W i s hs hs0 hFull v R b α k x) t := by
  change b.coord k (weilA (S := S₀) W hμ₀ R
      (show R ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x)
      ((1 : R) ⊗ₜ kannE W i s hs hs0 hFull v t)) =
    weilS (S := S₀) W hμ₀ (kannE W i s hs hs0 hFull v
      ((kannE W i s hs hs0 hFull v).symm (kannCoordTens (kann_torsS_nsmul W i)
        (b.coord k).toAddMonoidHom (AddMonoidHom.id _)
          (show R ⊗[ℤ] TorsS K S₀ W ((2 ^ i : ℕ) : ℤ) from x))))
      (kannE W i s hs hs0 hFull v t)
  rw [AddEquiv.apply_symm_apply]
  exact binA_coord_weilA_right W i R b hμ₀ k _ _

variable [DecidableEq (v.1.adicCompletion K)] [(localTwist W h v.1).IsElliptic]

include b in
/-- PROVED (tex 3418–3421, 3437–3444). **The exact annihilator for the Kummer conditions over `R` at
`v`** (the direction the per-place duality uses): if the Kummer image of `B(K_v)` (`B = E^{(h)}`
over `K_v`) is its own annihilator for the flipped coefficient pairing `ψ₀ᵗ` (hypothesis `hannF`,
trace-free form), then a `1`-cocycle `y` of `C^•_cont(G_{K_v}, (R ⊗ E[2^i])(α))` whose cup products
`y ∪ ι'_v(κ_Q)` with the Kummer cocycles of the dual condition are all coboundaries lies in the
degree-one term `kummerZ' ⊔ B¹` of the Kummer condition over `R`. -/
theorem binA_ann (α : GKS K S₀ →* Rˣ) [IsOpenKer α]
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
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
    (y : contCochain R (Gloc K v.1)
      (ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))) 1)
    (hy : contD R (Gloc K v.1) _ 1 y = 0)
    (hcup : ∀ Q : (localTwist W h v.1).toAffine.Point,
      contCup (binABeta hS W i v R hμ₀ α) (kann_contPair (binABeta hS W i v R hμ₀ α)) 1 1 2 rfl y
        (kummerCocycleIn (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v) (1 : R) Q) ∈
          LinearMap.range (contD R (Gloc K v.1)
            (ResMod (locMap K S v.1) (InflMod hS (Tate1 R hμ₀))) 1)) :
    y ∈ kummerZ' R (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v) ⊔
      contB1 R (Gloc K v.1)
        (ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))) :=
  kannCoef_ann_left (binABeta hS W i v R hμ₀ α) (kannPsi hS W i s hs hs0 hFull v hμ₀)
    (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v)
    (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v)
    b hannF (binABeta_smul hS W i v R hμ₀ α)
    (genIotaS_smul hS R W (2 ^ i) s hs hs0 α hFull v hα)
    (genIotaS_smul hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα))
    (binAPi hS W i s hs hs0 hFull v R b α)
    (fun k σ x => binAPi_smul hS W i s hs hs0 hFull v R b α hα k σ x)
    (binAPi_recon hS W i s hs hs0 hFull v R b α) (binATau hS i v R b hμ₀)
    (fun k σ w => binATau_smul hS i v R b hμ₀ k σ w)
    (fun k x t => binATau_beta_right hS W i s hs hs0 hFull v R b hμ₀ α k x t) y hy hcup

include b in
/-- PROVED (tex 3418–3421, 3437–3444). **Isotropy of the Kummer conditions over `R` at `v`**: if the
Kummer image of `B(K_v)` is isotropic for `ψ₀` (hypothesis `hiso₀`), the cup product of any element
of the degree-one term of the Kummer condition of `(R ⊗ E[2^i])(α)` with any element of that of
`(R ⊗ E[2^i])(α⁻¹)` is a coboundary. -/
theorem binA_iso (α : GKS K S₀ →* Rˣ) [IsOpenKer α]
    (hα : IsLocallyQuadAtGen (S := S₀) R α (quadChar s hs hs0) v.1)
    (hiso₀ : ∀ P Q : (localTwist W h v.1).toAffine.Point,
      contCup (kannPsi hS W i s hs hs0 hFull v hμ₀)
        (kann_contPair (kannPsi hS W i s hs hs0 hFull v hμ₀)) 1 1 2 rfl
        (kummerCocycle _ _ (2 ^ i) P) (kummerCocycle _ _ (2 ^ i) Q) ∈
          LinearMap.range (contD ℤ (Gloc K v.1)
            (ResMod (locMap K S v.1) (InflMod hS (Tate1 (ZMod (2 ^ i)) hμ₀))) 1))
    {u : contCochain R (Gloc K v.1)
      (ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))) 1}
    (hu : u ∈ kummerZ' R (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v) ⊔
      contB1 R (Gloc K v.1)
        (ResMod (locMap K S v.1) (InflMod hS (CoefMod R α (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))))
    {u' : contCochain R (Gloc K v.1) (ResMod (locMap K S v.1)
      (InflMod hS (CoefMod R (charInv α) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ))))) 1}
    (hu' : u' ∈ kummerZ' R (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v) ⊔
      contB1 R (Gloc K v.1) (ResMod (locMap K S v.1)
        (InflMod hS (CoefMod R (charInv α) (TorsS K S₀ W ((2 ^ i : ℕ) : ℤ)))))) :
    contCup (binABeta hS W i v R hμ₀ α) (kann_contPair (binABeta hS W i v R hμ₀ α)) 1 1 2 rfl
        u u' ∈
      LinearMap.range (contD R (Gloc K v.1)
        (ResMod (locMap K S v.1) (InflMod hS (Tate1 R hμ₀))) 1) :=
  kannCoef_iso (binABeta hS W i v R hμ₀ α) (kannPsi hS W i s hs hs0 hFull v hμ₀)
    (genIotaS hS R W (2 ^ i) s hs hs0 α hFull v)
    (genIotaS hS R W (2 ^ i) s hs hs0 (charInv α) hFull v)
    b hiso₀ (binABeta_smul hS W i v R hμ₀ α)
    (genIotaS_smul hS R W (2 ^ i) s hs hs0 α hFull v hα)
    (genIotaS_smul hS R W (2 ^ i) s hs hs0 (charInv α) hFull v (isLocallyQuadAtGen_charInv hα))
    (binAPi hS W i s hs hs0 hFull v R b (charInv α))
    (fun k σ x => binAPi_smul hS W i s hs hs0 hFull v R b (charInv α)
      (isLocallyQuadAtGen_charInv hα) k σ x)
    (fun k => ((b.coord k 1).val : ℤ))
    (fun k t => binAPi_iota hS W i s hs hs0 hFull v R b (charInv α) k t)
    (binATau hS i v R b hμ₀)
    (fun k t x => binATau_beta_left hS W i s hs hs0 hFull v R b hμ₀ α k t x)
    (binAJ hS i v R hμ₀) (binAJ_smul hS i v R hμ₀) (binATau_recon hS i v R b hμ₀) hu hu'

end Coef

/-! ### Agreement with round 2 for the scalar ring -/

section Agree

open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S₀) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S₀ W (2 ^ i))
  (v : Places K S)

/-- PROVED (`rfl`). For `R = A_i` and the power basis, the coordinate maps are round 2's
`kannPiBase`. -/
theorem binAPiBase_acoef (α : GKS K S₀ →* (Acoef i)ˣ) (k : Fin (kannPB i).dim) :
    binAPiBase W i s hs hs0 hFull v (Acoef i) (kannPB i).basis α k =
      kannPiBase W i s hs hs0 hFull v α k :=
  rfl

variable (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))

/-- PROVED (`rfl`). For `R = A_i` and the power basis, the coordinate maps of `R(1)` are round 2's
`kannTau`. -/
theorem binATau_acoef (k : Fin (kannPB i).dim) :
    binATau hS i v (Acoef i) (kannPB i).basis hμ₀ k = kannTau hS i v hμ₀ k :=
  rfl

/-- PROVED (`rfl`). For `R = A_i`, the inclusion `j` is round 2's `kannJ`. -/
theorem binAJ_acoef : binAJ hS i v (Acoef i) hμ₀ = kannJ hS i v hμ₀ :=
  rfl

end Agree

end ZInQ.Manuscript.RC.KummerMaps
