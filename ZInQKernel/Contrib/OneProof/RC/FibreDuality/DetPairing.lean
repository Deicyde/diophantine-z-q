import ZInQKernel.Contrib.OneProof.RC.FibreDuality.Cyclotomic2
import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Rank

/-!
# Lane RC31, part 7: the perfect Galois-equivariant pairing on `T_2E` and on the fibres

Manuscript `diophantine_zq.tex`, tex 2780 (`T = T_2E`), tex 2798–2805 (the Weil pairing
`e_2 : T × T → ℤ₂(1)`, "and `e_2` transforms by the cyclotomic character"), tex 5037
(`β = ε e_2` with `ε` a unit), and the characteristic-zero fibres of the switching argument
(tex 4976–5200).

* `detT`: the determinant form `T_2E × T_2E → ℤ₂` in lane RC28's basis `tateBasis`
  (alternating, `detT (b 0) (b 1) = 1`).
* **`detT_mod_eq_weil`, `isUnit_weilS_basis`**: at every finite level `2^n`, the reduction of
  `detT` times the unit `ε_n = e_{2^n}(b 0, b 1)` is the genuine Weil pairing `e_{2^n}` of the
  levels; so `detT` is the Weil pairing up to the unit `ε_n⁻¹` at every level.
* **`detT_smul`**: `detT (σ x) (σ y) = χ(σ) detT x y` for the `2`-adic cyclotomic character
  `χ = cyc2` (from the Galois equivariance of `e_{2^n}`); `det_actLin`: `det ρ_T(σ) = χ(σ)`.
* **`betaVP : V_𝔭(α) × V_𝔭(α⁻¹) → k(𝔭)`**: the base change of `detT`, with
  `betaVP_smul` (`β(σ a, σ b) = χ(σ) β(a, b)`), the lattice bound `betaVP_latt`, and perfectness
  `betaVP_bijective`, `betaVP_flip_bijective`.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.FibreDuality

open NumberField IsDedekindDomain TensorProduct
open Module (Basis)
open ZInQ.Manuscript.RC.Uniform (Lambda)
open ZInQ.Manuscript.RC.SelmerComplex (GKS)
open ZInQ.Manuscript.RC.Wiring (ResAt)
open ZInQ.Manuscript.RC.CoefModules (TorsS HasRootsOfUnity cycS weilS weilS_apply weilS_smul
  weilS_perfect weilBar inclTors natCast_ne_zero_bar)
open ZInQ.Manuscript.RC.LambdaCoef (HasFullTwoTorsion TateS Lev projLev resN tateBasis
  projLev_surjective mem_ker_projLev_iff coe_projLev projLev_smul actLin VP latt vpBasis vpEquiv
  resChar coe_resChar finrank_vp)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K}

/-! ### The Weil pairing is alternating -/

section WeilAlt

variable [W.IsElliptic] {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)

/-- **The Weil pairing on `E(K_S)[N]` is alternating**: `e_N(P, P) = 0` (tex 2798–2805;
Silverman III.8.1(b), through Tau Ceti's `weilPairing_self`). Kind: PROVED. -/
theorem weilS_self (P : TorsS K S W N) : weilS W hμ P P = 0 := by
  rw [weilS_apply]
  have h := TauCeti.Isogeny.weilPairing_self (W.baseChange (AlgebraicClosure K)) N
    (natCast_ne_zero_bar N) (inclTors W N P)
  change weilBar W N (inclTors W N P) (inclTors W N P) = 0 at h
  rw [h, map_zero]

/-- **The Weil pairing is skew**: `e_N(P, Q) = -e_N(Q, P)` (tex 2798–2805). Kind: PROVED. -/
theorem weilS_swap (P Q : TorsS K S W N) : weilS W hμ P Q = -weilS W hμ Q P := by
  have h := weilS_self hμ (P + Q)
  simp only [map_add, AddMonoidHom.add_apply, weilS_self, zero_add, add_zero] at h
  linear_combination h

/-- `e_N(m P, Q) = m e_N(P, Q)` (tex 2798–2805). Kind: PROVED. -/
theorem weilS_nsmul_left (m : ℕ) (P Q : TorsS K S W N) :
    weilS W hμ (m • P) Q = (m : ZMod N) * weilS W hμ P Q := by
  rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul]

/-- `e_N(P, m Q) = m e_N(P, Q)` (tex 2798–2805). Kind: PROVED. -/
theorem weilS_nsmul_right (m : ℕ) (P Q : TorsS K S W N) :
    weilS W hμ P (m • Q) = (m : ZMod N) * weilS W hμ P Q := by
  rw [map_nsmul, nsmul_eq_mul]

end WeilAlt

/-! ### The determinant form on `T_2E` -/

section Det

variable [W.IsElliptic] [HasFullTwoTorsion K S W]

/-- **The determinant form** `T_2E × T_2E → ℤ₂`,
`(x, y) ↦ x₀ y₁ - x₁ y₀` in the coordinates of lane RC28's basis `tateBasis` (tex 2780,
tex 2798–2805). Kind: definition. -/
def detT : TateS K S W →ₗ[ℤ_[2]] TateS K S W →ₗ[ℤ_[2]] ℤ_[2] :=
  LinearMap.mk₂ ℤ_[2]
    (fun x y => tateBasis.repr x 0 * tateBasis.repr y 1 - tateBasis.repr x 1 * tateBasis.repr y 0)
    (fun x x' y => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun c x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [map_add, Finsupp.add_apply]; ring)
    (fun c x y => by simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]; ring)

/-- The formula for `detT` (tex 2780). Kind: PROVED. -/
theorem detT_apply (x y : TateS K S W) :
    detT x y = tateBasis.repr x 0 * tateBasis.repr y 1 - tateBasis.repr x 1 * tateBasis.repr y 0 :=
  rfl

/-- **`detT` is alternating**: `detT x x = 0` (tex 2798–2805). Kind: PROVED. -/
theorem detT_self (x : TateS K S W) : detT x x = 0 := by
  rw [detT_apply]; ring

/-- **`detT` is skew**: `detT y x = -detT x y` (tex 2798–2805). Kind: PROVED. -/
theorem detT_swap (x y : TateS K S W) : detT y x = -detT x y := by
  rw [detT_apply, detT_apply]; ring

/-- **`detT (b 0) (b 1) = 1`** for `b = tateBasis` (tex 2780). Kind: PROVED. -/
theorem detT_basis : detT (tateBasis 0) (tateBasis 1 : TateS K S W) = 1 := by
  rw [detT_apply]
  simp [Basis.repr_self]

/-- `detT (b 1) (b 0) = -1` (tex 2780). Kind: PROVED. -/
theorem detT_basis_swap : detT (tateBasis 1) (tateBasis 0 : TateS K S W) = -1 := by
  rw [detT_swap, detT_basis]

omit [W.IsElliptic] [HasFullTwoTorsion K S W] in
/-- `projLev n (a • x) = (a mod 2^n) • projLev n x` (tex 2780). Kind: PROVED. -/
theorem projLev_padicSmul (n : ℕ) (a : ℤ_[2]) (x : TateS K S W) :
    projLev n (a • x) = resN n a • projLev n x := rfl

/-- The level `n` of `x = x₀ b 0 + x₁ b 1` (tex 2780). Kind: PROVED. -/
theorem projLev_eq_basis (n : ℕ) (x : TateS K S W) :
    projLev n x = resN n (tateBasis.repr x 0) • projLev n (tateBasis 0) +
      resN n (tateBasis.repr x 1) • projLev n (tateBasis 1) := by
  conv_lhs => rw [← tateBasis.sum_repr x]
  rw [Fin.sum_univ_two, map_add, projLev_padicSmul, projLev_padicSmul]

/-- **`detT` is the Weil pairing up to the unit `ε_n = e_{2^n}(b 0, b 1)` at level `2^n`**:
`(detT x y mod 2^n) · e_{2^n}(b 0, b 1) = e_{2^n}(x_n, y_n)` (tex 2798–2805; tex 5037:
`β = ε e_2`). Kind: PROVED (bilinearity and alternation of `e_{2^n}`). -/
theorem detT_mod_eq_weil (n : ℕ) (hμ : HasRootsOfUnity K S (2 ^ n)) (x y : TateS K S W) :
    PadicInt.toZModPow n (detT x y) *
        weilS W hμ (projLev n (tateBasis 0)) (projLev n (tateBasis 1)) =
      weilS W hμ (projLev n x) (projLev n y) := by
  rw [projLev_eq_basis n x, projLev_eq_basis n y]
  simp only [map_add, AddMonoidHom.add_apply, weilS_nsmul_left, weilS_nsmul_right, weilS_self,
    mul_zero, zero_add, add_zero]
  rw [weilS_swap hμ (projLev n (tateBasis 1)), detT_apply]
  simp only [resN, ZMod.natCast_zmod_val, map_sub, map_mul]
  ring

omit [NumberField K] [W.IsElliptic] [HasFullTwoTorsion K S W] in
/-- `2^{k+1} r ≠ 2^k` in `ℤ₂` (reduce modulo `2^{k+1}`). Kind: PROVED. -/
theorem two_pow_succ_mul_ne (k : ℕ) (r : ℤ_[2]) :
    ((2 ^ (k + 1) : ℕ) : ℤ_[2]) * r ≠ ((2 ^ k : ℕ) : ℤ_[2]) := by
  intro hr
  have h3 := congrArg (PadicInt.toZModPow (k + 1)) hr
  rw [map_mul, map_natCast, map_natCast, ZMod.natCast_self, zero_mul, eq_comm,
    ZMod.natCast_eq_zero_iff, Nat.pow_dvd_pow_iff_le_right (by norm_num)] at h3
  omega

omit [NumberField K] [W.IsElliptic] [HasFullTwoTorsion K S W] in
/-- A non-unit `w` of `ℤ/2^{k+1}` is killed by `2^k`. Kind: PROVED. -/
theorem two_pow_mul_eq_zero_of_not_isUnit (k : ℕ) (w : ZMod (2 ^ (k + 1))) (hnu : ¬IsUnit w) :
    ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) * w = 0 := by
  rw [← ZMod.natCast_zmod_val w] at hnu ⊢
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (Nat.succ_pos k)] at hnu
  have h2 : 2 ∣ w.val := by
    by_contra h
    exact hnu ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h).symm
  obtain ⟨c, hc⟩ := h2
  rw [hc, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  exact ⟨c, by ring⟩

/-- `2^k b 0` is nonzero at level `k + 1` (a basis vector is not in `2 T_2E`; tex 2780).
Kind: PROVED. -/
theorem two_pow_smul_projLev_basis_ne (k : ℕ) :
    (2 ^ k : ℕ) • projLev (k + 1) (tateBasis 0 : TateS K S W) ≠ 0 := by
  intro hP0
  have hker : ((2 ^ k : ℕ) • (tateBasis 0 : TateS K S W)).pt (k + 1) = 0 := by
    rw [← coe_projLev, map_nsmul, hP0]
    rfl
  obtain ⟨Q, hQ⟩ := (mem_ker_projLev_iff (k + 1) _).mp hker
  have hc := congrArg ((tateBasis (K := K) (S := S) (W := W)).coord 0) hQ
  rw [map_smul, map_nsmul, Basis.coord_apply, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_eq_same, smul_eq_mul, nsmul_eq_mul, mul_one,
    show (2 : ℤ_[2]) ^ (k + 1) = ((2 ^ (k + 1) : ℕ) : ℤ_[2]) by push_cast; rfl] at hc
  exact two_pow_succ_mul_ne k _ hc

/-- **`ε_n = e_{2^n}(b 0, b 1)` is a unit of `ℤ/2^n`** (tex 2798–2805, tex 5037): otherwise
`2^{n-1} b 0` would pair trivially with all of `E(K_S)[2^n]`, hence vanish at level `n` by
perfectness of `e_{2^n}`, i.e. `2^{n-1} b 0 ∈ 2^n T_2E`, impossible for a basis vector.
Kind: PROVED. -/
theorem isUnit_weilS_basis (n : ℕ) (hμ : HasRootsOfUnity K S (2 ^ n)) :
    IsUnit (weilS W hμ (projLev n (tateBasis 0)) (projLev n (tateBasis 1))) := by
  cases n with
  | zero =>
    have : Subsingleton (ZMod (2 ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero 2)
    exact isUnit_of_subsingleton _
  | succ k =>
    by_contra hnu
    have hw2 := two_pow_mul_eq_zero_of_not_isUnit k _ hnu
    refine two_pow_smul_projLev_basis_ne (S := S) (W := W) k ?_
    apply (weilS_perfect W hμ (HasFullTwoTorsion.full (k + 1))).1.1
    rw [show weilS W hμ 0 = 0 from map_zero _]
    ext Q
    obtain ⟨y, rfl⟩ := projLev_surjective (k + 1) Q
    rw [projLev_eq_basis (k + 1) y, AddMonoidHom.zero_apply]
    simp only [map_add, weilS_nsmul_left, weilS_nsmul_right, weilS_self, mul_zero, zero_add]
    linear_combination ((resN (k + 1) (tateBasis.repr y 1) : ℕ) : ZMod (2 ^ (k + 1))) * hw2

/-- **`detT` transforms by the `2`-adic cyclotomic character** (tex 2798–2805: "`e_2`
transforms by the cyclotomic character"): `detT (σ x) (σ y) = χ(σ) detT x y`. Kind: PROVED
(at every level `2^n` from `detT_mod_eq_weil`, `isUnit_weilS_basis` and `weilS_smul`; then
`toZModPow_cyc2`). -/
theorem detT_smul (σ : GKS K S) (x y : TateS K S W) :
    detT (σ • x) (σ • y) = (cyc2 K S σ : ℤ_[2]) * detT x y := by
  have : HasTwoPowerRoots K S := hasTwoPowerRoots_of_fullTwoTorsion K S W
  refine PadicInt.ext_of_toZModPow.mp fun n => ?_
  have hμ : HasRootsOfUnity K S (2 ^ n) := HasTwoPowerRoots.roots n
  refine (isUnit_weilS_basis (W := W) n hμ).mul_left_inj.mp ?_
  rw [detT_mod_eq_weil, projLev_smul, projLev_smul, weilS_smul, ← detT_mod_eq_weil, map_mul,
    toZModPow_cyc2 n hμ, mul_assoc]

omit [W.IsElliptic] [HasFullTwoTorsion K S W] in
/-- `actLin σ` is `σ` (tex 2780). Kind: PROVED. -/
theorem actLin_apply (σ : GKS K S) (x : TateS K S W) : actLin K S W σ x = σ • x := rfl

/-- **`det ρ_T(σ) = χ(σ)`** (tex 2780, tex 2798–2805). Kind: PROVED (from `detT_smul` at the
basis). -/
theorem det_actLin (σ : GKS K S) : LinearMap.det (actLin K S W σ) = (cyc2 K S σ : ℤ_[2]) := by
  have h := detT_smul σ (tateBasis 0) (tateBasis 1 : TateS K S W)
  rw [detT_basis, mul_one] at h
  rw [← LinearMap.det_toMatrix tateBasis, Matrix.det_fin_two, ← h, detT_apply]
  simp only [LinearMap.toMatrix_apply, actLin_apply]
  ring

end Det

/-! ### The pairing on the characteristic-zero fibres -/

section Fibre

variable [W.IsElliptic] [HasFullTwoTorsion K S W] (P : Ideal Lambda) [P.IsPrime]
  (α : GKS K S →* Lambdaˣ)

variable (W) in
/-- **The fibre pairing** `β_𝔭 : V_𝔭(α) × V_𝔭(α⁻¹) → k(𝔭)`, the `k(𝔭)`-bilinear base change of
`detT` (tex 2798–2805, tex 4976–5200; tex 5037). Kind: definition. -/
def betaVP : VP K S W P α →ₗ[ResAt P] VP K S W P α⁻¹ →ₗ[ResAt P] ResAt P :=
  LinearMap.BilinForm.baseChange (ResAt P) (detT (K := K) (S := S) (W := W))

/-- `β_𝔭(c ⊗ x, c' ⊗ y) = c c' detT(x, y)` (tex 4976–5200). Kind: PROVED. -/
theorem betaVP_tmul (c c' : ResAt P) (x y : TateS K S W) :
    betaVP W P α (show VP K S W P α from c ⊗ₜ x) (show VP K S W P α⁻¹ from c' ⊗ₜ y) =
      c * c' * algebraMap ℤ_[2] (ResAt P) (detT x y) := by
  change (detT x y) • (c * c') = _
  rw [Algebra.smul_def]
  ring

/-- The reductions of `α` and `α⁻¹` multiply to one (tex 2798–2805: "the two scalar characters
multiply to one"). Kind: PROVED. -/
theorem resChar_mul_resChar_inv (σ : GKS K S) :
    ((resChar P α σ : (ResAt P)ˣ) : ResAt P) * ((resChar P α⁻¹ σ : (ResAt P)ˣ) : ResAt P) = 1 := by
  rw [coe_resChar, coe_resChar, MonoidHom.inv_apply, ← map_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, map_one]

/-- **`β_𝔭` transforms by the cyclotomic character**: `β_𝔭(σ a, σ b) = χ(σ) β_𝔭(a, b)`
(tex 2798–2805, tex 4976–5200). Kind: PROVED (`detT_smul` and `resChar_mul_resChar_inv`). -/
theorem betaVP_smul (σ : GKS K S) (a : VP K S W P α) (b : VP K S W P α⁻¹) :
    betaVP W P α (σ • a) (σ • b) =
      algebraMap ℤ_[2] (ResAt P) (cyc2 K S σ : ℤ_[2]) * betaVP W P α a b := by
  induction a using VP.induction with
  | zero => simp only [smul_zero, map_zero, LinearMap.zero_apply, mul_zero]
  | add a a' ha ha' =>
    rw [smul_add, map_add, LinearMap.add_apply, ha, ha', map_add, LinearMap.add_apply, mul_add]
  | tmul c x =>
    induction b using VP.induction with
    | zero => simp only [smul_zero, map_zero, mul_zero]
    | add b b' hb hb' => rw [smul_add, map_add, hb, hb', map_add, mul_add]
    | tmul c' y =>
      rw [VP.smul_tmul, VP.smul_tmul, betaVP_tmul, betaVP_tmul, detT_smul, map_mul]
      have h := resChar_mul_resChar_inv P α σ
      linear_combination (c * c' * algebraMap ℤ_[2] (ResAt P) (cyc2 K S σ : ℤ_[2]) *
        algebraMap ℤ_[2] (ResAt P) (detT x y)) * h

/-- **Lattice bound**: `β_𝔭` maps `latt(α) × latt(α⁻¹)` into the image of `Λ`
(tex 4976–5200). Kind: PROVED. -/
theorem betaVP_latt {a : VP K S W P α} {b : VP K S W P α⁻¹} (ha : a ∈ latt K S W P α)
    (hb : b ∈ latt K S W P α⁻¹) :
    ∃ l : Lambda, betaVP W P α a b = algebraMap Lambda (ResAt P) l := by
  unfold latt at ha hb
  induction ha using Submodule.span_induction with
  | mem a' ha' =>
    obtain ⟨x, rfl⟩ := ha'
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨y, rfl⟩ := hb'
      refine ⟨algebraMap ℤ_[2] Lambda (detT x y), ?_⟩
      rw [betaVP_tmul, one_mul, one_mul, ← IsScalarTower.algebraMap_apply]
    | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
    | add b₁ b₂ _ _ h₁ h₂ =>
      obtain ⟨l₁, e₁⟩ := h₁
      obtain ⟨l₂, e₂⟩ := h₂
      exact ⟨l₁ + l₂, by rw [map_add, e₁, e₂, map_add]⟩
    | smul l b' _ h =>
      obtain ⟨l', e⟩ := h
      exact ⟨l * l', by rw [← algebraMap_smul (ResAt P) l b', map_smul, e, smul_eq_mul, map_mul]⟩
  | zero => exact ⟨0, by rw [map_zero, LinearMap.zero_apply, map_zero]⟩
  | add a₁ a₂ _ _ h₁ h₂ =>
    obtain ⟨l₁, e₁⟩ := h₁
    obtain ⟨l₂, e₂⟩ := h₂
    exact ⟨l₁ + l₂, by rw [map_add, LinearMap.add_apply, e₁, e₂, map_add]⟩
  | smul l a' _ h =>
    obtain ⟨l', e⟩ := h
    exact ⟨l * l', by
      rw [← algebraMap_smul (ResAt P) l a', map_smul, LinearMap.smul_apply, e, smul_eq_mul,
        map_mul]⟩

/-- The basis `vpBasis` of `V_𝔭` is `1 ⊗ b i` (tex 4976–5200). Kind: PROVED. -/
theorem vpBasis_apply' (i : Fin 2) :
    vpBasis (K := K) (S := S) (W := W) (α := α) P i =
      show VP K S W P α from (1 : ResAt P) ⊗ₜ tateBasis i := by
  rw [vpBasis, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  rfl

/-- **`β_𝔭` on the basis**: `β_𝔭(1 ⊗ b i, 1 ⊗ b j) = detT(b i, b j)`; its Gram matrix is
`[[0, 1], [-1, 0]]` (tex 4976–5200). Kind: PROVED. -/
theorem betaVP_basis (i j : Fin 2) :
    betaVP W P α (vpBasis P i) (vpBasis P j) =
      algebraMap ℤ_[2] (ResAt P) (detT (tateBasis i) (tateBasis j : TateS K S W)) := by
  rw [vpBasis_apply', vpBasis_apply', betaVP_tmul, one_mul, one_mul]

/-- `β_𝔭(a, 1 ⊗ b 1)` is the `0`-th coordinate of `a` (tex 4976–5200). Kind: PROVED. -/
theorem betaVP_apply_basis_one (a : VP K S W P α) :
    betaVP W P α a (vpBasis P 1) = (vpBasis P).repr a 0 := by
  conv_lhs => rw [← (vpBasis P).sum_repr a]
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, betaVP_basis, betaVP_basis, detT_basis, detT_self]
  simp

/-- `β_𝔭(a, 1 ⊗ b 0)` is minus the `1`-st coordinate of `a` (tex 4976–5200). Kind: PROVED. -/
theorem betaVP_apply_basis_zero (a : VP K S W P α) :
    betaVP W P α a (vpBasis P 0) = -(vpBasis P).repr a 1 := by
  conv_lhs => rw [← (vpBasis P).sum_repr a]
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, betaVP_basis, betaVP_basis, detT_basis_swap, detT_self]
  simp

/-- `β_𝔭(1 ⊗ b 0, b)` is the `1`-st coordinate of `b` (tex 4976–5200). Kind: PROVED. -/
theorem betaVP_basis_zero_apply (b : VP K S W P α⁻¹) :
    betaVP W P α (vpBasis P 0) b = (vpBasis P).repr b 1 := by
  conv_lhs => rw [← (vpBasis P).sum_repr b]
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul, betaVP_basis, betaVP_basis, detT_basis,
    detT_self]
  simp

/-- `β_𝔭(1 ⊗ b 1, b)` is minus the `0`-th coordinate of `b` (tex 4976–5200). Kind: PROVED. -/
theorem betaVP_basis_one_apply (b : VP K S W P α⁻¹) :
    betaVP W P α (vpBasis P 1) b = -(vpBasis P).repr b 0 := by
  conv_lhs => rw [← (vpBasis P).sum_repr b]
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul, betaVP_basis, betaVP_basis, detT_basis_swap,
    detT_self]
  simp

/-- `β_𝔭` is nondegenerate on the left (tex 4976–5200). Kind: PROVED. -/
theorem betaVP_injective : Function.Injective (betaVP W P α) := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
  have h1 := betaVP_apply_basis_one P α a
  have h0 := betaVP_apply_basis_zero P α a
  rw [ha, LinearMap.zero_apply] at h0 h1
  refine (vpBasis P).ext_elem_iff.mpr fun i => ?_
  fin_cases i
  · simpa using h1.symm
  · simpa using h0

/-- `β_𝔭` is nondegenerate on the right (tex 4976–5200). Kind: PROVED. -/
theorem betaVP_flip_injective : Function.Injective (betaVP W P α).flip := by
  refine (injective_iff_map_eq_zero _).mpr fun b hb => ?_
  have h0 := betaVP_basis_zero_apply P α b
  have h1 := betaVP_basis_one_apply P α b
  rw [← LinearMap.flip_apply (betaVP W P α), hb, LinearMap.zero_apply] at h0 h1
  refine (vpBasis P).ext_elem_iff.mpr fun i => ?_
  fin_cases i
  · simpa using h1
  · simpa using h0.symm

/-- **`β_𝔭` is perfect on the left**: `V_𝔭(α) ≃ Hom(V_𝔭(α⁻¹), k(𝔭))` (tex 2798–2805,
tex 4976–5200). Kind: PROVED (injective, both sides of dimension `2`). -/
theorem betaVP_bijective : Function.Bijective (betaVP W P α) := by
  have hinj := betaVP_injective (W := W) P α
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [Module.finrank_linearMap_self, finrank_vp, finrank_vp]

/-- **`β_𝔭` is perfect on the right**: `V_𝔭(α⁻¹) ≃ Hom(V_𝔭(α), k(𝔭))` (tex 2798–2805,
tex 4976–5200). Kind: PROVED. -/
theorem betaVP_flip_bijective : Function.Bijective (betaVP W P α).flip := by
  have hinj := betaVP_flip_injective (W := W) P α
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  rw [Module.finrank_linearMap_self, finrank_vp, finrank_vp]

end Fibre

end ZInQ.Manuscript.RC.FibreDuality
