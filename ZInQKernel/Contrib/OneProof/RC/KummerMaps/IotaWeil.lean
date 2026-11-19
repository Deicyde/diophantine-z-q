import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthKummer
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.NonVacuity
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.BaseChange
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Bilinear
import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.Pairing
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Add
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.PointMap
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Reduction

/-!
# Lane RC29 (Kummer maps), round 2: the Kummer coefficient maps `ι_v` respect the Weil pairing

Manuscript `diophantine_zq.tex` (11/5), proof of Lemma `ex:arith-local-kummer`, tex 3442–3444:

> The local finite dualities [Milne I.2.3, I.3.2–I.3.5] make the Kummer map adjoint to
> `H¹(F, B[2^a]) → H¹(F, B)[2^a]`. The latter has Kummer image as kernel, so the Kummer image is
> its exact annihilator.

The local duality on `H¹(F, B[2^a])` is the cup product through the Weil pairing `e^B` of the local
twist `B = E^{(h)}` over `F = K_v`, while the global Selmer-cone duality (tex 2798–2805, lane
RC28's `weilPairingM` on `M_i × M_i(α⁻¹) → A_i(1)`) uses the Weil pairing of `E` over `K̄`, read
through the discrete logarithm at a primitive root of unity `ζ ∈ K_S`. The Kummer conditions are
carried from `B` into `M_i` by the coefficient maps `ι_v` (`Iota.lean`:
`ι_v(t) = 1 ⊗ j⁻¹(φ_q t)`, `φ_q` the twist identification over `K̄_v`, `j` the comparison along the
fixed embedding `K̄ → K̄_v`). The step needs that the `ι_v` carry `e^B` to `weilPairingM`.

## Main results

* **`iotaWeil_pairing`: the main formula** `weilPairingM (ι_v t₁) (ι'_v t₂) = ℓ_v(e^B(t₁, t₂))`
  in `A_i(1) ≅ A_i` (PROVED, exact: the unit of the requested formula is `u = 1`).
* `iotaWeilLog hμ v`: the discrete logarithm `ℓ_v : μ_{2^i}(K̄_v) ≃ ℤ/2^i` at `j(ζ)`;
  `iotaWeilLog_restrict`: `ℓ_v ∘ j = logBar` (lane RC28's logarithm at `ζ`, PROVED);
  **`iotaWeilLog_smul`: `ℓ_v` is `G_{K_v}`-equivariant into `(ℤ/2^i)(1)`**,
  `ℓ_v(σ x) = χ_cyc(p_v σ) · ℓ_v(x)` with lane RC28's `cycS` (PROVED).
* `iotaWeil_weilS_eq`: lane RC28's `weilS` on `E(K_S)[N]` is `ℓ_v` of the Weil pairing of
  `E_v = E ×_K K_v` over `K̄_v` at the images under `j` (PROVED, from Tau Ceti's functoriality of
  the Weil pairing under field homomorphisms, `weilPairing_torsionMapAlong`);
  `iotaWeil_pairing_exact`: `weilPairingM (ι_v t₁) (ι'_v t₂) = ℓ_v(e^{E_v}(φ_q t₁, φ_q t₂))`.
* `iotaWeilVc_weilPairing`: **the Weil pairing is invariant under a change of variables**
  (Silverman III.8.2 for isomorphisms), over any separably closed field (PROVED: the change of
  variables is a separable isogeny of degree one, `iotaWeilVcIsogeny`, acting on points as the
  change of variables, and the other group's degree formula `weilPairing_torsionMap` applies);
  `iotaWeilTwist_invariance`: `e^{E_v}(φ_q t₁, φ_q t₂) = e^B(t₁, t₂)` (PROVED).
* Properties of `ψ(t₁, t₂) = weilPairingM (ι_v t₁) (ι'_v t₂)`: values in the image of `ℤ/2^i`
  (`iotaWeil_pairing_mem_range`); **`G_{K_v}`-equivariant into `A_i(1)`** with `G_{K_v}` acting
  through `p_v = locMap` (`iotaWeil_pairing_smul`, from `IsLocallyQuadAt`); alternating
  (`iotaWeil_pairing_self`); perfect: the `ℤ/2^i`-valued form `ψ₀ = ℓ_v ∘ e^B` has both
  adjoints bijective onto `Hom(B[2^i], ℤ/2^i)` (`iotaWeilForm_perfect`), and `ψ` is
  nondegenerate on both sides for `i ≠ 0` (`iotaWeil_pairing_nondegenerate_left/right`);
  `ψ₀` is `G_{K_v}`-equivariant into `(ℤ/2^i)(1)` (`iotaWeilForm_smul`, through
  `iotaWeilB_smul`, the Galois equivariance of `e^B`).
* Also kept (the form first announced): a unit `iotaWeilUnit` with
  `ℓ_v(e^{E_v}(φ_q t₁, φ_q t₂)) = u · ℓ_v(e^B(t₁, t₂))`, obtained without the invariance (two
  alternating nondegenerate forms on the free rank-two `ℤ/2^i`-module `B(K̄_v)[2^i]` differ by a
  unit, `iotaWeil_alt_eq_unit_mul`), `iotaWeil_pairing_unit`, and `iotaWeilUnit_eq_one : u = 1`.

## Kinds and departures

All declarations are definitions or PROVED. Hypotheses are lane RC28's `FullTorsion` (GLUE,
Néron–Ogg–Shafarevich, kept explicit as in `Iota.lean`), `HasRootsOfUnity` (the `hμ` of lane
RC28's Weil pairing) and, for the equivariance of `ψ` only, the landed `IsLocallyQuadAt` (ELLIOT
there, tex 2729, 3431, 3500–3506). No new predicate is introduced.

* DEPARTURE (form): `A_i(1)` is lane RC28's `Tate1 A_i hμ` (`A_i` with the cyclotomic action);
  the formula is stated after the identity `CharMod.equiv : A_i(1) ≃ A_i`.
* The text uses tacitly that the twist identification `B[2^i] ≅ E[2^i](χ_h)` respects Weil
  pairings; this is proved here (`iotaWeilTwist_invariance`), not assumed.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain WeierstrassCurve TensorProduct ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Contrib.CloudB3RC53.Duality (natCard_addMonoidHom_zmod_le finite_addMonoidHom)

/-! ### Discrete logarithms at a primitive root of unity -/

section Log

variable {L : Type*} [CommRing L] [IsDomain L] {N : ℕ} [NeZero N]

/-- Definition. **The discrete logarithm `μ_N(L) ≃ ℤ/N` at a primitive `N`-th root of unity `u`**
(the construction of lane RC28's `logBar`). -/
def iotaWeilZLog {u : Lˣ} (hpu : IsPrimitiveRoot u N) :
    Additive (rootsOfUnity N L) ≃+ ZMod N :=
  ((hpu.zmodEquivZPowers).trans (MulEquiv.subgroupCongr hpu.zpowers_eq).toAdditive).symm

/-- PROVED. `ℓ(u^n) = n`. -/
theorem iotaWeilZLog_pow {u : Lˣ} (hpu : IsPrimitiveRoot u N) (n : ℕ) (y : rootsOfUnity N L)
    (hy : (y : Lˣ) = u ^ n) : iotaWeilZLog hpu (Additive.ofMul y) = n := by
  rw [iotaWeilZLog, AddEquiv.symm_apply_eq]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [AddEquiv.trans_apply, IsPrimitiveRoot.zmodEquivZPowers_apply_coe_nat]
  simp [hy]

/-- PROVED. Every `N`-th root of unity is a power of the primitive root `u`. -/
theorem iotaWeil_exists_pow {u : Lˣ} (hpu : IsPrimitiveRoot u N) (y : rootsOfUnity N L) :
    ∃ n : ℕ, (y : Lˣ) = u ^ n := by
  obtain ⟨n, -, hn⟩ := hpu.eq_pow_of_mem_rootsOfUnity y.2
  exact ⟨n, hn.symm⟩

end Log

/-! ### Alternating forms on a free module of rank two -/

section AltForm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- PROVED. **An alternating bilinear form on a free module of rank two is a multiple of the
determinant**: `β(x, y) = det(x, y) · β(b₀, b₁)`. -/
theorem iotaWeil_alt_det (b : Module.Basis (Fin 2) R M) (β : M →ₗ[R] M →ₗ[R] R)
    (hβ : ∀ x, β x x = 0) (x y : M) :
    β x y = (b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0) * β (b 0) (b 1) := by
  have hskew : β (b 1) (b 0) = -β (b 0) (b 1) := by
    have h := hβ (b 0 + b 1)
    simp only [map_add, LinearMap.add_apply, hβ, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
  simp only [Fin.sum_univ_two, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hβ,
    hskew, smul_eq_mul]
  ring

/-- PROVED. **A nondegenerate alternating form on a free rank-two module over a finite ring takes a
unit value on a basis** (its value is a non-zero-divisor, hence a unit). -/
theorem iotaWeil_isUnit_of_separating [Finite R] (b : Module.Basis (Fin 2) R M)
    (β : M →ₗ[R] M →ₗ[R] R) (hβ : ∀ x, β x x = 0) (hsep : ∀ x, (∀ y, β x y = 0) → x = 0) :
    IsUnit (β (b 0) (b 1)) := by
  refine IsLeftRegular.isUnit_of_finite ?_
  intro a a' haa
  have h0 : β (b 0) (b 1) * (a - a') = 0 := by
    simp only at haa
    rw [mul_sub, haa, sub_self]
  have hx : (a - a') • b 0 = 0 := hsep _ fun y => by
    rw [iotaWeil_alt_det b β hβ]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
    rw [Finsupp.single_eq_of_ne (by decide), mul_zero, zero_mul, sub_zero]
    linear_combination (b.repr y 1) * h0
  have h1 := congrArg (fun z => b.repr z 0) hx
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
  exact sub_eq_zero.1 h1

/-- PROVED. **Two nondegenerate alternating forms on a free rank-two module over a finite ring
differ by a unit.** -/
theorem iotaWeil_alt_eq_unit_mul [Finite R] (b : Module.Basis (Fin 2) R M)
    (β₁ β₂ : M →ₗ[R] M →ₗ[R] R) (h₁ : ∀ x, β₁ x x = 0) (h₂ : ∀ x, β₂ x x = 0)
    (hs₁ : ∀ x, (∀ y, β₁ x y = 0) → x = 0) (hs₂ : ∀ x, (∀ y, β₂ x y = 0) → x = 0) :
    ∃ u : Rˣ, ∀ x y, β₁ x y = u * β₂ x y := by
  obtain ⟨c₁, hc₁⟩ := iotaWeil_isUnit_of_separating b β₁ h₁ hs₁
  obtain ⟨c₂, hc₂⟩ := iotaWeil_isUnit_of_separating b β₂ h₂ hs₂
  refine ⟨c₁ * c₂⁻¹, fun x y => ?_⟩
  rw [iotaWeil_alt_det b β₁ h₁, iotaWeil_alt_det b β₂ h₂, ← hc₁, ← hc₂, Units.val_mul]
  have : ((c₂⁻¹ : Rˣ) : R) * c₂ = 1 := Units.inv_mul c₂
  linear_combination (-(b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0) * (c₁ : R)) * this

end AltForm

section Bilin

variable {N : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod N) M]

/-- Definition. The `ℤ/N`-bilinear form of an additive pairing into `ℤ/N` (additive maps of
`ℤ/N`-modules are `ℤ/N`-linear). -/
def iotaWeilBilin (f : M →+ M →+ ZMod N) : M →ₗ[ZMod N] M →ₗ[ZMod N] ZMod N :=
  LinearMap.mk₂ (ZMod N) (fun x y => f x y)
    (fun x x' y => by rw [map_add, AddMonoidHom.add_apply])
    (fun c x y => by rw [ZMod.map_smul f c x, AddMonoidHom.smul_apply])
    (fun x y y' => map_add _ _ _)
    (fun c x y => ZMod.map_smul (f x) c y)

theorem iotaWeilBilin_apply (f : M →+ M →+ ZMod N) (x y : M) : iotaWeilBilin f x y = f x y :=
  rfl

end Bilin

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}

/-! ### The local discrete logarithm `ℓ_v` -/

section LogV

variable {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N) (v : HeightOneSpectrum (𝓞 K))

omit [NeZero N] in
/-- PROVED. `j(ζ)` is a primitive `N`-th root of unity of `K̄_v`, for the primitive root
`ζ ∈ K_S` behind `hμ` (the one of lane RC28's `logBar`). -/
theorem iotaWeil_isPrimitiveRoot_loc : IsPrimitiveRoot (embS K S v (Classical.choose hμ)) N :=
  (Classical.choose_spec hμ).map_of_injective (embS_injective K S v)

/-- Definition. The unit `j(ζ)` of `K̄_v`. -/
def iotaWeilUnitLoc : (AlgebraicClosure (v.adicCompletion K))ˣ :=
  ((iotaWeil_isPrimitiveRoot_loc hμ v).isUnit (NeZero.ne N)).unit

theorem iotaWeil_isPrimitiveRoot_unitLoc : IsPrimitiveRoot (iotaWeilUnitLoc hμ v) N := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact iotaWeil_isPrimitiveRoot_loc hμ v

/-- Definition. **The local discrete logarithm `ℓ_v : μ_N(K̄_v) ≃ ℤ/N` at `j(ζ)`**, `ζ ∈ K_S` the
primitive root behind `hμ` and lane RC28's `logBar`, `j` the fixed embedding `K̄ → K̄_v`. -/
def iotaWeilLog : Additive (rootsOfUnity N (AlgebraicClosure (v.adicCompletion K))) ≃+ ZMod N :=
  iotaWeilZLog (iotaWeil_isPrimitiveRoot_unitLoc hμ v)

/-- Definition. The unit `ζ ∈ K̄` behind lane RC28's `logBar`. -/
def iotaWeilUnitBar : (AlgebraicClosure K)ˣ :=
  ((isPrimitiveRoot_bar hμ).isUnit (NeZero.ne N)).unit

theorem iotaWeil_isPrimitiveRoot_unitBar : IsPrimitiveRoot (iotaWeilUnitBar hμ) N := by
  rw [← IsPrimitiveRoot.coe_units_iff]
  exact isPrimitiveRoot_bar hμ

/-- PROVED. Lane RC28's `logBar` is the discrete logarithm at `ζ`. -/
theorem iotaWeil_logBar_eq : logBar hμ = iotaWeilZLog (iotaWeil_isPrimitiveRoot_unitBar hμ) :=
  rfl

/-- Definition. The fixed embedding `j : K̄ → K̄_v` (`decompEmb`) as a ring homomorphism. -/
abbrev iotaWeilEmb : AlgebraicClosure K →+* AlgebraicClosure (v.adicCompletion K) :=
  (decompEmb K v).toRingHom

/-- PROVED. **`ℓ_v ∘ j = logBar`**: the logarithm at `j(ζ)` of the image under `j` of an `N`-th
root of unity of `K̄` is its logarithm at `ζ`. -/
theorem iotaWeilLog_restrict (w : Additive (rootsOfUnity N (AlgebraicClosure K))) :
    iotaWeilLog hμ v (Additive.ofMul (restrictRootsOfUnity (iotaWeilEmb v) N w.toMul)) =
      logBar hμ w := by
  obtain ⟨n, hn⟩ := iotaWeil_exists_pow (iotaWeil_isPrimitiveRoot_unitBar hμ) w.toMul
  have h1 : logBar hμ w = (n : ZMod N) :=
    iotaWeilZLog_pow (iotaWeil_isPrimitiveRoot_unitBar hμ) n w.toMul hn
  rw [h1, iotaWeilLog]
  refine iotaWeilZLog_pow _ n _ ?_
  apply Units.ext
  rw [restrictRootsOfUnity_coe_apply, hn, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    map_pow]
  rfl

/-- Definition. An element of `G_{K_v}` as a `K_v`-automorphism of `K̄_v`. -/
abbrev iotaWeilGal (σ : Gloc K v) :
    AlgebraicClosure (v.adicCompletion K) ≃ₐ[v.adicCompletion K]
      AlgebraicClosure (v.adicCompletion K) :=
  σ

/-- PROVED. `σ(j ζ) = (j ζ)^{χ_cyc(p_v σ)}` for `σ ∈ G_{K_v}`. -/
theorem iotaWeil_gal_unitLoc (σ : Gloc K v) :
    iotaWeilGal v σ ((iotaWeilUnitLoc hμ v : (AlgebraicClosure (v.adicCompletion K))ˣ) :
        AlgebraicClosure (v.adicCompletion K)) =
      ((iotaWeilUnitLoc hμ v : (AlgebraicClosure (v.adicCompletion K))ˣ) :
        AlgebraicClosure (v.adicCompletion K)) ^
        ((cycS hμ (locMap K S v σ) : (ZMod N)ˣ) : ZMod N).val := by
  have hu : ((iotaWeilUnitLoc hμ v : (AlgebraicClosure (v.adicCompletion K))ˣ) :
      AlgebraicClosure (v.adicCompletion K)) = embS K S v (Classical.choose hμ) :=
    IsUnit.unit_spec _
  rw [hu]
  change σ.toAlgHom (embS K S v (Classical.choose hμ)) = _
  rw [← embS_locMap K S v σ, cycS_spec hμ (locMap K S v σ)
    (Classical.choose_spec hμ).pow_eq_one, map_pow]

/-- PROVED. **`ℓ_v` is `G_{K_v}`-equivariant from `μ_N(K̄_v)` to `(ℤ/N)(1)`**, the cyclotomic
action through the localization `p_v = locMap` (lane RC28's `cycS`):
`ℓ_v(σ x) = χ_cyc(p_v σ) · ℓ_v(x)`. -/
theorem iotaWeilLog_smul (σ : Gloc K v)
    (w : Additive (rootsOfUnity N (AlgebraicClosure (v.adicCompletion K)))) :
    iotaWeilLog hμ v (Additive.ofMul (restrictRootsOfUnity (iotaWeilGal v σ) N w.toMul)) =
      ((cycS hμ (locMap K S v σ) : (ZMod N)ˣ) : ZMod N) * iotaWeilLog hμ v w := by
  obtain ⟨n, hn⟩ := iotaWeil_exists_pow (iotaWeil_isPrimitiveRoot_unitLoc hμ v) w.toMul
  set c := ((cycS hμ (locMap K S v σ) : (ZMod N)ˣ) : ZMod N) with hc
  have h1 : iotaWeilLog hμ v w = (n : ZMod N) :=
    iotaWeilZLog_pow (iotaWeil_isPrimitiveRoot_unitLoc hμ v) n w.toMul hn
  have h2 : iotaWeilLog hμ v (Additive.ofMul (restrictRootsOfUnity (iotaWeilGal v σ) N w.toMul)) =
      ((c.val * n : ℕ) : ZMod N) := by
    refine iotaWeilZLog_pow _ (c.val * n) _ ?_
    apply Units.ext
    rw [restrictRootsOfUnity_coe_apply, hn, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      map_pow, iotaWeil_gal_unitLoc hμ v σ, ← pow_mul]
  rw [h1, h2, Nat.cast_mul, ZMod.natCast_zmod_val]

end LogV

/-! ### `weilS` through the fixed embedding: functoriality of the Weil pairing -/

section Functor

variable (W : WeierstrassCurve K) [W.IsElliptic] {N : ℕ} [NeZero N] (hμ : HasRootsOfUnity K S N)
  (v : HeightOneSpectrum (𝓞 K))

omit [W.IsElliptic] [NeZero N] in
/-- PROVED. `(E_{K̄})^j = (E_v)_{K̄_v}`: pushing the coefficients of `W` over `K̄` along `j` gives
the base change of `W_v = W ×_K K_v` to `K̄_v` (`j` is a `K`-algebra map). -/
theorem iotaWeil_curve_eq :
    (W.baseChange (AlgebraicClosure K)).map (iotaWeilEmb v) =
      (W.baseChange (v.adicCompletion K)).baseChange (AlgebraicClosure (v.adicCompletion K)) := by
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext x
  exact (decompEmb K v).commutes x

/-- Definition. **The Weil pairing on lane RC28's `B(F̄)[N]`** (`TorsAlg F B N`): Tau Ceti's
`weilPairing (B.baseChange F̄) N` (Silverman III.8.1), with values in `μ_N(F̄)`. -/
def iotaWeilAlg (F : Type) [Field F] (B : WeierstrassCurve F) [B.IsElliptic] (N : ℕ) [NeZero N]
    (hN : ((N : ℕ) : AlgebraicClosure F) ≠ 0) :
    TorsAlg F B N →+ TorsAlg F B N →+ Additive (rootsOfUnity N (AlgebraicClosure F)) :=
  TauCeti.Isogeny.weilPairing (B.baseChange (AlgebraicClosure F)) N hN

/-- PROVED. `N ≠ 0` in `K̄_v` (characteristic zero). -/
theorem iotaWeil_natCast_ne_zero_loc : ((N : ℕ) : AlgebraicClosure (v.adicCompletion K)) ≠ 0 :=
  Nat.cast_ne_zero.2 (NeZero.ne N)

omit [W.IsElliptic] [NeZero N] in
/-- PROVED. The comparison point map `E(K_S) → E(K̄_v)` (lane RC29's `compPt`) is the point map
`E(K_S) → E(K̄)` (lane RC28's `inclTors`) followed by the point map along `j`, transported along
`iotaWeil_curve_eq`. -/
theorem iotaWeil_compPt_eq (P : (W.baseChange (KS K S)).toAffine.Point) :
    (compPt W v P : ((W.baseChange (v.adicCompletion K)).baseChange
        (AlgebraicClosure (v.adicCompletion K))).toAffine.Point) =
      cast (congrArg (fun V : WeierstrassCurve (AlgebraicClosure (v.adicCompletion K)) =>
        V.toAffine.Point) (iotaWeil_curve_eq W v))
        (Affine.Point.mapAlong (iotaWeilEmb v) (iotaWeilEmb v).injective
          (Affine.Point.map (inclS K S) P)) := by
  rcases P with _ | ⟨x, y, hxy⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, Affine.Point.mapAlong_zero,
      Affine.Point.cast_zero (iotaWeil_curve_eq W v)]
    rfl
  · rw [compPt_some, Affine.Point.map_some, Affine.Point.mapAlong_some,
      Affine.Point.cast_some (iotaWeil_curve_eq W v)]
    exact some_eq_some rfl rfl _ _

/-- PROVED. The torsion comparison `compTors` factors through lane RC28's `inclTors` and Tau
Ceti's `torsionMapAlong` along `j`. -/
theorem iotaWeil_compTors_eq (P : TorsS K S W N) :
    compTors W N v P = AddEquiv.torsionByCongr
      (AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure (v.adicCompletion K)) =>
        V.toAffine.Point) (iotaWeil_curve_eq W v)) N
      ((W.baseChange (AlgebraicClosure K)).torsionMapAlong (iotaWeilEmb v) N (inclTors W N P)) := by
  apply Subtype.ext
  rw [coe_compTors, AddEquiv.torsionByCongr_apply_coe, AddEquiv.cast_apply,
    coe_torsionMapAlong_apply, coe_inclTors]
  exact iotaWeil_compPt_eq W v P.1

/-- PROVED (Silverman III.8.1, through Tau Ceti's `weilPairing_torsionMapAlong`). **Lane RC28's
Weil pairing `weilS` on `E(K_S)[N]` is `ℓ_v` of the Weil pairing of `E_v` over `K̄_v` at the images
under `j`**: `weilS(P, Q) = ℓ_v(e^{E_v}(j P, j Q))`. -/
theorem iotaWeil_weilS_eq (P Q : TorsS K S W N) :
    weilS W hμ P Q = iotaWeilLog hμ v
      (iotaWeilAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) N
        (iotaWeil_natCast_ne_zero_loc v) (compTors W N v P) (compTors W N v Q)) := by
  rw [weilS_apply, ← iotaWeilLog_restrict hμ v, iotaWeil_compTors_eq, iotaWeil_compTors_eq]
  congr 1
  have h1 := WeierstrassCurve.weilPairing_torsionByCongr_cast (iotaWeil_curve_eq W v) N
    (iotaWeil_natCast_ne_zero_loc v)
    ((W.baseChange (AlgebraicClosure K)).torsionMapAlong (iotaWeilEmb v) N (inclTors W N P))
    ((W.baseChange (AlgebraicClosure K)).torsionMapAlong (iotaWeilEmb v) N (inclTors W N Q))
  have h2 := WeierstrassCurve.weilPairing_torsionMapAlong (W.baseChange (AlgebraicClosure K))
    (iotaWeilEmb v) N (natCast_ne_zero_bar N) (inclTors W N P) (inclTors W N Q)
  exact (h1.trans h2).symm

end Functor

/-! ### Invariance of the Weil pairing under a change of variables -/

section VarChange

open WeierstrassCurve.Affine TauCeti TauCeti.Isogeny Polynomial

variable {F : Type*} [Field F] [DecidableEq F] (V : WeierstrassCurve F) [V.IsElliptic]
  (C : VariableChange F)

omit [DecidableEq F] in
/-- PROVED. **A change of variables preserves the points with a pole at a place**: for a place `P`
of `L/F` and `R ∈ (C • V)(L)` with `R = O` or `1 < P(x(R))`, also `ψ_C(R) = O` or
`1 < P(x(ψ_C R))`, since `x(ψ_C R) = u²x(R) + r` with `u, r` constants. -/
theorem iotaWeilVc_mem_polePoints {L : Type*} [Field L] [DecidableEq L] [Algebra F L]
    (P : TauCeti.Place F L) {R : ((C • V).baseChange L).toAffine.Point}
    (hR : R ∈ polePoints (C • V) P) : V.pointEquivVariableChange L C R ∈ polePoints V P := by
  rcases R with _ | ⟨x, y, h⟩
  · left
    rw [← Affine.Point.zero_def, map_zero]
  · right
    rcases hR with h0 | hlt
    · exact absurd h0 (Affine.Point.some_ne_zero _)
    · rw [Point.xCoord_some] at hlt
      rw [pointEquivVariableChange_some, Point.xCoord_some]
      have hu : P.valuation (((C.baseChange L).u : L)) = 1 := by
        simp only [VariableChange.baseChange, VariableChange.map_u, Units.coe_map,
          MonoidHom.coe_ofClass]
        exact Valuation.IsTrivialOn.eq_one _ C.u.ne_zero
      have hr : P.valuation ((C.baseChange L).r) ≤ 1 := by
        simp only [VariableChange.baseChange, VariableChange.map_r]
        exact Valuation.IsTrivialOn.valuation_algebraMap_le_one _ _
      have h1 : P.valuation (((C.baseChange L).u : L) ^ 2 * x) = P.valuation x := by
        rw [map_mul, map_pow, hu, one_pow, one_mul]
      rw [Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hr (h1 ▸ hlt)), h1]
      exact hlt

/-- Definition. **The generic point of `C • V`, moved to `V` by the change of variables**: the point
`ψ_C(x₁, y₁) = (u²x₁ + r, u³y₁ + u²s x₁ + t)` of `V` over the function field of `C • V`. -/
def iotaWeilVcQ : (V.baseChange (C • V).toAffine.FunctionField).toAffine.Point :=
  V.pointEquivVariableChange _ C (genericPoint (C • V).toAffine)

omit [DecidableEq F] in
/-- PROVED. `iotaWeilVcQ` on the coordinates of the generic point. -/
theorem iotaWeilVcQ_eq : iotaWeilVcQ V C = V.pointEquivVariableChange _ C
    (.some _ _ (nonsingular_genericX_genericY (C • V).toAffine)) := rfl

omit [DecidableEq F] in
/-- PROVED. `iotaWeilVcQ ≠ O`. -/
theorem iotaWeilVcQ_ne_zero : iotaWeilVcQ V C ≠ 0 := by
  rw [iotaWeilVcQ, Ne, AddEquiv.map_eq_zero_iff, genericPoint_eq_some]
  exact Affine.Point.some_ne_zero _

omit [DecidableEq F] in
/-- PROVED. The generic point has a pole at the place at infinity. -/
theorem iotaWeilVc_generic_mem :
    genericPoint (C • V).toAffine ∈ polePoints (C • V) (Place.infinity (C • V).toAffine) := by
  rw [mem_polePoints_iff, xCoord_genericPoint, Place.valuation_infinity, genericX_eq_algebraMap]
  exact Or.inr (one_lt_infinityPlace_X _)

omit [DecidableEq F] in
/-- PROVED. `iotaWeilVcQ` has a pole at the place at infinity of `C • V`. -/
theorem iotaWeilVcQ_mem : iotaWeilVcQ V C ∈ polePoints V (Place.infinity (C • V).toAffine) :=
  iotaWeilVc_mem_polePoints V C _ (iotaWeilVc_generic_mem V C)

/-- Definition. **The change of variables as an isogeny `C • V → V`**: its coordinate pullback
evaluates the coordinate functions of `V` at `iotaWeilVcQ`, pointed because `x` acquires a pole at
infinity (Tau Ceti's construction `Hom.ofPolePoint`, repeated with an explicit isogeny). -/
def iotaWeilVcIsogeny : Isogeny (C • V).toAffine V.toAffine :=
  ⟨CoordinateRing.evalAlgHom (Point.nonsingular_coords (iotaWeilVcQ_ne_zero V C)).left,
    CoordinatePullback.mapsInfinity_of_one_lt_infinityPlace _ (algebraMap F[X] _ X) (by
      rw [AdjoinRoot.algebraMap_eq, CoordinateRing.evalAlgHom_of_X, ← Place.valuation_infinity]
      exact ((mem_polePoints_iff _ _ _).1 (iotaWeilVcQ_mem V C)).resolve_left
        (iotaWeilVcQ_ne_zero V C))⟩

omit [DecidableEq F] in
/-- PROVED. The tautological point of `iotaWeilVcIsogeny` is `iotaWeilVcQ`. -/
theorem iotaWeilVc_tautologicalPoint :
    (Hom.ofIsogeny (iotaWeilVcIsogeny V C)).tautologicalPoint = iotaWeilVcQ V C := by
  rw [Hom.tautologicalPoint_ofIsogeny]
  exact Point.eq_of_coords (CoordinatePullback.tautologicalPoint_ne_zero _)
    (iotaWeilVcQ_ne_zero V C)
    (by
      rw [CoordinatePullback.xCoord_tautologicalPoint]
      exact CoordinateRing.evalAlgHom_of_X (Point.nonsingular_coords (iotaWeilVcQ_ne_zero V C)).left)
    (by
      rw [CoordinatePullback.yCoord_tautologicalPoint]
      exact CoordinateRing.evalAlgHom_root (Point.nonsingular_coords (iotaWeilVcQ_ne_zero V C)).left)

omit [V.IsElliptic] in
/-- PROVED. The change of variables commutes with the base change of points from `F` to `L`. -/
theorem iotaWeilVc_baseChange {L : Type*} [Field L] [DecidableEq L] [Algebra F L]
    (P : (C • V).toAffine.Point) :
    V.pointEquivVariableChange L C
        (Point.baseChange (W' := C • V) F L (Point.equivBaseChangeSelf (C • V).toAffine P)) =
      Point.baseChange (W' := V) F L
        (Point.equivBaseChangeSelf V.toAffine (Affine.Point.addEquivVariableChange V C P)) := by
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero, map_zero, map_zero, map_zero]
  · rw [Point.equivBaseChangeSelf_some, Affine.Point.coe_addEquivVariableChange,
      Affine.Point.equivVariableChange_some, Point.equivBaseChangeSelf_some]
    simp only [Point.baseChange, Affine.Point.map_some, pointEquivVariableChange_some]
    refine some_eq_some ?_ ?_ _ _
    · simp [VariableChange.baseChange]
    · simp [VariableChange.baseChange]

/-- PROVED. **On points, `iotaWeilVcIsogeny` is the change of variables**:
`(ofIsogeny φ_C)(P) = ψ_C(P)` (the generic point reduces to `P` at the place of `P`, and `ψ_C`
preserves the kernel of reduction). -/
theorem iotaWeilVc_pointMap (P : (C • V).toAffine.Point) :
    (Hom.ofIsogeny (iotaWeilVcIsogeny V C)).pointMap P =
      Affine.Point.addEquivVariableChange V C P := by
  rw [Hom.pointMap_eq_iff, iotaWeilVc_tautologicalPoint]
  have hG := reductionOfDegreeEqOne_genericPoint (C • V).toAffine P
  rw [reductionOfDegreeEqOne_eq_iff] at hG
  have h1 := iotaWeilVc_mem_polePoints V C _ hG
  rw [map_sub, iotaWeilVc_baseChange] at h1
  exact h1

omit [DecidableEq F] in
/-- PROVED. The function-field pullback sends `x` to `u²x₁ + r`. -/
theorem iotaWeilVc_fieldPullback_genericX :
    (iotaWeilVcIsogeny V C).fieldPullback (genericX V.toAffine) =
      (((C.baseChange (C • V).toAffine.FunctionField).u : (C • V).toAffine.FunctionField) ^ 2 *
        genericX (C • V).toAffine + (C.baseChange (C • V).toAffine.FunctionField).r) := by
  rw [genericX_def, fieldPullback_algebraMap, AdjoinRoot.mk_C]
  rw [show (iotaWeilVcIsogeny V C).pullback (AdjoinRoot.of V.toAffine.polynomial X) =
    (iotaWeilVcQ V C).xCoord from
      CoordinateRing.evalAlgHom_of_X (Point.nonsingular_coords (iotaWeilVcQ_ne_zero V C)).left]
  rw [iotaWeilVcQ_eq, pointEquivVariableChange_some, Point.xCoord_some]

omit [DecidableEq F] in
/-- PROVED. The function-field pullback sends `y` to `u³y₁ + u²s x₁ + t`. -/
theorem iotaWeilVc_fieldPullback_genericY :
    (iotaWeilVcIsogeny V C).fieldPullback (genericY V.toAffine) =
      (((C.baseChange (C • V).toAffine.FunctionField).u : (C • V).toAffine.FunctionField) ^ 3 *
        genericY (C • V).toAffine +
        ((C.baseChange (C • V).toAffine.FunctionField).u : (C • V).toAffine.FunctionField) ^ 2 *
          (C.baseChange (C • V).toAffine.FunctionField).s * genericX (C • V).toAffine +
        (C.baseChange (C • V).toAffine.FunctionField).t) := by
  rw [genericY_def, fieldPullback_algebraMap, AdjoinRoot.mk_X]
  rw [show (iotaWeilVcIsogeny V C).pullback (AdjoinRoot.root V.toAffine.polynomial) =
    (iotaWeilVcQ V C).yCoord from
      CoordinateRing.evalAlgHom_root (Point.nonsingular_coords (iotaWeilVcQ_ne_zero V C)).left]
  rw [iotaWeilVcQ_eq, pointEquivVariableChange_some, Point.yCoord_some]

omit [DecidableEq F] in
/-- PROVED. The function-field pullback of `iotaWeilVcIsogeny` is surjective: its image contains
`x₁` and `y₁`, which generate the function field of `C • V`. -/
theorem iotaWeilVc_fieldRange : (iotaWeilVcIsogeny V C).fieldPullback.fieldRange = ⊤ := by
  set L := (C • V).toAffine.FunctionField
  set u : L := ((C.baseChange L).u : L) with hu_def
  have hu : u ≠ 0 := Units.ne_zero _
  rw [fieldRange_eq_adjoin_genericX_genericY, eq_top_iff,
    ← adjoin_genericX_genericY_eq_top (C • V).toAffine, IntermediateField.adjoin_le_iff]
  set E := IntermediateField.adjoin F {(iotaWeilVcIsogeny V C).fieldPullback (genericX V.toAffine),
    (iotaWeilVcIsogeny V C).fieldPullback (genericY V.toAffine)}
  have hxE : (iotaWeilVcIsogeny V C).fieldPullback (genericX V.toAffine) ∈ E :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hyE : (iotaWeilVcIsogeny V C).fieldPullback (genericY V.toAffine) ∈ E :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  have huE : u ∈ E := by
    rw [hu_def]
    simp only [VariableChange.baseChange, VariableChange.map_u, Units.coe_map,
      MonoidHom.coe_ofClass]
    exact IntermediateField.algebraMap_mem _ _
  have hrE : (C.baseChange L).r ∈ E := by
    simp only [VariableChange.baseChange, VariableChange.map_r]
    exact IntermediateField.algebraMap_mem _ _
  have hsE : (C.baseChange L).s ∈ E := by
    simp only [VariableChange.baseChange, VariableChange.map_s]
    exact IntermediateField.algebraMap_mem _ _
  have htE : (C.baseChange L).t ∈ E := by
    simp only [VariableChange.baseChange, VariableChange.map_t]
    exact IntermediateField.algebraMap_mem _ _
  rw [iotaWeilVc_fieldPullback_genericX] at hxE
  rw [iotaWeilVc_fieldPullback_genericY] at hyE
  have hgx : genericX (C • V).toAffine ∈ E := by
    have : genericX (C • V).toAffine = (u ^ 2 * genericX (C • V).toAffine + (C.baseChange L).r -
        (C.baseChange L).r) / u ^ 2 := by
      field_simp
      ring
    rw [this]
    exact div_mem (sub_mem hxE hrE) (pow_mem huE 2)
  have hgy : genericY (C • V).toAffine ∈ E := by
    have : genericY (C • V).toAffine = (u ^ 3 * genericY (C • V).toAffine +
        u ^ 2 * (C.baseChange L).s * genericX (C • V).toAffine + (C.baseChange L).t -
        u ^ 2 * (C.baseChange L).s * genericX (C • V).toAffine - (C.baseChange L).t) / u ^ 3 := by
      field_simp
      ring
    rw [this]
    exact div_mem (sub_mem (sub_mem hyE (mul_mem (mul_mem (pow_mem huE 2) hsE) hgx)) htE)
      (pow_mem huE 3)
  exact Set.pair_subset hgx hgy

omit [DecidableEq F] in
/-- PROVED. `iotaWeilVcIsogeny` has degree one. -/
theorem iotaWeilVc_degree : (iotaWeilVcIsogeny V C).degree = 1 := by
  rw [Isogeny.degree_def, IntermediateField.finrank_eq_one_iff_eq_top]
  exact iotaWeilVc_fieldRange V C

omit [DecidableEq F] in
/-- PROVED. `iotaWeilVcIsogeny` is separable (its function-field extension is trivial). -/
theorem iotaWeilVc_isSeparable : Algebra.IsSeparable
    (iotaWeilVcIsogeny V C).fieldPullback.fieldRange (C • V).toAffine.FunctionField := by
  refine ⟨fun x => ?_⟩
  have hx : x ∈ (iotaWeilVcIsogeny V C).fieldPullback.fieldRange := by
    rw [iotaWeilVc_fieldRange V C]
    exact IntermediateField.mem_top
  exact isSeparable_algebraMap (⟨x, hx⟩ : (iotaWeilVcIsogeny V C).fieldPullback.fieldRange)

/-- PROVED (Silverman III.8.2 for the isomorphism `ψ_C`, through the degree formula
`e_N(φS, φT) = e_N(S, T)^{deg φ}` for separable isogenies of the other group's Weil-pairing
contribution, `weilPairing_torsionMap`, at `deg φ_C = 1`). **The Weil pairing is invariant under a
change of variables**: `e_N(ψ_C S, ψ_C T) = e_N(S, T)` for `ψ_C : (C • V)(F)[N] ≃ V(F)[N]` over a
separably closed field `F`. -/
theorem iotaWeilVc_weilPairing [IsSepClosed F] (N : ℕ) [NeZero N] (hN : (N : F) ≠ 0)
    (S T : Submodule.torsionBy ℤ (C • V).toAffine.Point (N : ℤ)) :
    TauCeti.Isogeny.weilPairing V N hN
        (AddEquiv.torsionByCongr (Affine.Point.addEquivVariableChange V C) N S)
        (AddEquiv.torsionByCongr (Affine.Point.addEquivVariableChange V C) N T) =
      TauCeti.Isogeny.weilPairing (C • V) N hN S T := by
  have := iotaWeilVc_isSeparable V C
  have h := ZInQ.Contrib.CloudB3RC53.WeilIsogeny.weilPairing_torsionMap
    (iotaWeilVcIsogeny V C) N hN S T
  rw [iotaWeilVc_degree, one_smul] at h
  have e : ∀ R : Submodule.torsionBy ℤ (C • V).toAffine.Point (N : ℤ),
      ZInQ.Contrib.CloudB3RC53.WeilIsogeny.torsionMap (iotaWeilVcIsogeny V C) N R =
        AddEquiv.torsionByCongr (Affine.Point.addEquivVariableChange V C) N R := fun R =>
    Subtype.ext ((iotaWeilVc_pointMap V C R).trans (AddEquiv.torsionByCongr_apply_coe _ _ R).symm)
  rw [← e S, ← e T]
  exact h

end VarChange

/-! ### The twist: comparing `e^{E_v} ∘ (φ_q × φ_q)` with `e^B` -/

section Twist

variable (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : HeightOneSpectrum (𝓞 K))

/-- Definition (tex 3413–3416). **The twist identification `φ_q : B(K̄_v)[2^i] ≃+ E_v(K̄_v)[2^i]`**
at `q = j(s)` (the landed `twistTors`, the first factor of `ι_v`). -/
abbrev iotaWeilTwist :
    TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) ≃+
      TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ i) :=
  twistTors (W.baseChange (v.adicCompletion K)) (algebraMap K (v.adicCompletion K) h)
    two_ne_zero (localSqrt_ne_zero s hs0 v) (localSqrt_sq s hs v) (2 ^ i)

/-- Definition (tex 3442–3444: the local finite duality of `B`). **The Weil pairing `e^B` of the
local twist `B = E^{(h)}` over `K̄_v`**: Tau Ceti's
`weilPairing (B.baseChange (AlgebraicClosure K_v)) (2^i)` on `B(K̄_v)[2^i]`. -/
def iotaWeilB :
    TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+
      TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+
        Additive (rootsOfUnity (2 ^ i) (AlgebraicClosure (v.adicCompletion K))) :=
  haveI := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v
  iotaWeilAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) (iotaWeil_natCast_ne_zero_loc v)

/-- Definition. The Weil pairing `e^{E_v}` of `E_v = W ×_K K_v` over `K̄_v`. -/
abbrev iotaWeilE :
    TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ i) →+
      TorsAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ i) →+
        Additive (rootsOfUnity (2 ^ i) (AlgebraicClosure (v.adicCompletion K))) :=
  iotaWeilAlg (v.adicCompletion K) (W.baseChange (v.adicCompletion K)) (2 ^ i)
    (iotaWeil_natCast_ne_zero_loc v)

omit [W.IsElliptic] in
/-- PROVED. `φ_q` is the change of variables `ψ_C` of the twist (`twistVariableChange`), after the
identification `B ×_{K_v} K̄_v = C • (E_v ×_{K_v} K̄_v)` (`twistVariableChange_smul_baseChange`). -/
theorem iotaWeilTwist_eq_vc (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilTwist W i s hs hs0 v t =
      AddEquiv.torsionByCongr (Affine.Point.addEquivVariableChange
        ((W.baseChange (v.adicCompletion K)).baseChange (AlgebraicClosure (v.adicCompletion K)))
        (twistVariableChange ((W.baseChange (v.adicCompletion K)).baseChange
          (AlgebraicClosure (v.adicCompletion K))) (localSqrt s v) (localSqrt_ne_zero s hs0 v)))
        ((2 ^ i : ℕ) : ℤ)
        (AddEquiv.torsionByCongr (AddEquiv.cast
          (M := fun V : WeierstrassCurve (AlgebraicClosure (v.adicCompletion K)) =>
            V.toAffine.Point)
          (twistVariableChange_smul_baseChange (W.baseChange (v.adicCompletion K))
            (algebraMap K (v.adicCompletion K) h) two_ne_zero (localSqrt_ne_zero s hs0 v)
            (localSqrt_sq s hs v)).symm) ((2 ^ i : ℕ) : ℤ) t) := by
  apply Subtype.ext
  rfl

/-- PROVED (the step tacit in tex 3413–3416, 3442–3444: the twist identification
`B[2^i] ≅ E[2^i](χ_h)` respects the Weil pairings). **`e^{E_v}(φ_q t₁, φ_q t₂) = e^B(t₁, t₂)`**:
`iotaWeilVc_weilPairing` for the change of variables of the twist, and transport of the Weil
pairing along the equality of curves (Tau Ceti `weilPairing_torsionByCongr_cast`). -/
theorem iotaWeilTwist_invariance (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilE W i v (iotaWeilTwist W i s hs hs0 v t₁) (iotaWeilTwist W i s hs hs0 v t₂) =
      iotaWeilB W i s hs hs0 v t₁ t₂ := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v
  rw [iotaWeilTwist_eq_vc, iotaWeilTwist_eq_vc]
  refine (iotaWeilVc_weilPairing _ _ (2 ^ i) (iotaWeil_natCast_ne_zero_loc v) _ _).trans ?_
  exact WeierstrassCurve.weilPairing_torsionByCongr_cast _ (2 ^ i) (iotaWeil_natCast_ne_zero_loc v)
    t₁ t₂

variable (hμ : HasRootsOfUnity K S (2 ^ i))

/-- Definition. **The form `ψ₁(t₁, t₂) = ℓ_v(e^{E_v}(φ_q t₁, φ_q t₂))`** on `B(K̄_v)[2^i]`. -/
def iotaWeilFormE :
    TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+
      TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+ ZMod (2 ^ i) :=
  (AddMonoidHom.compHom (iotaWeilLog hμ v).toAddMonoidHom).comp
    (((iotaWeilE W i v).compl₂ (iotaWeilTwist W i s hs hs0 v).toAddMonoidHom).comp
      (iotaWeilTwist W i s hs hs0 v).toAddMonoidHom)

theorem iotaWeilFormE_apply (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilFormE W i s hs hs0 v hμ t₁ t₂ =
      iotaWeilLog hμ v (iotaWeilE W i v (iotaWeilTwist W i s hs hs0 v t₁)
        (iotaWeilTwist W i s hs hs0 v t₂)) :=
  rfl

/-- Definition. **The form `ψ₂(t₁, t₂) = ℓ_v(e^B(t₁, t₂))`** on `B(K̄_v)[2^i]`. -/
def iotaWeilFormB :
    TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+
      TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+ ZMod (2 ^ i) :=
  (AddMonoidHom.compHom (iotaWeilLog hμ v).toAddMonoidHom).comp (iotaWeilB W i s hs hs0 v)

theorem iotaWeilFormB_apply (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilFormB W i s hs hs0 v hμ t₁ t₂ = iotaWeilLog hμ v (iotaWeilB W i s hs hs0 v t₁ t₂) :=
  rfl

/-- PROVED (Silverman III.8.1(b), Tau Ceti `weilPairing_self`). `ψ₁` is alternating. -/
theorem iotaWeilFormE_self (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilFormE W i s hs hs0 v hμ t t = 0 := by
  rw [iotaWeilFormE_apply]
  have : iotaWeilE W i v (iotaWeilTwist W i s hs hs0 v t) (iotaWeilTwist W i s hs hs0 v t) = 0 :=
    TauCeti.Isogeny.weilPairing_self _ _ _ _
  rw [this, map_zero]

/-- PROVED (Silverman III.8.1(b)). `ψ₂` is alternating. -/
theorem iotaWeilFormB_self (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilFormB W i s hs hs0 v hμ t t = 0 := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v
  rw [iotaWeilFormB_apply]
  have : iotaWeilB W i s hs hs0 v t t = 0 := TauCeti.Isogeny.weilPairing_self _ _ _ _
  rw [this, map_zero]

/-- PROVED (Silverman III.8.1(c), Tau Ceti `weilPairing_nondegenerate`). `ψ₁` is nondegenerate
(`φ_q` is bijective). -/
theorem iotaWeilFormE_sep (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i))
    (ht : ∀ t', iotaWeilFormE W i s hs hs0 v hμ t t' = 0) : t = 0 := by
  apply (iotaWeilTwist W i s hs hs0 v).injective
  rw [map_zero]
  refine TauCeti.Isogeny.weilPairing_nondegenerate
    ((W.baseChange (v.adicCompletion K)).baseChange (AlgebraicClosure (v.adicCompletion K)))
    (2 ^ i) (iotaWeil_natCast_ne_zero_loc v) fun T => ?_
  obtain ⟨t', rfl⟩ := (iotaWeilTwist W i s hs hs0 v).surjective T
  have h1 : iotaWeilLog hμ v (iotaWeilE W i v (iotaWeilTwist W i s hs hs0 v t)
      (iotaWeilTwist W i s hs hs0 v t')) = 0 := ht t'
  exact (iotaWeilLog hμ v).injective (h1.trans (map_zero _).symm)

/-- PROVED (Silverman III.8.1(c)). `ψ₂` is nondegenerate. -/
theorem iotaWeilFormB_sep (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i))
    (ht : ∀ t', iotaWeilFormB W i s hs hs0 v hμ t t' = 0) : t = 0 := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v
  refine TauCeti.Isogeny.weilPairing_nondegenerate
    ((localTwist W h v).baseChange (AlgebraicClosure (v.adicCompletion K)))
    (2 ^ i) (iotaWeil_natCast_ne_zero_loc v) fun T => ?_
  have h1 : iotaWeilLog hμ v (iotaWeilB W i s hs hs0 v t T) = 0 := ht T
  exact (iotaWeilLog hμ v).injective (h1.trans (map_zero _).symm)

/-- PROVED. **`ψ₁ = u · ψ₂` for a unit `u` of `ℤ/2^i`**: both are alternating nondegenerate
`ℤ/2^i`-bilinear forms on `B(K̄_v)[2^i]`, free of rank two (Tau Ceti `nonempty_basis_torsionBy`),
so they differ by a unit (`iotaWeil_alt_eq_unit_mul`). -/
theorem iotaWeil_exists_unit :
    ∃ u : (ZMod (2 ^ i))ˣ, ∀ t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i),
      iotaWeilFormE W i s hs hs0 v hμ t₁ t₂ = u * iotaWeilFormB W i s hs hs0 v hμ t₁ t₂ := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v
  let : Module (ZMod (2 ^ i)) (TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :=
    TauCeti.Isogeny.pointTorsionModule
      ((localTwist W h v).baseChange (AlgebraicClosure (v.adicCompletion K))) (2 ^ i)
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) (ZMod (2 ^ i))
      (TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i))) :=
    WeierstrassCurve.nonempty_basis_torsionBy _ _ (iotaWeil_natCast_ne_zero_loc v)
  exact iotaWeil_alt_eq_unit_mul b (iotaWeilBilin (iotaWeilFormE W i s hs hs0 v hμ))
    (iotaWeilBilin (iotaWeilFormB W i s hs hs0 v hμ)) (iotaWeilFormE_self W i s hs hs0 v hμ)
    (iotaWeilFormB_self W i s hs hs0 v hμ) (iotaWeilFormE_sep W i s hs hs0 v hμ)
    (iotaWeilFormB_sep W i s hs hs0 v hμ)

/-- Definition. **The unit `u`** comparing `ℓ_v ∘ e^{E_v} ∘ (φ_q × φ_q)` with `ℓ_v ∘ e^B`
(`iotaWeilUnit_spec`). -/
def iotaWeilUnit : (ZMod (2 ^ i))ˣ :=
  Classical.choose (iotaWeil_exists_unit W i s hs hs0 v hμ)

/-- PROVED. `ℓ_v(e^{E_v}(φ_q t₁, φ_q t₂)) = u · ℓ_v(e^B(t₁, t₂))`. -/
theorem iotaWeilUnit_spec (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilFormE W i s hs hs0 v hμ t₁ t₂ =
      (iotaWeilUnit W i s hs hs0 v hμ : ZMod (2 ^ i)) * iotaWeilFormB W i s hs hs0 v hμ t₁ t₂ :=
  Classical.choose_spec (iotaWeil_exists_unit W i s hs hs0 v hμ) t₁ t₂

/-- PROVED. If the twist identification respects the Weil pairings exactly, the unit is `1`. The
hypothesis holds (`iotaWeilTwist_invariance`); see `iotaWeilUnit_eq_one`. -/
theorem iotaWeilUnit_eq_one_of_invariance
    (hinv : ∀ t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i),
      iotaWeilE W i v (iotaWeilTwist W i s hs hs0 v t₁) (iotaWeilTwist W i s hs hs0 v t₂) =
        iotaWeilB W i s hs hs0 v t₁ t₂) :
    iotaWeilUnit W i s hs hs0 v hμ = 1 := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v
  let : Module (ZMod (2 ^ i)) (TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :=
    TauCeti.Isogeny.pointTorsionModule
      ((localTwist W h v).baseChange (AlgebraicClosure (v.adicCompletion K))) (2 ^ i)
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) (ZMod (2 ^ i))
      (TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i))) :=
    WeierstrassCurve.nonempty_basis_torsionBy _ _ (iotaWeil_natCast_ne_zero_loc v)
  obtain ⟨c, hc⟩ := iotaWeil_isUnit_of_separating b
    (iotaWeilBilin (iotaWeilFormB W i s hs hs0 v hμ)) (iotaWeilFormB_self W i s hs hs0 v hμ)
    (iotaWeilFormB_sep W i s hs hs0 v hμ)
  have h1 := iotaWeilUnit_spec W i s hs hs0 v hμ (b 0) (b 1)
  rw [iotaWeilFormE_apply, hinv, ← iotaWeilFormB_apply] at h1
  have h2 : iotaWeilFormB W i s hs hs0 v hμ (b 0) (b 1) = c := hc.symm
  rw [h2] at h1
  apply Units.ext
  have h3 := congrArg (fun z => z * ((c⁻¹ : (ZMod (2 ^ i))ˣ) : ZMod (2 ^ i))) h1
  simp only [mul_assoc, Units.mul_inv, mul_one] at h3
  rw [Units.val_one]
  exact h3.symm

/-- PROVED. **`u = 1`** (`iotaWeilTwist_invariance`). -/
theorem iotaWeilUnit_eq_one : iotaWeilUnit W i s hs hs0 v hμ = 1 :=
  iotaWeilUnit_eq_one_of_invariance W i s hs hs0 v hμ (iotaWeilTwist_invariance W i s hs hs0 v)

end Twist

/-! ### The main formula -/

section Pairing

variable (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (hFull : FullTorsion K S W (2 ^ i))
  (v : HeightOneSpectrum (𝓞 K)) (hμ : HasRootsOfUnity K S (2 ^ i)) (α : GKS K S →* (Acoef i)ˣ)

/-- PROVED. RC28's `weilPairingM` on pure tensors `1 ⊗ P`, `1 ⊗ Q` is `weilS(P, Q)` in `A_i`. -/
theorem iotaWeil_weilPairingM_oneTmul (P Q : TorsS K S W ((2 ^ i : ℕ) : ℤ)) :
    CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)
        (weilPairingM W hμ (Acoef i) α (oneTmul (Acoef i) α _ P)
          (oneTmul (Acoef i) (charInv α) _ Q)) =
      algebraMap (ZMod (2 ^ i)) (Acoef i) (weilS W hμ P Q) := by
  show (1 * 1) * algebraMap (ZMod (2 ^ i)) (Acoef i) (weilS W hμ P Q) = _
  rw [one_mul, one_mul]

/-- PROVED (tex 3442–3444, the comparison of the dualities). **The Kummer coefficient maps carry
the Weil pairing of `E_v`, transported along the twist, to lane RC28's pairing**:
`weilPairingM (ι_v t₁) (ι'_v t₂) = ℓ_v(e^{E_v}(φ_q t₁, φ_q t₂))` in `A_i(1) ≅ A_i`, with `ι_v` for
`α` and `ι'_v` for `α⁻¹` (`kummerIotaBase`). Exact (no unit). -/
theorem iotaWeil_pairing_exact
    (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)
        (weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t₁)
          (kummerIotaBase W i s hs hs0 (charInv α) hFull v t₂)) =
      algebraMap (ZMod (2 ^ i)) (Acoef i) (iotaWeilFormE W i s hs hs0 v hμ t₁ t₂) := by
  rw [kummerIotaBase_apply, kummerIotaBase_apply, iotaWeil_weilPairingM_oneTmul,
    iotaWeil_weilS_eq W hμ v, ← compTorsEquiv_apply W _ hFull, ← compTorsEquiv_apply W _ hFull,
    AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

/-- PROVED (tex 3442–3444). **The main formula: the Kummer coefficient maps `ι_v` respect the Weil
pairing**: for `t₁, t₂ ∈ B(K̄_v)[2^i]`,
`weilPairingM (ι_v t₁) (ι'_v t₂) = ℓ_v(e^B(t₁, t₂))` in `A_i(1) ≅ A_i`, where `e^B` is the Weil
pairing of the local twist `B = E^{(h)}` over `K̄_v` (Tau Ceti, `iotaWeilB`), `ℓ_v` the discrete
logarithm at `j(ζ)` (`iotaWeilLog`, `ζ` the primitive root behind `hμ`), `ι_v` for `α` and `ι'_v`
for `α⁻¹` (`kummerIotaBase`). The unit of the requested formula is `u = 1`. Hypotheses:
`FullTorsion` (GLUE, lane RC28) for `ι_v`. -/
theorem iotaWeil_pairing (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)
        (weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t₁)
          (kummerIotaBase W i s hs hs0 (charInv α) hFull v t₂)) =
      algebraMap (ZMod (2 ^ i)) (Acoef i) (iotaWeilLog hμ v (iotaWeilB W i s hs hs0 v t₁ t₂)) := by
  rw [iotaWeil_pairing_exact, iotaWeilFormE_apply, iotaWeilTwist_invariance]

/-- PROVED. The main formula in the form with the unit `u = iotaWeilUnit … ` (which is `1`,
`iotaWeilUnit_eq_one`): `weilPairingM (ι_v t₁) (ι'_v t₂) = u · ℓ_v(e^B(t₁, t₂))`. -/
theorem iotaWeil_pairing_unit (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)
        (weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t₁)
          (kummerIotaBase W i s hs hs0 (charInv α) hFull v t₂)) =
      algebraMap (ZMod (2 ^ i)) (Acoef i)
        ((iotaWeilUnit W i s hs hs0 v hμ : ZMod (2 ^ i)) *
          iotaWeilLog hμ v (iotaWeilB W i s hs hs0 v t₁ t₂)) := by
  rw [iotaWeil_pairing_exact, iotaWeilUnit_spec, iotaWeilFormB_apply]

/-- PROVED. The main formula from an invariance hypothesis (which holds:
`iotaWeilTwist_invariance`; kept for the form announced first). -/
theorem iotaWeil_pairing_of_invariance
    (hinv : ∀ t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i),
      iotaWeilE W i v (iotaWeilTwist W i s hs hs0 v t₁) (iotaWeilTwist W i s hs hs0 v t₂) =
        iotaWeilB W i s hs hs0 v t₁ t₂)
    (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)
        (weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t₁)
          (kummerIotaBase W i s hs hs0 (charInv α) hFull v t₂)) =
      algebraMap (ZMod (2 ^ i)) (Acoef i) (iotaWeilLog hμ v (iotaWeilB W i s hs hs0 v t₁ t₂)) := by
  rw [iotaWeil_pairing_exact, iotaWeilFormE_apply, hinv]

/-- PROVED. **`ψ(t₁, t₂) = weilPairingM (ι_v t₁) (ι'_v t₂)` takes values in the image of
`ℤ/2^i`.** -/
theorem iotaWeil_pairing_mem_range
    (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    ∃ z : ZMod (2 ^ i), CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)
        (weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t₁)
          (kummerIotaBase W i s hs hs0 (charInv α) hFull v t₂)) =
      algebraMap (ZMod (2 ^ i)) (Acoef i) z :=
  ⟨_, iotaWeil_pairing_exact W i s hs hs0 hFull v hμ α t₁ t₂⟩

/-- PROVED (Silverman III.8.1(b)). **`ψ` is alternating**: `weilPairingM (ι_v t) (ι'_v t) = 0`. -/
theorem iotaWeil_pairing_self (t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t)
      (kummerIotaBase W i s hs hs0 (charInv α) hFull v t) = 0 := by
  apply (CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)).injective
  rw [iotaWeil_pairing_exact, iotaWeilFormE_self, map_zero, map_zero]

/-- PROVED (tex 2798–2805, 3413–3438). **`ψ` is `G_{K_v}`-equivariant into `A_i(1)`**, `G_{K_v}`
acting through `p_v = locMap` on `A_i(1)` (the cyclotomic character), when the character `α` of
`M_i` is `χ_h` on the decomposition group (the landed `IsLocallyQuadAt`; for `α⁻¹` by
`isLocallyQuadAt_charInv`): `ψ(σ t₁, σ t₂) = p_v(σ) • ψ(t₁, t₂)`. -/
theorem iotaWeil_pairing_smul (hα : IsLocallyQuadAt i α (quadChar s hs hs0) v) (σ : Gloc K v)
    (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v (σ • t₁))
        (kummerIotaBase W i s hs hs0 (charInv α) hFull v (σ • t₂)) =
      locMap K S v σ • weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t₁)
        (kummerIotaBase W i s hs hs0 (charInv α) hFull v t₂) := by
  rw [kummerIotaBase_smul W i s hs hs0 α hFull v hα σ t₁,
    kummerIotaBase_smul W i s hs hs0 (charInv α) hFull v (isLocallyQuadAt_charInv hα) σ t₂,
    weilPairingM_smul]

end Pairing

/-! ### Perfectness and equivariance of the `ℤ/2^i`-valued form `ψ₀ = ℓ_v ∘ e^B` -/

section Perfect

variable (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (v : HeightOneSpectrum (𝓞 K))
  (hμ : HasRootsOfUnity K S (2 ^ i))

/-- Definition. **The `ℤ/2^i`-valued form `ψ₀(t₁, t₂) = ℓ_v(e^B(t₁, t₂))`** of the main formula
(`ψ = algebraMap ∘ ψ₀`; `iotaWeilForm_apply`). -/
abbrev iotaWeilForm :
    TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+
      TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i) →+ ZMod (2 ^ i) :=
  iotaWeilFormE W i s hs hs0 v hμ

/-- PROVED. `ψ₀(t₁, t₂) = ℓ_v(e^B(t₁, t₂))`. -/
theorem iotaWeilForm_apply (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilForm W i s hs hs0 v hμ t₁ t₂ = iotaWeilLog hμ v (iotaWeilB W i s hs hs0 v t₁ t₂) :=
  (iotaWeilFormE_apply W i s hs hs0 v hμ t₁ t₂).trans
    (congrArg (iotaWeilLog hμ v) (iotaWeilTwist_invariance W i s hs hs0 v t₁ t₂))

/-- PROVED (Silverman III.8.1(b): skew-symmetry). `ψ₀(t₂, t₁) = −ψ₀(t₁, t₂)`. -/
theorem iotaWeilForm_swap (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilForm W i s hs hs0 v hμ t₂ t₁ = -iotaWeilForm W i s hs hs0 v hμ t₁ t₂ := by
  have h0 : iotaWeilFormE W i s hs hs0 v hμ (t₁ + t₂) (t₁ + t₂) = 0 :=
    iotaWeilFormE_self W i s hs hs0 v hμ (t₁ + t₂)
  rw [map_add, map_add, AddMonoidHom.add_apply, AddMonoidHom.add_apply,
    iotaWeilFormE_self, iotaWeilFormE_self, zero_add, add_zero] at h0
  linear_combination h0

include hs hs0 in
/-- PROVED. `|B(K̄_v)[2^i]| = (2^i)²` (through the twist identification and lane RC29's
`natCard_torsAlg_adic`). -/
theorem iotaWeil_natCard_torsB :
    Nat.card (TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) = (2 ^ i) ^ 2 := by
  rw [Nat.card_congr (iotaWeilTwist W i s hs hs0 v).toEquiv]
  exact natCard_torsAlg_adic W (2 ^ i) v

/-- PROVED (Silverman III.8.1(c) with the count `|B[2^i]| = (2^i)²`). **`ψ₀` is perfect**: both
adjoints `B[2^i] → Hom(B[2^i], ℤ/2^i)` are bijective. -/
theorem iotaWeilForm_perfect :
    Function.Bijective (iotaWeilForm W i s hs hs0 v hμ) ∧
      Function.Bijective (iotaWeilForm W i s hs hs0 v hμ).flip := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v
  have := finite_addMonoidHom (TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i))
    (ZMod (2 ^ i))
  have hinj1 : Function.Injective (iotaWeilForm W i s hs hs0 v hμ) := by
    refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
    exact iotaWeilFormE_sep W i s hs hs0 v hμ t fun t' => by
      have h1 := DFunLike.congr_fun ht t'
      rw [AddMonoidHom.zero_apply] at h1
      exact h1
  have hinj2 : Function.Injective (iotaWeilForm W i s hs hs0 v hμ).flip := by
    refine (injective_iff_map_eq_zero _).2 fun t ht => ?_
    exact iotaWeilFormE_sep W i s hs hs0 v hμ t fun t' => by
      have h1 := congrArg (fun f => f t') ht
      simp only [AddMonoidHom.flip_apply, AddMonoidHom.zero_apply] at h1
      have h2 := iotaWeilForm_swap W i s hs hs0 v hμ t' t
      rw [h1, neg_zero] at h2
      exact h2
  exact ⟨hinj1.bijective_of_nat_card_le (natCard_addMonoidHom_zmod_le _ _),
    hinj2.bijective_of_nat_card_le (natCard_addMonoidHom_zmod_le _ _)⟩

/-- PROVED. The constant coefficient retracts `ℤ/2^i → A_i` (`i ≠ 0`). -/
theorem iotaWeil_acoefConst_algebraMap (hi : i ≠ 0) (z : ZMod (2 ^ i)) :
    acoefConst i hi (algebraMap (ZMod (2 ^ i)) (Acoef i) z) = z := by
  show acoefConst i hi (Ideal.Quotient.mk _ (Polynomial.C z)) = z
  rw [acoefConst, Ideal.Quotient.lift_mk, Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]

/-- PROVED. **`ψ` is nondegenerate on the left** (`i ≠ 0`): if `weilPairingM (ι_v t₁) (ι'_v t₂) = 0`
for all `t₂`, then `t₁ = 0`. -/
theorem iotaWeil_pairing_nondegenerate_left (hi : i ≠ 0) (hFull : FullTorsion K S W (2 ^ i))
    (α : GKS K S →* (Acoef i)ˣ) (t₁ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i))
    (ht : ∀ t₂, weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t₁)
      (kummerIotaBase W i s hs hs0 (charInv α) hFull v t₂) = 0) : t₁ = 0 := by
  refine iotaWeilFormE_sep W i s hs hs0 v hμ t₁ fun t₂ => ?_
  have h1 := congrArg (CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)) (ht t₂)
  rw [iotaWeil_pairing_exact, map_zero] at h1
  have h2 := congrArg (acoefConst i hi) h1
  rwa [iotaWeil_acoefConst_algebraMap i hi, map_zero] at h2

/-- PROVED. **`ψ` is nondegenerate on the right** (`i ≠ 0`). -/
theorem iotaWeil_pairing_nondegenerate_right (hi : i ≠ 0) (hFull : FullTorsion K S W (2 ^ i))
    (α : GKS K S →* (Acoef i)ˣ) (t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i))
    (ht : ∀ t₁, weilPairingM W hμ (Acoef i) α (kummerIotaBase W i s hs hs0 α hFull v t₁)
      (kummerIotaBase W i s hs hs0 (charInv α) hFull v t₂) = 0) : t₂ = 0 := by
  refine iotaWeilFormE_sep W i s hs hs0 v hμ t₂ fun t₁ => ?_
  have h1 := congrArg (CharMod.equiv (Acoef i) (cycA (Acoef i) hμ)) (ht t₁)
  rw [iotaWeil_pairing_exact, map_zero] at h1
  have h2 := congrArg (acoefConst i hi) h1
  rw [iotaWeil_acoefConst_algebraMap i hi, map_zero] at h2
  have h3 := iotaWeilForm_swap W i s hs hs0 v hμ t₁ t₂
  change iotaWeilFormE W i s hs hs0 v hμ t₂ t₁ = -iotaWeilFormE W i s hs hs0 v hμ t₁ t₂ at h3
  rw [h3, h2, neg_zero]

/-- PROVED (Silverman III.8.1(e), Tau Ceti `weilPairing_torsionGaloisAction`). **`e^B` is
`G_{K_v}`-equivariant**: `e^B(σ t₁, σ t₂) = σ(e^B(t₁, t₂))`. -/
theorem iotaWeilB_smul (σ : Gloc K v)
    (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilB W i s hs hs0 v (σ • t₁) (σ • t₂) =
      Additive.ofMul (restrictRootsOfUnity (iotaWeilGal v σ) (2 ^ i)
        (iotaWeilB W i s hs hs0 v t₁ t₂).toMul) := by
  have := isElliptic_localTwist W (ne_zero_of_sqrt s hs hs0) v
  have e : ∀ t : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i),
      σ • t = Multiplicative.toAdd ((localTwist W h v).torsionGaloisAction ((2 ^ i : ℕ) : ℤ)
        (iotaWeilGal v σ)) t := fun t =>
    Subtype.ext ((torsionGaloisAction_eq_smul (B := localTwist W h v) σ t).symm)
  rw [e t₁, e t₂]
  exact WeierstrassCurve.weilPairing_torsionGaloisAction (localTwist W h v) (2 ^ i)
    (iotaWeil_natCast_ne_zero_loc v) (iotaWeilGal v σ) t₁ t₂

/-- PROVED. **`ψ₀` is `G_{K_v}`-equivariant into `(ℤ/2^i)(1)`**:
`ψ₀(σ t₁, σ t₂) = χ_cyc(p_v σ) · ψ₀(t₁, t₂)` (lane RC28's `cycS` through `locMap`). -/
theorem iotaWeilForm_smul (σ : Gloc K v)
    (t₁ t₂ : TorsAlg (v.adicCompletion K) (localTwist W h v) (2 ^ i)) :
    iotaWeilForm W i s hs hs0 v hμ (σ • t₁) (σ • t₂) =
      ((cycS hμ (locMap K S v σ) : (ZMod (2 ^ i))ˣ) : ZMod (2 ^ i)) *
        iotaWeilForm W i s hs hs0 v hμ t₁ t₂ := by
  rw [iotaWeilForm_apply, iotaWeilForm_apply, iotaWeilB_smul, iotaWeilLog_smul]

end Perfect

/-! ### Non-vacuity -/

section NonVacuity

variable (S : Set (HeightOneSpectrum (𝓞 ℚ)))

/-- PROVED (non-vacuity of `hμ`). `μ_2 ⊂ K_S` over `ℚ`, for every `S` (lane RC28's
`hasRootsOfUnity_of_fullTorsion` for `E_1`, with the landed `fullTorsion_curveEll_one`). -/
theorem iotaWeil_hasRootsOfUnity_one : HasRootsOfUnity ℚ S (2 ^ 1) :=
  haveI := isElliptic_curveEll (K := ℚ) one_ne_zero
  hasRootsOfUnity_of_fullTorsion ℚ S (curveEll 1) (2 ^ 1) (fullTorsion_curveEll_one S)

/-- PROVED (non-vacuity of all hypotheses of the main formula): over `ℚ`, for `E_1`, `h = 1`,
`i = 1`, the landed `alphaOne`, every `S` and every place `v`. -/
theorem iotaWeil_pairing_nonvacuous (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI := isElliptic_curveEll (K := ℚ) one_ne_zero
    ∀ t₁ t₂ : TorsAlg (v.adicCompletion ℚ) (localTwist (curveEll (1 : ℚ)) 1 v) (2 ^ 1),
      CharMod.equiv (Acoef 1) (cycA (Acoef 1) (iotaWeil_hasRootsOfUnity_one S))
          (weilPairingM (curveEll 1) (iotaWeil_hasRootsOfUnity_one S) (Acoef 1) (alphaOne S 1)
            (kummerIotaBase (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (alphaOne S 1)
              (fullTorsion_curveEll_one S) v t₁)
            (kummerIotaBase (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (charInv (alphaOne S 1))
              (fullTorsion_curveEll_one S) v t₂)) =
        algebraMap (ZMod (2 ^ 1)) (Acoef 1)
          (iotaWeilLog (iotaWeil_hasRootsOfUnity_one S) v
            (iotaWeilB (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero v t₁ t₂)) := by
  have := isElliptic_curveEll (K := ℚ) one_ne_zero
  exact iotaWeil_pairing (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero
    (fullTorsion_curveEll_one S) v (iotaWeil_hasRootsOfUnity_one S) (alphaOne S 1)

/-- PROVED (non-vacuity of the hypotheses of `iotaWeil_pairing_smul`): the equivariance of `ψ`
holds for `E_1`, `h = 1`, `i = 1`, `alphaOne`, every `S`, `v`. -/
theorem iotaWeil_pairing_smul_nonvacuous (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI := isElliptic_curveEll (K := ℚ) one_ne_zero
    ∀ (σ : Gloc ℚ v) (t₁ t₂ : TorsAlg (v.adicCompletion ℚ)
        (localTwist (curveEll (1 : ℚ)) 1 v) (2 ^ 1)),
      weilPairingM (curveEll 1) (iotaWeil_hasRootsOfUnity_one S) (Acoef 1) (alphaOne S 1)
          (kummerIotaBase (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (alphaOne S 1)
            (fullTorsion_curveEll_one S) v (σ • t₁))
          (kummerIotaBase (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (charInv (alphaOne S 1))
            (fullTorsion_curveEll_one S) v (σ • t₂)) =
        locMap ℚ S v σ • weilPairingM (curveEll 1) (iotaWeil_hasRootsOfUnity_one S) (Acoef 1)
          (alphaOne S 1)
          (kummerIotaBase (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (alphaOne S 1)
            (fullTorsion_curveEll_one S) v t₁)
          (kummerIotaBase (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (charInv (alphaOne S 1))
            (fullTorsion_curveEll_one S) v t₂) := by
  have := isElliptic_curveEll (K := ℚ) one_ne_zero
  exact iotaWeil_pairing_smul (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero
    (fullTorsion_curveEll_one S) v (iotaWeil_hasRootsOfUnity_one S) (alphaOne S 1)
    (isLocallyQuadAt_alphaOne S 1 v)

end NonVacuity

end ZInQ.Manuscript.RC.KummerMaps
