import ZInQKernel.Contrib.CloudB3RC53.DetTateCyclotomic.Basic

/-!
# `det ρ₂ = χ₂`: the determinant of the `2`-adic Tate representation is the cyclotomic character

Target (with the same body as `DetTateTwoEqCyclotomic` of
`ZInQKernel/Contrib/OneProof/RC/TateWiring/Image.lean`, namespace `ZInQ.Manuscript.RC.TateWiring`,
of the Theorem 5.3 lanes; bridged by definitional equality in `RC/TateWiring/Discharge.lean`,
`detTateTwoEqCyclotomic_holds`):

```
DetTateTwoEqCyclotomic E :=
  ∀ σ : GalQ, LinearMap.det (tateRep E 2 σ) = (cyclotomicCharacter Qbar 2 σ.toRingEquiv : ℤ_[2])
```

with Mathlib's `cyclotomicCharacter`. PROVED here for **every elliptic curve `E/ℚ`**
(`detTateTwoEqCyclotomic`). Serre 1972, p. 300 (McGill notes, pp. I-3, I-4); Silverman III.8.1.

**Proof.** For `N = 2^k` the argument of `Basic.lean` gives, for all `S, T ∈ E[N]`,
`e_N(σS, σT) = (det ρ₂(σ) mod N) · e_N(S, T)` (`weilPairing_galois_eq_det`: `A` the matrix of
`ρ₂(σ)` in a `ℤ₂`-basis of `T₂E`, `e_N` alternating and `ZMod N`-bilinear). With Galois
equivariance and the surjectivity of `e_N(S, ·)` onto `μ_N`, `σ` acts on `μ_N` by
`t ↦ t^{det mod N}`, so `det ρ₂(σ) mod N` is the modular cyclotomic character of `σ`
(`modularCyclotomicCharacter.unique`), which is `χ₂(σ) mod N`
(`cyclotomicCharacter.toZModPow`). Equality at every level gives equality in `ℤ₂`
(`PadicInt.ext_of_toZModPow`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic

open ZInQ.Manuscript.RC.PrintsArith TauCeti TauCeti.Isogeny WeierstrassCurve
open scoped WeierstrassCurve

/-- **`det ρ₂ = χ₂`** (same body as `RC/TateWiring/Image.lean`'s `DetTateTwoEqCyclotomic`,
namespace `ZInQ.Manuscript.RC.TateWiring`): the determinant of the `2`-adic Tate representation
is Mathlib's `2`-adic cyclotomic character. -/
def DetTateTwoEqCyclotomic (E : WeierstrassCurve ℚ) : Prop :=
  ∀ σ : GalQ, LinearMap.det (tateRep E 2 σ) = (cyclotomicCharacter Qbar 2 σ.toRingEquiv : ℤ_[2])

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The Weil pairing transforms by the determinant**: for `N = 2^k`,
`e_N(σS, σT) = (det ρ₂(σ) mod N) · e_N(S, T)` for all `S, T ∈ E[N]`. -/
theorem weilPairing_galois_eq_det (σ : GalQ) (k : ℕ)
    (hN : ((2 ^ k : ℕ) : Qbar) ≠ 0)
    (S T : AddSubgroup.torsionBy (E⁄Qbar).toAffine.Point ((2 ^ k : ℕ) : ℤ)) :
    weilPairingBilin (E⁄Qbar) (2 ^ k) hN
        (Multiplicative.toAdd (E.torsionGaloisAction ((2 ^ k : ℕ) : ℤ) σ) S)
        (Multiplicative.toAdd (E.torsionGaloisAction ((2 ^ k : ℕ) : ℤ) σ) T) =
      PadicInt.toZModPow k (LinearMap.det (tateRep E 2 σ)) •
        weilPairingBilin (E⁄Qbar) (2 ^ k) hN S T := by
  have hℓ : ((2 : ℕ) : Qbar) ≠ 0 := by norm_num
  -- a `ℤ₂`-basis of `T₂E` and the matrix of `ρ₂(σ)`
  obtain ⟨e⟩ := (E⁄Qbar).nonempty_linearEquiv_tateModule (ℓ := 2) hℓ
  let b : Module.Basis (Fin 2) ℤ_[2] (TateMod E 2) := Module.Basis.ofEquivFun e
  set f := tateRep E 2 σ with hfdef
  set Am := LinearMap.toMatrix b b f with hAm
  have hdet : Am.det = LinearMap.det f := by rw [hAm, LinearMap.det_toMatrix]
  have hf : ∀ j, f (b j) = Am 0 j • b 0 + Am 1 j • b 1 := by
    intro j
    conv_lhs => rw [← b.sum_repr (f (b j))]
    rw [Fin.sum_univ_two, hAm, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
  -- reduction modulo `2^k` and the level-`k` images of the basis
  let red : ℤ_[2] →+* ZMod (2 ^ k) := PadicInt.toZModPow k
  let P : Fin 2 → AddSubgroup.torsionBy (E⁄Qbar).toAffine.Point ((2 ^ k : ℕ) : ℤ) :=
    fun j => TateModule.proj k (b j)
  have hproj : ∀ x : TateMod E 2, TateModule.proj k x =
      red (b.repr x 0) • P 0 + red (b.repr x 1) • P 1 := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum, Fin.sum_univ_two, TateModule.proj_smul, TateModule.proj_smul]
  let act := Multiplicative.toAdd (E.torsionGaloisAction ((2 ^ k : ℕ) : ℤ) σ)
  have hact : ∀ x : TateMod E 2, act (TateModule.proj k x) = TateModule.proj k (f x) := by
    intro x
    apply Subtype.ext
    rw [torsionGaloisAction_apply_coe, pointGaloisAction_apply, hfdef, coe_proj_tateRep]
  have hactP : ∀ j, act (P j) = red (Am 0 j) • P 0 + red (Am 1 j) • P 1 := by
    intro j
    change act (TateModule.proj k (b j)) = _
    rw [hact, hf, map_add, TateModule.proj_smul, TateModule.proj_smul]
  have hactsmul : ∀ (c : ZMod (2 ^ k)) X, act (c • X) = c • act X := by
    intro c X
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  -- every point of `E[N]` is a combination of `P₀, P₁`
  have hsurj : Function.Surjective
      (TateModule.proj (p := 2) (A := (E⁄Qbar).toAffine.Point) k) :=
    TateModule.proj_surjective
      (TateModule.tateModuleTransition_surjective_of_natCard (by norm_num)
        ((E⁄Qbar).natCard_tateModuleLevel hℓ)) k
  obtain ⟨s, rfl⟩ := hsurj S
  obtain ⟨t, rfl⟩ := hsurj T
  set B := weilPairingBilin (E⁄Qbar) (2 ^ k) hN
  have hB := isAlt_weilPairingBilin (E⁄Qbar) (2 ^ k) hN
  have hdet2 : red (Am 0 0) * red (Am 1 1) - red (Am 0 1) * red (Am 1 0) =
      PadicInt.toZModPow k (LinearMap.det f) := by
    have h := congrArg red hdet
    rwa [Matrix.det_fin_two, map_sub, map_mul, map_mul] at h
  set s0 := red (b.repr s 0)
  set s1 := red (b.repr s 1)
  set t0 := red (b.repr t 0)
  set t1 := red (b.repr t 1)
  have hS : act (TateModule.proj k s) =
      (s0 * red (Am 0 0) + s1 * red (Am 0 1)) • P 0 +
        (s0 * red (Am 1 0) + s1 * red (Am 1 1)) • P 1 := by
    rw [hproj s, map_add, hactsmul, hactsmul, hactP, hactP]
    module
  have hT : act (TateModule.proj k t) =
      (t0 * red (Am 0 0) + t1 * red (Am 0 1)) • P 0 +
        (t0 * red (Am 1 0) + t1 * red (Am 1 1)) • P 1 := by
    rw [hproj t, map_add, hactsmul, hactsmul, hactP, hactP]
    module
  change B (act (TateModule.proj k s)) (act (TateModule.proj k t)) = _
  rw [hS, hT, hproj s, hproj t, isAlt_comb B hB, isAlt_comb B hB, smul_smul]
  congr 1
  linear_combination (s0 * t1 - s1 * t0) * hdet2

/-- **`det ρ₂ = χ₂` for every elliptic curve `E/ℚ`** (PROVED). -/
theorem detTateTwoEqCyclotomic : DetTateTwoEqCyclotomic E := by
  intro σ
  refine PadicInt.ext_of_toZModPow.mp fun k => ?_
  have hN : ((2 ^ k : ℕ) : Qbar) ≠ 0 := by
    exact_mod_cast (pow_ne_zero k two_ne_zero : (2 : ℕ) ^ k ≠ 0)
  rw [show (cyclotomicCharacter Qbar 2 σ.toRingEquiv : ℤ_[2]) =
      (cyclotomicCharacter Qbar 2 σ.toRingEquiv).val from rfl, cyclotomicCharacter.toZModPow]
  refine modularCyclotomicCharacter.unique _ _ σ.toRingEquiv fun t ht => ?_
  obtain ⟨S, hS⟩ := exists_surjective_weilPairing (E⁄Qbar) (2 ^ k) hN
  obtain ⟨T, hT⟩ := hS (Additive.ofMul ⟨t, ht⟩)
  have h := weilPairing_torsionGaloisAction E (2 ^ k) hN σ S T
  have hdet := weilPairing_galois_eq_det E σ k hN S T
  rw [weilPairingBilin_apply, weilPairingBilin_apply] at hdet
  rw [hdet, hT, ← ZMod.natCast_zmod_val (PadicInt.toZModPow k (LinearMap.det (tateRep E 2 σ))),
    Nat.cast_smul_eq_nsmul] at h
  have h' := congrArg (fun x ↦ (((Additive.toMul x : rootsOfUnity (2 ^ k) Qbar) : Qbarˣ) : Qbar)) h
  simp only [toMul_nsmul, toMul_ofMul, SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val] at h'
  rw [restrictRootsOfUnity_coe_apply] at h'
  simpa using h'.symm

end ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic
