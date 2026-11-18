import ZInQKernel.Contrib.OneProof.RC.PrintsArith.Serre
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Bilinear
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Galois
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.RootsOfUnity

/-!
# `det ρ₂ = χ₂` in the direction used: determinant one fixes the `2`-power roots of unity

Target: lane RC9's GLUE `ZInQ.Manuscript.RC.PrintsArith.DetTateTwoCyclotomic E`
(`ZInQKernel/Contrib/OneProof/RC/PrintsArith/Serre.lean`):

```
∀ σ : GalQ, LinearMap.det (tateRep E 2 σ) = 1 →
  ∀ (k : ℕ) (ζ : Qbar), ζ ^ (2 ^ k) = 1 → σ ζ = ζ
```

used at tex L3597–3605 (`ex:arith-moving-character`: the determinant-one part of the image of
`ρ_T` is the image of `G_{ℚ(μ_{2^∞})}`). PROVED here for **every elliptic curve `E/ℚ`**
(`detTateTwoCyclotomic`), from the Weil pairing of the vendored Tau Ceti library.

**Proof.** Let `N = 2^k`, `f = ρ₂(σ)` with `det f = 1`. Choose a `ℤ₂`-basis `b₀, b₁` of `T₂E`
(free of rank two, Tau Ceti `nonempty_linearEquiv_tateModule`), let `A` be the matrix of `f`, and
`P_j = π_k(b_j) ∈ E[N]` their images at level `k`. As `π_k` is onto `E[N]` and reduces scalars
modulo `N`, every `S ∈ E[N]` is `s̄₀ P₀ + s̄₁ P₁`, and `σ P_j = Σ_i Ā_{ij} P_i`. The Weil pairing
`e_N` is `ZMod N`-bilinear and alternating (Tau Ceti `weilPairingBilin`, `isAlt_weilPairingBilin`),
so `e_N(aX + bY, cX + dY) = (ad − bc) e_N(X, Y)` (`isAlt_comb`); hence
`e_N(σS, σT) = det(Ā) e_N(S, T) = e_N(S, T)` (`weilPairing_galois_eq`), since
`det Ā = det A mod N = 1`. Galois equivariance (`weilPairing_torsionGaloisAction`) gives
`σ(e_N(S, T)) = e_N(σS, σT) = e_N(S, T)`, and `e_N(S, ·)` is onto `μ_N` for a suitable `S`
(`exists_surjective_weilPairing`), so `σ` fixes `μ_N`. This is the argument of Tau Ceti's
`algEquiv_apply_eq_self_of_torsionGaloisAction_eq_one` with "acts trivially on `E[N]`" replaced by
"has determinant one on `T₂E`".
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic

open ZInQ.Manuscript.RC.PrintsArith TauCeti TauCeti.Isogeny WeierstrassCurve
open scoped WeierstrassCurve

/-- An alternating bilinear map on two combinations: `B(aX + bY, cX + dY) = (ad − bc) B(X, Y)`. -/
theorem isAlt_comb {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module R V] (B : M →ₗ[R] M →ₗ[R] V) (hB : B.IsAlt) (x y : M) (a b c d : R) :
    B (a • x + b • y) (c • x + d • y) = (a * d - b * c) • B x y := by
  have hyx : B y x = -B x y := by
    have h := hB (x + y)
    simp only [map_add, LinearMap.add_apply, hB x, hB y, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_left h
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hB x, hB y, hyx,
    smul_zero, zero_add, add_zero]
  module

variable (E : WeierstrassCurve ℚ) [E.IsElliptic]

/-- **The Weil pairing is invariant under `σ` when `det ρ₂(σ) = 1`**: for `N = 2^k`,
`e_N(σS, σT) = e_N(S, T)` for all `S, T ∈ E[N]`. -/
theorem weilPairing_galois_eq (σ : GalQ) (hσ : LinearMap.det (tateRep E 2 σ) = 1) (k : ℕ)
    (hN : ((2 ^ k : ℕ) : Qbar) ≠ 0)
    (S T : AddSubgroup.torsionBy (E⁄Qbar).toAffine.Point ((2 ^ k : ℕ) : ℤ)) :
    weilPairingBilin (E⁄Qbar) (2 ^ k) hN
        (Multiplicative.toAdd (E.torsionGaloisAction ((2 ^ k : ℕ) : ℤ) σ) S)
        (Multiplicative.toAdd (E.torsionGaloisAction ((2 ^ k : ℕ) : ℤ) σ) T) =
      weilPairingBilin (E⁄Qbar) (2 ^ k) hN S T := by
  have hℓ : ((2 : ℕ) : Qbar) ≠ 0 := by norm_num
  -- a `ℤ₂`-basis of `T₂E` and the matrix of `ρ₂(σ)`
  obtain ⟨e⟩ := (E⁄Qbar).nonempty_linearEquiv_tateModule (ℓ := 2) hℓ
  let b : Module.Basis (Fin 2) ℤ_[2] (TateMod E 2) := Module.Basis.ofEquivFun e
  set f := tateRep E 2 σ with hfdef
  set Am := LinearMap.toMatrix b b f with hAm
  have hdet : Am.det = 1 := by rw [hAm, LinearMap.det_toMatrix]; exact hσ
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
  have hdet2 : red (Am 0 0) * red (Am 1 1) - red (Am 0 1) * red (Am 1 0) = 1 := by
    have h := congrArg red hdet
    rwa [Matrix.det_fin_two, map_sub, map_mul, map_mul, map_one] at h
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
  rw [hS, hT, hproj s, hproj t, isAlt_comb B hB, isAlt_comb B hB]
  congr 1
  linear_combination (s0 * t1 - s1 * t0) * hdet2

/-- **`DetTateTwoCyclotomic` for every elliptic curve `E/ℚ`** (PROVED): if `det ρ₂(σ) = 1`, then
`σ` fixes every `2`-power root of unity (Weil pairing; tex L3597–3605). -/
theorem detTateTwoCyclotomic : DetTateTwoCyclotomic E := by
  intro σ hσ k ζ hζ
  have hN : ((2 ^ k : ℕ) : Qbar) ≠ 0 := by
    exact_mod_cast (pow_ne_zero k two_ne_zero : (2 : ℕ) ^ k ≠ 0)
  obtain ⟨S, hS⟩ := exists_surjective_weilPairing (E⁄Qbar) (2 ^ k) hN
  obtain ⟨T, hT⟩ := hS (Additive.ofMul (rootsOfUnity.mkOfPowEq ζ hζ))
  have h := weilPairing_torsionGaloisAction E (2 ^ k) hN σ S T
  have hinv := weilPairing_galois_eq E σ hσ k hN S T
  rw [weilPairingBilin_apply, weilPairingBilin_apply] at hinv
  rw [hinv, hT] at h
  simpa using congrArg (fun x ↦ (((Additive.toMul x : rootsOfUnity (2 ^ k) Qbar) : Qbarˣ) : Qbar))
    h.symm

end ZInQ.Contrib.CloudB3RC53.DetTateCyclotomic
