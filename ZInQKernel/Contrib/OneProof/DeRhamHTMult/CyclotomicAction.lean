import ZInQKernel.Contrib.G9.KerTheta

/-! # Galois action on `p`-power roots of unity in the tilt

`σ ∈ G_{ℚ_p}` acts on a `p^k`-th root of unity `ζ ∈ 𝓞_ℂ_p` by `ζ ↦ ζ^{χ(σ) mod p^k}`
(`oAct_eq_pow`, from Mathlib's `cyclotomicCharacter.spec` on `ℚ̄_p`), and the `n`-th `p`-power root
of `σ♭(ε)` is `σ(ε^{(n)})` (`root_preTiltMap`). Hence for `ε♯ = 1`,
`(σ♭ ε)^{(k)} = (ε^{(k)})^{b_k}` with `b_k ≡ χ(σ) mod p^k` (`root_flat_eq_pow`).
-/

set_option autoImplicit false

namespace DeRhamHTMult

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.G9.BdrKer.Cp

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

theorem iterate_preTiltMap (σ : GQp p) (n : ℕ) (x : PreTilt 𝓞_ℂ_[p] p) :
    ((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) (DR.preTiltMap p (oAct p σ) x) =
      DR.preTiltMap p (oAct p σ) (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm^[n]) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      RingHom.map_frobeniusEquiv_symm]

theorem root_preTiltMap (σ : GQp p) (x : PreTilt 𝓞_ℂ_[p] p) (n : ℕ) :
    root (DR.preTiltMap p (oAct p σ) x) n = oAct p σ (root x n) := by
  rw [root, iterate_preTiltMap, DR.untilt_preTiltMap]
  rfl

/-- `σ(ζ) = ζ^{χ(σ) mod p^k}` for `ζ^{p^k} = 1` in `𝓞_ℂ_p`. -/
theorem oAct_eq_pow (σ : GQp p) (k : ℕ) {ζ : 𝓞_ℂ_[p]} (hζ : ζ ^ p ^ k = 1) :
    oAct p σ ζ = ζ ^ (PadicInt.toZModPow k (cyc p σ : ℤ_[p])).val := by
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (PadicAlgCl p) (p ^ k)
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  have hωC : IsPrimitiveRoot (algebraMap (PadicAlgCl p) ℂ_[p] ω) (p ^ k) :=
    hω.map_of_injective hinj
  have hζC : ((ζ : ℂ_[p])) ^ p ^ k = 1 := by
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hζ
    simpa using this
  obtain ⟨i, -, hi⟩ := hωC.eq_pow_of_pow_eq_one hζC
  set z : PadicAlgCl p := ω ^ i
  have hz : (ζ : ℂ_[p]) = ((z : PadicAlgCl p) : ℂ_[p]) := by
    rw [PadicComplex.coe_eq, map_pow, ← hi]
  have hzp : z ^ p ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hspec := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := k) σ.toRingEquiv z hzp
  apply Subtype.ext
  change cpAct p σ (ζ : ℂ_[p]) = ((ζ ^ _ : 𝓞_ℂ_[p]) : ℂ_[p])
  rw [hz, cpAct_coe]
  push_cast
  rw [hz]
  change (((σ.toRingEquiv z : PadicAlgCl p)) : ℂ_[p]) = _
  rw [hspec, cyc, PadicComplex.coe_eq, PadicComplex.coe_eq, map_pow]

/-- `(σ♭ ε)^{(k)} = (ε^{(k)})^{b}` with `b = (χ(σ) mod p^k)` as a natural number. -/
theorem root_flat_eq_pow (σ : GQp p) {ε : PreTilt 𝓞_ℂ_[p] p} (h1 : PreTilt.untilt ε = 1)
    (k : ℕ) : root (DR.preTiltMap p (oAct p σ) ε) k =
      root ε k ^ (PadicInt.toZModPow k (cyc p σ : ℤ_[p])).val := by
  rw [root_preTiltMap, oAct_eq_pow p σ k (by rw [root_pow, h1])]

theorem sub_val_mem (a : ℤ_[p]) (k : ℕ) :
    a - ((PadicInt.toZModPow k a).val : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
    sub_self]

theorem val_le (a : ℤ_[p]) (k : ℕ) : (PadicInt.toZModPow k a).val ≤ p ^ k := by
  have : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  exact (ZMod.val_lt _).le

end

end DeRhamHTMult
