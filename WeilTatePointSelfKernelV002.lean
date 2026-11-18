import WeilTateTorsionLiftV001
import WeilTatePointLeftNondegV003

/-!
# Both `ℓ`-adic kernels of a self-pairing on the actual `T_ℓ(A)` from a finite right-kernel container

For `A : PkgI3.AbVar K` (`K` of characteristic `0`), `Ω` algebraically closed over `K`, a prime `ℓ` and a
level pairing `P` on `A(Ω) × A(Ω)` (in the application Mumford's `e^L` for `L` defined over `K`): if every
element of every finite-level right kernel lies in one finite subgroup `C ⊆ A(Ω)` (for `e^L`, `C = K(L)`),
then the limit pairing `T_ℓ(A) × T_ℓ(A) → T_ℓ(μ(Ω))` has trivial left and right kernels.  Torsion finiteness
(`finite_powKer`), roots of unity (`hasEnoughRootsOfUnity_exponent`) and the lifting of torsion points to
`T_ℓ(A)` (`exists_tate_lift_of_divisible` with `pt_pow_surjective`) are discharged; no finite-level
perfectness and no condition `ℓ ∤ #C`.
-/

noncomputable section

open CategoryTheory MonObj
open scoped CategoryTheory.MonObj

namespace WeilTate.Divisible

theorem point_tate_kernels {K : Type} [Field K] [CharZero K] (A : PkgI3.AbVar K) {Ω : Type} [Field Ω]
    [IsAlgClosed Ω] [Algebra K Ω] (ℓ : ℕ) [Fact ℓ.Prime] (P : LevelPairing ℓ (A.Pt Ω) (A.Pt Ω) Ω)
    (C : Subgroup (A.Pt Ω)) [Finite C]
    (hR : ∀ (k : ℕ) (y : A.Pt Ω), y ^ (ℓ ^ k) = 1 →
      (∀ x : A.Pt Ω, x ^ (ℓ ^ k) = 1 → P.e k x y = 1) → y ∈ C) :
    (∀ t : TΩ A Ω ℓ, (∀ s, P.tatePairing t s = 0) → t = 0) ∧
    (∀ s : TΩ A Ω ℓ, (∀ t, P.tatePairing t s = 0) → s = 0) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  have hp : ℓ.Prime := Fact.out
  have hℓK : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  refine P.tate_kernels_of_right_bounded
    (fun k => finite_powKer (Ω := Ω) A (ℓ ^ k) (pow_pos hp.pos k))
    (fun k => by
      haveI := finite_powKer (Ω := Ω) A (ℓ ^ k) (pow_pos hp.pos k)
      exact hasEnoughRootsOfUnity_exponent Ω _) C hR
    (fun k x hx => exists_tate_lift_of_divisible (pt_pow_surjective (Ω := Ω) A ℓ hℓK) k x hx)

end WeilTate.Divisible

#check @WeilTate.Divisible.point_tate_kernels
#print axioms WeilTate.Divisible.point_tate_kernels
