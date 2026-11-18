import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Comparison
import ZInQKernel.Contrib.OneProof.RC.Odd.Statements

/-!
# Lane RC23-visibility: the finite theta coefficients (O.4) and the comparison (O.7)

Manuscript (11/5), Appendix F: the sum (O.4) and its precision (Proposition `ex:app-theta-form`,
tex 8462–8622), the proof of the unaveraged comparison (O.7) and the precision of its orientation
count (Proposition `ex:app-theta-comparison`, tex 9101–9405), and the phase removal of §7
(tex 2081–2084, 2538). The output is lane RC12's `Odd.ThetaComparison` (the input `hO7` of
`Odd.visibility_of_comparison`).

**Genuine objects.** The quaternion algebra `B` is Mathlib's
`ℍ[ℚ,a,0,b] = QuaternionAlgebra ℚ a 0 b` (definite for `a, b < 0`; Elliot's `B`, ramified exactly
at `ℓ₀` and `∞`, tex 8462–8463, is one of these). `V(ℚ) = B⁰ = {x | x.re = 0}`, and
`Q_B(x) = Nrd(x) = x x̄` is `nrd` (tex 8497).

**The finite model of one stage** (`ThetaStage`, tex 8462–8621): the adelic data are replaced by
what (O.4) uses of them: the finite set `X` of supersingular pairs, the finite groups
`G z = R_z^× ⊂ B^×` with `|R_z^×| ∣ c₀`, the weights `f z x = f(z⁻¹xz)` with values in the
character ring `𝒪` (invariant under conjugation by `R_z^×`, finitely supported on each norm sphere
of `V(ℚ)`), the norm characters `χN z = χ_{h_*}(Nrd z)` and integer lifts `P z` of `P_M(z)`.
`thetaCoeff` is the sum (O.4).

PROVED here:
* `algebraMap_nrd_of_re_eq_zero`, `nrd_eq_mul_iff` — `Nrd(x) = −x²` on `B⁰`, and `Q_B(x) = mD` iff
  `x² = Dh_*` for `h_* = −m` (tex 8497, 9123–9124);
* `thetaCoeff_relift_dvd` — the precision of (O.4) (tex 8617–8621, 9372–9377, 9383–9386);
* `orbit_count_abstract`, `orbit_count` — the orbit count (tex 9297–9311, 9378–9390);
* `O7_of_inputs` — (O.7) from its named inputs (tex 9136–9370);
* `phase_removal`, `ComparisonInputs.comparison` — the phase removal (tex 2081–2084, 2538);
* `thetaComparison_of_inputs` — the family form, producing `Odd.ThetaComparison`;
* `ThetaExample.nonvacuous_O7`, `ThetaExample.thetaComparison` — a concrete instance in which every
  input holds and the conclusion pins down a nonzero coefficient.

The inputs that are not finite algebra are hypotheses, each with its tex lines and kind: the orbit
parametrization (ELLIOT, tex 9136–9170), the weights along the torsor (ELLIOT, tex 9171–9194,
9297–9305), the reduction identity at the reference tuple (PRINT Cornut–Jetchev, UNVERIFIED here,
+ ELLIOT, tex 9195–9296), the orientation changes (ELLIOT, tex 9329–9364), the stabilizers
`𝒪_F^× = {±1}` (ELLIOT/GLUE, tex 9308–9309) and, for the phase removal, that the phase is a unit
(ELLIOT, tex 9325–9327) and `2^M𝒪 ∩ ℤ = 2^Mℤ` (GLUE).

Convention: `u ∈ R_z^×` acts by conjugation `x ↦ u x u⁻¹` (a left action). As `R_z^×` is a group,
invariance under it is the same statement as Elliot's invariance under `x ↦ u⁻¹ x u` (tex 8573).
-/

open scoped Quaternion

namespace ZInQ.Manuscript.RC.Visibility

/-! ### The quaternion algebra: `V = B⁰` and `Q_B = Nrd` (tex 8497, 9123–9124) -/

section Quat

variable {a b : ℚ}

/-- **GLUE (definition), tex 8497.** The reduced norm `Nrd(x) = x x̄` of `B = ℍ[ℚ,a,0,b]`
(`x̄ = star x` the quaternion conjugate; `x x̄` is a scalar, `QuaternionAlgebra.mul_star_eq_coe`),
explicitly `x₁² − a x₂² − b x₃² + ab x₄²` (`nrd_apply`). Mathlib's `normSq` exists only for
Hamilton's quaternions `ℍ[ℚ] = ℍ[ℚ,-1,0,-1]`, where it agrees with `nrd` (`nrd_eq_normSq`). -/
def nrd (x : ℍ[ℚ,a,0,b]) : ℚ := (x * star x).re

/-- **PROVED.** `Nrd(x) = x x̄` in `B` (tex 8497). -/
theorem algebraMap_nrd (x : ℍ[ℚ,a,0,b]) : algebraMap ℚ ℍ[ℚ,a,0,b] (nrd x) = x * star x := by
  rw [QuaternionAlgebra.coe_algebraMap]
  exact (QuaternionAlgebra.mul_star_eq_coe x).symm

/-- **PROVED.** `Nrd(x) = x₁² − a x₂² − b x₃² + ab x₄²` (tex 8497). -/
theorem nrd_apply (x : ℍ[ℚ,a,0,b]) :
    nrd x = x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2 := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.re_star, QuaternionAlgebra.imI_star,
    QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star]
  ring

/-- **PROVED.** On Hamilton's quaternions `nrd` is Mathlib's `Quaternion.normSq` (tex 8497). -/
theorem nrd_eq_normSq (x : ℍ[ℚ]) : nrd x = Quaternion.normSq x :=
  (Quaternion.normSq_def x).symm

/-- **PROVED.** The reduced norm is multiplicative (used for conjugation, tex 8573, 9297–9300). -/
theorem nrd_mul (p q : ℍ[ℚ,a,0,b]) : nrd (p * q) = nrd p * nrd q := by
  apply QuaternionAlgebra.algebraMap_injective (R := ℚ) (c₁ := a) (c₂ := 0) (c₃ := b)
  rw [algebraMap_nrd, map_mul, algebraMap_nrd, algebraMap_nrd, star_mul]
  calc p * q * (star q * star p) = p * (q * star q) * star p := by simp only [mul_assoc]
    _ = p * algebraMap ℚ ℍ[ℚ,a,0,b] (nrd q) * star p := by rw [algebraMap_nrd]
    _ = p * star p * algebraMap ℚ ℍ[ℚ,a,0,b] (nrd q) := by
        rw [mul_assoc, Algebra.commutes, ← mul_assoc]
    _ = p * star p * (q * star q) := by rw [algebraMap_nrd]

/-- **PROVED.** `Nrd(1) = 1`. -/
theorem nrd_one : nrd (1 : ℍ[ℚ,a,0,b]) = 1 := by simp [nrd]

/-- **PROVED.** `Nrd(−x) = Nrd(x)` (the vectors `x`, `−x` of tex 9312–9316 have the same norm). -/
theorem nrd_neg (x : ℍ[ℚ,a,0,b]) : nrd (-x) = nrd x := by simp [nrd]

/-- **PROVED.** `re(xy) = re(yx)` in `ℍ[ℚ,a,0,b]` (the reduced trace is `2 re`). -/
theorem quat_re_mul_comm (p q : ℍ[ℚ,a,0,b]) : (p * q).re = (q * p).re := by
  simp only [QuaternionAlgebra.re_mul]; ring

/-- **PROVED.** Conjugation by a unit preserves `V = B⁰` (tex 8497, 8573). -/
theorem quat_re_conj (u : ℍ[ℚ,a,0,b]ˣ) (x : ℍ[ℚ,a,0,b]) :
    ((u : ℍ[ℚ,a,0,b]) * x * ((u⁻¹ : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b])).re = x.re := by
  rw [quat_re_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

/-- **PROVED.** Conjugation by a unit preserves `Q_B = Nrd` (tex 8497, 8573). -/
theorem nrd_conj (u : ℍ[ℚ,a,0,b]ˣ) (x : ℍ[ℚ,a,0,b]) :
    nrd ((u : ℍ[ℚ,a,0,b]) * x * ((u⁻¹ : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b])) = nrd x := by
  rw [nrd_mul, nrd_mul, mul_comm (nrd (u : ℍ[ℚ,a,0,b])), mul_assoc, ← nrd_mul, Units.mul_inv,
    nrd_one, mul_one]

/-- **PROVED (tex 8497).** On `V = B⁰`, `Q_B(x) = Nrd(x) = −x²`, as an identity in `B`. -/
theorem algebraMap_nrd_of_re_eq_zero {x : ℍ[ℚ,a,0,b]} (hx : x.re = 0) :
    algebraMap ℚ ℍ[ℚ,a,0,b] (nrd x) = -(x * x) := by
  rw [algebraMap_nrd, QuaternionAlgebra.star_eq_neg.mpr hx, mul_neg]

/-- **PROVED (tex 9123–9124).** For `x ∈ B⁰` and `h_* = −m`: `Q_B(x) = mD` iff `x² = Dh_*`. -/
theorem nrd_eq_mul_iff {x : ℍ[ℚ,a,0,b]} (hx : x.re = 0) (m D hstar : ℚ) (hm : hstar = -m) :
    nrd x = m * D ↔ x * x = algebraMap ℚ ℍ[ℚ,a,0,b] (D * hstar) := by
  constructor
  · intro h
    have h' := algebraMap_nrd_of_re_eq_zero hx
    rw [h] at h'
    rw [hm, show D * -m = -(m * D) by ring, map_neg, h', neg_neg]
  · intro h
    apply QuaternionAlgebra.algebraMap_injective (R := ℚ) (c₁ := a) (c₂ := 0) (c₃ := b)
    rw [algebraMap_nrd_of_re_eq_zero hx, h, hm, show D * -m = -(m * D) by ring, map_neg, neg_neg]

end Quat

/-! ### The finite model of one stage and the sum (O.4) (tex 8462–8621) -/

/-- **ELLIOT (definition: the data of one actual stage, as a finite model; tex 8462–8621).**
`O` is the character ring `𝒪`, the valuation ring at a place above two of the field generated by
the fixed root-character values (tex 8567–8570). The adelic objects enter through the finite data
that (O.4) uses; each field records its source and kind. -/
structure ThetaStage (O : Type*) [CommRing O] (a b : ℚ) where
  /-- The supersingular pairs `X = B^×\B̂^×/R̂^×` (tex 8465–8466). -/
  X : Type
  /-- GLUE: `X` is finite (the class set of an Eichler order). -/
  [fintypeX : Fintype X]
  /-- `R_z^× ⊂ B^×`, the automorphism group of the pair `z`, `R_z = B ∩ zR̂z⁻¹` (tex 8467–8468). -/
  G : X → Subgroup ℍ[ℚ,a,0,b]ˣ
  /-- `|R_z^×| ∣ c₀` (tex 8605–8611). Lane RC12 proves it (`Odd.card_dvd_c0_of_basis`) for every
  finite subgroup of the units of a ring with a rank-four `ℤ`-basis; that `R_z` is such a ring and
  `R_z^×` is finite is GLUE. It makes each `R_z^×` finite (`ThetaStage.finite_G`). -/
  card_G_dvd : ∀ z, Nat.card (G z) ∣ Odd.c0
  /-- The weights `f z x = f(z⁻¹xz)`, `f = ∏_p f_p` the finite Schwartz function, zero off its
  support, with values in `𝒪` (tex 8495–8576). -/
  f : X → ℍ[ℚ,a,0,b] → O
  /-- ELLIOT (tex 8571–8576, 9297–9300): `f(u⁻¹xu) = χ_{h_*}(Nrd u)⁻¹ f(x)` for `u ∈ R̂^×`, and a
  unit of the definite order `R_z` has `Nrd u = 1`; so `f z` is invariant under conjugation by
  `R_z^×` (written `x ↦ u x u⁻¹`, equivalently `x ↦ u⁻¹ x u` since `R_z^×` is a group). -/
  f_conj : ∀ z, ∀ u ∈ G z, ∀ x, f z (↑u * x * ↑u⁻¹) = f z x
  /-- The norm character `χN z = χ_{h_*}(Nrd z)` (tex 8601–8602), well defined on `X`
  (ELLIOT, tex 8612–8614). -/
  χN : X → O
  /-- Integer lifts of `P_M(z) = λ_M(Lπ_{ℓ₀}(z)) ∈ ℤ/2^M` ("arbitrary integral lifts", tex 8476,
  8493). -/
  P : X → ℤ
  /-- ELLIOT/GLUE (tex 8563–8564, 9092–9093): on each norm sphere of `V(ℚ)` the weight has finite
  support (the local supports are compact open and `Q_B` is positive definite). -/
  finite_supp : ∀ z (n : ℚ), {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n ∧ f z x ≠ 0}.Finite

attribute [instance] ThetaStage.fintypeX

variable {O : Type*} [CommRing O] {a b : ℚ}

/-- **ELLIOT (definition (O.4), tex 8598–8604).**
`H_M(n) = c₀ ∑_{z∈X} P_M(z) χ_{h_*}(Nrd z)/|R_z^×| · ∑_{x∈V(ℚ), Q_B(x)=n} f(z⁻¹xz)`, written with
the integer `c₀/|R_z^×|` (tex 8617) and the integer lifts `P z`. The inner sum is finite
(`finite_supp`); `n` ranges over `ℚ`, Elliot's indices being its nonnegative integers. -/
noncomputable def thetaCoeff (S : ThetaStage O a b) (n : ℚ) : O :=
  ∑ z, ((Odd.c0 / Nat.card (S.G z) : ℕ) : O) * (S.P z : O) * S.χN z *
    ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n}, S.f z x

namespace ThetaStage

/-- **PROVED (tex 8467–8468, 8611).** Each `R_z^×` is finite: its order divides `c₀ ≠ 0`. -/
theorem finite_G (S : ThetaStage O a b) (z : S.X) : Finite (S.G z) :=
  Nat.finite_of_card_ne_zero fun h => by
    have hd := S.card_G_dvd z
    rw [h] at hd
    exact absurd (Nat.eq_zero_of_zero_dvd hd) (by norm_num [Odd.c0])

/-- **Definition (tex 8493, 8619–8620).** The same stage with other integer lifts `P'` of `P_M`. -/
def relift (S : ThetaStage O a b) (P' : S.X → ℤ) : ThetaStage O a b := { S with P := P' }

/-- **Definition (tex 9123–9134).** The support set at the class `z` and norm `n`:
`{x ∈ V(ℚ) | Q_B(x) = n, f(z⁻¹xz) ≠ 0}`; for `n = mD` these are the optimal embeddings
`𝒪_F → R_z` with a nonzero weight (ELLIOT, tex 9123–9134). -/
def supp (S : ThetaStage O a b) (z : S.X) (n : ℚ) : Set ℍ[ℚ,a,0,b] :=
  {x | x.re = 0 ∧ nrd x = n ∧ S.f z x ≠ 0}

/-- **PROVED (instance; tex 9297–9311).** `R_z^×` acts on the support set by conjugation
`u • x = u x u⁻¹`: conjugation preserves `B⁰`, `Nrd` and, by `f_conj`, the weight. -/
instance conjAction (S : ThetaStage O a b) (z : S.X) (n : ℚ) :
    MulAction (S.G z) (S.supp z n) where
  smul u x := ⟨((u : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) * x *
      (((u : ℍ[ℚ,a,0,b]ˣ)⁻¹ : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]), by
    obtain ⟨hre, hn, hf⟩ := x.2
    refine ⟨by rw [quat_re_conj, hre], by rw [nrd_conj, hn], ?_⟩
    rw [S.f_conj z u u.2]
    exact hf⟩
  one_smul x := by
    apply Subtype.ext
    show ((1 : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) * x *
      (((1 : ℍ[ℚ,a,0,b]ˣ)⁻¹ : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) = x
    simp
  mul_smul u v x := by
    apply Subtype.ext
    show (((u * v : S.G z) : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) * x *
        ((((u * v : S.G z) : ℍ[ℚ,a,0,b]ˣ)⁻¹ : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) =
      ((u : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) * (((v : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) * x *
        (((v : ℍ[ℚ,a,0,b]ˣ)⁻¹ : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b])) *
        (((u : ℍ[ℚ,a,0,b]ˣ)⁻¹ : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b])
    simp only [Subgroup.coe_mul, mul_inv_rev, Units.val_mul]
    simp only [mul_assoc]

/-- **PROVED.** The action is `u • x = u x u⁻¹`. -/
theorem coe_smul (S : ThetaStage O a b) (z : S.X) (n : ℚ) (u : S.G z) (x : S.supp z n) :
    ((u • x : S.supp z n) : ℍ[ℚ,a,0,b]) =
      ((u : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) * x * (((u : ℍ[ℚ,a,0,b]ˣ)⁻¹ : ℍ[ℚ,a,0,b]ˣ) : ℍ[ℚ,a,0,b]) :=
  rfl

/-- **PROVED (instance; tex 8563–8564).** The support sets are finite (`finite_supp`). -/
instance finite_supp_coe (S : ThetaStage O a b) (z : S.X) (n : ℚ) : Finite (S.supp z n) :=
  (S.finite_supp z n).to_subtype

/-- **PROVED (tex 9297–9300).** The weight is constant on each conjugation orbit. -/
theorem f_eq_of_mem_orbit (S : ThetaStage O a b) (z : S.X) (n : ℚ) (x y : S.supp z n)
    (h : y ∈ MulAction.orbit (S.G z) x) : S.f z y = S.f z x := by
  obtain ⟨u, rfl⟩ := MulAction.mem_orbit_iff.mp h
  rw [coe_smul, S.f_conj z u u.2]

/-- **PROVED.** The inner sum of (O.4) is the sum over the (finite) support set. -/
theorem finsum_eq_supp (S : ThetaStage O a b) (z : S.X) (n : ℚ) :
    ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n}, S.f z x = ∑ᶠ x : S.supp z n, S.f z x := by
  have hset : {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n} ∩ Function.support (S.f z) =
      S.supp z n := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, supp, and_assoc]
  rw [← finsum_mem_inter_support, hset, finsum_set_coe_eq_finsum_mem]

variable {S : ThetaStage O a b} {n : ℚ} {ι : Type*}

/-- **Definition (tex 9150–9170).** For an orbit parametrization
`ι ≃ Σ z, (R_z^×-orbits of the support set at z)`, the class component `zc`. -/
def zc (param : ι ≃ Σ z : S.X, MulAction.orbitRel.Quotient (S.G z) (S.supp z n)) (p : ι) : S.X :=
  (param p).1

/-- **Definition (tex 9150–9174, 9297–9305).** A representative of the orbit `p` (the weight does
not depend on the choice, `f_eq_of_mem_orbit`). -/
noncomputable def rep (param : ι ≃ Σ z : S.X, MulAction.orbitRel.Quotient (S.G z) (S.supp z n))
    (p : ι) : ℍ[ℚ,a,0,b] :=
  ((param p).2.out : S.supp (param p).1 n)

end ThetaStage

open ThetaStage

/-! ### The precision of (O.4) (tex 8617–8621, 9372–9377, 9383–9386) -/

/-- **PROVED.** Unfolding (O.4) for the relifted stage. -/
theorem thetaCoeff_relift (S : ThetaStage O a b) (P' : S.X → ℤ) (n : ℚ) :
    thetaCoeff (S.relift P') n = ∑ z, ((Odd.c0 / Nat.card (S.G z) : ℕ) : O) * (P' z : O) *
      S.χN z * ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n}, S.f z x :=
  rfl

/-- **PROVED (tex 8619–8621, 9372–9377, 9383–9386).** Two stages with the same data except the
lifts, `P' z ≡ P z (mod 2^M)` for all `z`: their coefficients agree modulo `2^M𝒪`. "Changing any
lift of `P_M` by `2^M` changes every coefficient by an element of `2^M𝒪`. In particular there is
no loss of precision from an automorphism denominator" (`c₀/|R_z^×|` is an integer). -/
theorem thetaCoeff_relift_dvd (S : ThetaStage O a b) (M : ℕ) (P' : S.X → ℤ)
    (hP : ∀ z, (2 : ℤ) ^ M ∣ P' z - S.P z) (n : ℚ) :
    (2 : O) ^ M ∣ thetaCoeff (S.relift P') n - thetaCoeff S n := by
  rw [thetaCoeff_relift, thetaCoeff, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro z _
  obtain ⟨k, hk⟩ := hP z
  have hk' : (P' z : O) - (S.P z : O) = (2 : O) ^ M * (k : O) := by
    have h := congrArg (fun t : ℤ => (t : O)) hk
    push_cast at h
    exact h
  have e : ((Odd.c0 / Nat.card (S.G z) : ℕ) : O) * (P' z : O) * S.χN z *
        ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n}, S.f z x -
      ((Odd.c0 / Nat.card (S.G z) : ℕ) : O) * (S.P z : O) * S.χN z *
        ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n}, S.f z x =
      (2 : O) ^ M * (((Odd.c0 / Nat.card (S.G z) : ℕ) : O) * (k : O) * S.χN z *
        ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n}, S.f z x) := by
    linear_combination (((Odd.c0 / Nat.card (S.G z) : ℕ) : O) * S.χN z *
        ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n}, S.f z x) * hk'
  rw [e]
  exact dvd_mul_right _ _

/-! ### The orbit count (tex 9297–9311, 9378–9390) -/

/-- **PROVED (tex 9308–9311, 9378–9390), abstract form.** A group `G` with `|G| ∣ c₀` acting on a
finite set `E` with every stabilizer of order two, and an orbit-constant weight `w`: every orbit
has `|G|/2` elements (and `2 ∣ |G|` when `E` is nonempty), so
`(c₀/|G|) ∑_{x∈E} w(x) = ∑_{orbits ω} (c₀/2) w(ω)`. The step `(c₀/|G|)(|G|/2) = c₀/2` is lane
RC12's `Odd.orbit_weight_eq`: no congruence is divided by two. -/
theorem orbit_count_abstract {G E : Type*} [Group G] [MulAction G E] [Finite E]
    (w : E → O) (hw : ∀ (g : G) (x : E), w (g • x) = w x) (hG : Nat.card G ∣ Odd.c0)
    (hstab : ∀ x : E, Nat.card (MulAction.stabilizer G x) = 2) :
    ((Odd.c0 / Nat.card G : ℕ) : O) * ∑ᶠ x, w x =
      ∑ᶠ ω : MulAction.orbitRel.Quotient G E, ((Odd.c0 / 2 : ℕ) : O) * w ω.out := by
  classical
  have hc0 : Odd.c0 ≠ 0 := by norm_num [Odd.c0]
  have hGpos : Nat.card G ≠ 0 := fun h => hc0 (Nat.eq_zero_of_zero_dvd (h ▸ hG))
  have : Finite G := Nat.finite_of_card_ne_zero hGpos
  have := Fintype.ofFinite E
  have horb : ∀ x : E, Nat.card (MulAction.orbit G x) * 2 = Nat.card G := by
    intro x
    rw [← hstab x, mul_comm, ← Subgroup.card_mul_index (MulAction.stabilizer G x),
      MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rcases isEmpty_or_nonempty E with hE | ⟨⟨x₀⟩⟩
  · have : IsEmpty (MulAction.orbitRel.Quotient G E) := ⟨fun ω => hE.false ω.out⟩
    rw [finsum_of_isEmpty, mul_zero, finsum_of_isEmpty]
  · have h2 : 2 ∣ Nat.card G := ⟨Nat.card (MulAction.orbit G x₀), by rw [← horb x₀, mul_comm]⟩
    have := Fintype.ofFinite (MulAction.orbitRel.Quotient G E)
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Equiv.sum_comp (MulAction.selfEquivSigmaOrbits' G E).symm, Fintype.sum_sigma]
    have hinner : ∀ ω : MulAction.orbitRel.Quotient G E,
        ∑ y : ω.orbit, w ((MulAction.selfEquivSigmaOrbits' G E).symm ⟨ω, y⟩) =
          ((Nat.card G / 2 : ℕ) : O) * w ω.out := by
      intro ω
      have hcon : ∀ y : ω.orbit,
          w ((MulAction.selfEquivSigmaOrbits' G E).symm ⟨ω, y⟩) = w ω.out := by
        intro y
        have hy : (y : E) ∈ MulAction.orbit G ω.out := by
          rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
          exact y.2
        obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
        show w (y : E) = w ω.out
        rw [← hg, hw]
      rw [Finset.sum_congr rfl (fun y _ => hcon y), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul]
      congr 1
      have hc : Fintype.card ω.orbit = Nat.card (MulAction.orbit G ω.out) := by
        rw [← Nat.card_eq_fintype_card,
          MulAction.orbitRel.Quotient.orbit_eq_orbit_out ω Quotient.out_eq']
      rw [hc]
      have := horb ω.out
      congr 1
      omega
    rw [Finset.sum_congr rfl (fun ω _ => hinner ω), Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    rw [← mul_assoc, ← Nat.cast_mul, Odd.orbit_weight_eq _ h2 hG]

/-- **PROVED (tex 9297–9311, 9378–9390).** The orbit count at one class `z` and norm `n`. If every
element of the support set has stabilizer of order two under conjugation by `R_z^×` (hypothesis
`hstab`, ELLIOT/GLUE, tex 9308–9309: the stabilizer of an embedding is `𝒪_F^× = {±1}`), the
`z`-summand of (O.4) regroups into conjugation orbits, each worth
`(c₀/|R_z^×|)(|R_z^×|/2) = c₀/2` times its weight. -/
theorem orbit_count (S : ThetaStage O a b) (z : S.X) (n : ℚ)
    (hstab : ∀ x : S.supp z n, Nat.card (MulAction.stabilizer (S.G z) x) = 2) :
    ((Odd.c0 / Nat.card (S.G z) : ℕ) : O) *
        ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = n}, S.f z x =
      ∑ᶠ ω : MulAction.orbitRel.Quotient (S.G z) (S.supp z n),
        ((Odd.c0 / 2 : ℕ) : O) * S.f z ω.out := by
  rw [S.finsum_eq_supp z n]
  exact orbit_count_abstract (fun x : S.supp z n => S.f z x) (fun u x => S.f_conj z u u.2 x)
    (S.card_G_dvd z) hstab

/-! ### (O.7) from its inputs (tex 9101–9390) -/

/-- **PROVED: (O.7) from its inputs (tex 9101–9370, 9378–9390).** Fix the stage `S`, the precision
`M`, `m = |h_*|`, the parameter `D` and the norm `n = mD`. The inputs, each its own hypothesis:
* `param`, `hTup` (ELLIOT, tex 9136–9170) — the orbit parametrization: the pairs (class `z`,
  `R_z^×`-conjugation orbit of the support set at `z`) are in bijection with `Tup × Cl`, where `Tup`
  is the set of local orientation tuples, of size `2^{ω(N)+1}` (tex 9136–9148: two orientations at
  each `p^e ‖ N` and two at `ℓ₀`), and `Cl = Pic(𝒪_F)` is the class-group torsor
  `F^×\F̂^×/𝒪̂_F^×` of each tuple (tex 9150–9169); `zc` is the class component;
* `hweight` (ELLIOT, tex 9171–9194, 9297–9305) — along the torsor the Schwartz factor is constant
  (`a` centralizes `x₀`) and the norm factor is the genus character: on the orbit `(t, [a])`,
  `χ_{h_*}(Nrd z_a) f(z_a⁻¹ x z_a) = ζ₀(t) χ_F([a])`;
* `hred` (PRINT: C. Cornut and D. Jetchev, *Liftings of reduction maps for quaternion algebras*,
  2010 preprint, Theorem 3.1, Corollary 3.2, §3.6 and §§4.9–4.10, as cited at tex 9195–9296 —
  UNVERIFIED here, not read; lane RC12's `Odd.CornutJetchevThm31` records its locators — + ELLIOT,
  tex 9195–9296) — the reduction identity at the reference tuple `t₀`,
  `∑_{[a]} χ_F([a]) P_M(z_a) = λ_M(\overline{LP_D})` in `ℤ/2^M`, for integer lifts:
  `2^M ∣ ∑_c χF(c) P(zc(t₀,c)) − λ` with `λ` an integer lift of `λ_M(\overline{LP_D})`;
* `horient` (ELLIOT, tex 9329–9364; the sign algebra is lane RC12's `Odd.orientation_signs`) —
  every tuple contributes as the reference tuple does, modulo `2^M` only (the Atkin–Lehner and
  uniformizer relations of `P_M` hold in `ℤ/2^M`, hence only modulo `2^M` for integer lifts);
* `hstab` (ELLIOT/GLUE, tex 9308–9309) — every support element has stabilizer `𝒪_F^× = {±1}`,
  of order two.
Conclusion, (O.7) in `𝒪`: `H_M(mD) ≡ c₀ 2^{ω(N)} ζ₀(t₀) λ (mod 2^M𝒪)`. Each orbit is worth `c₀/2`
(`orbit_count`), the tuples are compared at precision `M` separately, and the `2^{ω(N)+1}` tuples
sum to `c₀ 2^{ω(N)}` (lane RC12's `Odd.O7_assembly`); no class number is divided out. -/
theorem O7_of_inputs (S : ThetaStage O a b) (M : ℕ) (m D : ℤ) (ω : ℕ)
    {Tup Cl : Type*} [Fintype Tup] [Fintype Cl] (hTup : Fintype.card Tup = 2 ^ (ω + 1))
    (param : Tup × Cl ≃
      Σ z : S.X, MulAction.orbitRel.Quotient (S.G z) (S.supp z ((m * D : ℤ) : ℚ)))
    (ζ₀ : Tup → O) (χF : Cl → O)
    (hweight : ∀ t c,
      S.χN (zc param (t, c)) * S.f (zc param (t, c)) (rep param (t, c)) = ζ₀ t * χF c)
    (t₀ : Tup) (lam : ℤ)
    (hred : (2 : O) ^ M ∣ ∑ c, χF c * (S.P (zc param (t₀, c)) : O) - (lam : O))
    (horient : ∀ t, (2 : O) ^ M ∣ ζ₀ t * ∑ c, χF c * (S.P (zc param (t, c)) : O) -
        ζ₀ t₀ * ∑ c, χF c * (S.P (zc param (t₀, c)) : O))
    (hstab : ∀ z (x : S.supp z ((m * D : ℤ) : ℚ)),
      Nat.card (MulAction.stabilizer (S.G z) x) = 2) :
    (2 : O) ^ M ∣ thetaCoeff S ((m * D : ℤ) : ℚ) - (Odd.c0 : O) * 2 ^ ω * ζ₀ t₀ * (lam : O) := by
  classical
  have : ∀ z, Fintype (MulAction.orbitRel.Quotient (S.G z) (S.supp z ((m * D : ℤ) : ℚ))) :=
    fun z => Fintype.ofFinite _
  -- regroup each class summand into orbits (the orbit count)
  have h1 : thetaCoeff S ((m * D : ℤ) : ℚ) =
      ∑ σ : (Σ z : S.X, MulAction.orbitRel.Quotient (S.G z) (S.supp z ((m * D : ℤ) : ℚ))),
        ((Odd.c0 / 2 : ℕ) : O) * (S.P σ.1 : O) * (S.χN σ.1 * S.f σ.1 σ.2.out) := by
    rw [thetaCoeff, Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    have h := orbit_count S z ((m * D : ℤ) : ℚ) (hstab z)
    calc ((Odd.c0 / Nat.card (S.G z) : ℕ) : O) * (S.P z : O) * S.χN z *
          ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = ((m * D : ℤ) : ℚ)}, S.f z x
        = (S.P z : O) * S.χN z * (((Odd.c0 / Nat.card (S.G z) : ℕ) : O) *
          ∑ᶠ x ∈ {x : ℍ[ℚ,a,0,b] | x.re = 0 ∧ nrd x = ((m * D : ℤ) : ℚ)}, S.f z x) := by ring
      _ = (S.P z : O) * S.χN z *
          ∑ q : MulAction.orbitRel.Quotient (S.G z) (S.supp z ((m * D : ℤ) : ℚ)),
            ((Odd.c0 / 2 : ℕ) : O) * S.f z q.out := by rw [h, finsum_eq_sum_of_fintype]
      _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun q _ => by ring)
  -- reindex by the parametrization `Tup × Cl ≃ Σ z, orbits at z`, and insert the weights
  have h2 : thetaCoeff S ((m * D : ℤ) : ℚ) =
      ∑ t, ((Odd.c0 / 2 : ℕ) : O) * (ζ₀ t * ∑ c, χF c * (S.P (zc param (t, c)) : O)) := by
    rw [h1, ← Equiv.sum_comp param, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hw := hweight t c
    simp only [zc, rep] at hw
    rw [hw]
    simp only [zc]
    ring
  -- the target, as a sum over the `2^{ω+1}` tuples (lane RC12's `O7_assembly`)
  have h3 : (Odd.c0 : O) * 2 ^ ω * ζ₀ t₀ * (lam : O) =
      ∑ _t : Tup, ((Odd.c0 / 2 : ℕ) : O) * ζ₀ t₀ * (lam : O) :=
    (Odd.O7_assembly ω hTup (fun _ => ((Odd.c0 / 2 : ℕ) : O) * ζ₀ t₀ * (lam : O)) (ζ₀ t₀)
      (lam : O) (fun _ => rfl)).symm
  -- each tuple is compared with the reduced point at precision `M`
  rw [h2, h3, ← Finset.sum_sub_distrib]
  apply Finset.dvd_sum
  intro t _
  have e : ((Odd.c0 / 2 : ℕ) : O) * (ζ₀ t * ∑ c, χF c * (S.P (zc param (t, c)) : O)) -
        ((Odd.c0 / 2 : ℕ) : O) * ζ₀ t₀ * (lam : O) =
      ((Odd.c0 / 2 : ℕ) : O) * ((ζ₀ t * ∑ c, χF c * (S.P (zc param (t, c)) : O) -
        ζ₀ t₀ * ∑ c, χF c * (S.P (zc param (t₀, c)) : O)) +
        ζ₀ t₀ * (∑ c, χF c * (S.P (zc param (t₀, c)) : O) - (lam : O))) := by ring
  rw [e]
  exact Dvd.dvd.mul_left (dvd_add (horient t) (Dvd.dvd.mul_left hred _)) _

/-! ### Phase removal (tex 2081–2084, 2538) -/

/-- **PROVED: phase removal (tex 2081–2084, 2538).** If `H ≡ c₀ 2^{ω(N)} ζ λ (mod 2^M𝒪)` ((O.7)),
the phase `ζ` is a unit of `𝒪` (ELLIOT, tex 9325–9327: a `2`-power root of unity), the integer `aθ`
represents the phase-removed coefficient `ζ⁻¹H` at precision `M` (`ζ aθ ≡ H`; tex 2081–2082: "use
its integer representative at that precision"), and `2^M𝒪 ∩ ℤ = 2^Mℤ` (`hO`, GLUE: true for `ℤ`,
`ℤ₂` and the valuation ring at a place above two of a number field), then
`aθ ≡ c₀ 2^{ω(N)} · 1 · λ (mod 2^M)` in `ℤ`: "after phase removal, the coefficients used for
valuation are integers" (tex 2538). -/
theorem phase_removal {M ω : ℕ} {H ζ : O} {aθ lam : ℤ} (hζ : IsUnit ζ)
    (hO7 : (2 : O) ^ M ∣ H - (Odd.c0 : O) * 2 ^ ω * ζ * (lam : O))
    (haθ : (2 : O) ^ M ∣ ζ * (aθ : O) - H)
    (hO : ∀ z : ℤ, (2 : O) ^ M ∣ (z : O) → (2 : ℤ) ^ M ∣ z) :
    (2 : ℤ) ^ M ∣ aθ - (Odd.c0 : ℤ) * 2 ^ ω * 1 * lam := by
  apply hO
  have h1 : (2 : O) ^ M ∣ ζ * ((aθ : O) - (Odd.c0 : O) * 2 ^ ω * (lam : O)) := by
    have h := dvd_add haθ hO7
    have e : ζ * (aθ : O) - H + (H - (Odd.c0 : O) * 2 ^ ω * ζ * (lam : O)) =
        ζ * ((aθ : O) - (Odd.c0 : O) * 2 ^ ω * (lam : O)) := by ring
    rwa [e] at h
  obtain ⟨u, rfl⟩ := hζ
  have h2 := Dvd.dvd.mul_left h1 ((u⁻¹ : Oˣ) : O)
  rw [← mul_assoc, Units.inv_mul, one_mul] at h2
  have e : (((aθ - (Odd.c0 : ℤ) * 2 ^ ω * 1 * lam : ℤ)) : O) =
      (aθ : O) - (Odd.c0 : O) * 2 ^ ω * (lam : O) := by push_cast; ring
  rw [e]
  exact h2

/-! ### The family form: lane RC12's `ThetaComparison` -/

/-- **Definition: the inputs of (O.7) and of its phase removal at one admissible `(θ, D)`**
(tex 9101–9405, 2081–2084, 2538). The fields are the hypotheses of `O7_of_inputs` and of
`phase_removal`, with the same sources and kinds. -/
structure ComparisonInputs (S : ThetaStage O a b) (M : ℕ) (m D : ℤ) (ω : ℕ) (lam aθ : ℤ) where
  /-- The local orientation tuples (tex 9136–9148). -/
  Tup : Type
  /-- The class group `Pic(𝒪_F)`, `F = ℚ(√(Dh_*))` (tex 9161–9166). -/
  Cl : Type
  /-- ELLIOT (tex 9136–9148): the tuples form a finite set. -/
  [fintypeTup : Fintype Tup]
  /-- `Pic(𝒪_F)` is finite (GLUE). -/
  [fintypeCl : Fintype Cl]
  /-- ELLIOT (tex 9148): there are `2^{ω(N)+1}` local orientation tuples. -/
  card_Tup : Fintype.card Tup = 2 ^ (ω + 1)
  /-- ELLIOT (tex 9136–9170): the orbit parametrization (`O7_of_inputs`, `param`). -/
  param : Tup × Cl ≃
    Σ z : S.X, MulAction.orbitRel.Quotient (S.G z) (S.supp z ((m * D : ℤ) : ℚ))
  /-- The phase `χ_{h_*}(Nrd z₀) f(z₀⁻¹x₀z₀)` of each tuple (tex 9303–9305, 9321–9322). -/
  ζ₀ : Tup → O
  /-- The genus character `χ_F([a]) = χ_{h_*}(N_{F/ℚ} a)` (tex 9178–9193, 9276). -/
  χF : Cl → O
  /-- ELLIOT (tex 9171–9194, 9297–9305): the weights along the torsor (`O7_of_inputs`,
  `hweight`). -/
  weight : ∀ t c,
    S.χN (zc param (t, c)) * S.f (zc param (t, c)) (rep param (t, c)) = ζ₀ t * χF c
  /-- The reference tuple, realized by the image of the reference Heegner point `x_D`
  (tex 9272–9274). -/
  t₀ : Tup
  /-- PRINT (Cornut–Jetchev Theorem 3.1, Corollary 3.2, §§4.9–4.10; UNVERIFIED here) + ELLIOT
  (tex 9195–9296): the reduction identity at the reference tuple (`O7_of_inputs`, `hred`). -/
  reduction : (2 : O) ^ M ∣ ∑ c, χF c * (S.P (zc param (t₀, c)) : O) - (lam : O)
  /-- ELLIOT (tex 9329–9364): the orientation changes (`O7_of_inputs`, `horient`). -/
  orientation : ∀ t, (2 : O) ^ M ∣ ζ₀ t * ∑ c, χF c * (S.P (zc param (t, c)) : O) -
    ζ₀ t₀ * ∑ c, χF c * (S.P (zc param (t₀, c)) : O)
  /-- ELLIOT/GLUE (tex 9308–9309): stabilizers `𝒪_F^× = {±1}` (`O7_of_inputs`, `hstab`). -/
  stab : ∀ z (x : S.supp z ((m * D : ℤ) : ℚ)), Nat.card (MulAction.stabilizer (S.G z) x) = 2
  /-- ELLIOT (tex 9325–9327): the phase of the reference tuple is a unit (a `2`-power root of
  unity). -/
  phase_unit : IsUnit (ζ₀ t₀)
  /-- Definition (tex 2081–2082): `aθ` is an integer representative of the phase-removed
  coefficient at precision `M`. -/
  representative : (2 : O) ^ M ∣ ζ₀ t₀ * (aθ : O) - thetaCoeff S ((m * D : ℤ) : ℚ)
  /-- GLUE: `2^M𝒪 ∩ ℤ = 2^Mℤ` (true for `ℤ`, `ℤ₂` and the valuation ring at a place above two). -/
  ring_two : ∀ z : ℤ, (2 : O) ^ M ∣ (z : O) → (2 : ℤ) ^ M ∣ z

attribute [instance] ComparisonInputs.fintypeTup ComparisonInputs.fintypeCl

/-- **PROVED (tex 9101–9390, 2081–2084).** From the inputs at one admissible `(θ, D)`: (O.7)
(`O7_of_inputs`) and the phase removal (`phase_removal`) give the clause of `Odd.ThetaComparison`
at `(θ, D)` with `ζ = 1`. -/
theorem ComparisonInputs.comparison {S : ThetaStage O a b} {M : ℕ} {m D : ℤ} {ω : ℕ}
    {lam aθ : ℤ} (I : ComparisonInputs S M m D ω lam aθ) :
    (2 : ℤ) ^ M ∣ aθ - (Odd.c0 : ℤ) * 2 ^ ω * 1 * lam :=
  phase_removal I.phase_unit
    (O7_of_inputs S M m D ω I.card_Tup I.param I.ζ₀ I.χF I.weight I.t₀ lam I.reduction
      I.orientation I.stab)
    I.representative I.ring_two

/-- **PROVED: the family form (tex 9101–9405, 2081–2084, 2522–2538).** For every stage `θ` a finite
model `S θ` of its data (over `ℍ[ℚ, a θ, 0, b θ]`: the algebra changes with `ℓ₀`) with the fixed
character ring `𝒪` (tex 8567–8570, 9326–9327), the fixed `m = |h_*|` and `ω = ω(N)`, and for every
admissible `(θ, D)` the inputs of (O.7) and of its phase removal at precision `M_θ`, with
`λ = lam θ D` and the integer representative `aθ θ D`: lane RC12's `Odd.ThetaComparison` holds
(with `ζ = 1`). -/
theorem thetaComparison_of_inputs {aq bq : ℕ → ℚ} (S : ∀ θ, ThetaStage O (aq θ) (bq θ))
    (Mθ : ℕ → ℕ) (aθ lam : ℕ → ℤ → ℤ) (admissible : ℕ → ℤ → Prop) (ω : ℕ) (m : ℤ)
    (H : ∀ θ D, admissible θ D → ComparisonInputs (S θ) (Mθ θ) m D ω (lam θ D) (aθ θ D)) :
    Odd.ThetaComparison Mθ aθ lam admissible ω :=
  fun θ D hD => ⟨1, odd_one, (H θ D hD).comparison⟩

/-! ### Non-vacuity: a concrete instance -/

namespace ThetaExample

/-- **Definition (non-vacuity instance).** `x₀ = 2i + j` in `ℍ[ℚ,-1,0,-3]`, the algebra `(−1,−3)`.
(GLUE remark, not used: `(−1,−3)` is ramified exactly at `3` and `∞`, as Elliot's `B` for
`ℓ₀ = 3`; `h_* = −7` has `(h_*/3) = −1`; `F = ℚ(√−7)` has class number one, as `Cl = Unit`.) -/
def x0 : ℍ[ℚ,-1,0,-3] := ⟨0, 2, 1, 0⟩

/-- **PROVED.** `Q_B(x₀) = 7 = mD` for `m = 7`, `D = 1`. -/
theorem nrd_x0 : nrd x0 = 7 := by
  simp only [nrd, x0, QuaternionAlgebra.re_mul, QuaternionAlgebra.star_mk]
  norm_num

/-- **PROVED (tex 9123–9124).** `x₀² = Dh_*` with `D = 1`, `h_* = −7`. -/
theorem x0_sq : x0 * x0 = algebraMap ℚ ℍ[ℚ,-1,0,-3] (1 * (-7)) :=
  (nrd_eq_mul_iff (x := x0) rfl 7 1 (-7) rfl).mp (by rw [nrd_x0]; norm_num)

/-- **PROVED.** `x₀ ≠ −x₀`. -/
theorem x0_ne_neg : x0 ≠ -x0 := by
  intro h
  have := congrArg QuaternionAlgebra.imI h
  simp [x0] at this
  norm_num at this

/-- **Definition (non-vacuity instance).** The subgroup `{±1}` of `ℍ[ℚ,-1,0,-3]ˣ`. -/
def pmOne : Subgroup ℍ[ℚ,-1,0,-3]ˣ where
  carrier := {1, -1}
  mul_mem' := by
    rintro x y (rfl | rfl) (rfl | rfl) <;> simp
  one_mem' := by simp
  inv_mem' := by
    rintro x (rfl | rfl) <;> simp

/-- **PROVED.** Conjugation by `±1` is trivial. -/
theorem pmOne_conj {u : ℍ[ℚ,-1,0,-3]ˣ} (hu : u ∈ pmOne) (x : ℍ[ℚ,-1,0,-3]) :
    (u : ℍ[ℚ,-1,0,-3]) * x * ((u⁻¹ : ℍ[ℚ,-1,0,-3]ˣ) : ℍ[ℚ,-1,0,-3]) = x := by
  rcases hu with rfl | rfl <;> simp

/-- **PROVED.** `|{±1}| = 2`. -/
theorem card_pmOne : Nat.card pmOne = 2 := by
  have h : (1 : ℍ[ℚ,-1,0,-3]ˣ) ≠ -1 := by
    intro h
    have := congrArg (fun u : ℍ[ℚ,-1,0,-3]ˣ => (u : ℍ[ℚ,-1,0,-3]).re) h
    norm_num at this
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
  exact Set.ncard_pair h

/-- **Definition (non-vacuity instance).** One class, `G = {±1}`, the weight the indicator of
`{x₀, −x₀}`, `χN = 1`, `P = 1`, over `𝒪 = ℤ`. -/
noncomputable def stage : ThetaStage ℤ (-1) (-3) where
  X := Unit
  G := fun _ => pmOne
  card_G_dvd := fun _ => by rw [card_pmOne]; norm_num [Odd.c0]
  f := fun _ => Set.indicator {x0, -x0} 1
  f_conj := fun _ u hu x => by rw [pmOne_conj hu x]
  χN := fun _ => 1
  P := fun _ => 1
  finite_supp := fun _ n => by
    apply (Set.toFinite ({x0, -x0} : Set ℍ[ℚ,-1,0,-3])).subset
    intro x hx
    by_contra h
    exact hx.2.2 (Set.indicator_of_notMem h _)

/-- **PROVED.** In the example the conjugation action is trivial. -/
theorem stage_smul (z : stage.X) (n : ℚ) (u : stage.G z) (x : stage.supp z n) : u • x = x := by
  apply Subtype.ext
  rw [ThetaStage.coe_smul]
  exact pmOne_conj u.2 x

/-- **PROVED.** In the example every stabilizer is `{±1}`, of order two (`hstab`). -/
theorem stage_stab (z : stage.X) (n : ℚ) (x : stage.supp z n) :
    Nat.card (MulAction.stabilizer (stage.G z) x) = 2 := by
  have h : MulAction.stabilizer (stage.G z) x = ⊤ := by
    ext u
    simp only [MulAction.mem_stabilizer_iff, stage_smul, Subgroup.mem_top]
  rw [h, Subgroup.card_top]
  exact card_pmOne

/-- **PROVED.** In the example the weight is `1` on the support. -/
theorem stage_f_supp {z : stage.X} {n : ℚ} (y : stage.supp z n) : stage.f z y = 1 := by
  have hy := y.2.2.2
  change Set.indicator {x0, -x0} 1 (y : ℍ[ℚ,-1,0,-3]) ≠ (0 : ℤ) at hy
  change Set.indicator {x0, -x0} 1 (y : ℍ[ℚ,-1,0,-3]) = (1 : ℤ)
  by_cases h : (y : ℍ[ℚ,-1,0,-3]) ∈ ({x0, -x0} : Set ℍ[ℚ,-1,0,-3])
  · rw [Set.indicator_of_mem h]; rfl
  · exact absurd (Set.indicator_of_notMem h _) hy

/-- **PROVED.** In the example the support consists of `x₀` and `−x₀` at most. -/
theorem stage_supp_mem {z : stage.X} {n : ℚ} (y : stage.supp z n) :
    (y : ℍ[ℚ,-1,0,-3]) = x0 ∨ (y : ℍ[ℚ,-1,0,-3]) = -x0 := by
  have hy := y.2.2.2
  change Set.indicator {x0, -x0} 1 (y : ℍ[ℚ,-1,0,-3]) ≠ (0 : ℤ) at hy
  by_contra h
  push Not at h
  apply hy
  apply Set.indicator_of_notMem
  rintro (h1 | h1)
  · exact h.1 h1
  · exact h.2 h1

/-- **PROVED.** `x₀` lies in the support at norm `mD = 7 · 1`. -/
theorem x0_mem (z : stage.X) : x0 ∈ stage.supp z ((7 * 1 : ℤ) : ℚ) := by
  refine ⟨rfl, by rw [nrd_x0]; norm_num, ?_⟩
  change Set.indicator {x0, -x0} 1 x0 ≠ (0 : ℤ)
  rw [Set.indicator_of_mem (by simp)]
  norm_num

/-- **PROVED.** `−x₀` lies in the support at norm `mD = 7 · 1`. -/
theorem neg_x0_mem (z : stage.X) : -x0 ∈ stage.supp z ((7 * 1 : ℤ) : ℚ) := by
  refine ⟨by simp [x0], by rw [nrd_neg, nrd_x0]; norm_num, ?_⟩
  change Set.indicator {x0, -x0} 1 (-x0) ≠ (0 : ℤ)
  rw [Set.indicator_of_mem (by simp)]
  norm_num

/-- **Definition (non-vacuity instance).** The unique class. -/
def z0 : stage.X := ()

/-- **Definition (non-vacuity instance).** The two orientations: `x₀` and `−x₀` (tex 9312–9316). -/
noncomputable def pt (t : Fin 2) : stage.supp z0 ((7 * 1 : ℤ) : ℚ) :=
  if t = 0 then ⟨x0, x0_mem z0⟩ else ⟨-x0, neg_x0_mem z0⟩

/-- **PROVED.** The two orientations are distinct. -/
theorem pt_injective : Function.Injective pt := by
  intro s t h
  have h' := congrArg Subtype.val h
  fin_cases s <;> fin_cases t
  · rfl
  · exact absurd h' (by simpa [pt] using x0_ne_neg)
  · exact absurd h'.symm (by simpa [pt] using x0_ne_neg)
  · rfl

/-- **Definition (non-vacuity instance; PROVED bijective).** The orbit parametrization
`Fin 2 × Unit ≃ Σ z, orbits`: `Tup = Fin 2` (`ω = 0`), `Cl = Unit`. -/
noncomputable def param : Fin 2 × Unit ≃
    Σ z : stage.X, MulAction.orbitRel.Quotient (stage.G z) (stage.supp z ((7 * 1 : ℤ) : ℚ)) :=
  Equiv.ofBijective (fun p => ⟨z0, Quotient.mk'' (pt p.1)⟩) (by
    constructor
    · rintro ⟨s, ⟨⟩⟩ ⟨t, ⟨⟩⟩ h
      have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have h3 := Quotient.exact h2
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp h3
      rw [stage_smul] at hg
      have hts : t = s := pt_injective hg
      rw [hts]
    · rintro ⟨z, q⟩
      cases z
      induction q using Quotient.inductionOn with
      | h y =>
        rcases stage_supp_mem y with hy | hy
        · refine ⟨(0, ()), ?_⟩
          have : pt 0 = y := Subtype.ext (by simp [pt, hy])
          simp only [this]
          rfl
        · refine ⟨(1, ()), ?_⟩
          have : pt 1 = y := Subtype.ext (by simp [pt, hy])
          simp only [this]
          rfl)

/-- **PROVED.** (O.7) for the example at every precision `M`, from `O7_of_inputs` with all its
inputs verified: `m = 7`, `D = 1`, `ω = 0`, `ζ₀ = χF = 1`, `t₀ = 0`, `λ = 1`. -/
theorem stage_O7 (M : ℕ) :
    (2 : ℤ) ^ M ∣ thetaCoeff stage ((7 * 1 : ℤ) : ℚ) - (Odd.c0 : ℤ) * 2 ^ 0 * 1 * 1 := by
  have h := O7_of_inputs stage M 7 1 0 (Tup := Fin 2) (Cl := Unit) (by simp) param
    (fun _ => (1 : ℤ)) (fun _ => (1 : ℤ))
    (fun t c => by
      have hf := stage_f_supp ((param (t, c)).2.out)
      simp only [zc, rep]
      rw [hf]
      rfl)
    0 1 (by simp [stage]) (fun t => by simp [stage]) (fun z x => stage_stab z _ x)
  simpa using h

/-- **PROVED.** An integer divisible by every power of two is zero. -/
theorem eq_of_forall_two_pow_dvd {x y : ℤ} (h : ∀ M : ℕ, (2 : ℤ) ^ M ∣ x - y) : x = y := by
  have h0 : x - y = 0 := by
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h (x - y).natAbs)
    rw [Int.natAbs_pow]
    exact Nat.lt_two_pow_self
  linarith

/-- **PROVED.** In the example, (O.7) at all precisions pins the coefficient down: `H(7) = c₀`. -/
theorem stage_thetaCoeff : thetaCoeff stage ((7 * 1 : ℤ) : ℚ) = Odd.c0 :=
  eq_of_forall_two_pow_dvd fun M => by simpa using stage_O7 M

/-- **PROVED (non-vacuity of `O7_of_inputs`).** Every input of `O7_of_inputs` holds for the example
(`stage_O7`), and its conclusion is not vacuous: it holds at every precision, it determines the
coefficient, `H(7) = c₀ ≠ 0`, and that coefficient is visible at precision `10` (`v₂ = 9`). -/
theorem nonvacuous_O7 :
    (∀ M : ℕ, (2 : ℤ) ^ M ∣ thetaCoeff stage ((7 * 1 : ℤ) : ℚ) - (Odd.c0 : ℤ) * 2 ^ 0 * 1 * 1) ∧
      thetaCoeff stage ((7 * 1 : ℤ) : ℚ) = Odd.c0 ∧
      ¬ (2 : ℤ) ^ 10 ∣ thetaCoeff stage ((7 * 1 : ℤ) : ℚ) := by
  refine ⟨stage_O7, stage_thetaCoeff, ?_⟩
  rw [stage_thetaCoeff]
  norm_num [Odd.c0]

/-- **Definition (non-vacuity instance).** The inputs of `ComparisonInputs` for the example, at
every precision `M`, with `aθ = c₀`. -/
noncomputable def inputs (M : ℕ) : ComparisonInputs stage M 7 1 0 1 Odd.c0 where
  Tup := Fin 2
  Cl := Unit
  card_Tup := by simp
  param := param
  ζ₀ := fun _ => 1
  χF := fun _ => 1
  weight := fun t c => by
    have hf := stage_f_supp ((param (t, c)).2.out)
    simp only [zc, rep]
    rw [hf]
    rfl
  t₀ := 0
  reduction := by simp [stage]
  orientation := fun t => by simp [stage]
  stab := fun z x => stage_stab z _ x
  phase_unit := isUnit_one
  representative := by rw [stage_thetaCoeff]; simp
  ring_two := fun z h => by simpa using h

/-- **PROVED (non-vacuity of `thetaComparison_of_inputs`).** The family form applies to the
constant family of the example (`M_θ = θ`, admissible `D = 1`, `λ = 1`, `aθ = c₀`). -/
theorem thetaComparison :
    Odd.ThetaComparison (fun θ => θ) (fun _ _ => (Odd.c0 : ℤ)) (fun _ _ => 1)
      (fun _ D => D = 1) 0 :=
  thetaComparison_of_inputs (aq := fun _ => -1) (bq := fun _ => -3) (fun _ => stage)
    (fun θ => θ) (fun _ _ => (Odd.c0 : ℤ)) (fun _ _ => 1) (fun _ D => D = 1) 0 7
    (fun θ D hD => by subst hD; exact inputs θ)

end ThetaExample

end ZInQ.Manuscript.RC.Visibility
