import Mathlib
import ZInQKernel.Contrib.OneProof.RC.AppF.Brandt
import ZInQKernel.Contrib.OneProof.RC.AppF.Prints
import ZInQKernel.Contrib.OneProof.RC.Odd.Statements
import ZInQKernel.Contrib.OneProof.RC.Odd.ThetaLocal
import ZInQKernel.Contrib.OneProof.RC.Odd.Constants

/-!
# App F: the weighted ternary theta sum (O.4) at one actual stage, and its coefficient source

Manuscript (11/5), Appendix F, Proposition `ex:app-theta-form` and its proof (tex 8408–9100).

`ThetaStage R` records the objects of (O.1)–(O.4) at one actual stage, over the coefficient ring
`R` (Elliot's `𝒪/2^M𝒪`):

* the definite algebra `B = (qa, qb)_ℚ` ramified exactly at `ℓ₀, ∞` (`ram`; existence is the PRINT
  `VoightMainThm1461`, tex 8462);
* the class set `X = B^×\B̂^×/R̂^×` of an Eichler order of level `N` (the supersingular pairs,
  tex 8463–8474), as a finite type, with `w z = |R_z^×|` dividing `c₀ = |GL₄(𝔽₃)|`
  (tex 8605–8611; PROVED in the tree as `Odd.card_dvd_c0_of_basis` for `R_z^× ⊂ GL₄(ℤ)`);
* `P z`, an integral lift of `P_M(z) = λ_M(Lπ_{ℓ₀}(z))` (tex 8476–8494), and `χN z = χ_{h_*}(Nrd z)`;
* `θ z k = ∑_{x ∈ V(ℚ), Q_B(x) = k} f(z⁻¹xz)`, the inner sum of (O.4), with the local weights (O.3)
  folded into `f`; at each good prime `p` its finite `p`-frame (`PFrame`, `Brandt.lean`) and the
  `p + 1` neighbours `nb p z L`;
* the characters `s(p) = η_B(p)` (a unit), `χ_{h_*}(p) = (−m/p)`, `η = η_B χ_{h_*}`.

The theta sum (O.4) is the finite sum `H(k) = ∑_z (c₀/w_z) P(z) χ_{h_*}(Nrd z) θ_z(k)` with the integer
`c₀/w_z` (so it is defined in `R` without division: "there is no loss of precision from an
automorphism denominator", tex 8619–8621), and the phase-removed stage coefficients are
`aθ(n) = H(mn)`.

PROVED here (from the fields, the local counts of `Lines.lean` and the transfer of `Brandt.lean`):
* `ThetaStage.brandt` (tex 9059–9082): `H(p²n) + s(−n/p)H(n) + ps²H(n/p²) = sχ_{h_*}(p)a_pH(n)`;
* `ThetaStage.recAt` ((O.6), tex 9083–9093): `RecAt p (η p) (−1/p) a_p aθ` at every good prime;
* `ThetaStage.aθ_zero` (tex 9092): `aθ 0 = 0`;
* `ThetaStage.sourceHyp`: `Odd.SourceHyp T δ η Good a_p aθ`, given `a_q ≡ q + 1 (mod 4)` (PROVED for
  the actual curve as `GlueSweep.Odd.ap_mod_four_curve`) and the depth inequality of App G
  (the field `SourceHyp.depth`, taken as a hypothesis, tex 10151–10256);
* `ThetaStage.oddStageSource`: the tree's `Odd.OddStageSource M δ η Good a_p aθ` for
  `R = ZMod (2^M)`.

What the fields encode, and what is missing, is in `docs/research/rc-appF-theta.md`. In short: the
fields are the definitions of the adelic construction plus three standard facts used by Elliot
without a print (the `T_p`-eigenrelation of `P_M`, tex 8476–8494; self-adjointness
`N_ij w_j = N_ji w_i`, tex 9069–9071; and the identification of a neighbour's theta coefficients
with the `y/p`-sum together with its norm-character change, tex 9045–9076). The existence of a
`ThetaStage` from `(E, ℓ₀, M, L, λ_M)` — quaternion orders, the adelic class set, the local
identifications — is the missing theory (not in Mathlib).
-/

namespace ZInQ.Manuscript.RC.AppF

open Finset ZInQ.Manuscript.RC.Odd

/-- The objects of (O.1)–(O.4) at one actual stage (see the module docstring). -/
structure ThetaStage (R : Type*) [CommRing R] where
  /-- the detecting prime -/
  ℓ₀ : ℕ
  /-- `B = (qa, qb)_ℚ` -/
  qa : ℚ
  qb : ℚ
  /-- `B` is ramified exactly at `ℓ₀` and `∞` (tex 8462) -/
  ram : RamifiedExactlyAtEll0Infty ℓ₀ qa qb
  /-- the class set of the Eichler order (supersingular pairs) -/
  X : Type
  [fin : Fintype X]
  /-- `w z = |R_z^×|` -/
  w : X → ℕ
  w_pos : ∀ z, 0 < w z
  /-- `|R_z^×| ∣ c₀` (tex 8605–8611) -/
  w_dvd : ∀ z, w z ∣ c0
  /-- an integral lift of `P_M(z)` -/
  P : X → R
  /-- `χ_{h_*}(Nrd z)` -/
  χN : X → R
  /-- `θ z k = ∑_{Q_B(x) = k} f(z⁻¹xz)` -/
  θ : X → ℕ → R
  /-- `m = |h_*|` -/
  m : ℕ
  /-- the good primes (outside the full support) -/
  Good : ℕ → Prop
  good_prime : ∀ p, Good p → p.Prime
  good_ne_two : ∀ p, Good p → p ≠ 2
  good_m : ∀ p, Good p → ¬ p ∣ m
  /-- `a_p(E)` -/
  ap : ℕ → ℤ
  /-- `s(p) = η_B(p)` and its inverse -/
  s : ℕ → R
  sinv : ℕ → R
  s_unit : ∀ p, Good p → s p * sinv p = 1
  /-- `η = η_B χ_{h_*}` -/
  η : ℕ → R
  η_mul : ∀ x y, η (x * y) = η x * η y
  η_one : η 1 = 1
  η_good : ∀ p, Good p → η p = s p * (jacobiSym (-(m : ℤ)) p : R)
  /-- the neighbour of `z` at the line `L` (tex 9039) -/
  nb : (p : ℕ) → X → Option (ZMod p) → X
  /-- `P_M` is a `T_p`-eigenfunction with eigenvalue `a_p` modulo `2^M` (tex 8476–8494) -/
  hecke : ∀ p (hp : Good p), haveI : NeZero p := ⟨(good_prime p hp).ne_zero⟩
    ∀ z, ∑ L, P (nb p z L) = (ap p : R) * P z
  /-- self-adjointness `N_ij w_j = N_ji w_i` (tex 9069–9071) -/
  adjoint : ∀ p (hp : Good p), haveI : NeZero p := ⟨(good_prime p hp).ne_zero⟩
    ∀ i j, nbrCount (nb p) i j * w j = nbrCount (nb p) j i * w i
  /-- the `p`-frame of each class -/
  frame : ∀ p, Good p → X → PFrame p R
  frame_theta : ∀ p (hp : Good p) z k, θ z k = (frame p hp z).theta k
  /-- "scaling by `p` at all other places multiplies the weight by `s`" (tex 9059) -/
  frame_scale : ∀ p (hp : Good p) z x,
    (frame p hp z).F ((frame p hp z).scale x) = s p * (frame p hp z).F x
  /-- the neighbour's theta coefficients are the `y/p`-sum with weight `s⁻¹F(y)`, and a neighbour
  changes the norm character by `χ_{h_*}(p)` (tex 9045–9076) -/
  frame_nbr : ∀ p (hp : Good p) z L n,
    χN (nb p z L) * θ (nb p z L) n =
      (jacobiSym (-(m : ℤ)) p : R) * χN z * (sinv p * (frame p hp z).nbrSum L n)
  /-- the coefficient at `0` vanishes by the local support at `p ∣ m` (tex 9092) -/
  theta_zero : ∀ z, θ z 0 = 0

namespace ThetaStage

variable {R : Type*} [CommRing R] (S : ThetaStage R)

attribute [instance] ThetaStage.fin

/-- **The theta sum (O.4)** (tex 8600–8604):
`H(k) = ∑_z (c₀/|R_z^×|) P_M(z) χ_{h_*}(Nrd z) ∑_{Q_B(x) = k} f(z⁻¹xz)`, a finite sum in `R`. -/
def H (k : ℕ) : R := ∑ z, ((c0 / S.w z : ℕ) : R) * S.P z * (S.χN z * S.θ z k)

/-- **The phase-removed stage coefficients** `aθ(n) = H_M(mn)` (tex 8416, 9083). -/
def aθ (n : ℕ) : R := S.H (S.m * n)

theorem jacobi_sq_one {p : ℕ} (hp : S.Good p) :
    (jacobiSym (-(S.m : ℤ)) p : R) * (jacobiSym (-(S.m : ℤ)) p : R) = 1 := by
  haveI := Fact.mk (S.good_prime p hp)
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have h0 : ((-(S.m : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h
    apply S.good_m p hp
    have : (p : ℤ) ∣ -(S.m : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h
    exact Int.natCast_dvd_natCast.mp (dvd_neg.mp this)
  rcases legendreSym.eq_one_or_neg_one p h0 with h | h <;> rw [h] <;> push_cast <;> ring

/-- **PROVED (tex 9059–9082): the Brandt identity.** At every good prime `p` and every index `n`:
`H(p²n) + s(−n/p)H(n) + p s² H(n/p²) = s χ_{h_*}(p) a_p H(n)` (`H(n/p²) = 0` if `p² ∤ n`). -/
theorem brandt {p : ℕ} (hp : S.Good p) (n : ℕ) :
    haveI := Fact.mk (S.good_prime p hp)
    S.H (p ^ 2 * n) + S.s p * (legendreSym p (-(n : ℤ)) : R) * S.H n +
      (p : R) * S.s p ^ 2 * divCoeff S.H (p ^ 2) n =
      S.s p * (jacobiSym (-(S.m : ℤ)) p : R) * (S.ap p : R) * S.H n := by
  haveI := Fact.mk (S.good_prime p hp)
  have hadj : ∀ i j, c0 / S.w i * nbrCount (S.nb p) i j = c0 / S.w j * nbrCount (S.nb p) j i :=
    fun i j => mass_adjoint (S.w_dvd i) (S.w_dvd j) (S.w_pos i) (S.w_pos j) (S.adjoint p hp i j)
  have hnbr : ∀ z n, ∑ L, (fun z k => S.χN z * S.θ z k) (S.nb p z L) n =
      (jacobiSym (-(S.m : ℤ)) p : R) * (S.sinv p * (S.χN z * S.θ z (p ^ 2 * n)) +
        (legendreSym p (-(n : ℤ)) : R) * (S.χN z * S.θ z n) +
        (p : R) * S.s p * divCoeff (fun k => S.χN z * S.θ z k) (p ^ 2) n) := by
    intro z n
    simp only [S.frame_nbr p hp]
    rw [← Finset.mul_sum, (S.frame p hp z).neighbor_identity (S.good_ne_two p hp)
      (S.s_unit p hp) (S.frame_scale p hp z) n]
    simp only [S.frame_theta p hp z]
    have : divCoeff (fun k => S.χN z * (S.frame p hp z).theta k) (p ^ 2) n =
        S.χN z * divCoeff (S.frame p hp z).theta (p ^ 2) n := by
      unfold divCoeff; split_ifs <;> simp
    rw [this]; ring
  have := brandt_identity (S.nb p) (fun z => c0 / S.w z) S.P (fun z k => S.χN z * S.θ z k)
    (S.ap p : R) (S.s p) (S.sinv p) (jacobiSym (-(S.m : ℤ)) p : R) (S.s_unit p hp)
    (S.jacobi_sq_one hp) hadj (S.hecke p hp) hnbr n
  exact this

/-- **PROVED ((O.6), tex 9083–9093).** At every good prime `p` the phase-removed coefficients
satisfy `aθ(p²n) = {η(p)a_p − ψ(p)(−n/p)} aθ(n) − p η(p)² aθ(n/p²)` with `ψ(p) = η(p)(−1/p)`
(`ψ/η = χ_{−1}`): `RecAt p (η p) (−1/p) a_p aθ`. -/
theorem recAt {p : ℕ} (hp : S.Good p) :
    haveI := Fact.mk (S.good_prime p hp)
    RecAt p (S.η p) (legendreSym p (-1)) (S.ap p) S.aθ := by
  haveI := Fact.mk (S.good_prime p hp)
  have hχ : (jacobiSym (-(S.m : ℤ)) p : R) = (legendreSym p (-(S.m : ℤ)) : R) := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
  have hχ2 : ((legendreSym p (-(S.m : ℤ)) : ℤ) : R) ^ 2 = 1 := by
    rw [pow_two, ← hχ]; exact S.jacobi_sq_one hp
  have hε : ((legendreSym p (S.m : ℤ) : ℤ) : R) =
      ((legendreSym p (-1) : ℤ) : R) * ((legendreSym p (-(S.m : ℤ)) : ℤ) : R) := by
    rw [← Int.cast_mul, ← legendreSym.mul]; congr 2; ring
  have h := O6_of_brandt S.H (S.good_m p hp) (S.s p) _ (S.ap p) (legendreSym p (-1)) hχ2 hε
    (fun n => by have := S.brandt hp n; rw [hχ] at this; exact this)
  rw [S.η_good p hp, hχ]
  exact h

/-- **PROVED (tex 9092).** `aθ(0) = 0`. -/
theorem aθ_zero : S.aθ 0 = 0 := by
  simp [aθ, H, S.theta_zero]

/-- **PROVED: the coefficient source.** For a stage whose `a_q` satisfy `a_q ≡ q + 1 (mod 4)` at
the good primes and whose coefficients satisfy App G's depth inequality (the field `depth` of
`SourceHyp`), the phase-removed coefficients `aθ` satisfy the tree's `SourceHyp`. -/
theorem sourceHyp {T δ : ℕ} (hap : ∀ q, S.Good q → S.ap q ≡ q + 1 [ZMOD 4])
    (depth : ∀ n, (2 : R) ^ (min T (δ + (oddPart n).card)) ∣ S.aθ n) :
    SourceHyp T δ S.η S.Good S.ap S.aθ where
  prime := S.good_prime
  odd q hq := by exact_mod_cast (S.good_prime q hq).odd_of_ne_two (S.good_ne_two q hq)
  ap_mod := hap
  recur q hq := by
    haveI := Fact.mk (S.good_prime q hq)
    refine ⟨legendreSym q (-1), ?_, S.recAt hq⟩
    have h0 : ((-1 : ℤ) : ZMod q) ≠ 0 := by simp
    exact legendreSym.eq_one_or_neg_one q h0
  zero := S.aθ_zero
  depth := depth
  mul := S.η_mul
  one := S.η_one

/-- **PROVED: the tree's `OddStageSource` at one actual stage** (`R = ZMod (2^M)`, the model of
`𝒪/2^M𝒪` used by `RC/Odd/Statements.lean`). Consumers: `Odd.O9_odd_stage`, `Odd.O11_odd_stage`. -/
theorem oddStageSource {M δ : ℕ} (S : ThetaStage (ZMod (2 ^ M)))
    (hap : ∀ q, S.Good q → S.ap q ≡ q + 1 [ZMOD 4])
    (depth : ∀ n, (2 : ZMod (2 ^ M)) ^ (min M (δ + (oddPart n).card)) ∣ S.aθ n) :
    OddStageSource M δ S.η S.Good S.ap S.aθ :=
  S.sourceHyp hap depth

end ThetaStage

end ZInQ.Manuscript.RC.AppF
