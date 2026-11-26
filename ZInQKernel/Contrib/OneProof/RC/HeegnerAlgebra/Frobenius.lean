import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.GroupRing

/-!
# Lane RC10 (Heegner algebra), part 5: exact finite precision for one derivative prime

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 6, tex lines 3097–3200: the Frobenius algebra (H13)–(H18) and the local relation (H19)
`f_new = 0`, `s_new = J f_old` at precision `2^m`.

Notation (tex 3097–3117): `X = D_I y_{f n_I}`, `Y = D_I y_{f n_I ℓ}`, `F` the arithmetic Frobenius
on the reduced curve, `F² - a_ℓ F + ℓ = 0`, `Tr Y = a_ℓ X`, `Ȳ = F X̄`, `F² X̄ = X̄` (H13);
`2^a Q = L X` and `f_old = (F² - 1) Q̄ = (a_ℓ F - (ℓ+1)) Q̄` (H14); `2^a Z = L D_ℓ Y`, `b` the
adjusted cocycle with `b|_{G_{H_{f n_I ℓ}}} = (g - 1) Z`, `U = (σ_ℓ - 1) Z - b(σ_ℓ)`.

Everything is `PROVED` from explicit hypotheses.  The hypotheses are the arithmetic inputs:
(4.1) (`Tr Y = a_ℓ X`; Cai–Chen–Liu, `PRINT`, unweighted: the print once the unit index
`u_1 = [𝒪_K^× : ℤ^×]` is one, `D_K < -4`), (H4) (`Ȳ = F X̄`, the CM congruence; `ELLIOT`'s
supersingular-specialization argument, tex 2948–2967), the splitting of `(ℓ)` in `H_{f n_I}`
(`F² X̄ = X̄`), inertia acting trivially on reductions, injectivity of reduction on `2`-primary
torsion, the characteristic polynomial of Frobenius, (H2) for the upper field, and the
formal-group division argument behind "the restricted Kummer class is zero" (Silverman IV.2.3,
IV.3.2; `PRINT`/`GLUE`).
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open Finset

/-! ## The cocycle computation (tex 3122–3139) -/

section Cocycle

variable {G V : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]

/-- tex 3133–3136, `PROVED`: for a cocycle `b` on `G = G_{H_{f n_I}}` whose restriction to the
normal subgroup `G_{H_{f n_I ℓ}}` is exactly the Kummer cocycle `g ↦ (g - 1) Z`, the element
`U = (σ - 1) Z - b(σ)` is fixed by `G_{H_{f n_I ℓ}}`, i.e. is a point of `E(H_{f n_I ℓ})`. -/
theorem U_fixed (Hup : Subgroup G) [Hup.Normal] (b : G → V)
    (hb : ∀ g k, b (g * k) = b g + g • b k) (Z : V) (hbH : ∀ h ∈ Hup, b h = h • Z - Z)
    (σ : G) : ∀ h ∈ Hup, h • ((σ • Z - Z) - b σ) = (σ • Z - Z) - b σ := by
  intro h hh
  have hh' : σ⁻¹ * h * σ ∈ Hup := by
    have := Subgroup.Normal.conj_mem ‹Hup.Normal› h hh σ⁻¹
    simpa using this
  have e1 : b (h * σ) = (h • Z - Z) + h • b σ := by rw [hb, hbH h hh]
  have e2 : b (h * σ) = b σ + σ • ((σ⁻¹ * h * σ) • Z - Z) := by
    rw [show h * σ = σ * (σ⁻¹ * h * σ) by group, hb, hbH _ hh']
  have e3 : σ • ((σ⁻¹ * h * σ) • Z - Z) = (h * σ) • Z - σ • Z := by
    rw [smul_sub, ← mul_smul, show σ * (σ⁻¹ * h * σ) = h * σ by group]
  rw [e3] at e2
  have key : h • b σ = b σ + (h * σ) • Z - σ • Z - h • Z + Z := by
    have := e1.symm.trans e2
    rw [← sub_eq_zero] at this ⊢
    rw [← this]; abel
  rw [smul_sub, smul_sub, key, mul_smul]
  abel

/-- tex 3137–3139, `PROVED`: `2^a U = L((ℓ+1) Y - a_ℓ X)`, from `2^a Z = L D_ℓ Y`, the values of
`b` lying in `E[2^a]`, `σ^{ℓ+1} Y = Y`, (H6) and `Tr Y = a_ℓ X` (4.1). -/
theorem two_pow_U (σ : G) (ℓ a : ℕ) (L aℓ : ℤ) (X Y Z bσ : V)
    (hZ : ((2 : ℤ) ^ a) • Z = L • Dact σ ℓ Y) (hbσ : ((2 : ℤ) ^ a) • bσ = 0)
    (hY : σ ^ (ℓ + 1) • Y = Y) (hTr : Tract σ ℓ Y = aℓ • X) :
    ((2 : ℤ) ^ a) • ((σ • Z - Z) - bσ) = L • (((ℓ : ℤ) + 1) • Y - aℓ • X) := by
  rw [smul_sub, hbσ, sub_zero, smul_sub, smul_comm, hZ, smul_comm σ L, ← smul_sub,
    H6_act σ ℓ Y hY, hTr]

/-- (H15), tex 3140–3146, `PROVED`: with `ℓ + 1 = 2^a u'` and `a_ℓ = 2^a v'`, the integral point
`U₀ = L u' Y - L v' X` has the same `2^a`-multiple as `U`; if `U` and `U₀` are points of the upper
field and every `2`-primary point there is killed by `2^e` (H2), then `2^e (U - U₀) = 0`. -/
theorem H15 (Hup : Subgroup G) (a e : ℕ) (L aℓ u' v' : ℤ) (ℓ : ℕ) (X Y U : V)
    (hu' : (ℓ : ℤ) + 1 = 2 ^ a * u') (hv' : aℓ = 2 ^ a * v')
    (hU : ((2 : ℤ) ^ a) • U = L • (((ℓ : ℤ) + 1) • Y - aℓ • X))
    (hUfix : ∀ h ∈ Hup, h • U = U) (hXfix : ∀ h ∈ Hup, h • X = X)
    (hYfix : ∀ h ∈ Hup, h • Y = Y)
    (hH2 : ∀ P : V, (∀ h ∈ Hup, h • P = P) → (∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) →
      ((2 : ℤ) ^ e) • P = 0) :
    ((2 : ℤ) ^ e) • (U - ((L * u') • Y - (L * v') • X)) = 0 := by
  apply hH2
  · intro h hh
    rw [smul_sub, smul_sub, smul_comm h (L * u'), smul_comm h (L * v'), hUfix h hh, hXfix h hh,
      hYfix h hh]
  · refine ⟨a, ?_⟩
    rw [smul_sub, hU, hu', hv']
    module

end Cocycle

/-! ## The Frobenius algebra (H14), (H17) -/

/-- (H14), tex 3114–3117, `PROVED`: if `F² - a F + ℓ = 0` then `F² - 1 = a F - (ℓ + 1)`. -/
theorem H14 {R : Type*} [Ring R] (F : R) (a ℓ : ℤ) (hF : F ^ 2 - (a : R) * F + (ℓ : R) = 0) :
    F ^ 2 - 1 = (a : R) * F - ((ℓ : R) + 1) := by
  have : F ^ 2 = (a : R) * F - (ℓ : R) := by
    rw [← sub_eq_zero, ← hF]; abel
  rw [this]; abel

/-- (H17), polynomial form, tex 3158–3162, `PROVED`:
`(X - a)(a X - (ℓ+1)) = (a - (ℓ+1) X) + a (X² - a X + ℓ)` in `ℤ[X]`. -/
theorem H17_poly (a ℓ : ℤ) :
    (Polynomial.X - Polynomial.C a) * (Polynomial.C a * Polynomial.X - (Polynomial.C ℓ + 1)) =
      (Polynomial.C a - (Polynomial.C ℓ + 1) * Polynomial.X) +
        Polynomial.C a * (Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C ℓ) := by
  ring

/-- (H17), tex 3158–3162, `PROVED` in any ring: if `F² - a F + ℓ = 0` then
`(F - a)(a F - (ℓ+1)) = a - (ℓ+1) F`. -/
theorem H17 {R : Type*} [Ring R] (F : R) (a ℓ : ℤ) (hF : F ^ 2 - (a : R) * F + (ℓ : R) = 0) :
    (F - (a : R)) * ((a : R) * F - ((ℓ : R) + 1)) = (a : R) - ((ℓ : R) + 1) * F := by
  have h := congrArg (Polynomial.aeval F) (H17_poly a ℓ)
  simp only [map_mul, map_sub, map_add, Polynomial.aeval_X, map_one, map_pow, map_intCast,
    eq_intCast] at h
  rw [h, hF, mul_zero, add_zero]

/-! ## Reductions: (H16), (H18), the precision push and (H19) -/

section Reduction

variable {G V Vb : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V] [AddCommGroup Vb]

/-- (H16), first equality, tex 3150–3157, `PROVED`.  With `b(σ) = (σ - 1) Z - U`, inertia acting
trivially on reductions (`red (σ Z) = red Z`), `Ȳ = F X̄` (H13), `2^a Q = L X`,
`ℓ + 1 = 2^a u'`, `a_ℓ = 2^a v'` and `U₀ = L u' Y - L v' X`, the singular coordinate is
`s_new = red b(σ) = (a_ℓ - (ℓ+1) F) Q̄ + ε` with `ε = -red(U - U₀)`. -/
theorem H16 (red : V →+ Vb) (F : Vb →+ Vb) (σ : G) (a : ℕ) (L aℓ u' v' : ℤ) (ℓ : ℕ)
    (X Y Z Q U : V) (hinert : red (σ • Z) = red Z) (hYX : red Y = F (red X))
    (hQ : ((2 : ℤ) ^ a) • Q = L • X) (hu' : (ℓ : ℤ) + 1 = 2 ^ a * u') (hv' : aℓ = 2 ^ a * v') :
    red ((σ • Z - Z) - U) =
      (aℓ • red Q - ((ℓ : ℤ) + 1) • F (red Q)) - red (U - ((L * u') • Y - (L * v') • X)) := by
  have hLX : L • red X = ((2 : ℤ) ^ a) • red Q := by rw [← map_zsmul, ← map_zsmul, hQ]
  have h1 : red ((L * u') • Y) = ((ℓ : ℤ) + 1) • F (red Q) := by
    rw [map_zsmul, hYX, mul_comm, mul_smul, ← map_zsmul F L, hLX, map_zsmul, smul_smul, hu',
      mul_comm]
  have h2 : red ((L * v') • X) = aℓ • red Q := by
    rw [map_zsmul, mul_comm, mul_smul, hLX, smul_smul, hv', mul_comm]
  rw [map_sub, map_sub, hinert, sub_self, map_sub, map_sub, h1, h2]
  abel

/-- (H14) on reduced points, tex 3114–3117, `PROVED`: from `F² - a_ℓ F + ℓ = 0` on the reduced
curve, `f_old = (F² - 1) Q̄ = (a_ℓ F - (ℓ+1)) Q̄`. -/
theorem H14_points (F : Vb →+ Vb) (aℓ ℓ : ℤ) (hchar : ∀ w : Vb, F (F w) - aℓ • F w + ℓ • w = 0)
    (Qb : Vb) : F (F Qb) - Qb = aℓ • F Qb - (ℓ + 1) • Qb := by
  have h1 := hchar Qb
  rw [add_smul, one_smul, ← sub_eq_zero, ← h1]; abel

/-- (H16), second equality, tex 3155–3162, `PROVED`: `(a_ℓ - (ℓ+1) F) Q̄ = (F - a_ℓ) f_old` with
`f_old = (F² - 1) Q̄`; this is (H17) applied to `Q̄`. -/
theorem H16_second (F : Vb →+ Vb) (aℓ ℓ : ℤ) (hchar : ∀ w : Vb, F (F w) - aℓ • F w + ℓ • w = 0)
    (Qb : Vb) :
    aℓ • Qb - (ℓ + 1) • F Qb = F (F (F Qb) - Qb) - aℓ • (F (F Qb) - Qb) := by
  have h1 := hchar Qb
  have h2 := hchar (F Qb)
  rw [map_sub, smul_sub]
  have e1 : F (F (F Qb)) = aℓ • F (F Qb) - ℓ • F Qb := by
    rw [← sub_eq_zero, ← h2]; abel
  have e2 : F (F Qb) = aℓ • F Qb - ℓ • Qb := by
    rw [← sub_eq_zero, ← h1]; abel
  rw [e1, e2, smul_sub, smul_smul, smul_smul, add_smul, one_smul]
  abel

/-- The precision push, tex 3163–3165, `PROVED`: if `s = (F - a_ℓ) f + ε` with `2^a f = 0`,
`2^e ε = 0`, `a - m ≥ e`, and `F - a_ℓ` acts as `J` on `2^a`-torsion (by (H12) and the
equivariant identification of `E[2^a]` with the reduced torsion), then at precision `m`
(multiplication by `2^{a-m}`) `s_new = J f_old`. -/
theorem precision_push (F J : Vb →+ Vb) (aℓ : ℤ) (a m e : ℕ) (hm : e ≤ a - m) (f ε : Vb)
    (hf : ((2 : ℤ) ^ a) • f = 0) (hε : ((2 : ℤ) ^ e) • ε = 0)
    (hJ : ∀ w : Vb, ((2 : ℤ) ^ a) • w = 0 → F w - aℓ • w = J w) :
    ((2 : ℤ) ^ (a - m)) • ((F f - aℓ • f) + ε) = J (((2 : ℤ) ^ (a - m)) • f) := by
  have hε' : ((2 : ℤ) ^ (a - m)) • ε = 0 := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hm
    rw [hk, pow_add, mul_comm, mul_smul, hε, smul_zero]
  rw [smul_add, hε', add_zero, hJ f hf, map_zsmul]

/-- `f_old` is `2^a`-torsion, tex 3114–3120, `PROVED`: `2^a (F² - 1) Q̄ = (F² - 1)(L X̄) = 0`
because `F² X̄ = X̄`. -/
theorem f_old_torsion (F : Vb →+ Vb) (a : ℕ) (L : ℤ) (Xb Qb : Vb)
    (hQ : ((2 : ℤ) ^ a) • Qb = L • Xb) (hX : F (F Xb) = Xb) :
    ((2 : ℤ) ^ a) • (F (F Qb) - Qb) = 0 := by
  rw [smul_sub, ← map_zsmul, ← map_zsmul, hQ, map_zsmul, map_zsmul, hX, sub_self]

/-- `∑_{j=1}^{ℓ} j = ℓ(ℓ+1)/2` (tex 3171, (H18)), in the form `2 ∑ j = ℓ(ℓ+1)`, `PROVED`. -/
theorem sum_Icc_id_two (ℓ : ℕ) : 2 * ∑ j ∈ Icc 1 ℓ, (j : ℤ) = (ℓ : ℤ) * (ℓ + 1) := by
  induction ℓ with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; push_cast; ring

/-- (H18), tex 3167–3174, `PROVED`: all inertia translates of `Y` have the same reduction, so
`red(L D_ℓ Y) = L ℓ(ℓ+1)/2 · F X̄`; with `ℓ + 1 = 2^{a+1} t` (H12) this is
`2^a · W`, `W = ℓ t L F X̄`, and `W` is fixed by `F²` ("the extra bit in (H12) pays exactly for
the division by two in (H18)"). -/
theorem H18 (red : V →+ Vb) (F : Vb →+ Vb) (σ : G) (a : ℕ) (L t : ℤ) (ℓ : ℕ) (X Y : V)
    (hinert : ∀ v : V, red (σ • v) = red v) (hYX : red Y = F (red X))
    (hX : F (F (red X)) = red X) (ht : (ℓ : ℤ) + 1 = 2 ^ (a + 1) * t) :
    red (L • Dact σ ℓ Y) = ((2 : ℤ) ^ a) • (((ℓ : ℤ) * t * L) • F (red X)) ∧
      F (F (((ℓ : ℤ) * t * L) • F (red X))) = ((ℓ : ℤ) * t * L) • F (red X) := by
  have hpow : ∀ j : ℕ, red (σ ^ j • Y) = red Y := by
    intro j; induction j with
    | zero => simp
    | succ n ih => rw [pow_succ', mul_smul, hinert, ih]
  have hsum : red (Dact σ ℓ Y) = (∑ j ∈ Icc 1 ℓ, (j : ℤ)) • red Y := by
    rw [Dact, map_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, hpow]
  have hS : ∑ j ∈ Icc 1 ℓ, (j : ℤ) = (ℓ : ℤ) * (2 ^ a * t) := by
    have h2 := sum_Icc_id_two ℓ
    rw [ht, pow_succ] at h2
    have : (2 : ℤ) * (∑ j ∈ Icc 1 ℓ, (j : ℤ) - (ℓ : ℤ) * (2 ^ a * t)) = 0 := by
      rw [mul_sub, h2]; ring
    have := (mul_eq_zero.mp this).resolve_left (by norm_num)
    linarith
  refine ⟨?_, ?_⟩
  · rw [map_zsmul, hsum, hS, hYX, smul_smul, smul_smul]
    congr 1; ring
  · rw [map_zsmul, map_zsmul, hX]

/-- (H19), the finite coordinate, tex 3175–3187, `PROVED`: if the restricted class is a
coboundary `g ↦ g P - P` (the local `2^a`-division point exists in the upper field, by the
formal-group argument) and the chosen Frobenius lift `φ` acts trivially on `E[2^a]` (by (H12):
`ρ_T(Fr_ℓ)² ≡ I`), then the cocycle value at `φ` is zero, independently of the coboundary
adjustment: `f_new = 0`. -/
theorem H19_finite (b : G → V) (P : V) (hcob : ∀ g, b g = g • P - P) (φ : G)
    (hφ : φ • P = P) : b φ = 0 := by
  rw [hcob, hφ, sub_self]

end Reduction

/-! ## One derivative prime, assembled -/

/-- (H13)–(H19) assembled, tex 3097–3190, `PROVED` from the listed inputs: the singular coordinate
of the new class at the derivative place, pushed to precision `m`, equals `J` applied to the
pushed finite coordinate `f_old = (F² - 1) Q̄` of the old class:
`2^{a-m} s_new = J (2^{a-m} f_old)`. -/
theorem H19_singular {G V Vb : Type*} [Group G] [AddCommGroup V] [DistribMulAction G V]
    [AddCommGroup Vb]
    (Hup : Subgroup G) [Hup.Normal]                -- `G_{H_{f n_I ℓ}} ⊴ G_{H_{f n_I}}`
    (σ : G) (ℓ a m e : ℕ) (L aℓ u' v' : ℤ)
    (X Y Z Q : V) (b : G → V)
    (hb : ∀ g k, b (g * k) = b g + g • b k)       -- `b` is a cocycle
    (hbtors : ((2 : ℤ) ^ a) • b σ = 0)              -- values in `E[2^a]`
    (hbH : ∀ h ∈ Hup, b h = h • Z - Z)             -- exact Kummer cocycle on the upper group
    (hZ : ((2 : ℤ) ^ a) • Z = L • Dact σ ℓ Y)       -- `2^a Z = L D_ℓ Y`
    (hQ : ((2 : ℤ) ^ a) • Q = L • X)                -- `2^a Q = L X`
    (hY : σ ^ (ℓ + 1) • Y = Y) (hTr : Tract σ ℓ Y = aℓ • X)   -- (4.1)
    (hXfix : ∀ h ∈ Hup, h • X = X) (hYfix : ∀ h ∈ Hup, h • Y = Y)
    (hH2 : ∀ P : V, (∀ h ∈ Hup, h • P = P) → (∃ k : ℕ, ((2 : ℤ) ^ k) • P = 0) →
      ((2 : ℤ) ^ e) • P = 0)                        -- (H2) for the upper field
    (hu' : (ℓ : ℤ) + 1 = 2 ^ a * u') (hv' : aℓ = 2 ^ a * v')   -- from (H12)
    (red : V →+ Vb) (F J : Vb →+ Vb)
    (hinert : red (σ • Z) = red Z)                  -- inertia acts trivially on reductions
    (hYX : red Y = F (red X)) (hXF : F (F (red X)) = red X)    -- (H13)
    (hchar : ∀ w : Vb, F (F w) - aℓ • F w + (ℓ : ℤ) • w = 0)  -- `F² - a_ℓ F + ℓ = 0`
    (hJ : ∀ w : Vb, ((2 : ℤ) ^ a) • w = 0 → F w - aℓ • w = J w)  -- (H12) on `E[2^a]`
    (hm : e ≤ a - m) :
    ((2 : ℤ) ^ (a - m)) • red (b σ) = J (((2 : ℤ) ^ (a - m)) • (F (F (red Q)) - red Q)) := by
  set U := (σ • Z - Z) - b σ with hUdef
  have hUfix : ∀ h ∈ Hup, h • U = U := U_fixed Hup b hb Z hbH σ
  have hU : ((2 : ℤ) ^ a) • U = L • (((ℓ : ℤ) + 1) • Y - aℓ • X) :=
    two_pow_U σ ℓ a L aℓ X Y Z (b σ) hZ hbtors hY hTr
  have hε := H15 Hup a e L aℓ u' v' ℓ X Y U hu' hv' hU hUfix hXfix hYfix hH2
  have hbσ : b σ = (σ • Z - Z) - U := by rw [hUdef]; abel
  have hs := H16 red F σ a L aℓ u' v' ℓ X Y Z Q U hinert hYX hQ hu' hv'
  rw [← hbσ] at hs
  set ε := -red (U - ((L * u') • Y - (L * v') • X)) with hεdef
  have hε' : ((2 : ℤ) ^ e) • ε = 0 := by
    rw [hεdef, smul_neg, ← map_zsmul, hε, map_zero, neg_zero]
  -- `(a_ℓ - (ℓ+1)F) Q̄ = (F - a_ℓ) f_old` with `f_old = (F² - 1) Q̄ = (a_ℓ F - (ℓ+1)) Q̄`
  have hfold : aℓ • red Q - ((ℓ : ℤ) + 1) • F (red Q) =
      F (F (F (red Q)) - red Q) - aℓ • (F (F (red Q)) - red Q) :=
    H16_second F aℓ ℓ hchar (red Q)
  have hf : ((2 : ℤ) ^ a) • (F (F (red Q)) - red Q) = 0 := by
    have hQb : ((2 : ℤ) ^ a) • red Q = L • red X := by rw [← map_zsmul, ← map_zsmul, hQ]
    exact f_old_torsion F a L (red X) (red Q) hQb hXF
  have hsum : red (b σ) = (F (F (F (red Q)) - red Q) - aℓ • (F (F (red Q)) - red Q)) + ε := by
    rw [hs, hfold, hεdef]; abel
  rw [hsum]
  exact precision_push F J aℓ a m e hm _ ε hf hε' hJ

end ZInQ.Manuscript.RC.HeegnerAlgebra
