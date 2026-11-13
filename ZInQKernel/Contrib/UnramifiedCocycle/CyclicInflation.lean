import ZInQKernel.Contrib.UnramifiedCocycle.PowerCochain
import ZInQKernel.HDecomp.Descent.B2Glue

/-!
# Explicit coboundaries after doubling a finite cyclic quotient

For every positive `n`, every (not necessarily normalized) sign cocycle on
`C_n = Multiplicative (ZMod n)` becomes a sign coboundary on `C_(2*n)` under the
natural reduction map.  The witness is the explicit product cochain from
`PowerCochain.lean`, multiplied by the original value at the identity.

This is a finite cyclic inflation theorem.  Its local pullback corollary requires
an actual continuous quotient lift; it does not assert the existence of that
unramified Galois lift.
-/

namespace ZInQ.Contrib.UnramifiedCocycle

open GlueDescent.B2

variable {U : Type*} [CommGroup U]

/-- The finite cyclic group in additive residue coordinates. -/
abbrev CyclicGroup (n : ℕ) := Multiplicative (ZMod n)

/-- The residue class of `1`, including the identity generator when `n = 1`. -/
def cyclicGenerator (n : ℕ) : CyclicGroup n := Multiplicative.ofAdd (1 : ZMod n)

theorem cyclicGenerator_pow (n k : ℕ) :
    cyclicGenerator n ^ k = Multiplicative.ofAdd (k : ZMod n) := by
  rw [cyclicGenerator, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]

@[simp] theorem cyclicGenerator_pow_order (n : ℕ) : cyclicGenerator n ^ n = 1 := by
  rw [cyclicGenerator_pow, ZMod.natCast_self]
  rfl

/-- The divisibility needed for the actual residue reduction map. -/
theorem dvd_double (n : ℕ) : n ∣ 2 * n := ⟨2, Nat.mul_comm _ _⟩

/-- Reduction `C_(2*n) → C_n`, not an arbitrary or unspecified cyclic map. -/
def cyclicReduction (n : ℕ) : CyclicGroup (2 * n) →* CyclicGroup n :=
  (ZMod.castHom (dvd_double n) (ZMod n)).toAddMonoidHom.toMultiplicative

theorem cyclicReduction_surjective (n : ℕ) : Function.Surjective (cyclicReduction n) := by
  intro x
  obtain ⟨y, hy⟩ := ZMod.castHom_surjective (dvd_double n) x.toAdd
  exact ⟨Multiplicative.ofAdd y, congrArg Multiplicative.ofAdd hy⟩

/-- Evaluate the reduction map using the canonical nonnegative representative. -/
theorem cyclicReduction_eq_pow (n : ℕ) [NeZero (2 * n)] (x : CyclicGroup (2 * n)) :
    cyclicReduction n x = cyclicGenerator n ^ x.toAdd.val := by
  rw [cyclicGenerator_pow]
  change Multiplicative.ofAdd ((ZMod.castHom (dvd_double n) (ZMod n)) x.toAdd) =
    Multiplicative.ofAdd (x.toAdd.val : ZMod n)
  apply congrArg Multiplicative.ofAdd
  calc
    _ = (ZMod.castHom (dvd_double n) (ZMod n)) (x.toAdd.val : ZMod (2 * n)) :=
      congrArg (ZMod.castHom (dvd_double n) (ZMod n)) (ZMod.natCast_zmod_val x.toAdd).symm
    _ = _ := map_natCast _ _

/-- The actual sign cochain on the doubled quotient, with normalization restored. -/
def doubledCochain (n : ℕ) (ε : CyclicGroup n → CyclicGroup n → U)
    (x : CyclicGroup (2 * n)) : U :=
  ε 1 1 * powerCochain (normalize ε) (cyclicGenerator n) x.toAdd.val

/-- The normalized coboundary calculation, including residue-coordinate wraparound. -/
theorem normalized_double_coboundary (n : ℕ) [NeZero n]
    (ε : CyclicGroup n → CyclicGroup n → U) (hc : CocycleLaw ε)
    (hs : ∀ x y, ε x y ^ 2 = 1) (x y : CyclicGroup (2 * n)) :
    normalize ε (cyclicReduction n x) (cyclicReduction n y) =
      dB (fun z : CyclicGroup (2 * n) =>
        powerCochain (normalize ε) (cyclicGenerator n) z.toAdd.val) x y := by
  let : NeZero (2 * n) := ⟨mul_ne_zero (by decide) (NeZero.ne n)⟩
  have hcn := normalize_cocycle ε hc
  have hun := normalize_one_right ε hc
  have hsn := normalize_sq ε hs
  have hperiod := powerCochain_double_period (normalize ε) (cyclicGenerator n)
    hcn hun hsn n (cyclicGenerator_pow_order n)
  simp only [dB, toAdd_mul, ZMod.val_add,
    nat_mod_of_period _ (2 * n) hperiod, cyclicReduction_eq_pow]
  apply (eq_mul_inv_iff_mul_eq).2
  exact powerCochain_mul (normalize ε) (cyclicGenerator n) hcn hun x.toAdd.val y.toAdd.val

/-- The product witness has square `1` at every point. -/
theorem doubledCochain_sq (n : ℕ) (ε : CyclicGroup n → CyclicGroup n → U)
    (hs : ∀ x y, ε x y ^ 2 = 1) (x : CyclicGroup (2 * n)) :
    doubledCochain n ε x ^ 2 = 1 := by
  rw [doubledCochain, mul_pow, hs,
    powerCochain_sq (normalize ε) (cyclicGenerator n) (normalize_sq ε hs), mul_one]

/-- Restoring the identity value gives the original, unnormalized cocycle exactly. -/
theorem doubledCochain_coboundary (n : ℕ) [NeZero n]
    (ε : CyclicGroup n → CyclicGroup n → U) (hc : CocycleLaw ε)
    (hs : ∀ x y, ε x y ^ 2 = 1) (x y : CyclicGroup (2 * n)) :
    ε (cyclicReduction n x) (cyclicReduction n y) = dB (doubledCochain n ε) x y := by
  have h := normalized_double_coboundary n ε hc hs x y
  have he : ε (cyclicReduction n x) (cyclicReduction n y) =
      dB (fun z : CyclicGroup (2 * n) =>
        powerCochain (normalize ε) (cyclicGenerator n) z.toAdd.val) x y * ε 1 1 := by
    rw [← h, normalize_mul_constant]
  rw [he]
  simp only [dB, doubledCochain]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/-- **Closed finite cyclic helper:** doubling kills every sign cocycle, without an
extra normalization assumption, without a restriction on the parity of `n`, and
with the trivial quotient `n = 1` included. -/
theorem signCob_cyclicDouble (n : ℕ) [NeZero n]
    (ε : CyclicGroup n → CyclicGroup n → U) (hε : IsSignCocycle ε) :
    SignCob (pull (cyclicReduction n) ε) := by
  refine ⟨doubledCochain n ε, IsLocallyConstant.of_discrete _,
    doubledCochain_sq n ε hε.2.1, ?_⟩
  exact doubledCochain_coboundary n ε hε.2.2 hε.2.1

/-- The finite cyclic result as a genuinely closed proposition with complex sign
coefficients.  This is deliberately distinct from `LeafUnramified`. -/
def FiniteCyclicInflation : Prop :=
  ∀ (n : ℕ) [NeZero n] (ε : CyclicGroup n → CyclicGroup n → ℂˣ),
    IsSignCocycle ε → SignCob (pull (cyclicReduction n) ε)

/-- Closed proof of the finite cyclic statement, not a provider for the arithmetic leaf. -/
theorem finiteCyclicInflation : FiniteCyclicInflation := by
  intro n _ ε hε
  exact signCob_cyclicDouble n ε hε

/-- Expanded statement used by the scoped type check; coefficients are fixed,
so this declaration has no universe parameters or ambient section hypotheses. -/
theorem finiteCyclicInflation_explicit (n : ℕ) [NeZero n]
    (ε : CyclicGroup n → CyclicGroup n → ℂˣ) (hε : IsSignCocycle ε) :
    SignCob (pull (cyclicReduction n) ε) := signCob_cyclicDouble n ε hε

/-- Pull an already constructed sign coboundary through a continuous group map. -/
theorem signCob_pull_continuous {G H : Type*} [Group G] [Group H]
    [TopologicalSpace G] [TopologicalSpace H] (r : H →* G) (hr : Continuous r)
    {ε : G → G → U} (hε : SignCob ε) : SignCob (pull r ε) := by
  obtain ⟨b, hbl, hbs, hbe⟩ := hε
  refine ⟨b ∘ r, hbl.comp_continuous hr, fun x => hbs (r x), ?_⟩
  intro x y
  simpa only [pull, dB, Function.comp_apply, map_mul] using hbe (r x) (r y)

/-- The exact local consumer of a genuine doubled cyclic quotient lift.
The lift and its continuity are explicit inputs, not claimed arithmetic facts. -/
theorem signCob_of_cyclicLift {G : Type*} [Group G] [TopologicalSpace G]
    (n : ℕ) [NeZero n] (q : G →* CyclicGroup n)
    (q₂ : G →* CyclicGroup (2 * n)) (hq₂ : Continuous q₂)
    (hcompat : (cyclicReduction n).comp q₂ = q)
    (ε : CyclicGroup n → CyclicGroup n → U) (hε : IsSignCocycle ε) :
    SignCob (pull q ε) := by
  have h := signCob_pull_continuous q₂ hq₂ (signCob_cyclicDouble n ε hε)
  have he : pull q₂ (pull (cyclicReduction n) ε) = pull q ε := by
    funext x y
    change ε (((cyclicReduction n).comp q₂) x) (((cyclicReduction n).comp q₂) y) =
      ε (q x) (q y)
    rw [hcompat]
  rwa [he] at h

end ZInQ.Contrib.UnramifiedCocycle
