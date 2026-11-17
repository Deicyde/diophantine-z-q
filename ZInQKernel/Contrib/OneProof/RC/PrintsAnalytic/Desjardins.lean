import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic

/-!
# Lane RC8: Desjardins, root numbers of twists at newly ramified primes (global-consequence form)

**Use in the manuscript (11/5 text).** tex L1994–2001 (proof of `ex:sec7-nonvanishing`): "The
root-number check includes ramified dyadic quadratic characters. At the primes in `S` equal
squareclasses give isomorphic local curves. At a good odd prime newly ramified in the parameter,
the root factor is `(-1/p)` [desjardins, Proposition 3.3]. Its product outside `S` is fixed by the
real sign and the dyadic unit class. Thus unit classes `3` or `7` modulo eight are allowed; the
field discriminant may be four times the parameter." This is what makes "the root number of a
signed unit filter" (L1974–1977: "A signed unit filter prescribes a real sign and unit
squareclasses at a finite set `S` containing `2, 3` and the bad primes ... If its root number is
even ...") well defined.

**The print** (J. Desjardins, *Root number of twists of an elliptic curve*, J. Théor. Nombres
Bordeaux 32 (2020), no. 1, 73–101; read in the publisher's PDF). §3.1.2, p. 84: "Let `p ≠ 2, 3` be a
prime number, and `t ∈ ℤ ∖ {0}` a squarefree integer. In the following, we compare `W_p(E)` and
`W_p(E_t)`."
> **Proposition 3.3.** Put `D_p ∈ {-1, +1}` the integer such that `W_p(E) = D_p W_p(E_t)`. We have
> (1) if `p ∤ t`: `D_p = +1` if `E` has good or additive reduction, `D_p = (t/p)` if `E` has
> multiplicative reduction;
> (2) if `p ∣ t`: `D_p = +1` if `E` has type `III` or `III*`; `D_p = (-1/p)` if `E` has type `I₀` or
> `I₀*`; `D_p = (3/p)` if `E` has type `II, II*, IV, IV*`; `D_p = -(-6b_{(p)}t_{(p)}/p)` if `E` has
> type `I_m` or `I_m*` (`m ≥ 1`).
Here `E : y² = x³ + ax + b` (`a, b ∈ ℤ`, minimal discriminant, §2.1), `E_t : y² = x³ + at²x + bt³`,
and `W_p` is the local root number, "defined in terms of the epsilon factors of the Weil–Deligne
representation of `ℚ_p`" (p. 73), with `W(E) = ∏_{p ≤ ∞} W_p(E)`, `W_∞(E) = -1`, and (p. 74) "`W(E)`
is equal to the sign of the functional equation of `L` by the Modularity Theorem over `ℚ`". The
case used is (2) with type `I₀` (good reduction at `p`): `W_p(E_t) = (-1/p) W_p(E) = (-1/p)`.

**Why a global-consequence form.** Local root numbers (epsilon factors of Weil–Deligne
representations) are not defined in Mathlib or the tree, so Proposition 3.3 itself cannot be
stated over genuine definitions. What the manuscript draws from it is global: for parameters `D,
D'` in one signed unit filter at `S`, `w(E^{(D)}) ∏_{p∣D} (-1/p) = w(E^{(D')}) ∏_{p∣D'} (-1/p)`.
`DesjardinsRootNumberFilter` states exactly that, over the shared vocabulary (`RootNumber`,
`qtwist`); its derivation from the print (DEPARTURE of form, recorded here):
* `W(E^{(D)}) = W_∞ · ∏_{q ∈ S} W_q(E^{(D)}) · ∏_{p ∉ S} W_p(E^{(D)})`, `W_∞ = -1`;
* `q ∈ S`: `D/D'` is a square in `ℚ_q` (Hensel, from the residue conditions), so `E^{(D)} ≅ E^{(D')}`
  over `ℚ_q` (`(X, Y) ↦ (u²X, u³Y)`), and local root numbers are invariants of the local curve;
* `p ∉ S`, `p ∤ D`: the twisted model is integral at `p` with `Δ = D⁶Δ(W)` prime to `p`: good
  reduction, `W_p = 1`;
* `p ∉ S`, `p ∣ D`: `p ≥ 5` and `E` is good at `p`; Proposition 3.3 (2), type `I₀`, gives
  `W_p(E^{(D)}) = (-1/p)` (at `p ≥ 5` the model is `p`-adically isomorphic to Desjardins' short model,
  compatibly with twisting);
* `∏_{p ∣ D} (-1/p) = (-1/|D|)` (Jacobi symbol; `D` is odd since `2 ∈ S`);
* `W = ` the sign of the functional equation (modularity; Desjardins p. 74): GLUE.

**Use check.** The manuscript's `S` contains `2, 3` and the bad primes ✓ (Proposition 3.3 needs
`p ≠ 2, 3`, and every newly ramified prime is outside `S`); the parameters are squarefree and prime
to `S` ✓ ("unit squareclasses"); a newly ramified good prime has type `I₀` ✓. The corollary
`rootNumber_eq_of_sameSignedUnitClasses` (PROVED) is the manuscript's sentence "Its product outside
`S` is fixed by the real sign and the dyadic unit class": parameters of one filter have one root
number. For `E_ℓ` use the integral model `curveZ ℓ` (`curveZ_map`, `curveZ_Δ`, PROVED).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53

/-- **`D` and `D'` lie in one signed unit filter at `S`**: the same sign, both prime to every
`q ∈ S`, `DD' ≡ 1 (mod 8)` when `q = 2`, and `DD'` a square modulo `q` for odd `q ∈ S`. By Hensel's
lemma this says `D/D'` is a square in `ℤ_q^×` for every `q ∈ S` (and positive at `∞`). -/
def SameSignedUnitClasses (S : Finset ℕ) (D D' : ℤ) : Prop :=
  Int.sign D = Int.sign D' ∧ ∀ q ∈ S, ¬ (q : ℤ) ∣ D ∧ ¬ (q : ℤ) ∣ D' ∧
    (q = 2 → (D * D') % 8 = 1) ∧ (q ≠ 2 → IsSquare ((D * D' : ℤ) : ZMod q))

/-- **Desjardins, Proposition 3.3, in the global form used at tex L1994–2001** (PRINT, composite;
J. Théor. Nombres Bordeaux 32 (2020) 73–101, Prop. 3.3 (2), type `I₀`, p. 84, with the product
formula `W = ∏_{p ≤ ∞} W_p`, `W_∞ = -1`, p. 73, and "`W(E)` is equal to the sign of the functional
equation of `L` by the Modularity Theorem over `ℚ`", p. 74). Let `W` be a Weierstrass equation over
`ℤ` of an elliptic curve `E/ℚ`, and `S` a finite set of primes containing `2`, `3` and every prime
dividing `Δ(W)`. For squarefree `D, D'` in one signed unit filter at `S`, with root numbers `w`, `w'`
of `E^{(D)}`, `E^{(D')}`:  `w · (-1/|D|) = w' · (-1/|D'|)`, where `(-1/|D|) = ∏_{p ∣ D} (-1/p)` is
the product of the newly ramified local root numbers. (See the module docstring for the derivation
from the print and the GLUE it uses.) -/
def DesjardinsRootNumberFilter : Prop :=
  ∀ (W : WeierstrassCurve ℤ) (S : Finset ℕ), (W.map (Int.castRingHom ℚ)).IsElliptic →
    (∀ q ∈ S, q.Prime) → 2 ∈ S → 3 ∈ S → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → p ∈ S) →
    ∀ D D' : ℤ, Squarefree D → Squarefree D' → SameSignedUnitClasses S D D' →
      ∀ w w' : ℤ, RootNumber (qtwist (W.map (Int.castRingHom ℚ)) D) w →
        RootNumber (qtwist (W.map (Int.castRingHom ℚ)) D') w' →
        w * jacobiSym (-1) D.natAbs = w' * jacobiSym (-1) D'.natAbs

/-- The integral Weierstrass equation `y² = x³ + 2ℓx² - 3ℓ²x` of `E_ℓ`. -/
def curveZ (ℓ : ℤ) : WeierstrassCurve ℤ := ⟨0, 2 * ℓ, 0, -3 * ℓ ^ 2, 0⟩

/-- `curveZ ℓ` is a model over `ℤ` of `E_ℓ` (PROVED). -/
theorem curveZ_map (ℓ : ℤ) : (curveZ ℓ).map (Int.castRingHom ℚ) = curve (ℓ : ℚ) := by
  simp only [curveZ, curve, WeierstrassCurve.map, map_zero, map_mul, map_neg, map_pow, map_ofNat,
    eq_intCast]

/-- `Δ(curveZ ℓ) = 2304 ℓ⁶ = 2⁸ 3² ℓ⁶` (PROVED): its prime divisors are `2`, `3` and those of `ℓ`. -/
theorem curveZ_Δ (ℓ : ℤ) : (curveZ ℓ).Δ = 2304 * ℓ ^ 6 := by
  simp only [curveZ, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

/-- In one signed unit filter at a set `S ∋ 2`, `(-1/|D|) = (-1/|D'|)` (PROVED): both parameters are
odd, `D ≡ D' (mod 8)`, and they have the same sign, so `|D| ≡ |D'| (mod 4)`. -/
theorem jacobiSym_neg_one_eq_of_sameSignedUnitClasses {S : Finset ℕ} (h2 : 2 ∈ S) {D D' : ℤ}
    (h : SameSignedUnitClasses S D D') :
    jacobiSym (-1) D.natAbs = jacobiSym (-1) D'.natAbs := by
  obtain ⟨hsign, hS⟩ := h
  obtain ⟨hD2, hD'2, h8, -⟩ := hS 2 h2
  have h8' : (D * D') % 8 = 1 := h8 rfl
  have hD2' : ¬ (2 : ℤ) ∣ D := by exact_mod_cast hD2
  have hD'2' : ¬ (2 : ℤ) ∣ D' := by exact_mod_cast hD'2
  have hsq : (D' * D') % 8 = 1 := by
    have : D' % 8 = 1 ∨ D' % 8 = 3 ∨ D' % 8 = 5 ∨ D' % 8 = 7 := by omega
    rcases this with h | h | h | h <;> simp [Int.mul_emod, h]
  have e1 : (D * D' * D') % 8 = D' % 8 := by
    rw [Int.mul_emod, h8', one_mul, Int.emod_emod_of_dvd _ (dvd_refl _)]
  have e2 : (D * D' * D') % 8 = D % 8 := by
    rw [mul_assoc, Int.mul_emod, hsq, mul_one, Int.emod_emod_of_dvd _ (dvd_refl _)]
  have hmod : D % 8 = D' % 8 := by rw [← e2, e1]
  have hD0 : D ≠ 0 := by rintro rfl; exact hD2' (dvd_zero _)
  have hmod4 : D.natAbs % 4 = D'.natAbs % 4 := by
    rcases lt_or_gt_of_ne hD0 with hneg | hpos
    · have hs : Int.sign D = -1 := Int.sign_eq_neg_one_of_neg hneg
      have hD'neg : D' < 0 := Int.sign_eq_neg_one_iff_neg.mp (hsign ▸ hs)
      have f1 : (D.natAbs : ℤ) = -D := Int.ofNat_natAbs_of_nonpos hneg.le
      have f2 : (D'.natAbs : ℤ) = -D' := Int.ofNat_natAbs_of_nonpos hD'neg.le
      omega
    · have hs : Int.sign D = 1 := Int.sign_eq_one_of_pos hpos
      have hD'pos : 0 < D' := Int.sign_eq_one_iff_pos.mp (hsign ▸ hs)
      have f1 : (D.natAbs : ℤ) = D := Int.natAbs_of_nonneg hpos.le
      have f2 : (D'.natAbs : ℤ) = D' := Int.natAbs_of_nonneg hD'pos.le
      omega
  have hDn : Odd D.natAbs := Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega))
  have hD'n : Odd D'.natAbs := Int.natAbs_odd.mpr (Int.odd_iff.mpr (by omega))
  rw [jacobiSym.at_neg_one hDn, jacobiSym.at_neg_one hD'n, ZMod.χ₄_nat_mod_four,
    ZMod.χ₄_nat_mod_four D'.natAbs, hmod4]

/-- **One filter, one root number** (PROVED from `DesjardinsRootNumberFilter`; the manuscript's
"Its product outside `S` is fixed by the real sign and the dyadic unit class", tex L1997–1999). -/
theorem rootNumber_eq_of_sameSignedUnitClasses (hDes : DesjardinsRootNumberFilter)
    {W : WeierstrassCurve ℤ} {S : Finset ℕ} (hE : (W.map (Int.castRingHom ℚ)).IsElliptic)
    (hS : ∀ q ∈ S, q.Prime) (h2 : 2 ∈ S) (h3 : 3 ∈ S)
    (hbad : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ W.Δ → p ∈ S) {D D' : ℤ} (hD : Squarefree D)
    (hD' : Squarefree D') (h : SameSignedUnitClasses S D D') {w w' : ℤ}
    (hw : RootNumber (qtwist (W.map (Int.castRingHom ℚ)) D) w)
    (hw' : RootNumber (qtwist (W.map (Int.castRingHom ℚ)) D') w') : w = w' := by
  have key := hDes W S hE hS h2 h3 hbad D D' hD hD' h w w' hw hw'
  rw [jacobiSym_neg_one_eq_of_sameSignedUnitClasses h2 h] at key
  have hne : jacobiSym (-1) D'.natAbs ≠ 0 := by
    rcases jacobiSym.eq_one_or_neg_one (a := -1) (b := D'.natAbs) (by simp) with h1 | h1 <;>
      rw [h1] <;> norm_num
  exact mul_right_cancel₀ hne key

end ZInQ.Manuscript.RC.PrintsAnalytic
