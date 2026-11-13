import ZInQKernel.Contrib.TYZGenus.CM
import ZInQKernel.Contrib.TYZDecomp.Leaves

/-!
# cm-points: TYZ's genus-point package as genuine leaves plus glue

Task cm-points (2026-11-13). Report: `docs/research/cm-points.md`; log: `scratch/cm-points/log.md`.
Owner: cm-points. Imports `TYZGenus/CM.lean` (this task); the ring class fields of
`TYZGenus/RingClass.lean` (task ring-class) and the modular curve of `TYZGenus/X0.lean`
(task x0-32) enter through the parameters `Hn` (TYZ's `ℍ'_n`) and `Z` (TYZ's genus points) and
are bridged once those files are merged.

`ZInQ.Contrib.TYZDecomp.TYZGenusPackage` asks, for each pinned `ℓ` and squarefree `n ≡ 5 (mod 8)`,
for `PropN.GenusData ℓ n`, a structure over an *abstract* `ℤ[i]`-module `M` with abstract `τ`, `β`,
`Z`, `P`, `ε`. Here the objects are pinned inside the genuine `ℤ[i]`-module `A(ℚ̄)`
(`A : y² = x³ + 4x`, `[i] = (x, y) ↦ (−x, iy)`):

* `M := A(ℍ'_n)` (`CM.ptsOver (Hn n)`, a `ℤ[i]`-submodule once `i ∈ ℍ'_n`);
* `τ(y/2) := y • T`, `T = (2, −4) = τ(1/2)` (the cusp dictionary of TYZ L1393–1404, checked against
  32a1 by PARI's modular symbols in rv-tyz-inputs §1.5a: `τ(1/2) = (2, −4)`, `τ(i/2) = (−2, −4i)`,
  `τ(1) = (0, 0)`, `τ((1 ± i)/2) = (∓2i, 0)`);
* `β := galPt σ` for an automorphism `σ` of `ℚ̄` lifting `β₁ = r_∞(−1)r₂(−2)` (pinned on all
  quadratic fields by `IsBetaOneLift`);
* `P := Pseq ℓ ε Z`, the recursion of TYZ §3.1 (L1325–1329) as a definition.

Then the fields of `GenusData` split into separate leaves (each about pinned objects) and glue:
`τ_eq_zero` and `β_τ` are proved here (explicit points), `[i]`-linearity of `β` (TYZ's F4) is proved,
and the leaves are TYZ Lemma 3.18 (`Lemma318`), the normality of `ℍ'_n` (`NormalFields`, F5), `i ∈ ℍ'_n`
(`IContained`), and the genus-point statements (`GenusPtsDefined`, `Thm35First`, `Lemma321`).

No `sorry`, no `axiom`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.Package

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.PropN

/-! ## §1. `A(ℚ̄)` as a `ℤ[i]`-module -/

/-- `(a + bi) • P = a•P + b•[i]P`. -/
instance : SMul GaussianInt PtA where
  smul z P := z.re • P + z.im • iPt P

theorem gsmul_def (z : GaussianInt) (P : PtA) : z • P = z.re • P + z.im • iPt P := rfl

theorem iPt_zero : iPt (0 : PtA) = 0 := rfl

theorem iPt_zsmul (k : ℤ) (P : PtA) : iPt (k • P) = k • iPt P :=
  map_zsmul iHom k P

theorem iPt_neg (P : PtA) : iPt (-P) = -iPt P := map_neg iHom P

instance : Module GaussianInt PtA where
  one_smul P := by rw [gsmul_def]; simp
  mul_smul z w P := by
    simp only [gsmul_def, Zsqrtd.re_mul, Zsqrtd.im_mul, iPt_add, iPt_zsmul, iPt_iPt]
    simp only [zsmul_add, add_zsmul, mul_zsmul, zsmul_neg, neg_zsmul, one_zsmul]
    abel
  smul_zero z := by rw [gsmul_def, iPt_zero]; simp only [zsmul_zero, add_zero]
  smul_add z P Q := by
    rw [gsmul_def, gsmul_def, gsmul_def, iPt_add]; simp only [zsmul_add]; abel
  add_smul z w P := by
    rw [gsmul_def, gsmul_def, gsmul_def]; simp only [Zsqrtd.re_add, Zsqrtd.im_add, add_zsmul]
    abel
  zero_smul P := by rw [gsmul_def]; simp

/-! ## §2. The pinned `τ` -/

theorem nonsingular_T : curveAbar.toAffine.Nonsingular 2 (-4) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  refine ⟨by norm_num, Or.inr ?_⟩
  norm_num

/-- `T = τ(1/2) = (2, −4)` (rv-tyz-inputs §1.5a: `[0] ↦ 1/2 ↦ (2, −4)` in the model `y² = x³ + 4x`). -/
def ptT : PtA := .some 2 (-4) nonsingular_T

/-- **TYZ's `y ↦ τ(y/2)`, pinned**: `τ(y/2) = y • τ(1/2)`, `ℤ[i] → A[(1+i)³]`. -/
def tauG : GaussianInt →+ PtA :=
  (LinearMap.toSpanSingleton GaussianInt PtA ptT).toAddMonoidHom

theorem tauG_apply (y : GaussianInt) : tauG y = y • ptT := rfl

section TauFacts
open WeierstrassCurve.Affine

theorem nonsingular_00 : curveAbar.toAffine.Nonsingular 0 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  refine ⟨by norm_num, Or.inl ?_⟩
  norm_num

/-- `τ(1) = (0, 0)`. -/
def pt00 : PtA := .some 0 0 nonsingular_00

theorem ptT_add_self : ptT + ptT = pt00 := by
  have hy : (-4 : Qbar) ≠ curveAbar.toAffine.negY 2 (-4) := by
    simp only [negY, curveAbar_a₁, curveAbar_a₃]; norm_num
  rw [ptT, Point.add_self_of_Y_ne hy, pt00, Point.some.injEq]
  have hs : curveAbar.toAffine.slope 2 2 (-4) (-4) = -2 := by
    rw [slope_of_Y_ne rfl hy]
    simp only [negY, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄]; norm_num
  simp only [addX, addY, negAddY, negY, hs, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
  constructor <;> norm_num

theorem pt00_add_self : pt00 + pt00 = 0 := by
  rw [pt00]
  exact Point.add_self_of_Y_eq (by simp only [negY, curveAbar_a₁, curveAbar_a₃]; ring)

theorem iPt_pt00 : iPt pt00 = pt00 := by
  rw [pt00, iPt_some, Point.some.injEq]; constructor <;> ring

theorem two_zsmul_ptT : (2 : ℤ) • ptT = pt00 := by rw [two_zsmul, ptT_add_self]

theorem four_zsmul_ptT : (4 : ℤ) • ptT = 0 := by
  rw [show (4 : ℤ) = 2 * 2 by norm_num, mul_zsmul, two_zsmul_ptT, two_zsmul, pt00_add_self]

theorem two_zsmul_iPt_ptT : (2 : ℤ) • iPt ptT = pt00 := by
  rw [← iPt_zsmul, two_zsmul_ptT, iPt_pt00]

theorem zsmul_ptT_emod (k : ℤ) : k • ptT = (k % 4) • ptT := by
  rw [show k • ptT = (k % 4 + 4 * (k / 4)) • ptT by congr 1; omega]
  rw [add_zsmul, mul_comm, mul_zsmul, four_zsmul_ptT, zsmul_zero, add_zero]

theorem nonsingular_T' : curveAbar.toAffine.Nonsingular 2 4 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  refine ⟨by norm_num, Or.inr ?_⟩
  norm_num

theorem neg_ptT : -ptT = .some 2 4 nonsingular_T' := by
  rw [ptT, Point.neg_some, Point.some.injEq]
  simp only [negY, curveAbar_a₁, curveAbar_a₃]; norm_num

/-- The four multiples of `T`. -/
theorem zsmul_ptT_cases (k : ℤ) :
    k • ptT = 0 ∧ k % 4 = 0 ∨ k • ptT = ptT ∧ k % 4 = 1 ∨ k • ptT = pt00 ∧ k % 4 = 2 ∨
      k • ptT = -ptT ∧ k % 4 = 3 := by
  rw [zsmul_ptT_emod]
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
  have h4 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
  interval_cases h : k % 4
  · simp
  · simp
  · simp [two_zsmul_ptT]
  · right; right; right
    refine ⟨?_, rfl⟩
    rw [show (3 : ℤ) = 4 + -1 by norm_num, add_zsmul, four_zsmul_ptT, neg_one_zsmul, zero_add]


theorem iPt_ptT_ne (k : ℤ) : iPt ptT ≠ k • ptT := by
  rcases zsmul_ptT_cases k with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · rw [ptT, iPt_some]; exact Point.some_ne_zero _
  · rw [ptT, iPt_some, Ne, Point.some.injEq]; intro h; have := h.1; norm_num at this
  · rw [ptT, iPt_some, pt00, Ne, Point.some.injEq]; intro h; have := h.1; norm_num at this
  · rw [neg_ptT, ptT, iPt_some, Ne, Point.some.injEq]; intro h; have := h.1; norm_num at this

theorem tauG_mk (a b : ℤ) : tauG ⟨a, b⟩ = a • ptT + b • iPt ptT := rfl

theorem twoTwoI_dvd_iff (a b : ℤ) : twoTwoI ∣ (⟨a, b⟩ : GaussianInt) ↔ 2 ∣ b ∧ 4 ∣ a + b := by
  constructor
  · rintro ⟨w, hw⟩
    have h1 := congrArg Zsqrtd.re hw
    have h2 := congrArg Zsqrtd.im hw
    simp only [twoTwoI, Zsqrtd.re_mul, Zsqrtd.im_mul] at h1 h2
    exact ⟨⟨w.re + w.im, by linarith⟩, ⟨w.re, by linarith⟩⟩
  · rintro ⟨⟨q, hq⟩, ⟨r, hr⟩⟩
    refine ⟨⟨r, q - r⟩, ?_⟩
    ext <;> simp only [twoTwoI, Zsqrtd.re_mul, Zsqrtd.im_mul] <;> linarith

/-- **TYZ L1386 for the pinned `τ`**: `τ(y/2) = 0 ↔ y ∈ (2 + 2i)ℤ[i]`. -/
theorem tauG_eq_zero (y : GaussianInt) : tauG y = 0 ↔ twoTwoI ∣ y := by
  obtain ⟨a, b⟩ := y
  rw [twoTwoI_dvd_iff, tauG_mk]
  have hb : b • iPt ptT = (b % 2) • iPt ptT + (b / 2) • pt00 := by
    rw [show b • iPt ptT = (b % 2 + 2 * (b / 2)) • iPt ptT by congr 1; omega]
    rw [add_zsmul, mul_comm, mul_zsmul, two_zsmul_iPt_ptT]
  have hT : a • ptT + (b / 2) • pt00 = (a + 2 * (b / 2)) • ptT := by
    rw [add_zsmul, mul_comm, mul_zsmul, two_zsmul_ptT]
  have hb2 : b % 2 = 0 ∨ b % 2 = 1 := Int.emod_two_eq_zero_or_one b
  rcases hb2 with h | h
  · rw [hb, h, zero_zsmul, zero_add, hT]
    have hbe : b = 2 * (b / 2) := by omega
    rcases zsmul_ptT_cases (a + 2 * (b / 2)) with ⟨e, hm⟩ | ⟨e, hm⟩ | ⟨e, hm⟩ | ⟨e, hm⟩ <;>
      rw [e]
    · exact ⟨fun _ => ⟨⟨b / 2, by omega⟩, by omega⟩, fun _ => rfl⟩
    · refine ⟨fun h0 => ?_, fun h0 => by omega⟩
      rw [ptT] at h0; exact absurd h0 (Point.some_ne_zero _)
    · refine ⟨fun h0 => ?_, fun h0 => by omega⟩
      rw [pt00] at h0; exact absurd h0 (Point.some_ne_zero _)
    · refine ⟨fun h0 => ?_, fun h0 => by omega⟩
      rw [neg_ptT] at h0; exact absurd h0 (Point.some_ne_zero _)
  · rw [hb, h, one_zsmul]
    refine ⟨fun h0 => ?_, fun h0 => by omega⟩
    exfalso
    have h1 : iPt ptT = (-(a + 2 * (b / 2))) • ptT := by
      rw [neg_zsmul, ← hT, eq_neg_iff_add_eq_zero, ← h0]; abel
    exact iPt_ptT_ne _ h1

end TauFacts

/-! ## §3. TYZ's recursion as a definition -/

/-- **`P(d)` of TYZ §3.1 (L1325–1329), by recursion on `d`**:
`P(d) = Z(d) − Σ_{d₁ ∣ d, d₁ > 1, d₁ ≡ 1, 3 (8)} ε(d/d₁, d₁) 𝓛(d₁) P(d/d₁)`. -/
def Pseq (ℓ : ℕ → ℤ) (ε : ℕ → ℕ → GaussianInt) (Z : ℕ → PtA) (d : ℕ) : PtA :=
  Z d - ∑ x ∈ (d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3))).attach,
    (ε (d / x.1) x.1 * (ℓ x.1 : GaussianInt)) • Pseq ℓ ε Z (d / x.1)
termination_by d
decreasing_by
  obtain ⟨hx, h1, -⟩ := Finset.mem_filter.mp x.2
  exact Nat.div_lt_self (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hx).2) h1

/-- The `ε`-classes of TYZ Theorem 3.3 (L1299–1311), as in `PropN.GenusData.eps_53`, `eps_pm1`. -/
def EpsClasses (n : ℕ) (ε : ℕ → ℕ → GaussianInt) : Prop :=
  (∀ d₀ d₁ : ℕ, d₀ * d₁ ∣ n → d₀ % 8 = 5 → d₁ % 8 = 3 → ε d₀ d₁ = gi ∨ ε d₀ d₁ = -gi) ∧
  (∀ d₀ d₁ : ℕ, d₀ * d₁ ∣ n →
    (d₀ % 8 = 5 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 1 ∨ d₀ % 8 = 7 ∧ d₁ % 8 = 3) →
    ε d₀ d₁ = 1 ∨ ε d₀ d₁ = -1)

/-! ## §4. The lifting `β'` of `β₁ = r_∞(−1)r₂(−2)` -/

/-- The odd part (with sign) of a squarefree integer: `D/2` if `2 ∣ D`, else `D`. -/
def oddPartSqfree (D : ℤ) : ℤ := if 2 ∣ D then D / 2 else D

/-- **The action of the idele `β₁ = r_∞(−1)r₂(−2)` on `√D`**, `D` squarefree: the product of
Hilbert symbols `(−1, D)_∞ (−2, D)_2 = sgn(D)·(−2, D)_2`, and `(−2, D)_2 = +1` iff the odd part
`v` of `D` is `≡ 1, 3 (mod 8)` (Serre, *A course in arithmetic*, Ch. III Thm. 1, formula for
`(a, b)_2`; STANDARD). Independent of the normalization of the Artin map (quadratic characters).
At `D = −1` it is `+1`: `β₁` fixes `i` (TYZ L2581). -/
def betaOneSign (D : ℤ) : ℤ :=
  (if D < 0 then -1 else 1) * (if oddPartSqfree D % 8 = 1 ∨ oddPartSqfree D % 8 = 3 then 1 else -1)

/-- `σ ∈ Gal(ℚ̄/ℚ)` acts on every quadratic field as `β₁ = r_∞(−1)r₂(−2)` does. A lifting of `β₁`
(TYZ L2496–2500: "any liftings") satisfies this; the converse needs `ℍ'_n ∩ ℚ^{ab}` to be
multiquadratic (not used: the leaves below only assert the *existence* of such a `σ`). -/
def IsBetaOneLift (σ : GalQ) : Prop :=
  ∀ D : ℤ, Squarefree D → ∀ r : Qbar, r ^ 2 = (D : Qbar) → σ r = (betaOneSign D : Qbar) * r

/-! ## §5. The leaves (parameters: `Hn n = ℍ'_n ⊆ ℚ̄`, `Z e` = TYZ's genus point `Z(e)`) -/

/-- **Leaf RC-i**: `i ∈ ℍ'_n` (TYZ L1321: `ℍ'_n = L_n(i)·Π H'_{d₀}`; definitional once
`RingClass.lean` defines `ℍ'_n`). -/
def IContained (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → iQ ∈ Hn n

/-- **Leaf RC-F5**: `ℍ'_n/ℚ` is normal (nt-tyz F5: from TYZ Proposition 3.2(1), L1253–1260, and
Cox, *Primes of the form x² + ny²*, Lemma 9.3: ring class fields are generalized dihedral over `ℚ`;
refereed). -/
def NormalFields (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → Normal ℚ (Hn n)

/-- **Leaf TYZ-3.18 (with Lemma 3.16 and TYZ's fact (1) on `τ`)**: for squarefree `n ≡ 5 (mod 8)`,
every torsion point of `A(ℍ'_n)` is `τ(y/2)` for some `y ∈ ℤ[i]`, i.e.
`A(ℍ'_n)_tors = A[(1+i)³] = τ(½ℤ[i])`. TYZ Lemma 3.18 (L2230–2232), Lemma 3.16 (L2182–2185), and
L1386–1399 (from Tian, Cambridge J. Math. 2 (2014)); refereed. -/
def Lemma318 (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ P ∈ ptsOver (Hn n), IsOfFinAddOrder P → ∃ y : GaussianInt, tauG y = P

/-- **Leaf CM-Z (fields of definition of the genus points)**: for `e ∣ n`, `e ≡ 5, 7 (mod 8)`,
`Z(e) ∈ A(ℍ'_n)`. TYZ L1318–1321 (for `e ≡ 5`, `H'_e` is a factor of `ℍ'_n`) and L2558 (for
`e ≡ 7`, `Z(e)` is defined over `L_e ⊂ L_n(i)`), resting on Shimura's reciprocity law
(`CM.CMFieldOfDefinition`) and TYZ Proposition 3.2(1), Theorem 3.6. Refereed. -/
def GenusPtsDefined (Hn : ℕ → IntermediateField ℚ Qbar) (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ ptsOver (Hn n)

/-- **Leaf TYZ-3.3/3.5 (Theorem 3.3, `ε`-part, and Theorem 3.5, first assertion)**: there are
`ε(d₀, d₁) ∈ μ₄` in the classes of Theorem 3.3 such that, if `𝓛(n) = 0`, the point `P(n)` of
the recursion is torsion. TYZ L1299–1311, L1325–1330, L1353–1356, L1295. Refereed (with the
caveat of `tyz-t1.md` on Theorem 3.3's unprinted computation). -/
def Thm35First (ℓ : ℕ → ℤ) (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧ (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n))

/-- **Leaf TYZ-3.21 (Lemma 3.21(1), (4))**: there is a lifting `β'` of `β₁` (one for all `e ∣ n`)
with `Z(e)^{β'+1} ∈ g(e)τ((1−i)/2) + ℤτ(1)` for `e ≡ 5` and `Z(e)^{β'+1} = g(e)τ(1/2)` for `e ≡ 7`.
TYZ L2496–2500, L2504–2516 (for any lifting); refereed. -/
def Lemma321 (Z : ℕ → PtA) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 → galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG 1)

/-- The three genus-point leaves bundled with an existential `Z` (used when `Z` is not yet pinned
by `CM.lean`): this is strictly finer than `TYZGenusPackage`, whose `M`, `τ`, `β` are existential
too. -/
def GenusPointLeaf (ℓ : ℕ → ℤ) (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ Z : ℕ → PtA,
    (∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ ptsOver (Hn n)) ∧
    (∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧ (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n))) ∧
    (∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 → galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG 1))

/-! ## §6. Glue (proved) -/

section Glue
open WeierstrassCurve.Affine

/-- `A(K)` as a `ℤ[i]`-submodule of `A(ℚ̄)`, for `i ∈ K`. -/
def ptsOverMod (K : IntermediateField ℚ Qbar) (hi : iQ ∈ K) : Submodule GaussianInt PtA where
  carrier := ptsOver K
  add_mem' ha hb := (ptsOver K).add_mem ha hb
  zero_mem' := (ptsOver K).zero_mem
  smul_mem' z P hP := by
    show z.re • P + z.im • iPt P ∈ ptsOver K
    exact (ptsOver K).add_mem ((ptsOver K).zsmul_mem hP _) ((ptsOver K).zsmul_mem (iPt_mem hi hP) _)

theorem ptT_mem (K : IntermediateField ℚ Qbar) : ptT ∈ ptsOver K := by
  rw [mem_ptsOver_iff]
  refine ⟨ofNat_mem K 2, ?_⟩
  exact K.neg_mem (ofNat_mem K 4)

theorem tauG_mem (K : IntermediateField ℚ Qbar) (hi : iQ ∈ K) (y : GaussianInt) :
    tauG y ∈ ptsOverMod K hi :=
  (ptsOverMod K hi).smul_mem y (ptT_mem K)

theorem galPt_ptT (σ : GalQ) : galPt σ ptT = ptT := by
  obtain ⟨h', e⟩ := galPt_some σ nonsingular_T
  rw [ptT, e, Point.some.injEq]
  exact ⟨map_ofNat σ 2, by rw [map_neg, map_ofNat]⟩

theorem galPt_tauG (σ : GalQ) (hσ : σ iQ = iQ) (y : GaussianInt) : galPt σ (tauG y) = tauG y := by
  rw [tauG_apply, gsmul_def, map_add, map_zsmul, map_zsmul, galPt_iPt σ hσ, galPt_ptT]

theorem betaOneSign_neg_one : betaOneSign (-1) = 1 := by decide

theorem fixes_i_of_isBetaOneLift {σ : GalQ} (hσ : IsBetaOneLift σ) : σ iQ = iQ := by
  have h := hσ (-1) (isUnit_one.neg).squarefree iQ (by rw [iQ_sq]; push_cast; ring)
  rw [h, betaOneSign_neg_one, Int.cast_one, one_mul]

theorem Pseq_eq (ℓ : ℕ → ℤ) (ε : ℕ → ℕ → GaussianInt) (Z : ℕ → PtA) (d : ℕ) :
    Pseq ℓ ε Z d = Z d - ∑ d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3)),
      (ε (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) • Pseq ℓ ε Z (d / d₁) := by
  rw [Pseq]
  congr 1
  exact Finset.sum_attach _ (fun d₁ => (ε (d / d₁) d₁ * (ℓ d₁ : GaussianInt)) • Pseq ℓ ε Z (d / d₁))

/-- For `d ∣ n` of class `5, 7` and `d₁ ∣ d` of class `1, 3`, `d / d₁ ∣ n` has class `5, 7`. -/
theorem div_class {n d d₁ : ℕ} (hd : d ∈ n.divisors) (hdc : d % 8 = 5 ∨ d % 8 = 7)
    (hd₁ : d₁ ∈ d.divisors.filter (fun d₁ => 1 < d₁ ∧ (d₁ % 8 = 1 ∨ d₁ % 8 = 3))) :
    d / d₁ ∈ n.divisors ∧ (d / d₁ % 8 = 5 ∨ d / d₁ % 8 = 7) := by
  obtain ⟨hd₁d, -, hc⟩ := Finset.mem_filter.mp hd₁
  have hdd : d₁ ∣ d := Nat.dvd_of_mem_divisors hd₁d
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hn0 : n ≠ 0 := (Nat.mem_divisors.mp hd).2
  refine ⟨Nat.mem_divisors.mpr ⟨(Nat.div_dvd_of_dvd hdd).trans hdn, hn0⟩, ?_⟩
  rcases hdc with h | h <;> rcases hc with h' | h'
  · rw [div_mod8_of hdd h h' (Or.inl rfl)]; left; rfl
  · rw [div_mod8_of hdd h h' (Or.inr (Or.inl rfl))]; right; rfl
  · rw [div_mod8_of hdd h h' (Or.inl rfl)]; right; rfl
  · rw [div_mod8_of hdd h h' (Or.inr (Or.inl rfl))]; left; rfl

theorem Pseq_mem {ℓ : ℕ → ℤ} {ε : ℕ → ℕ → GaussianInt} {Z : ℕ → PtA} {n : ℕ}
    {S : Submodule GaussianInt PtA}
    (hZ : ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ S) :
    ∀ d, d ∈ n.divisors → (d % 8 = 5 ∨ d % 8 = 7) → Pseq ℓ ε Z d ∈ S := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd hdc
    rw [Pseq_eq]
    refine S.sub_mem (hZ d hd hdc) (S.sum_mem fun d₁ hd₁ => S.smul_mem _ ?_)
    obtain ⟨h1, h2⟩ := div_class hd hdc hd₁
    obtain ⟨-, hlt, -⟩ := Finset.mem_filter.mp hd₁
    exact ih _ (Nat.div_lt_self (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2.symm.symm |>
      fun h => Nat.pos_of_mem_divisors hd) hlt) h1 h2

open Classical in
/-- **Core glue**: the pinned objects give `PropN.GenusData ℓ n`. -/
theorem genusData_of {ℓ : ℕ → ℤ} {n : ℕ} (hn : n % 8 = 5) (K : IntermediateField ℚ Qbar)
    (hi : iQ ∈ K) (hN : Normal ℚ K)
    (h318 : ∀ P ∈ ptsOver K, IsOfFinAddOrder P → ∃ y : GaussianInt, tauG y = P)
    (Z : ℕ → PtA) (hZ : ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ ptsOver K)
    (ε : ℕ → ℕ → GaussianInt) (hε : EpsClasses n ε)
    (htors : ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε Z n))
    (σ : GalQ) (hσ : IsBetaOneLift σ)
    (h5 : ∀ e ∈ n.divisors, e % 8 = 5 →
        ∃ k : ℤ, galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2)
    (h7 : ∀ e ∈ n.divisors, e % 8 = 7 → galPt σ (Z e) + Z e = (gNat e : ℤ) • tauG 1) :
    Nonempty (GenusData ℓ n) := by
  set S := ptsOverMod K hi with hS
  have hZS : ∀ e ∈ n.divisors, (e % 8 = 5 ∨ e % 8 = 7) → Z e ∈ S := hZ
  have hPS := Pseq_mem (ℓ := ℓ) (ε := ε) hZS
  have hσK : ∀ x ∈ K, σ x ∈ K := fun x hx =>
    (IntermediateField.normal_iff_forall_map_le.mp hN) σ.toAlgHom ⟨x, hx, rfl⟩
  have hσi := fixes_i_of_isBetaOneLift hσ
  have hn0 : n ≠ 0 := by omega
  have hnd : n ∈ n.divisors := Nat.mem_divisors_self n hn0
  let ZM : ℕ → S := fun e =>
    if h : e ∈ n.divisors ∧ (e % 8 = 5 ∨ e % 8 = 7) then ⟨Z e, hZS e h.1 h.2⟩ else 0
  let PM : ℕ → S := fun e =>
    if h : e ∈ n.divisors ∧ (e % 8 = 5 ∨ e % 8 = 7) then ⟨Pseq ℓ ε Z e, hPS e h.1 h.2⟩ else 0
  let τM : GaussianInt →+ S :=
    AddMonoidHom.mk' (fun y => ⟨tauG y, tauG_mem K hi y⟩) (fun a b => by ext; simp)
  let βM : S →+ S :=
    AddMonoidHom.mk' (fun x => ⟨galPt σ x, galPt_mem σ hσK x.2⟩) (fun a b => by ext; simp)
  have hZM : ∀ e (h : e ∈ n.divisors ∧ (e % 8 = 5 ∨ e % 8 = 7)), (ZM e : PtA) = Z e :=
    fun e h => by simp only [ZM, dite_eq_left_of_eq_true (eq_true h)]
  have hPM : ∀ e (h : e ∈ n.divisors ∧ (e % 8 = 5 ∨ e % 8 = 7)), (PM e : PtA) = Pseq ℓ ε Z e :=
    fun e h => by simp only [PM, dite_eq_left_of_eq_true (eq_true h)]
  refine ⟨{
      M := S
      Z := ZM
      P := PM
      ε := ε
      eps_53 := And.left hε
      eps_pm1 := And.right hε
      recursion := ?_
      torsion_of_zero := ?_
      τ := τM
      τ_eq_zero := ?_
      tors_mem_range := ?_
      β := βM
      β_τ := ?_
      beta_five := ?_
      beta_seven := ?_ }⟩
  · intro d hd hdc
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_sum, hPM d ⟨hd, hdc⟩, hZM d ⟨hd, hdc⟩, Pseq_eq]
    congr 1
    refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
    rw [Submodule.coe_smul, hPM _ (div_class hd hdc hd₁)]
  · intro h0
    have ht := htors h0
    rw [← hPM n ⟨hnd, Or.inl hn⟩] at ht
    exact (AddSubmonoid.isOfFinAddOrder_coe (H := S.toAddSubmonoid)).mp ht
  · intro y
    rw [← tauG_eq_zero]
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  · intro x hx
    obtain ⟨y, hy⟩ := h318 x x.2 ((AddSubmonoid.isOfFinAddOrder_coe (H := S.toAddSubmonoid)).mpr hx)
    exact ⟨y, Subtype.ext hy⟩
  · intro y
    exact Subtype.ext (galPt_tauG σ hσi y)
  · intro e he he5
    obtain ⟨k, hk⟩ := h5 e he he5
    refine ⟨k, Subtype.ext ?_⟩
    have h := hZM e ⟨he, Or.inl he5⟩
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, AddMonoidHom.mk'_apply, h, βM, τM]
    exact hk
  · intro e he he7
    apply Subtype.ext
    have h := hZM e ⟨he, Or.inr he7⟩
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, AddMonoidHom.mk'_apply, h, βM, τM]
    exact h7 e he he7

open ZInQ.Contrib.TYZDecomp in
/-- **Glue, level 1**: `i ∈ ℍ'_n`, normality of `ℍ'_n`, Lemma 3.18 and the genus-point leaf
(with existential `Z`) give `TYZGenusPackage`; here `M`, `τ`, `β` are pinned. -/
theorem genusPackage_of_genusPointLeaf (Hn : ℕ → IntermediateField ℚ Qbar) (hI : IContained Hn)
    (hN : NormalFields Hn) (h318 : Lemma318 Hn)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeaf ℓ Hn) : TYZGenusPackage := by
  intro ℓ hℓ n hn hsq
  obtain ⟨Z, hZ, ⟨ε, hε, ht⟩, ⟨σ, hσ, h5, h7⟩⟩ := hG ℓ hℓ n hn hsq
  exact genusData_of hn (Hn n) (hI n hn hsq) (hN n hn hsq) (h318 n hn hsq) Z hZ ε hε ht σ hσ h5 h7

/-- **Glue, level 2**: with the genus points `Z` pinned, the three genus-point leaves give the
bundled leaf. -/
theorem genusPointLeaf_of_split {ℓ : ℕ → ℤ} {Hn : ℕ → IntermediateField ℚ Qbar} {Z : ℕ → PtA}
    (hZ : GenusPtsDefined Hn Z) (h35 : Thm35First ℓ Z) (h321 : Lemma321 Z) :
    GenusPointLeaf ℓ Hn :=
  fun n hn hsq => ⟨Z, hZ n hn hsq, h35 n hn hsq, h321 n hn hsq⟩

open ZInQ.Contrib.TYZDecomp in
/-- **Main glue**: the split leaves give `TYZGenusPackage`. -/
theorem genusPackage_of_split (Hn : ℕ → IntermediateField ℚ Qbar) (Z : ℕ → PtA)
    (hI : IContained Hn) (hN : NormalFields Hn) (h318 : Lemma318 Hn)
    (hZ : GenusPtsDefined Hn Z) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ Z)
    (h321 : Lemma321 Z) : TYZGenusPackage :=
  genusPackage_of_genusPointLeaf Hn hI hN h318 fun ℓ hℓ =>
    genusPointLeaf_of_split hZ (h35 ℓ hℓ) h321

open ZInQ.Contrib.TYZDecomp ZInQ.Literature in
/-- **The premise `TYZThm35ReadingA` from the split leaves** (with the three genuine TYZ leaves on
`𝓛` of `TYZDecomp.Leaves`, through Proposition N). -/
theorem tyzThm35ReadingA_of_split (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (Hn : ℕ → IntermediateField ℚ Qbar) (Z : ℕ → PtA)
    (hI : IContained Hn) (hN : NormalFields Hn) (h318 : Lemma318 Hn)
    (hZ : GenusPtsDefined Hn Z) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ Z)
    (h321 : Lemma321 Z) : TYZThm35ReadingA :=
  tyzThm35ReadingA_of_leaves h11 h1 h29 (genusPackage_of_split Hn Z hI hN h318 hZ h35 h321)

end Glue

end ZInQ.Contrib.TYZGenus.Package
