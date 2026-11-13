import ZInQKernel.Contrib.TYZGenus.CM
import ZInQKernel.Contrib.TYZDecomp.Leaves
import ZInQKernel.Contrib.TYZGenus.RingClass

/-!
# cm-points: TYZ's genus-point package as genuine leaves plus glue

Task cm-points (2026-11-13). Report: `docs/research/cm-points.md`; log: `scratch/cm-points/log.md`.
Owner: cm-points. Imports `TYZGenus/CM.lean` (this task, which imports x0-32's `TYZGenus/X0.lean`)
and ring-class's `TYZGenus/RingClass.lean`. §5–§6 work with parameters `Hn` (TYZ's `ℍ'_n`) and `Z`
(TYZ's genus points); §7 instantiates `Hn := RingClass.HHprime`; §8 pins the class-5 genus points by
the Heegner points of `CM.lean`.

**Main theorem** (`tyzThm35ReadingA_of_cm`, §8): the three genuine `𝓛`-leaves of `TYZDecomp.Leaves`,
`TYZZnOverHprime` (`z_n ∈ A(H'_n)`), `HprimeNormal` (`H'_d/ℚ` normal), `Lemma318 HHprime` (TYZ Lemma
3.18) and the bundled `GenusPointLeafCM` (existential only over TYZ's choice of `Φ₀`, the class-7
genus points, `ε` and the lift `β'`) give `Literature.TYZThm35ReadingA`.

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
(`IContained`, proved for ring-class's `ℍ'_n`), and the genus-point statements (`GenusPtsDefined`,
`Thm35First`, `Lemma321`).

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

/-! **Soundness note (review 2026-11-13).** `GenusPtsDefined`, `Thm35First` and `Lemma321` take the
genus points `Z` as a *free parameter*. They are closed leaves only once `Z` is pinned by a
definition; asserted separately with their own `∃ Z` they would not be about the same points (e.g.
`Z = 0` satisfies `GenusPtsDefined`). The glue theorems that take them (`genusPackage_of_split`,
`genusPackage_of_ringClass`, …) are sound because one `Z` is shared, but the closed form used by the
main theorem is the bundled `GenusPointLeafCM` (§8). -/

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

/-! ## §7. With ring-class's `ℍ'_n` (`RingClass.HHprime`) -/

section RingClassBridge
open ZInQ.Contrib.TYZGenus.RingClass

theorem iQ_mem_Lni (n : ℕ) : iQ ∈ Lni n :=
  IntermediateField.subset_adjoin _ _ (Set.mem_union_left _ iQ_sq)

/-- **`i ∈ ℍ'_n`** for ring-class's `ℍ'_n` (proved). -/
theorem iContained_HHprime : IContained HHprime := fun n _ _ =>
  (le_sup_left : Lni n ≤ HHprime n) (iQ_mem_Lni n)

/-- `L_n(i)` is normal over `ℚ` (generated by full sets of roots of `X² + 1`, `X² − p`). -/
theorem normal_Lni (n : ℕ) : Normal ℚ (Lni n) := by
  rw [IntermediateField.normal_iff_forall_map_le]
  intro σ
  rw [Lni, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  apply IntermediateField.subset_adjoin
  rcases hx with hx | ⟨p, hp, hx⟩
  · left
    show σ x ^ 2 = -1
    rw [← map_pow, hx, map_neg, map_one]
  · right
    refine ⟨p, hp, ?_⟩
    rw [← map_pow, hx, map_natCast]

/-- **Reduction of F5 for ring-class's `ℍ'_n`**: if every `H'_d` (`d ≡ 5 (mod 8)` squarefree) is
normal over `ℚ`, then `NormalFields HHprime`. -/
theorem normalFields_HHprime
    (hH : ∀ d : ℕ, d % 8 = 5 → Squarefree d → Normal ℚ (Hprimebar d)) :
    NormalFields HHprime := by
  intro n _ hsq
  have h1 : Normal ℚ (Lni n) := normal_Lni n
  have e : (⨆ d₀ ∈ n.divisors.filter (fun d => d % 8 = 5), Hprimebar d₀ :
      IntermediateField ℚ Qbar) =
      ⨆ d : (n.divisors.filter (fun d => d % 8 = 5) : Set ℕ), Hprimebar d := iSup_subtype'
  have h2 : ∀ d : (n.divisors.filter (fun d => d % 8 = 5) : Set ℕ), Normal ℚ (Hprimebar d) := by
    rintro ⟨d₀, hd⟩
    obtain ⟨hdn, hd5⟩ := Finset.mem_filter.mp hd
    exact hH d₀ hd5 (hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors hdn))
  have h3 := IntermediateField.normal_iSup (F := ℚ) (K := Qbar) _ (h := h2)
  rw [← e] at h3
  unfold HHprime
  exact IntermediateField.normal_sup (F := ℚ) (K := Qbar) (Lni n) _

theorem Hprimebar_le_HHprime {n e : ℕ} (he : e ∈ n.divisors) (he5 : e % 8 = 5) :
    Hprimebar e ≤ HHprime n :=
  le_sup_of_le_right (le_iSup₂_of_le (f := fun d₀ (_ : d₀ ∈ n.divisors.filter (fun d => d % 8 = 5)) =>
    Hprimebar d₀) e (Finset.mem_filter.mpr ⟨he, he5⟩) le_rfl)

/-- A genus-point sum `Σ_{t ∈ Φ} t(z_e)` of a point `z_e ∈ A(H'_e)` lies in `A(ℍ'_n)` for `e ∣ n`,
`e ≡ 5 (mod 8)`, if `H'_e/ℚ` is normal (whatever the finite set `Φ` of automorphisms). -/
theorem genusSum_mem_HHprime {n e : ℕ} (he : e ∈ n.divisors) (he5 : e % 8 = 5)
    (hN : Normal ℚ (Hprimebar e)) (Φ : Finset GalQ) {z : PtA} (hz : z ∈ ptsOver (Hprimebar e)) :
    genusSum Φ z ∈ ptsOver (HHprime n) :=
  genusSum_mem (fun t _ x hx => Hprimebar_le_HHprime he he5
    ((IntermediateField.normal_iff_forall_map_le.mp hN) t.toAlgHom ⟨x, hx, rfl⟩)) hz

/-- **Leaf RC-F5'** (normality of `H'_d`, for ring-class's `Hprimebar`): `H'_d/ℚ` is normal for
squarefree `d ≡ 5 (mod 8)`. TYZ Proposition 3.2(1) (L1253–1260: `H'_d` is the fixed field of
`σ_{1+2ϖ}` in `H_{d,4}`) with Cox, *Primes of the form x² + ny²*, Lemma 9.3 (ring class fields are
generalized dihedral over `ℚ`, so every subgroup of `Gal(H_{d,4}/K_d)` is normal in
`Gal(H_{d,4}/ℚ)`; UNVERIFIED number). Refereed. -/
def HprimeNormal : Prop := ∀ d : ℕ, d % 8 = 5 → Squarefree d → Normal ℚ (Hprimebar d)

open ZInQ.Contrib.TYZDecomp in
/-- **Main glue with ring-class's `ℍ'_n`**: `TYZGenusPackage` from the normality of the `H'_d`,
TYZ Lemma 3.18 for `ℍ'_n`, and the three genus-point leaves. -/
theorem genusPackage_of_ringClass (Z : ℕ → PtA) (hHp : HprimeNormal)
    (h318 : Lemma318 HHprime) (hZ : GenusPtsDefined HHprime Z)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ Z) (h321 : Lemma321 Z) : TYZGenusPackage :=
  genusPackage_of_split HHprime Z iContained_HHprime (normalFields_HHprime hHp) h318 hZ h35 h321

open ZInQ.Contrib.TYZDecomp in
/-- **The premise `TYZThm35ReadingA` from genuine leaves, with ring-class's `ℍ'_n`.** -/
theorem tyzThm35ReadingA_of_ringClass (h11 : TYZThm11Integral) (h1 : TYZLcalOne)
    (h29 : TYZLemma29Mod2) (Z : ℕ → PtA) (hHp : HprimeNormal)
    (h318 : Lemma318 HHprime) (hZ : GenusPtsDefined HHprime Z)
    (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ Z) (h321 : Lemma321 Z) :
    ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_leaves h11 h1 h29 (genusPackage_of_ringClass Z hHp h318 hZ h35 h321)

end RingClassBridge

/-! ## §8. TYZ's genus points through CM points; Shimura reciprocity in TYZ's form -/

section CMBridge
open ZInQ.Contrib.TYZGenus.RingClass TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
  ZInQ.RouteK.Rank5b

/-- `ρ ∈ Gal(ℚ̄/ℚ)` acts on `H_{d,4} ⊂ ℚ̄` as the Artin symbol of `c ∈ Pic(𝒪_{d,4})`
(through ring-class's embedding `embed d : K_dˢ → ℚ̄` and Tau Ceti's `ringClassArtinEquiv`). -/
def ActsAsArtin4 (ρ : GalQ) (d : ℕ) [NeZero d] (c : Pic (O4 d)) : Prop :=
  ∀ x : H4 d, ρ (embed d (x : SeparableClosure (QNeg d))) =
    embed d ((artin4 d c x : H4 d) : SeparableClosure (QNeg d))

/-- **Leaf CM-2-TYZ (field of definition of TYZ's Heegner point)**: for squarefree `n ≡ 5 (mod 8)`,
`f₀(P_n)` (the Heegner point of `[16(n+1), −8, 1]`, discriminant `−64n`, order `𝒪_{n,4} = ℤ[4√−n]`)
is defined over the ring class field `H_{n,4}`. The instance `H(−64n) = H_{n,4}` of
`CM.CMFieldOfDefinition` (`cmFieldTYZ_of`). Sources: main theorem of complex multiplication /
Shimura reciprocity for `X₀(N)` (Shimura 1971 Thm. 5.4 and Ch. 6; Gross 1984 §3; UNVERIFIED
numbers); TYZ Proposition 3.2 (L1253–1260). Refereed. -/
def CMFieldOfDefinitionTYZ : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → tyzHeegnerPt n ∈ ptsOver (H4bar n)

theorem cmFieldTYZ_of {H : ℤ → IntermediateField ℚ Qbar} (h : CMFieldOfDefinition H)
    (hH : ∀ n : ℕ, n % 8 = 5 → Squarefree n → H (-64 * n) ≤ H4bar n) : CMFieldOfDefinitionTYZ := by
  intro n hn hsq
  have h1 := h (-64 * n) (tyzForm n hn)
  simp only [tyzHeegnerPt, hn, ↓reduceDIte]
  rw [mem_ptsOver_iff] at h1 ⊢
  revert h1
  rcases heegnerPt (tyzForm n hn) with _ | ⟨x, y, _⟩
  · intro _; trivial
  · intro h1; exact ⟨hH n hn hsq h1.1, hH n hn hsq h1.2⟩

/-- **Leaf TYZ-3.6 (Shimura reciprocity in TYZ's form, Corollary 3.9 / Theorem 3.6)**: `σ_{1+2ϖ}`
fixes `z_n = f_n(P_n)`: every `ρ` acting on `H_{n,4}` as the Artin symbol of
`sigmaClass n` fixes `z_n`. TYZ Corollary 3.9 (`π(1+2ϖ)f_n = f_n`) with Shimura reciprocity on
`P_n = [h, 1]` (rv-tyz-inputs §1.5, L1433–1683, re-derived there); refereed. Here `z_n` is
`CM.tyzZn n = (1 − [i]) f₀(P_n)` (the translation of TYZ's `f_n(P_n)` to `X₀(32)` of
`tyz-t1.md` §3.1, AI-derived and checked numerically there). -/
def TYZSigmaFixesZn : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n (sigmaClass n) → galPt ρ (tyzZn n) = tyzZn n

/-- **Leaf TYZ-3.2 (the field of `z_n`)**: `z_n ∈ A(H'_n)`. Consequence of `CMFieldOfDefinitionTYZ`
(`z_n ∈ A(H_{n,4})`, since `i ∈ H_{n,4}`) and `TYZSigmaFixesZn` (`H'_n` is the fixed field of
`σ_{1+2ϖ}`, TYZ Proposition 3.2(1)); stated as one leaf (the Galois-theoretic deduction through
ring-class's embedding is not formalized). Refereed (TYZ L1253–1260, Theorem 3.6). -/
def TYZZnOverHprime : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → tyzZn n ∈ ptsOver (Hprimebar n)

theorem Lni_mono {e n : ℕ} (h : e ∣ n) (hn : n ≠ 0) : Lni e ≤ Lni n := by
  apply IntermediateField.adjoin.mono
  rintro x (hx | ⟨p, hp, hx⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨p, Nat.primeFactors_mono h hn hp, hx⟩

theorem Lni_le_HHprime (n : ℕ) : Lni n ≤ HHprime n := le_sup_left

/-- **Glue: TYZ's class-5 genus points lie in `A(ℍ'_n)`**, for *every* choice of the finite set `Φ`
of automorphisms (TYZ's `Φ₀`), from `z_e ∈ A(H'_e)` and normality of `H'_e`. -/
theorem tyzGenusSum_mem (hz : TYZZnOverHprime) (hN : HprimeNormal) {n e : ℕ} (hsq : Squarefree n)
    (he : e ∈ n.divisors) (he5 : e % 8 = 5) (Φ : Finset GalQ) :
    genusSum Φ (tyzZn e) ∈ ptsOver (HHprime n) := by
  have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
  exact genusSum_mem_HHprime he he5 (hN e he5 hse) Φ (hz e he5 hse)

/-- **Glue for `GenusPtsDefined`**: if `Z` is TYZ's genus-point sum on class 5 (any `Φ e`) and
`Z(e) ∈ A(L_e)` on class 7 (TYZ L2558), then `GenusPtsDefined HHprime Z`. -/
theorem genusPtsDefined_of (hz : TYZZnOverHprime) (hN : HprimeNormal) (Φ : ℕ → Finset GalQ)
    (Z : ℕ → PtA) (h5 : ∀ e, e % 8 = 5 → Z e = genusSum (Φ e) (tyzZn e))
    (h7 : ∀ e, e % 8 = 7 → Squarefree e → Z e ∈ ptsOver (Lni e)) : GenusPtsDefined HHprime Z := by
  intro n hn hsq e he hec
  rcases hec with he5 | he7
  · rw [h5 e he5]; exact tyzGenusSum_mem hz hN hsq he he5 (Φ e)
  · have hn0 : n ≠ 0 := by omega
    have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
    have hle : Lni e ≤ HHprime n := (Lni_mono (Nat.dvd_of_mem_divisors he) hn0).trans (Lni_le_HHprime n)
    have := h7 e he7 hse
    rw [mem_ptsOver_iff] at this ⊢
    revert this
    rcases Z e with _ | ⟨x, y, _⟩
    · intro _; trivial
    · intro h; exact ⟨hle h.1, hle h.2⟩

/-- TYZ's genus points with the class-5 ones pinned by CM: `Z(e) = Σ_{t ∈ Φ e} t(z_e)` for
`e ≡ 5 (mod 8)` (TYZ L1318, `z_e = CM.tyzZn e`), and `Z7 e` otherwise (class 7: TYZ's `f_e(P_e)` for
`e ≡ 7` is not pinned here, see `docs/research/cm-points.md` §4). -/
def tyzGenusPt (Φ : ℕ → Finset GalQ) (Z7 : ℕ → PtA) (e : ℕ) : PtA :=
  if e % 8 = 5 then genusSum (Φ e) (tyzZn e) else Z7 e

/-- **The remaining bundled leaf, CM form**: for each squarefree `n ≡ 5 (mod 8)` there are a choice
`Φ` of TYZ's sets `Φ₀` (TYZ: any choice works, L2547–2554), class-7 genus points `Z7 e ∈ A(L_e)`
(TYZ L2558), `ε` and a lifting `β'` such that Theorem 3.3/3.5 (first assertion) and Lemma 3.21(1),
(4) hold for the genus points `tyzGenusPt Φ Z7`, whose class-5 values are pinned by the Heegner
points of `CM.lean`. Strictly finer than `GenusPointLeaf` (and than `TYZGenusPackage`). -/
def GenusPointLeafCM (ℓ : ℕ → ℤ) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∃ (Φ : ℕ → Finset GalQ) (Z7 : ℕ → PtA),
    (∀ e ∈ n.divisors, e % 8 = 7 → Z7 e ∈ ptsOver (Lni e)) ∧
    (∃ ε : ℕ → ℕ → GaussianInt, EpsClasses n ε ∧
      (ℓ n = 0 → IsOfFinAddOrder (Pseq ℓ ε (tyzGenusPt Φ Z7) n))) ∧
    (∃ σ : GalQ, IsBetaOneLift σ ∧
      (∀ e ∈ n.divisors, e % 8 = 5 → ∃ k : ℤ,
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2) ∧
      (∀ e ∈ n.divisors, e % 8 = 7 →
        galPt σ (tyzGenusPt Φ Z7 e) + tyzGenusPt Φ Z7 e = (gNat e : ℤ) • tauG 1))

open ZInQ.Contrib.TYZDecomp in
/-- **Glue, CM form**: `z_e ∈ A(H'_e)`, normality of the `H'_d`, Lemma 3.18 for `ℍ'_n` and the CM-form
bundled leaf give `TYZGenusPackage`. -/
theorem genusPackage_of_cm (hz : TYZZnOverHprime) (hN : HprimeNormal) (h318 : Lemma318 HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : TYZGenusPackage := by
  refine genusPackage_of_genusPointLeaf HHprime iContained_HHprime (normalFields_HHprime hN) h318
    fun ℓ hℓ n hn hsq => ?_
  obtain ⟨Φ, Z7, h7, hP, hβ⟩ := hG ℓ hℓ n hn hsq
  refine ⟨tyzGenusPt Φ Z7, fun e he hec => ?_, hP, hβ⟩
  rcases hec with he5 | he7
  · simp only [tyzGenusPt, he5, ↓reduceIte]
    exact tyzGenusSum_mem hz hN hsq he he5 (Φ e)
  · have hn0 : n ≠ 0 := by omega
    have hle : Lni e ≤ HHprime n :=
      (Lni_mono (Nat.dvd_of_mem_divisors he) hn0).trans (Lni_le_HHprime n)
    have h75 : ¬ e % 8 = 5 := by omega
    simp only [tyzGenusPt, h75, ↓reduceIte]
    have := h7 e he he7
    rw [mem_ptsOver_iff] at this ⊢
    revert this
    rcases Z7 e with _ | ⟨x, y, _⟩
    · intro _; trivial
    · intro h; exact ⟨hle h.1, hle h.2⟩

open ZInQ.Contrib.TYZDecomp in
/-- **The premise `TYZThm35ReadingA` from the CM-form leaves.** -/
theorem tyzThm35ReadingA_of_cm (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hz : TYZZnOverHprime) (hN : HprimeNormal) (h318 : Lemma318 HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_leaves h11 h1 h29 (genusPackage_of_cm hz hN h318 hG)

end CMBridge

/-! ## §9. `τ(½ℤ[i]) = A[(1+i)³]`: Lemma 3.18 in TYZ's literal form -/

section Literal318
open WeierstrassCurve.Affine

theorem iPt_ptT_eq : iPt ptT = .some (-2) (-4 * iQ) (by
    have := nonsingular_iPt nonsingular_T
    convert this using 1; ring) := by
  rw [ptT, iPt_some, Point.some.injEq]; constructor <;> ring

theorem nonsingular_m2iQ : curveAbar.toAffine.Nonsingular (-2 * iQ) 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff']
  simp only [curveAbar_a₁, curveAbar_a₂, curveAbar_a₃, curveAbar_a₄, curveAbar_a₆]
  have hi := iQ_sq
  refine ⟨by linear_combination (8 * iQ) * hi, Or.inl ?_⟩
  intro h
  have : (8 : Qbar) = 0 := by linear_combination h + 12 * hi
  norm_num at this

/-- `τ((1+i)/2) = T + [i]T = (−2i, 0)`. -/
theorem ptT_add_iPt_ptT : ptT + iPt ptT = .some (-2 * iQ) 0 nonsingular_m2iQ := by
  rw [iPt_ptT_eq, ptT]
  have hx : (2 : Qbar) ≠ -2 := by norm_num
  rw [Point.add_of_X_ne hx, Point.some.injEq]
  have hi := iQ_sq
  have hs : curveAbar.toAffine.slope 2 (-2) (-4) (-4 * iQ) = -1 + iQ := by
    rw [slope_of_X_ne hx]
    field_simp
    ring
  simp only [addX, addY, negAddY, negY, hs, curveAbar_a₁, curveAbar_a₂, curveAbar_a₃]
  constructor
  · linear_combination hi
  · linear_combination (3 - iQ) * hi

theorem iPt_some_m2iQ : iPt (.some (-2 * iQ) 0 nonsingular_m2iQ) =
    .some (2 * iQ) 0 (by
      have := nonsingular_iPt nonsingular_m2iQ
      convert this using 1 <;> ring) := by
  rw [iPt_some, Point.some.injEq]; constructor <;> ring

/-- **The eight points of `A[(1+i)³]` (x0-32's `X0.IsTorsI3`) are values of the pinned `τ`.** -/
theorem isTorsI3_mem_range (P : PtA) (h : X0.IsTorsI3 P) : ∃ y : GaussianInt, tauG y = P := by
  rcases P with _ | ⟨x, y, hP⟩
  · exact ⟨0, map_zero tauG⟩
  simp only [X0.IsTorsI3, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩
  · exact ⟨⟨2, 0⟩, by rw [tauG_mk, two_zsmul_ptT, zero_zsmul, add_zero]; rfl⟩
  · exact ⟨⟨-1, 0⟩, by rw [tauG_mk, neg_one_zsmul, zero_zsmul, add_zero, neg_ptT]⟩
  · exact ⟨⟨1, 0⟩, by rw [tauG_mk, one_zsmul, zero_zsmul, add_zero]; rfl⟩
  · refine ⟨⟨0, -1⟩, ?_⟩
    rw [tauG_mk, neg_one_zsmul, zero_zsmul, zero_add, iPt_ptT_eq, Point.neg_some, Point.some.injEq]
    simp only [negY, curveAbar_a₁, curveAbar_a₃]
    exact ⟨trivial, by ring⟩
  · exact ⟨⟨0, 1⟩, by rw [tauG_mk, one_zsmul, zero_zsmul, zero_add, iPt_ptT_eq]⟩
  · refine ⟨⟨1, -1⟩, ?_⟩
    have e : ptT - iPt ptT = -iPt (ptT + iPt ptT) := by rw [iPt_add, iPt_iPt]; abel
    rw [tauG_mk, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, e, ptT_add_iPt_ptT, iPt_some_m2iQ,
      Point.neg_some, Point.some.injEq]
    simp only [negY, curveAbar_a₁, curveAbar_a₃]
    exact ⟨trivial, by ring⟩
  · exact ⟨⟨1, 1⟩, by rw [tauG_mk, one_zsmul, one_zsmul, ptT_add_iPt_ptT]⟩

theorem gi_smul (P : PtA) : (ZInQ.PropN.gi : GaussianInt) • P = iPt P := by
  have h1 : (ZInQ.PropN.gi).re = 0 := rfl
  have h2 : (ZInQ.PropN.gi).im = 1 := rfl
  rw [gsmul_def, h1, h2, zero_zsmul, one_zsmul, zero_add]

/-- `2(P + [i]P) = (2 + 2i)•P`. -/
theorem two_nsmul_add_iPt (P : PtA) : 2 • (P + iPt P) = (ZInQ.PropN.twoTwoI : GaussianInt) • P := by
  rw [gsmul_def]
  show 2 • (P + iPt P) = (2 : ℤ) • P + (2 : ℤ) • iPt P
  rw [two_nsmul, two_zsmul, two_zsmul]; abel

/-- **Leaf TYZ-3.18, literal form**: for squarefree `n ≡ 5 (mod 8)`, `A(ℍ'_n)_tors ⊆ A[(1+i)³]`,
i.e. every torsion point `P` of `A(ℍ'_n)` satisfies `2(P + [i]P) = 0`. TYZ Lemma 3.18 (L2230–2232),
literally (no `τ`); refereed. Equivalent to `Lemma318` (`lemma318_iff_literal`). -/
def Lemma318Literal (Hn : ℕ → IntermediateField ℚ Qbar) : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n →
    ∀ P ∈ ptsOver (Hn n), IsOfFinAddOrder P → 2 • (P + iPt P) = 0

/-- **`Lemma318` (with the pinned `τ`) is TYZ's literal Lemma 3.18**: `τ(½ℤ[i]) = A[(1+i)³]`, by
x0-32's explicit list `X0.two_nsmul_add_iPt_eq_zero_iff` and `tauG_eq_zero`. So the leaf does not
depend on TYZ's fact (1) about `τ`. -/
theorem lemma318_iff_literal (Hn : ℕ → IntermediateField ℚ Qbar) :
    Lemma318 Hn ↔ Lemma318Literal Hn := by
  constructor
  · intro h n hn hsq P hP ht
    obtain ⟨y, rfl⟩ := h n hn hsq P hP ht
    rw [two_nsmul_add_iPt, tauG_apply, smul_smul, ← tauG_apply, tauG_eq_zero]
    exact Dvd.intro y rfl
  · intro h n hn hsq P hP ht
    exact isTorsI3_mem_range P ((X0.two_nsmul_add_iPt_eq_zero_iff P).mp (h n hn hsq P hP ht))

open ZInQ.Contrib.TYZDecomp ZInQ.Contrib.TYZGenus.RingClass in
/-- **Main theorem, literal Lemma 3.18**: as `tyzThm35ReadingA_of_cm`, with TYZ Lemma 3.18 in its
literal form `A(ℍ'_n)_tors ⊆ A[(1+i)³]`. -/
theorem tyzThm35ReadingA_of_cm' (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hz : TYZZnOverHprime) (hN : HprimeNormal) (h318 : Lemma318Literal HHprime)
    (hG : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → GenusPointLeafCM ℓ) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_cm h11 h1 h29 hz hN ((lemma318_iff_literal HHprime).mpr h318) hG

end Literal318

end ZInQ.Contrib.TYZGenus.Package
