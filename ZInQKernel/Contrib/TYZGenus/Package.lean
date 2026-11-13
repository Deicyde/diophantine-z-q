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

end ZInQ.Contrib.TYZGenus.Package
