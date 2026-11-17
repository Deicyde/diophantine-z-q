import ZInQKernel.Contrib.OneProof.BFHKronecker
import ZInQKernel.Contrib.OneProof.BFHPrinted.Gamma0Newform

/-!
# Bump–Friedberg–Hoffstein 1990, clause (ii), over the classical newform on `Γ₀(N)`

Task bfh-gamma0 (report `docs/research/bfh-gamma0.md`). bfh-kronecker's leaf
`ZInQ.BFHPrinted.BFHClauseIIKronecker` states clause (ii) of the opening theorem of
Bump–Friedberg–Hoffstein (Invent. Math. 102 (1990) 543–618) over Tau Ceti's newform on `Γ₁(N)`
with trivial nebentypus (`f : Newform N 2`, `f.χ = 1`). BFH's `f` is a newform on `Γ₀(N)`. This
file states the clause over the classical newform on `Γ₀(N)` (`BFHClauseIIGamma0`, over
`IsGamma0Newform` of `BFHPrinted/Gamma0Newform.lean`) and proves:

* `bfhClauseIIKronecker_of_bfhClauseIIGamma0`: the leaf over `Γ₀(N)` implies bfh-kronecker's leaf.
  The one identification needed, that `f.toCuspFormGamma0 hχ` is a classical `Γ₀(N)`-newform with
  the same Fourier coefficients, is `isGamma0Newform_toCuspFormGamma0` and
  `coeffGamma0_toCuspFormGamma0`;
* `bfhClauseIIGamma0_iff : BFHClauseIIGamma0 ↔ BFHClauseIIKronecker` (the converse through
  `IsGamma0Newform.toNewform`), so the leaf over `Γ₀(N)` is no stronger than bfh-kronecker's, and
  `bfhClauseIIGamma0_iff_bfhClauseII` (equivalent to bfh-leaf's);
* `frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0`: the assembly with the leaf in place of
  `FHNonvanishing` (the leaf used once, at `B = 4`, through bfh-kronecker's
  `exists_heegnerDisc_of_bfhClauseIIKronecker`);
* `fhNonvanishing_of_bfhClauseIIGamma0`: `FHNonvanishing` for every `B` from the leaf (the drop-in
  replacement of `GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH` in `ZInQ.OneProof.frozenTarget`).
-/

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup HeckeRing.GL2 NumberField

namespace ZInQ.BFHPrinted

open ZInQ.GZDecomp ZInQ.GZFH ZInQ.FHPrinted

/-! ## The objects of the leaf, on `Γ₀(N)` -/

/-- **`ε` is the sign of the functional equation of `L(s, F)`** for a weight-2 cusp form `F` on
`Γ₀(N)`: the entire continuation `G` of `L(s, F) = ∑ aₙ(F) n^{−s}` (from `Re s > 2`) satisfies
`Λ_N(2 − s) = ε Λ_N(s)` on `0 < Re s < 2`, where `Λ_N(s) = N^{s/2} (2π)^{−s} Γ(s) G(s)`
(`ZInQ.Literature.completedL`). bfh-leaf's `IsFESign` with `F`'s coefficients. -/
def IsFESignGamma0 {N : ℕ} (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2) (ε : ℤ) : Prop :=
  ∃ G : ℂ → ℂ, IsEntireCont (coeffGamma0 F) 2 G ∧ ∀ s : ℂ, 0 < s.re → s.re < 2 →
    ZInQ.Literature.completedL N G (2 - s) = (ε : ℂ) * ZInQ.Literature.completedL N G s

/-- The coefficients `aₙ(F) (D / n)` of `L(s, F, χ_D)`, `χ_D(n) = (D / n)` the Kronecker symbol
(`kroneckerSym`). -/
noncomputable def kroneckerTwistCoeffGamma0 {N : ℕ} (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2)
    (D : ℤ) (n : ℕ) : ℂ :=
  coeffGamma0 F n * (kroneckerSym D n : ℂ)

/-- **`L(1, F, χ_D) ≠ 0`**: the entire continuation of `∑ aₙ(F) (D / n) n^{−s}` (from `Re s > 2`)
does not vanish at the centre `s = 1` (`= k/2` for the weight `k = 2`). -/
def KroneckerCentralValueNeZeroGamma0 {N : ℕ} (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2)
    (D : ℤ) : Prop :=
  ∀ G : ℂ → ℂ, IsEntireCont (kroneckerTwistCoeffGamma0 F D) 2 G → G 1 ≠ 0

/-! ## The leaf -/

/-- **Bump–Friedberg–Hoffstein 1990, opening theorem, clause (ii), at weight `k = 2`: the
classical newform on `Γ₀(N)`, `χ_D(n) = (D / n)` the Kronecker symbol.**

Printed statement (the statement-check read of D. Bump, S. Friedberg, J. Hoffstein, Invent. Math.
102 (1990), opening theorem, pp. 543–544; paraphrase): let `f` be a newform of even weight `k` and
trivial character on `Γ₀(N)`, `ε` the sign of the functional equation of `L(s, f)`, and `S` a
finite set of primes containing the primes dividing `N`. Then there is a fundamental
discriminant `D` of a quadratic field with `ε D > 0`, every `p ∈ S` split in `ℚ(√D)`, and
`L(k/2, f, χ_D) ≠ 0`, where `χ_D(n) = (D / n)` and `L(s, f, χ_D) = ∑ aₙ χ_D(n) n^{−s}` (centre
`s = k/2`). No CM exclusion, no level condition.

Here, the direct instance at `k = 2` (centre `s = 1`):
* `F : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2` with `IsGamma0Newform F` (a cusp form of weight 2
  on `Γ₀(N)` that is an eigenform of the Hecke operators `T_n`, `(n, N) = 1`, lies in the new
  subspace of `S_2(Γ₀(N))`, the Petersson complement of the `V_d S_2(Γ₀(M))`, `dM ∣ N`,
  `M ≠ N`, and has `a₁ = 1`); trivial character is built into `Γ₀(N)`;
* `IsFESignGamma0 F ε`: `ε` is the sign of the functional equation of the completed `L(s, F)` at
  level `N`;
* `S : Finset ℕ` of primes containing every prime dividing `N`;
* `Int.IsFundamentalDiscr D` (Mathlib) with `D ≠ 1`; `0 < ε * D`; `SplitsInQuadratic D S` (two
  distinct primes of `𝓞 K` above each `p ∈ S`, `K` a quadratic number field containing `√D`);
* `KroneckerCentralValueNeZeroGamma0 F D`: `L(1, F, χ_D) ≠ 0` with `χ_D(n) = (D / n)`
  (`kroneckerSym`, the Kronecker symbol).

Source: D. Bump, S. Friedberg, J. Hoffstein, *Nonvanishing theorems for L-functions of modular
forms and their derivatives*, Invent. Math. 102 (1990), 543–618, opening theorem (pp. 543–544),
clause (ii). -/
def BFHClauseIIGamma0 : Prop :=
  ∀ (N : ℕ) [NeZero N] (F : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2), IsGamma0Newform F →
  ∀ ε : ℤ, IsFESignGamma0 F ε →
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ∣ N → p ∈ S) →
    ∃ D : ℤ, Int.IsFundamentalDiscr D ∧ D ≠ 1 ∧ 0 < ε * D ∧ SplitsInQuadratic D S ∧
      KroneckerCentralValueNeZeroGamma0 F D

/-! ## From the newform on `Γ₁(N)` to the newform on `Γ₀(N)` -/

/-- The coefficients of `f.toCuspFormGamma0 hχ` are `GZDecomp.coeff f`. -/
theorem coeffGamma0_toCuspFormGamma0_eq_coeff {N : ℕ} [NeZero N] (f : Newform N 2)
    (hχ : f.χ = 1) : coeffGamma0 (f.toCuspFormGamma0 hχ) = coeff f :=
  funext fun n => coeffGamma0_toCuspFormGamma0 f hχ n

theorem isFESignGamma0_toCuspFormGamma0_iff {N : ℕ} [NeZero N] (f : Newform N 2) (hχ : f.χ = 1)
    (ε : ℤ) : IsFESignGamma0 (f.toCuspFormGamma0 hχ) ε ↔ IsFESign f ε := by
  rw [IsFESignGamma0, IsFESign, coeffGamma0_toCuspFormGamma0_eq_coeff]

theorem kroneckerCentralValueNeZeroGamma0_toCuspFormGamma0_iff {N : ℕ} [NeZero N]
    (f : Newform N 2) (hχ : f.χ = 1) (D : ℤ) :
    KroneckerCentralValueNeZeroGamma0 (f.toCuspFormGamma0 hχ) D ↔
      KroneckerCentralValueNeZero f D := by
  have h : kroneckerTwistCoeffGamma0 (f.toCuspFormGamma0 hχ) D = kroneckerTwistCoeff f D := by
    funext n
    rw [kroneckerTwistCoeffGamma0, kroneckerTwistCoeff, coeffGamma0_toCuspFormGamma0_eq_coeff]
  rw [KroneckerCentralValueNeZeroGamma0, KroneckerCentralValueNeZero, h]

/-- **The leaf over the classical `Γ₀(N)`-newform implies bfh-kronecker's leaf over Tau Ceti's
`Γ₁(N)`-newform with trivial nebentypus**: apply it to `f.toCuspFormGamma0 hχ`, a classical
newform on `Γ₀(N)` (`isGamma0Newform_toCuspFormGamma0`) with the same coefficients. -/
theorem bfhClauseIIKronecker_of_bfhClauseIIGamma0 (h : BFHClauseIIGamma0) :
    BFHClauseIIKronecker := by
  intro N _ f hχ ε hε S hSp hS
  obtain ⟨D, hfd, hD1, hsign, hsplit, hL⟩ :=
    h N (f.toCuspFormGamma0 hχ) (isGamma0Newform_toCuspFormGamma0 f hχ) ε
      ((isFESignGamma0_toCuspFormGamma0_iff f hχ ε).mpr hε) S hSp hS
  exact ⟨D, hfd, hD1, hsign, hsplit,
    (kroneckerCentralValueNeZeroGamma0_toCuspFormGamma0_iff f hχ D).mp hL⟩

/-! ## The converse: the two leaves are equivalent -/

/-- The coefficients of the Tau Ceti newform attached to a classical newform `F` are `F`'s. -/
theorem coeff_toNewform {N : ℕ} [NeZero N] {F : CuspForm ((Gamma0 N).map (mapGL ℝ)) 2}
    (hF : IsGamma0Newform F) : coeff hF.toNewform = coeffGamma0 F := by
  rw [← coeffGamma0_toCuspFormGamma0_eq_coeff hF.toNewform hF.toNewform_χ,
    hF.toCuspFormGamma0_toNewform]

/-- **bfh-kronecker's leaf implies the leaf over `Γ₀(N)`**: apply it to `hF.toNewform`, the
restriction of `F` to `Γ₁(N)`, a Tau Ceti newform of trivial nebentypus
(`restrict_mem_cuspFormsNew_of_isGamma0New`). -/
theorem bfhClauseIIGamma0_of_bfhClauseIIKronecker (h : BFHClauseIIKronecker) :
    BFHClauseIIGamma0 := by
  intro N _ F hF ε hε S hSp hS
  have hc := coeff_toNewform hF
  obtain ⟨D, hfd, hD1, hsign, hsplit, hL⟩ :=
    h N hF.toNewform hF.toNewform_χ ε (by rw [IsFESign, hc]; exact hε) S hSp hS
  refine ⟨D, hfd, hD1, hsign, hsplit, ?_⟩
  have hk : kroneckerTwistCoeffGamma0 F D = kroneckerTwistCoeff hF.toNewform D := by
    funext n
    rw [kroneckerTwistCoeffGamma0, kroneckerTwistCoeff, hc]
  rw [KroneckerCentralValueNeZeroGamma0, hk]
  exact hL

/-- **The leaf over the classical `Γ₀(N)`-newform is equivalent to bfh-kronecker's leaf.** -/
theorem bfhClauseIIGamma0_iff : BFHClauseIIGamma0 ↔ BFHClauseIIKronecker :=
  ⟨bfhClauseIIKronecker_of_bfhClauseIIGamma0, bfhClauseIIGamma0_of_bfhClauseIIKronecker⟩

/-- **…and to bfh-leaf's leaf** (`χ_D` from local components, `S ⊇` primes dividing `2N`). -/
theorem bfhClauseIIGamma0_iff_bfhClauseII : BFHClauseIIGamma0 ↔ BFHClauseII :=
  bfhClauseIIGamma0_iff.trans bfhClauseIIKronecker_iff

/-! ## The assembly -/

/-- **`GrossZagierCd` from the theta-newform leaf, BFH (ii) over `Γ₀(N)` and
Gross–Zagier–Heegner.** -/
theorem grossZagierCd_of_bfhClauseIIGamma0 (hL1 : HeckeThetaNewform) (hBFH : BFHClauseIIGamma0)
    (hL3 : GrossZagierHeegner) : GrossZagierCd :=
  grossZagierCd_of_bfhClauseIIKronecker hL1 (bfhClauseIIKronecker_of_bfhClauseIIGamma0 hBFH) hL3

/-- **Theorem 1.1 from `SixContactMin`, TYZ Theorem 3.5(2) in reading A, the theta-newform leaf,
BFH (ii) over the classical `Γ₀(N)`-newform, and Gross–Zagier–Heegner**:
`GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves` with `hL2 : FHNonvanishing`
replaced by `hBFH : BFHClauseIIGamma0`. -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhGamma0 (hH : SixContactMin)
    (hA : ZInQ.Literature.TYZThm35ReadingA) (hL1 : HeckeThetaNewform)
    (hBFH : BFHClauseIIGamma0) (hL3 : GrossZagierHeegner) : FrozenTarget :=
  frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker hH hA hL1
    (bfhClauseIIKronecker_of_bfhClauseIIGamma0 hBFH) hL3

/-- **`FHNonvanishing` (every bound `B`) from the leaf over `Γ₀(N)`**: the drop-in replacement of
`GZFH.fhNonvanishing_of_friedbergHoffsteinB_FE hFH` in `ZInQ.OneProof.frozenTarget`. -/
theorem fhNonvanishing_of_bfhClauseIIGamma0 (h : BFHClauseIIGamma0) : FHNonvanishing :=
  fhNonvanishing_of_bfhClauseIIKronecker (bfhClauseIIKronecker_of_bfhClauseIIGamma0 h)

end ZInQ.BFHPrinted
