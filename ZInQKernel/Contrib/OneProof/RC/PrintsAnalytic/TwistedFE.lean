import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.HoffsteinLuo
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.TwistedFEKronecker
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.TwistedFEFricke

/-!
# Lane RC33: the twisted functional equation, PROVED

`twistedFunctionalEquation_proved : TwistedFunctionalEquation` (PROVED, standard axioms). This is
lane RC8's statement `PrintsAnalytic.TwistedFunctionalEquation` (`HoffsteinLuo.lean`), which the
structure `RCLeaves` (`RC/Wiring/Leaves.lean`) carried as the GLUE field `twistedFE` ("textbook:
Shimura, Atkin–Li; recalled as display (1) of Hoffstein–Luo, Math. Res. Lett. 4 (1997), p. 435,
and by Bump–Friedberg–Hoffstein, Invent. Math. 102 (1990), p. 543"; used without citation in the
manuscript at tex 2346, 8586–8588, 10025–10026, 10044–10047): for a newform `f` of trivial
nebentypus, weight `k > 0` and level `N`, and a fundamental discriminant `D` prime to `N`, the
twisted Dirichlet series `∑ χ_D(n) aₙ(f) n^{-s}` has an entire continuation `F` with
`Λ_{D²N}(k - s) = i^k ε_N(f) χ_D(-N) Λ_{D²N}(s)` on `0 < Re s < k`, where
`Λ_{D²N}(s) = (D²N)^{s/2} (2π)^{-s} Γ(s) F(s)` (`completedL`) and
`χ_D(-N) = sgn(D) χ_D(N)`. The statement is proved in every weight, not only in the weight `2`
used by its consumer (`twistedRootNumberCurve_of`, `Bridges.lean`, which applies it at `k = 2`).

**The proof** (the classical route of Shimura, *Introduction to the Arithmetic Theory of
Automorphic Functions*, Proposition 3.64; Atkin–Li, Invent. Math. 48 (1978), Theorem 3.1;
Iwaniec, *Topics in Classical Automorphic Forms*, §7.3 and Theorem 7.6 — locators UNVERIFIED, not
re-read here; the Lean proof does not depend on them):
1. `χ_D` is a primitive quadratic Dirichlet character modulo `|D|` with `χ_D(n) = (D/n)` for
   `n ≥ 1` and `χ_D(-1) = sgn D` (`TwistedFEKronecker.lean`, PROVED);
2. the twist `f ⊗ χ_D = |D|⁻¹ ∑_a 𝓕χ_D(a) f|[1, a/|D|; 0, 1]` (Tau Ceti's `CuspForm.twist`) is a
   cusp form on `Γ₁(D²N)` with `aₙ(f ⊗ χ_D) = χ_D(n) aₙ(f)`, and its Fricke relation is
   `(√(D²N))^{2-k} (f ⊗ χ_D)|W_{D²N} = ε_N(f) χ_D(-N) (f ⊗ χ_D)` (`TwistedFEFricke.lean`, PROVED,
   from `(√N)^{2-k} f|W_N = ε_N(f) f`, Tau Ceti's `Newform.frickeSign`);
3. the Mellin transform gives the functional equation of `Λ_{D²N}` for `F = L(f ⊗ χ_D, s)`
   (Mathlib's `ModularForm.L`), whose Dirichlet series is `∑ χ_D(n) aₙ(f) n^{-s}` on
   `Re s > k/2 + 1` (this file).
The reduction `twistedFE_of_char` isolates step 1: it proves the conclusion for any primitive
quadratic character modulo `|D|` with the values of `χ_D` at the positive integers and at `-1`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 HeckeRing.GL2 Complex CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace TwistedFE

/-- **The two completions agree on `Re s > 0`, for any cusp form** (PROVED): for a cusp form `g`
of positive weight on an arithmetic subgroup and a level `L ≥ 1`,
`L^{s/2} (2π)^{-s} Γ(s) L(g, s) = Λ_L(s, g)`, where `L(g, s)` is Mathlib's `ModularForm.L` and
`Λ_L` is Tau Ceti's `CuspForm.frickeCompletedL` (lane RC8's `completedL_L_eq_frickeCompletedL`
for an arbitrary cusp form; `Γ(s) ≠ 0` for `Re s > 0`). -/
theorem completedL_L_eq_frickeCompletedL_of_cuspForm {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {k : ℤ} (hk : 0 < k) (g : CuspForm Γ k) (L : ℕ) [NeZero L] {s : ℂ}
    (hs : 0 < s.re) :
    completedL L (ModularForm.L hk g) s =
      CuspForm.frickeCompletedL g (L.toPNat (NeZero.pos L)) s := by
  rw [CuspForm.frickeCompletedL_eq_cpow_mul_Λ g _ hk s,
    show ((L.toPNat (NeZero.pos L) : ℕ+) : ℕ) = L from rfl]
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hpi0 : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hpi : (2 * Real.pi : ℂ) ^ (-s) ≠ 0 :=
    fun h => hpi0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
  simp only [completedL, ModularForm.L, Complex.Gammaℂ_def]
  field_simp

/-- **A newform of trivial nebentypus is `Γ₀(N)`-invariant** (PROVED): `f|γ = f` for
`γ ∈ Γ₀(N)` (Tau Ceti's `mem_cuspFormCharSpace_iff_nebentypus` at the trivial character). -/
theorem slash_Gamma0_of_newform {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (hχ : f.χ = 1)
    (g : CongruenceSubgroup.Gamma0 N) :
    ⇑f.toCuspForm ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) = ⇑f.toCuspForm := by
  have h := (mem_cuspFormCharSpace_iff_nebentypus k f.χ f.toCuspForm).mp f.mem_charSpace g
  rw [h, hχ]
  simp

/-- **The Fricke relation of a newform** (PROVED): `(√N)^{2-k} f|W_N = ε_N(f) f` for a newform
of trivial nebentypus, `ε_N(f)` Tau Ceti's `Newform.frickeSign`. -/
theorem normalizer_smul_slash_frickeGL_of_newform {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (hχ : f.χ = 1) :
    TauCeti.atkinLehnerNormalizer N k • (⇑f.toCuspForm ∣[k] TauCeti.frickeGL ℝ N) =
      f.frickeSign hχ • ⇑f.toCuspForm := by
  have h := congrArg DFunLike.coe (f.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ)
  rw [TauCeti.coe_normalizedFrickeOperatorCusp, FunLike.coe_smul] at h
  exact h

/-- **The twisted functional equation from a character** (PROVED). Let `f` be a newform of
trivial nebentypus, weight `k > 0`, level `N`, and `D ≠ 0` prime to `N`. If `χ` is a primitive
quadratic Dirichlet character modulo `|D|` with `χ(n) = (D/n)` for every `n ≥ 1` and
`χ(-1) = sgn D`, then `F = L(f ⊗ χ, s)` (Mathlib's `ModularForm.L` of Tau Ceti's twist, a cusp
form on `Γ₁(D²N)`) is an entire continuation of `∑ χ_D(n) aₙ(f) n^{-s}` from
`Re s > k/2 + 1`, and `Λ_{D²N}(k - s) = i^k ε_N(f) sgn(D) χ_D(N) Λ_{D²N}(s)` on
`0 < Re s < k`. The Dirichlet series: Tau Ceti's `CuspForm.LSeries_qExpansion_coeff_eq` (width
`1`) and `CuspForm.qExpansion_twist_coeff`; the functional equation:
`TwistedFE.twist_frickeCompletedL_sub`, transported by
`completedL_L_eq_frickeCompletedL_of_cuspForm` at `s` and at `k - s`. -/
theorem twistedFE_of_char {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (hχ : f.χ = 1)
    (hk : 0 < k) {D : ℤ} (hD0 : D ≠ 0) (hDN : IsCoprime D (N : ℤ))
    (χ : DirichletCharacter ℂ D.natAbs) (hprim : χ.IsPrimitive) (hquad : χ.IsQuadratic)
    (hval : ∀ n : ℕ, n ≠ 0 → χ n = (kronecker D n : ℂ))
    (hneg : χ (-1) = (kroneckerNegOne D : ℂ)) :
    ∃ F : ℂ → ℂ, IsEntireContinuation (twistCoeff (nfCoeff f) D) ((k : ℝ) / 2 + 1) F ∧
      ∀ s : ℂ, 0 < s.re → s.re < k →
        completedL (D.natAbs ^ 2 * N) F (k - s) =
          newformSign f hχ * ((kroneckerNegOne D * kronecker D N : ℤ) : ℂ) *
            completedL (D.natAbs ^ 2 * N) F s := by
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD0⟩
  have hNM : N.Coprime D.natAbs := by
    have h := Int.isCoprime_iff_gcd_eq_one.mp hDN
    exact Nat.Coprime.symm h
  have hNL : N * D.natAbs ∣ D.natAbs ^ 2 * N := ⟨D.natAbs, by ring⟩
  have hML : D.natAbs * D.natAbs ∣ D.natAbs ^ 2 * N := ⟨N, by ring⟩
  set g := CuspForm.twist (⇑χ) hNL hML f.toCuspForm with hg
  refine ⟨ModularForm.L hk g, ⟨CuspForm.differentiable_L hk g, fun s hs => ?_⟩, ?_⟩
  · have h := CuspForm.LSeries_qExpansion_coeff_eq hk g hs
    rw [strictWidthInfty_Gamma1, Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    rw [← h]
    refine LSeries_congr (fun {n} hn => ?_) s
    rw [CuspForm.qExpansion_twist_coeff, hval n hn]
    rfl
  · intro s hs0 hsk
    have hks : 0 < ((k : ℂ) - s).re := by
      rw [Complex.sub_re, Complex.intCast_re]
      linarith
    rw [completedL_L_eq_frickeCompletedL_of_cuspForm hk g _ hks,
      completedL_L_eq_frickeCompletedL_of_cuspForm hk g _ hs0]
    rw [twist_frickeCompletedL_sub hprim hquad hNM hNL hML f.toCuspForm
      (slash_Gamma0_of_newform f hχ) (normalizer_smul_slash_frickeGL_of_newform f hχ) s]
    have hχN : χ (-(N : ZMod D.natAbs)) = ((kroneckerNegOne D * kronecker D N : ℤ) : ℂ) := by
      rw [neg_eq_neg_one_mul, map_mul, hneg, hval N (NeZero.ne N)]
      push_cast
      ring
    rw [hχN, newformSign]
    ring

end TwistedFE

/-- **The twisted functional equation** (PROVED; formerly the GLUE field `RCLeaves.twistedFE`;
display (1) of Hoffstein–Luo, Math. Res. Lett. 4 (1997), p. 435, and Bump–Friedberg–Hoffstein,
Invent. Math. 102 (1990), p. 543; used at tex 2346, 8586–8588, 10025–10026, 10044–10047). For a
newform `f` of trivial nebentypus, weight `k > 0`, level `N`, sign `ε = newformSign f`, and a
fundamental discriminant `D` prime to `N`, the twisted series `∑ χ_D(n) aₙ(f) n^{-s}` has an
entire continuation `F` with `Λ_{D²N}(k - s) = ε χ_D(-N) Λ_{D²N}(s)` on `0 < Re s < k`. The
character is `TwistedFE.kroneckerChar` (primitive, quadratic, `χ_D(n) = (D/n)`,
`χ_D(-1) = sgn D`) and the rest is `TwistedFE.twistedFE_of_char`. -/
theorem twistedFunctionalEquation_proved : TwistedFunctionalEquation := by
  intro N _ k f hχ hk D hD hDN
  exact TwistedFE.twistedFE_of_char f hχ hk
    (Int.natAbs_pos.mp (TwistedFE.natAbs_pos_of_isFundamentalDiscriminant hD)) hDN
    (TwistedFE.kroneckerChar hD) (TwistedFE.kroneckerChar_isPrimitive hD)
    (TwistedFE.kroneckerChar_isQuadratic hD) (fun n hn => TwistedFE.kroneckerChar_natCast hD hn)
    (TwistedFE.kroneckerChar_neg_one hD)

end ZInQ.Manuscript.RC.PrintsAnalytic
