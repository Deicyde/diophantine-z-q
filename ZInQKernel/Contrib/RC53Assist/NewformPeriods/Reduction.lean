import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Glue
import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Transport

/-!
# `NewformPeriodsRational` from Shimura 1973, Faltings 1983 and three named translation steps

**Main theorem** (`newformPeriodsRational_of_prints`, PROVED):

```
Shimura1973Thm1RationalGamma0 → Faltings1983Kor2EllipticQ →
  NewformOfModularCurveGlue → ParametrizationPeriodsGlue → IsogenyLatticeGlue →
    NewformPeriodsRational
```

with `NewformPeriodsRational` the unchanged target
`ZInQ.Contrib.CloudB3RC53.ModularWeil.NewformPeriodsRational`. The proof, for an elliptic `E/ℚ`,
the cusp form `f` on `Γ₀(newformLevel E)` with the coefficients of `L(E, s)`, and a period
lattice `Lat` of `E`:

1. (PROVED, `Transport.lean`) If `newformLevel E = 0`, every period vanishes and `c = 1` works.
   Otherwise `E` is modular (`IsModular`), and it suffices to prove `SomeLevelPeriodsRational`.
2. (G0) A normalized full Hecke eigenform `g` on `Γ₀(M)` with `a_n(g) = E.LFunction n`; its
   coefficients `b n` are rational.
3. (PRINT, Shimura) An elliptic curve `A/ℚ`, a nonconstant point `(x, y)` of `A` over
   `ℚ(j, j_M)`, `c ∈ ℂ` with `θx = c · ĝ · (2y + a₁x + a₃)`, and `A.LFunction p = b p` off a finite
   set of primes.
4. (PROVED, `ne_zero_of_pullbackIsMultiple`, `exists_rat_eq_of_pullbackIsMultiple`) `c` is nonzero
   and rational.
5. (G1) `c · Π_M(g) ⊆ Λ_A` for a period lattice of `A` (one exists: `exists_isLatticeOf`).
6. (PRINT, Faltings) `A.LFunction p = E.LFunction p` off a finite set, so there is an isogeny
   `A → E` over `ℚ`.
7. (G2) `s · Λ_A ⊆ Lat` with `s ∈ ℚ^×`; hence `(s c) · Π_M(g) ⊆ Lat`.
8. (PROVED, `newformPeriodsRational_of_someLevel`) `f = g` on `ℍ` (equal `q`-expansions), and with
   `d = #SL(2, ℤ/Mℤ)`, `(d s c) · Π_N(f) ⊆ Lat`.

The order of quantifiers is the target's: the rational scalar is chosen after `E`, `f` and `Lat`,
and before `γ` and `τ`.

`modularToWeakWeil_of_prints` composes with the proved assembly
`ModularWeil.modularToWeakWeil_of_newformPeriodsRational`.
-/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.NewformPeriods

open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.ModularWeil
open ZInQ.Manuscript.PoleS12
open CongruenceSubgroup UpperHalfPlane

/-- **The some-level period statement from the two prints and the three named steps** (PROVED). -/
theorem someLevelPeriodsRational_of_prints
    (hS : Shimura1973Thm1RationalGamma0) (hF : Faltings1983Kor2EllipticQ)
    (h0 : NewformOfModularCurveGlue) (h1 : ParametrizationPeriodsGlue)
    (h2 : IsogenyLatticeGlue) : SomeLevelPeriodsRational := by
  intro E hE hmod
  obtain ⟨M, hM, g, heig, hcoef⟩ := h0 E hE hmod
  -- the rational coefficients of `g`
  set b : ℕ → ℚ := fun n => if n = 0 then 0 else ((E.LFunction n : ℤ) : ℚ) with hbdef
  have hb : ∀ n : ℕ, (qExpansion 1 g).coeff n = (b n : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [CuspFormClass.qExpansion_coeff_zero g one_pos (one_mem_strictPeriods_Gamma0 M)]
      simp [hbdef]
    · rw [hcoef n hn]
      simp [hbdef, hn.ne']
  have hb1 : b 1 = 1 := by
    have h := heig.1
    rw [hb 1] at h
    exact_mod_cast h
  have hgb : qExpansion 1 g = (PowerSeries.mk b).map (algebraMap ℚ ℂ) := by
    ext n
    simp [hb n]
  -- Shimura's quotient, in coordinates
  obtain ⟨A, hA, x, y, hpt, ⟨c, hpull⟩, S, hSp⟩ := hS M g heig b hb
  have hc0 : c ≠ 0 := ne_zero_of_pullbackIsMultiple hpt.2.2.2 hpull
  -- the pull-back scalar is rational
  have hpull' : PullbackIsMultiple A x y ((PowerSeries.mk b).map (algebraMap ℚ ℂ)) c := by
    rw [← hgb]
    exact hpull
  obtain ⟨r, hr⟩ := exists_rat_eq_of_pullbackIsMultiple hpt.2.2.2 hb1 hpull'
  -- periods of `g` in a lattice of `A`
  have : A.IsElliptic := hA
  obtain ⟨LatA, hLatA⟩ := exists_isLatticeOf A
  have hscaleA : IsParamScale M g LatA c := h1 M g A hA x y hpt c hc0 hpull LatA hLatA
  -- Faltings: `A` is isogenous to `E`
  have hiso : Nonempty (TauCeti.Isogeny A.toAffine E.toAffine) := by
    refine hF A E hA hE ⟨S, fun p hp hpS => ?_⟩
    have h := hSp p hp hpS
    simp only [hbdef, hp.ne_zero, ite_false] at h
    exact_mod_cast h
  refine ⟨M, Nat.pos_of_ne_zero (NeZero.ne M), g, hcoef, fun Lat hLat => ?_⟩
  obtain ⟨s, hs0, hs⟩ := h2 A E hA hE hiso LatA Lat hLatA hLat
  have hr0 : r ≠ 0 := by
    rintro rfl
    apply hc0
    rw [← hr]
    simp
  refine ⟨s * r, ?_, fun γ hγ τ => ?_⟩
  · exact_mod_cast mul_ne_zero hs0 hr0
  · have hmem := hscaleA.2 γ hγ τ
    rw [← hr] at hmem
    have h3 := hs _ hmem
    push_cast
    rw [mul_assoc]
    exact h3

/-- **`NewformPeriodsRational` from the printed leaves and the named translation steps**
(PROVED). Printed leaves: `Shimura1973Thm1RationalGamma0` (Shimura 1973, Theorem 1, p. 526, at
`Γ = Γ₀(M)`, `K = ℚ`, consequence form) and `Faltings1983Kor2EllipticQ` (Faltings 1983, §5,
Korollar 2, p. 361, iii ⇒ i for elliptic curves over `ℚ`). Named translation steps (GLUE):
`NewformOfModularCurveGlue`, `ParametrizationPeriodsGlue`, `IsogenyLatticeGlue`. -/
theorem newformPeriodsRational_of_prints
    (hS : Shimura1973Thm1RationalGamma0) (hF : Faltings1983Kor2EllipticQ)
    (h0 : NewformOfModularCurveGlue) (h1 : ParametrizationPeriodsGlue)
    (h2 : IsogenyLatticeGlue) : NewformPeriodsRational :=
  newformPeriodsRational_of_someLevel (someLevelPeriodsRational_of_prints hS hF h0 h1 h2)

/-- **`ModularToWeakWeil` from the same inputs** (PROVED, through the assembly
`modularToWeakWeil_of_newformPeriodsRational`). -/
theorem modularToWeakWeil_of_prints
    (hS : Shimura1973Thm1RationalGamma0) (hF : Faltings1983Kor2EllipticQ)
    (h0 : NewformOfModularCurveGlue) (h1 : ParametrizationPeriodsGlue)
    (h2 : IsogenyLatticeGlue) : ModularToWeakWeil :=
  modularToWeakWeil_of_newformPeriodsRational (newformPeriodsRational_of_prints hS hF h0 h1 h2)

end ZInQ.Contrib.RC53Assist.NewformPeriods
