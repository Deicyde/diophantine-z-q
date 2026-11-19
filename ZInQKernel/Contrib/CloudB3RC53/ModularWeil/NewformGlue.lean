import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Glue
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# G0: the newform of a modular elliptic curve (named consequence glue)

The package `RC53Assist/NewformPeriods` names the translation step G0,
`NewformOfModularCurveGlue`: a modular `E/ℚ` (`IsModular E`: a weight-two cusp form on `Γ₀(N)`
with the coefficients of `L(E, s)`) has, at some level `M`, a normalized full Hecke eigenform with
trivial character whose coefficients are `aₙ = E.LFunction n`.

**What is glue, and what is proved.**
* `LiCarayolNewformOfModular` (CONSEQUENCE GLUE, not a print): for a modular `E` there are
  `M ∣ N` and a newform of level `M`, weight `2` and trivial nebentypus (Tau Ceti's
  `HeckeRing.GL2.Newform`, Miyake's primitive form) whose coefficients are `E.LFunction n` for
  every `n ≥ 1`. Its sources (locators checked against page images by an independent reader;
  verdict: consequence, not a literal statement of either paper):
  - W.-C. W. Li, *Newforms and functional equations*, Math. Ann. **212** (1975), 285–315
    (bibitem `li-newforms`, tex L11050–11052): the old/new decomposition and the primitive
    forms, §2, p. 294; Theorem 3 (i), (iii), p. 295; strong multiplicity one, Theorem 5, p. 298.
    The manuscript's own locator for this bibitem is p. 296 (the Fricke-conjugation relation),
    which supports a different step;
  - H. Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de Hilbert*,
    Ann. Sci. ÉNS **19** (1986), 409–468 (bibitem `carayol`, tex L11205–11208): Théorème (A),
    pp. 410–411, the `ℓ`-adic Galois representation attached to a newform and its local–global
    compatibility, and the unnumbered Corollaire in §0.8, p. 411. Together with the Galois
    comparison below, the eigenvalues at the primes dividing the level are `+1`, `−1` or `0`,
    matching the local factors of `L(E, s)` at the bad primes.
  Further inputs, beyond both papers, are folded into this glue:
  - the Hecke bridge: the input form, whose coefficients are those of `L(E, s)`, is a Hecke
    eigenform away from its level;
  - the Galois comparison: the representation of the newform and the Tate module of `E` agree
    (Čebotarev density and Brauer–Nesbitt, from the coefficients at the good primes);
  - Casselman's newvector theory: the level of the newform is the conductor of the attached
    local representations, so that the coefficients at the primes dividing the level match the
    local factors of `L(E, s)`.
  The identification of the level with the conductor is not stated in Lean (Mathlib has no
  conductor of an elliptic curve).
* **`newformOfModularCurveGlue_of_print` (PROVED)**: `LiCarayolNewformOfModular →
  NewformOfModularCurveGlue` (the name is kept from an earlier labelling). The full eigen-ness at
  every `Tₙ`, the primes dividing the level included, is Tau Ceti's theorem
  `Newform.toEigenform` (Diamond–Shurman Theorem 5.8.2, Miyake Theorem 4.6.13), and the passage
  from `Γ₁(M)` with trivial character to `Γ₀(M)` is `cuspFormCharSpaceOneEquiv`. Both preserve the
  underlying function on `ℍ`.

**Classification.** `LiCarayolNewformOfModular` CONSEQUENCE GLUE (sources Li 1975 §2 p. 294,
Theorem 3 (i), (iii) p. 295 and Theorem 5 p. 298; Carayol 1986 Théorème (A) pp. 410–411 and the
Corollaire of §0.8 p. 411; locators checked against page images by an independent reader; plus
the Hecke bridge, the Čebotarev/Brauer–Nesbitt comparison and Casselman's newvector/conductor
comparison); the reduction PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open CongruenceSubgroup UpperHalfPlane HeckeRing.GL2
open ZInQ.Contrib.RC53Assist.NewformPeriods ZInQ.Manuscript.PoleS12

/-- **The newform of a modular elliptic curve** (CONSEQUENCE GLUE, not a print; sources Li 1975,
bibitem `li-newforms`, §2 p. 294, Theorem 3 (i), (iii) p. 295 and Theorem 5 p. 298, and Carayol
1986, bibitem `carayol`, Théorème (A) pp. 410–411 and the Corollaire of §0.8 p. 411, locators
checked against page images by an independent reader; together with the Hecke bridge, the
Čebotarev/Brauer–Nesbitt comparison and Casselman's newvector/conductor comparison; see the
module docstring). If `E/ℚ` has a weight-two
cusp form on `Γ₀(N)`, `N > 0`, with the coefficients of `L(E, s)`, then for some `M ∣ N` there is
a newform of level `M`, weight `2` and trivial nebentypus whose coefficients are `E.LFunction n`
for every `n ≥ 1`. -/
def LiCarayolNewformOfModular : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic →
    ∀ (N : ℕ) (_ : 0 < N) (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2),
      (∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ)) →
      ∃ (M : ℕ) (_ : NeZero M) (F : Newform M 2), M ∣ N ∧ F.χ = 1 ∧
        ∀ n : ℕ, 0 < n → (qExpansion 1 F.toCuspForm).coeff n = (E.LFunction n : ℂ)

/-- **G0 from the consequence glue `LiCarayolNewformOfModular`** (PROVED). -/
theorem newformOfModularCurveGlue_of_print (h : LiCarayolNewformOfModular) :
    NewformOfModularCurveGlue := by
  intro E hE hM
  obtain ⟨N, hN, f, hf⟩ := hM
  obtain ⟨M, hM0, F, -, hχ, hcoeff⟩ := h E hE N hN f hf
  have hmem : F.toCuspForm ∈ cuspFormCharSpace (N := M) 2 (1 : (ZMod M)ˣ →* ℂˣ) :=
    hχ ▸ F.mem_charSpace
  set g := TauCeti.cuspFormCharSpaceOneEquiv M 2 ⟨F.toCuspForm, hmem⟩
  have hg : ⇑g = ⇑F.toCuspForm := TauCeti.coe_cuspFormCharSpaceOneEquiv_apply _
  refine ⟨M, hM0, g, ⟨?_, F.toEigenform, by rw [Newform.toEigenform_χ, hχ], fun τ => ?_⟩,
    fun n hn => ?_⟩
  · rw [show qExpansion 1 g = qExpansion 1 F.toCuspForm from congrArg (qExpansion 1) hg]
    exact Newform.qExpansion_coeff_one F
  · rw [Newform.toEigenform_toCuspForm, hg]
  · rw [show qExpansion 1 g = qExpansion 1 F.toCuspForm from congrArg (qExpansion 1) hg]
    exact hcoeff n hn

end ZInQ.Contrib.CloudB3RC53.ModularWeil
