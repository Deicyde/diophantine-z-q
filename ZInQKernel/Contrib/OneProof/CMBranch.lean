import ZInQKernel.Contrib.OneProof.H.LPrefix
import ZInQKernel.Contrib.OneProof.CMBranch.Arith

/-! # cm-branch: the manuscript's CM fibres (diophantine_zq.tex L581-631), from the cited leaves

The fleet's route excludes CM fibres by NoCM (h-trust A10, which replaces N5 L578-631). This file
formalizes the manuscript's own CM paragraph instead: for a CM fibre it produces glue-assembly's
`GlueAssembly.CMOutput h_F(A)`, the disjunct of `GlueAssembly.GlueOutputs` that the chain never
used, from

* printed leaves: Fowler, Prop. 2.7 (`FowlerProp27`); Barquero-Sanchez–Cadwallader–Cannon–Genao–Masri,
  Eq. (6.2) (`CMHeight62`); Gaudron–Rémond Thm 1.4 (the chain's `R19_GaudronRemond`, reused); Faltings'
  Lemma 5, lower half (the chain's `R20Lower`, reused);
* classical CM facts the manuscript states without a citation: `CMjDegree` (`[ℚ(j(E)):ℚ] = h(Δ)`),
  `CMPotentialGood` (CM ⇒ potentially good reduction);
* named glue: `CMFibreSplit` (A8's field for the CM fibre and the matrix units, L583-586),
  `ReducedCMPeriod` (L598-599), `HeightAdditivityUpper` (the other half of additivity, L621);
* Lean proofs of all the arithmetic (`Arith.lean`, and `cmOutput_of`, `faltingsHeight_le_bcm` here).

The case split (`glueOutputs_of_branches`) is then a Lean proof: `GlueOutputs` follows from the non-CM
branch restricted to fibres without CM (`NonCMBranch`) and the CM branch (`CMBranchOut`).
-/

namespace HDec
namespace CMBranch

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.ZInQ ZInQ ZInQ.JHeight HDec.LeafQM.AV HDec.ZInQ.DefFaltings
open HSyn HSyn.G0Split
open _root_.CMBranch

/-! ## 1. Imaginary quadratic orders -/

/-- `R` is an order of the imaginary quadratic field `k`: `k` is totally complex of degree 2 and `R`
is a subring of finite index of `𝓞_k` (finite conductor `[𝓞_k : R]`, `LeafQM.AV.conductor`). -/
def IsImagQuadOrder (k : Type) [Field k] [NumberField k] (R : Subring k) : Prop :=
  NumberField.IsTotallyComplex k ∧ Module.finrank ℚ k = 2 ∧
    R ≤ (integralClosure ℤ k).toSubring ∧ LeafQM.AV.conductor R ≠ 0

/-- The discriminant of the order `R`: `Δ_R = f² d_k`, `f = [𝓞_k : R]` (STANDARD: the order of
conductor `f` in a quadratic field has discriminant `f² d_k`; Cox, *Primes of the form x²+ny²*,
eq. (7.3), UNVERIFIED number). -/
noncomputable def orderDisc {k : Type} [Field k] [NumberField k] (R : Subring k) : ℤ :=
  (LeafQM.AV.conductor R : ℤ) ^ 2 * NumberField.discr k

/-! ## 2. The printed leaves -/

/-- **Leaf (printed form): Fowler, Prop. 2.7.** G. Fowler, *Some uniform effective results on
André–Oort for sums of powers in ℂⁿ*, Math. Proc. Cambridge Philos. Soc. 180 (2026) 607-641,
Prop. 2.7 (article pp. 9-10, printed pp. 615-616; read by the upstream audit,
`docs/reviews/height-replacement/height/AUDIT.md` item 1): every negative order discriminant `Δ` with
`h(Δ) ≤ n` has `√|Δ| ≤ 2n² exp(21000 n²)`, with no exceptional field. Stated over orders: `Δ = Δ_R`
and `h(Δ) = #Pic(R)` (the class number of primitive forms of discriminant `Δ` is that of proper
`R`-ideals; Cox Thm 7.7, UNVERIFIED number). Used at `n = D` (manuscript L589-593). -/
def FowlerProp27 : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R →
    ∀ n : ℕ, 1 ≤ n → Nat.card (CommRing.Pic R) ≤ n →
      Real.sqrt |(orderDisc R : ℝ)| ≤ 2 * (n : ℝ) ^ 2 * Real.exp (21000 * (n : ℝ) ^ 2)

/-- `E` (an elliptic curve: an abelian variety of dimension 1) has geometric endomorphism ring `R`:
`End(E_{L̄}) ≅ R`. -/
def IsCMBy {L : Type} [Field L] (E : ZInQ.DefFaltings.AbVar L) (k : Type) [Field k]
    (R : Subring k) : Prop :=
  Nonempty (PkgI3.AbVar.End ((LeafAdopt.abVarEquiv L E).baseChange (AlgebraicClosure L)) ≃+* R)

/-- `τ` is a period of `E` at `σ`: `E(ℂ)_σ ≅ ℂ/Λ` analytically (`ZInQ.LeafPush2.IsUniformization`,
`g = 1`) with `Λ = c(ℤ + τℤ)` for some `c ≠ 0`. -/
def IsPeriodAt {K : Type} [Field K] (E : PkgI3.AbVar K) (σ : K →+* ℂ) (τ : ℂ) : Prop :=
  ∃ (Λ : Submodule ℤ (Fin 1 → ℂ)) (Φ : (Fin 1 → ℂ) → ZInQ.LeafPush2.CPts E σ),
    ZInQ.LeafPush2.IsUniformization σ Λ Φ ∧
      ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z 0 = c * (m + n * τ)

/-- **Leaf (consequence of the printed formula): Barquero-Sanchez, Cadwallader, Cannon, Genao, Masri,
Eq. (6.2).** *Faltings heights of CM elliptic curves and special Gamma values*, Res. Number Theory 3
(2017) art. 13, §6, Eq. (6.2), pp. 13-14 (read by the upstream audit, AUDIT.md item 2: original
Faltings metric, `Δ(τ) = (2π)¹² η(τ)²⁴`; the general elliptic discriminant formula, attributed there to
Silverman, Prop. 1.1). For an elliptic curve `E/K` with good reduction everywhere over `L ⊇ K` (an
abelian-scheme group model `𝒢` of `E_L` over `𝓞_L`) the finite term vanishes and the stable height is
the average over `σ : L → ℂ` of `−(1/12) log(|Δ(τ_σ)| (Im τ_σ)⁶)`, `τ_σ` a period of `E` at `σ`.
Stated as the inequality `≤` (the half the manuscript uses, L594-613). -/
def CMHeight62 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (E : ZInQ.DefFaltings.AbVar K), E.dim = 1 →
    ∀ 𝒢 : ZInQ.DefFaltings.GroupModel E L, IsProper 𝒢.G.hom →
    ∀ τ : (L →+* ℂ) → ℂ,
      (∀ σ, 0 < (τ σ).im ∧ IsPeriodAt (LeafAdopt.abVarEquiv K E) (σ.comp (algebraMap K L)) (τ σ)) →
      stableFaltingsHeight E ≤ (((∑ σ, summand62 (τ σ)) / Module.finrank ℚ L : ℝ) : EReal)

/-- **Leaf (classical, no citation in the manuscript): the degree of a singular modulus.** For an
elliptic curve `E/L` with `End(E_{L̄}) ≅ R`, `j(E) ∈ L` has degree `h(R) = #Pic(R)` over `ℚ`, so
`#Pic(R) ≤ [L:ℚ]` (manuscript L586-587, "The degree of `j(E)` is its order class number"; Cox,
*Primes of the form x² + ny²*, Thm 11.1 (orders), UNVERIFIED number; the upstream audit,
`docs/theorem-application-audit/FINDINGS.md`, sources it to Fowler §2.1). -/
def CMjDegree : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R → IsCMBy E k R →
      Nat.card (CommRing.Pic R) ≤ Module.finrank ℚ L

/-- **Leaf (classical, no citation in the manuscript): CM elliptic curves have potentially good
reduction** (manuscript L596-597, "After a finite extension `E` has everywhere good reduction, since
its `j`-invariant is integral"; Serre–Tate, Ann. of Math. 88 (1968), §6 Thm 7 / Silverman, AEC
VII.5.5 with the integrality of singular moduli; also proved in the cited [cmheight], proof of
Thm 1.3, p. 15 (AUDIT.md item 2)). Form: an abelian-scheme group model of `E_{L₁}` over `𝓞_{L₁}`
for some finite `L₁/L`. -/
def CMPotentialGood : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R → IsCMBy E k R →
      ∃ (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L L₁)
        (𝒢 : ZInQ.DefFaltings.GroupModel E L₁), IsProper 𝒢.G.hom

/-! ## 3. The named glue -/

/-- **Glue (on-the-spot, manuscript L598-599): reduced CM periods.** For `E/K` with `End(E_{K̄}) ≅ R`
and every `σ : K → ℂ`, `E` has a period `τ` at `σ` with `√3/2 ≤ Im τ ≤ √|Δ_R|/2`. Sketch:
`End(E_ℂ^σ) ≅ End(E_{K̄}) ≅ R` (rigidity), so the lattice is homothetic to a proper fractional
`R`-ideal; a reduced basis (`|Re τ| ≤ 1/2`, `|τ| ≥ 1`) gives `Im τ ≥ √3/2`, and `τ` is the root of a
primitive form `(a, b, c)` of discriminant `Δ_R`, so `Im τ = √|Δ_R|/(2a) ≤ √|Δ_R|/2`. -/
def ReducedCMPeriod : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (E : ZInQ.DefFaltings.AbVar K), E.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k), IsImagQuadOrder k R → IsCMBy E k R →
      ∀ σ : K →+* ℂ, ∃ τ : ℂ, IsPeriodAt (LeafAdopt.abVarEquiv K E) σ τ ∧
        Real.sqrt 3 / 2 ≤ τ.im ∧ τ.im ≤ Real.sqrt |(orderDisc R : ℝ)| / 2

/-- **Glue (manuscript L621, "additivity"): the upper half of additivity of the stable height**,
`h_F(A × Z) ≤ h_F(A) + h_F(Z)` (equality: Faltings 1983 §1; the chain's `HeightAdditivity` is the
other half). -/
def HeightAdditivityUpper : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L),
    IsProductOf P.X A.X Z.X → ∀ a z p : ℝ, stableFaltingsHeight A = a →
      stableFaltingsHeight Z = z → stableFaltingsHeight P = p → p ≤ a + z

/-- No `ℚ̄`-point of `Y` over `J(u)` carries a CM object: `End_𝒪(P.A) = ℤ` at each (FS5 at `u`). -/
def NoCMAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ) :
    Prop :=
  ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
    π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
    ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-- **Glue (manuscript A8, L520-562, for a CM fibre, and L583-586).** If some point over `J(u)` has
CM, the fibre surface has a model `A` over a number field `L` with `[L:ℚ] ≤ D` over which every
geometric endomorphism is defined (A8; its proof does not use the case split), and the matrix units of
`End⁰(A) = M₂(k)` give an elliptic curve `E/L` with `End(E_{L̄})` an order `R` of `k`, the product
`E² = E × E` and an `L`-isogeny `E² → A`. -/
def CMFibreSplit : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet → ¬ NoCMAt Y Φ π u →
    ∃ (L : GlueAssembly.NF) (A E Pr : ZInQ.DefFaltings.AbVar L.K) (k : Type) (_ : Field k)
      (_ : NumberField k) (R : Subring k),
      FibreOver Y Φ π u L A ∧ Module.finrank ℚ L.K ≤ heightD ∧ E.dim = 1 ∧
      Pr.dim = (2 : ℕ) ∧ IsProductOf Pr.X E.X E.X ∧ (∃ φ : Pr.X ⟶ A.X, IsIsogeny φ) ∧
      IsImagQuadOrder k R ∧ IsCMBy E k R

/-! ## 4. `h_F(E) ≤ B_cm` (manuscript L586-612) -/

theorem cast_bcm {B D : ℕ} (h : B = D ^ 2 * 3 ^ (21000 * D ^ 2) + 1) :
    (B : ℝ) = (D : ℝ) ^ 2 * 3 ^ (21000 * D ^ 2) + 1 := by
  rw [h]; push_cast; ring

theorem cast_heightBcm : (heightBcm : ℝ) = (heightD : ℝ) ^ 2 * 3 ^ (21000 * heightD ^ 2) + 1 :=
  cast_bcm _root_.ZInQ.Compiler.Precision.heightBcm_eq

theorem one_le_heightD_nat : 1 ≤ heightD := by
  have := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  omega

/-- **`h_F(E) ≤ B_cm`.** Steps: `h(Δ) ≤ d ≤ D` (`CMjDegree`, L586-587); Fowler at `n = D` (L589-593);
good reduction after a finite extension (`CMPotentialGood`, L596-597); Eq. (6.2) (`CMHeight62`,
L600-604) with reduced periods (`ReducedCMPeriod`, L598-599); each summand `≤ π√|Δ|/12 + 1`
(`archSummand_le`, L605-611); `≤ B_cm` (`bcm_of_fowler`, L611-612). -/
theorem faltingsHeight_le_bcm (hfin : StableHeightFinite) (hF : FowlerProp27) (hJ : CMjDegree)
    (hPG : CMPotentialGood) (h62 : CMHeight62) (hRP : ReducedCMPeriod)
    {L : Type} [Field L] [NumberField L] (E : ZInQ.DefFaltings.AbVar L) (hE1 : E.dim = 1)
    {k : Type} [Field k] [NumberField k] (R : Subring k) (hR : IsImagQuadOrder k R)
    (hCM : IsCMBy E k R) (hd : Module.finrank ℚ L ≤ heightD) :
    faltingsHeight E ≤ (heightBcm : ℝ) := by
  obtain ⟨L₁, i1, i2, i3, 𝒢, h𝒢⟩ := hPG L E hE1 k R hR hCM
  set s := Real.sqrt |(orderDisc R : ℝ)| with hs
  have hτ : ∀ σ : L₁ →+* ℂ, ∃ τ : ℂ,
      IsPeriodAt (LeafAdopt.abVarEquiv L E) (σ.comp (algebraMap L L₁)) τ ∧
        Real.sqrt 3 / 2 ≤ τ.im ∧ τ.im ≤ s / 2 :=
    fun σ => hRP L E hE1 k R hR hCM _
  choose τ hτ using hτ
  have h3 : (0 : ℝ) < Real.sqrt 3 / 2 := by positivity
  have hpos : ∀ σ, 0 < (τ σ).im := fun σ => lt_of_lt_of_le h3 (hτ σ).2.1
  have hle := h62 L L₁ E hE1 𝒢 h𝒢 τ (fun σ => ⟨hpos σ, (hτ σ).1⟩)
  have hterm : ∀ σ, summand62 (τ σ) ≤ Real.pi * s / 12 + 1 := by
    intro σ
    rw [summand62_eq_archSummand (hpos σ)]
    have h1 := archSummand_le (hτ σ).2.1
    have h2 : Real.pi * (τ σ).im / 6 ≤ Real.pi * (s / 2) / 6 := by
      have := mul_le_mul_of_nonneg_left (hτ σ).2.2 Real.pi_pos.le; linarith
    linarith
  have hn : (0 : ℝ) < Module.finrank ℚ L₁ := by exact_mod_cast Module.finrank_pos
  have hcard : (Finset.univ : Finset (L₁ →+* ℂ)).card = Module.finrank ℚ L₁ := by
    rw [Finset.card_univ]; exact NumberField.Embeddings.card L₁ ℂ
  have havg : (∑ σ, summand62 (τ σ)) / Module.finrank ℚ L₁ ≤ Real.pi * s / 12 + 1 := by
    rw [div_le_iff₀ hn]
    calc ∑ σ, summand62 (τ σ) ≤ ∑ _σ : L₁ →+* ℂ, (Real.pi * s / 12 + 1) := Finset.sum_le_sum fun σ _ => hterm σ
      _ = (Real.pi * s / 12 + 1) * Module.finrank ℚ L₁ := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
  have hfow : s ≤ 2 * (heightD : ℝ) ^ 2 * Real.exp (21000 * (heightD : ℝ) ^ 2) :=
    hF k R hR heightD one_le_heightD_nat ((hJ L E hE1 k R hR hCM).trans hd)
  have hB := bcm_of_fowler heightD hfow
  rw [← cast_heightBcm] at hB
  have hE : (faltingsHeight E : EReal) ≤ ((heightBcm : ℝ) : EReal) := by
    rw [faltingsHeight_coe hfin]
    exact hle.trans (EReal.coe_le_coe_iff.mpr (havg.trans hB))
  exact EReal.coe_le_coe_iff.mp hE

/-! ## 5. `CMOutput` (manuscript L614-628) -/

theorem grKappa_two (n : ℕ) (x : ℝ) :
    grKappa 2 n x = ((28 : ℝ) ^ 256 * n * (max (max x (Real.log n)) 1) ^ 2) ^ 8192 := by
  unfold grKappa; norm_num

/-- **The CM branch output** (manuscript L614-628): Gaudron–Rémond Thm 1.4 over `L` with source `E²`
(`R19_GaudronRemond`), Faltings' height variation (lower half, `R20Lower`) and additivity
(`HeightAdditivityUpper`) give glue-assembly's `CMOutput h_F(A)`; with `cm_branch_nat` this is
`h_F(A) ≤ C_cm`. -/
theorem cmOutput_of (hfin : StableHeightFinite) (hAddU : HeightAdditivityUpper)
    (r19 : R19_GaudronRemond) (r20 : R20Lower) {L : Type} [Field L] [NumberField L]
    (A E Pr : ZInQ.DefFaltings.AbVar L) (hd : Module.finrank ℚ L ≤ heightD)
    (hE : faltingsHeight E ≤ (heightBcm : ℝ)) (hPr2 : Pr.dim = (2 : ℕ))
    (hprod : IsProductOf Pr.X E.X E.X) (hiso : ∃ φ : Pr.X ⟶ A.X, IsIsogeny φ) :
    GlueAssembly.CMOutput (faltingsHeight A) := by
  set d : ℝ := (Module.finrank ℚ L : ℝ) with hddef
  set e := faltingsHeight E
  set x := faltingsHeight Pr
  set a := faltingsHeight A
  have hx : stableFaltingsHeight Pr = x := (faltingsHeight_coe hfin Pr).symm
  have he : stableFaltingsHeight E = e := (faltingsHeight_coe hfin E).symm
  have ha : stableFaltingsHeight A = a := (faltingsHeight_coe hfin A).symm
  obtain ⟨⟨φ, hφ, hdeg⟩, -⟩ := r19 L Pr A 2 x hPr2 hx hiso
  have hvar := r20 L Pr A φ hφ x a hx ha
  have hadd := hAddU L Pr E E hprod e e x he he hx
  have hd1 : (1 : ℝ) ≤ d := by
    have : 0 < Module.finrank ℚ L := Module.finrank_pos
    rw [hddef]; exact_mod_cast this
  have hdD : d ≤ heightD := by rw [hddef]; exact_mod_cast hd
  set M := max (2 * e) (max (Real.log d) 1) with hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hlog28 : 0 ≤ Real.log 28 := Real.log_nonneg (by norm_num)
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hRHS : 0 ≤ 8192 * (256 * Real.log 28 + Real.log d + 2 * Real.log M) := by positivity
  refine ⟨d, e, Real.log (isogDeg φ), hd1, hdD, hE, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (isogDeg φ) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact hRHS
    have hm : max (max x (Real.log d)) 1 ≤ M := by
      rw [hM, ← max_assoc]
      exact max_le_max (max_le_max (by linarith) le_rfl) le_rfl
    have hm1 : (1 : ℝ) ≤ max (max x (Real.log d)) 1 := le_max_right _ _
    rw [grKappa_two] at hdeg
    have hdegpos : (0 : ℝ) < isogDeg φ := by exact_mod_cast hpos
    have h28 : (0 : ℝ) < 28 ^ 256 := by positivity
    calc Real.log (isogDeg φ)
        ≤ Real.log (((28 : ℝ) ^ 256 * d * (max (max x (Real.log d)) 1) ^ 2) ^ 8192) :=
          Real.log_le_log hdegpos hdeg
      _ = 8192 * (256 * Real.log 28 + Real.log d +
            2 * Real.log (max (max x (Real.log d)) 1)) := by
          rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast; ring
      _ ≤ 8192 * (256 * Real.log 28 + Real.log d + 2 * Real.log M) := by
          have := Real.log_le_log (by linarith) hm
          linarith
  · linarith

/-- **`h_F(A) ≤ C_cm` for the CM fibre**, the manuscript's conclusion (L622-625), from `CMOutput` by
glue-assembly's proved `cm_branch_nat`. -/
theorem le_heightCcm_of_cmOutput {hA : ℝ} (h : GlueAssembly.CMOutput hA) : hA ≤ heightCcm := by
  obtain ⟨d, hE, L, hd1, hd, hEB, hL, hvar⟩ := h
  have hcm := GlueAssembly.cm_branch_nat _root_.ZInQ.Compiler.Precision.heightBcm_eq
    _root_.ZInQ.Compiler.Precision.heightCcm_eq one_le_heightD_nat hd1 hd hEB hL hvar
  exact hcm

/-! ## 6. The CM branch on the fibre, and the case split -/

/-- **The CM branch's interface**: for `u ∉ 𝒞` with a CM point over `J(u)`, the theta point, Pazuki's
bound and `CMOutput` for the Faltings height of the fibre surface (the `Or.inr` disjunct of
`GlueOutputs`). -/
def CMBranchOut : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet → ¬ NoCMAt Y Φ π u →
    ∃ (K : GlueAssembly.NF) (z : Fin 10 → K.K) (hA : ℝ),
      3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K.K (Jmap u) ∧
      GlueAssembly.PazukiOutput (Height.logHeight z / Module.finrank ℚ K.K) hA ∧
      GlueAssembly.CMOutput hA

/-- **The non-CM branch's interface** (the chain's `Or.inl` path, at fibres without CM): for `u ∉ 𝒞`
with no CM point over `J(u)`, the theta point, Pazuki's bound and `NonCMOutput`. -/
def NonCMBranch : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π →
    (∀ t : OnePoint LeafQM.AV.Qbar, ∃ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar),
      Φ LeafQM.AV.Qbar y = M3.mk P ∧ π.val (K := LeafQM.AV.Qbar) y.left = t) →
    ∀ u : ℚ, u ∉ contactSet → NoCMAt Y Φ π u →
    ∃ (K : GlueAssembly.NF) (z : Fin 10 → K.K) (hA : ℝ),
      3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K.K (Jmap u) ∧
      GlueAssembly.PazukiOutput (Height.logHeight z / Module.finrank ℚ K.K) hA ∧
      GlueAssembly.NonCMOutput (heightQ heightD) (contactSupport Mult.S_mul u) hA

/-- **The CM branch, proved** from `CMFibreSplit`, the leaves of §2, the glue of §3, the chain's
`R19_GaudronRemond`, `R20Lower`, `ThetaPazuki`, `DimBaseChange` and H5's finiteness. -/
theorem cmBranchOut_of (hfin : StableHeightFinite) (hDim : DimBaseChange) (hTP : ThetaPazuki)
    (hSplit : CMFibreSplit) (hF : FowlerProp27) (hJ : CMjDegree) (hPG : CMPotentialGood)
    (h62 : CMHeight62) (hRP : ReducedCMPeriod) (hAddU : HeightAdditivityUpper)
    (r19 : R19_GaudronRemond) (r20 : R20Lower) : CMBranchOut := by
  intro Y Φ π h1 h2 u hu hCM
  obtain ⟨L, A, E, Pr, k, _, _, R, hFib, hd, hE1, hPr2, hprod, hiso, hR, hCMR⟩ :=
    hSplit Y Φ π h1 h2 u hu hCM
  obtain ⟨emb, y, P, hP, hy, hisoA⟩ := hFib
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hisoA P.surface
  obtain ⟨K', z, hF1, hPaz⟩ := hTP Y Φ π h1 h2 u hu L A ⟨emb, y, P, hP, hy, hisoA⟩ hA2 _
    (faltingsHeight_coe hfin A).symm
  refine ⟨K', z, faltingsHeight A, hF1, hPaz, ?_⟩
  exact cmOutput_of hfin hAddU r19 r20 A E Pr hd
    (faltingsHeight_le_bcm hfin hF hJ hPG h62 hRP E hE1 R hR hCMR hd) hPr2 hprod hiso

/-- **The case split** (manuscript L578-580, "We treat these two cases separately", merged at
L901-905): `GlueOutputs S_mul` from the moduli data with a point over every value, the non-CM branch at
fibres without CM, and the CM branch. -/
theorem glueOutputs_of_branches
    (hfib : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ t : OnePoint LeafQM.AV.Qbar, ∃ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar),
        Φ LeafQM.AV.Qbar y = M3.mk P ∧ π.val (K := LeafQM.AV.Qbar) y.left = t)
    (hNC : NonCMBranch) (hCMb : CMBranchOut) : GlueAssembly.GlueOutputs Mult.S_mul := by
  obtain ⟨Y, Φ, π, h1, h2, hpts⟩ := hfib
  intro u hu
  by_cases hno : NoCMAt Y Φ π u
  · obtain ⟨K, z, hA, hF1, hPaz, hO⟩ := hNC Y Φ π h1 h2 hpts u hu hno
    exact ⟨K, z, hA, hF1, hPaz, Or.inl hO⟩
  · obtain ⟨K, z, hA, hF1, hPaz, hO⟩ := hCMb Y Φ π h1 h2 u hu hno
    exact ⟨K, z, hA, hF1, hPaz, Or.inr hO⟩

/-- **`SixContactMin` from the two branches** (glue-assembly's `sixContactMinAt_of_glueOutputs`). -/
theorem sixContactMin_of_branches
    (hfib : ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧
      ∀ t : OnePoint LeafQM.AV.Qbar, ∃ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar),
        Φ LeafQM.AV.Qbar y = M3.mk P ∧ π.val (K := LeafQM.AV.Qbar) y.left = t)
    (hNC : NonCMBranch) (hCMb : CMBranchOut) : _root_.ZInQ.SixContactMin :=
  HSyn.sixContactMin_of_glueOutputs (glueOutputs_of_branches hfib hNC hCMb)

end CMBranch
end HDec
