import ZInQKernel.Contrib.OneProof.ElkiesX6StarPrinted
import ZInQKernel.Contrib.OneProof.LinYangPrinted
import ZInQKernel.Contrib.OneProof.MumfordRigidity
import ZInQKernel.Contrib.OneProof.CarayolLevel
import ZInQKernel.Contrib.OneProof.LeafAudit1115H29
import ZInQKernel.Contrib.OneProof.QMRecPrinted
import ZInQKernel.Contrib.OneProof.PanBerger
import ZInQKernel.Contrib.OneProof.FaltingsTateSurj
import ZInQKernel.Contrib.OneProof.ShimuraIntegralModelUsed
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.HeegnerCd
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilLattice

/-!
# leaf-audit: adversarial Lean audit of the leaves introduced on 2026-11-15

Report: `docs/research/leaf-audit.md`; log: `scratch/leaf-audit/log.md`. For each leaf: (1) non-vacuity (its
hypotheses can be met), (2) a sanity case, (3) the Lean proofs relating it to the field it replaces.

* **`LinYangEx29All` is false** (§1): its premises on the Hauptmodul `j₆` are invariant under `j₆ ↦ conj ∘ j₆`,
  its conclusion is not. With `IgusaThetaExpressions` and `QMHauptmodul` it forces `j_θ = jNum/jDen ∘ Ω` to be
  real wherever `jDen ≠ 0`; numerically `j_θ(0.3 + 1.1i) = 4.2731… − 0.6831…i` (`|jDen| ≈ 3·10⁵`;
  `scratch/leaf-audit/py/jtheta_nonreal.py`). Correction: theta-fold's existential `LinYangEx29`.
* The other leaves: non-vacuity shown where Lean can build an instance (zero abelian variety, trivial family,
  `N = 1` and `τ = i`, sibling leaves for TYZ); the old/new implications are checked below.

`h29-ne3`'s leaves live in `LeafAudit1115H29` (a verbatim copy of `scratch/h29-ne3/TYZLemma29Mod2.lean`, the
drop-in replacement of `ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean`; same namespace).
-/

noncomputable section

namespace LeafAudit1115

/-! ## 1. `LinYangEx29All` (theta-fold): FALSE as stated -/

open HDec HDec.HSyn.G0Split.ThetaPt.LinYangPrinted

/-- Complex conjugation on the Riemann sphere `ℂ ∪ {∞}`. -/
def conjOP : OnePoint ℂ ≃ₜ OnePoint ℂ :=
  Homeomorph.onePointCongr Complex.conjLIE.toHomeomorph

@[simp] theorem conjOP_coe (z : ℂ) :
    conjOP (z : OnePoint ℂ) = ((starRingEnd ℂ z : ℂ) : OnePoint ℂ) := rfl

@[simp] theorem conjOP_infty : conjOP OnePoint.infty = OnePoint.infty := rfl

/-- **`LinYangEx29All` forces `(z − z̄)·s₂³ = 0`.** Its premises on `j₆` are invariant under
`j₆ ↦ conj ∘ j₆` (conjugation fixes `0`, `∞`, `−16/27`), its conclusion `s₃² = z s₂³` is not. -/
theorem linYangEx29All_conj (hA : LinYangEx29All) (j6 : UpperHalfPlane → OnePoint ℂ)
    (hc : Continuous j6)
    (hfib : ∀ τ τ' : UpperHalfPlane, j6 τ = j6 τ' ↔ ∃ γ ∈ PkgI1.GammaStar, γ • τ = τ')
    (hs : Function.Surjective j6)
    (h4 : ∀ x : PkgI1.B, PkgI1.InO x → x * x = -1 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((0 : ℂ) : OnePoint ℂ))
    (h3 : ∀ x : PkgI1.B, PkgI1.InO x → x * x - x + 1 = 0 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = (OnePoint.infty : OnePoint ℂ))
    (h24 : ∀ x : PkgI1.B, PkgI1.InO x → x * x = -6 → ∀ γ : GL (Fin 2) ℝ,
      (γ : Matrix (Fin 2) (Fin 2) ℝ) = PkgI1.iota x → ∀ τ : UpperHalfPlane, γ • τ = τ →
        j6 τ = ((-16/27 : ℂ) : OnePoint ℂ))
    (τ : UpperHalfPlane) (z : ℂ) (hz : j6 τ = (z : OnePoint ℂ)) :
    (z - starRingEnd ℂ z) * lyS2 (PkgI1.Omega τ) ^ 3 = 0 := by
  have e1 := (hA j6 hc hfib hs h4 h3 h24 τ z hz).1
  have e2 := (hA (conjOP ∘ j6) (conjOP.continuous.comp hc)
    (fun τ τ' => by
      simp only [Function.comp_apply]
      rw [conjOP.injective.eq_iff]
      exact hfib τ τ')
    (conjOP.surjective.comp hs)
    (fun x hx hxx γ hγ τ hτ => by simp [h4 x hx hxx γ hγ τ hτ])
    (fun x hx hxx γ hγ τ hτ => by simp [h3 x hx hxx γ hγ τ hτ])
    (fun x hx hxx γ hγ τ hτ => by
      simp only [Function.comp_apply, h24 x hx hxx γ hγ τ hτ, conjOP_coe]
      congr 1
      rw [map_div₀, map_neg, map_ofNat, map_ofNat])
    τ (starRingEnd ℂ z) (by simp [hz])).1
  linear_combination e2 - e1

/-- **With Igusa's theta expressions and `QMHauptmodul`, `LinYangEx29All` makes `j_θ` real** wherever its
denominator `jDen = (Σθ⁸)⁵` does not vanish. Numerically `j_θ(0.3 + 1.1i) = 4.2731… − 0.6831…i` with
`|jDen| ≈ 3·10⁵` (scratch/leaf-audit/py/jtheta_nonreal.py), so the three statements are inconsistent. -/
theorem jtheta_real_of_leaves (hI : IgusaThetaExpressions) (hA : LinYangEx29All)
    (hH : PkgI1.QMHauptmodul) (τ : UpperHalfPlane) (hden : PkgI1.jDen (PkgI1.Omega τ) ≠ 0) :
    (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)).im = 0 := by
  obtain ⟨f, hc, hval, hfib, hs, h4, h3, h24⟩ := hH
  set w := PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) with hw
  have hrel := linYangEx29All_conj hA f hc hfib hs h4 h3 h24 τ w (hval τ hden)
  have hs2 : lyS2 (PkgI1.Omega τ) ≠ 0 := by
    have hSieg := HDec.HSyn.G0Split.FibreQM.PeriodMap.omegaSiegel_proof (τ : ℂ) τ.im_pos
    rw [lyS2, (hI _ hSieg).1, HDec.HSyn.G0Split.ThetaPt.ThetaGlue.psi4Th]
    intro h
    apply hden
    rw [PkgI1.jDen]
    have : PkgI1.thetaSum8 (PkgI1.Omega τ) = 0 := by linear_combination 4 * h
    rw [this]; ring
  have hw0 : w - starRingEnd ℂ w = 0 := by
    rcases mul_eq_zero.1 hrel with h | h
    · exact h
    · exact (hs2 ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).1 h)).elim
  have := congrArg Complex.im hw0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
  linarith

/-- **`LinYangEx29All` is refuted** by Igusa's theta expressions, `QMHauptmodul` and one point where
`j_θ = jNum/jDen ∘ Ω` is finite and not real (numerics: `τ = 0.3 + 1.1i`). -/
theorem not_linYangEx29All (hI : IgusaThetaExpressions) (hH : PkgI1.QMHauptmodul)
    (hnum : ∃ τ : UpperHalfPlane, PkgI1.jDen (PkgI1.Omega τ) ≠ 0 ∧
      (PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ)).im ≠ 0) :
    ¬ LinYangEx29All := by
  intro hA
  obtain ⟨τ, hden, him⟩ := hnum
  exact him (jtheta_real_of_leaves hI hA hH τ hden)

/-- The corrected (existential) form `LinYangEx29` already feeds the consumer, with no `QMHauptmodul`. -/
example (hI : IgusaThetaExpressions) (hL : LinYangEx29) :
    HDec.HSyn.G0Split.ThetaPt.ThetaSplit.ThetaRatiosAtQM :=
  HDec.HSyn.G0Split.ThetaPt.IgusaAlgFinal.thetaRatiosAtQM_of_printed hI hL

end LeafAudit1115


/-! ## 2. `ElkiesX6StarFunctionField` (elkies-coord) -/

namespace HDec.QMSplit.Moduli.ElkiesCoord.LeafAudit1115

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV

/-- **Non-vacuity of the function-field clause:** its premises (`X₆` integral, `t` regular at the generic
point) hold for every witness, since the leaf's own chart clause gives them. -/
theorem ff_premises_of_charts {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left}
    (hc : X6Glue.ElkiesCharts X t) : ∃ _ : IsIntegral X.left, genericPoint X.left ∈ t.U :=
  ⟨isIntegral_of_charts hc, by have := isIntegral_of_charts hc; exact genericPoint_mem_of_charts hc⟩

/-- Old from new (elkies-coord, compiled there): the leaf implies the field `ElkiesX6StarPrinted`. -/
example : ElkiesX6StarFunctionField → ElkiesX6Star.ElkiesX6StarPrinted :=
  elkiesX6StarPrinted_of_functionField

end HDec.QMSplit.Moduli.ElkiesCoord.LeafAudit1115

namespace LeafAudit1115

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-! ## 4. `FaltingsTateSurj` (faltings-cm) at the zero abelian variety -/

instance subsingleton_pt_zero (K L : Type) [Field K] [Field L] [Algebra K L] :
    Subsingleton ((PkgI3.AbVar.zero K).Pt L) :=
  ⟨fun a b => CartesianMonoidalCategory.toUnit_unique a b⟩

instance subsingleton_T_zero (K : Type) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] :
    Subsingleton ((PkgI3.AbVar.zero K).T ℓ) :=
  ⟨fun a b => Subtype.ext (funext fun n => by
    exact Additive.toMul.injective (Subsingleton.elim _ _))⟩

/-- **FaltingsTateSurj, sanity case (unconditional):** its conclusion holds for `A = B = 0` over `ℚ`. -/
theorem faltingsTateSurj_zero (ℓ : ℕ) [Fact ℓ.Prime] :
    {φ | PkgI3.AbVar.IsGalEquivariant φ} ⊆
      Set.range (PkgI3.AbVar.tateHomZl ℓ (PkgI3.AbVar.zero ℚ) (PkgI3.AbVar.zero ℚ)) := by
  intro φ _
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact LinearMap.ext fun x => Subsingleton.elim _ _

/-! ## 3. `MumfordGroupLaw` (leaf-fold23) at the trivial family `Spec ℚ → Spec ℚ` -/

/-- The trivial family over `S = Spec ℚ`: `F = 𝟙_ (Over S)` (`F.hom = 𝟙 S`). -/
abbrev Striv : Scheme.{0} := Spec (CommRingCat.of ℚ)

theorem one_pt_zero_comp (K : Type) [Field K] {T : Scheme.{0}} (s : Spec (CommRingCat.of K) ⟶ T) :
    ((1 : (PkgI3.AbVar.zero K).Pt K)).left ≫ s = s := by
  have w := Over.w (1 : (PkgI3.AbVar.zero K).Pt K)
  have e : (PkgI3.AbVar.ptObj (K := K) K).hom = 𝟙 _ := by
    change Spec.map (CommRingCat.ofHom (algebraMap K K)) = _
    rw [show CommRingCat.ofHom (algebraMap K K) = 𝟙 _ from rfl, Spec.map_id]; rfl
  rw [e] at w
  erw [Category.comp_id] at w
  erw [w, Category.id_comp]

instance isIso_zero_hom (K : Type) [Field K] : IsIso (PkgI3.AbVar.zero K).X.hom := by
  change IsIso (𝟙 _); infer_instance

instance isIso_unit_hom (S : Scheme.{0}) : IsIso (𝟙_ (Over S)).hom := by
  change IsIso (𝟙 _); infer_instance

/-- **MumfordGroupLaw, non-vacuity:** every hypothesis is met by the trivial family `F = Spec ℚ` over
`S = Spec ℚ` with `e = 𝟙` (every field fibre is the zero abelian variety). -/
theorem mumfordGroupLaw_premises_trivial :
    IsLocallyNoetherian Striv ∧ IsProper (𝟙_ (Over Striv)).hom ∧ Smooth (𝟙_ (Over Striv)).hom ∧
      GeometricallyConnected (𝟙_ (Over Striv)).hom ∧ (𝟙 Striv : Striv ⟶ (𝟙_ (Over Striv)).left) ≫
        (𝟙_ (Over Striv)).hom = 𝟙 Striv ∧
      (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Striv),
        ∃ (A : PkgI3.AbVar K) (g : A.X.left ⟶ (𝟙_ (Over Striv)).left),
          LeafQM.AV.R1UnivRigid.IsAbVarFibre (𝟙_ (Over Striv)) (𝟙 Striv) s A g) := by
  refine ⟨inferInstance, by dsimp; infer_instance, by dsimp; infer_instance, ?_, by simp, ?_⟩
  · have : GeometricallyIntegral (𝟙_ (Over Striv)).hom := by dsimp; infer_instance
    dsimp; infer_instance
  · intro K _ s
    refine ⟨PkgI3.AbVar.zero K, s, ?_, ?_⟩
    · exact IsPullback.of_vert_isIso ⟨by simp [PkgI3.AbVar.zero]⟩
    · rw [one_pt_zero_comp]; rfl

/-- **MumfordGroupLaw, sanity case (unconditional):** its conclusion holds at the trivial family. -/
theorem mumfordGroupLaw_trivial_conclusion :
    ∃ _G : GrpObj (𝟙_ (Over Striv)), η[𝟙_ (Over Striv)].left = (𝟙 Striv : Striv ⟶ (𝟙_ (Over Striv)).left) :=
  ⟨inferInstance, rfl⟩

/-- Not stronger: implied by the field it replaced (`MumfordRigidityCore`). -/
example : LeafQM.AV.R1UnivRigid.MumfordRigidityCore → ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw :=
  ZInQ.Contrib.MumfordRigidity.mumfordGroupLaw_of_core

/-- Faltings, both directions (faltings-cm). -/
example : PkgI3.FaltingsTate → ZInQ.Contrib.FaltingsCM.FaltingsTateSurj :=
  ZInQ.Contrib.FaltingsCM.faltingsTateSurj_of_faltingsTate
example : ZInQ.Contrib.FaltingsCM.FaltingsTateSurj → ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed →
    PkgI3.FaltingsTate :=
  ZInQ.Contrib.FaltingsCM.faltingsTate_of_surj

end LeafAudit1115


/-! ## 5. `NewformRepConductor` (r17-bypass) -/

namespace CarayolLevel.LeafAudit1115

open PkgI4 LadicCond C9Rhof

/-- Old from new. -/
example : NewformRepConductor → LadicCond.CarayolR17' := carayolR17'_of_newformRepConductor

/-- New from old (with R14's existence of an attached semisimple representation): not stronger. -/
example (h : LadicCond.CarayolR17')
    (hex : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (ιC : Qbar →ₐ[ℚ] ℂ) (ιL : Qbar →ₐ[ℚ] PadicAlgCl ℓ)
      (N : ℕ) (χ : DirichletCharacter ℂ N) (f : CF N 2), 0 < N → IsNewform f χ →
      ∃ ρ : GaloisRep ℓ 2, ρ.IsSemisimple ∧ ρ.AttachedTo ιC ιL f) :
    NewformRepConductor :=
  newformRepConductor_of_R17' h hex

end CarayolLevel.LeafAudit1115

/-! ## 6. `TYZLemma29PrintedNe3`, `TYZThm21At31` (h29-ne3) -/

namespace ZInQ.Contrib.TYZDecomp.H29Split.LeafAudit1115

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp NumberField
open IsDedekindDomain
open scoped Quaternion TensorProduct FiniteAdeleExtension

/-- A sign choice of `𝓛` from TYZ Theorem 1.1 (the open hypothesis `h11 : TYZThm11Integral`). -/
def lcalOf (h11 : TYZThm11Integral) (m : ℕ) : ℤ :=
  open Classical in
  if h : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) then (h11 m h.1 h.2).choose else 0

theorem isLcalSign_lcalOf (h11 : TYZThm11Integral) : IsLcalSign (lcalOf h11) := by
  intro m hm hc
  have h : Squarefree m ∧ (m % 8 = 1 ∨ m % 8 = 3) := ⟨hm, hc⟩
  unfold lcalOf
  split_ifs
  exact (h11 m h.1 h.2).choose_spec

/-- **Non-vacuity of `TYZLemma29PrintedNe3` and `TYZThm21At31`, relative to their sibling leaves**: at every
squarefree `1 < n ≡ 1, 3 (mod 8)` (e.g. `n = 3` for `TYZThm21At31`, `n = 11` for `TYZLemma29PrintedNe3`) the
quantified objects exist: an admissible `τ` (from Legendre and Jones–Pall), a nonzero test vector
(`TYZTestVectorExists`) and a sign choice `ℓ` of `𝓛` (`TYZThm11Integral`, the open hypothesis `h11`). -/
theorem tyz_premises (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16) (hT : TYZTestVectorExists)
    (h11 : TYZThm11Integral) (n : ℕ) [NeZero n] (hsq : Squarefree n) (h1 : 1 < n)
    (hcl : n % 8 = 1 ∨ n % 8 = 3) :
    ∃ (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (ℓ : ℕ → ℤ),
      AdmissibleTau n τ ∧ IsTestVector n τ f ∧ (∃ x : ℍ[AQ]ˣ, f x ≠ 0) ∧ IsLcalSign ℓ := by
  obtain ⟨τ, hτ⟩ := tyzTauExists_of_legendreJonesPall (legendreJonesPall_of hL hJ) n hsq hcl
  obtain ⟨f, hf, hx⟩ := hT n hsq h1 hcl τ hτ
  exact ⟨τ, f, lcalOf h11, hτ, hf, hx, isLcalSign_lcalOf h11⟩

theorem squarefree_three : Squarefree 3 := Nat.prime_three.squarefree
theorem squarefree_eleven : Squarefree 11 := (by norm_num : Nat.Prime 11).squarefree

example (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16) (hT : TYZTestVectorExists)
    (h11 : TYZThm11Integral) :
    ∃ (τ : QNeg 3 →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (ℓ : ℕ → ℤ),
      AdmissibleTau 3 τ ∧ IsTestVector 3 τ f ∧ (∃ x : ℍ[AQ]ˣ, f x ≠ 0) ∧ IsLcalSign ℓ :=
  tyz_premises hL hJ hT h11 3 squarefree_three (by norm_num) (Or.inr rfl)

example (hL : LegendreThreeSquares) (hJ : JonesPallX2Y2Z16) (hT : TYZTestVectorExists)
    (h11 : TYZThm11Integral) :
    ∃ (τ : QNeg 11 →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) (ℓ : ℕ → ℤ),
      AdmissibleTau 11 τ ∧ IsTestVector 11 τ f ∧ (∃ x : ℍ[AQ]ˣ, f x ≠ 0) ∧ IsLcalSign ℓ :=
  tyz_premises hL hJ hT h11 11 squarefree_eleven (by norm_num) (Or.inr rfl)

/-- **Not stronger (1/2):** h29-fix's `TYZLemma29Printed` (the `w_K` form it replaces) implies the new print
`TYZLemma29PrintedNe3`. -/
theorem ne3_of_printed (h : TYZLemma29Printed) : TYZLemma29PrintedNe3 := by
  intro n _ hsq h1 h3 hcl τ hτ f hf ℓ hℓ
  obtain ⟨ε, hε, he⟩ := h n hsq h1 hcl τ hτ f hf ℓ hℓ
  refine ⟨ε, hε, ?_⟩
  have hw : wK n = 1 := by simp [wK, h3]
  rw [hw, one_mul] at he
  exact he

/-- **Not stronger (2/2):** `TYZLemma29Printed` implies `TYZThm21At31`. -/
theorem thm21At31_of_printed (h : TYZLemma29Printed) : TYZThm21At31 := by
  intro τ hτ f hf ℓ hℓ
  obtain ⟨ε, hε, he⟩ := h 3 squarefree_three (by norm_num) (Or.inr rfl) τ hτ f hf ℓ hℓ
  refine ⟨ε 1, hε 1, ?_⟩
  rw [pairIdx_three_eq, Finset.sum_singleton, Nat.div_one, wK_three_eq_torsionOrder,
    genusPeriodTV_three] at he
  rw [← he]
  ring

/-- The two new leaves are equivalent to h29-fix's `TYZLemma29Printed` (with h29-ne3's
`tyzLemma29Printed_of_ne3_thm21`). -/
theorem printed_iff : TYZLemma29Printed ↔ TYZLemma29PrintedNe3 ∧ TYZThm21At31 :=
  ⟨fun h => ⟨ne3_of_printed h, thm21At31_of_printed h⟩,
    fun h => tyzLemma29Printed_of_ne3_thm21 h.1 h.2⟩

end ZInQ.Contrib.TYZDecomp.H29Split.LeafAudit1115

/-! ## 10. `X0ModuliGaloisMero` (gz-heegner) -/

namespace ZInQ.GZHeegner.LeafAudit1115

open UpperHalfPlane Complex
open ZInQ.Contrib.TYZGenus.Shimura ZInQ.Contrib.TYZGenus.CM HeckeRing.GL2 WeierstrassCurve
  ZInQ.Contrib.TYZDecomp.CurveA

theorem pp_I : T5Glue.pp UpperHalfPlane.I = ZInQ.GZWeil.squarePP := rfl

theorem jL_pp_I : T5Glue.jL (T5Glue.pp UpperHalfPlane.I) = 1728 := by
  rw [pp_I, T5Glue.jL, T5Glue.discL, ZInQ.GZWeil.g₃_squarePP]
  have h2 := ZInQ.GZWeil.g₂_ne_zero_of_g₃_eq_zero _ ZInQ.GZWeil.g₃_squarePP
  field_simp
  ring

theorem isRatModFnMero_one : IsRatModFnMero 1 (fun _ => (1 : ℂ)) := by
  refine ⟨fun γ _ τ => rfl, fun τ => analyticAt_const.meromorphicAt, fun γ => ⟨0, ?_⟩,
    ⟨0, fun n => if n = 0 then 1 else 0, 0, fun τ _ => ?_⟩⟩
  · simp only [CharP.cast_eq_zero, mul_zero, zero_mul, Real.exp_zero]
    exact Asymptotics.isBigO_const_const _ one_ne_zero _
  · rw [pow_zero, one_mul]
    convert hasSum_single (f := fun n : ℕ => ((if n = 0 then 1 else 0 : ℚ) : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * τ) ^ n) 0 (fun b hb => by simp [hb]) using 1
    simp

/-- **Non-vacuity of `X0ModuliGaloisMero`:** all its hypotheses are met at `N = 1`, `g = 1`, `σ = id`,
`τ = τ' = i`, `μ = 1` (the moduli coordinate `j(i) = 1728` is algebraic). -/
theorem x0ModuliGaloisMero_premises :
    ∃ (g : UpperHalfPlane → ℂ) (σ : ℂ ≃+* ℂ) (τ τ' : UpperHalfPlane) (μ : ℂ),
      IsRatModFnMero 1 g ∧ RegularAt g τ ∧ RegularAt g τ' ∧
      (∀ i < 1, ∃ a : Qbar, ιC a = T5Glue.modCoord 1 τ i) ∧
      T5Glue.IsConjModel (σ : ℂ →+* ℂ) (T5Glue.pp τ) (T5Glue.pp τ') μ := by
  refine ⟨fun _ => 1, RingEquiv.refl ℂ, UpperHalfPlane.I, UpperHalfPlane.I, 1, isRatModFnMero_one,
    analyticAt_const, analyticAt_const, fun i hi => ⟨1728, ?_⟩, ⟨one_ne_zero, by simp, by simp⟩⟩
  obtain rfl : i = 0 := by omega
  rw [T5Glue.modCoord_zero, jL_pp_I, map_ofNat]

end ZInQ.GZHeegner.LeafAudit1115

/-! ## 7. `MainTheoremCM` (qmrec-printed) -/

namespace QMRecPrinted.LeafAudit1115

/-- Old from new: the leaf (with the textbook leaves already in the bundles) gives `QMReciprocityL3` and the
field `rayClassCMAb`. The proof of `qmReciprocityL3_of_printed` instantiates every hypothesis of the leaf at the
route's instance (`E = K(√2)` with its CM-field instance `isCMField_EK`, the reflex datum, the QM surface's
uniformization and type), which is the non-vacuity check at the route. -/
example : MainTheoremCM → ZInQ.HomUnify.HomLatticeCorr → ShimuraSplit2.QMReciprocityL3 :=
  qmReciprocityL3_of_printed

#check @rayClassCMAb_of_mainCM

end QMRecPrinted.LeafAudit1115

/-! ## 8. `PanPrinted`, `BergerPrinted` (pb-bypass) -/

namespace HDec.PkgI4.PanBergerSplit.LeafAudit1115

/-- Old from new. -/
example : PanPrinted → BergerPrinted → PanBerger := panBerger_of_printed

/-- Sanity case (pb-bypass): the trivial representation is potentially semistable. -/
example (p : ℕ) [Fact p.Prime] : IsPst p (1 : GQp p →* GL (Fin 1) ℚ_[p]) := isPst_trivial p

end HDec.PkgI4.PanBergerSplit.LeafAudit1115

/-! ## 9. `ShimuraIntegralModelUsed` (sir-printed) -/

namespace SIRPrinted.LeafAudit1115

/-- Not stronger: implied by the field it replaces. -/
example : SGRSplit.ShimuraIntegralModelRep → ShimuraIntegralModelUsed := shimuraIntegralModelUsed_of_rep

/-- Enough for the consumer. -/
example : ShimuraIntegralModelUsed → HDec.CurveSplitGR.ShimuraGoodReductionNoGuard :=
  shimuraGoodReductionNoGuard_of_used

end SIRPrinted.LeafAudit1115

/-! ## 11. `GrossZagierFormulaCd`, `GrossConjugationCd` (gz-weil) -/

namespace ZInQ.GZWeil.LeafAudit1115

/-- With gz-hl3's composite `HeegnerPointRationalCd`, the two leaves give the `C_d` form of `hL3`. -/
example : ZInQ.GZHL3.HeegnerPointRationalCd → ZInQ.GZHL3.GrossZagierFormulaCd →
    ZInQ.GZHL3.GrossConjugationCd → ZInQ.GZStatements.GrossZagierHeegnerCd :=
  grossZagierHeegnerCd_of_threeLeaves

/-- Not stronger than gz-hl3's general leaves (restrictions to `C_d`). -/
example : ZInQ.GZHL3.GrossZagierFormula → ZInQ.GZHL3.GrossZagierFormulaCd := ZInQ.GZHL3.grossZagierFormulaCd_of
example : ZInQ.GZHL3.GrossConjugation → ZInQ.GZHL3.GrossConjugationCd := ZInQ.GZHL3.grossConjugationCd_of

/-- `X0ModuliGaloisMero` implies the kernel's `hX`, and with `ShimuraMainCM` gives gz-hl3's composite. -/
example : ZInQ.GZHeegner.X0ModuliGaloisMero → T5Glue.X0ModuliGalois := ZInQ.GZHeegner.x0ModuliGalois_of_mero
example : T5Glue.ShimuraMainCM → ZInQ.GZHeegner.X0ModuliGaloisMero → ZInQ.GZHL3.HeegnerPointRational :=
  ZInQ.GZHeegner.heegnerPointRational_of_printed

end ZInQ.GZWeil.LeafAudit1115

end

#print axioms LeafAudit1115.not_linYangEx29All
#print axioms LeafAudit1115.jtheta_real_of_leaves
#print axioms HDec.QMSplit.Moduli.ElkiesCoord.LeafAudit1115.ff_premises_of_charts
#print axioms LeafAudit1115.mumfordGroupLaw_premises_trivial
#print axioms LeafAudit1115.mumfordGroupLaw_trivial_conclusion
#print axioms LeafAudit1115.faltingsTateSurj_zero
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.LeafAudit1115.tyz_premises
#print axioms ZInQ.Contrib.TYZDecomp.H29Split.LeafAudit1115.printed_iff
#print axioms ZInQ.GZHeegner.LeafAudit1115.x0ModuliGaloisMero_premises
