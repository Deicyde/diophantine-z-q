import ZInQKernel.Contrib.OneProof.QuotientP1Printed
import ZInQKernel.Contrib.OneProof.QuotientP1.P1ModelE
import ZInQKernel.Contrib.OneProof.QuotientP1.TameQuotSmooth
import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used

/-!
# p1-quot3, L4 part F: `quotientP1Coordinate` without L4 (scratch)
-/

noncomputable section

namespace HDec

set_option maxHeartbeats 1000000

attribute [-instance] TauCeti.FinitePadicExtension.toAlgebra
  TauCeti.FinitePadicExtension.ofInstances TauCeti.FinitePadicExtension.toModuleFinite
  TauCeti.FinitePadicExtension.toValuativeExtension

namespace MCRQuot

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM LeafQM.AV VertWitness HeckeRestNV
open G0ModField PropTSRed PropTSGlue ModelGlue MCRGlue LeafQM.AV.Pin PkgI3

/-! ## Values of a chart structure at field points -/

section Values

variable {K : Type} [Field K] {X : Scheme.{0}}

theorem val_zero (σ : ToP1 X) (z : Spec (CommRingCat.of K) ⟶ X) (h : σ.val z = OnePoint.some 0) :
    ptOf z ∈ σ.U ∧ ptOf z ∉ X.basicOpen σ.f := by
  by_cases hz : ptOf z ∈ σ.U
  · rw [val_of_mem σ z hz] at h
    exact ⟨hz, (ev_eq_zero_iff z hz σ.f).1 (OnePoint.coe_injective h)⟩
  · rw [val_of_not_mem σ z hz] at h
    exact absurd h (OnePoint.infty_ne_coe _)

theorem val_infty (σ : ToP1 X) (z : Spec (CommRingCat.of K) ⟶ X) (h : σ.val z = OnePoint.infty) :
    ptOf z ∉ σ.U := by
  intro hz
  rw [val_of_mem σ z hz] at h
  exact OnePoint.coe_ne_infty _ h

theorem val_const (σ : ToP1 X) (Z : Over (Spec (CommRingCat.of ℚ))) (hZ : Z.left = X)
    (z : Spec (CommRingCat.of K) ⟶ Z.left) (σ' : ToP1 Z.left) (c : ℚ) [Algebra ℚ K]
    (h : σ'.val z = OnePoint.some (algebraMap ℚ K c)) :
    ptOf z ∈ σ'.U ∧ ptOf z ∉ Z.left.basicOpen
      (σ'.f - baseToSectionsOver (CommRingCat.of ℚ) Z σ'.U c) := by
  by_cases hz : ptOf z ∈ σ'.U
  · rw [val_of_mem σ' z hz] at h
    refine ⟨hz, (ev_eq_zero_iff z hz _).1 ?_⟩
    have h1 : ev z hz σ'.f = algebraMap ℚ K c := OnePoint.coe_injective h
    have h2 : ev z hz (baseToSectionsOver (CommRingCat.of ℚ) Z σ'.U c) = algebraMap ℚ K c := by
      have := RingHom.ext_rat ((ev z hz).comp (baseToSectionsOver (CommRingCat.of ℚ) Z σ'.U))
        (algebraMap ℚ K)
      exact congrArg (fun φ => φ c) this
    rw [map_sub, h1, h2, sub_self]
  · rw [val_of_not_mem σ' z hz] at h
    exact absurd h (OnePoint.infty_ne_coe _)

end Values

/-- `−16/27` as a unit of `ℤ_(p)` (`p > 3`). -/
theorem exists_c (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    ∃ c : Zloc p, IsUnit c ∧ zlocToRat p c = -16 / 27 := by
  have h27 : ¬ p ∣ 27 := by
    intro h
    have : p ∣ 3 ^ 3 := by norm_num; exact h
    have := (Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) this)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h16 : ¬ p ∣ 16 := by
    intro h
    have : p ∣ 2 ^ 4 := by norm_num; exact h
    have := (Nat.Prime.dvd_of_dvd_pow (Fact.out : p.Prime) this)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  obtain hu27 := MCRGlue.TameQuotScheme.isUnit_card_Zloc p 27 h27
  obtain hu16 := MCRGlue.TameQuotScheme.isUnit_card_Zloc p 16 h16
  refine ⟨-((16 : ℕ) : Zloc p) * ↑hu27.unit⁻¹, (hu16.neg).mul hu27.unit⁻¹.isUnit, ?_⟩
  rw [map_mul, map_neg, map_natCast, map_units_inv, IsUnit.unit_spec, map_natCast]
  norm_num

/-- **Glue C2 without the coordinate `ρ'₀` (that is, without L4)**: `CoordinateFromSections` with the hypothesis
`IsP1Coordinate 𝒵 ρ'₀` removed and `𝒵` integral. -/
def CoordinateFromSectionsGen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 324 < p →
    ∀ (𝒴 : Over (Spec (CommRingCat.of (Zloc p)))) (𝒜 : QMFamily 𝒴.left), IsShimuraModel p 𝒴 𝒜 →
    CMObjectsExist →
    ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
      R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (𝒵 : Over (Spec (CommRingCat.of (Zloc p)))) (q : 𝒴 ⟶ 𝒵),
      IsGQuotient (fibreAut 𝒴 𝒜) q.left → IsFinite q.left →
      IsProper 𝒵.hom → SmoothOfRelativeDimension 1 𝒵.hom → IsIntegral 𝒵.left →
    (∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM3 P'.q) ∨ (HasCM4 P.q ∧ HasCM24 P'.q) ∨ (HasCM3 P.q ∧ HasCM24 P'.q)) →
      Disjoint (closure ({q.left (qbarPoint y)} : Set 𝒵.left)) (closure {q.left (qbarPoint y')})) →
    ∃ ρ' : ToP1 𝒵.left, IsP1Coordinate 𝒵 ρ' ∧ CoordFibres 𝒴 𝒜 (ρ'.comp q.left)

/-- **`CoordinateFromSectionsGen` from T5, glue A, (B-desc) and (B-iso)**: the generic coordinate `σ'` (the descent
of `π`) takes the values `0, ∞, −16/27` at the three CM points, whose sections are pairwise disjoint, so it extends
to `P¹_{ℤ_(p)}` (`P1Model.exists_p1Coordinate`, no L4). -/
theorem coordinateFromSectionsGen_of (hA : FibreAutTame) (hT : ObjBridge.TorsionStructure)
    (hD : QuotientDescendsQ) (hB : ToP1BijIsCoordinateQ) : CoordinateFromSectionsGen := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf hZp hZs hZI hdisj
  obtain ⟨hfin, htame⟩ := hA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  have hinvq := hq.1
  obtain ⟨g, hg, -⟩ := exists_genFib_to_Y hM h1
  have huniq : ∀ (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y P' → M3.mk P = M3.mk P' := by
    intro y P P' hP hP'
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    rw [← hg Qbar s P ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP),
      ← hg Qbar s P' ((congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP')]
  choose fib hfib using fun y => hM.2.2.1 Qbar y
  set j := pullback.fst 𝒴.hom (specRatToZloc p)
  let σ : ToP1 (genFib 𝒴).left := π.comp g.left
  have hσ : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, σ.val (K := Qbar) s.left = π.val (K := Qbar) (s ≫ g).left :=
    fun s => ToP1.val_comp_right π g.left s.left
  have hrel : ∀ s s' : fieldPt Qbar ⟶ genFib 𝒴,
      (σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left ↔
        TwistEq (fib (s.left ≫ j)) (fib (s'.left ≫ j))) := by
    intro s s'
    rw [hσ, hσ]
    exact (h2 (s ≫ g) (s' ≫ g) _ _ (hg Qbar s _ (hfib _)) (hg Qbar s' _ (hfib _))).1
  have hinvσ : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (h : Aut 𝒴.left), h ∈ fibreAut 𝒴 𝒜 →
      s'.left ≫ j = s.left ≫ j ≫ h.asIso.hom →
      σ.val (K := Qbar) s.left = σ.val (K := Qbar) s'.left := by
    intro s s' h hh e
    refine (hrel s s').2 (twistEq_of_mem_fibreAut hM huniq hh (s.left ≫ j) _ _ (hfib _) ?_)
    exact (congrArg (fun t => IsFibreOf 𝒜 t (fib (s'.left ≫ j)))
      (e.trans (Category.assoc _ _ _).symm)).mp (hfib _)
  obtain ⟨σ', hσ', hlift⟩ := hD p 𝒴 𝒵 q (fibreAut 𝒴 𝒜) hM.1 hM.2.1 hfin (fibreAut_over 𝒴 𝒜) hq hqf σ hinvσ
  have k : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, (s ≫ genFibMap q).left ≫
      pullback.fst 𝒵.hom (specRatToZloc p) = (s.left ≫ j) ≫ q.left := fun s =>
    (Category.assoc _ _ _).trans ((congrArg (s.left ≫ ·) (genFibMap_fst q)).trans
      (Category.assoc _ _ _).symm)
  have hσ'Q : IsP1CoordinateQ (genFib 𝒵) σ' := by
    refine hB (genFib 𝒵) (genFib_isProper 𝒵 hZp) (genFib_smooth 𝒵 hZs) σ' ⟨?_, ?_⟩
    · intro t t' htt
      obtain ⟨s, rfl⟩ := hlift t
      obtain ⟨s', rfl⟩ := hlift t'
      simp only [hσ'] at htt
      obtain ⟨h, hhG, hh⟩ := mem_orbit_of_twistEq hT hM (s.left ≫ j) (s'.left ≫ j) _ _ (hfib _)
        (hfib _) ((hrel s s').1 htt)
      apply genFib_pt_inj 𝒵
      refine (k s).trans ((k s').trans ?_).symm
      exact (congrArg (· ≫ q.left) hh).trans ((Category.assoc _ _ _).trans
        (congrArg ((s.left ≫ j) ≫ ·) (hinvq h hhG)))
    · intro v
      obtain ⟨y0⟩ := hM.2.2.2.2.2.2.2
      obtain ⟨s0, -⟩ := genFib_pt 𝒴 y0
      have hfin' : ∀ s : fieldPt Qbar ⟶ genFib 𝒴, {s' : fieldPt Qbar ⟶ genFib 𝒴 |
          σ.val (K := Qbar) s'.left = σ.val (K := Qbar) s.left}.Finite := by
        intro s
        have hT' := twistClassFinite hT (fib (s.left ≫ j))
        refine Set.Finite.of_finite_image (f := fun s' => M3.mk (fib (s'.left ≫ j)))
          (hT'.subset ?_) ?_
        · rintro _ ⟨s', hs', rfl⟩
          exact ⟨_, rfl, (hrel s s').1 hs'.symm⟩
        · intro a _ b _ hab
          exact genFib_pt_inj 𝒴 a b (hM.2.2.2.1 _ _ _ _ (hfib _) (hfib _) hab)
      obtain ⟨s, hs⟩ := _root_.LeafQM.AV.Pin.curveFacts.2 (genFib 𝒴) (genFib_isProper 𝒴 hM.1)
        (genFib_smooth 𝒴 hM.2.1) ⟨s0⟩ σ hfin' v
      exact ⟨s ≫ genFibMap q, (hσ' s).trans hs⟩
  -- q-fibres and twist classes (coordinateFromSections_of)
  have horb : ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' → (y ≫ q.left = y' ≫ q.left ↔ TwistEq P P') := by
    intro y y' P P' hP hP'
    constructor
    · intro e
      obtain ⟨h, hhG, rfl⟩ := exists_eq_comp_of_isGQuotient hq y y' e
      exact twistEq_of_mem_fibreAut hM huniq hhG y P P' hP hP'
    · intro hte
      obtain ⟨h, hhG, rfl⟩ := mem_orbit_of_twistEq hT hM y y' P P' hP hP' hte
      rw [Category.assoc, hinvq h hhG]
  have hR2 : ∀ (s s' : fieldPt Qbar ⟶ genFib 𝒴) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P →
        IsFibreOf 𝒜 (s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P' →
      (π.val (K := Qbar) (s ≫ g).left = π.val (K := Qbar) (s' ≫ g).left ↔ TwistEq P P') ∧
      (HasCM4 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.some 0) ∧
      (HasCM3 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.infty) ∧
      (HasCM24 P.q → π.val (K := Qbar) (s ≫ g).left = OnePoint.some (-16 / 27)) :=
    fun s s' P P' hP hP' => h2 (s ≫ g) (s' ≫ g) P P' (hg Qbar s P hP) (hg Qbar s' P' hP')
  have hsameCM : ∀ (y y' : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left) (P P' : QML3 Qbar),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜 y' P' →
      ((HasCM4 P.q ∧ HasCM4 P'.q) ∨ (HasCM3 P.q ∧ HasCM3 P'.q) ∨
        (HasCM24 P.q ∧ HasCM24 P'.q)) → y ≫ q.left = y' ≫ q.left := by
    intro y y' P P' hP hP' hcm
    obtain ⟨s, hs⟩ := genFib_pt 𝒴 y
    obtain ⟨s', hs'⟩ := genFib_pt 𝒴 y'
    have hP2 : IsFibreOf 𝒜 (s.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P :=
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs).mpr hP
    have hP2' : IsFibreOf 𝒜 (s'.left ≫ pullback.fst 𝒴.hom (specRatToZloc p)) P' :=
      (congrArg (fun t => IsFibreOf 𝒜 t _) hs').mpr hP'
    obtain ⟨hrel', c4, c3, c2⟩ := hR2 s s' P P' hP2 hP2'
    obtain ⟨-, c4', c3', c2'⟩ := hR2 s' s P' P hP2' hP2
    refine (horb y y' P P' hP hP').2 (hrel'.1 ?_)
    rcases hcm with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · rw [c4 a, c4' b]
    · rw [c3 a, c3' b]
    · rw [c2 a, c2' b]
  -- the three CM points and their generic coordinates
  obtain ⟨⟨P4, c4⟩, ⟨P3, c3⟩, ⟨P2, c2⟩⟩ := hCM
  obtain ⟨y4, hy4⟩ := hM.2.2.2.2.1 P4
  obtain ⟨y3, hy3⟩ := hM.2.2.2.2.1 P3
  obtain ⟨y2, hy2⟩ := hM.2.2.2.2.1 P2
  obtain ⟨s4, hs4⟩ := genFib_pt 𝒴 y4
  obtain ⟨s3, hs3⟩ := genFib_pt 𝒴 y3
  obtain ⟨s2, hs2⟩ := genFib_pt 𝒴 y2
  have hP4 : IsFibreOf 𝒜 (s4.left ≫ j) P4 := (congrArg (fun t => IsFibreOf 𝒜 t _) hs4).mpr hy4
  have hP3 : IsFibreOf 𝒜 (s3.left ≫ j) P3 := (congrArg (fun t => IsFibreOf 𝒜 t _) hs3).mpr hy3
  have hP2' : IsFibreOf 𝒜 (s2.left ≫ j) P2 := (congrArg (fun t => IsFibreOf 𝒜 t _) hs2).mpr hy2
  have hv4 : σ'.val (K := Qbar) (s4 ≫ genFibMap q).left = OnePoint.some 0 := by
    rw [hσ', hσ]; exact (hR2 s4 s4 P4 P4 hP4 hP4).2.1 c4
  have hv3 : σ'.val (K := Qbar) (s3 ≫ genFibMap q).left = OnePoint.infty := by
    rw [hσ', hσ]; exact (hR2 s3 s3 P3 P3 hP3 hP3).2.2.1 c3
  have hv2 : σ'.val (K := Qbar) (s2 ≫ genFibMap q).left = OnePoint.some (-16 / 27) := by
    rw [hσ', hσ]; exact (hR2 s2 s2 P2 P2 hP2' hP2').2.2.2 c2
  -- points of the generic fibre of `𝒵`
  set t4 := (s4 ≫ genFibMap q).left
  set t3 := (s3 ≫ genFibMap q).left
  set t2 := (s2 ≫ genFibMap q).left
  have hjt : ∀ (s : fieldPt Qbar ⟶ genFib 𝒴) (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left),
      s.left ≫ j = y → (s ≫ genFibMap q).left ≫ P1Model.jj 𝒵 = y ≫ q.left := by
    intro s y hs
    rw [← hs]; exact k s
  have hj4 := hjt s4 y4 hs4
  have hj3 := hjt s3 y3 hs3
  have hj2 := hjt s2 y2 hs2
  have hpt : ∀ (t : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒵).left)
      (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left), t ≫ P1Model.jj 𝒵 = y ≫ q.left →
      P1Model.jj 𝒵 (ptOf t) = q.left (qbarPoint y) := by
    intro t y ht
    change qbarPoint (t ≫ P1Model.jj 𝒵) = _
    rw [ht]; rfl
  obtain ⟨hy0U, hy0⟩ := val_zero σ' t4 hv4
  have hyinf := val_infty σ' t3 hv3
  obtain ⟨c, hcu, hcv⟩ := exists_c p (by omega)
  have hv2' : σ'.val (K := Qbar) t2 = OnePoint.some (algebraMap ℚ Qbar (zlocToRat p c)) := by
    rw [hcv, hv2]; congr 1; simp
  obtain ⟨hycU, hycv⟩ := val_const σ' (genFib 𝒵) rfl t2 σ' (zlocToRat p c) hv2'
  have hcl : ∀ (t : Spec (CommRingCat.of Qbar) ⟶ (genFib 𝒵).left)
      (y : Spec (CommRingCat.of Qbar) ⟶ 𝒴.left), t ≫ P1Model.jj 𝒵 = y ≫ q.left →
      ∀ x ∈ closure {P1Model.jj 𝒵 (ptOf t)}, 𝒵.hom x ≠ P1Model.s0 p → x = P1Model.jj 𝒵 (ptOf t) := by
    intro t y ht x hx hxs
    haveI := P1Model.zloc_isDVR' (p := p)
    have hb : 𝒵.hom x = ⟨⊥, Ideal.isPrime_bot⟩ :=
      PrimeSpectrum.ext (QuotientP1Proof.asIdeal_eq_bot_of_ne_closedPoint _ _ hxs)
    have hpt' : P1Model.jj 𝒵 (ptOf t) = qbarPoint (t ≫ P1Model.jj 𝒵) := rfl
    rw [hpt'] at hx ⊢
    exact eq_of_specializes_generic 𝒵 _ x hb (specializes_iff_mem_closure.mpr hx)
  have d43 := hdisj y4 y3 P4 P3 hy4 hy3 (Or.inl ⟨c4, c3⟩)
  have d42 := hdisj y4 y2 P4 P2 hy4 hy2 (Or.inr (Or.inl ⟨c4, c2⟩))
  have d32 := hdisj y3 y2 P3 P2 hy3 hy2 (Or.inr (Or.inr ⟨c3, c2⟩))
  rw [← hpt t4 y4 hj4, ← hpt t3 y3 hj3] at d43
  rw [← hpt t4 y4 hj4, ← hpt t2 y2 hj2] at d42
  rw [← hpt t3 y3 hj3, ← hpt t2 y2 hj2] at d32
  obtain ⟨ρ, hρ, hval⟩ := P1Model.exists_p1Coordinate 𝒵 σ' hσ'Q (ptOf t4) (ptOf t3) (ptOf t2) c
    hcu hy0U hy0 hyinf hycU hycv (hcl t4 y4 hj4) (hcl t3 y3 hj3) d43 d42.symm d32.symm
  have v4 : ρ.val (y4 ≫ q.left) = OnePoint.some 0 := by rw [← hj4]; exact (hval Qbar t4).trans hv4
  have v3 : ρ.val (y3 ≫ q.left) = OnePoint.infty := by rw [← hj3]; exact (hval Qbar t3).trans hv3
  have v2 : ρ.val (y2 ≫ q.left) = OnePoint.some (-16 / 27) := by
    rw [← hj2]; exact (hval Qbar t2).trans hv2
  refine ⟨ρ, hρ, ?_⟩
  intro y y' P Q hP hQ
  rw [ToP1.val_comp_right, ToP1.val_comp_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Iff.trans ?_ (horb y y' P Q hP hQ)
    exact ⟨fun e => val_injective_of_isP1Coordinate hρ _ _ e, fun e => by rw [e]⟩
  · intro h4
    rw [hsameCM y y4 P P4 hP hy4 (Or.inl ⟨h4, c4⟩), v4]
  · intro h3
    rw [hsameCM y y3 P P3 hP hy3 (Or.inr (Or.inl ⟨h3, c3⟩)), v3]
  · intro h24
    rw [hsameCM y y2 P P2 hP hy2 (Or.inr (Or.inr ⟨h24, c2⟩)), v2]

/-- **`QuotientP1Coordinate` from Lichtenbaum's theorem, mcr-glue's L2, L3, Edixhoven's theorem, T5,
`HeckeIrreducible` and `CMStabObjWeak` — without L4 `SmoothModelOfP1`.** As p1-quot2's
`quotientP1Coordinate_of_printed2`, with `coordinateFromSections_of''` (which needs L4's coordinate `ρ'₀`) replaced by
`coordinateFromSectionsGen_of` (the generic coordinate extends across the special fibre because the three CM sections
are pairwise disjoint). -/
theorem quotientP1Coordinate_of_printed3 (hL : _root_.QuotientP1Proof.LichtenbaumProjective)
    (hQE : FiniteQuotientExists) (hTS : TameQuotientSmooth)
    (hE : EdixhovenFixedSmooth2) (hT : PkgI2.TorsionStructure.{0}) (hYI : PropTSGlue.HeckeIrreducible)
    (hO : CMStabObjWeak) : MCRGlue.QuotientP1Coordinate := by
  intro p _ hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  have hC : CurveBijIso := _root_.CurveSplit.curveBijIso
  have hfix : FibreAutFixFinite := fibreAutFixFinite_of' hC hYI
  have gA : FibreAutTame := fibreAutTame_of' hT hfix
  obtain ⟨hfin, hnd⟩ := gA p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2
  have hover := fibreAut_over 𝒴 𝒜
  haveI : IsIntegral 𝒴.left := isIntegral_model hC hYI hM h1 hh h2
  haveI : IsDiscreteValuationRing (Zloc p) := zloc_isDVR p
  haveI : IsProper 𝒴.hom := hM.1
  haveI : SmoothOfRelativeDimension 1 𝒴.hom := hM.2.1
  have hAF : ∀ s : Finset 𝒴.left, ∃ W : 𝒴.left.Opens, IsAffineOpen W ∧ ∀ x ∈ s, x ∈ W :=
    fun s => _root_.QuotientP1Proof.exists_affine_of_lichtenbaum hL 𝒴.hom s
  obtain ⟨𝒵, q, hq, hqf⟩ := hQE p 𝒴 hM.1 hAF (fibreAut 𝒴 𝒜) hfin hover
  obtain ⟨hZp, hZs⟩ := hTS p 𝒴 𝒵 q hM.1 hM.2.1 _ hfin hnd hover hq hqf
  -- the quotient is integral
  haveI := hqf
  haveI : SmoothOfRelativeDimension 1 𝒵.hom := hZs
  haveI : Smooth 𝒵.hom := SmoothOfRelativeDimension.smooth 1 _
  haveI : Surjective q.left := QuotProper.surjective_of_isGQuotient _ q.left hq
  haveI : IrreducibleSpace 𝒵.left := q.left.surjective.irreducibleSpace q.left.continuous
  haveI : IsReduced 𝒵.left := by
    haveI : ∀ x : 𝒵.left, _root_.IsReduced (𝒵.left.presheaf.stalk x) := fun x => by
      obtain ⟨h1, -⟩ :=
        ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
          (Zloc p) 𝒵.hom x
      infer_instance
    exact isReduced_of_isReduced_stalk 𝒵.left
  haveI : IsIntegral 𝒵.left := isIntegral_of_irreducibleSpace_of_isReduced 𝒵.left
  obtain ⟨ρ', hρ', hCF⟩ := coordinateFromSectionsGen_of gA hT quotientDescendsQ
    (toP1BijIsCoordinateQ_of hC p1SchemeQ) p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf hZp hZs
    inferInstance (cMSectionsDisjoint'_of hE gA hfix gQuotientPointOrbits (cMStabNontrivial_of hO)
      qbarPointsConjugate p hp 𝒴 𝒜 hM hCM Y Φ π h1 hh h2 𝒵 q hq hqf)
  exact ⟨𝒵, q, ρ', hqf, hρ', hCF⟩

/-- **`QuotientP1Coordinate` from Lichtenbaum's theorem, mcr-glue's L2, Edixhoven's theorem and the chain's fields**
(L3 proved from `regularSmoothPerfect`; L4 bypassed). -/
theorem quotientP1Coordinate_of_fields5 (hL : _root_.QuotientP1Proof.LichtenbaumProjective)
    (hQE : FiniteQuotientExists) (hE : EdixhovenFixedSmooth2)
    (hRS : _root_.CurveSplit.RegularSmoothPerfect) (hMT : _root_.AvSplit.MumfordTorsionAlgClosed)
    (hM : _root_.ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw)
    (hU3 : _root_.RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (hU : _root_.BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : _root_.ZInQ.HomLattice.GAGAMorphism) : MCRGlue.QuotientP1Coordinate :=
  quotientP1Coordinate_of_printed3 hL hQE (tameQuotientSmooth_of_regularSmoothPerfect hRS) hE
    (_root_.AvSplit.torsionStructure_of_mumford hMT)
    (TSHecke.heckeIrreducible_of_connected (_root_.DCY3Used.y3Connected_of_leaves hM hU3))
    (cMStabObjWeak_of_fields hU hG hMT)

end MCRQuot

end HDec
