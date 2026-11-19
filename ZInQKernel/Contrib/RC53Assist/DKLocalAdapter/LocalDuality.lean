import ZInQKernel.Contrib.RC53Assist.DKLocalAdapter.GlobalTraceLeaf
import ZInQKernel.Contrib.RC53Assist.IntegralDuality.TorsionFreeDualExactness

/-!
# Transport of the literal integral local Kummer duality map

References: `diophantine_zq.tex`, lines 3413–3463;
Milne, *Arithmetic Duality Theorems*, I.2.3 and I.3.4;
Nekovář, *Selmer complexes*, 5.4.1 and 6.3.1.
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.RC53Assist.DKLocalAdapter

open CategoryTheory HomologicalComplex NumberField IsDedekindDomain
open HomologySequence ComposableArrows Abelian
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality
open ZInQ.Contrib.CloudB3RC53.Torsion
open ZInQ.Contrib.RC53Assist.IntegralDuality
open ZInQ.Contrib.RC53Assist.DerivedKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual
open ZInQ.Manuscript.RC.SelmerComplex

section CycleComparison

/-- Kind: proved algebraic theorem; the last-term cohomological five
lemma for short exact cochain sequences (Nekovář 1.1.3). -/
theorem quasiIso_third_of_first_second {C : Type*} [Category C] [Abelian C]
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)} (φ : S₁ ⟶ S₂)
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
    (h₁ : QuasiIso φ.τ₁) (h₂ : QuasiIso φ.τ₂) : QuasiIso φ.τ₃ := by
  have i₁ : ∀ n, IsIso (homologyMap φ.τ₁ n) := fun n =>
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  have i₂ : ∀ n, IsIso (homologyMap φ.τ₂ n) := fun n =>
    (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hrel : (ComplexShape.up ℤ).Rel n (n + 1) := by simp
  have hm : Mono (homologyMap φ.τ₃ n) := by
    have := i₁ n
    have := i₂ n
    have := i₁ (n + 1)
    exact mono_of_epi_of_mono_of_mono
      ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ n (n + 1) hrel))
      (composableArrows₅_exact hS₁ n (n + 1) hrel).δlast.δlast
      (composableArrows₅_exact hS₂ n (n + 1) hrel).δlast.δlast
      (inferInstanceAs (Epi (homologyMap φ.τ₁ n)))
      (inferInstanceAs (Mono (homologyMap φ.τ₂ n)))
      (inferInstanceAs (Mono (homologyMap φ.τ₁ (n + 1))))
  have he : Epi (homologyMap φ.τ₃ n) := by
    have := i₂ n
    have := i₁ (n + 1)
    have := i₂ (n + 1)
    exact epi_of_epi_of_epi_of_mono
      ((δ₀Functor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ n (n + 1) hrel))
      (composableArrows₅_exact hS₁ n (n + 1) hrel).δ₀.δlast
      (composableArrows₅_exact hS₂ n (n + 1) hrel).δ₀.δlast
      (inferInstanceAs (Epi (homologyMap φ.τ₂ n)))
      (inferInstanceAs (Epi (homologyMap φ.τ₁ (n + 1))))
      (inferInstanceAs (Mono (homologyMap φ.τ₂ (n + 1))))
  exact isIso_of_mono_of_epi _

universe u
variable {R : Type u} [CommRing R] {A B : GCx R}

/-- Kind: proved algebraic theorem; exactness of the literal shifted
cone detects the same map's quasi-isomorphy (Nekovář 1.1.3). -/
theorem quasiIso_of_cone_exact (f : GHom A B) (hc : GAcyclic (coneCx f)) :
    QuasiIso (GHom.toCC f) := by
  have h₁ : QuasiIso (coneSESHom f).τ₁ := by
    change QuasiIso (GHom.toCC (idGHom (shiftDown B)))
    rw [toCC_idGHom]
    infer_instance
  have h₂ : QuasiIso (coneSESHom f).τ₂ :=
    quasiIso_of_acyclic _ ((acyclic_toCC_iff _).2 hc)
      ((acyclic_toCC_iff _).2 (coneCx_id_acyclic B))
  exact quasiIso_third_of_first_second (coneSESHom f)
    (coneSES_shortExact f) (coneSES_shortExact _) h₁ h₂

/-- Kind: proved algebraic theorem; changing the target degree of a
relation-indexed cochain square does not change its boundary equation
(Nekovář 1.1.3). -/
theorem map_eq_boundary_iff (f : GHom A B) {p j q : ℤ}
    (hj : j = q) (hp : p + 1 = q) (x : A.X j) (b : B.X p) :
    f.f j q hj x = B.d p q hp b ↔
      f.f j j rfl x = B.d p j (hp.trans hj.symm) b := by
  subst q
  rfl

/-- Kind: proved algebraic theorem; zero of a relation-indexed
differential is invariant under its target-degree equality
(Nekovář 1.1.3). -/
theorem differential_zero_iff (C : GCx R) {p q r : ℤ}
    (h : p + 1 = q) (e : q = r) (x : C.X p) :
    C.d p q h x = 0 ↔ C.d p r (h.trans e) x = 0 := by
  subst r
  rfl

/-- Kind: proved algebraic theorem; cycle lifting and boundary reflection
for one fixed cochain map give an exact mapping cone. No comparison is
postulated in the conclusion (Nekovář 1.1.3). -/
theorem cone_exact_of_cycle_lifts (f : GHom A B)
    (hlift : ∀ (j : ℤ) (y : B.X j), B.d j (j + 1) rfl y = 0 →
      ∃ (x : A.X j), A.d j (j + 1) rfl x = 0 ∧
        ∃ b : B.X (j - 1), y = f.f j j rfl x + B.d (j - 1) j (by omega) b)
    (hdetect : ∀ (j : ℤ) (x : A.X j), A.d j (j + 1) rfl x = 0 →
      (∃ b : B.X (j - 1), f.f j j rfl x = B.d (j - 1) j (by omega) b) →
        ∃ a : A.X (j - 1), A.d (j - 1) j (by omega) a = x) :
    GAcyclic (coneCx f) := by
  intro i j k hij hjk z hz
  have hi : i = j - 1 := by omega
  subst i
  subst k
  change (A.X j × B.X (j - 1)) at z
  have hz₁ : A.d j (j + 1) rfl z.1 = 0 := congrArg Prod.fst hz
  have hz₂ : f.f j j rfl z.1 = B.d (j - 1) j (by omega) z.2 := by
    have h := congrArg Prod.snd hz
    change f.f j (j + 1 - 1) (by omega) z.1 -
      B.d (j - 1) (j + 1 - 1) (by omega) z.2 = 0 at h
    exact (map_eq_boundary_iff f (p := j - 1) (j := j) (q := j + 1 - 1)
      (by omega) (by omega) z.1 z.2).mp (sub_eq_zero.mp h)
  obtain ⟨a, ha⟩ := hdetect j z.1 hz₁ ⟨z.2, hz₂⟩
  have hcy : B.d (j - 1) j (by omega)
      (z.2 - f.f (j - 1) (j - 1) rfl a) = 0 := by
    rw [map_sub]
    have hf := f.comm (j - 1) j (j - 1) j
      rfl (by omega) (by omega) rfl a
    rw [← hf, ha]
    exact sub_eq_zero.mpr hz₂.symm
  obtain ⟨x, hx, b, hb⟩ := hlift (j - 1)
    (z.2 - f.f (j - 1) (j - 1) rfl a)
    ((differential_zero_iff B (p := j - 1) (q := j - 1 + 1) (r := j)
      rfl (by omega) _).mpr hcy)
  have hx₀ : A.d (j - 1) j (by omega) x = 0 :=
    (differential_zero_iff A (p := j - 1) (q := j - 1 + 1) (r := j)
      rfl (by omega) x).mp hx
  refine ⟨(a + x, -b), ?_⟩
  apply Prod.ext
  · change A.d (j - 1) j (by omega) (a + x) = z.1
    rw [map_add, ha, hx₀, add_zero]
  · change f.f (j - 1) (j - 1) rfl (a + x) -
      B.d (j - 1 - 1) (j - 1) (by omega) (-b) = z.2
    rw [map_add, map_neg, sub_neg_eq_add]
    have h := sub_eq_iff_eq_add.mp hb
    simpa only [add_comm, add_left_comm, add_assoc] using h.symm

/-- Kind: proved algebraic theorem; elementwise cycle comparison implies
quasi-isomorphy of that same map (Nekovář 1.1.3). -/
theorem quasiIso_of_cycle_lifts (f : GHom A B)
    (hlift : ∀ (j : ℤ) (y : B.X j), B.d j (j + 1) rfl y = 0 →
      ∃ (x : A.X j), A.d j (j + 1) rfl x = 0 ∧
        ∃ b : B.X (j - 1), y = f.f j j rfl x + B.d (j - 1) j (by omega) b)
    (hdetect : ∀ (j : ℤ) (x : A.X j), A.d j (j + 1) rfl x = 0 →
      (∃ b : B.X (j - 1), f.f j j rfl x = B.d (j - 1) j (by omega) b) →
        ∃ a : A.X (j - 1), A.d (j - 1) j (by omega) a = x) :
    QuasiIso (GHom.toCC f) :=
  quasiIso_of_cone_exact f (cone_exact_of_cycle_lifts f hlift hdetect)

end CycleComparison

section BasedComparison

open Matrix ZInQ.Contrib.RC53Assist.DerivedKummer.Comparison

variable {R : Type} [CommRing R]
  {κe κo κe' κo' : Type} [Fintype κe] [Fintype κo] [Fintype κe'] [Fintype κo']
  [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo']
  {C : BasedCx R κe κo} {D : BasedCx R κe' κo'}

/-- Kind: proved algebraic theorem; exactness of the matrix cone gives
cycle lifting and boundary reflection for its specified comparison
(Nekovář 1.1.3; tex 3442–3450). -/
theorem based_cycle_comparison_of_cone_exact (f : ChainMapR C D)
    (hc : (BasedCx.coneR f).IsExact) : CohomologyComparison f := by
  constructor
  · intro y hy
    have hz : (BasedCx.coneR f).dOE *ᵥ Sum.elim y (0 : κo → R) = 0 := by
      change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ Sum.elim y 0 = 0
      rw [fromBlocks_mulVec]
      simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        hy, mulVec_zero, zero_mulVec, zero_add, neg_mulVec, neg_zero]
      funext i
      rcases i with i | i <;> rfl
    obtain ⟨w, hw⟩ := hc.1 (Sum.elim y 0) hz
    let x : κe → R := w ∘ Sum.inr
    let b : κo' → R := w ∘ Sum.inl
    change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ w = Sum.elim y 0 at hw
    rw [fromBlocks_mulVec] at hw
    refine ⟨x, ?_, b, ?_⟩
    · apply neg_eq_zero.mp
      funext i
      have h := congrFun hw (Sum.inr i)
      simpa only [x, zero_mulVec, zero_add, neg_mulVec, Sum.elim_inr] using h
    · funext i
      have h := congrFun hw (Sum.inl i)
      simpa only [x, b, Sum.elim_inl, Pi.add_apply, add_comm] using h
  · intro x hx ⟨b, hb⟩
    have hz : (BasedCx.coneR f).dEO *ᵥ Sum.elim b (-x) = 0 := by
      change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ Sum.elim b (-x) = 0
      rw [fromBlocks_mulVec]
      simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        mulVec_neg, hb, add_neg_cancel, zero_mulVec, zero_add,
        neg_mulVec, neg_neg, hx]
      funext i
      rcases i with i | i <;> rfl
    obtain ⟨w, hw⟩ := hc.2 (Sum.elim b (-x)) hz
    refine ⟨w ∘ Sum.inr, ?_⟩
    change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ w = Sum.elim b (-x) at hw
    rw [fromBlocks_mulVec] at hw
    apply neg_injective
    funext i
    have h := congrFun hw (Sum.inr i)
    simpa only [zero_mulVec, zero_add, neg_mulVec, Sum.elim_inr] using h
  · intro y hy
    have hz : (BasedCx.coneR f).dEO *ᵥ Sum.elim y (0 : κe → R) = 0 := by
      change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ Sum.elim y 0 = 0
      rw [fromBlocks_mulVec]
      simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        hy, mulVec_zero, zero_mulVec, zero_add, neg_mulVec, neg_zero]
      funext i
      rcases i with i | i <;> rfl
    obtain ⟨w, hw⟩ := hc.2 (Sum.elim y 0) hz
    let x : κo → R := w ∘ Sum.inr
    let b : κe' → R := w ∘ Sum.inl
    change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ w = Sum.elim y 0 at hw
    rw [fromBlocks_mulVec] at hw
    refine ⟨x, ?_, b, ?_⟩
    · apply neg_eq_zero.mp
      funext i
      have h := congrFun hw (Sum.inr i)
      simpa only [x, zero_mulVec, zero_add, neg_mulVec, Sum.elim_inr] using h
    · funext i
      have h := congrFun hw (Sum.inl i)
      simpa only [x, b, Sum.elim_inl, Pi.add_apply, add_comm] using h
  · intro x hx ⟨b, hb⟩
    have hz : (BasedCx.coneR f).dOE *ᵥ Sum.elim b (-x) = 0 := by
      change fromBlocks D.dOE f.fO 0 (-C.dEO) *ᵥ Sum.elim b (-x) = 0
      rw [fromBlocks_mulVec]
      simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        mulVec_neg, hb, add_neg_cancel, zero_mulVec, zero_add,
        neg_mulVec, neg_neg, hx]
      funext i
      rcases i with i | i <;> rfl
    obtain ⟨w, hw⟩ := hc.1 (Sum.elim b (-x)) hz
    refine ⟨w ∘ Sum.inr, ?_⟩
    change fromBlocks D.dEO f.fE 0 (-C.dOE) *ᵥ w = Sum.elim b (-x) at hw
    rw [fromBlocks_mulVec] at hw
    apply neg_injective
    funext i
    have h := congrFun hw (Sum.inr i)
    simpa only [zero_mulVec, zero_add, neg_mulVec, Sum.elim_inr] using h

end BasedComparison

section ComparisonCoordinates

open Matrix
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.BasedBridge
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.FiniteSourceCoordinates
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

variable {R : Type} [CommRing R] {c1 c2 r1 r0 : ℕ}
  (d : (Fin c1 → R) →ₗ[R] (Fin c2 → R))
  (f : (Fin r1 → R) →ₗ[R] (Fin r0 → R))
  (g : GHom (twoTermBased d).toGCx (dualCx (presentationCx r1 r0 f) 2))

/-- Kind: proved algebraic theorem; the first comparison matrix is
exactly the specified cochain map in the coordinate dual
(tex 3442–3450; Nekovář 1.1.3). -/
theorem comparison_one_value (u : Fin c1 → R) :
    asDual (g.f 1 1 rfl (oddCoordinates d u)) =
      vectorDual r0 ((basedComparison d f g).fO *ᵥ u) := by
  rw [basedComparison_one]
  exact ((vectorDual r0).apply_symm_apply (comparisonOne d f g u)).symm

/-- Kind: proved algebraic theorem; the second matrix is the same
comparison map in its complementary coordinate dual
(tex 3442–3450; Nekovář 1.1.3). -/
theorem comparison_two_value (u : Fin c2 → R) :
    asDual (g.f 2 2 rfl (evenCoordinates d u)) =
      vectorDual r1 ((basedComparison d f g).fE *ᵥ u) := by
  rw [basedComparison_two]
  exact ((vectorDual r1).apply_symm_apply (comparisonTwo d f g u)).symm

/-- Kind: proved algebraic theorem; the complementary-degree dual
presentation has its unsigned relation differential in degree one
(tex 3442–3450; Nekovář 1.1.3). -/
theorem dual_presentation_d_one
    (x : (dualCx (presentationCx r1 r0 f) 2).X 1) :
    asDual ((dualCx (presentationCx r1 r0 f) 2).d 1 2 rfl x) = f.dualMap (asDual x) := by
  apply LinearMap.ext
  intro u
  change (-(sgn (1 : ℤ))) • asDual x (f u) = asDual x (f u)
  simp [sgn]

/-- Kind: proved algebraic theorem; the dual presentation has no terms
outside degrees one and two (tex 3442–3450; Nekovář 1.1.3). -/
theorem dual_presentation_support (n : ℤ) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    Subsingleton ((dualCx (presentationCx r1 r0 f) 2).X n) := by
  letI : Subsingleton ((presentationCx r1 r0 f).X (2 - n)) :=
    presentationCx_vanishes r1 r0 f (2 - n) (by omega)
  change Subsingleton (Module.Dual R ((presentationCx r1 r0 f).X (2 - n)))
  infer_instance

/-- Kind: proved algebraic theorem; a contraction of the genuine based
comparison cone proves quasi-isomorphy of the cochain map from which its
matrices were read, not a replacement map (tex 3442–3450; Nekovář 1.1.3). -/
theorem comparison_quasiIso_of_contraction
    (h : Nonempty (Contraction (BasedCx.coneR (basedComparison d f g)))) :
    QuasiIso (GHom.toCC g) := by
  let fm := basedComparison d f g
  have hc := based_cycle_comparison_of_cone_exact fm
    ((BasedCx.coneR fm).isExact_of_contraction h.some)
  apply quasiIso_of_cycle_lifts g
  · intro n y hy
    by_cases hn1 : n = 1
    · subst n
      change (dualCx (presentationCx r1 r0 f) 2).d 1 2 rfl y = 0 at hy
      let v := (vectorDual r0).symm (asDual y)
      have hv : (dualPresentationCx f).dEO *ᵥ v = 0 := by
        rw [dualPresentationCx_d]
        apply (vectorDual r1).injective
        rw [dualRelation_dual, map_zero]
        have hh := congrArg asDual hy
        rw [dual_presentation_d_one] at hh
        change f.dualMap (asDual y) = (0 : Module.Dual R (Fin r1 → R)) at hh
        simpa only [v, LinearEquiv.apply_symm_apply] using hh
      obtain ⟨u, hu, b, hb⟩ := hc.liftO v hv
      have hu₀ : d u = 0 := by
        simpa only [twoTermBased_d] using hu
      have hb₀ : fm.fO *ᵥ u = v := by
        simpa only [dualPresentationCx, zero_mulVec, add_zero] using hb
      refine ⟨oddCoordinates d u, ?_, 0, ?_⟩
      · change (twoTermBased d).toGCx.d 1 2 rfl (oddCoordinates d u) = 0
        rw [oddCoordinates_d, hu₀, map_zero]
      · rw [map_zero, add_zero]
        apply dualCx_ext
        intro z
        have hh : asDual (g.f 1 1 rfl (oddCoordinates d u)) = asDual y := by
          rw [comparison_one_value, hb₀]
          exact (vectorDual r0).apply_symm_apply _
        exact (LinearMap.congr_fun hh z).symm
    · by_cases hn2 : n = 2
      · subst n
        let v := (vectorDual r1).symm (asDual y)
        obtain ⟨u, hu, b, hb⟩ := hc.liftE v (by exact zero_mulVec v)
        refine ⟨evenCoordinates d u, even_d_zero d u, vectorDual r0 b, ?_⟩
        apply dualCx_ext
        intro z
        have hh : asDual (g.f 2 2 rfl (evenCoordinates d u)) +
            asDual ((dualCx (presentationCx r1 r0 f) 2).d 1 2 rfl (vectorDual r0 b)) = asDual y := by
          rw [comparison_two_value, dual_presentation_d_one]
          change vectorDual r1 (fm.fE *ᵥ u) + f.dualMap (vectorDual r0 b) = asDual y
          rw [← dualRelation_dual, ← map_add]
          have hb₀ : fm.fE *ᵥ u + dualRelation f b = v := by
            simpa only [dualPresentationCx_d] using hb
          rw [hb₀]
          exact (vectorDual r1).apply_symm_apply _
        exact (LinearMap.congr_fun hh z).symm
      · letI := source_subsingleton d n hn1 hn2
        letI := dual_presentation_support f n hn1 hn2
        refine ⟨0, map_zero _, 0, ?_⟩
        exact Subsingleton.elim _ _
  · intro n x hx ⟨b, hb⟩
    by_cases hn1 : n = 1
    · subst n
      change (dualCx (presentationCx r1 r0 f) 2).X 0 at b
      change (twoTermBased d).toGCx.d 1 2 rfl x = 0 at hx
      change g.f 1 1 rfl x = (dualCx (presentationCx r1 r0 f) 2).d 0 1 rfl b at hb
      letI := dual_presentation_support f 0 (by omega) (by omega)
      have hb0 : b = 0 := Subsingleton.elim _ _
      have hzero : g.f 1 1 rfl x = 0 := by simpa only [hb0, map_zero] using hb
      let u := oddProjection d x
      have hu : (twoTermBased d).dEO *ᵥ u = 0 := by
        have hh := hx
        rw [← odd_reconstruct d x, oddCoordinates_d] at hh
        have he := congrArg (evenProjection d) hh
        change d u = 0 at he
        simpa only [twoTermBased_d] using he
      have hf : fm.fO *ᵥ u = 0 := by
        apply (vectorDual r0).injective
        rw [map_zero, ← comparison_one_value]
        rw [odd_reconstruct, hzero]
        rfl
      obtain ⟨a, ha⟩ := hc.detectO u hu ⟨0, by simpa only [mulVec_zero] using hf.symm⟩
      have hu0 : u = 0 := ha.symm.trans (zero_mulVec a)
      have hx0 : x = 0 := by
        rw [← odd_reconstruct d x]
        change oddCoordinates d u = 0
        rw [hu0, map_zero]
      exact ⟨0, by rw [map_zero, hx0]⟩
    · by_cases hn2 : n = 2
      · subst n
        change (dualCx (presentationCx r1 r0 f) 2).X 1 at b
        change g.f 2 2 rfl x = (dualCx (presentationCx r1 r0 f) 2).d 1 2 rfl b at hb
        let u := evenProjection d x
        let v := (vectorDual r0).symm (asDual b)
        have hv : (dualPresentationCx f).dEO *ᵥ v = fm.fE *ᵥ u := by
          rw [dualPresentationCx_d]
          apply (vectorDual r1).injective
          rw [dualRelation_dual, ← comparison_two_value]
          rw [even_reconstruct]
          have he := congrArg asDual hb
          rw [dual_presentation_d_one] at he
          simpa only [v, LinearEquiv.apply_symm_apply] using he.symm
        obtain ⟨a, ha⟩ := hc.detectE u (zero_mulVec u) ⟨v, hv⟩
        have ha₀ : d a = u := by simpa only [twoTermBased_d] using ha
        refine ⟨oddCoordinates d a, ?_⟩
        change (twoTermBased d).toGCx.d 1 2 rfl (oddCoordinates d a) = x
        rw [oddCoordinates_d, ha₀]
        exact even_reconstruct d x
      · letI := source_subsingleton d n hn1 hn2
        have hx0 : x = 0 := Subsingleton.elim _ _
        exact ⟨0, by rw [map_zero, hx0]⟩

end ComparisonCoordinates

section ActualComparison

open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualSelfDual
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.ActualBasedComparison

variable (K : Type) [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))
  [DecidableEq (w.adicCompletion K)] (B : WeierstrassCurve (w.adicCompletion K)) [B.IsElliptic]

/-- Kind: proved arithmetic theorem; the actual quotient-cone comparison
on continuous Tate cochains is a quasi-isomorphism, by the contraction
of the matrix comparison in any independent actual source model
(tex 3442–3450; Milne I.2.3 and I.3.4). -/
theorem actual_local_comparison_quasiIso_of_models {c1 c2 : ℕ}
    (I : TwoTermConeBasedResolution K w B c1 c2)
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hthird : FiniteCycleLift.ThirdDegreeExact (w.adicCompletion K)) :
    QuasiIso (GHom.toCC (localSelfDualComparison K w B hM)) := by
  have h := ComparisonEvaluation.contraction_of_actual_models K w B I hM hF hthird
  letI : QuasiIso (GHom.toCC I.realization) := I.quasiIso
  haveI : QuasiIso (GHom.toCC I.realization ≫ GHom.toCC (localSelfDualComparison K w B hM)) := by
    rw [GHom.toCC_comp]
    exact comparison_quasiIso_of_contraction I.differential (actualLocalPresentation K w B).f
      (ghomComp I.realization (localSelfDualComparison K w B hM)) h
  exact quasiIso_of_comp_left (GHom.toCC I.realization) (GHom.toCC (localSelfDualComparison K w B hM))

/-- Kind: proved arithmetic theorem; the same actual continuous local
self-dual comparison is quasi-isomorphic using only the cited Milne
prints, with its source model constructed rather than supplied
(tex 3442–3450; Milne I.2.3 and I.3.4). -/
theorem actual_local_comparison_quasiIso_of_print
    (hM : MilneLocalDualityPrint) (hF : MilneFiniteLocalDualityPrint)
    (hH : FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint) :
    QuasiIso (GHom.toCC (localSelfDualComparison K w B hM)) :=
  actual_local_comparison_quasiIso_of_models K w B
    (FiniteLocalDegreeBound.basedResolution_of_print hM hF hH K w B) hM hF
    (FiniteLocalDegreeBound.actualThirdDegreeExact_of_print hH (w.adicCompletion K))

end ActualComparison

section LiteralKummerClosure

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralTransport

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition with proved membership; an actual rational local
point determines a term of the literal integral Kummer condition
(tex 3413–3438; Milne I.3.4). -/
def literalPointTerm (P : (W.baseChange (w.adicCompletion K)).toAffine.Point) :
    (integralCondition (S := S) W w).X 1 :=
  ⟨(globalKummerCycle (S := S) W w P).val, by
    change (globalKummerCycle (S := S) W w P).val ∈
      tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w ⊔
        contB1 ℤ_[2] (Gloc K w) (ResMod (locMap K S w) (TateS K S W))
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨P, rfl⟩)⟩

/-- Kind: proved theorem; the literal point term has the unchanged
actual continuous Kummer cycle (tex 3413–3438; Milne I.3.4). -/
theorem literalPointTerm_cycle (P : (W.baseChange (w.adicCompletion K)).toAffine.Point) :
    integralConditionCycleMap (S := S) W w (literalPointTerm W w P) =
      globalKummerCycle (S := S) W w P := Subtype.ext rfl

/-- Kind: proved arithmetic theorem; all genuine finite Kummer image
conditions imply membership in the literal integral Kummer condition.
Finiteness is used for that condition's terms, not for all Galois
cochains (tex 3413–3438; Milne I.2.1 and I.3.4). -/
theorem literal_kummer_mem_of_all_finite_images (hloc : MilneLocalFiniteness)
    (c : LinearMap.ker ((pointComplex (w.adicCompletion K)
      (W.baseChange (w.adicCompletion K))).d 1 2).hom)
    (hc : ∀ a, pointH1Reduction (w.adicCompletion K) (W.baseChange (w.adicCompletion K)) a c ∈
      ((W.baseChange (w.adicCompletion K)).kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range) :
    ((localPointCochainInv (S := S) W w).f 1).hom c.val ∈
      tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w ⊔
        contB1 ℤ_[2] (Gloc K w) (ResMod (locMap K S w) (TateS K S W)) := by
  let U := integralCondition (S := S) W w
  let F := w.adicCompletion K
  let B := W.baseChange F
  letI : Module.Finite ℤ_[2] (U.X 1) := integralCondition_one_finite W w hloc
  letI : Module.Free ℤ_[2] (U.X 1) := integralCondition_term_free W w hloc 1
  let J := Module.Free.ChooseBasisIndex ℤ_[2] (U.X 1)
  let n := Fintype.card J
  let b : Module.Basis (Fin n) ℤ_[2] (U.X 1) :=
    (Module.Free.chooseBasis ℤ_[2] (U.X 1)).reindex (Fintype.equivFin J)
  let κ : (Fin n → ℤ_[2]) →ₗ[ℤ_[2]] LinearMap.ker ((actualIntegralComplex F B).d 1 2).hom :=
    (pointCycleToAlg F B).comp ((localPointCycleMap (S := S) W w).comp
      ((integralConditionCycleMap (S := S) W w).comp b.equivFun.symm.toLinearMap))
  let ca := pointCycleToAlg F B c
  have hfinite : ∀ a, ∃ u : Fin n → ℤ_[2],
      reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a (κ u) =
        reducedOneClass (Field.absoluteGaloisGroup F) (PtAlg F B) a ca := by
    intro a
    obtain ⟨P, hP⟩ := hc a
    let z : U.X 1 := literalPointTerm (S := S) W w P
    let u := b.equivFun z
    refine ⟨u, ?_⟩
    apply (explicitCoeff1Equiv (Field.absoluteGaloisGroup F)
      (FiniteTateCoeff (Field.absoluteGaloisGroup F) (PtAlg F B) a)
      (actualLevelEquiv F B a) continuous_of_discreteTopology
      continuous_of_discreteTopology (actualLevelEquiv_smul F B a)).injective
    change actualH1Reduction F B a (κ u) = actualH1Reduction F B a ca
    have hκ : κ u = pointCycleToAlg F B (localPointCycleMap (S := S) W w
        (globalKummerCycle (S := S) W w P)) := by
      change pointCycleToAlg F B (localPointCycleMap (S := S) W w
        (integralConditionCycleMap (S := S) W w (b.equivFun.symm (b.equivFun z)))) = _
      rw [LinearEquiv.symm_apply_apply]
      change pointCycleToAlg F B (localPointCycleMap (S := S) W w
        (integralConditionCycleMap (S := S) W w (literalPointTerm (S := S) W w P))) = _
      rw [literalPointTerm_cycle]
    rw [hκ, pointCycleToAlg_h1]
    change FiniteTrace.hOneToAlg F B (2 ^ a)
        (pointH1Reduction F B a (localPointCycleMap (S := S) W w (globalKummerCycle (S := S) W w P))) =
      actualH1Reduction F B a (pointCycleToAlg F B c)
    rw [pointCycleToAlg_h1, localKummerCycle_class]
    exact congrArg (FiniteTrace.hOneToAlg F B (2 ^ a)) hP
  obtain ⟨u, q, hq⟩ := SourceKummerClasses.integral_based_image_of_all_finite_images F B κ ca hfinite
  let z : U.X 1 := b.equivFun.symm u
  let p := localPointCycleMap (S := S) W w (integralConditionCycleMap (S := S) W w z)
  let qP := ((toSepComplex F B).f 0).hom q
  have hqP : ((pointComplex F B).d 0 1).hom qP = c.val - p.val := by
    dsimp only [qP]
    rw [← toSepComplex_d, hq, map_sub]
    change (toSepCycle F B ca).val - (toSepCycle F B (κ u)).val = _
    have hκ : κ u = pointCycleToAlg F B p := rfl
    rw [hκ]
    dsimp only [ca]
    rw [pointCycleToAlg_sep, pointCycleToAlg_sep]
  have hcomm : ((restrictedPointComplex (S := S) W w).d 0 1).hom
      (((localPointCochainInv (S := S) W w).f 0).hom qP) =
        ((localPointCochainInv (S := S) W w).f 1).hom (((pointComplex F B).d 0 1).hom qP) := by
    have hh := congrArg (fun k => k.hom qP) ((localPointCochainInv (S := S) W w).comm 0 1)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  have hp : ((localPointCochainInv (S := S) W w).f 1).hom p.val = z.val := by
    change ((localPointCochainInv (S := S) W w).f 1).hom
      (((localPointCochainMap W w).f 1).hom z.val) = z.val
    have hh := congrArg (fun k => (k.f 1).hom z.val) (localPointCochainMap_inv W w)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using hh
  have hh : ((restrictedPointComplex (S := S) W w).d 0 1).hom
      (((localPointCochainInv (S := S) W w).f 0).hom qP) =
        ((localPointCochainInv (S := S) W w).f 1).hom c.val - z.val := by
    calc
      _ = ((localPointCochainInv (S := S) W w).f 1).hom (((pointComplex F B).d 0 1).hom qP) := hcomm
      _ = ((localPointCochainInv (S := S) W w).f 1).hom c.val -
          ((localPointCochainInv (S := S) W w).f 1).hom p.val := by rw [hqP, map_sub]
      _ = _ := by rw [hp]
  have he := sub_eq_iff_eq_add.mp hh.symm
  rw [he]
  apply Submodule.add_mem
  · exact Submodule.mem_sup_right ⟨((localPointCochainInv (S := S) W w).f 0).hom qP, rfl⟩
  · exact z.property

end LiteralKummerClosure

section LiteralPresentation

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition; all restricted degree-zero cochains are the
literal degree-zero Kummer terms (tex 3413–3438). -/
def literalZeroTermMap : (restrictedPointComplex (S := S) W w).X 0 →ₗ[ℤ_[2]]
    (integralCondition (S := S) W w).X 0 where
  toFun b := ofCondZero
    (tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w)
    (tateKummerZ_cocycle W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w) b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Kind: definition with proved membership; the actual completion
presentation's Kummer one-map lands in the literal condition, by its
all-level genuine finite classes (tex 3413–3438; Milne I.3.4). -/
def actualLiteralOne (hloc : MilneLocalFiniteness) :
    (Fin (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).rankZero → ℤ_[2]) →ₗ[ℤ_[2]]
      (integralCondition (S := S) W w).X 1 :=
  ((((localPointCochainInv (S := S) W w).f 1).hom).comp
    ((LinearMap.ker ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 1 2).hom).subtype.comp
      (localKummerOne K w (W.baseChange (w.adicCompletion K))))).codRestrict _ (fun u =>
    literal_kummer_mem_of_all_finite_images W w hloc
      (localKummerOne K w (W.baseChange (w.adicCompletion K)) u)
      (fun a => localKummerOne_mem_genuine_Kummer K w (W.baseChange (w.adicCompletion K)) a u))

/-- Kind: definition with proved differential and cycle fields; the
actual completion presentation maps to the literal Kummer condition
using the fixed cochain dictionary (tex 3413–3438; Milne I.3.4). -/
def actualLiteralPresentation (hloc : MilneLocalFiniteness) :
    PresentationMap (integralCondition (S := S) W w)
      (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).rankOne
      (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).rankZero
      (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).f where
  zero := (literalZeroTermMap (S := S) W w).comp
    ((((localPointCochainInv (S := S) W w).f 0).hom).comp
      (localKummerZero K w (W.baseChange (w.adicCompletion K))))
  one := actualLiteralOne W w hloc
  differential u := by
    apply Subtype.ext
    change ((restrictedPointComplex (S := S) W w).d 0 1).hom
      (((localPointCochainInv (S := S) W w).f 0).hom
        (localKummerZero K w (W.baseChange (w.adicCompletion K)) u)) =
      ((localPointCochainInv (S := S) W w).f 1).hom
        (localKummerOne K w (W.baseChange (w.adicCompletion K))
          ((actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).f u)).val
    rw [← localKummerZero_d]
    have hh := congrArg (fun k => k.hom (localKummerZero K w (W.baseChange (w.adicCompletion K)) u))
      ((localPointCochainInv (S := S) W w).comm 0 1)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hh
  cycle u := by
    letI := integralKummerCondition_support (S := S) W w 2 (by omega)
    exact Subsingleton.elim _ _

/-- Kind: definition; the chain map from the actual finite free
completion presentation to the literal integral local Kummer condition
is constructed from actual cycle membership (tex 3413–3438). -/
def actualConditionToLiteral (hloc : MilneLocalFiniteness) :
    GHom (ActualSelfDual.localCondition K w (W.baseChange (w.adicCompletion K)))
      (integralCondition (S := S) W w) :=
  presentationMap (actualLiteralPresentation W w hloc)

/-- Kind: proved theorem; degree zero of the presentation transport is
the inverse fixed cochain dictionary on the actual relation primitive
(tex 3413–3438). -/
theorem actualConditionToLiteral_zero (hloc : MilneLocalFiniteness)
    (u : Fin (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).rankOne → ℤ_[2]) :
    ((actualConditionToLiteral W w hloc).f 0 0 rfl u).val =
      ((localPointCochainInv (S := S) W w).f 0).hom
        (localKummerZero K w (W.baseChange (w.adicCompletion K)) u) := rfl

/-- Kind: proved theorem; degree one is the inverse same cochain
dictionary on the actual completed Kummer cocycle (tex 3413–3438). -/
theorem actualConditionToLiteral_one (hloc : MilneLocalFiniteness)
    (u : Fin (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).rankZero → ℤ_[2]) :
    ((actualConditionToLiteral W w hloc).f 1 1 rfl u).val =
      ((localPointCochainInv (S := S) W w).f 1).hom
        (localKummerOne K w (W.baseChange (w.adicCompletion K)) u).val := rfl

end LiteralPresentation

section LiteralComparison

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralReduction
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralKummer
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: proved arithmetic theorem; the actual presentation's one-map
has precisely its own relation vectors as continuous boundaries
(tex 3413–3438; Milne I.3.4). -/
theorem actual_kummer_relation_of_boundary
    (u : Fin (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).rankZero → ℤ_[2])
    (b : (pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).X 0)
    (hb : ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 0 1).hom b =
      (localKummerOne K w (W.baseChange (w.adicCompletion K)) u).val) :
    ∃ a, (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).f a = u := by
  let F := w.adicCompletion K
  let B := W.baseChange F
  let P := actualLocalPresentation K w B
  have hr : ∀ a, completionKummerClass F B a (P.g u) = 0 := by
    intro a
    have h := ActualConeModels.point_reduction_boundary K w B a
      (localKummerOne K w B u) b hb
    rw [localKummerOne_reduction] at h
    have hA : actualH1Reduction F B a (actualLocalKummerOne K w B u) = 0 := by
      apply (FiniteTrace.hOneToAlg F B (2 ^ a)).symm.injective
      exact h.trans (map_zero _).symm
    rw [actualLocalKummerOne, basedKummerOne_reduction] at hA
    exact hA
  have hg : P.g u = 0 :=
    SourceKummerClasses.completion_class_family_injective F B (P.g u) 0
      (fun a => (hr a).trans (map_zero (completionKummerClass F B a)).symm)
  exact P.exact u hg

/-- Kind: proved arithmetic theorem; the literal degree-zero Kummer
term has no nonzero cycle, by the actual local Tate invariants
(tex 3413–3438; Silverman III.7). -/
theorem literal_zero_cycle_eq_zero (y : (integralCondition (S := S) W w).X 0)
    (hy : (integralCondition (S := S) W w).d 0 1 rfl y = 0) : y = 0 := by
  have hraw : ((restrictedPointComplex (S := S) W w).d 0 1).hom y.val = 0 := by
    exact congrArg Subtype.val hy
  have hpoint : ((pointComplex (w.adicCompletion K) (W.baseChange (w.adicCompletion K))).d 0 1).hom
      (((localPointCochainMap (S := S) W w).f 0).hom y.val) = 0 := by
    have h := congrArg (fun k => k.hom y.val) ((localPointCochainMap (S := S) W w).comm 0 1)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hraw, map_zero] using h
  have hz := SourceDegreeZero.actual_zero_cochain_kernel K w (W.baseChange (w.adicCompletion K))
    (((localPointCochainMap (S := S) W w).f 0).hom y.val) hpoint
  have h := congrArg (fun k => ((localPointCochainInv (S := S) W w).f 0).hom k) hz
  have hi := congrArg (fun k => (k.f 0).hom y.val) (localPointCochainMap_inv (S := S) W w)
  apply Subtype.ext
  change y.val = 0
  have he : ((localPointCochainInv (S := S) W w).f 0).hom
      (((localPointCochainMap (S := S) W w).f 0).hom y.val) = y.val := by
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using hi
  exact he.symm.trans (h.trans (map_zero _))

/-- Kind: proved arithmetic theorem; the map from the actual completion
presentation to the literal integral condition is a quasi-isomorphism.
Both cycle lifting and boundary reflection use the same fixed Kummer
maps (tex 3413–3438; Milne I.2.1 and I.3.4). -/
theorem actualConditionToLiteral_quasiIso (hloc : MilneLocalFiniteness) :
    QuasiIso (GHom.toCC (actualConditionToLiteral (S := S) W w hloc)) := by
  let B := W.baseChange (w.adicCompletion K)
  let P := actualLocalPresentation K w B
  let U := integralCondition (S := S) W w
  let F := actualConditionToLiteral (S := S) W w hloc
  apply quasiIso_of_cycle_lifts F
  · intro n y hy
    by_cases hn0 : n = 0
    · subst n
      change U.d 0 1 rfl y = 0 at hy
      have hy0 := literal_zero_cycle_eq_zero W w y hy
      refine ⟨0, map_zero _, 0, ?_⟩
      rw [hy0, map_zero, map_zero, zero_add]
    · by_cases hn1 : n = 1
      · subst n
        let c := localPointCycleMap (S := S) W w (integralConditionCycleMap (S := S) W w y)
        obtain ⟨u, b, hb⟩ := SourceIntegralImage.local_integral_image_of_all_finite_images K w B c
          (fun a => integralCondition_finite_Kummer W w a y)
        let bR := literalZeroTermMap (S := S) W w (((localPointCochainInv (S := S) W w).f 0).hom b)
        have hInv : ((localPointCochainInv (S := S) W w).f 1).hom c.val = y.val := by
          change ((localPointCochainInv (S := S) W w).f 1).hom
            (((localPointCochainMap (S := S) W w).f 1).hom y.val) = y.val
          have h := congrArg (fun k => (k.f 1).hom y.val) (localPointCochainMap_inv (S := S) W w)
          simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
            LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
        have hbR : U.d 0 1 rfl bR = y - F.f 1 1 rfl u := by
          apply Subtype.ext
          change ((restrictedPointComplex (S := S) W w).d 0 1).hom
            (((localPointCochainInv (S := S) W w).f 0).hom b) =
            y.val - ((localPointCochainInv (S := S) W w).f 1).hom (localKummerOne K w B u).val
          have h := congrArg (fun k => k.hom b) ((localPointCochainInv (S := S) W w).comm 0 1)
          have hcomm : ((restrictedPointComplex (S := S) W w).d 0 1).hom
              (((localPointCochainInv (S := S) W w).f 0).hom b) =
              ((localPointCochainInv (S := S) W w).f 1).hom (((pointComplex (w.adicCompletion K) B).d 0 1).hom b) := by
            simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h
          rw [hcomm, hb, map_sub, hInv]
        refine ⟨u, ?_, bR, ?_⟩
        · change (ActualSelfDual.localCondition K w B).d 1 2 rfl u = 0
          exact Subsingleton.elim _ _
        · change y = F.f 1 1 rfl u + U.d 0 1 rfl bR
          have h := sub_eq_iff_eq_add.mp hbR.symm
          exact h.trans (add_comm _ _)
      · letI := integralKummerCondition_support (S := S) W w n (by omega)
        letI : Subsingleton ((ActualSelfDual.localCondition K w B).X n) :=
          presentationCx_vanishes P.rankOne P.rankZero P.f n (by omega)
        refine ⟨0, map_zero _, 0, ?_⟩
        exact Subsingleton.elim _ _
  · intro n x hx ⟨b, hb⟩
    by_cases hn0 : n = 0
    · subst n
      change P.f x = 0 at hx
      have hx0 : x = 0 := P.injective (hx.trans (map_zero P.f).symm)
      exact ⟨0, by rw [map_zero, hx0]⟩
    · by_cases hn1 : n = 1
      · subst n
        change U.X 0 at b
        change F.f 1 1 rfl x = U.d 0 1 rfl b at hb
        have hraw := congrArg Subtype.val hb
        change ((localPointCochainInv (S := S) W w).f 1).hom (localKummerOne K w B x).val =
          ((restrictedPointComplex (S := S) W w).d 0 1).hom b.val at hraw
        have hcomm := congrArg (fun k => k.hom b.val) ((localPointCochainMap (S := S) W w).comm 0 1)
        have hi := congrArg (fun k => (k.f 1).hom (localKummerOne K w B x).val)
          (localPointCochainInv_map (S := S) W w)
        have hinv : ((localPointCochainMap (S := S) W w).f 1).hom
            (((localPointCochainInv (S := S) W w).f 1).hom (localKummerOne K w B x).val) =
              (localKummerOne K w B x).val := by
          simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
            LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using hi
        have hbP : ((pointComplex (w.adicCompletion K) B).d 0 1).hom
            (((localPointCochainMap (S := S) W w).f 0).hom b.val) =
              (localKummerOne K w B x).val := by
          have h := congrArg (fun k => ((localPointCochainMap (S := S) W w).f 1).hom k) hraw
          have he : ((pointComplex (w.adicCompletion K) B).d 0 1).hom
              (((localPointCochainMap (S := S) W w).f 0).hom b.val) =
                ((localPointCochainMap (S := S) W w).f 1).hom
                  (((restrictedPointComplex (S := S) W w).d 0 1).hom b.val) := by
            simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using hcomm
          exact he.trans (h.symm.trans hinv)
        obtain ⟨a, ha⟩ := actual_kummer_relation_of_boundary W w x
          (((localPointCochainMap (S := S) W w).f 0).hom b.val) hbP
        exact ⟨a, ha⟩
      · letI : Subsingleton ((ActualSelfDual.localCondition K w B).X n) :=
          presentationCx_vanishes P.rankOne P.rankZero P.f n (by omega)
        have hx0 : x = 0 := Subsingleton.elim _ _
        exact ⟨0, by rw [map_zero, hx0]⟩

end LiteralComparison

section LiteralDualComparison

open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: proved algebraic theorem; the actual completion presentation
has torsion-free terms, without any assertion that its cohomology is
torsion-free (tex 3413–3438; Silverman III.7). -/
theorem actualCondition_term_torsionFree (n : ℤ) :
    Module.IsTorsionFree ℤ_[2] ((ActualSelfDual.localCondition K w
      (W.baseChange (w.adicCompletion K))).X n) := by
  by_cases h0 : n = 0
  · subst n
    change Module.IsTorsionFree ℤ_[2]
      (Fin (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).rankOne → ℤ_[2])
    infer_instance
  by_cases h1 : n = 1
  · subst n
    change Module.IsTorsionFree ℤ_[2]
      (Fin (actualLocalPresentation K w (W.baseChange (w.adicCompletion K))).rankZero → ℤ_[2])
    infer_instance
  letI : Subsingleton ((ActualSelfDual.localCondition K w (W.baseChange (w.adicCompletion K))).X n) :=
    presentationCx_vanishes _ _ _ n (by omega)
  infer_instance

/-- Kind: proved arithmetic theorem; the contravariant dual of the
actual-presentation-to-literal-condition map is quasi-isomorphic, by
scoped torsion-free dual exactness over the compact scalar PID. This
uses no infinite-cochain dual base-change identity
(tex 3413–3438; Nekovář 1.1.3). -/
theorem actualConditionToLiteral_dual_quasiIso (hloc : MilneLocalFiniteness) (m : ℤ) :
    QuasiIso (GHom.toCC (dualHom (actualConditionToLiteral (S := S) W w hloc) m)) :=
  dualHom_quasiIso_torsionFree (actualConditionToLiteral (S := S) W w hloc)
    (actualCondition_term_torsionFree W w) (integralCondition_term_torsionFree W w)
    m (actualConditionToLiteral_quasiIso W w hloc)

end LiteralDualComparison

section FixedCochainDictionary

open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing

/-- Kind: proved algebraic theorem; an isomorphism of natural cochain
complexes remains an isomorphism after the fixed relation-indexed
presentation (Nekovář 1.1.3; tex 3413–3438). -/
theorem natHom_quasiIso_of_iso {R : Type} [CommRing R]
    {C D : CochainComplex (ModuleCat R) ℕ} (e : C ≅ D) :
    QuasiIso (GHom.toCC (natHom e.hom)) := by
  let f := GHom.toCC (natHom e.hom)
  let g := GHom.toCC (natHom e.inv)
  have hfg : f ≫ g = 𝟙 _ := by
    ext n x
    cases n with
    | ofNat n =>
      change (e.inv.f n).hom ((e.hom.f n).hom x) = x
      have h := congrArg (fun k => (k.f n).hom x) e.hom_inv_id
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
        LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
    | negSucc n =>
      letI : Subsingleton ((natCx C).toCC.X (Int.negSucc n)) := by
        change Subsingleton PUnit
        infer_instance
      exact Subsingleton.elim _ _
  have hgf : g ≫ f = 𝟙 _ := by
    ext n x
    cases n with
    | ofNat n =>
      change (e.hom.f n).hom ((e.inv.f n).hom x) = x
      have h := congrArg (fun k => (k.f n).hom x) e.inv_hom_id
      simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
        LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
    | negSucc n =>
      letI : Subsingleton ((natCx D).toCC.X (Int.negSucc n)) := by
        change Subsingleton PUnit
        infer_instance
      exact Subsingleton.elim _ _
  letI : IsIso f := ⟨⟨g, hfg, hgf⟩⟩
  exact inferInstanceAs (QuasiIso f)

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: proved theorem; the fixed continuous Tate dictionary gives the
same quasi-isomorphism in the integral relation-indexed cochains
(tex 3413–3438; Silverman III.7). -/
theorem fixed_point_dictionary_quasiIso :
    QuasiIso (GHom.toCC (natHom (localPointCochainMap (S := S) W w))) :=
  natHom_quasiIso_of_iso (localPointCochainIso (S := S) W w)

/-- Kind: proved theorem; the inverse is the inverse of the same actual
cochain dictionary, not a separately supplied derived comparison
(tex 3413–3438; Silverman III.7). -/
theorem fixed_point_dictionary_inverse_quasiIso :
    QuasiIso (GHom.toCC (natHom (localPointCochainInv (S := S) W w))) :=
  natHom_quasiIso_of_iso (localPointCochainIso (S := S) W w).symm

/-- Kind: proved theorem; the actual-presentation-to-literal-condition
map is strictly over the fixed actual point cochains in all degrees
(tex 3413–3438; Milne I.3.4). -/
theorem actualConditionToLiteral_over_point (hloc : MilneLocalFiniteness) (n : ℤ)
    (u : (ActualSelfDual.localCondition K w (W.baseChange (w.adicCompletion K))).X n) :
    (natHom (localPointCochainMap (S := S) W w)).f n n rfl
      ((integralConditionMap (S := S) W w).f n n rfl
        ((actualConditionToLiteral (S := S) W w hloc).f n n rfl u)) =
      (ActualSelfDual.localConditionMap K w (W.baseChange (w.adicCompletion K))).f n n rfl u := by
  by_cases h0 : n = 0
  · subst n
    change ((localPointCochainMap (S := S) W w).f 0).hom
      (((localPointCochainInv (S := S) W w).f 0).hom
        (TransportedLocal.localKummerZero K w (W.baseChange (w.adicCompletion K)) u)) =
      TransportedLocal.localKummerZero K w (W.baseChange (w.adicCompletion K)) u
    have h := congrArg (fun k => (k.f 0).hom
      (TransportedLocal.localKummerZero K w (W.baseChange (w.adicCompletion K)) u))
      (localPointCochainInv_map (S := S) W w)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  by_cases h1 : n = 1
  · subst n
    change ((localPointCochainMap (S := S) W w).f 1).hom
      (((localPointCochainInv (S := S) W w).f 1).hom
        (TransportedLocal.localKummerOne K w (W.baseChange (w.adicCompletion K)) u).val) =
      (TransportedLocal.localKummerOne K w (W.baseChange (w.adicCompletion K)) u).val
    have h := congrArg (fun k => (k.f 1).hom
      (TransportedLocal.localKummerOne K w (W.baseChange (w.adicCompletion K)) u).val)
      (localPointCochainInv_map (S := S) W w)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using h
  letI : Subsingleton ((ActualSelfDual.localCondition K w (W.baseChange (w.adicCompletion K))).X n) :=
    SelfDualCore.presentationCx_vanishes _ _ _ n (by omega)
  have hu : u = 0 := Subsingleton.elim _ _
  rw [hu, map_zero, map_zero, map_zero, map_zero]

end FixedCochainDictionary

section OrdinaryConeTransport

open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

variable {R : Type} [CommRing R] {A B A' B' : GCx R}

/-- Kind: definition with proved differential fields; a strict square
of local-condition inclusions induces its literal ordinary-cone map
(Nekovář 1.1.3; tex 3413–3438). -/
def ordinaryConeTransport (i : GHom A B) (i' : GHom A' B')
    (p : GHom A A') (q : GHom B B')
    (hsq : ∀ (n : ℤ) (a : A.X n),
      q.f n n rfl (i.f n n rfl a) = i'.f n n rfl (p.f n n rfl a)) :
    GHom (ordinaryCone i) (ordinaryCone i') where
  f n m h := by
    subst m
    exact LinearMap.prodMap (q.f n n rfl) (p.f (n + 1) (n + 1) rfl)
  comm n n' m m' hnm hn hm hn'm' z := by
    subst m
    subst m'
    subst n'
    apply Prod.ext
    · change q.f (n + 1) (n + 1) rfl
        (B.d n (n + 1) rfl z.1 + i.f (n + 1) (n + 1) rfl z.2) =
      B'.d n (n + 1) rfl (q.f n n rfl z.1) +
        i'.f (n + 1) (n + 1) rfl (p.f (n + 1) (n + 1) rfl z.2)
      rw [map_add, hsq]
      exact congrArg (fun x => x + i'.f (n + 1) (n + 1) rfl
        (p.f (n + 1) (n + 1) rfl z.2)) (q.comm n (n + 1) n (n + 1) rfl rfl rfl rfl z.1)
    · change p.f (n + 1 + 1) (n + 1 + 1) rfl (-(A.d (n + 1) (n + 1 + 1) rfl z.2)) =
        -(A'.d (n + 1) (n + 1 + 1) rfl (p.f (n + 1) (n + 1) rfl z.2))
      rw [map_neg]
      exact congrArg Neg.neg (p.comm (n + 1) (n + 1 + 1) (n + 1) (n + 1 + 1)
        rfl rfl rfl rfl z.2)

end OrdinaryConeTransport

section ActualConeDictionary

open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: proved theorem; the inverse Tate dictionary identifies the
actual completion inclusion with the literal Kummer inclusion strictly
in every degree (tex 3413–3438; Milne I.3.4). -/
theorem actualConditionToLiteral_over_inverse_point (hloc : MilneLocalFiniteness) (n : ℤ)
    (u : (ActualSelfDual.localCondition K w (W.baseChange (w.adicCompletion K))).X n) :
    (natHom (localPointCochainInv (S := S) W w)).f n n rfl
      ((ActualSelfDual.localConditionMap K w (W.baseChange (w.adicCompletion K))).f n n rfl u) =
    (integralConditionMap (S := S) W w).f n n rfl
      ((actualConditionToLiteral (S := S) W w hloc).f n n rfl u) := by
  by_cases h0 : n = 0
  · subst n
    rfl
  by_cases h1 : n = 1
  · subst n
    rfl
  letI : Subsingleton ((ActualSelfDual.localCondition K w (W.baseChange (w.adicCompletion K))).X n) :=
    presentationCx_vanishes _ _ _ n (by omega)
  have hu : u = 0 := Subsingleton.elim _ _
  rw [hu, map_zero, map_zero, map_zero, map_zero]

/-- Kind: definition; the literal quotient cone for the original
integral local Kummer condition (tex 3413–3438; Nekovář 6.3.1). -/
abbrev literalLocalQuotientCone := ordinaryCone (integralConditionMap (S := S) W w)

/-- Kind: definition with proved cochain fields; the actual completion
quotient cone maps to the literal integral Kummer quotient cone using
the two fixed comparison maps (tex 3413–3438; Nekovář 6.3.1). -/
def actualConeToLiteral (hloc : MilneLocalFiniteness) :
    GHom (ActualSelfDual.localQuotientCone K w (W.baseChange (w.adicCompletion K)))
      (literalLocalQuotientCone (S := S) W w) :=
  ordinaryConeTransport (ActualSelfDual.localConditionMap K w (W.baseChange (w.adicCompletion K)))
    (integralConditionMap (S := S) W w) (actualConditionToLiteral (S := S) W w hloc)
    (natHom (localPointCochainInv (S := S) W w))
    (actualConditionToLiteral_over_inverse_point W w hloc)

/-- Kind: proved theorem; the quotient-cone comparison retains its
actual continuous cochain component and actual Kummer component
(tex 3413–3438; Nekovář 6.3.1). -/
theorem actualConeToLiteral_apply (hloc : MilneLocalFiniteness) (n : ℤ)
    (x : (ActualSelfDual.localQuotientCone K w (W.baseChange (w.adicCompletion K))).X n) :
    (actualConeToLiteral (S := S) W w hloc).f n n rfl x =
      ((natHom (localPointCochainInv (S := S) W w)).f n n rfl x.1,
        (actualConditionToLiteral (S := S) W w hloc).f (n + 1) (n + 1) rfl x.2) := rfl

end ActualConeDictionary

section LiteralComparisonMap

open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.SelfDualCore

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: definition with proved support and isotropy fields; the
canonical comparison on the literal integral local Kummer quotient
cone uses the globally oriented coefficient dictionary
(tex 3413–3450; Milne I.3.4; Nekovář 6.3.1). -/
def literalLocalSelfDualComparison (hM : MilneLocalDualityPrint) :
    GHom (literalLocalQuotientCone (S := S) W w) (dualCx (integralCondition (S := S) W w) 2) :=
  selfDualConeComparison (integralConditionMap (S := S) W w)
    (natPair (restrictedIntegralCup (S := S) W w)) (orientedLocalTrace (S := S) W w)
    (orientedLocalTrace_boundary W w)
    (integralKummerCondition_support W w)
    (fun u v => by
      change orientedLocalTrace (S := S) W w
        ((restrictedIntegralCup W w).P 1 1 2 rfl u.val v.val) = 0
      rw [orientedLocalTrace_cup_one]
      exact kummerTracePair_condition W w hM u v)

/-- Kind: proved theorem; the literal comparison evaluates the same
continuous cup product and canonical scalar trace, with no replacement
of its map (tex 3413–3450; Nekovář 6.3.1). -/
theorem literalLocalSelfDualComparison_apply (hM : MilneLocalDualityPrint) (n : ℤ)
    (x : (literalLocalQuotientCone (S := S) W w).X n)
    (u : (integralCondition (S := S) W w).X (2 - n)) :
    asDual ((literalLocalSelfDualComparison (S := S) W w hM).f n n rfl x) u =
      orientedLocalTrace (S := S) W w
        ((natPair (restrictedIntegralCup W w)).P n (2 - n) 2 (by omega) x.1
          ((integralConditionMap (S := S) W w).f (2 - n) (2 - n) rfl u)) := rfl

end LiteralComparisonMap

section LiteralFirstOrthogonality

open TauCeti TauCeti.ContCohomology
open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC53Assist.CentralKummer
open ZInQ.Manuscript.RC.LambdaCoef
open ZInQ.Contrib.RC53Assist.InnerLimitArith (MilneLocalFiniteness)
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.IntegralPairing
open ZInQ.Contrib.RC53Assist.DerivedKummerActual.TransportedLocal

variable {K : Type} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))} (W : WeierstrassCurve K)
  [W.IsElliptic] [HasFullTwoTorsion K S W]
  (w : HeightOneSpectrum (𝓞 K)) [DecidableEq (w.adicCompletion K)]

/-- Kind: proved arithmetic theorem; the canonical trace annihilator of
the entire literal Kummer condition in degree one is the literal
Kummer condition itself, including continuous boundaries
(tex 3413–3450; Milne I.3.4). -/
theorem literal_first_trace_annihilator (hM : MilneLocalDualityPrint)
    (hloc : MilneLocalFiniteness)
    (c : LinearMap.ker ((restrictedPointComplex (S := S) W w).d 1 2).hom)
    (hc : ∀ u : (integralCondition (S := S) W w).X 1,
      orientedLocalTrace (S := S) W w ((restrictedIntegralCup W w).P 1 1 2 rfl u.val c.val) = 0) :
    c.val ∈ tateKummerZ W (HasFullTwoTorsion.full (K := K) (S := S) (W := W)) w ⊔
      contB1 ℤ_[2] (Gloc K w) (ResMod (locMap K S w) (TateS K S W)) := by
  let B := W.baseChange (w.adicCompletion K)
  let p := localPointCycleMap (S := S) W w c
  have hp : ∀ u : Fin (actualLocalPresentation K w B).rankZero → ℤ_[2],
      AllCochainTrace.trv (w.adicCompletion K)
        (integralCupOne (w.adicCompletion K) B (localKummerOne K w B u).val p.val) = 0 := by
    intro u
    have h := hc ((actualConditionToLiteral (S := S) W w hloc).f 1 1 rfl u)
    rw [orientedLocalTrace_cup_one] at h
    have hs := actualConditionToLiteral_over_point (S := S) W w hloc 1 u
    change ((localPointCochainMap (S := S) W w).f 1).hom
      ((actualConditionToLiteral (S := S) W w hloc).f 1 1 rfl u).val = (localKummerOne K w B u).val at hs
    change AllCochainTrace.trv (w.adicCompletion K)
      (integralCupOne (w.adicCompletion K) B
        (((localPointCochainMap (S := S) W w).f 1).hom
          ((actualConditionToLiteral (S := S) W w hloc).f 1 1 rfl u).val) p.val) = 0 at h
    rw [hs] at h
    exact h
  obtain ⟨u, b, hb⟩ := SourceIntegralImage.local_integral_annihilator_of_print K w B hM p hp
  have hfinite : ∀ a, pointH1Reduction (w.adicCompletion K) B a p ∈
      (B.kummerMap (2 ^ a) (twoPower_isUnit (w.adicCompletion K) a)).range := by
    intro a
    let z := p - localKummerOne K w B u
    have hz := ActualConeModels.point_reduction_boundary K w B a z b hb
    change pointH1Reduction (w.adicCompletion K) B a (p - localKummerOne K w B u) = 0 at hz
    rw [map_sub, sub_eq_zero] at hz
    rw [hz]
    exact localKummerOne_mem_genuine_Kummer K w B a u
  have h := literal_kummer_mem_of_all_finite_images (S := S) W w hloc p hfinite
  have hi := congrArg (fun k => (k.f 1).hom c.val) (localPointCochainMap_inv (S := S) W w)
  have he : ((localPointCochainInv (S := S) W w).f 1).hom p.val = c.val := by
    change ((localPointCochainInv (S := S) W w).f 1).hom
      (((localPointCochainMap (S := S) W w).f 1).hom c.val) = c.val
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.hom_comp,
      LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using hi
  rw [he] at h
  exact h

end LiteralFirstOrthogonality

end ZInQ.Contrib.RC53Assist.DKLocalAdapter
