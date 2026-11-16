import ZInQKernel.Contrib.OneProof.SGA1Printed
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.QuasiProjective

open scoped Topology
open Filter Set CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

noncomputable section

namespace SerreGAGA

open UnifPrinted UnifTopology SGA1Printed SGA1Etale
open PkgI3 (AbVar)

/-- **Projective variety over `ℂ`** in Serre's sense (FAC, GAGA): a reduced closed subscheme of a
projective space `ℙ^N_ℂ` (`N` finite), as a `ℂ`-scheme. -/
def IsProjVar (X : Over (Spec (CommRingCat.of ℂ))) : Prop :=
  IsReduced X.left ∧
    ∃ (N : Type) (_ : Finite N) (i : X.left ⟶ ℙ(N; Spec (CommRingCat.of ℂ))),
      IsClosedImmersion i ∧ i ≫ ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ) = X.hom

/-- LEAF: Serre's GAGA for holomorphic maps of projective varieties. -/
def SerreGAGAMorphism : Prop :=
  ∀ (X Y : Over (Spec (CommRingCat.of ℂ))), IsProjVar X → IsProjVar Y →
    ∀ F : CPt X → CPt Y, IsAnMorphism X Y F → ∃ f : X ⟶ Y, ∀ P, F P = P ≫ f

/-- Abelian varieties are projective varieties. -/
theorem isProjVar (A : AbVar ℂ) : IsProjVar A.X := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  refine ⟨inferInstance, ?_⟩
  obtain ⟨N, hN, i, hi, hover⟩ :=
    GrpObj.exists_isImmersion_projectiveSpace_of_smooth_of_geometricallyIntegral A.X
  have : IsProper (i ≫ ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ)) := by
    rw [hover]; infer_instance
  have : IsProper i := IsProper.of_comp i (ℙ(N; Spec (CommRingCat.of ℂ)) ↘ Spec (CommRingCat.of ℂ))
  exact ⟨N, hN, i, .of_isPreimmersion i i.isClosedMap.isClosed_range, hover⟩

theorem sga1_XII_4_4_of_serre (h : SerreGAGAMorphism) : SGA1_XII_4_4 :=
  fun A B F hF => h A.X B.X (isProjVar A) (isProjVar B) F hF

theorem gagaMorphism_of_serre (hM : MumfordComplexTorus) (hL : SGA1_XII_3_3a)
    (hPC : ProperCompactAn) (hC : SGA1_XII_2_4) (hS : SerreGAGAMorphism) :
    ZInQ.HomLattice.GAGAMorphism :=
  gagaMorphism_of_printed hM hL hPC hC (sga1_XII_4_4_of_serre hS)

/-! Germ form -/

variable {X Y : Over (Spec (CommRingCat.of ℂ))}

theorem anFunAt_eventually [LocallyOfFiniteType X.hom] {F : CPt X → ℂ} {P : CPt X}
    (h : AnFunAt X F P) : ∀ᶠ Q in @nhds _ (analyticTopology X) P, AnFunAt X F Q := by
  letI := analyticTopology X
  obtain ⟨U, k, g, H, hPU, hH, hev⟩ := h
  have hcont : ContinuousAt (fun Q i => XevalAt X U (g i) Q) P :=
    continuousAt_pi.mpr fun i => continuousAt_xevalAt_an U (g i) hPU
  have hH' := hcont.eventually hH.eventually_analyticAt
  filter_upwards [(isOpen_ptIn_an U).mem_nhds hPU, hH', hev.eventually_nhds] with Q hQU hQH hQe
  exact ⟨U, k, g, H, hQU, hQH, hQe⟩

theorem isAnMorphism_iff_germ [LocallyOfFiniteType Y.hom] (F : CPt X → CPt Y) :
    IsAnMorphism X Y F ↔ @Continuous _ _ (analyticTopology X) (analyticTopology Y) F ∧
      ∀ (P : CPt X) (s : CPt Y → ℂ), AnFunAt Y s (F P) → AnFunAt X (s ∘ F) P := by
  letI := analyticTopology X
  letI := analyticTopology Y
  constructor
  · rintro ⟨hc, hF⟩
    refine ⟨hc, fun P s hs => ?_⟩
    have hmem : F P ∈ interior {Q | AnFunAt Y s Q} :=
      mem_interior_iff_mem_nhds.mpr (anFunAt_eventually hs)
    exact hF _ s isOpen_interior (fun Q hQ => (interior_subset (s := {Q | AnFunAt Y s Q}) hQ : AnFunAt Y s Q)) P hmem
  · rintro ⟨hc, hF⟩
    exact ⟨hc, fun W s _ hs P hP => hF P s (hs _ hP)⟩

/-! Serre's sheaf -/

/-- Affine chart inside a given open. -/
theorem exists_affineChart_le [LocallyOfFiniteType X.hom] {P : CPt X} {U : X.left.Opens}
    (hPU : XPtIn X P U) : ∃ c : AffineChart X, XPtIn X P c.U ∧ c.U ≤ U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    ((xPtIn_iff _ _).mp hPU) U.2
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType X.hom (inferInstance)
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by rw [Scheme.Hom.preimage_top]; exact le_top)
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom y, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ (Scheme.ΓSpecIso _).inv).hom y = y
    rw [Iso.hom_inv_id]; rfl
  have hft' : (algC X V).FiniteType :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ hsurj)
  letI := (algC X V).toAlgebra
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft'
  refine ⟨⟨V, hV, n, fun i => φ (MvPolynomial.X i), fun y => ?_⟩, (xPtIn_iff _ _).mpr hxV,
    fun x hx => hVU hx⟩
  obtain ⟨p, hp⟩ := hφ y
  refine ⟨p, ?_⟩
  rw [← hp]
  conv_rhs => rw [MvPolynomial.aeval_unique φ]
  rfl

/-- Serre's structure sheaf. -/
def SerreHolAt (X : Over (Spec (CommRingCat.of ℂ))) (F : CPt X → ℂ) (P : CPt X) : Prop :=
  ∃ c : AffineChart X, XPtIn X P c.U ∧ ∃ H : (Fin c.k → ℂ) → ℂ,
    AnalyticAt ℂ H (fun i => XevalAt X c.U (c.f i) P) ∧
    ∀ᶠ Q in @nhds _ (analyticTopology X) P, F Q = H (fun i => XevalAt X c.U (c.f i) Q)

theorem anFunAt_iff_serreHolAt [LocallyOfFiniteType X.hom] (F : CPt X → ℂ) (P : CPt X) :
    AnFunAt X F P ↔ SerreHolAt X F P := by
  letI := analyticTopology X
  constructor
  · rintro ⟨U, k, g, H, hPU, hH, hev⟩
    obtain ⟨c, hPc, hcU⟩ := exists_affineChart_le hPU
    choose p hp using fun j => c.generates (res hcU (g j))
    have hval : ∀ Q, XPtIn X Q c.U → (fun j => XevalAt X U (g j) Q) =
        fun j => MvPolynomial.eval (fun i => XevalAt X c.U (c.f i) Q) (p j) := by
      intro Q hQ; funext j
      rw [← xevalAt_res hcU (g j) hQ, ← hp j, xevalAt_eq_evP hQ, MvPolynomial.coe_eval₂Hom,
        evP_eval₂]
      simp only [xevalAt_eq_evP hQ]
    refine ⟨c, hPc, fun v => H (fun j => MvPolynomial.eval v (p j)), ?_, ?_⟩
    · refine AnalyticAt.comp (g := H) (f := fun v j => MvPolynomial.eval v (p j)) ?_
        (AnalyticAt.pi fun j => ?_)
      · rw [← hval P hPc]; exact hH
      · have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (A := ℂ) (B := ℂ)
          (f := fun v : Fin c.k → ℂ => v) (z := fun i => XevalAt X c.U (c.f i) P)
          (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.k => ℂ) i).analyticAt _)
          (p j)
        simpa [MvPolynomial.coe_aeval_eq_eval] using h
    · filter_upwards [hev, (isOpen_ptIn_an c.U).mem_nhds hPc] with Q hQ hQc
      rw [hQ, hval Q hQc]
  · rintro ⟨c, hPc, H, hH, hev⟩
    exact ⟨c.U, c.k, c.f, H, hPc, hH, hev⟩

theorem isAnMorphism_iff_serre [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (F : CPt X → CPt Y) :
    IsAnMorphism X Y F ↔ @Continuous _ _ (analyticTopology X) (analyticTopology Y) F ∧
      ∀ (P : CPt X) (s : CPt Y → ℂ), SerreHolAt Y s (F P) → SerreHolAt X (s ∘ F) P := by
  rw [isAnMorphism_iff_germ]
  simp only [← anFunAt_iff_serreHolAt]

#print axioms gagaMorphism_of_serre
#print axioms isAnMorphism_iff_germ
#print axioms anFunAt_iff_serreHolAt
#print axioms isAnMorphism_iff_serre

end SerreGAGA
