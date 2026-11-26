import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.Core
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.ArcAnalytic
import ZInQKernel.Contrib.OneProof.CuspFormDifferentials.LocalTopology
import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected
import ZInQKernel.Contrib.CloudB3W17Hodge.Port.Other.AlgebraicGeometry.ComplexPoint.SmoothConnected
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.CuspAssignment
import ZInQKernel.Contrib.OneProof.RC.X0Model2.JOrbit

/-! Every complex point of the complexified modular curve is either the image of a
point of the upper half-plane under the analytic arc, or one of the algebraic cusps.

The image of the arc is open by the open mapping theorem in charts, since the arc
is not locally constant (the analytic `j`-function is not). Its closure adds only the
finitely many cusp limits, one for each coset of `Γ₀(N)` in `SL(2, ℤ)`, through the
fundamental domain. The curve is integral (it is smooth and geometrically connected,
with a rational cusp), so its complex points are connected, and they stay connected
after removing finitely many points. The holomorphy of the arc is the separate target
statement `K4`; the main results are stated with it as an explicit hypothesis and then
specialized to the holomorphy theorem `mdifferentiable_arcPoint`. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Filter Set UpperHalfPlane Topology PkgI3
open scoped Manifold MatrixGroups

namespace ZInQ.Manuscript.RC.CuspFormDifferentials

open J0Cusps

variable (N : ℕ) [NeZero N]

/-- The statement `K4`: the analytic point map is holomorphic. -/
def K4Statement : Prop :=
  MDifferentiable 𝓘(ℂ) 𝓘(ℂ, Fin 1 → ℂ) (arcPoint N)

/-- The complex point of the algebraic cusp attached to a cusp orbit. -/
def cuspPoint (c : cuspIndex N) : ComplexPoint (curveC N) :=
  complexLift (extendPoint (algebraicCusp N c))

instance curveC_t2 : T2Space (ComplexPoint (curveC N)) := source_t2 N

theorem arcPoint_smul_surj (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) (τ : ℍ) :
    arcPoint N (γ • τ) = arcPoint N τ := by
  unfold arcPoint
  congr 1
  apply Over.OverMorphism.ext
  exact X0Model2.complexPoint_smul N γ hγ τ

theorem complexPoint_eq_of_arcPoint_eq_surj {τ σ : ℍ} (h : arcPoint N τ = arcPoint N σ) :
    X0Model.complexPoint N τ = X0Model.complexPoint N σ := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
  have eval (a : AbVar.ptObj (K := ℚ) ℂ ⟶ source N) :
      (complexLift a).left ≫ Limits.pullback.fst (source N).hom f = a.left :=
    Limits.pullback.lift_fst _ _ _
  have := (eval (interior N τ)).symm.trans ((congrArg (fun z : ComplexPoint (curveC N) =>
    z.left ≫ Limits.pullback.fst (source N).hom f) h).trans (eval (interior N σ)))
  exact this

theorem analyticJ_eq_of_arcPoint_eq {τ σ : ℍ} (h : arcPoint N τ = arcPoint N σ) :
    X0Model.analyticJ τ = X0Model.analyticJ σ :=
  X0Model2.analyticJ_eq_of_complexPoint_eq N τ σ (complexPoint_eq_of_arcPoint_eq_surj N h)

/-- The analytic `j`-function is not constant near any point. -/
theorem analyticJ_not_eventually_const (τ : ℍ) :
    ¬ ∀ᶠ z in 𝓝 τ, X0Model.analyticJ z = X0Model.analyticJ τ := by
  intro h
  let U : Set ℂ := {z | 0 < z.im}
  have hU : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  have hc : ContinuousAt UpperHalfPlane.ofComplex (τ : ℂ) :=
    UpperHalfPlane.ofComplex.continuousAt (by simpa [UpperHalfPlane.ofComplex] using τ.im_pos)
  have h' : (X0Model.analyticJ ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      (fun _ => X0Model.analyticJ τ) := by
    have ht : Tendsto UpperHalfPlane.ofComplex (𝓝 (τ : ℂ)) (𝓝 τ) := by
      have := hc.tendsto
      rwa [UpperHalfPlane.ofComplex_apply] at this
    exact ht.eventually h
  have hEq := X0Model.analyticOn_j.eqOn_of_preconnected_of_eventuallyEq
    (analyticOnNhd_const) hU τ.im_pos h'
  let z₁ : ℍ := ⟨2 * Complex.I, by simp⟩
  let z₂ : ℍ := ⟨3 * Complex.I, by simp⟩
  have h₁ := hEq (show (z₁ : ℂ) ∈ U from z₁.im_pos)
  have h₂ := hEq (show (z₂ : ℂ) ∈ U from z₂.im_pos)
  simp only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] at h₁ h₂
  obtain ⟨γ, hγ⟩ := (X0Model2.analyticJ_eq_iff z₁ z₂).mp (h₁.trans h₂.symm)
  have hz₁ : z₁ ∈ ModularGroup.fdo := by
    constructor <;> norm_num [z₁, Complex.normSq_apply]
  have hz₂ : γ • z₁ ∈ ModularGroup.fdo := by
    rw [hγ]
    constructor <;> norm_num [z₂, Complex.normSq_apply]
  have := ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hz₁ hz₂
  rw [hγ] at this
  have him := congrArg UpperHalfPlane.im this
  simp [z₁, z₂] at him

/-- The analytic arc is not constant near any point. -/
theorem arcPoint_not_eventually_const (τ : ℍ) :
    ¬ ∀ᶠ z in 𝓝 τ, arcPoint N z = arcPoint N τ := fun h =>
  analyticJ_not_eventually_const τ (h.mono fun _ hz => analyticJ_eq_of_arcPoint_eq N hz)

/-- Representatives of the cosets of `Γ₀(N)`: every element of `SL(2, ℤ)` is an element
of `Γ₀(N)` times one of them. -/
def cosetRep (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) : SL(2, ℤ) := (Quotient.out q)⁻¹

omit [NeZero N] in
theorem exists_cosetRep (σ : SL(2, ℤ)) :
    ∃ q, ∃ k ∈ CongruenceSubgroup.Gamma0 N, σ = k * cosetRep N q := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) σ⁻¹
  refine ⟨(σ⁻¹ : SL(2, ℤ)), h, h.2, ?_⟩
  rw [cosetRep, hh]
  group

instance : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
  Subgroup.finite_quotient_of_finiteIndex

/-- The finitely many cusp points reached from the coset representatives. -/
def cuspSet : Set (ComplexPoint (curveC N)) :=
  Set.range fun q => cuspPoint N (orbitOfSL N (cosetRep N q))

theorem cuspSet_finite : (cuspSet N).Finite := Set.finite_range _

theorem range_arcPoint_eq :
    Set.range (arcPoint N) =
      ⋃ q, (fun z => arcPoint N (cosetRep N q • z)) '' ModularGroup.fd := by
  ext p
  constructor
  · rintro ⟨τ, rfl⟩
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    obtain ⟨q, k, hk, hσ⟩ := exists_cosetRep N g⁻¹
    refine mem_iUnion.mpr ⟨q, g • τ, hg, ?_⟩
    change arcPoint N (cosetRep N q • g • τ) = arcPoint N τ
    rw [← arcPoint_smul_surj N k hk, ← mul_smul, ← mul_smul, ← hσ, inv_mul_cancel, one_smul]
  · intro hp
    obtain ⟨q, z, _, rfl⟩ := mem_iUnion.mp hp
    exact ⟨_, rfl⟩

theorem closure_range_arcPoint_subset (hK4 : K4Statement N) :
    closure (Set.range (arcPoint N)) ⊆ Set.range (arcPoint N) ∪ cuspSet N := by
  rw [range_arcPoint_eq, closure_iUnion_of_finite]
  refine iUnion_subset fun q => ?_
  let f := fun z : ℍ => arcPoint N (cosetRep N q • z)
  have hsmul : Continuous fun z : ℍ => cosetRep N q • z := by
    have : (fun z : ℍ => cosetRep N q • z) =
        fun z : ℍ => ((cosetRep N q : GL (Fin 2) ℝ) • z) := by
      funext z; rfl
    rw [this]
    exact continuous_const_smul _
  have hf : Continuous f := hK4.continuous.comp hsmul
  have hlim : Tendsto f atImInfty (𝓝 (cuspPoint N (orbitOfSL N (cosetRep N q)))) :=
    algebraicCusp_limit N (cosetRep N q)
  have hsub := closure_image_subset_insert hf (S := ModularGroup.fd)
    (L := cuspPoint N (orbitOfSL N (cosetRep N q))) (fun V hV => by
      obtain ⟨A, hA⟩ := (atImInfty_mem _).mp (hlim hV)
      refine ⟨ModularGroup.truncatedFundamentalDomain A, fun x hx => hx.1,
        ModularGroup.isCompact_truncatedFundamentalDomain A, fun x hx hxK => ?_⟩
      exact hA x (le_of_lt (not_le.mp fun h => hxK ⟨hx, h⟩)))
  refine hsub.trans ?_
  rintro p (rfl | hp)
  · exact Or.inr ⟨q, rfl⟩
  · exact Or.inl (mem_iUnion.mpr ⟨q, hp⟩)

theorem isOpen_range_arcPoint (hK4 : K4Statement N) : IsOpen (Set.range (arcPoint N)) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨τ, rfl⟩
  exact range_mem_nhds_of_mdifferentiable hK4 τ (arcPoint_not_eventually_const N τ)

/-- The complexified curve is integral. -/
theorem curveC_isIntegral : IsIntegral (curveC N).left := by
  let : IsIntegral (source N).left := X0Model.integral N
  have hsmooth : Smooth (curveC N).hom := SmoothOfRelativeDimension.smooth 1 _
  have hgcQ : GeometricallyConnected (source N).hom :=
    geometricallyConnected_of_connectedSpace_of_section (source N).hom (X0Model.cusp N)
      (X0Model.cusp_overQ N)
  have hgc : GeometricallyConnected (curveC N).hom :=
    (geometricallyConnected_iff_baseChange_fieldExtension ℚ ℂ (source N).hom).mp hgcQ
  let p := arcPoint N UpperHalfPlane.I
  exact isIntegral_of_smooth_of_geometricallyConnected ℂ (curveC N).hom hsmooth hgc p.left
    (by simpa using Over.w p)

instance curveC_connected : ConnectedSpace (ComplexPoint (curveC N)) := by
  let := curveC_isIntegral N
  have : Smooth (curveC N).hom := SmoothOfRelativeDimension.smooth 1 _
  let : IsProper (source N).hom := X0Model.proper N
  have : IsProper (curveC N).hom := by
    change IsProper (Limits.pullback.snd (source N).hom
      (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))))
    infer_instance
  have : QuasiSeparatedSpace (curveC N).left :=
    quasiSeparatedSpace_of_quasiSeparated (curveC N).hom
  exact ComplexPoint.connectedSpace (curveC N)

/-- **K10.** Assuming the holomorphy statement `K4`, every complex point of the
complexified modular curve is a point of the analytic arc or an algebraic cusp. -/
theorem complexPoint_eq_arcPoint_or_cusp_of_K4 (hK4 : K4Statement N)
    (p : ComplexPoint (curveC N)) :
    (∃ τ : ℍ, p = arcPoint N τ) ∨ ∃ c : cuspIndex N, p = cuspPoint N c := by
  let A := Set.range (arcPoint N)
  let C := cuspSet N
  have hA : IsOpen A := isOpen_range_arcPoint N hK4
  have hC : C.Finite := cuspSet_finite N
  have hZ : IsClosed (A ∪ C) := by
    refine closure_subset_iff_isClosed.mp ?_
    rw [closure_union, hC.isClosed.closure_eq]
    exact union_subset (closure_range_arcPoint_subset N hK4) subset_union_right
  have hV : IsPreconnected Cᶜ :=
    isPreconnected_compl_of_finite (fun c O hO => exists_open_punctured_preconnected c O hO) C hC
  have hcov : Cᶜ ⊆ A ∪ (A ∪ C)ᶜ := by
    intro x _
    by_cases hx : x ∈ A
    · exact Or.inl hx
    · right
      rintro (h | h)
      · exact hx h
      · exact ‹x ∈ Cᶜ› h
  have hdisj : Disjoint A (A ∪ C)ᶜ := Set.disjoint_left.mpr fun x hx h => h (Or.inl hx)
  rcases hV.subset_or_subset hA hZ.isOpen_compl hdisj hcov with h | h
  · by_cases hp : p ∈ C
    · obtain ⟨q, rfl⟩ := hp
      exact Or.inr ⟨_, rfl⟩
    · obtain ⟨τ, hτ⟩ := h hp
      exact Or.inl ⟨τ, hτ.symm⟩
  · exfalso
    -- the arc would land in the finite set of cusp points
    have hAC : A ⊆ C := by
      intro x hx
      by_contra hxC
      exact (h hxC) (Or.inl hx)
    let τ := UpperHalfPlane.I
    let p₀ := arcPoint N τ
    have hO : IsOpen (C \ {p₀})ᶜ := ((hC.subset sdiff_subset).isClosed).isOpen_compl
    have hp₀ : p₀ ∈ (C \ {p₀})ᶜ := fun h => h.2 rfl
    have hev : ∀ᶠ z in 𝓝 τ, arcPoint N z ∈ (C \ {p₀})ᶜ :=
      hK4.continuous.continuousAt.preimage_mem_nhds (hO.mem_nhds hp₀)
    apply arcPoint_not_eventually_const N τ
    filter_upwards [hev] with z hz
    by_contra hne
    exact hz ⟨hAC ⟨z, rfl⟩, hne⟩

/-- **K10**, for closed points of the underlying scheme. -/
theorem closedPoint_eq_arcPoint_or_cusp_of_K4 (hK4 : K4Statement N) (x : (curveC N).left)
    (hx : x ∈ closedPoints (curveC N).left) :
    (∃ τ : ℍ, (arcPoint N τ).underlying = x) ∨
      ∃ c : cuspIndex N, (cuspPoint N c).underlying = x := by
  have : LocallyOfFiniteType (curveC N).hom := by
    have := SmoothOfRelativeDimension.smooth 1 (curveC N).hom
    infer_instance
  let w := (pointEquivClosedPoint (curveC N).hom).symm ⟨x, hx⟩
  let z : ComplexPoint (curveC N) := Over.homMk w.1 w.2
  have hz : z.underlying = x :=
    congrArg Subtype.val ((pointEquivClosedPoint (curveC N).hom).apply_symm_apply ⟨x, hx⟩)
  rcases complexPoint_eq_arcPoint_or_cusp_of_K4 N hK4 z with ⟨τ, hτ⟩ | ⟨c, hc⟩
  · exact Or.inl ⟨τ, hτ ▸ hz⟩
  · exact Or.inr ⟨c, hc ▸ hz⟩

/-- **K10**: every complex point of the complexified modular curve is a point of the
analytic arc or an algebraic cusp. -/
theorem complexPoint_eq_arcPoint_or_cusp (p : ComplexPoint (curveC N)) :
    (∃ τ : ℍ, p = arcPoint N τ) ∨ ∃ c : cuspIndex N, p = cuspPoint N c :=
  complexPoint_eq_arcPoint_or_cusp_of_K4 N (mdifferentiable_arcPoint N) p

/-- **K10**: every closed point of the complexified modular curve is the underlying
point of a point of the analytic arc or of an algebraic cusp. -/
theorem closedPoint_eq_arcPoint_or_cusp (x : (curveC N).left)
    (hx : x ∈ closedPoints (curveC N).left) :
    (∃ τ : ℍ, (arcPoint N τ).underlying = x) ∨
      ∃ c : cuspIndex N, (cuspPoint N c).underlying = x :=
  closedPoint_eq_arcPoint_or_cusp_of_K4 N (mdifferentiable_arcPoint N) x hx

end ZInQ.Manuscript.RC.CuspFormDifferentials
