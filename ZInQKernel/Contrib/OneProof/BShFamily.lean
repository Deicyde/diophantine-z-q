import ZInQKernel.Contrib.OneProof.BShFamilyAssembly
import ZInQKernel.Contrib.OneProof.BShFamilyCoordinates
import ZInQKernel.Contrib.OneProof.R16Thm1

/-! ON THE SPOT (provenance (c)): the simultaneous local matching
for the normalized generic curve proves the fixed standard-model row. -/

noncomputable section

namespace BShFamily

open BShTraces BShStandard ShimuraPointDict AfTateLam LeafModCurves PkgI3 PkgI3.AbVar
open AlgebraicGeometry CategoryTheory UpperHalfPlane Filter WeierstrassCurve
open scoped MatrixGroups Topology

variable {X : Over SpecQ} [IsIntegral X.left] {J : AbVar ℚ}
variable {N p : ℕ} {jX tX : X.left.functionField}
local notation "K" => X.left.functionField

theorem tendsto_punctured_branch (s : ℍ → ℍ) (hc : Continuous s) (hi : Function.Injective s)
    (τ : ℍ) : Tendsto s (𝓝[≠] τ) (𝓝[≠] (s τ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin (a := τ) (s := ({τ} : Set ℍ)ᶜ)] with z hz
  exact fun e => hz (hi e)

open T5Glue X1Igusa.Weber in
/-- Equality of the two restricted germs suffices to identify the two complex
punctured germs along any continuous injective branch reparametrization. -/
theorem pairedGerms_of_restrict
    {L : Type*} [Field L] (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX)
    (τ : ℍ) (s : ℍ → ℍ) (hc : Continuous s) (hi : Function.Injective s)
    (u : L →+* MeromorphicGerm (τ : ℂ)) (r : L × L)
    (hj : restrict τ (u r.1) = ((fun z : ℍ => Jf (s z)) : Germ (𝓝[≠] τ) ℂ))
    (ht : restrict τ (u r.2) = ((fun z : ℍ => Wf N (s z)) : Germ (𝓝[≠] τ) ℂ)) :
    PairedGerms hN hG τ (s τ) u r := by
  let f (z : ℂ) : ℂ := s (ofComplex z)
  have hs := tendsto_punctured_branch s hc hi τ
  have hcoe : Tendsto ofComplex (𝓝[≠] (τ : ℂ)) (𝓝[≠] τ) := by
    rw [← map_punctured_coe τ, tendsto_map'_iff]
    simp only [Function.comp_def, ofComplex_apply]
    exact tendsto_id
  have htcoe : Tendsto ((↑) : ℍ → ℂ) (𝓝[≠] (s τ)) (𝓝[≠] ((s τ : ℍ) : ℂ)) :=
    (map_punctured_coe (s τ)).le
  have hf : Tendsto f (𝓝[≠] (τ : ℂ)) (𝓝[≠] ((s τ : ℍ) : ℂ)) :=
    htcoe.comp (hs.comp hcoe)
  refine ⟨f,hf,?_,?_⟩
  · apply restrict_punctured_injective τ
    rw [(fieldGerm_coordinates hN hG (s τ)).1]
    change restrict τ (u r.1) = ((fun z : ℍ => Jf (f z)) : Germ (𝓝[≠] τ) ℂ)
    simpa only [f, ofComplex_apply] using hj
  · apply restrict_punctured_injective τ
    rw [(fieldGerm_coordinates hN hG (s τ)).2]
    change restrict τ (u r.2) = ((fun z : ℍ => Wf N (f z)) : Germ (𝓝[≠] τ) ℂ)
    simpa only [f, ofComplex_apply] using ht

theorem continuous_injective_shiftDiv (p i : ℕ) (hp : 0 < p) :
    Continuous (shiftDiv p i) ∧ Function.Injective (shiftDiv p i) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · apply isEmbedding_coe.continuous_iff.mpr
    simp only [Function.comp_def, HeckePin.coe_shiftDiv _ _ hp]
    exact (continuous_coe.add continuous_const).div_const (p : ℂ)
  · intro z w h
    have e := congrArg ((↑) : ℍ → ℂ) h
    simp only [HeckePin.coe_shiftDiv _ _ hp] at e
    exact UpperHalfPlane.coe_inj.mp (add_right_cancel ((div_left_inj' hp').mp e))

theorem continuous_injective_mulNat (p : ℕ) (hp : 0 < p) :
    Continuous (mulNat p) ∧ Function.Injective (mulNat p) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · apply isEmbedding_coe.continuous_iff.mpr
    simp only [Function.comp_def, HeckePin.coe_mulNat _ hp]
    exact continuous_const.mul continuous_coe
  · intro z w h
    have e := congrArg ((↑) : ℍ → ℂ) h
    simp only [HeckePin.coe_mulNat _ hp] at e
    exact UpperHalfPlane.coe_inj.mp (mul_left_cancel₀ hp' e)

open T5Glue X1Igusa.Weber PeriodPair in
/-- The local match of the normalized algebraic Vélu pair works on both
coordinates and uses the same choice of kernel for both. -/
theorem local_kernel_profiles (hN : 2 ≤ N) (hG : IsX1Gen N X jX tX) (hp : p.Prime) :
    let L := DivisionField jX p
    let E := curveG (modelG jX)
    let x := modelX jX tX
    let U := Kernel (E.map (algebraMap K L)) p N (algebraMap K L x)
    let r (i : U) := veluPair (algebraMap K L E.a₄) (algebraMap K L E.a₆) (algebraMap K L x) i.val
    ∀ τ : ℍ, ∃ (u : L →+* MeromorphicGerm (τ : ℂ)) (e : PrimeBranch N p ≃ U),
      ((meromorphicIncl _).comp u).comp (algebraMap K L) = fieldGerm hN hG τ ∧
      (∀ i : Fin p, PairedGerms hN hG τ (shiftDiv p i τ) u (r (e (.inl i)))) ∧
      (∀ (i : {u : Unit // ¬ p ∣ N}) (g : SL(2, ℤ)), (N : ℤ) ∣ g 1 0 →
        (g 1 1 : ZMod N) = (p : ZMod N) →
        PairedGerms hN hG τ (g • mulNat p τ) u (r (e (.inr i)))) := by
  dsimp only
  intro τ
  obtain ⟨u,e,hu,he⟩ := exists_local_kernel_equiv hN hG hp τ
  let E := curveG (modelG jX)
  let x := modelX jX tX
  let m := meromorphicFieldGerm hN hG τ
  let A (z : ℍ) := -((pp z).g₂ ^ 3 / (pp z).g₃ ^ 2 / 4)
  let C (z : ℍ) := normX z (1 / (N : ℂ))
  have h₄ : restrict τ (m E.a₄) = (A : Germ (𝓝[≠] τ) ℂ) := by
    have hg : restrict τ (m (modelG jX)) =
        ((fun s : ℍ => (pp s).g₂ ^ 3 / (pp s).g₃ ^ 2) : Germ (𝓝[≠] τ) ℂ) :=
      restrict_modelG hN hG τ
    simp only [E, curveG, map_neg, map_div₀, restrict_div_eq, map_ofNat, hg]
    rfl
  have h₆ : restrict τ (m E.a₆) = (A : Germ (𝓝[≠] τ) ℂ) := h₄
  have hx : restrict τ (m x) = (C : Germ (𝓝[≠] τ) ℂ) := restrict_modelX hN hG τ
  have hbase : ((meromorphicIncl _).comp u).comp (algebraMap K (DivisionField jX p)) =
      fieldGerm hN hG τ := by
    rw [RingHom.comp_assoc, hu]
    rfl
  have core (i : PrimeBranch N p) (s : ℍ → ℍ) (hc : Continuous s) (hi : Function.Injective s)
      (hpw : ∀ z : ℍ, (pp (s z)).g₂ ≠ 0 → (pp (s z)).g₃ ≠ 0 →
        markedLatticeCoordinates (cosets hp.pos (branchLine i) z) ⟨0,hp.pos⟩ (1 / (N : ℂ)) =
          (jL (pp (s z)), weber (pp (s z)) (1 / (N : ℂ)))) :
      PairedGerms hN hG τ (s τ) u
        (veluPair (algebraMap K _ E.a₄) (algebraMap K _ E.a₆) (algebraMap K _ x) (e i).val) := by
    let f (z : ℍ) := familyPair (A z) (A z) (C z)
      (fun k : Multiple p => normX z ((k.val.val : ℂ) * generator p (branchLine i) z))
    have mon := map_veluPair u (algebraMap K _ E.a₄) (algebraMap K _ E.a₆)
      (algebraMap K _ x) (e i).val
    have hmap (a : K) : u (algebraMap K _ a) = m a := DFunLike.congr_fun hu a
    simp only [hmap, he] at mon
    have hg : ∀ᶠ z : ℍ in 𝓝[≠] τ, f z = (Jf (s z), Wf N (s z)) := by
      filter_upwards [eventually_good τ, (tendsto_punctured_branch s hc hi τ).eventually
        (eventually_good (s τ))] with z hz hs
      rw [show f z = _ from normalized_familyPair_eq_lattice hp _ z N hz.1 hz.2,
        hpw z hs.1 hs.2, weber_eq_Wf _ hs.1 hs.2]
      simp [Jf, ofComplex_apply]
    have hr := restrict_analytic_pair hp τ (branchLine i) h₄ h₆ hx
    apply pairedGerms_of_restrict hN hG τ s hc hi u _
    · exact (congrArg (fun q => restrict τ q.1) mon).trans
        (hr.1.trans (Germ.coe_eq.mpr (hg.mono fun z hz => congrArg Prod.fst hz)))
    · exact (congrArg (fun q => restrict τ q.2) mon).trans
        (hr.2.trans (Germ.coe_eq.mpr (hg.mono fun z hz => congrArg Prod.snd hz)))
  refine ⟨u,e,hbase,?_,?_⟩
  · intro i
    obtain ⟨hc,hi⟩ := continuous_injective_shiftDiv p i hp.pos
    exact core (.inl i) _ hc hi (fun z h₂ h₃ => triangular_coordinates p hp.pos i z hN h₂ h₃)
  · intro i g hg hd
    obtain ⟨hc,hi⟩ := continuous_injective_mulNat p hp.pos
    let H := Homeomorph.smul (α := ℍ) (Matrix.SpecialLinearGroup.mapGL ℝ g)
    refine core (.inr i) (fun z => g • mulNat p z) (H.continuous.comp hc)
      (H.injective.comp hi) ?_
    intro z h₂ h₃
    obtain ⟨h₂',h₃'⟩ := (diamond_good g (mulNat p z)).mp ⟨h₂,h₃⟩
    have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hs := ppScale_isScale (p : ℂ)⁻¹ (inv_ne_zero hp') (mulNat p z)
    exact horizontal_coordinates p hp z hN i.property g hg hd
      (by rw [horizontal, hs.g₂]; exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (inv_ne_zero hp'))) h₂')
      (by rw [horizontal, hs.g₃]; exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (inv_ne_zero hp'))) h₃')

open X1Igusa.Weber in
/-- The marked quotient construction gives every prime trace on the fixed curve. -/
theorem exists_primeTrace (hN : 2 ≤ N) (hp : p.Prime) (hC : IsCurve X)
    (hG : IsX1Gen N X jX tX) (aj : X ⟶ J.X) :
    ∃ F : X ⟶ J.X, IsPrimeTrace jX tX aj N p F := by
  letI : CharZero K := charZero_of_injective_ringHom (baseMap X).injective
  letI : IsGalois K (DivisionField jX p) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  exact primeTrace_of_kernel_profiles hN hp hC hG aj (L := DivisionField jX p)
    (curveG (modelG jX)) (modelX jX tX) (local_kernel_profiles hN hG hp)

/-- The exact standard-model Hecke bridge. -/
theorem bShStandardModel_proof : R16Thm1.BShStandardModel := by
  apply bShStandardModel_of_primeTraces
  intro N hN X _ jX tX hC hG P₀ J aj hJ p
  exact exists_primeTrace hN p.property hC hG aj

/-- The exact Hecke existence statement for the fixed model. -/
theorem heckeJ1DS_proof : AfTateLam.HeckeJ1DS :=
  heckeJ1DS_of_bShStandardModel bShStandardModel_proof

#print axioms pairedGerms_of_restrict
#print axioms continuous_injective_shiftDiv
#print axioms continuous_injective_mulNat
#print axioms tendsto_punctured_branch
#print axioms local_kernel_profiles
#print axioms exists_primeTrace
#print axioms bShStandardModel_proof
#print axioms heckeJ1DS_proof

end BShFamily
