import Mathlib.Topology.Instances.ZMod
import ZInQKernel.HDecomp.Textbook.T10Etale

/-!
# The finite coefficient tower on the pro-étale site

These are the coefficient sheaves given by continuous maps to the finite residue rings.
The degree-zero difference operator is already surjective; passage through degree one
also needs a comparison of torsors or a suitable result on derived products.
-/

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped PadicInt

namespace ZInQ.Manuscript.T10Proetale

noncomputable section

universe u

variable (X : Scheme.{u}) (ℓ : ℕ)

/-- The small pro-étale sheaf of continuous functions into a topological abelian group. -/
def continuousCoefficients (B : Type) [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] : Sheaf (Scheme.ProEt.topology X) Ab.{u+1} :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{u+1}).obj <|
    (T10Etale.piX X).sheafPushforwardContinuous _ _ Scheme.proetaleTopology |>.obj
      ⟨continuousMapPresheafAb B, .of_le Scheme.proetaleTopology_le_fpqcTopology
        (isSheaf_fpqcTopology_continuousMapPresheafAb B)⟩

private def mapContinuousSections {U : Scheme.{u}} {B D : Type}
    [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]
    [TopologicalSpace D] [AddCommGroup D] [IsTopologicalAddGroup D]
    (f : B →+ D) (hf : Continuous f) :
    ULift.{u+1} C(U, B) →+ ULift.{u+1} C(U, D) where
  toFun x := ULift.up ((⟨f, hf⟩ : C(B, D)).comp x.down)
  map_zero' := ULift.ext (ContinuousMap.ext fun _ => f.map_zero)
  map_add' x y := ULift.ext (ContinuousMap.ext fun p => f.map_add (x.down p) (y.down p))

/-- Functoriality in a continuous additive coefficient map. -/
def mapContinuousCoefficients {B D : Type} [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] [TopologicalSpace D] [AddCommGroup D] [IsTopologicalAddGroup D]
    (f : B →+ D) (hf : Continuous f) :
    continuousCoefficients X B ⟶ continuousCoefficients X D :=
  ObjectProperty.homMk
    { app U := AddCommGrpCat.ofHom (mapContinuousSections (U := U.unop.left) f hf)
      naturality U V g := by ext x; rfl }

/-- Degree (i) with the finite pro-étale coefficients used in the reduction tower. -/
abbrev ProFiniteH (n i : ℕ) : Type (u + 1) :=
  (continuousCoefficients X (ZMod (ℓ ^ n))).H i

/-- Reduction from level (n+1) to (n), before taking cohomology. -/
abbrev residueStep (n : ℕ) : ZMod (ℓ ^ (n + 1)) →+* ZMod (ℓ ^ n) :=
  ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) _

/-- The map on cohomology induced by coefficient reduction. -/
def proTransition (n i : ℕ) : ProFiniteH X ℓ (n + 1) i →+ ProFiniteH X ℓ n i :=
  Sheaf.H.map (mapContinuousCoefficients X (residueStep ℓ n).toAddMonoidHom
    continuous_of_discreteTopology) i

/-- Reduction is onto on continuous sections over any object of the site.
A set-theoretic right inverse of the residue map is continuous on the finite discrete domain. -/
theorem residueStep_surjective_sections (n : ℕ) (U : X.ProEt) :
    Function.Surjective
      ((mapContinuousCoefficients X (residueStep ℓ n).toAddMonoidHom
        continuous_of_discreteTopology).hom.app (op U)) := by
  intro x
  let x' : C(U.left, ZMod (ℓ ^ n)) := x.down
  have h : Function.Surjective (residueStep ℓ n) :=
    ZMod.castHom_surjective (pow_dvd_pow ℓ (Nat.le_succ n))
  let s : C(ZMod (ℓ ^ n), ZMod (ℓ ^ (n + 1))) :=
    ⟨Function.surjInv h, continuous_of_discreteTopology⟩
  refine ⟨ULift.up (s.comp x'), ULift.ext (ContinuousMap.ext fun p => ?_)⟩
  exact Function.rightInverse_surjInv h (x' p)

/-- The degree-zero reduction maps are surjective on every scheme. -/
theorem proTransition_surjective_H0 (n : ℕ) :
    Function.Surjective (proTransition X ℓ n 0) := by
  intro y
  let hT := T10Etale.isTerminalProEt X
  let E (m : ℕ) := Sheaf.H.equiv₀ (continuousCoefficients X (ZMod (ℓ ^ m))) hT
  obtain ⟨s, hs⟩ := residueStep_surjective_sections X ℓ n (T10Etale.terminalProEt X) (E n y)
  refine ⟨(E (n + 1)).symm s, (E n).injective ?_⟩
  rw [← hs, proTransition, ← Sheaf.H.equiv₀_naturality]
  rw [(E (n + 1)).apply_symm_apply]

/-- For a countable tower with surjective transitions, the difference map on
the product is surjective. This is the degree-zero calculation needed for lim¹. -/
theorem difference_surjective {M : ℕ → Type*} [∀ n, AddGroup (M n)]
    (r : ∀ n, M (n+1) → M n) (hr : ∀ n, Function.Surjective (r n)) :
    Function.Surjective (fun x : ∀ n, M n => fun n => x n - r n (x (n+1))) := by
  intro y
  let x : ∀ n, M n := Nat.rec 0 (fun n a => Function.surjInv (hr n) (-y n + a))
  refine ⟨x, funext fun n => ?_⟩
  change x n - r n (Function.surjInv (hr n) (-y n + x n)) = y n
  rw [Function.rightInverse_surjInv (hr n) (-y n + x n)]
  simp [sub_eq_add_neg]

set_option maxHeartbeats 500000 in
/-- The cokernel model for lim¹ of the degree-zero tower vanishes. -/
theorem proH0_difference_surjective :
    Function.Surjective (fun x : ∀ n, ProFiniteH X ℓ n 0 =>
      fun n => x n - proTransition X ℓ n 0 (x (n + 1))) :=
  difference_surjective (M := fun n => ProFiniteH X ℓ n 0) (fun n => proTransition X ℓ n 0)
    (proTransition_surjective_H0 X ℓ)

variable [Fact ℓ.Prime]

/-- The coefficient reduction from the actual padic sheaf is continuous.
Its kernel contains an open ball around zero. -/
theorem continuous_toResidue (n : ℕ) :
    Continuous (PadicInt.toZModPow (p := ℓ) n) := by
  apply continuous_of_continuousAt_zero (PadicInt.toZModPow (p := ℓ) n).toAddMonoidHom
  rw [continuousAt_def]
  intro s hs
  have hs0 : (0 : ZMod (ℓ ^ n)) ∈ s := mem_of_mem_nhds (by simpa using hs)
  have hpos : 0 < (ℓ : ℝ) ^ (-(n : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : ℓ.Prime).pos) _
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℤ_[ℓ]) hpos) fun a ha => ?_
  have hker : PadicInt.toZModPow (p := ℓ) n a = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]
    apply (PadicInt.norm_le_pow_iff_mem_span_pow a n).mp
    exact le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using ha)
  show PadicInt.toZModPow (p := ℓ) n a ∈ s
  rwa [hker]

/-- The map from the row's cohomology to the pro-étale group at one finite stage. -/
def proReduction (n i : ℕ) : X.EllAdicCohomology ℓ i →+ ProFiniteH X ℓ n i :=
  Sheaf.H.map
    (mapContinuousCoefficients X (PadicInt.toZModPow (p := ℓ) n).toAddMonoidHom
      (continuous_toResidue ℓ n)) i

/-- The finite stage maps of the row's cohomology give a compatible sequence. -/
theorem proReduction_transition (n i : ℕ) (x : X.EllAdicCohomology ℓ i) :
    proTransition X ℓ n i (proReduction X ℓ (n + 1) i x) = proReduction X ℓ n i x := by
  let z : (continuousCoefficients X ℤ_[ℓ]).H i := x
  let r (m : ℕ) :=
    mapContinuousCoefficients X (PadicInt.toZModPow (p := ℓ) m).toAddMonoidHom
      (continuous_toResidue ℓ m)
  let s := mapContinuousCoefficients X (residueStep ℓ n).toAddMonoidHom
    continuous_of_discreteTopology
  have hr : r (n + 1) ≫ s = r n := by
    apply Sheaf.hom_ext
    ext U : 2
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro a
    let a' : C(U.unop.left, ℤ_[ℓ]) := a.down
    exact ULift.ext (ContinuousMap.ext fun p =>
      PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) (a' p))
  change Sheaf.H.map s i (Sheaf.H.map (r (n + 1)) i z) = Sheaf.H.map (r n) i z
  rw [← Sheaf.H.map_comp_apply, hr]

section Transport

variable {Y : Scheme.{u}} (e : X ≅ Y)

set_option backward.isDefEq.respectTransparency false

/-- An isomorphism of base schemes transports continuous coefficient functions unchanged
on each corresponding site object. -/
def continuousCoefficientsIso (B : Type) [TopologicalSpace B] [AddCommGroup B]
    [IsTopologicalAddGroup B] :
    (T10Etale.sheafEquiv e).functor.obj (continuousCoefficients X B) ≅
      continuousCoefficients Y B :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- The finite stage version of the row's transport, from the same equivalence of sites. -/
def proFiniteTransport (n i : ℕ) : ProFiniteH X ℓ n i →+ ProFiniteH Y ℓ n i :=
  ((Ext.mk₀ (T10Etale.constIso e _).inv).precomp _ (zero_add i)).comp
    (((Ext.mk₀ (continuousCoefficientsIso X e (ZMod (ℓ ^ n))).hom).postcomp _ (add_zero i)).comp
      ((T10Etale.sheafEquiv e).functor.mapExtAddHom _ _ i))

/-- Reducing the row's pro-étale cohomology commutes with the actual transport. -/
theorem proReduction_transport (n i : ℕ) (x : X.EllAdicCohomology ℓ i) :
    proReduction Y ℓ n i (T10Etale.transport ℓ e i x) =
      proFiniteTransport X ℓ e n i (proReduction X ℓ n i x) := by
  let r (S : Scheme.{u}) :=
    mapContinuousCoefficients S (PadicInt.toZModPow (p := ℓ) n).toAddMonoidHom
      (continuous_toResidue ℓ n)
  have hr : (T10Etale.sheafEquiv e).functor.map (r X) ≫
        (continuousCoefficientsIso X e (ZMod (ℓ ^ n))).hom =
      (T10Etale.ellIso ℓ e).hom ≫ r Y := by
    apply Sheaf.hom_ext
    ext U : 2
    rfl
  let z : (T10Etale.F X ℓ).H i := x
  change ((Ext.mk₀ (T10Etale.constIso e _).inv).comp
      ((z.mapExactFunctor (T10Etale.sheafEquiv e).functor).comp
        (Ext.mk₀ (T10Etale.ellIso ℓ e).hom) (add_zero i)) (zero_add i)).comp
      (Ext.mk₀ (r Y)) (add_zero i) =
    (Ext.mk₀ (T10Etale.constIso e _).inv).comp
      (((z.comp (Ext.mk₀ (r X)) (add_zero i)).mapExactFunctor
        (T10Etale.sheafEquiv e).functor).comp
        (Ext.mk₀ (continuousCoefficientsIso X e (ZMod (ℓ ^ n))).hom) (add_zero i)) (zero_add i)
  simp only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero,
    Ext.mk₀_comp_mk₀, hr]

end Transport

end

end ZInQ.Manuscript.T10Proetale
