import ZInQKernel.Contrib.OneProof.SGRDirectNV
import ZInQKernel.Contrib.OneProof.STQM
import ZInQKernel.Contrib.OneProof.GR56Lattice

/-! # Hecke automorphisms on the finite normalization chart

ON THE SPOT (provenance (c)): descend the already constructed `w₆` isomorphism
for CM(−24), and transfer the Hecke actions to the finite Galois extension by
counting one generically étale fibre.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.LeafQM _root_.LeafQM.AV HDec.LeafQM.AV.Pin.Exact
open GlueDescent.B2Q
open HDec HDec.G0ModField HDec.PropTSRed HDec.TSHecke

namespace SGRDirect.HeckeSqrt

/-- The CM(−24) pair is fixed by `w₆`. Over `ℂ` the integral intertwiner is
`ι(ij) φ / 6`, where `φ² = −6` in the commutant (the construction in
`GapST.twist_of_cm`). Base change and descent transfer it to `ℚ̄`. -/
theorem cm24_fixed (hT : PkgI2.TorsionStructure.{0})
    (hU : ZInQ.LeafPush2.UniformizationExists) (hC : HDec.HomUnify.HomLatticeCorr)
    (hA : HeckeRest.QMAutCard) (P : QMPair Qbar) (hP : HasCM24 P.q) :
    Nonempty (QMIso (P.q.twist (rep 3)) P.q) := by
  let Q := GR56.bcQ P
  obtain ⟨e⟩ := GR56.com_bcQ P
  obtain ⟨φ, hφ, hsq⟩ := hP
  let f : com P.q := ⟨φ, hφ⟩
  have hf : f * f = -6 := Subtype.ext hsq
  have hs24 : e f * e f = -6 := by rw [← map_mul, hf, map_neg, map_ofNat]
  have h24 : HasCM24 Q.q := ⟨e f, (e f).2, congrArg Subtype.val hs24⟩
  have excl := (hA P.A P.surface P.q).2
  -- Rule out the other two cases after descending their commutant witnesses.
  have n4 : ¬ HasCM4 Q.q := by
    rintro ⟨x, hx, hxx⟩
    let z := e.symm ⟨x, hx⟩
    have hz : z * z = -1 := by
      apply e.injective
      simp only [map_mul, map_neg, map_one, z, RingEquiv.apply_symm_apply]
      exact Subtype.ext hxx
    exact excl.2.1 ⟨⟨z, z.2, congrArg Subtype.val hz⟩, ⟨φ, hφ, hsq⟩⟩
  have n3 : ¬ HasCM3 Q.q := by
    rintro ⟨x, hx, hxx⟩
    let z := e.symm ⟨x, hx⟩
    have hz : z * z - z + 1 = 0 := by
      apply e.injective
      simp only [map_mul, map_sub, map_add, map_one, map_zero, z, RingEquiv.apply_symm_apply]
      exact Subtype.ext hxx
    exact excl.2.2 ⟨⟨z, z.2, congrArg Subtype.val hz⟩, ⟨φ, hφ, hsq⟩⟩
  rcases GapST.twist_of_cm hT hU hC Q.surface Q.q (Or.inr (Or.inr h24)) with
    h | h | ⟨_, ⟨iso⟩⟩
  · exact (n4 h.1).elim
  · exact (n3 h.1).elim
  exact GR56.qmIso_descend (P.twist (rep 3)) P iso.symm

/-- A fixed QM pair yields a fixed full level class after adjusting the marking. -/
theorem fixed_level (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar)
    (α : O ≃+* O) (G : QMIso (P.q.twist α) P.q) :
    ∃ u : Oˣ, M3.rightMul u (M3.twist α (M3.mk P)) = M3.mk P := by
  let e₀ : Level3 (P.twist α).q := pullLevel G P.e
  obtain ⟨u₀, v₀, hvu, hu⟩ := Level3.torsor hT (P.twist α) e₀
  obtain ⟨u, d, hd⟩ := TSHeckeUnits.exists_unit_congr u₀ v₀ hvu
  have he : (P.twist α).e.rightMul u = e₀ := Level3.ext' (AddMonoidHom.ext fun a => by
    rw [hu a]
    show (P.twist α).e.eta (a * u) = (P.twist α).e.eta (a * u₀)
    rw [(P.twist α).e.eq_iff]
    exact ⟨-(a * d), by rw [← _root_.mul_sub, ← neg_sub, hd]; noncomm_ring⟩)
  refine ⟨u, Quotient.sound ⟨?_⟩⟩
  show QML3.Iso ⟨P.A, P.surface, (P.twist α).q, (P.twist α).e.rightMul u⟩ P
  rw [he]
  exact pullIso P.surface P.surface G P.e

section Chart

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E]
  {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {Φ : PtEquiv Y}

local notation "B₀" => integralClosure ℚ[X] E
local notation "G₀" => Gal(E / RatFunc ℚ)

instance galComm : SMulCommClass G₀ ℚ[X] E := ⟨fun g a x => by
  rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
    IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E, AlgEquiv.commutes]⟩

theorem poly_injective : Function.Injective (algebraMap ℚ[X] E) := by
  rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
  exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))

/-- The finite chart with its point identification. -/
structure Chart (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) (E : Type)
    [Field E] [Algebra ℚ[X] E] where
  h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left
  isOpen : IsOpenImmersion h
  img : ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.infty →
    ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure ℚ[X] E)), y = y' ≫ h
  val : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
    π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
      OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X))

attribute [instance] Chart.isOpen

def Chart.point (D : Chart Y π E) (ψ : B₀ →+* Qbar) : fieldPt Qbar ⟶ Y :=
  Over.homMk (Spec.map (CommRingCat.ofHom ψ) ≫ D.h) (TSHeckeGal.specQbar_to_specQ_eq' _ _)

theorem Chart.point_injective (D : Chart Y π E) : Function.Injective D.point := by
  intro ψ ψ' e
  have h := congrArg Over.Hom.left e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono D.h).1 h))

theorem Chart.exists_point (D : Chart Y π E) (y : fieldPt Qbar ⟶ Y)
    (hy : π.val (K := Qbar) y.left ≠ OnePoint.infty) : ∃ ψ, D.point ψ = y := by
  obtain ⟨z, hz⟩ := D.img y.left hy
  refine ⟨(Spec.preimage z).hom, ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (Spec.preimage z).hom) ≫ D.h = y.left
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, hz]

/-- Restrict a Galois automorphism to the integral closure. -/
def ringAction (τ : G₀) : B₀ →+* B₀ := MulSemiringAction.toRingHom _ _ τ

@[simp] theorem ringAction_apply (τ : G₀) (b : B₀) :
    (ringAction τ b : E) = τ (b : E) := rfl

theorem ringAction_mul (τ υ : G₀) : ringAction (τ * υ) = (ringAction τ).comp (ringAction υ) :=
  RingHom.ext fun _ => Subtype.ext rfl

theorem inertia_iff_stabilizes (ψ : B₀ →+* Qbar) (τ : G₀) :
    τ ∈ InertiaQ E (RingHom.ker ψ) ↔ ψ.comp (ringAction τ) = ψ := by
  constructor
  · intro h
    ext b
    obtain ⟨c, hc, hcb⟩ := h b
    have he : c = ringAction τ b := Subtype.ext hc
    rw [RingHom.comp_apply, ← he]
    exact sub_eq_zero.mp (by simpa only [RingHom.mem_ker, map_sub] using hcb)
  · intro h b
    refine ⟨ringAction τ b, rfl, ?_⟩
    rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply, h, sub_self]

variable [FiniteDimensional (RatFunc ℚ) E]

theorem Chart.exists_aut (D : Chart Y π E) [LocallyOfFiniteType Y.hom] (g : Y ⟶ Y)
    (hg : ∀ z : fieldPt Qbar ⟶ Y, π.val (K := Qbar) (z ≫ g).left = π.val (K := Qbar) z.left) :
    ∃ τ : G₀, ∀ ψ, D.point (ψ.comp (ringAction τ)) = D.point ψ ≫ g := by
  obtain ⟨σ, hσh, hσX⟩ := TSHeckeGal.exists_sigma D.h D.img D.val g.left
    (fun z => hg (Over.homMk z (TSHeckeGal.specQbar_to_specQ_eq' _ _)))
  obtain ⟨τ, hτ⟩ := TSHeckeGal.exists_tau σ hσX
  have hσ : ringAction τ = σ := RingHom.ext fun b => Subtype.ext (hτ b)
  refine ⟨τ, fun ψ => ?_⟩
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (ψ.comp (ringAction τ))) ≫ D.h =
    (Spec.map (CommRingCat.ofHom ψ) ≫ D.h) ≫ g.left
  rw [hσ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hσh, Category.assoc]

/-- A Galois element acts on the chart by a twist followed by a change of marking. -/
theorem Chart.exists_hecke [IsGalois (RatFunc ℚ) E] (D : Chart Y π E)
    (h1 : R1fpProps Y Φ) (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π)
    (hT : ObjBridge.TorsionStructure) (τ : G₀) :
    ∃ (α : O ≃+* O) (u : Oˣ), ∀ ψ,
      Φ Qbar (D.point (ψ.comp (ringAction τ))) =
        M3.rightMul u (M3.twist α (Φ Qbar (D.point ψ))) := by
  classical
  haveI := h1.1
  haveI := h1.2.1
  obtain ⟨t, s, hs, hst⟩ := TSHecke.genericFibreCount E
  obtain ⟨ψ₀, hψ₀⟩ : s.Nonempty := by
    rw [← Finset.card_pos]
    exact lt_of_lt_of_le Module.finrank_pos hs
  have key : ∀ ψ ∈ s, ∃ (υ : G₀) (α : O ≃+* O) (u : Oˣ),
      ψ = ψ₀.comp (ringAction υ) ∧
      ∀ ξ, Φ Qbar (D.point (ξ.comp (ringAction υ))) =
        M3.rightMul u (M3.twist α (Φ Qbar (D.point ξ))) := by
    intro ψ hψ
    have hπ : π.val (K := Qbar) (D.point ψ₀).left = π.val (K := Qbar) (D.point ψ).left := by
      change π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ₀) ≫ D.h) =
        π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ D.h)
      rw [D.val, D.val, hst _ hψ₀, hst _ hψ]
    obtain ⟨α, u, g₁, g₂, hg₁, hg₂, he⟩ := fibre_transitive_aut hT hh h2 _ _ hπ
    obtain ⟨υ, hυ⟩ := D.exists_aut (g₁.hom ≫ g₂.hom) (fun z => by
      rw [← Category.assoc, pi_invariant_rightMul h2 u g₂ hg₂,
        pi_invariant_twist h2 α g₁ hg₁])
    refine ⟨υ, α, u, D.point_injective (he.trans (hυ ψ₀).symm), fun ξ => ?_⟩
    rw [hυ, ← Category.assoc, hg₂, hg₁]
  choose T α u he hact using key
  have hinj : Function.Injective (fun ψ : s => T ψ.1 ψ.2) := by
    rintro ⟨ψ, hψ⟩ ⟨ψ', hψ'⟩ hh
    apply Subtype.ext
    change T ψ hψ = T ψ' hψ' at hh
    change ψ = ψ'
    exact (he ψ hψ).trans ((congrArg (fun σ => ψ₀.comp (ringAction σ)) hh).trans (he ψ' hψ').symm)
  have hs' : Fintype.card G₀ ≤ Fintype.card s := by
    rw [Fintype.card_coe, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact hs
  obtain ⟨⟨ψ, hψ⟩, hτ⟩ := (Fintype.bijective_iff_injective_and_card _).2
    ⟨hinj, le_antisymm (Fintype.card_le_of_injective _ hinj) hs'⟩ |>.2 τ
  exact ⟨α ψ hψ, u ψ hψ, hτ ▸ hact ψ hψ⟩

end Chart

end SGRDirect.HeckeSqrt

#print axioms SGRDirect.HeckeSqrt.cm24_fixed
#print axioms SGRDirect.HeckeSqrt.Chart.exists_hecke
