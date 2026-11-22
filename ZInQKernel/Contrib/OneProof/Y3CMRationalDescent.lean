import ZInQKernel.Contrib.OneProof.Y3SchemeQuotient
import ZInQKernel.Contrib.OneProof.RayClassShimura
import Mathlib.FieldTheory.Galois.Infinite

/-! Descent of distinguished geometric points on the rational quotient. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open LeafQM LeafQM.AV LeafQM.AV.Pin
open HDec.QMSplit.Moduli
open scoped CategoryTheory.Obj

namespace Y3P1j

set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [Algebra ℚ K]

/-- A point of a rational scheme defined over a Galois extension descends to
a rational point when every automorphism fixes it. -/
theorem exists_rat_point_of_galois_fixed [IsGalois ℚ K]
    {Z : Over (Spec (CommRingCat.of ℚ))} (p : fieldPt K ⟶ Z)
    (hfixed : ∀ σ : K ≃ₐ[ℚ] K, fieldMap σ.toAlgHom ≫ p = p) :
    ∃ q : fieldPt ℚ ⟶ Z, fieldMap (Algebra.ofId ℚ K) ≫ q = p := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hp, _⟩ :=
    Z.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (ptOf p.left)) isOpen_univ
  let e := ev p.left hp
  have hchart : p.left = Spec.map (CommRingCat.ofHom e) ≫ hU.fromSpec :=
    InvariantSchemePoints.affine_point_eq_map U hU p.left hp
  have hfix (σ : K ≃ₐ[ℚ] K) (s : Γ(Z.left, U)) : σ (e s) = e s := by
    have he := congrArg (fun f : fieldPt K ⟶ Z => f.left) (hfixed σ)
    change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p.left = p.left at he
    rw [hchart, ← Category.assoc, ← Spec.map_comp, cancel_mono] at he
    have hring := Spec.map_injective he
    exact congrArg (fun φ : Γ(Z.left, U) ⟶ CommRingCat.of K => φ s) hring
  have heval (s : Γ(Z.left, U)) : ∃ r : ℚ, algebraMap ℚ K r = e s :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (e s)).mpr (fun σ => hfix σ s)
  choose v hv using heval
  have inj := (algebraMap ℚ K).injective
  let d : Γ(Z.left, U) →+* ℚ :=
    { toFun := v
      map_one' := inj (by rw [hv, map_one, map_one])
      map_mul' := fun a b => inj (by simp only [map_mul, hv])
      map_zero' := inj (by rw [hv, map_zero, map_zero])
      map_add' := fun a b => inj (by simp only [map_add, hv]) }
  let q := Spec.map (CommRingCat.ofHom d) ≫ hU.fromSpec
  have hq : q ≫ Z.hom = (fieldPt ℚ).hom := by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of ℚ) (S := CommRingCat.of ℚ)
      (q ≫ Z.hom)
    rw [← hφ]
    change Spec.map φ = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ))
    congr 1
    exact CommRingCat.Hom.ext (RingHom.ext_rat _ _)
  refine ⟨Over.homMk q hq, Over.OverMorphism.ext ?_⟩
  change Spec.map (CommRingCat.ofHom (algebraMap ℚ K)) ≫
    (Spec.map (CommRingCat.ofHom d) ≫ hU.fromSpec) = p.left
  rw [hchart, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext s
  exact hv s

/-- A Galois-stable singleton of geometric points is defined over the rational
base. This applies separately to the three distinguished CM fibres. -/
theorem exists_rat_point_of_galois_stable_singleton [IsGalois ℚ K]
    {Z : Over (Spec (CommRingCat.of ℚ))} (isDistinguished : (fieldPt K ⟶ Z) → Prop)
    (hu : ∃! p, isDistinguished p)
    (hs : ∀ (σ : K ≃ₐ[ℚ] K) (p : fieldPt K ⟶ Z), isDistinguished p →
      isDistinguished (fieldMap σ.toAlgHom ≫ p)) :
    ∃ q : fieldPt ℚ ⟶ Z, isDistinguished (fieldMap (Algebra.ofId ℚ K) ≫ q) := by
  obtain ⟨p, hp, huniq⟩ := hu
  obtain ⟨q, hq⟩ := exists_rat_point_of_galois_fixed p (fun σ => huniq _ (hs σ p hp))
  exact ⟨q, hq.symm ▸ hp⟩

set_option synthInstance.maxHeartbeats 200000 in
/-- Each of the three centralizer conditions is preserved by field base change. -/
theorem hasCM_preserved_by_baseChange {K L : Type} [Field K] [Field L]
    (f : K →+* L) (P : QML3 K) (Q : QML3 L) (hf : IsBaseChangeOf f P Q) :
    (HasCM4 P.q → HasCM4 Q.q) ∧ (HasCM3 P.q → HasCM3 Q.q) ∧ (HasCM24 P.q → HasCM24 Q.q) := by
  let _ : Algebra K L := f.toAlgebra
  obtain ⟨R, hR⟩ := RayClassCFT.exists_bc_ringHom (K := K) (L := L) (P := P) (Q := Q) hf
  refine ⟨fun ⟨φ, hφ, h2⟩ => ⟨R φ, RayClassCFT.com_map R hR hφ, ?_⟩,
    fun ⟨φ, hφ, h2⟩ => ⟨R φ, RayClassCFT.com_map R hR hφ, ?_⟩,
    fun ⟨φ, hφ, h2⟩ => ⟨R φ, RayClassCFT.com_map R hR hφ, ?_⟩⟩
  · rw [← map_mul, h2, map_neg, map_one]
  · have := congrArg R h2
    rwa [map_add, map_sub, map_mul, map_one, map_zero] at this
  · rw [← map_mul, h2, map_neg, map_ofNat]

/-- A nonempty CM condition consisting of one twist class cuts out the fibre
of a rational point of the quotient. -/
theorem exists_rational_distinguished_fibre
    {Y Z : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (π : Y ⟶ Z)
    (hΦ : Y3Fix.R1fpPropsAbP Y Φ)
    (hquot : ∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar),
      Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
        (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)))
    (C : QML3 Qbar → Prop) (hnonempty : ∃ P, C P)
    (htrans : ∀ P Q, C P → C Q → ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q))
    (hstable : ∀ P Q (α : O ≃+* O), QMIso (P.q.twist α) Q.q → C P → C Q)
    (hbc : ∀ (σ : Qbar ≃ₐ[ℚ] Qbar) P Q, IsBaseChangeOf σ.toRingHom P Q → C P → C Q) :
    ∃ x : fieldPt ℚ ⟶ Z, ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
      Φ Qbar y = M3.mk P → (C P ↔ y ≫ π = fieldMap (Algebra.ofId ℚ Qbar) ≫ x) := by
  obtain ⟨P₀, hP₀⟩ := hnonempty
  let y₀ := (Φ Qbar).symm (M3.mk P₀)
  have hy₀ : Φ Qbar y₀ = M3.mk P₀ := (Φ Qbar).apply_symm_apply _
  have hf (σ : Qbar ≃ₐ[ℚ] Qbar) : fieldMap σ.toAlgHom ≫ (y₀ ≫ π) = y₀ ≫ π := by
    obtain ⟨Q, hQ, hB⟩ := hΦ.2.2.1 Qbar Qbar σ.toAlgHom y₀ P₀ hy₀
    exact (Category.assoc _ _ _).symm.trans
      ((hquot (fieldMap σ.toAlgHom ≫ y₀) y₀ Q P₀ hQ hy₀).mpr
        (htrans Q P₀ (hbc σ P₀ Q hB hP₀) hP₀))
  obtain ⟨x, hx⟩ := exists_rat_point_of_galois_fixed (y₀ ≫ π) hf
  refine ⟨x, fun y P hP => ?_⟩
  rw [hx]
  constructor
  · intro h
    exact (hquot y y₀ P P₀ hP hy₀).mpr (htrans P P₀ h hP₀)
  · intro h
    obtain ⟨α, ⟨e⟩⟩ := (hquot y₀ y P₀ P hy₀ hP).mp h.symm
    exact hstable P₀ P α e hP₀

end Y3P1j

#print axioms Y3P1j.exists_rat_point_of_galois_fixed
#print axioms Y3P1j.exists_rat_point_of_galois_stable_singleton
#print axioms Y3P1j.exists_rational_distinguished_fibre
