import ZInQKernel.Contrib.OneProof.HeckeSqrtAction

/-! ON THE SPOT (provenance (c)): the four outer twists act freely on a
non-CM fibre. The two-bit twist of a Galois element is therefore uniquely
determined; its second bit is zero on inertia over 0 and one on a CM(−24)
stabilizer. -/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.LeafQM _root_.LeafQM.AV HDec.LeafQM.AV.Pin.Exact
open GlueDescent.B2Q
open HDec HDec.G0ModField HDec.TSHecke HDec.HeckeRest

namespace SGRDirect.HeckeSqrt

variable {E : Type} [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
  [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
  {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {Φ : PtEquiv Y}

local notation "B₀" => integralClosure ℚ[X] E
local notation "G₀" => Gal(E / RatFunc ℚ)

/-- On underlying pairs, the field automorphism acts by the indicated representative. -/
def Trace (D : Chart Y π E) (Φ : PtEquiv Y) (τ : G₀) (k : Fin 4) : Prop :=
  ∀ (ψ : B₀ →+* Qbar) (P Q : QML3 Qbar), Φ Qbar (D.point ψ) = M3.mk P →
    Φ Qbar (D.point (ψ.comp (ringAction τ))) = M3.mk Q →
    Nonempty (QMIso (P.q.twist (rep k)) Q.q)

theorem trace_of_action {D : Chart Y π E} {τ : G₀} (α : O ≃+* O) (u : Oˣ)
    (h : ∀ ψ, Φ Qbar (D.point (ψ.comp (ringAction τ))) =
      M3.rightMul u (M3.twist α (Φ Qbar (D.point ψ)))) :
    ∃ k, Trace D Φ τ k := by
  obtain ⟨k, v, hv⟩ := rep_cover α
  refine ⟨k, fun ψ P Q hP hQ => ?_⟩
  have e := h ψ
  rw [hP, hQ] at e
  change M3.mk Q = M3.mk ((P.twist α).rightMul u) at e
  obtain ⟨i⟩ := Quotient.exact e.symm
  exact ⟨(innerIso P.q (rep k) α v hv).symm.trans (qmIso_of_iso i)⟩

theorem trace_rep {D : Chart Y π E} {τ : G₀} (k : Fin 4) (u : Oˣ)
    (h : ∀ ψ, Φ Qbar (D.point (ψ.comp (ringAction τ))) =
      M3.rightMul u (M3.twist (rep k) (Φ Qbar (D.point ψ)))) :
    Trace D Φ τ k := by
  intro ψ P Q hP hQ
  have e := h ψ
  rw [hP, hQ] at e
  change M3.mk Q = M3.mk ((P.twist (rep k)).rightMul u) at e
  obtain ⟨i⟩ := Quotient.exact e.symm
  exact ⟨qmIso_of_iso i⟩

theorem trace_mul {D : Chart Y π E} {τ υ : G₀} {k l : Fin 4}
    (hτ : Trace D Φ τ k) (hυ : Trace D Φ υ l) : Trace D Φ (τ * υ) (xr k l) := by
  intro ψ P R hP hR
  rw [ringAction_mul, ← RingHom.comp_assoc] at hR
  let Q := (Φ Qbar (D.point (ψ.comp (ringAction τ)))).out
  have hQ : Φ Qbar (D.point (ψ.comp (ringAction τ))) = M3.mk Q := (Quotient.out_eq _).symm
  obtain ⟨i⟩ := hτ ψ P Q hP hQ
  obtain ⟨j⟩ := hυ _ Q R hQ hR
  refine ⟨(qmCongr i (rep l) ?_ (fun _ => rfl)).trans j⟩
  intro a
  change P.q.iota (rep (xr k l) a) = P.q.iota (rep k (rep l a))
  rw [rep_rep]

theorem trace_unique {D : Chart Y π E} (h2 : R2fpProps Y Φ π) (hW : ALFixedPoints)
    {τ : G₀} {k l : Fin 4} (hk : Trace D Φ τ k) (hl : Trace D Φ τ l) : k = l := by
  obtain ⟨ψ, hψ⟩ := GFC.exists_extend (S := B₀)
    (Polynomial.eval₂RingHom (algebraMap ℚ Qbar) 1)
    (by
      have h : Function.Injective (algebraMap ℚ[X] B₀) := fun a b hab =>
        poly_injective (congrArg (fun z : B₀ => (z : E)) hab)
      intro a ha
      have hz : a = 0 := h ((RingHom.mem_ker.mp ha).trans (map_zero _).symm)
      simp [hz])
  have hx : ψ (algebraMap ℚ[X] B₀ X) = 1 := by
    simpa using RingHom.congr_fun hψ X
  let y := D.point ψ
  let P := (Φ Qbar y).out
  let Q := (Φ Qbar (D.point (ψ.comp (ringAction τ)))).out
  have hp : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
  have hq : Φ Qbar (D.point (ψ.comp (ringAction τ))) = M3.mk Q := (Quotient.out_eq _).symm
  have hy : π.val (K := Qbar) y.left = OnePoint.some 1 := (D.val ψ).trans (congrArg OnePoint.some hx)
  obtain ⟨-, h4, h3, h24⟩ := h2 y y P P hp hp
  obtain ⟨w1, w2, w3⟩ := hW P.A P.surface P.q
  obtain ⟨i⟩ := hk ψ P Q hp hq
  obtain ⟨j⟩ := hl ψ P Q hp hq
  have hf := (rk_iff P k l).1 ⟨i.trans j.symm⟩
  have hz : xr k l = 0 := by
    revert hf
    generalize xr k l = m
    intro hf
    fin_cases m
    · rfl
    · exact (one_ne_zero (OnePoint.coe_injective (hy.symm.trans (h4 (w1 hf))))).elim
    · exact (OnePoint.coe_ne_infty _ (hy.symm.trans (h3 (w2 hf)))).elim
    · have h := OnePoint.coe_injective (hy.symm.trans (h24 (w3 hf)))
      norm_num at h
  have eq := xr_xr_right k l
  rw [hz] at eq
  have h0 (m : Fin 4) : xr 0 m = m := by revert m; decide
  rw [h0] at eq
  exact eq.symm

/-- Sign of the second bit of an outer twist. -/
def sign (k : Fin 4) : ℚ := ![1, 1, -1, -1] k

theorem sign_xr (k l : Fin 4) : sign (xr k l) = sign k * sign l := by
  fin_cases k <;> fin_cases l <;> norm_num [sign, xr, Matrix.cons_val_zero, Matrix.cons_val_succ]

theorem sign_sq (k : Fin 4) : sign k ^ 2 = 1 := by
  fin_cases k <;> norm_num [sign, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- The unique outer twist associated to each field automorphism. -/
def index [IsGalois (RatFunc ℚ) E] (D : Chart Y π E) (h1 : R1fpProps Y Φ)
    (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π) (hT : ObjBridge.TorsionStructure) (τ : G₀) : Fin 4 :=
  (let ⟨α, u, h⟩ := D.exists_hecke h1 hh h2 hT τ
   show ∃ k, Trace D Φ τ k from trace_of_action α u h).choose

theorem trace_index [IsGalois (RatFunc ℚ) E] (D : Chart Y π E) (h1 : R1fpProps Y Φ)
    (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π) (hT : ObjBridge.TorsionStructure) (τ : G₀) :
    Trace D Φ τ (index D h1 hh h2 hT τ) :=
  Exists.choose_spec (let ⟨α, u, h⟩ := D.exists_hecke h1 hh h2 hT τ
    show ∃ k, Trace D Φ τ k from trace_of_action α u h)

theorem trace_sign_at_zero {D : Chart Y π E} (h2 : R2fpProps Y Φ π) (hW : ALFixedPoints)
    {τ : G₀} {k : Fin 4} (hτ : Trace D Φ τ k) (ψ : B₀ →+* Qbar)
    (hx : ψ (algebraMap ℚ[X] B₀ X) = 0) (hi : τ ∈ InertiaQ E (RingHom.ker ψ)) :
    sign k = 1 := by
  let y := D.point ψ
  let P := (Φ Qbar y).out
  have hp : Φ Qbar y = M3.mk P := (Quotient.out_eq _).symm
  have hy : π.val (K := Qbar) y.left = OnePoint.some 0 := (D.val ψ).trans (congrArg OnePoint.some hx)
  have hfix := (inertia_iff_stabilizes _ _).1 hi
  have hI := hτ ψ P P hp (by rw [hfix]; exact hp)
  obtain ⟨-, -, h3, h24⟩ := h2 y y P P hp hp
  obtain ⟨-, w2, w3⟩ := hW P.A P.surface P.q
  fin_cases k
  · rfl
  · rfl
  · exact (OnePoint.coe_ne_infty _ (hy.symm.trans (h3 (w2 hI)))).elim
  · have h := OnePoint.coe_injective (hy.symm.trans (h24 (w3 hI)))
    norm_num at h

theorem exists_inertia_trace_three {D : Chart Y π E} (h1 : R1fpProps Y Φ)
    (hh : R1heckeProps Y Φ) (h2 : R2fpProps Y Φ π) (hT : ObjBridge.TorsionStructure)
    (P : QML3 Qbar) (hP : HasCM24 P.q) (G : QMIso (P.q.twist (rep 3)) P.q) :
    ∃ (ψ : B₀ →+* Qbar) (τ : G₀), τ ∈ InertiaQ E (RingHom.ker ψ) ∧ Trace D Φ τ 3 := by
  haveI := h1.1
  haveI := h1.2.1
  let y := (Φ Qbar).symm (M3.mk P)
  have hy : Φ Qbar y = M3.mk P := Equiv.apply_symm_apply _ _
  have hπ := (h2 y y P P hy hy).2.2.2 hP
  obtain ⟨ψ, hψ⟩ := D.exists_point y (hπ ▸ OnePoint.coe_ne_infty _)
  obtain ⟨u, hu⟩ := fixed_level hT P _ G
  obtain ⟨g₁, hg₁⟩ := hh.1 (rep 3)
  obtain ⟨g₂, hg₂⟩ := hh.2 u
  obtain ⟨τ, hτ⟩ := D.exists_aut (g₁.hom ≫ g₂.hom) (fun z => by
    rw [← Category.assoc, pi_invariant_rightMul h2 u g₂ hg₂, pi_invariant_twist h2 _ g₁ hg₁])
  have hact ξ : Φ Qbar (D.point (ξ.comp (ringAction τ))) =
      M3.rightMul u (M3.twist (rep 3) (Φ Qbar (D.point ξ))) := by
    rw [hτ, ← Category.assoc, hg₂, hg₁]
  refine ⟨ψ, τ, (inertia_iff_stabilizes _ _).2 ?_, trace_rep 3 u hact⟩
  apply D.point_injective
  apply (Φ Qbar).injective
  rw [hact, hψ, hy, hu]

end SGRDirect.HeckeSqrt

#print axioms SGRDirect.HeckeSqrt.trace_unique
#print axioms SGRDirect.HeckeSqrt.trace_sign_at_zero
#print axioms SGRDirect.HeckeSqrt.exists_inertia_trace_three
