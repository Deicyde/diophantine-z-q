import ZInQKernel.Contrib.OneProof.H.TailU

/-! # Complex Atkin–Lehner fixed points -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open LeafQM LeafQM.AV PkgI3
open HDec.LeafQM.AV.Pin.Exact HDec.LeafQM.AV.Pin.NormO

set_option linter.style.haveILetI false

namespace HDec.QMSplit.Aut

private theorem twist_data_over_field {K : Type} [Field K] {A : AbVar K} (q : QMStr A) (α : LeafQM.O ≃+* LeafQM.O)
    (τ : LeafQM.O) (c : ℤ) (hατ : α τ = τ) (hcomm : ∀ a, α a * τ = τ * a) (hαα : ∀ a, α (α a) = a)
    (hττ : τ * τ = (c : LeafQM.O)) (G : QMIso (q.twist α) q) :
    ∃ V W Winv : com q, V * V = (c : com q) * W ∧ W * Winv = 1 := by
  set φ : AbVar.End A := G.φ
  set ψ : AbVar.End A := G.ψ
  have eq1 : ∀ a, φ * q.iota (α a) = q.iota a * φ := fun a => AbVar.Hom.ext' (G.equivariant a)
  have eq2 : ∀ a, ψ * q.iota a = q.iota (α a) * ψ := fun a => AbVar.Hom.ext' (G.symm.equivariant a)
  have hφψ : φ * ψ = 1 := AbVar.Hom.ext' G.right
  have memc : ∀ z : AbVar.End A, (∀ a, q.iota a * z = z * q.iota a) → z ∈ com q := by
    intro z hz
    rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    exact hz a
  have hW : φ * φ ∈ com q := memc _ fun a => by
    rw [← mul_assoc, ← eq1, mul_assoc, ← eq1, hαα, mul_assoc]
  have hWi : ψ * ψ ∈ com q := memc _ fun a => by
    have h1 := eq2 (α a)
    rw [hαα] at h1
    rw [mul_assoc, eq2, ← mul_assoc, ← h1, mul_assoc]
  have hV : φ * q.iota τ ∈ com q := memc _ fun a => by
    rw [← mul_assoc, ← eq1, mul_assoc, ← map_mul, hcomm, map_mul, mul_assoc]
  refine ⟨⟨_, hV⟩, ⟨_, hW⟩, ⟨_, hWi⟩, ?_, ?_⟩
  · apply Subtype.ext
    have h1 : q.iota τ * φ = φ * q.iota τ := by rw [← eq1, hατ]
    change φ * q.iota τ * (φ * q.iota τ) = ((c : com q) : AbVar.End A) * (φ * φ)
    rw [show ((c : com q) : AbVar.End A) = (c : AbVar.End A) by push_cast; rfl]
    calc φ * q.iota τ * (φ * q.iota τ) = φ * (q.iota τ * φ) * q.iota τ := by noncomm_ring
      _ = φ * φ * (q.iota (τ * τ)) := by rw [h1, map_mul]; noncomm_ring
      _ = (c : AbVar.End A) * (φ * φ) := by rw [hττ, map_intCast, (Int.cast_commute c _).eq]
  · apply Subtype.ext
    change φ * φ * (ψ * ψ) = 1
    calc φ * φ * (ψ * ψ) = φ * (φ * ψ) * ψ := by noncomm_ring
      _ = 1 := by rw [hφψ, mul_one, hφψ]


/-- Atkin–Lehner fixed points of complex QM surfaces have the corresponding CM type. -/
theorem alFixedPoints_complex_of (h : QMCentralizerCMC) (A : AbVar ℂ) (hA : A.dim = 2)
    (q : QMStr A) :
    (Nonempty (QMIso (q.twist (rep 1)) q) → HasCM4 q) ∧
    (Nonempty (QMIso (q.twist (rep 2)) q) → HasCM3 q) ∧
    (Nonempty (QMIso (q.twist (rep 3)) q) → HasCM24 q) := by
  have data : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) →
      Nonempty (QMIso (q.twist (rep kk)) q) → ∃ V W Winv : com q, V * V = (c : com q) * W ∧ W * Winv = 1 := by
    intro kk c hk0 hsq ⟨G⟩
    obtain ⟨f1, f2, f3, f4⟩ := conjO_facts (tt kk) (tt_isNorm kk) (tt_mem kk hk0) c hsq
    exact twist_data_over_field q (rep kk) _ c f1 f2 f3 f4 G
  obtain ⟨h4i, h3i, h24i⟩ := cm_iff q
  rcases h A hA q with he | ⟨k, _, _, hkc, hk2, Φ, he⟩
  · obtain ⟨e⟩ := he
    have zc : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) → ¬ IsSquare c → ¬ IsSquare (-c) →
        ¬ Nonempty (QMIso (q.twist (rep kk)) q) := by
      intro kk c hk0 hsq n1 n2 hG
      obtain ⟨V, W, Wi, hV, hW⟩ := data kk c hk0 hsq hG
      apply int_case c n1 n2 (e V) (e W) (e Wi)
      · rw [← map_mul, hV, map_mul, map_intCast, Int.cast_id]
      · rw [← map_mul, hW, map_one]
    refine ⟨fun hG => (zc 1 2 (by decide) tt1_sq (by decide +kernel) (by decide +kernel) hG).elim,
      fun hG => (zc 2 (-3) (by decide) tt2_sq (by decide +kernel) (by decide +kernel) hG).elim,
      fun hG => (zc 3 6 (by decide) tt3_sq (by decide +kernel) (by decide +kernel) hG).elim⟩
  · obtain ⟨e⟩ := he
    haveI := hkc
    set R := LeafQM.O.comap Φ.toRingHom
    obtain ⟨s4, s3, s24⟩ := sub_ex_iff R
    have e4 : HasCM4 q ↔ ∃ r ∈ R, r * r = -1 := by rw [h4i, ex4_iff e, s4]
    have e3 : HasCM3 q ↔ ∃ r ∈ R, r * r - r + 1 = 0 := by rw [h3i, ex3_iff e, s3]
    have e24 : HasCM24 q ↔ ∃ r ∈ R, r * r = -6 := by rw [h24i, ex24_iff e, s24]
    have tr : ∀ (kk : Fin 4) (c : ℤ), kk ≠ 0 → (tt kk : B) * tt kk = (c : B) →
        Nonempty (QMIso (q.twist (rep kk)) q) →
        ∃ v w wi : k, v ∈ R ∧ w ∈ R ∧ wi ∈ R ∧ w * wi = 1 ∧ v * v = c * w := by
      intro kk c hk0 hsq hG
      obtain ⟨V, W, Wi, hV, hW⟩ := data kk c hk0 hsq hG
      refine ⟨(e V : R), (e W : R), (e Wi : R), (e V).2, (e W).2, (e Wi).2, ?_, ?_⟩
      · have := congrArg Subtype.val (show e W * e Wi = 1 by rw [← map_mul, hW, map_one])
        exact this
      · have := congrArg Subtype.val (show e V * e V = (c : R) * e W by
          rw [← map_mul, hV, map_mul, map_intCast])
        rw [show ((((c : R) * e W : R)) : k) = (c : k) * (e W : R) by push_cast; rfl] at this
        exact this
    refine ⟨fun hG => ?_, fun hG => ?_, fun hG => ?_⟩
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 1 2 (by decide) tt1_sq hG
      exact e4.2 (al2 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 2 (-3) (by decide) tt2_sq hG
      exact e3.2 (al3 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))
    · obtain ⟨v, w, wi, hv, hw, hwi, hww, hvv⟩ := tr 3 6 (by decide) tt3_sq hG
      exact e24.2 (al6 hk2 Φ hv hw hwi hww (by rw [hvv]; push_cast; ring))


end HDec.QMSplit.Aut

#print axioms HDec.QMSplit.Aut.alFixedPoints_complex_of
