import ZInQKernel.Contrib.CloudB3SC6FixedFields.PointFibreInvariance

/-!
# Point fibres realize every sign change in the function field

This reverses only the chart-action part of the existing Elkies argument. The
moduli witness and point-fibre clause are hypotheses. No finite-extension or
fixed-field criterion is duplicated here.
-/

namespace CloudB3SC6FixedFields

open CategoryTheory AlgebraicGeometry Limits
open _root_.HDec.LeafQM _root_.HDec.LeafQM.AV
open HDec.QMSplit.Moduli HDec.QMSplit.Moduli.ElkiesCoord X6Glue

section Signs

variable {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
variable {X : Over (Spec (CommRingCat.of ℚ))} [IsIntegral X.left]
variable {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X}
variable {t : ToP1 X.left}

/-- With the prescribed charts and point-fibre clause, each of the four coordinate-sign pairs
is induced by an element of W on the function field. A fibre with both coordinates nonzero
identifies the globally constant signs of that element. -/
theorem exists_W_with_signs_of_point_fibres (h6 : X6Props Y Φ X Ψ fY)
    (φU : ElkiesRing ≃+* Γ(X.left, t.U)) (φV : ElkiesRing ≃+* Γ(X.left, t.V))
    (hU : IsAffineOpen t.U) (hV : IsAffineOpen t.V)
    (hT : φU eT = t.f) (hTg : φV eT = t.g)
    (hg1 : X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eS) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) = 1)
    (hg2 : X.left.presheaf.map (homOfLE (inf_le_left : t.U ⊓ t.V ≤ t.U)).op (φU eR) *
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eS) =
      X.left.presheaf.map (homOfLE (inf_le_right : t.U ⊓ t.V ≤ t.V)).op (φV eR))
    (hηU : genericPoint X.left ∈ t.U) (hηV : genericPoint X.left ∈ t.V)
    (hfib : ∀ x x' : fieldPt Qbar ⟶ X,
      t.val (K := Qbar) x.left = t.val (K := Qbar) x'.left ↔
        ∃ g ∈ ElkiesX6Star.atkinLehnerW X Ψ, x ≫ g.hom = x')
    (c d : ℤˣ) :
    ∃ g ∈ ElkiesX6Star.atkinLehnerW X Ψ,
      ffPullback (Z := X.left) ((Over.forget _).mapIso g) (jU φU hηU eS) =
        ((c : ℤ) : X.left.functionField) * jU φU hηU eS ∧
      ffPullback (Z := X.left) ((Over.forget _).mapIso g) (jU φU hηU eR) =
        ((d : ℤ) : X.left.functionField) * jU φU hηU eR := by
  obtain ⟨b, hb⟩ := exists_sq_eq (-6)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h] at hb
    norm_num at hb
  let p0 : HDec.X6Kummer.ConicPt := Sum.inl ⟨(1, b), by
    simp only
    linear_combination hb⟩
  let F : (fieldPt Qbar ⟶ X) → HDec.X6Kummer.ConicPt := fun x => conicMapL φU φV hTg x.left
  have hsurj : ∀ p, ∃ x, F x = p := by
    intro p
    obtain ⟨y, hy⟩ := conicMapL_surjective φU φV hTg hU hV p
    exact ⟨Over.homMk y (specQ_hom_ext _ _), hy⟩
  obtain ⟨x0, hx0⟩ := hsurj p0
  obtain ⟨x1, hx1⟩ := hsurj (signAct c d p0)
  have hval : t.val (K := Qbar) x0.left = t.val (K := Qbar) x1.left :=
    val_eq_of_signAct hT hTg x0.left x1.left c d (by change F x1 = signAct c d (F x0); rw [hx1, hx0])
  obtain ⟨g, hg, hxg⟩ := (hfib x0 x1).mp hval
  let σ : X.left.functionField →+* X.left.functionField :=
    ffPullback (Z := X.left) ((Over.forget _).mapIso g)
  set τ := jU φU hηU eT
  set S := jU φU hηU eS
  set R := jU φU hηU eR
  have hτ : σ τ = τ := by
    have hh := coordinate_mem_fixedByW_of_point_fibres h6 hηU hfib g hg
    simpa [σ, τ, jU, hT] using hh
  have r1 : S ^ 2 = -τ := by
    have hh := congrArg (jU φU hηU) rel1
    simp only [map_add, map_pow, map_zero] at hh
    linear_combination hh
  have r2 : R ^ 2 = 3 * (τ - 1) := by
    have hh := congrArg (jU φU hηU) rel2
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_one, map_zero] at hh
    linear_combination hh
  obtain ⟨c', hc'⟩ := pm_unit _ _ (sq_pm σ S (-τ) (by rw [map_neg, hτ]) r1)
  obtain ⟨d', hd'⟩ := pm_unit _ _
    (sq_pm σ R (3 * (τ - 1)) (by rw [map_mul, map_sub, map_ofNat, map_one, hτ]) r2)
  have ha := conicMapL_comp_of_signs hηU hηV hT hTg hg1 hg2
    ((Over.forget _).mapIso g) c' d' hτ hc' hd' x0.left
  change F (x0 ≫ g.hom) = signAct c' d' (F x0) at ha
  rw [hxg, hx1, hx0] at ha
  have he : (((c : ℤ) : Qbar), ((d : ℤ) : Qbar) * b) =
      (((c' : ℤ) : Qbar), ((d' : ℤ) : Qbar) * b) := by
    have hh := congrArg (fun p : HDec.X6Kummer.ConicPt =>
      match p with | Sum.inl q => q.1 | Sum.inr _ => (0, 0)) ha
    simpa only [p0, signAct, mul_one] using hh
  have hc : c = c' := Units.ext (Int.cast_injective (congrArg Prod.fst he))
  have hd : d = d' := Units.ext (Int.cast_injective
    ((mul_left_inj' hb0).mp (congrArg Prod.snd he)))
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [σ, S, hc] using hc'
  · simpa only [σ, R, hd] using hd'

end Signs

end CloudB3SC6FixedFields
