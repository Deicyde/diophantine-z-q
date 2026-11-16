import ZInQKernel.Contrib.OneProof.ElkiesX6Star
import ZInQKernel.Contrib.OneProof.QMLattice

/-! bg-explicit draft: `BabaGranathRationalAb` from Elkies' printed leaf and `ALFixedPoints`. -/

noncomputable section

namespace BGExplicit

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

open HDec.LeafQM.AV.Pin.Exact (rep)
open HDec.HeckeRest (xr)

/-- Two equal Atkin–Lehner twists give a fixed point of a nontrivial one. -/
theorem fixed_of_twist_iso (P : QMPair Qbar) (a b : Fin 4)
    (e : QMIso (P.q.twist (rep a)) (P.q.twist (rep b))) :
    Nonempty (QMIso (P.q.twist (rep (xr a b))) P.q) := by
  refine ⟨HDec.HeckeRest.qmCongr e (rep b) (fun x => ?_) (fun x => ?_)⟩
  · show P.q.iota (rep (xr a b) x) = P.q.iota (rep a (rep b x))
    rw [HDec.HeckeRest.rep_rep]
  · show P.q.iota x = P.q.iota (rep b (rep b x))
    rw [HDec.HeckeRest.rep_rep, HDec.HeckeRest.xr_self, HDec.HeckeRest.rep_zero]

theorem xr_cases (a b : Fin 4) (h : a ≠ b) : xr a b = 1 ∨ xr a b = 2 ∨ xr a b = 3 := by
  revert a b; decide

/-- A pair isomorphic to two distinct Atkin–Lehner twists of itself... (fixed point) has CM. -/
theorem cm_of_twist_iso (hW : HDec.HeckeRest.ALFixedPoints) (P : QMPair Qbar) (a b : Fin 4)
    (hab : a ≠ b) (e : QMIso (P.q.twist (rep a)) (P.q.twist (rep b))) :
    HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q := by
  obtain ⟨f⟩ := fixed_of_twist_iso P a b e
  obtain ⟨w1, w2, w3⟩ := hW P.A P.surface P.q
  rcases xr_cases a b hab with h | h | h <;> rw [h] at f
  · exact Or.inl (w1 ⟨f⟩)
  · exact Or.inr (Or.inl (w2 ⟨f⟩))
  · exact Or.inr (Or.inr (w3 ⟨f⟩))

open Classical in
/-- Separation by a square root. -/
theorem sep_of_sq {α : Type*} (F : α → Prop) (c : α → Qbar) (r : Qbar)
    (hc : ∀ x, F x → c x ^ 2 = r ^ 2) (hinj : ∀ x y, F x → F y → c x = c y → x = y) :
    ∀ x y, F x → F y → decide (c x = r) = decide (c y = r) → x = y := by
  intro x y hx hy hd
  apply hinj x y hx hy
  have ox := sq_eq_sq_iff_eq_or_eq_neg.1 (hc x hx)
  have oy := sq_eq_sq_iff_eq_or_eq_neg.1 (hc y hy)
  by_cases h1 : c x = r
  · have : c y = r := by simpa [h1] using hd.symm
    rw [h1, this]
  · have h2 : c y ≠ r := by simpa [h1] using hd.symm
    rw [ox.resolve_left h1, oy.resolve_left h2]


/-- Coordinates of a `ℚ̄`-point of the conic. -/
def cX (c : HDec.X6Kummer.ConicPt) : Qbar := Sum.elim (fun p => p.1.1) (fun _ => 0) c
def cY (c : HDec.X6Kummer.ConicPt) : Qbar := Sum.elim (fun p => p.1.2) (fun _ => 0) c
def cB (c : HDec.X6Kummer.ConicPt) : Qbar := Sum.elim (fun _ => 0) (fun b => b.1) c

section Main

variable {X : Over (Spec (CommRingCat.of ℚ))} {t : ToP1 X.left}
  (e : (fieldPt Qbar ⟶ X) ≃ HDec.X6Kummer.ConicPt)
  (hp : ∀ (x : fieldPt Qbar ⟶ X) p, e x = Sum.inl p →
      t.val (K := Qbar) x.left = OnePoint.some (-(p.1.1 ^ 2)))
  (hi : ∀ (x : fieldPt Qbar ⟶ X) b, e x = Sum.inr b → t.val (K := Qbar) x.left = OnePoint.infty)
include hp hi

theorem fibre_one (x : fieldPt Qbar ⟶ X) (hx : t.val (K := Qbar) x.left = OnePoint.some 1) :
    ∃ p, e x = Sum.inl p ∧ p.1.1 ^ 2 = -1 ∧ p.1.2 = 0 := by
  rcases h : e x with p | b
  · have h1 := hp x p h
    rw [hx] at h1
    have h2 : p.1.1 ^ 2 = -1 := by
      have := OnePoint.coe_injective h1
      linear_combination this
    refine ⟨p, rfl, h2, ?_⟩
    have h3 := p.2
    rw [h2] at h3
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linear_combination h3)
  · have := hi x b h
    rw [hx] at this
    exact absurd this (OnePoint.coe_ne_infty _)

theorem fibre_zero (x : fieldPt Qbar ⟶ X) (hx : t.val (K := Qbar) x.left = OnePoint.some 0) :
    ∃ p, e x = Sum.inl p ∧ p.1.1 = 0 ∧ p.1.2 ^ 2 = -3 := by
  rcases h : e x with p | b
  · have h1 := hp x p h
    rw [hx] at h1
    have h2 : p.1.1 = 0 := by
      have := OnePoint.coe_injective h1
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by linear_combination this)
    refine ⟨p, rfl, h2, ?_⟩
    have h3 := p.2
    rw [h2] at h3
    linear_combination h3
  · have := hi x b h
    rw [hx] at this
    exact absurd this (OnePoint.coe_ne_infty _)

omit hi in
theorem fibre_infty (x : fieldPt Qbar ⟶ X) (hx : t.val (K := Qbar) x.left = OnePoint.infty) :
    ∃ b, e x = Sum.inr b := by
  rcases h : e x with p | b
  · have h1 := hp x p h
    rw [hx] at h1
    exact absurd h1.symm (OnePoint.coe_ne_infty _)
  · exact ⟨b, rfl⟩

end Main

open Classical in
theorem babaGranathRationalAb_of_AL (h : HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted)
    (hW : HDec.HeckeRest.ALFixedPoints) : HDec.QMSplit.Moduli.BabaGranathRationalAb := by
  obtain ⟨Y, Φ, X, Ψ, fY, t, h1, h6, hcl, hc⟩ :=
    HDec.QMSplit.Moduli.ElkiesX6Star.elkiesEquationsX6Ab_of_printed h
  obtain ⟨e, -, hp, hi⟩ := X6Glue.conicModelT_of_charts hc
  have hgex : ∀ k : Fin 4, ∃ g : X ≅ X, ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ (x ≫ g.hom) = Quotient.mk _ (P.twist (rep k)) :=
    fun k => h6.2.2.2.2.1 (rep k)
  choose g hg using hgex
  -- a fibre of `t` separated by a Boolean function consists of CM points
  have key : ∀ (x : fieldPt Qbar ⟶ X) (sgn : (fieldPt Qbar ⟶ X) → Bool),
      (∀ y z : fieldPt Qbar ⟶ X, t.val (K := Qbar) y.left = t.val (K := Qbar) x.left →
        t.val (K := Qbar) z.left = t.val (K := Qbar) x.left → sgn y = sgn z → y = z) →
      ∀ P : QMPair Qbar, Ψ x = Quotient.mk _ P → HasCM4 P.q ∨ HasCM3 P.q ∨ HasCM24 P.q := by
    intro x sgn hsep P hP
    have hfib : ∀ k, t.val (K := Qbar) (x ≫ (g k).hom).left = t.val (K := Qbar) x.left := fun k =>
      (((hcl x (x ≫ (g k).hom) P (P.twist (rep k)) hP (hg k x P hP)).1).2
        ⟨rep k, ⟨QMIso.refl _⟩⟩).symm
    obtain ⟨a, b, hab, hs⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin 4 => sgn (x ≫ (g k).hom)) (by simp)
    have hxe := hsep _ _ (hfib a) (hfib b) hs
    have hq : (Quotient.mk _ (P.twist (rep a)) : Quotient (pairSetoid Qbar)) =
        Quotient.mk _ (P.twist (rep b)) := by
      rw [← hg a x P hP, ← hg b x P hP, hxe]
    obtain ⟨f⟩ := Quotient.exact hq
    exact cm_of_twist_iso hW P a b hab f
  obtain ⟨I, hI⟩ := IsAlgClosed.isSquare (-1 : Qbar)
  obtain ⟨R, hR⟩ := IsAlgClosed.isSquare (-3 : Qbar)
  have hI2 : I ^ 2 = -1 := by rw [hI]; ring
  have hR2 : R ^ 2 = -3 := by rw [hR]; ring
  -- the three special points
  let x₁ : fieldPt Qbar ⟶ X := e.symm (Sum.inl ⟨(I, 0), by simp only; rw [hI2]; ring⟩)
  let x₀ : fieldPt Qbar ⟶ X := e.symm (Sum.inl ⟨(0, R), by simp only; rw [hR2]; ring⟩)
  let x₂ : fieldPt Qbar ⟶ X := e.symm (Sum.inr ⟨R, hR2⟩)
  have t₁ : t.val (K := Qbar) x₁.left = OnePoint.some 1 := by
    rw [hp x₁ _ (e.apply_symm_apply _)]; simp only; rw [hI2]; norm_num
  have t₀ : t.val (K := Qbar) x₀.left = OnePoint.some 0 := by
    rw [hp x₀ _ (e.apply_symm_apply _)]; simp
  have t₂ : t.val (K := Qbar) x₂.left = OnePoint.infty := hi x₂ _ (e.apply_symm_apply _)
  -- their QM pairs
  obtain ⟨P₁, hP₁⟩ : ∃ P, Ψ x₁ = Quotient.mk _ P := ⟨_, (Quotient.out_eq _).symm⟩
  obtain ⟨P₀, hP₀⟩ : ∃ P, Ψ x₀ = Quotient.mk _ P := ⟨_, (Quotient.out_eq _).symm⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P, Ψ x₂ = Quotient.mk _ P := ⟨_, (Quotient.out_eq _).symm⟩
  -- the fibres over `1, 0, ∞` are separated
  have sep₁ : ∀ y z : fieldPt Qbar ⟶ X, t.val (K := Qbar) y.left = t.val (K := Qbar) x₁.left →
      t.val (K := Qbar) z.left = t.val (K := Qbar) x₁.left →
      decide (cX (e y) = I) = decide (cX (e z) = I) → y = z := by
    rw [t₁]
    refine sep_of_sq (fun y => t.val (K := Qbar) y.left = OnePoint.some 1) (fun y => cX (e y)) I
      (fun y hy => ?_) (fun y z hy hz hyz => ?_)
    · obtain ⟨p, hpe, hp1, -⟩ := fibre_one e hp hi y hy
      simp only [hpe, cX, Sum.elim_inl]; rw [hp1, hI2]
    · obtain ⟨p, hpe, -, hp2⟩ := fibre_one e hp hi y hy
      obtain ⟨p', hpe', -, hp2'⟩ := fibre_one e hp hi z hz
      simp only [hpe, hpe', cX, Sum.elim_inl] at hyz
      apply e.injective
      rw [hpe, hpe']
      exact congrArg Sum.inl (Subtype.ext (Prod.ext hyz (hp2.trans hp2'.symm)))
  have sep₀ : ∀ y z : fieldPt Qbar ⟶ X, t.val (K := Qbar) y.left = t.val (K := Qbar) x₀.left →
      t.val (K := Qbar) z.left = t.val (K := Qbar) x₀.left →
      decide (cY (e y) = R) = decide (cY (e z) = R) → y = z := by
    rw [t₀]
    refine sep_of_sq (fun y => t.val (K := Qbar) y.left = OnePoint.some 0) (fun y => cY (e y)) R
      (fun y hy => ?_) (fun y z hy hz hyz => ?_)
    · obtain ⟨p, hpe, -, hp1⟩ := fibre_zero e hp hi y hy
      simp only [hpe, cY, Sum.elim_inl]; rw [hp1, hR2]
    · obtain ⟨p, hpe, hp2, -⟩ := fibre_zero e hp hi y hy
      obtain ⟨p', hpe', hp2', -⟩ := fibre_zero e hp hi z hz
      simp only [hpe, hpe', cY, Sum.elim_inl] at hyz
      apply e.injective
      rw [hpe, hpe']
      exact congrArg Sum.inl (Subtype.ext (Prod.ext (hp2.trans hp2'.symm) hyz))
  have sep₂ : ∀ y z : fieldPt Qbar ⟶ X, t.val (K := Qbar) y.left = t.val (K := Qbar) x₂.left →
      t.val (K := Qbar) z.left = t.val (K := Qbar) x₂.left →
      decide (cB (e y) = R) = decide (cB (e z) = R) → y = z := by
    rw [t₂]
    refine sep_of_sq (fun y => t.val (K := Qbar) y.left = OnePoint.infty) (fun y => cB (e y)) R
      (fun y hy => ?_) (fun y z hy hz hyz => ?_)
    · obtain ⟨b, hbe⟩ := fibre_infty e hp y hy
      simp only [hbe, cB, Sum.elim_inr]; rw [b.2, hR2]
    · obtain ⟨b, hbe⟩ := fibre_infty e hp y hy
      obtain ⟨b', hbe'⟩ := fibre_infty e hp z hz
      simp only [hbe, hbe', cB, Sum.elim_inr] at hyz
      apply e.injective
      rw [hbe, hbe']
      exact congrArg Sum.inr (Subtype.ext hyz)
  -- the CM types at the three points
  have c₁ : HasCM4 P₁.q := by
    rcases key x₁ _ sep₁ P₁ hP₁ with c | c | c
    · exact c
    · have := (hcl x₁ x₁ P₁ P₁ hP₁ hP₁).2.2.2 c
      rw [t₁] at this; exact absurd this (OnePoint.coe_ne_infty _)
    · have := (hcl x₁ x₁ P₁ P₁ hP₁ hP₁).2.1 c
      rw [t₁] at this; exact absurd (OnePoint.coe_injective this) one_ne_zero
  have c₀ : HasCM24 P₀.q := by
    rcases key x₀ _ sep₀ P₀ hP₀ with c | c | c
    · have := (hcl x₀ x₀ P₀ P₀ hP₀ hP₀).2.2.1 c
      rw [t₀] at this; exact absurd (OnePoint.coe_injective this) zero_ne_one
    · have := (hcl x₀ x₀ P₀ P₀ hP₀ hP₀).2.2.2 c
      rw [t₀] at this; exact absurd this (OnePoint.coe_ne_infty _)
    · exact c
  have c₂ : HasCM3 P₂.q := by
    rcases key x₂ _ sep₂ P₂ hP₂ with c | c | c
    · have := (hcl x₂ x₂ P₂ P₂ hP₂ hP₂).2.2.1 c
      rw [t₂] at this; exact absurd this.symm (OnePoint.coe_ne_infty _)
    · exact c
    · have := (hcl x₂ x₂ P₂ P₂ hP₂ hP₂).2.1 c
      rw [t₂] at this; exact absurd this.symm (OnePoint.coe_ne_infty _)
  refine ⟨Y, Φ, X, Ψ, fY, t, ((1 : ℚ) : OnePoint ℚ), OnePoint.infty, ((0 : ℚ) : OnePoint ℚ), h1, h6,
    OnePoint.coe_ne_infty _, fun h => one_ne_zero (OnePoint.coe_injective h),
    (OnePoint.coe_ne_infty _).symm, fun x x' P Q hP hQ => ⟨(hcl x x' P Q hP hQ).1, ?_, ?_, ?_⟩⟩
  · have e1 : ((1 : ℚ) : OnePoint ℚ).map (algebraMap ℚ Qbar) = OnePoint.some 1 := by simp
    rw [e1]
    refine ⟨(hcl x x' P Q hP hQ).2.2.1, fun hx => ?_⟩
    obtain ⟨α, ⟨f⟩⟩ := (hcl x₁ x P₁ P hP₁ hP).1.1 (t₁.trans hx.symm)
    exact HasCM4.of_iso f ((hasCM4_twist P₁.q α).2 c₁)
  · have e1 : (OnePoint.infty : OnePoint ℚ).map (algebraMap ℚ Qbar) = OnePoint.infty := rfl
    rw [e1]
    refine ⟨(hcl x x' P Q hP hQ).2.2.2, fun hx => ?_⟩
    obtain ⟨α, ⟨f⟩⟩ := (hcl x₂ x P₂ P hP₂ hP).1.1 (t₂.trans hx.symm)
    exact HasCM3.of_iso f ((hasCM3_twist P₂.q α).2 c₂)
  · have e1 : ((0 : ℚ) : OnePoint ℚ).map (algebraMap ℚ Qbar) = OnePoint.some 0 := by simp
    rw [e1]
    refine ⟨(hcl x x' P Q hP hQ).2.1, fun hx => ?_⟩
    obtain ⟨α, ⟨f⟩⟩ := (hcl x₀ x P₀ P hP₀ hP).1.1 (t₀.trans hx.symm)
    exact HasCM24.of_iso f ((hasCM24_twist P₀.q α).2 c₀)

theorem babaGranathRationalAb_of_printed
    (h : HDec.QMSplit.Moduli.ElkiesX6Star.ElkiesX6StarPrinted)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : HDec.QMSplit.Moduli.BabaGranathRationalAb :=
  babaGranathRationalAb_of_AL h (HDec.QMSplit.Aut.rows_of_C (HDec.QMLattice.qmCentralizerCMC_of hU hG hM)
    (HDec.AVB2.t11b_of_exists HDec.HSyn.t11bExists_lf8)).2.1

end BGExplicit

#print axioms BGExplicit.babaGranathRationalAb_of_AL
#print axioms BGExplicit.babaGranathRationalAb_of_printed
