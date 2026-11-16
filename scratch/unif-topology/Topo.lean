import ZInQKernel.Contrib.OneProof.UniformizationPrinted

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits

set_option linter.unusedSectionVars false

noncomputable section

namespace UnifTopology

open UnifPrinted

variable {X : Over (Spec (CommRingCat.of ℂ))}

instance : Unique (PkgI3.AbVar.ptObj (K := ℂ) ℂ).left :=
  inferInstanceAs (Unique (Spec (CommRingCat.of ℂ)))

/-! ## Evaluation at `ℂ`-points as a `ℂ`-algebra map -/

/-- The structure map `ℂ → Γ(X, U)` of the `ℂ`-scheme `X`. -/
def algC (X : Over (Spec (CommRingCat.of ℂ))) (U : X.left.Opens) : ℂ →+* Γ(X.left, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ U (by rw [Scheme.Hom.preimage_top]; exact le_top)).hom

/-- Evaluation at a `ℂ`-point `P ∈ U(ℂ)`, as a ring map `Γ(X, U) → ℂ`. -/
def evP (P : CPt X) (U : X.left.Opens) (h : XPtIn X P U) : Γ(X.left, U) →+* ℂ :=
  (P.left.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom

theorem xevalAt_eq_evP {P : CPt X} {U : X.left.Opens} (h : XPtIn X P U) (f : Γ(X.left, U)) :
    XevalAt X U f P = evP P U h f := by
  unfold XevalAt
  rw [dite_eq_left_of_eq_true (eq_true h)]
  rfl

theorem appLE_id_top (φ : Spec (CommRingCat.of ℂ) ⟶ Spec (CommRingCat.of ℂ)) (e) (hφ : φ = 𝟙 _) :
    φ.appLE ⊤ ⊤ e = 𝟙 _ := by
  subst hφ
  exact (Spec (CommRingCat.of ℂ)).presheaf.map_id _

/-- Evaluation at a `ℂ`-point is a `ℂ`-algebra map. -/
theorem evP_comp_algC (P : CPt X) (U : X.left.Opens) (h : XPtIn X P U) :
    (evP P U h).comp (algC X U) = RingHom.id ℂ := by
  have h' : ⊤ ≤ P.left ⁻¹ᵁ U := h
  have hw : P.left ≫ X.hom = 𝟙 _ := by rw [Over.w P, ptObj_hom]
  have key : X.hom.appLE ⊤ U (by rw [Scheme.Hom.preimage_top]; exact le_top) ≫
      P.left.appLE U ⊤ h' = 𝟙 _ := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact appLE_id_top _ _ hw
  have key' : ∀ y, (P.left.appLE U ⊤ h').hom
      ((X.hom.appLE ⊤ U (by rw [Scheme.Hom.preimage_top]; exact le_top)).hom y) = y := fun y => by
    rw [← CommRingCat.comp_apply, key]; rfl
  ext c
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom c) = c := by
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (Scheme.ΓSpecIso _).hom).hom c = c
    rw [Iso.inv_hom_id]; rfl
  exact (congrArg (fun y => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom y) (key' _)).trans e2

/-- `f : Fin k → Γ(X, U)` generates `Γ(X, U)` as a `ℂ`-algebra: the `ℂ`-algebra map
`ℂ[x₁, …, x_k] → Γ(X, U)`, `xᵢ ↦ fᵢ`, is surjective (for `U` affine: `f` is a closed embedding
`U ↪ 𝔸^k`). -/
def Generates (U : X.left.Opens) {k : ℕ} (f : Fin k → Γ(X.left, U)) : Prop :=
  Function.Surjective (MvPolynomial.eval₂Hom (algC X U) f)

theorem evP_eval₂ (P : CPt X) (U : X.left.Opens) (h : XPtIn X P U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (p : MvPolynomial (Fin k) ℂ) :
    evP P U h (MvPolynomial.eval₂ (algC X U) f p) =
      MvPolynomial.eval (fun i => evP P U h (f i)) p := by
  rw [MvPolynomial.eval₂_comp_left, evP_comp_algC, MvPolynomial.eval₂_id]
  rfl

/-! ## Points and basic opens -/

theorem xPtIn_iff (P : CPt X) (W : X.left.Opens) :
    XPtIn X P W ↔ P.left.base (default : Spec (CommRingCat.of ℂ)) ∈ W := by
  constructor
  · intro h
    exact h (show (default : Spec (CommRingCat.of ℂ)) ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
  · intro h y _
    rw [Subsingleton.elim y default]
    exact h

/-- `P ∈ D(s)(ℂ)` iff `s(P) ≠ 0`. -/
theorem xPtIn_basicOpen_iff (P : CPt X) {U : X.left.Opens} (h : XPtIn X P U) (s : Γ(X.left, U)) :
    XPtIn X P (X.left.basicOpen s) ↔ evP P U h s ≠ 0 := by
  have hb := Scheme.basicOpen_appLE P.left ⊤ U h s
  rw [top_inf_eq] at hb
  unfold XPtIn
  rw [← hb]
  set r := P.left.appLE U ⊤ h s with hr
  have hev : evP P U h s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r := rfl
  rw [hev]
  constructor
  · intro htop h0
    have hr0 : r = 0 := by
      have e : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom r) = r := by
        change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ (Scheme.ΓSpecIso _).inv).hom r = r
        rw [Iso.hom_inv_id]; rfl
      rw [← e]
      change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) = 0
      rw [h0, map_zero]
    rw [hr0, Scheme.basicOpen_zero] at htop
    exact htop (show (default : Spec (CommRingCat.of ℂ)) ∈ (⊤ : (Spec (CommRingCat.of ℂ)).Opens) from trivial)
  · intro hne
    have hu : IsUnit r := by
      have h1 : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom r) := Ne.isUnit hne
      have h2 := h1.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      have e : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
          ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom r) = r := by
        change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ (Scheme.ΓSpecIso _).inv).hom r = r
        rw [Iso.hom_inv_id]; rfl
      rwa [e] at h2
    rw [Scheme.basicOpen_of_isUnit _ hu]

/-! ## The chart `U(ℂ) → ℂ^k` -/

/-- The `ℂ`-points of `X` lying in `U`. -/
abbrev UPt (X : Over (Spec (CommRingCat.of ℂ))) (U : X.left.Opens) : Type :=
  {P : CPt X // XPtIn X P U}

/-- The coordinate map `U(ℂ) → ℂ^k`, `P ↦ (f₁(P), …, f_k(P))`. -/
def coord {U : X.left.Opens} {k : ℕ} (f : Fin k → Γ(X.left, U)) : UPt X U → (Fin k → ℂ) :=
  fun P i => XevalAt X U (f i) P.1

theorem continuous_xevalAt_restrict (U : X.left.Opens) (g : Γ(X.left, U)) :
    Continuous[(classicalTopology X).induced Subtype.val, _]
      (fun P : UPt X U => XevalAt X U g P.1) := by
  letI := classicalTopology X
  rw [continuous_iff_continuousAt]
  intro P₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hopen : IsOpen {P : CPt X | XPtIn X P U ∧ ‖XevalAt X U g P - XevalAt X U g P₀.1‖ < ε} :=
    isOpen_basic g _ ε
  have hmem := (hopen.preimage continuous_subtype_val).mem_nhds
    (show P₀ ∈ Subtype.val ⁻¹' _ from ⟨P₀.2, by simpa using hε⟩)
  filter_upwards [hmem] with P hP
  rw [dist_eq_norm]
  exact hP.2

/-- **Main lemma.** For `U` affine and `f` generating `Γ(X, U)`, the inclusion `U(ℂ) → X(ℂ)` is
continuous from the topology induced by `f : U(ℂ) → ℂ^k` to the classical topology: every regular
function on a Zariski open `V` is, near each point of `U(ℂ) ∩ V(ℂ)`, a quotient of polynomials in
the coordinates (`IsAffineOpen.isLocalization_basicOpen`). -/
theorem continuous_val_coord {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) :
    Continuous[(inferInstance : TopologicalSpace (Fin k → ℂ)).induced (coord f),
      classicalTopology X] (Subtype.val : UPt X U → CPt X) := by
  letI tC := classicalTopology X
  letI tU : TopologicalSpace (UPt X U) := TopologicalSpace.induced (coord f) inferInstance
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨V, g, z, ε, rfl⟩
  rw [isOpen_iff_forall_mem_open]
  rintro P₀ ⟨hP₀V, hP₀ε⟩
  have hP₀U : XPtIn X P₀.1 U := P₀.2
  have hxU := (xPtIn_iff _ _).mp hP₀U
  have hxV := (xPtIn_iff _ _).mp hP₀V
  obtain ⟨s, hsle, hxs⟩ := hU.exists_basicOpen_le (V := U ⊓ V) ⟨_, ⟨hxU, hxV⟩⟩ hxU
  have hsV : X.left.basicOpen s ≤ V := hsle.trans inf_le_right
  haveI := hU.isLocalization_basicOpen s
  obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.surj (Submonoid.powers s) (res hsV g)
  obtain ⟨m, hm⟩ := t.2
  obtain ⟨pa, hpa⟩ := hf a
  obtain ⟨ps, hps⟩ := hf s
  simp only [MvPolynomial.coe_eval₂Hom] at hpa hps
  -- the identity at a point of `D(s)(ℂ)`
  have hval : ∀ Q : UPt X U, XPtIn X Q.1 (X.left.basicOpen s) →
      XPtIn X Q.1 V ∧ XevalAt X V g Q.1 * (XevalAt X U s Q.1) ^ m = XevalAt X U a Q.1 := by
    intro Q hQ
    refine ⟨xPtIn_mono hsV hQ, ?_⟩
    have e1 := congrArg (evP Q.1 _ hQ) hat
    simp only [map_mul] at e1
    rw [← xevalAt_eq_evP] at e1
    rw [← xevalAt_eq_evP hQ, ← xevalAt_eq_evP hQ] at e1
    have e2 : XevalAt X (X.left.basicOpen s) (algebraMap Γ(X.left, U) Γ(X.left, X.left.basicOpen s)
        (t : Γ(X.left, U))) Q.1 = XevalAt X U t Q.1 :=
      xevalAt_res (X.left.basicOpen_le s) _ hQ
    have e3 : XevalAt X (X.left.basicOpen s) (algebraMap Γ(X.left, U) Γ(X.left, X.left.basicOpen s)
        a) Q.1 = XevalAt X U a Q.1 :=
      xevalAt_res (X.left.basicOpen_le s) _ hQ
    rw [xevalAt_res hsV _ hQ, e2, e3] at e1
    rw [← e1, ← hm, xevalAt_eq_evP Q.2, xevalAt_eq_evP Q.2, map_pow]
  have hcoord : ∀ (Q : UPt X U) (p : MvPolynomial (Fin k) ℂ),
      XevalAt X U (MvPolynomial.eval₂ (algC X U) f p) Q.1 = MvPolynomial.eval (coord f Q) p := by
    intro Q p
    rw [xevalAt_eq_evP Q.2, evP_eval₂]
    have : (fun i => evP Q.1 U Q.2 (f i)) = coord f Q :=
      funext fun i => by rw [coord, xevalAt_eq_evP Q.2]
    rw [this]
  let F : (Fin k → ℂ) → ℂ := fun w => MvPolynomial.eval w pa / (MvPolynomial.eval w ps) ^ m
  let W : Set (Fin k → ℂ) := {w | MvPolynomial.eval w ps ≠ 0} ∩ F ⁻¹' Metric.ball z ε
  have hWopen : IsOpen W := by
    have h0 : IsOpen {w : Fin k → ℂ | MvPolynomial.eval w ps ≠ 0} :=
      isOpen_ne_fun (MvPolynomial.continuous_eval ps) continuous_const
    refine ContinuousOn.isOpen_inter_preimage ?_ h0 Metric.isOpen_ball
    exact (MvPolynomial.continuous_eval pa).continuousOn.div
      ((MvPolynomial.continuous_eval ps).pow m).continuousOn fun w hw => pow_ne_zero _ hw
  -- on `D(s)(ℂ)`, `g = a / s^m`
  have hF : ∀ Q : UPt X U, MvPolynomial.eval (coord f Q) ps ≠ 0 →
      XPtIn X Q.1 V ∧ F (coord f Q) = XevalAt X V g Q.1 := by
    intro Q hQ
    have hQs : XevalAt X U s Q.1 ≠ 0 := by rw [← hps, hcoord]; exact hQ
    have hQD : XPtIn X Q.1 (X.left.basicOpen s) := by
      rw [xPtIn_basicOpen_iff _ Q.2, ← xevalAt_eq_evP]; exact hQs
    obtain ⟨hQV, he⟩ := hval Q hQD
    refine ⟨hQV, ?_⟩
    simp only [F]
    rw [← hcoord, ← hcoord, hpa, hps, ← he, mul_div_assoc, div_self (pow_ne_zero _ hQs), mul_one]
  refine ⟨coord f ⁻¹' W, ?_, isOpen_induced hWopen, ?_⟩
  · rintro Q ⟨hQ, hQb⟩
    obtain ⟨hQV, he⟩ := hF Q hQ
    refine ⟨hQV, ?_⟩
    rw [← he]
    simpa [Metric.mem_ball, dist_eq_norm] using hQb
  · have hP₀D : XPtIn X P₀.1 (X.left.basicOpen s) := (xPtIn_iff _ _).mpr hxs
    have hne : MvPolynomial.eval (coord f P₀) ps ≠ 0 := by
      rw [← hcoord, hps, xevalAt_eq_evP P₀.2, ← xPtIn_basicOpen_iff]; exact hP₀D
    refine ⟨hne, ?_⟩
    obtain ⟨-, he⟩ := hF P₀ hne
    show F (coord f P₀) ∈ Metric.ball z ε
    rw [he, Metric.mem_ball, dist_eq_norm]
    exact hP₀ε

/-- **Affine pieces.** For `U` affine and `f₁, …, f_k` generating `Γ(X, U)` as a `ℂ`-algebra, the
classical topology restricted to `U(ℂ)` is the topology induced by `U(ℂ) → ℂ^k`. -/
theorem induced_classicalTopology_eq {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) :
    (classicalTopology X).induced (Subtype.val : UPt X U → CPt X) =
      (inferInstance : TopologicalSpace (Fin k → ℂ)).induced (coord f) := by
  apply le_antisymm
  · letI : TopologicalSpace (UPt X U) := (classicalTopology X).induced Subtype.val
    exact continuous_iff_le_induced.mp
      (continuous_pi fun i => continuous_xevalAt_restrict U (f i))
  · exact continuous_iff_le_induced.mp (continuous_val_coord hU f hf)

end UnifTopology
