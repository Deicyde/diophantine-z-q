import ZInQKernel.Contrib.OneProof.UniformizationPrinted

/-!
# unif-topology: the classical topology of `X(ℂ)` is the analytic topology

`ZInQKernel/Contrib/OneProof/UniformizationPrinted.lean` (unif-printed) proves the textbook field
`uniformizationLeafAll` (`BPAnalytic.Uniformization.UniformizationLeafAll`) from Mumford's theorem and
three statements of the analytic dictionary stated over `UnifPrinted.classicalTopology X`, the
coarsest topology on `X(ℂ)` in which every `U(ℂ)` is open and every regular function is continuous.
The prints use the analytic (Euclidean) topology. This file proves that the two agree:

* `induced_classicalTopology_eq`, `isEmbedding_coord`: for `U ⊆ X` affine and `f₁, …, f_k`
  generating `Γ(X, U)` as a `ℂ`-algebra (`Generates`), the map `U(ℂ) → ℂ^k`, `P ↦ (fᵢ(P))ᵢ`, is
  injective and the classical topology on `U(ℂ)` is the subspace topology of `ℂ^k`;
* `classicalTopology_eq_gluedTopology`: for any family of such affine charts whose `ℂ`-points cover
  `X(ℂ)`, the classical topology is the topology glued from the charts;
* `classicalTopology_eq_analyticTopology`: for `X` locally of finite type over `ℂ`, the classical
  topology equals `analyticTopology X` (the textbook definition: `S` open iff `S ∩ U(ℂ)` is open in
  `U(ℂ) ⊂ ℂ^k` for every affine chart).

Then the three dictionary leaves are restated over `analyticTopology` (`SmoothComplexManifoldAn`,
`ProperCompactAn`, `ConnectedConnectedAn`), shown equivalent to unif-printed's (`*_iff`), and
`uniformizationLeafAll_of_analytic` proves the field from them and `UnifPrinted.MumfordComplexTorus`.
Copied from `scratch/unif-topology/Topo.lean` (docs/research/unif-topology.md).
-/

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

/-! ## `U(ℂ) → ℂ^k` is injective: `U(ℂ)` is a subspace of `ℂ^k` -/

instance : IsAffine (PkgI3.AbVar.ptObj (K := ℂ) ℂ).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of ℂ)))

/-- A `ℂ`-point in an affine open `U` is determined by its ring map `Γ(X, U) → Γ(Spec ℂ, ⊤)`. -/
theorem eq_of_appLE_eq {U : X.left.Opens} (hU : IsAffineOpen U) {P Q : CPt X}
    (hP : ⊤ ≤ P.left ⁻¹ᵁ U) (hQ : ⊤ ≤ Q.left ⁻¹ᵁ U)
    (h : P.left.appLE U ⊤ hP = Q.left.appLE U ⊤ hQ) : P = Q := by
  have eP := IsAffineOpen.SpecMap_appLE_fromSpec P.left hU (isAffineOpen_top _) hP
  have eQ := IsAffineOpen.SpecMap_appLE_fromSpec Q.left hU (isAffineOpen_top _) hQ
  rw [h] at eP
  have e : (isAffineOpen_top _).fromSpec ≫ P.left = (isAffineOpen_top _).fromSpec ≫ Q.left :=
    eP.symm.trans eQ
  rw [IsAffineOpen.fromSpec_top] at e
  apply Over.OverMorphism.ext
  exact (cancel_epi _).mp e

/-- **`U(ℂ) → ℂ^k` is injective** for `U` affine and `f` generating `Γ(X, U)`. -/
theorem coord_injective {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) : Function.Injective (coord f) := by
  intro P Q hPQ
  have hev : evP P.1 U P.2 = evP Q.1 U Q.2 := by
    ext y
    obtain ⟨p, rfl⟩ := hf y
    simp only [MvPolynomial.coe_eval₂Hom]
    rw [evP_eval₂, evP_eval₂]
    have e1 : (fun i => evP P.1 U P.2 (f i)) = coord f P :=
      funext fun i => by rw [coord, xevalAt_eq_evP P.2]
    have e2 : (fun i => evP Q.1 U Q.2 (f i)) = coord f Q :=
      funext fun i => by rw [coord, xevalAt_eq_evP Q.2]
    rw [e1, e2, hPQ]
  have e : ∀ z : Γ(Spec (CommRingCat.of ℂ), ⊤), (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom z) = z := fun z => by
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ (Scheme.ΓSpecIso _).inv).hom z = z
    rw [Iso.hom_inv_id]; rfl
  refine Subtype.ext (eq_of_appLE_eq hU P.2 Q.2 (CommRingCat.hom_ext (RingHom.ext fun y => ?_)))
  have h1 : (P.1.left.appLE U ⊤ P.2).hom y =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (evP P.1 U P.2 y) := (e _).symm
  have h2 : (Q.1.left.appLE U ⊤ Q.2).hom y =
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom (evP Q.1 U Q.2 y) := (e _).symm
  refine h1.trans ?_
  rw [hev]
  exact h2.symm

/-- **Affine pieces, embedding form.** For `U` affine and `f₁, …, f_k` generating `Γ(X, U)`, the map
`U(ℂ) → ℂ^k` is a topological embedding when `U(ℂ) ⊂ X(ℂ)` carries the classical topology: `U(ℂ)` is
homeomorphic to its image with the subspace topology of `ℂ^k`. -/
theorem isEmbedding_coord {U : X.left.Opens} (hU : IsAffineOpen U) {k : ℕ}
    (f : Fin k → Γ(X.left, U)) (hf : Generates U f) :
    @Topology.IsEmbedding _ _ ((classicalTopology X).induced Subtype.val) _ (coord f) :=
  letI : TopologicalSpace (UPt X U) := (classicalTopology X).induced Subtype.val
  ⟨⟨induced_classicalTopology_eq hU f hf⟩, coord_injective hU f hf⟩

/-! ## Gluing along an affine cover -/

/-- The topology on `X(ℂ)` glued from affine charts: `S` is open iff for every `j`, `S ∩ U_j(ℂ)` is
open in `U_j(ℂ) ⊂ ℂ^{k_j}` (the topology induced by `coord (f j)`). -/
def gluedTopology {ι : Type*} (U : ι → X.left.Opens) (k : ι → ℕ)
    (f : ∀ j, Fin (k j) → Γ(X.left, U j)) : TopologicalSpace (CPt X) :=
  ⨆ j, TopologicalSpace.coinduced (Subtype.val : UPt X (U j) → CPt X)
    ((inferInstance : TopologicalSpace (Fin (k j) → ℂ)).induced (coord (f j)))

/-- **Gluing.** For any family of affine opens `U_j` with `ℂ`-algebra generators `f_j` of
`Γ(X, U_j)` whose `ℂ`-points cover `X(ℂ)`, the classical topology is the glued topology. -/
theorem classicalTopology_eq_gluedTopology {ι : Type*} (U : ι → X.left.Opens)
    (hU : ∀ j, IsAffineOpen (U j)) (k : ι → ℕ) (f : ∀ j, Fin (k j) → Γ(X.left, U j))
    (hf : ∀ j, Generates (U j) (f j)) (hcov : ∀ P : CPt X, ∃ j, XPtIn X P (U j)) :
    classicalTopology X = gluedTopology U k f := by
  have hA := fun j => induced_classicalTopology_eq (hU j) (f j) (hf j)
  apply le_antisymm
  · rw [TopologicalSpace.le_def]
    intro S (hS : @IsOpen _ (gluedTopology U k f) S)
    letI := classicalTopology X
    rw [gluedTopology, isOpen_iSup_iff] at hS
    simp only [isOpen_coinduced] at hS
    have hS' : ∀ j, ∃ O, IsOpen[classicalTopology X] O ∧
        (Subtype.val : UPt X (U j) → CPt X) ⁻¹' O = Subtype.val ⁻¹' S := by
      intro j
      have := hS j
      rw [← hA j] at this
      exact isOpen_induced_iff.mp this
    choose O hO hOS using hS'
    have hSeq : S = ⋃ j, O j ∩ {P | XPtIn X P (U j)} := by
      ext P
      simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro hP
        obtain ⟨j, hj⟩ := hcov P
        refine ⟨j, ?_, hj⟩
        have : (⟨P, hj⟩ : UPt X (U j)) ∈ Subtype.val ⁻¹' S := hP
        rw [← hOS j] at this
        exact this
      · rintro ⟨j, hPO, hj⟩
        have : (⟨P, hj⟩ : UPt X (U j)) ∈ Subtype.val ⁻¹' O j := hPO
        rw [hOS j] at this
        exact this
    rw [hSeq]
    exact @isOpen_iUnion _ _ (classicalTopology X) _ fun j =>
      @IsOpen.inter _ (classicalTopology X) _ _ (hO j) (isOpen_ptIn (U j))
  · refine iSup_le fun j => ?_
    rw [coinduced_le_iff_le_induced, ← hA j]

/-! ## The analytic topology -/

/-- An affine chart of the `ℂ`-scheme `X`: an affine open `U` with `ℂ`-algebra generators
`f₁, …, f_k` of `Γ(X, U)`, i.e. a closed embedding `U ↪ 𝔸^k_ℂ`, `P ↦ (f₁(P), …, f_k(P))`. -/
structure AffineChart (X : Over (Spec (CommRingCat.of ℂ))) where
  /-- the affine open -/
  U : X.left.Opens
  isAffine : IsAffineOpen U
  /-- the number of generators -/
  k : ℕ
  /-- the generators -/
  f : Fin k → Γ(X.left, U)
  generates : Generates U f

/-- **The analytic (Euclidean) topology on `X(ℂ)`** (Serre, GAGA §2; SGA 1, XII §1; Mumford, *Red
book* I §10; Hartshorne, App. B): `X(ℂ)` is covered by the sets `U(ℂ)`, `U` affine; through a closed
embedding `U ↪ 𝔸^k` (given by `ℂ`-algebra generators `f₁, …, f_k` of `Γ(X, U)`) `U(ℂ)` is a subset
of `ℂ^k` and carries the subspace topology; `S ⊆ X(ℂ)` is open iff every `S ∩ U(ℂ)` is open in
`U(ℂ)`. (Here over all affine charts at once; `classicalTopology_eq_gluedTopology` shows that any
covering family of charts gives the same topology.) -/
def analyticTopology (X : Over (Spec (CommRingCat.of ℂ))) : TopologicalSpace (CPt X) :=
  gluedTopology (fun c : AffineChart X => c.U) (fun c => c.k) (fun c => c.f)

/-- For `X` locally of finite type over `ℂ`, every `ℂ`-point lies in an affine chart. -/
theorem exists_affineChart [LocallyOfFiniteType X.hom] (P : CPt X) :
    ∃ c : AffineChart X, XPtIn X P c.U := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := X.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show P.left.base default ∈ (⊤ : X.left.Opens) from trivial) (⊤ : X.left.Opens).2
  have hft := HasRingHomProperty.appLE @LocallyOfFiniteType X.hom (inferInstance)
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by rw [Scheme.Hom.preimage_top]; exact le_top)
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom y, ?_⟩
    change ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ≫ (Scheme.ΓSpecIso _).inv).hom y = y
    rw [Iso.hom_inv_id]; rfl
  have hft' : (algC X V).FiniteType :=
    RingHom.FiniteType.comp hft (RingHom.FiniteType.of_surjective _ hsurj)
  letI := (algC X V).toAlgebra
  obtain ⟨n, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hft'
  refine ⟨⟨V, hV, n, fun i => φ (MvPolynomial.X i), fun y => ?_⟩, (xPtIn_iff _ _).mpr hxV⟩
  obtain ⟨p, hp⟩ := hφ y
  refine ⟨p, ?_⟩
  rw [← hp]
  conv_rhs => rw [MvPolynomial.aeval_unique φ]
  rfl

/-- **The classical topology is the analytic topology** (for `X` locally of finite type over `ℂ`). -/
theorem classicalTopology_eq_analyticTopology [LocallyOfFiniteType X.hom] :
    classicalTopology X = analyticTopology X :=
  classicalTopology_eq_gluedTopology _ (fun c => c.isAffine) _ _ (fun c => c.generates)
    exists_affineChart

/-! ## The printed leaves over the analytic topology -/

/-- **LEAF (printed form): the complex manifold `X(ℂ)` of a smooth variety.** For `X` smooth, proper
and irreducible over `ℂ`, the set `X(ℂ)` with its analytic topology is a complex (analytic) manifold,
regular functions are holomorphic on `U(ℂ)`, and at every point some regular functions (local
parameters) are local holomorphic coordinates. Shafarevich, *Basic algebraic geometry 2*, 2nd ed.
(1994), Ch. VII §1.1; Serre, GAGA (1956) §2; SGA 1, Exp. XII, 1.1 and 3.1; locators UNVERIFIED.
Same statement as `UnifPrinted.SmoothComplexManifold` with `analyticTopology` in place of
`classicalTopology` (equivalent: `smoothComplexManifoldAn_iff`). -/
def SmoothComplexManifoldAn : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), Smooth X.hom → IsProper X.hom → IrreducibleSpace X.left →
    letI := analyticTopology X
    ∃ (n : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt X)),
      IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt X) ∧
      (∀ (U : X.left.Opens) (f : Γ(X.left, U)),
        ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X U f) {P | XPtIn X P U}) ∧
      (∀ P : CPt X, ∃ (U : X.left.Opens) (f : Fin n → Γ(X.left, U)), XPtIn X P U ∧
        IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω
          (fun Q i => XevalAt X U (f i) Q) P)

/-- **LEAF (printed form): proper implies compact.** For `X` proper over `ℂ`, `X(ℂ)` is compact in the
analytic topology. Serre, GAGA (1956), §2, Prop. 6; SGA 1, Exp. XII, Prop. 3.2; locators UNVERIFIED. -/
def ProperCompactAn : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), IsProper X.hom →
    @CompactSpace (CPt X) (analyticTopology X)

/-- **LEAF (printed form): irreducible implies connected.** For `X` irreducible and proper over `ℂ`,
`X(ℂ)` is connected in the analytic topology. Shafarevich, *Basic algebraic geometry 2*, Ch. VII §2.1,
Thm. 1; SGA 1, Exp. XII, Prop. 2.4; locators UNVERIFIED. -/
def ConnectedConnectedAn : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of ℂ))), IsProper X.hom → IrreducibleSpace X.left →
    @ConnectedSpace (CPt X) (analyticTopology X)

theorem smoothComplexManifoldAn_iff : SmoothComplexManifoldAn ↔ SmoothComplexManifold := by
  refine forall_congr' fun X => imp_congr_right fun _ => imp_congr_right fun hP =>
    imp_congr_right fun _ => ?_
  haveI := hP
  rw [classicalTopology_eq_analyticTopology]

theorem properCompactAn_iff : ProperCompactAn ↔ ProperCompact := by
  refine forall_congr' fun X => imp_congr_right fun hP => ?_
  haveI := hP
  rw [classicalTopology_eq_analyticTopology]

theorem connectedConnectedAn_iff : ConnectedConnectedAn ↔ ConnectedConnected := by
  refine forall_congr' fun X => imp_congr_right fun hP => imp_congr_right fun _ => ?_
  haveI := hP
  rw [classicalTopology_eq_analyticTopology]

/-- **Main theorem.** `UniformizationLeafAll` from Mumford's theorem and the three dictionary
statements over the analytic topology of `X(ℂ)`. -/
theorem uniformizationLeafAll_of_analytic (hM : MumfordComplexTorus)
    (hMan : SmoothComplexManifoldAn) (hPC : ProperCompactAn) (hCC : ConnectedConnectedAn) :
    BPAnalytic.Uniformization.UniformizationLeafAll :=
  uniformizationLeafAll_of_printed hM (smoothComplexManifoldAn_iff.mp hMan)
    (properCompactAn_iff.mp hPC) (connectedConnectedAn_iff.mp hCC)

end UnifTopology
