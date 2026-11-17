/-
H5 FIX EDITION STEP-F1 (NEW edition, 2026-11-17, H5 lane3 ). SOURCE ONLY, UNCOMPILED by lane3.
Base file: step2-b/src/ZInQKernel/Contrib/CloudR2NOS/Step2B2/Mumford.lean (sha256 1cc1b27a7e9f0141729ef488a8996c6ad646e15ca0d7e3d47d37dec259a1569e).
Body changes relative to the base: ONLY P1 (record step-fix1/FIX_RECORD_STEP_F1.json). The base header below describes the BASE edition.
-/
/-
H5 lane3 Step 2, B2.d (d.3): `MumfordContractedCombinatorics` PROVED from (d.1), (d.2), the
small obligations of MumfordSmall.lean, B1's `SupportComponentsFinite`, Step2B1 translation
lemmas, and Mathlib commutativity. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.
The proof is the one in the MumfordSmall.lean header.
COMPILE NOTE: the commutative-group identities between rational points are closed by
`convert … using 2; simp [mul_comm, mul_assoc, mul_left_comm]`. Each is a true identity in a
commutative group, but this simp normalization is unverified until compile. If it does not
close, replace it with explicit `mul_comm`/`mul_inv_cancel_left` rewrites.
-/
import ZInQKernel.Contrib.CloudR2NOS.Step2B2.MumfordSmall

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.MonObj

open scoped CategoryTheory.MonoidalCategory

namespace ZInQ.Contrib.CloudR2NOS.Step2B2

local notation "tr" => H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation

theorem mumfordContractedCombinatorics (hMink : MinkowskiIrreducible.{u})
    (hPur : PurityTranslateEquality.{u}) (hPT : PointTranslation.{u}) (hPI : PointInversion.{u})
    (hJ1 : RationalPointsDetermineClosed.{u}) (hJ3 : IrreducibleInComponent.{u})
    (hJ4 : PointsOfSupportInComponents.{u})
    (hFin : ZInQ.Contrib.CloudR2NOS.Step2B1.SupportComponentsFinite.{u}) :
    MumfordContractedCombinatorics.{u} := by
  intro K _ _ A _ D hD C hCcl hCirr hCinf hH
  classical
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  let pt : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) → A.X.left :=
    fun x => x.left (IsLocalRing.closedPoint K)
  let Z : Set A.X.left := (D.support : Set A.X.left)
  have hZcl : IsClosed Z := D.support.isClosed
  let IsComp : Set A.X.left → Prop :=
    Maximal (fun Y : Set A.X.left => Y ⊆ Z ∧ IsIrreducible Y)
  -- basic translation facts
  have tr_inv_tr : ∀ (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) (a : A.X.left),
      tr A y (tr A y⁻¹ a) = a := by
    intro y a
    have h := congrArg (fun φ : A.X.left ⟶ A.X.left => φ a)
      ((ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul A y⁻¹ y).symm.trans
        (by rw [inv_mul_cancel]; exact ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one A))
    simpa using h
  have tr_tr_inv : ∀ (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) (a : A.X.left),
      tr A y⁻¹ (tr A y a) = a := by
    intro y a
    simpa using tr_inv_tr y⁻¹ a
  haveI tr_iso : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X, IsIso (tr A y) := fun y =>
    ⟨⟨tr A y⁻¹, by
      rw [← ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul, mul_inv_cancel,
        ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one], by
      rw [← ZInQ.Contrib.CloudR2NOS.Step2B1.tr_mul, inv_mul_cancel,
        ZInQ.Contrib.CloudR2NOS.Step2B1.tr_one]⟩⟩
  have tr_closed : ∀ y (S : Set A.X.left), IsClosed S → IsClosed ((tr A y) ⁻¹' S) :=
    fun y S hS => hS.preimage (tr A y).continuous
  -- the preimage under `tr y⁻¹` is the image under `tr y`; irreducibility is preserved
  have tr_irr : ∀ y (S : Set A.X.left), IsIrreducible S → IsIrreducible ((tr A y⁻¹) ⁻¹' S) := by
    intro y S hS
    have he : (tr A y⁻¹) ⁻¹' S = (tr A y) '' S := by
      ext a
      constructor
      · intro ha
        exact ⟨tr A y⁻¹ a, ha, tr_inv_tr y a⟩
      · rintro ⟨b, hb, rfl⟩
        change tr A y⁻¹ (tr A y b) ∈ S
        rw [tr_tr_inv]
        exact hb
    rw [he]
    exact hS.image _ (tr A y).continuous.continuousOn
  -- components are closed
  have comp_closed : ∀ F, IsComp F → IsClosed F := by
    intro F hF
    have h1 : closure F ⊆ Z := closure_minimal hF.1.1 hZcl
    have h2 : IsIrreducible (closure F) := hF.1.2.closure
    have h3 : closure F ⊆ F := hF.2 ⟨h1, h2⟩ subset_closure
    exact closure_subset_iff_isClosed.mp h3
  -- a rational point of `C`
  obtain ⟨c₀, hc₀⟩ := hCinf.nonempty
  -- the closed set `Q` and its inverse
  let Q : Set A.X.left := ⋂ c ∈ {c : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X | pt c ∈ C},
    (tr A c) ⁻¹' Z
  have hQcl : IsClosed Q := isClosed_biInter fun c _ => tr_closed c Z hZcl
  let Qm : Set A.X.left := ((ι[A.X]).left) ⁻¹' Q
  have hQmcl : IsClosed Qm := hQcl.preimage (ι[A.X]).left.continuous
  -- the component claim: every component is fixed by `c * c₀⁻¹`
  have key : ∀ F, IsComp F → ∀ c, pt c ∈ C → (tr A (c * c₀⁻¹)) ⁻¹' F = F := by
    intro F hF
    have hFcl := comp_closed F hF
    -- S1: Minkowski points lie in `Q ∪ Qm`
    have hS1 : ∀ d c : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X, pt d ∈ F → pt c ∈ C →
        pt (d * c⁻¹) ∈ Q ∪ Qm := by
      intro d c hd hc
      set x := d * c⁻¹
      have hcx : c * x = d := by simp [x, mul_comm d]
      have hcW : pt c ∈ (tr A x) ⁻¹' Z := by
        change tr A x (pt c) ∈ Z
        rw [hPT A c x, hcx]
        exact hF.1.1 hd
      rcases hH x with hsub | hdisj
      · rcases (isIrreducible_iff_closed_union_closed.mp hCirr).2 _ _ (tr_closed x Z hZcl)
            (tr_closed x⁻¹ Z hZcl) hsub with h | h
        · left
          refine Set.mem_iInter₂.mpr fun c' hc' => ?_
          change tr A c' (pt x) ∈ Z
          rw [hPT A x c', mul_comm, ← hPT A c' x]
          exact h hc'
        · right
          change (ι[A.X]).left (pt x) ∈ Q
          rw [hPI A x]
          refine Set.mem_iInter₂.mpr fun c' hc' => ?_
          change tr A c' (pt x⁻¹) ∈ Z
          rw [hPT A x⁻¹ c', mul_comm, ← hPT A c' x⁻¹]
          exact h hc'
      · exfalso
        have h := Set.mem_inter hc (Or.inl hcW)
        rw [hdisj] at h
        exact h
    -- S2: case split, by irreducibility of the Minkowski closure
    have hM := hMink A F C hFcl hF.1.2 hCcl hCirr
    have hMsub : closure {a : A.X.left | ∃ e f : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
        pt e ∈ F ∧ pt f ∈ C ∧ a = pt (e * f⁻¹)} ⊆ Q ∪ Qm := by
      refine closure_minimal ?_ (hQcl.union hQmcl)
      rintro _ ⟨e, f, he, hf, rfl⟩
      exact hS1 e f he hf
    rcases (isIrreducible_iff_closed_union_closed.mp hM).2 _ _ hQcl hQmcl hMsub with hA | hB
    · -- Case A
      have hA' : ∀ d c c' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X, pt d ∈ F → pt c ∈ C →
          pt c' ∈ C → pt (d * c⁻¹ * c') ∈ Z := by
        intro d c c' hd hc hc'
        have h := Set.mem_iInter₂.mp (hA (subset_closure ⟨d, c, hd, hc, rfl⟩)) c' hc'
        rwa [hPT A (d * c⁻¹) c'] at h
      intro c hc
      set y := c * c₀⁻¹
      -- `E_y := tr y⁻¹ ⁻¹' F` lies in `F`, via the component trick
      have hEsubF : (tr A y⁻¹) ⁻¹' F ⊆ F := by
        -- the closed conditions `B_G`
        let B : Set A.X.left → Set A.X.left := fun G =>
          ⋂ d ∈ {d : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X | pt d ∈ F}, (tr A (d * c₀⁻¹)) ⁻¹' G
        have hBcl : ∀ G, IsComp G → IsClosed (B G) := fun G hG =>
          isClosed_biInter fun d _ => tr_closed _ G (comp_closed G hG)
        have hcover : ∀ c' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X, pt c' ∈ C →
            ∃ G, IsComp G ∧ pt c' ∈ B G := by
          intro c' hc'
          -- `E_{c' c₀⁻¹}` is irreducible and lies in `Z`
          have hEZ : (tr A (c' * c₀⁻¹)⁻¹) ⁻¹' F ⊆ Z := by
            refine hJ1 A _ Z (tr_closed _ F hFcl) hZcl fun x hx => ?_
            change tr A (c' * c₀⁻¹)⁻¹ (pt x) ∈ F at hx
            rw [hPT A x] at hx
            have := hA' (x * (c' * c₀⁻¹)⁻¹) c₀ c' hx hc₀ hc'
            convert this using 2
            simp [mul_comm, mul_assoc, mul_left_comm]
          obtain ⟨G, hG, hEG⟩ := hJ3 A D _ hEZ (tr_irr _ F hF.1.2)
          refine ⟨G, hG, Set.mem_iInter₂.mpr fun d hd => ?_⟩
          change tr A (d * c₀⁻¹) (pt c') ∈ G
          rw [hPT A c' (d * c₀⁻¹)]
          apply hEG
          change tr A (c' * c₀⁻¹)⁻¹ (pt (c' * (d * c₀⁻¹))) ∈ F
          rw [hPT A]
          convert hd using 2
          simp [mul_comm, mul_assoc, mul_left_comm]
        -- the finitely many closed sets `B G` cover `C`
        have hCfin := hFin A D
        let 𝓑 : Set (Set A.X.left) := B '' {G | IsComp G}
        have h𝓑fin : 𝓑.Finite := hCfin.image B
        have hCB : C ⊆ ⋃₀ 𝓑 := by
          refine hJ1 A C _ hCcl (?_) fun c' hc' => ?_
          · exact Set.Finite.isClosed_sUnion h𝓑fin (by rintro _ ⟨G, hG, rfl⟩; exact hBcl G hG)
          · obtain ⟨G, hG, hmem⟩ := hcover c' hc'
            exact Set.mem_sUnion.mpr ⟨B G, ⟨G, hG, rfl⟩, hmem⟩
        obtain ⟨_, ⟨G₀, hG₀, rfl⟩, hCG₀⟩ :=
          (isIrreducible_iff_sUnion_isClosed.mp hCirr) h𝓑fin.toFinset
            (by intro z hz; rw [Set.Finite.mem_toFinset] at hz; obtain ⟨G, hG, rfl⟩ := hz;
                exact hBcl G hG)
            (by simpa using hCB)
        -- `G₀ = F`, using `c₀`
        have hFG₀ : F ⊆ G₀ := by
          refine hJ1 A F G₀ hFcl (comp_closed G₀ hG₀) fun d hd => ?_
          have := Set.mem_iInter₂.mp (hCG₀ hc₀) d hd
          change tr A (d * c₀⁻¹) (pt c₀) ∈ G₀ at this
          rw [hPT A] at this
          convert this using 2
          simp [mul_comm, mul_assoc]
        have hG₀F : G₀ = F := Set.Subset.antisymm (hF.2 hG₀.1 hFG₀) hFG₀
        -- conclude `E_y ⊆ F` from `pt c ∈ B F`
        refine hJ1 A _ F (tr_closed _ F hFcl) hFcl fun x hx => ?_
        have hcB := Set.mem_iInter₂.mp (hCG₀ hc) (x * y⁻¹) (by
          change tr A y⁻¹ (pt x) ∈ F at hx
          rwa [hPT A] at hx)
        change tr A ((x * y⁻¹) * c₀⁻¹) (pt c) ∈ G₀ at hcB
        rw [hPT A, hG₀F] at hcB
        convert hcB using 2
        simp [y, mul_comm, mul_assoc, mul_left_comm]
      -- (d.2): equality, then transport to `tr y`
      have hEq : (tr A y⁻¹) ⁻¹' F = F := hPur A D hD (tr A y⁻¹) F F hF hF hEsubF
      ext a
      constructor
      · intro ha
        change tr A y a ∈ F at ha
        rw [← hEq] at ha
        change tr A y⁻¹ (tr A y a) ∈ F at ha
        rwa [tr_tr_inv] at ha
      · intro ha
        change tr A y a ∈ F
        rw [← hEq]
        change tr A y⁻¹ (tr A y a) ∈ F
        rwa [tr_tr_inv]
    · -- Case B
      have hB' : ∀ d c c' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X, pt d ∈ F → pt c ∈ C →
          pt c' ∈ C → pt (c * d⁻¹ * c') ∈ Z := by
        intro d c c' hd hc hc'
        have h := hB (subset_closure ⟨d, c, hd, hc, rfl⟩)
        change (ι[A.X]).left (pt (d * c⁻¹)) ∈ Q at h
        rw [hPI A] at h
        have h2 := Set.mem_iInter₂.mp h c' hc'
        change tr A c' (pt (d * c⁻¹)⁻¹) ∈ Z at h2
        rw [hPT A] at h2
        convert h2 using 2
        simp [mul_comm, mul_assoc, mul_left_comm]
      -- the reflections `ρ_s(a) = a⁻¹ s` and the sets `R_s := ρ_s⁻¹ F`
      let ρ : (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) → (A.X.left ⟶ A.X.left) :=
        fun s => (ι[A.X]).left ≫ tr A s
      have hρpt : ∀ s x, ρ s (pt x) = pt (x⁻¹ * s) := by
        intro s x
        change tr A s ((ι[A.X]).left (pt x)) = _
        rw [hPI A, hPT A]
      haveI hρiso : ∀ s, IsIso (ρ s) := fun s => by
        haveI : IsIso (ι[A.X]).left :=
          (inferInstance : IsIso ((Over.forget (Spec (CommRingCat.of K))).map ι[A.X]))
        exact IsIso.comp_isIso
      -- all `R_{c c₀}` lie in one component `G₁`, by the component trick in `c`
      let B : Set A.X.left → Set A.X.left := fun G =>
        ⋂ d ∈ {d : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X | pt d ∈ F},
          (tr A (c₀ * d⁻¹)) ⁻¹' G
      have hBcl : ∀ G, IsComp G → IsClosed (B G) := fun G hG =>
        isClosed_biInter fun d _ => tr_closed _ G (comp_closed G hG)
      have hRZ : ∀ c, pt c ∈ C → (ρ (c * c₀)) ⁻¹' F ⊆ Z := by
        intro c hc
        refine hJ1 A _ Z (hFcl.preimage (ρ (c * c₀)).continuous) hZcl fun x hx => ?_
        change ρ (c * c₀) (pt x) ∈ F at hx
        rw [hρpt] at hx
        have := hB' (x⁻¹ * (c * c₀)) c c₀ hx hc hc₀
        convert this using 2
        simp [mul_comm, mul_assoc, mul_left_comm]
      have hRirr : ∀ s, IsIrreducible ((ρ s) ⁻¹' F) := by
        intro s
        have hinv1 : ∀ b, inv (ρ s) (ρ s b) = b := fun b => by
          rw [← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
          rfl
        have hinv2 : ∀ b, ρ s (inv (ρ s) b) = b := fun b => by
          rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
          rfl
        have he : (ρ s) ⁻¹' F = (inv (ρ s)) '' F := by
          ext a
          exact ⟨fun ha => ⟨ρ s a, ha, hinv1 a⟩, by
            rintro ⟨b, hb, rfl⟩
            change ρ s (inv (ρ s) b) ∈ F
            rw [hinv2]
            exact hb⟩
        rw [he]
        exact hF.1.2.image _ (inv (ρ s)).continuous.continuousOn
      have hcover : ∀ c, pt c ∈ C → ∃ G, IsComp G ∧ pt c ∈ B G := by
        intro c hc
        obtain ⟨G, hG, hRG⟩ := hJ3 A D _ (hRZ c hc) (hRirr _)
        refine ⟨G, hG, Set.mem_iInter₂.mpr fun d hd => ?_⟩
        change tr A (c₀ * d⁻¹) (pt c) ∈ G
        rw [hPT A]
        apply hRG
        change ρ (c * c₀) (pt (c * (c₀ * d⁻¹))) ∈ F
        rw [hρpt]
        convert hd using 2
        simp [mul_comm, mul_assoc, mul_left_comm]
      have hCfin := hFin A D
      let 𝓑 : Set (Set A.X.left) := B '' {G | IsComp G}
      have h𝓑fin : 𝓑.Finite := hCfin.image B
      have hCB : C ⊆ ⋃₀ 𝓑 := by
        refine hJ1 A C _ hCcl (?_) fun c' hc' => ?_
        · exact Set.Finite.isClosed_sUnion h𝓑fin (by rintro _ ⟨G, hG, rfl⟩; exact hBcl G hG)
        · obtain ⟨G, hG, hmem⟩ := hcover c' hc'
          exact Set.mem_sUnion.mpr ⟨B G, ⟨G, hG, rfl⟩, hmem⟩
      obtain ⟨_, ⟨G₁, hG₁, rfl⟩, hCG₁⟩ :=
        (isIrreducible_iff_sUnion_isClosed.mp hCirr) h𝓑fin.toFinset
          (by intro z hz; rw [Set.Finite.mem_toFinset] at hz; obtain ⟨G, hG, rfl⟩ := hz;
              exact hBcl G hG)
          (by simpa using hCB)
      -- each `R_{c c₀}` lies in `G₁`, hence equals it by (d.2)
      have hRG₁ : ∀ c, pt c ∈ C → (ρ (c * c₀)) ⁻¹' F = G₁ := by
        intro c hc
        refine hPur A D hD (ρ (c * c₀)) F G₁ hF hG₁ ?_
        refine hJ1 A _ G₁ (hFcl.preimage (ρ (c * c₀)).continuous) (comp_closed G₁ hG₁)
          fun x hx => ?_
        change ρ (c * c₀) (pt x) ∈ F at hx
        rw [hρpt] at hx
        have := Set.mem_iInter₂.mp (hCG₁ hc) (x⁻¹ * (c * c₀)) hx
        change tr A (c₀ * (x⁻¹ * (c * c₀))⁻¹) (pt c) ∈ G₁ at this
        rw [hPT A] at this
        convert this using 2
        simp [mul_comm, mul_assoc, mul_left_comm]
      -- comparing `c` with `c₀`: `F` is stable under `y = c c₀⁻¹`
      intro c hc
      set y := c * c₀⁻¹
      have hRR : (ρ (c * c₀)) ⁻¹' F = (ρ (c₀ * c₀)) ⁻¹' F := (hRG₁ c hc).trans (hRG₁ c₀ hc₀).symm
      have hsub : ∀ (s s' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X),
          (ρ s) ⁻¹' F = (ρ s') ⁻¹' F → F ⊆ (tr A (s⁻¹ * s')) ⁻¹' F := by
        intro s s' hss'
        refine hJ1 A F _ hFcl (tr_closed _ F hFcl) fun d hd => ?_
        have hx : pt (s * d⁻¹) ∈ (ρ s) ⁻¹' F := by
          change ρ s (pt (s * d⁻¹)) ∈ F
          rw [hρpt]
          convert hd using 2
          simp [mul_comm, mul_assoc]
        rw [hss'] at hx
        change ρ s' (pt (s * d⁻¹)) ∈ F at hx
        rw [hρpt] at hx
        change tr A (s⁻¹ * s') (pt d) ∈ F
        rw [hPT A]
        convert hx using 2
        simp [mul_comm, mul_assoc, mul_left_comm]
      have h1 : F ⊆ (tr A y) ⁻¹' F := by
        have := hsub (c₀ * c₀) (c * c₀) hRR.symm
        convert this using 3
        simp [y, mul_comm, mul_assoc, mul_left_comm]
      have h2 : F ⊆ (tr A y⁻¹) ⁻¹' F := by
        have := hsub (c * c₀) (c₀ * c₀) hRR
        convert this using 3
        simp [y, mul_comm, mul_assoc, mul_left_comm]
      refine (Set.Subset.antisymm ?_ h1)
      intro a ha
      have := h2 ha
      change tr A y⁻¹ (tr A y a) ∈ F at this
      rwa [tr_tr_inv] at this
  -- every component is fixed, so the support is fixed
  have hsupp : ∀ c, pt c ∈ C → (tr A (c * c₀⁻¹)) ⁻¹' Z = Z := by
    intro c hc
    ext a
    constructor
    · intro ha
      obtain ⟨G, hG, haG⟩ := hJ4 A D _ ha
      have : a ∈ (tr A (c * c₀⁻¹)) ⁻¹' G := haG
      rw [key G hG c hc] at this
      exact hG.1.1 this
    · intro ha
      obtain ⟨G, hG, haG⟩ := hJ4 A D a ha
      have : a ∈ (tr A (c * c₀⁻¹)) ⁻¹' G := by rw [key G hG c hc]; exact haG
      exact hG.1.1 this
  -- the infinite family `c * c₀⁻¹` lies in the support stabilizer
  have himg : (fun c => c * c₀⁻¹) '' {c | pt c ∈ C} ⊆
      {x | (D.comap (tr A x)).support = D.support} := by
    rintro _ ⟨c, hc, rfl⟩
    change (D.comap (tr A (c * c₀⁻¹))).support = D.support
    rw [Scheme.IdealSheafData.support_comap]
    exact Closeds.ext (hsupp c hc)
  exact (hCinf.image (fun a _ b _ h => mul_right_cancel h)).mono himg

end ZInQ.Contrib.CloudR2NOS.Step2B2
