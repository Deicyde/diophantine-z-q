import ZInQKernel.Contrib.OneProof.Y3FullThreeZ30
import ZInQKernel.OneProof.H.TailZ21

/-! # y3-p1j: the map `Y₃ → P¹_j` (diophantine_zq.tex L420-440) and the moduli row's R2 re-sourced to it

Task y3-p1j (2026-11-17). Report: `docs/research/y3-p1j.md`; log: `scratch/y3-p1j/log.md`.

* §1-2 (proved, from the leaf `Y3RouteA.Y3FullThreeRepZ30` alone): the global generators of the manuscript's
  finite-adelic normalizer `N` act on the moduli problem over any base (`opP`, `rightMulP`, `twistP`: twists by
  `Aut 𝒪` and right multiplication of the three-marking by `𝒪^×`), hence, by the uniqueness in the universal
  property (Yoneda), by automorphisms of the integral model `𝒴/ℤ[1/30]` (`isoR`, `isoT`), with the composition
  laws of the operations, and `−1` acting trivially (`sigmaR_neg_one`; L430-434); summary `action_of_z30`.
* §3: the leaf `Y3ToP1j` (kind consequence, flag ELLIOT: the manuscript's L425-440 with the identification of the
  normalizer quotient cited at L420-422), the glue `ToP1DescendsAlongSurj` (textbook descent of a map to `P¹`
  along a surjection of curves), and the proofs `hauptmodulOfX6_of_y3ToP1j : Y3ToP1j → ToP1DescendsAlongSurj →
  PairsLift → HauptmodulOfX6` and `r1r2W_of_y3ToP1j` (the row `LeafAdopt.R1R2fpRepW` with R2 from `Y3ToP1j`
  instead of Baba–Granath on `X₆`).

No `sorry`; `#print axioms` of the three summary theorems: `propext, Classical.choice, Quot.sound`.
-/

set_option linter.all false

noncomputable section

namespace Y3P1j

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open Y3Fix SGRSplit HDec.VertWitness HDec.ModelGlue Y3Audit Y3RouteA
open scoped CategoryTheory.Obj

/-! ## 1. The generators of `N` acting on the moduli problem over a base

One combined operation `op α u`: `ι ↦ ι ∘ α`, `η ↦ η ∘ α ∘ (· u)`, for `α ∈ Aut 𝒪` and `u ∈ 𝒪^×`. (Elaborating the
two special cases directly makes the structure-instance elaborator loop; with `α` free it does not.) -/

section Ops

variable {S : Scheme.{0}}

/-- `op α u` on families. -/
def famOp (α : O ≃+* O) (u : Oˣ) (𝒜 : QMFamily S) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota (α a)
  iota_over a := 𝒜.iota_over _
  eta a := 𝒜.eta (α (a * u))
  eta_sec a := 𝒜.eta_sec _

theorem zm (u : Oˣ) : (0 : O) * (u : O) = 0 := MulZeroClass.zero_mul _

theorem op_zero (α : O ≃+* O) (u : Oˣ) : α ((0 : O) * (u : O)) = 0 := by rw [zm, map_zero]

/-- **The combined operation on objects of the printed moduli problem**, without the level clause. -/
def opNL (α : O ≃+* O) (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeNL S :=
  letI := 𝒜.grp
  { toQMFamily := famOp α u 𝒜.toQMFamily
    grp := 𝒜.grp
    geomConn := 𝒜.geomConn
    one_eq := 𝒜.one_eq.trans (congrArg 𝒜.eta (op_zero α u).symm)
    iota_hom := fun a => 𝒜.iota_hom (α a)
    iota_one := by
      change 𝒜.iota (α 1) = _
      rw [map_one]; exact 𝒜.iota_one
    iota_mul := fun a b => by
      change 𝒜.iota (α (a * b)) = 𝒜.iota (α b) ≫ 𝒜.iota (α a)
      rw [map_mul]; exact 𝒜.iota_mul _ _
    iota_add := fun a b => by
      change Over.homMk (𝒜.iota (α (a + b))) (𝒜.iota_over _) =
        Over.homMk (𝒜.iota (α a)) (𝒜.iota_over _) * Over.homMk (𝒜.iota (α b)) (𝒜.iota_over _)
      rw [map_add]; exact 𝒜.iota_add _ _
    eta_add := fun a b => by
      change secF 𝒜.toQMFamily (α ((a + b) * u)) = secF 𝒜.toQMFamily (α (a * u)) * secF 𝒜.toQMFamily (α (b * u))
      rw [add_mul, map_add]; exact 𝒜.eta_add _ _
    eta_linear := fun a b => by
      change 𝒜.eta (α (a * b * u)) = 𝒜.eta (α (b * u)) ≫ 𝒜.iota (α a)
      rw [_root_.mul_assoc, map_mul]; exact 𝒜.eta_linear _ _
    eta_three := fun b => by
      change 𝒜.eta (α (3 * b * u)) = 𝒜.eta (α (0 * u))
      rw [op_zero, _root_.mul_assoc, map_mul, map_ofNat]; exact 𝒜.eta_three _ }

theorem level_opNL (α : O ≃+* O) (u : Oˣ) (𝒜 : QMAbSchemeP S) : LevelPrint (opNL α u 𝒜) := by
  intro k _ _ s
  obtain ⟨h1, h2⟩ := 𝒜.level k s
  refine ⟨fun a => ?_, fun x hx => ?_⟩
  · change s ≫ 𝒜.eta (α (a * u)) = s ≫ 𝒜.eta (α (0 * u)) ↔ _
    rw [op_zero, h1]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨α.symm b * ↑u⁻¹, ?_⟩
      have : a * ↑u = 3 * α.symm b := by
        apply α.injective; rw [hb, map_mul, map_ofNat, RingEquiv.apply_symm_apply]
      rw [← _root_.mul_assoc, ← this, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    · rintro ⟨b, rfl⟩
      exact ⟨α (b * u), by rw [_root_.mul_assoc, map_mul, map_ofNat]⟩
  · obtain ⟨a, ha⟩ := h2 x hx
    refine ⟨α.symm a * ↑u⁻¹, ?_⟩
    change x = cpt s ≫ (Over.pullback s).map (secF 𝒜.toQMFamily (α (α.symm a * ↑u⁻¹ * ↑u)))
    rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one, RingEquiv.apply_symm_apply]; exact ha

/-- **The combined operation on objects of the printed moduli problem.** -/
def opP (α : O ≃+* O) (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeP S :=
  { toQMAbSchemeNL := opNL α u 𝒜, level := level_opNL α u 𝒜 }

/-- **`rightMul u`** (`u ∈ 𝒪^×`): the action of `K₀` through `𝒪^× → (𝒪/3𝒪)^×` on the three-marking. -/
def rightMulP (u : Oˣ) (𝒜 : QMAbSchemeP S) : QMAbSchemeP S := opP (RingEquiv.refl O) u 𝒜

/-- **`twist α`** (`α ∈ Aut 𝒪`; by Skolem–Noether `α = Ad(b)` for `b` in the normalizer of `𝒪` in `B^×`, the
global part of `N`). -/
def twistP (α : O ≃+* O) (𝒜 : QMAbSchemeP S) : QMAbSchemeP S := opP α 1 𝒜

theorem qmFamFibre_op {T : Scheme.{0}} (α : O ≃+* O) (u : Oˣ) {𝒜 : QMFamily T} {g : S ⟶ T}
    {𝒜' : QMFamily S} (h : QMFamFibre 𝒜 g 𝒜') : QMFamFibre (famOp α u 𝒜) g (famOp α u 𝒜') := by
  obtain ⟨h, hpb, hi, he⟩ := h
  exact ⟨h, hpb, fun a => hi (α a), fun a => he (α (a * u))⟩

theorem qmFamFibreP_op {T : Scheme.{0}} (α : O ≃+* O) (u : Oˣ) {𝒜 : QMAbSchemeP T} {g : S ⟶ T}
    {𝒜' : QMAbSchemeP S} (h : QMFamFibre 𝒜.toQMFamily g 𝒜'.toQMFamily) :
    QMFamFibre (opP α u 𝒜).toQMFamily g (opP α u 𝒜').toQMFamily :=
  qmFamFibre_op α u h

/-- `QMFamFibre` only sees `F`, `ι`, `η`: transport along pointwise equalities. -/
theorem qmFamFibre_congr {T : Scheme.{0}} {𝒜 : QMFamily T} {g : S ⟶ T} {𝒜' 𝒜'' : QMFamily S}
    (hF : 𝒜'.F = 𝒜''.F) (hi : ∀ a, HEq (𝒜'.iota a) (𝒜''.iota a)) (he : ∀ a, HEq (𝒜'.eta a) (𝒜''.eta a))
    (h : QMFamFibre 𝒜 g 𝒜') : QMFamFibre 𝒜 g 𝒜'' := by
  obtain ⟨F', p', s', i', o', e', es'⟩ := 𝒜'
  obtain ⟨F'', p'', s'', i'', o'', e'', es''⟩ := 𝒜''
  cases hF
  have hi' : i' = i'' := funext fun a => eq_of_heq (hi a)
  have he' : e' = e'' := funext fun a => eq_of_heq (he a)
  subst hi' he'
  exact h

theorem qmFamFibre_id (𝒜 : QMFamily S) : QMFamFibre 𝒜 (𝟙 S) 𝒜 :=
  ⟨𝟙 _, IsPullback.of_horiz_isIso ⟨by simp⟩, fun a => by simp, fun a => by simp⟩

end Ops

/-! ## 2. Yoneda: the operations act on the representing scheme of `Y3FullThreeRepZ30` -/

section Yoneda

variable {𝒴 : Over (Spec (CommRingCat.of Z30))} {𝒜 : QMAbSchemeP 𝒴.left}

/-- The representing scheme is locally noetherian (smooth over the noetherian `ℤ[1/30]`). -/
theorem isLocallyNoetherian_of_smooth (h : SmoothOfRelativeDimension 1 𝒴.hom) : IsLocallyNoetherian 𝒴.left := by
  haveI := h
  exact LocallyOfFiniteType.isLocallyNoetherian 𝒴.hom

/-- The universal property, packaged. -/
def IsUniv (𝒴 : Over (Spec (CommRingCat.of Z30))) (𝒜 : QMAbSchemeP 𝒴.left) : Prop :=
  ∀ (S : Over (Spec (CommRingCat.of Z30))), IsLocallyNoetherian S.left →
    ∀ 𝒜' : QMAbSchemeP S.left, ∃! g : S ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily g.left 𝒜'.toQMFamily

/-- **The endomorphism induced by an operation `T` on the functor** (Yoneda): the unique `σ : 𝒴 → 𝒴` over
`ℤ[1/30]` with `T 𝒜 ≅ σ^* 𝒜`. -/
theorem exists_induced (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (𝒜' : QMAbSchemeP 𝒴.left) :
    ∃! σ : 𝒴 ⟶ 𝒴, QMFamFibre 𝒜.toQMFamily σ.left 𝒜'.toQMFamily :=
  hU 𝒴 hN 𝒜'

/-- Uniqueness, as an equation. -/
theorem induced_eq (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) {𝒜' : QMAbSchemeP 𝒴.left}
    {σ τ : 𝒴 ⟶ 𝒴} (hσ : QMFamFibre 𝒜.toQMFamily σ.left 𝒜'.toQMFamily)
    (hτ : QMFamFibre 𝒜.toQMFamily τ.left 𝒜'.toQMFamily) : σ = τ :=
  (hU 𝒴 hN 𝒜').unique hσ hτ

/-- The induced map of `rightMul u`. -/
def sigmaR (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (u : Oˣ) : 𝒴 ⟶ 𝒴 :=
  (exists_induced hU hN (rightMulP u 𝒜)).exists.choose

theorem sigmaR_spec (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (u : Oˣ) :
    QMFamFibre 𝒜.toQMFamily (sigmaR hU hN u).left (rightMulP u 𝒜).toQMFamily :=
  (exists_induced hU hN (rightMulP u 𝒜)).exists.choose_spec

/-- The induced map of `twist α`. -/
def sigmaT (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (α : O ≃+* O) : 𝒴 ⟶ 𝒴 :=
  (exists_induced hU hN (twistP α 𝒜)).exists.choose

theorem sigmaT_spec (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (α : O ≃+* O) :
    QMFamFibre 𝒜.toQMFamily (sigmaT hU hN α).left (twistP α 𝒜).toQMFamily :=
  (exists_induced hU hN (twistP α 𝒜)).exists.choose_spec

/-- `rightMul 1` induces the identity. -/
theorem sigmaR_one (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) : sigmaR hU hN 1 = 𝟙 𝒴 := by
  refine induced_eq hU hN (sigmaR_spec hU hN 1) ?_
  refine qmFamFibre_congr (𝒜' := 𝒜.toQMFamily) rfl (fun a => HEq.rfl) (fun a => heq_of_eq ?_) (qmFamFibre_id 𝒜.toQMFamily)
  change 𝒜.eta a = 𝒜.eta (RingEquiv.refl O (a * ((1 : Oˣ) : O)))
  rw [Units.val_one, _root_.mul_one]; rfl

/-- **Composition law of `rightMul`**: `σ_u ≫ σ_v = σ_{v u}`. -/
theorem sigmaR_comp (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (u v : Oˣ) :
    sigmaR hU hN u ≫ sigmaR hU hN v = sigmaR hU hN (v * u) := by
  refine induced_eq hU hN ?_ (sigmaR_spec hU hN (v * u))
  have h := qmFamFibre_trans (sigmaR_spec hU hN v) (qmFamFibreP_op (RingEquiv.refl O) v (sigmaR_spec hU hN u))
  refine qmFamFibre_congr (𝒜' := (opP (RingEquiv.refl O) v (rightMulP u 𝒜)).toQMFamily) rfl (fun a => HEq.rfl) (fun a => heq_of_eq ?_) h
  change 𝒜.eta (RingEquiv.refl O (RingEquiv.refl O (a * ↑v) * ↑u)) = 𝒜.eta (RingEquiv.refl O (a * ↑(v * u)))
  rw [Units.val_mul, ← _root_.mul_assoc]; rfl

/-- **`rightMul u` acts by automorphisms** of the integral model. -/
def isoR (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (u : Oˣ) : 𝒴 ≅ 𝒴 where
  hom := sigmaR hU hN u
  inv := sigmaR hU hN u⁻¹
  hom_inv_id := by rw [sigmaR_comp, inv_mul_cancel, sigmaR_one]
  inv_hom_id := by rw [sigmaR_comp, mul_inv_cancel, sigmaR_one]

/-- `twist (refl)` induces the identity. -/
theorem sigmaT_refl (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) :
    sigmaT hU hN (RingEquiv.refl O) = 𝟙 𝒴 := by
  refine induced_eq hU hN (sigmaT_spec hU hN _) ?_
  refine qmFamFibre_congr (𝒜' := 𝒜.toQMFamily) rfl (fun a => HEq.rfl) (fun a => heq_of_eq ?_) (qmFamFibre_id 𝒜.toQMFamily)
  change 𝒜.eta a = 𝒜.eta (RingEquiv.refl O (a * ((1 : Oˣ) : O)))
  rw [Units.val_one, _root_.mul_one]; rfl

/-- **Composition law of `twist`**: `σ_α ≫ σ_β = σ_{β.trans α}` (`(β.trans α) a = α (β a)`). -/
theorem sigmaT_comp (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (α β : O ≃+* O) :
    sigmaT hU hN α ≫ sigmaT hU hN β = sigmaT hU hN (β.trans α) := by
  refine induced_eq hU hN ?_ (sigmaT_spec hU hN (β.trans α))
  have h := qmFamFibre_trans (sigmaT_spec hU hN β) (qmFamFibreP_op β 1 (sigmaT_spec hU hN α))
  refine qmFamFibre_congr (𝒜' := (opP β 1 (twistP α 𝒜)).toQMFamily) rfl (fun a => HEq.rfl) (fun a => heq_of_eq ?_) h
  change 𝒜.eta (α (β (a * ((1 : Oˣ) : O)) * ((1 : Oˣ) : O))) = 𝒜.eta ((β.trans α) (a * ((1 : Oˣ) : O)))
  rw [Units.val_one, _root_.mul_one, _root_.mul_one]; rfl

/-- **`twist α` acts by automorphisms** of the integral model. -/
def isoT (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) (α : O ≃+* O) : 𝒴 ≅ 𝒴 where
  hom := sigmaT hU hN α
  inv := sigmaT hU hN α.symm
  hom_inv_id := by
    rw [sigmaT_comp]
    rw [RingEquiv.symm_trans_self, sigmaT_refl]
  inv_hom_id := by
    rw [sigmaT_comp]
    rw [RingEquiv.self_trans_symm, sigmaT_refl]

/-- `ι(-1)` is an automorphism of `A` over the base. -/
theorem iota_neg_one_sq (𝒜 : QMAbSchemeP 𝒴.left) : 𝒜.iota (-1) ≫ 𝒜.iota (-1) = 𝟙 _ := by
  rw [← 𝒜.iota_mul, _root_.neg_one_mul, neg_neg, 𝒜.iota_one]

/-- **The central element `−1` acts trivially** (manuscript L430-434 for the central idele `−1`, whose image
in `(𝒪/3𝒪)^×` is the only central unit not in `K₃`): `(A, ι, η(·(−1))) ≅ (A, ι, η)` through `ι(−1) = [−1]`, so
the induced map is the identity. -/
theorem sigmaR_neg_one (hU : IsUniv 𝒴 𝒜) (hN : IsLocallyNoetherian 𝒴.left) : sigmaR hU hN (-1) = 𝟙 𝒴 := by
  refine induced_eq hU hN (sigmaR_spec hU hN (-1)) ?_
  haveI : IsIso (𝒜.iota (-1)) := ⟨⟨𝒜.iota (-1), iota_neg_one_sq 𝒜, iota_neg_one_sq 𝒜⟩⟩
  have hpb : IsPullback (𝒜.iota (-1)) 𝒜.F.hom 𝒜.F.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [𝒜.iota_over, Category.comp_id]⟩
  refine ⟨𝒜.iota (-1), hpb, fun a => ?_, fun a => ?_⟩
  · change 𝒜.iota a ≫ 𝒜.iota (-1) = 𝒜.iota (-1) ≫ 𝒜.iota a
    rw [← 𝒜.iota_mul, ← 𝒜.iota_mul, _root_.neg_one_mul, _root_.mul_neg_one]
  · change 𝒜.eta (RingEquiv.refl O (a * ↑(-1 : Oˣ))) ≫ 𝒜.iota (-1) = 𝟙 _ ≫ 𝒜.eta a
    rw [RingEquiv.refl_apply, ← 𝒜.eta_linear, Units.val_neg, Units.val_one, _root_.mul_neg_one,
      _root_.neg_one_mul, neg_neg, Category.id_comp]

/-- **The Yoneda action on the integral model of `Y₃`**, from the leaf `Y3FullThreeRepZ30` alone: there are a
proper smooth curve `𝒴/ℤ[1/30]` with a universal object and automorphisms `isoR u` (`u ∈ 𝒪^×`) and `isoT α`
(`α ∈ Aut 𝒪`) of `𝒴` over `ℤ[1/30]`, each characterized by `σ^*𝒜 ≅ T 𝒜`, with the composition laws of the
operations, and `−1 ∈ 𝒪^×` acting trivially. -/
theorem action_of_z30 (h : Y3FullThreeRepZ30) :
    ∃ (𝒴 : Over (Spec (CommRingCat.of Z30))) (𝒜 : QMAbSchemeP 𝒴.left)
      (σR : Oˣ → (𝒴 ≅ 𝒴)) (σT : (O ≃+* O) → (𝒴 ≅ 𝒴)),
      IsProper 𝒴.hom ∧ SmoothOfRelativeDimension 1 𝒴.hom ∧ IsUniv 𝒴 𝒜 ∧
      (∀ u, QMFamFibre 𝒜.toQMFamily (σR u).hom.left (rightMulP u 𝒜).toQMFamily) ∧
      (∀ α, QMFamFibre 𝒜.toQMFamily (σT α).hom.left (twistP α 𝒜).toQMFamily) ∧
      (∀ u v, (σR u).hom ≫ (σR v).hom = (σR (v * u)).hom) ∧
      (∀ α β, (σT α).hom ≫ (σT β).hom = (σT (β.trans α)).hom) ∧
      (σR (-1)).hom = 𝟙 𝒴 := by
  obtain ⟨𝒴, 𝒜, hP, hS, hU⟩ := h
  have hN := isLocallyNoetherian_of_smooth hS
  exact ⟨𝒴, 𝒜, isoR hU hN, isoT hU hN, hP, hS, hU, sigmaR_spec hU hN, sigmaT_spec hU hN,
    sigmaR_comp hU hN, sigmaT_comp hU hN, sigmaR_neg_one hU hN⟩

end Yoneda

/-! ## 3. The leaf `Y3ToP1j` (diophantine_zq.tex L420-440) -/

section Leaf

open HDec.QMSplit.Moduli

/-- **The clauses of `Y3ToP1j` at one fine witness `(Y, Φ)` and one `π : Y → P¹`** (the quotient of `Y₃` by
`N/(𝔸_f^× K₃)`, on `ℚ̄`-points, in the coordinate `j`):
* (quotient) two `ℚ̄`-points have the same `π`-value iff their underlying QM pairs are `Aut(𝒪)`-twists of each
  other: the `N`-orbits, since `N = N_{B^×}(𝒪)·𝔸_f^×·K₀` acts through `Aut 𝒪 = N_{B^×}(𝒪)/ℚ^×` (twists) and
  through `K₀/K₃ = (𝒪/3𝒪)^×` on the three-marking, and the three-markings of one pair form one
  `(𝒪/3𝒪)^×`-orbit;
* (branch values, L421-422) the CM points by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]` are exactly the fibres over `0`, `∞`,
  `−16/27`;
* (quotient map) `π` is onto `P¹(ℚ̄)`;
* (degree, L437-440) every fibre on `ℚ̄`-points is finite with at most `324` points (a consequence of
  `deg(Y₃ → P¹_j) ≤ 4|(𝒪/3𝒪)^×| ≤ 324`). -/
def Y3ToP1jAt (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) : Prop :=
  (∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar), Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
      (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
          ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
      (HasCM4 P.q ↔ π.val (K := Qbar) y.left = OnePoint.some 0) ∧
      (HasCM3 P.q ↔ π.val (K := Qbar) y.left = OnePoint.infty) ∧
      (HasCM24 P.q ↔ π.val (K := Qbar) y.left = OnePoint.some (-16 / 27))) ∧
  (∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = t) ∧
  (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite ∧
      {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.ncard ≤ 324)

/-- **LEAF `Y3ToP1j` (kind consequence; flag ELLIOT: the manuscript's own claim, diophantine_zq.tex L425-440,
with the identification of the normalizer quotient cited at L420-422 to Baba–Granath and Lin–Yang).**

Manuscript (Glazer, 11/5 manuscript, proof of Theorem 4.1; read for this leaf):
* L411-420: `B = (2, −3)`, `𝒪 = ℤ[i, (1 + j)/2]`, `μ = 2j + ij`, the principal-polarization datum with Rosati
  involution `a ↦ μ⁻¹ā μ`;
* L420-422: "the normalizer quotient is `P¹_j`, with branch values `0, ∞, −16/27` and indices `4, 6, 2`"
  [Baba–Granath; Lin–Yang];
* L423-424: `K₀ = 𝒪̂^×`, `K₃ = ker(K₀ → (𝒪/3𝒪)^×)`;
* L425-429: `N` the finite-adelic normalizer of `𝒪̂`; it normalizes `K₃`; `|N/(𝔸_f^× K₀)| = 4`;
* L430-434: central finite ideles act trivially on the level-three curve;
* L434-440: the whole `Y₃`, with all its determinant components, admits the action of `N/(𝔸_f^× K₃)` with
  quotient `P¹_j`, and `deg(Y₃ → P¹_j) ≤ 4|(𝒪/3𝒪)^×| ≤ 4·81 = 324`.

Lean form: for every fine witness `(Y, Φ)` of the level-3 moduli problem (`R1fpProps`, the kernel's `Y₃`), some
`π : Y → P¹` satisfies `Y3ToP1jAt`. The action itself is not in the leaf: its global generators (twists by
`Aut 𝒪` and `rightMul` by `𝒪^×`) are automorphisms of `Y` by the proved glue `heckeOfFine_proof`
(`R1heckeProps`), and of the integral model by `action_of_z30` (this file, from `Y3FullThreeRepZ30`), where
`−1` acts trivially (`sigmaR_neg_one`, the case of L430-434 that is not already in `K₃`). The CM clauses are
the branch-value statement of L421-422 in the form of the kernel's Baba–Granath reading (each of
`CM(−4)`, `CM(−3)`, `CM(−24)` is the fibre over its branch value; Baba–Granath §3.1, UNVERIFIED). The degree
clause is a consequence of the degree bound (a finite morphism of degree `d` has fibres of at most `d` points).
Not printed form: no print states this for the level-3 curve; the manuscript derives it from the adelic
computation at L425-436 plus the cited identification of the normalizer quotient (L420-422). -/
def Y3ToP1j : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → ∃ π : ToP1 Y.left, Y3ToP1jAt Y Φ π

/-- **GLUE `ToP1DescendsAlongSurj` (descent of a map to `P¹` along a surjection of curves).** For proper smooth
curves `Y`, `X` over `ℚ`, `f : Y → X` onto `X(ℚ̄)` and `π : Y → P¹` constant on the `ℚ̄`-fibres of `f`, there
is `π₆ : X → P¹` with `π₆ ∘ f = π` on `ℚ̄`-points. Textbook: it is the kernel's proved `FactorThroughSurj`
(`factorThroughSurj_proof`, TailZ20) with `X' = P¹_ℚ`, once `P¹_ℚ` is an object of `Over (Spec ℚ)`, proper and
smooth of relative dimension 1, with the chart dictionary `ToP1 X ≃ (X ⟶ P¹_ℚ)` (Hartshorne II.7.1; the
kernel states maps to `P¹` by charts because Mathlib 4.35 has no `P¹` with its point bijection). -/
def ToP1DescendsAlongSurj : Prop :=
  ∀ (Y X : Over (Spec (CommRingCat.of ℚ))), IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    IsProper X.hom → SmoothOfRelativeDimension 1 X.hom → ∀ (f : Y ⟶ X) (π : ToP1 Y.left),
    (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ f = x) →
    (∀ y y' : fieldPt Qbar ⟶ Y, y ≫ f = y' ≫ f → π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left) →
      ∃ π₆ : ToP1 X.left, ∀ y : fieldPt Qbar ⟶ Y, π₆.val (K := Qbar) (y ≫ f).left = π.val (K := Qbar) y.left

/-- Twisting both sides of an isomorphism of QM pairs. -/
def qmIsoTwist {K : Type} [Field K] {A A' : PkgI3.AbVar K} {q : QMStr A} {q' : QMStr A'} (f : QMIso q q')
    (α : O ≃+* O) : QMIso (q.twist α) (q'.twist α) where
  φ := f.φ
  ψ := f.ψ
  left := f.left
  right := f.right
  equivariant a := f.equivariant (α a)

/-- The forgetful map is onto `X(ℚ̄)` on a coarse witness, from `PairsLift`. -/
theorem lift_of_pairsLift {Y X : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X} (h6 : X6Props Y Φ X Ψ fY)
    (hL : PairsLift) (x : fieldPt Qbar ⟶ X) : ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x := by
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Ψ x)
  obtain ⟨P, hP⟩ := hL Q
  refine ⟨(Φ Qbar).symm (M3.mk P), Ψ.injective ?_⟩
  rw [h6.2.2.2.2.2 _ P (Equiv.apply_symm_apply _ _), hP, hQ]

/-- The class of the underlying pair of a point of `Y` is the class of its image in `X`. -/
theorem forget_rel {Y X : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)} {fY : Y ⟶ X} (h6 : X6Props Y Φ X Ψ fY)
    {y : fieldPt Qbar ⟶ Y} {Py : QML3 Qbar} (hy : Φ Qbar y = M3.mk Py) {P : QMPair Qbar}
    (hP : Ψ (y ≫ fY) = Quotient.mk _ P) : Nonempty (QMIso Py.q P.q) := by
  have := (h6.2.2.2.2.2 y Py hy).symm.trans hP
  exact Quotient.exact this

/-- **R2 on `X₆` (the kernel's `HauptmodulOfX6`) from `Y3ToP1j`**, the descent glue and `PairsLift`: descend
`π` along the forgetful map `Y₃ → X₆` (constant on its fibres by the quotient clause with `α = id`) and
transport the clauses along `QMIso`s. -/
theorem hauptmodulOfX6_of_y3ToP1j (hY : Y3ToP1j) (hD : ToP1DescendsAlongSurj) (hL : PairsLift) :
    HauptmodulOfX6 := by
  intro Y Φ X Ψ fY h1 h6
  obtain ⟨π, hcl, hsurj, -⟩ := hY Y Φ h1
  have rep : ∀ y : fieldPt Qbar ⟶ Y, ∃ P : QML3 Qbar, Φ Qbar y = M3.mk P := fun y => by
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ Qbar y)
    exact ⟨P, hP.symm⟩
  have hconst : ∀ y y' : fieldPt Qbar ⟶ Y, y ≫ fY = y' ≫ fY →
      π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left := by
    intro y y' hyy
    obtain ⟨P, hP⟩ := rep y
    obtain ⟨Q, hQ⟩ := rep y'
    obtain ⟨e⟩ := forget_rel h6 hP (P := Q.forget) (by rw [hyy]; exact h6.2.2.2.2.2 y' Q hQ)
    exact ((hcl y y' P Q hP hQ).1).2 ⟨RingEquiv.refl O, ⟨e⟩⟩
  obtain ⟨π₆, hπ₆⟩ := hD Y X h1.1 h1.2.1 h6.1 h6.2.1 fY π (lift_of_pairsLift h6 hL) hconst
  refine ⟨π₆, fun x x' P Q hP hQ => ?_, fun t => ?_⟩
  · obtain ⟨y, rfl⟩ := lift_of_pairsLift h6 hL x
    obtain ⟨y', rfl⟩ := lift_of_pairsLift h6 hL x'
    obtain ⟨Py, hPy⟩ := rep y
    obtain ⟨Qy, hQy⟩ := rep y'
    obtain ⟨e⟩ := forget_rel h6 hPy hP
    obtain ⟨e'⟩ := forget_rel h6 hQy hQ
    obtain ⟨hf, h4, h3, h24⟩ := hcl y y' Py Qy hPy hQy
    rw [hπ₆, hπ₆]
    refine ⟨hf.trans ⟨fun ⟨α, ⟨g⟩⟩ => ⟨α, ⟨((qmIsoTwist e.symm α).trans g).trans e'⟩⟩,
      fun ⟨α, ⟨g⟩⟩ => ⟨α, ⟨((qmIsoTwist e α).trans g).trans e'.symm⟩⟩⟩, ?_, ?_, ?_⟩
    · exact ⟨fun h => h4.1 (HasCM4.of_iso e.symm h), fun h => HasCM4.of_iso e (h4.2 h)⟩
    · exact ⟨fun h => h3.1 (HasCM3.of_iso e.symm h), fun h => HasCM3.of_iso e (h3.2 h)⟩
    · exact ⟨fun h => h24.1 (HasCM24.of_iso e.symm h), fun h => HasCM24.of_iso e (h24.2 h)⟩
  · obtain ⟨y, hy⟩ := hsurj t
    exact ⟨y ≫ fY, (hπ₆ y).trans hy⟩

/-- **The row `r1r2` (weak form) with R2 re-sourced to `Y3ToP1j`**: the kernel's `r1r2fpRep_of'W` (TailZ21)
with `HauptmodulOfX6` from `hauptmodulOfX6_of_y3ToP1j` instead of Baba–Granath on `X₆`. `PairsLift` is supplied
from T5 (`pairsLift_of_t5`), itself from the proved `mumfordTorsionAlgClosed_proof`. The other inputs are
those of `r1r2fpRep_of'W`: the canonical model `CanonicalModelY3`, the coarse space `CoarseX6OfFineW`,
reciprocity `ReciprocityOfFine`, and González–Rotger `ResidueOfX6`. -/
theorem r1r2W_of_y3ToP1j (hE : CanonicalModelY3) (hX : CoarseX6OfFineW) (hY : Y3ToP1j)
    (hD : ToP1DescendsAlongSurj) (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : HDec.LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of'W hE hX (hauptmodulOfX6_of_y3ToP1j hY hD
    (pairsLift_of_t5 (AvSplit.torsionStructure_of_mumford
      ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof))) hR h5

/-- **Consistency: the row's `X₆` data give every clause of `Y3ToP1jAt` except the degree bound**, for
`π = π₆ ∘ fY`. So, against the leaves the chain already uses (Baba–Granath on `X₆` through the row), the only new
content of `Y3ToP1j` is the fibre bound `≤ 324` (L437-440) and the passage from one witness to every witness. -/
theorem y3ToP1jAt_noDeg_of_row (h : HDec.LeafAdopt.R1R2fpRepW) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left), R1fpProps Y Φ ∧
      (∀ (y y' : fieldPt Qbar ⟶ Y) (P Q : QML3 Qbar), Φ Qbar y = M3.mk P → Φ Qbar y' = M3.mk Q →
        (π.val (K := Qbar) y.left = π.val (K := Qbar) y'.left ↔
            ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q)) ∧
        (HasCM4 P.q ↔ π.val (K := Qbar) y.left = OnePoint.some 0) ∧
        (HasCM3 P.q ↔ π.val (K := Qbar) y.left = OnePoint.infty) ∧
        (HasCM24 P.q ↔ π.val (K := Qbar) y.left = OnePoint.some (-16 / 27))) ∧
      (∀ t : OnePoint Qbar, ∃ y : fieldPt Qbar ⟶ Y, π.val (K := Qbar) y.left = t) := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, h6, h2, -, ⟨hs6, hsY⟩, -⟩ := h
  have hv : ∀ y : fieldPt Qbar ⟶ Y, (π₆.comp fY.left).val (K := Qbar) y.left = π₆.val (K := Qbar) (y ≫ fY).left :=
    fun y => ToP1.val_comp_right (K := Qbar) π₆ fY.left y.left
  refine ⟨Y, Φ, π₆.comp fY.left, h1, fun y y' P Q hP hQ => ?_, fun t => ?_⟩
  · rw [hv, hv]
    exact h2 (y ≫ fY) (y' ≫ fY) P.forget Q.forget (h6.2.2.2.2.2 y P hP) (h6.2.2.2.2.2 y' Q hQ)
  · obtain ⟨x, hx⟩ := hs6 t
    obtain ⟨y, rfl⟩ := hsY x
    exact ⟨y, (hv y).trans hx⟩

end Leaf

end Y3P1j
