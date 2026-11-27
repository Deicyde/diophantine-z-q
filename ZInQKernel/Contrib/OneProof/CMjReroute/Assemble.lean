import ZInQKernel.Contrib.OneProof.CMjReroute.WitnessMatch
import ZInQKernel.Contrib.OneProof.CMjReroute.CMPoint
import ZInQKernel.Contrib.OneProof.CMjReroute.DictionaryProved
import ZInQKernel.Contrib.OneProof.CMjReroute.OrbitBound
import ZInQKernel.Contrib.OneProof.CMjReroute.RingClassKernel

/-!
# The class-number bound at a CM point of the CM branch's own witness

Let `(Y, Φ, π)` be a witness of the moduli clauses of the CM branch, `y` a `ℚ̄`-point of `Y` over a
rational value of `π`, with QM pair `P`, and let `End_𝒪(P)` contain a non-integer `φ`. Then there are an
imaginary quadratic field `K` and an embedding `q : K → B` such that

* `card Pic(q⁻¹(𝒪)) ≤ 324`, and
* `q⁻¹(𝒪) ≅ End_𝒪(P')` with central image, where `P'/ℂ` is the QM pair at a representative `(τ, u)`,
  `u ∈ 𝒪̂^×`, of `ιC^* y` under Deligne's uniformization, and `End(P.A)` maps injectively into
  `End(P'.A)` (base change to `ℂ`, then the QM isomorphism of the moduli clause), carrying `End_𝒪(P)`
  into `End_𝒪(P')`; by rigidity this map is a ring isomorphism.

The inputs are the leaves the CM branch already reads (`Y3FullThreeRepZ30`,
`DeligneCanonicalModelY3EveryPrint`, `Y3ToP1j`), proved results of the tree (the Hom–lattice
correspondence, Eichler's class number one, uniformization of `ℂ`-points), and the ring-class kernel
of `q⁻¹(𝒪)` with its two side conditions (`ideleClassArtinMap_ringClassField_eq_one`,
`comap_le_integralClosure`, `conductor_comap_ne_zero`).
-/

noncomputable section

namespace HDec.CMBranch.CMjReroute

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open _root_.LeafQM _root_.LeafQM.AV ShimuraCFT RayClassCFT
open _root_.ZInQ.LeafPush2 (CPts IsUniformization)
open NumberField IsDedekindDomain TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields

/-! ## Base change and QM isomorphisms keep a non-integral endomorphism non-integral -/

section Transfer

/-- Conjugation by an isomorphism is injective. -/
theorem conjEnd_injective {L : Type} [Field L] {A A' : PkgI3.AbVar L} (e : A.X ≅ A'.X)
    (h1 : IsMonHom e.hom) (h2 : IsMonHom e.inv) : Function.Injective (conjEnd e h1 h2) := by
  intro f g hfg
  have key : ∀ x : PkgI3.AbVar.End A', conjEnd e.symm h2 h1 (conjEnd e h1 h2 x) = x := fun x =>
    PkgI3.AbVar.Hom.ext' (by
      change e.inv ≫ (e.hom ≫ x.hom ≫ e.inv) ≫ e.hom = x.hom
      simp)
  rw [← key f, ← key g, hfg]

/-- The QM isomorphism as an isomorphism of the underlying group schemes. -/
def isoOfQM {L : Type} [Field L] {A A' : PkgI3.AbVar L} {q : QMStr A} {q' : QMStr A'}
    (g : QMIso q q') : A.X ≅ A'.X :=
  ⟨g.φ.hom, g.ψ.hom, g.left, g.right⟩

/-- **The transfer map** `End(P.A) → End(P'.A)` for `P/ℚ̄`, its base change `Q/ℂ` and a QM isomorphism
`Q ≅ P'`: an injective ring map carrying `ι_P` to `ι_{P'}`. -/
theorem exists_transfer {P : QML3 Qbar} {Q P' : QML3 ℂ}
    (hbc : IsBaseChangeOf (ιC : Qbar →+* ℂ) P Q) (g : QMIso Q.q P'.q) :
    ∃ T : PkgI3.AbVar.End P.A →+* PkgI3.AbVar.End P'.A, Function.Injective T ∧
      ∀ a : O, T (P.q.iota a) = P'.q.iota a := by
  let _ : Algebra Qbar ℂ := (ιC : Qbar →+* ℂ).toAlgebra
  obtain ⟨gp, hpb, hι, hη⟩ := hbc
  have hη0 := eta_compat (P := P) (Q := Q) (g := gp) hη
  let e := bcIso hpb
  have h1 := bcIso_isMonHom hpb hη0
  have h2 := bcIso_inv_isMonHom hpb hη0
  let R : PkgI3.AbVar.End P.A →+* PkgI3.AbVar.End Q.A :=
    (conjEnd e h1 h2).comp (HDec.G0ModField.KernelField.endBC P.A ℂ)
  have hR : ∀ a : O, R (P.q.iota a) = Q.q.iota a := fun a => by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ (HDec.G0ModField.KernelField.endBC P.A ℂ (P.q.iota a)).hom ≫ e.inv =
      (Q.q.iota a).hom
    rw [← Category.assoc, bc_iota hpb hι a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hRinj : Function.Injective R :=
    (conjEnd_injective e h1 h2).comp (HDec.G0ModField.KernelField.endBC_injective P.A ℂ)
  let f := (isoOfQM g).symm
  have k1 : IsMonHom f.hom := inferInstanceAs (IsMonHom g.ψ.hom)
  have k2 : IsMonHom f.inv := inferInstanceAs (IsMonHom g.φ.hom)
  let C : PkgI3.AbVar.End Q.A →+* PkgI3.AbVar.End P'.A := conjEnd f k1 k2
  have hC : ∀ a : O, C (Q.q.iota a) = P'.q.iota a := fun a => by
    apply PkgI3.AbVar.Hom.ext'
    change g.ψ.hom ≫ (Q.q.iota a).hom ≫ g.φ.hom = (P'.q.iota a).hom
    rw [g.equivariant a, ← Category.assoc, g.right, Category.id_comp]
  refine ⟨C.comp R, (conjEnd_injective f k1 k2).comp hRinj, fun a => ?_⟩
  rw [RingHom.comp_apply, hR, hC]

/-- An injective ring map keeps a non-integer non-integer. -/
theorem nonint_of_injective {A B : Type*} [Ring A] [Ring B] (T : A →+* B) (hT : Function.Injective T)
    {φ : A} (hne : ∀ n : ℤ, φ ≠ n) : ∀ n : ℤ, T φ ≠ n := fun n h =>
  hne n (hT (by rw [h, map_intCast]))

/-- Conjugation by an isomorphism is onto. -/
theorem conjEnd_surjective {L : Type} [Field L] {A A' : PkgI3.AbVar L} (e : A.X ≅ A'.X)
    (h1 : IsMonHom e.hom) (h2 : IsMonHom e.inv) : Function.Surjective (conjEnd e h1 h2) :=
  fun x => ⟨conjEnd e.symm h2 h1 x, PkgI3.AbVar.Hom.ext' (by
    change e.hom ≫ (e.inv ≫ x.hom ≫ e.hom) ≫ e.inv = x.hom
    simp)⟩

/-- **Rigidity**: over an algebraically closed field of characteristic zero, every endomorphism of a
base change is the base change of a unique endomorphism. -/
theorem endBC_surjective_of_rigidity (h11b : ZInQ.LeafPush2.T11b_Rigidity) {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {L : Type} [Field L] [Algebra k L] (A : PkgI3.AbVar k) :
    Function.Surjective (HDec.G0ModField.KernelField.endBC A L) := by
  intro x
  obtain ⟨φ, ⟨hφ, hFφ⟩, -⟩ := h11b k L A A x.hom inferInstance
  exact ⟨@PkgI3.AbVar.Hom.mk' k _ A A φ hφ, PkgI3.AbVar.Hom.ext' hFφ⟩

/-- **The transfer map is a ring isomorphism** (rigidity of homomorphisms from `ℚ̄` to `ℂ`). -/
theorem exists_transfer_equiv (h11b : ZInQ.LeafPush2.T11b_Rigidity) {P : QML3 Qbar}
    {Q P' : QML3 ℂ} (hbc : IsBaseChangeOf (ιC : Qbar →+* ℂ) P Q) (g : QMIso Q.q P'.q) :
    ∃ T : PkgI3.AbVar.End P.A ≃+* PkgI3.AbVar.End P'.A,
      ∀ a : O, T (P.q.iota a) = P'.q.iota a := by
  let _ : Algebra Qbar ℂ := (ιC : Qbar →+* ℂ).toAlgebra
  obtain ⟨gp, hpb, hι, hη⟩ := hbc
  have hη0 := eta_compat (P := P) (Q := Q) (g := gp) hη
  let e := bcIso hpb
  have h1 := bcIso_isMonHom hpb hη0
  have h2 := bcIso_inv_isMonHom hpb hη0
  let f := (isoOfQM g).symm
  have k1 : IsMonHom f.hom := inferInstanceAs (IsMonHom g.ψ.hom)
  have k2 : IsMonHom f.inv := inferInstanceAs (IsMonHom g.φ.hom)
  let R : PkgI3.AbVar.End P.A →+* PkgI3.AbVar.End P'.A :=
    (conjEnd f k1 k2).comp ((conjEnd e h1 h2).comp (HDec.G0ModField.KernelField.endBC P.A ℂ))
  have hbij : Function.Bijective R :=
    ⟨(conjEnd_injective f k1 k2).comp ((conjEnd_injective e h1 h2).comp
        (HDec.G0ModField.KernelField.endBC_injective P.A ℂ)),
      (conjEnd_surjective f k1 k2).comp ((conjEnd_surjective e h1 h2).comp
        (endBC_surjective_of_rigidity h11b P.A))⟩
  refine ⟨RingEquiv.ofBijective R hbij, fun a => ?_⟩
  have hR : conjEnd e h1 h2 (HDec.G0ModField.KernelField.endBC P.A ℂ (P.q.iota a)) =
      Q.q.iota a := by
    apply PkgI3.AbVar.Hom.ext'
    change e.hom ≫ (HDec.G0ModField.KernelField.endBC P.A ℂ (P.q.iota a)).hom ≫ e.inv =
      (Q.q.iota a).hom
    rw [← Category.assoc, bc_iota hpb hι a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  show conjEnd f k1 k2 (conjEnd e h1 h2 (HDec.G0ModField.KernelField.endBC P.A ℂ (P.q.iota a))) =
    P'.q.iota a
  rw [hR]
  apply PkgI3.AbVar.Hom.ext'
  change g.ψ.hom ≫ (Q.q.iota a).hom ≫ g.φ.hom = (P'.q.iota a).hom
  rw [g.equivariant a, ← Category.assoc, g.right, Category.id_comp]

/-- Rigidity, proved in the tree. -/
theorem t11b_proved : ZInQ.LeafPush2.T11b_Rigidity :=
  HDec.HSyn.t11b_of_exists5 HDec.HSyn.t11bExists_lf8

end Transfer

/-! ## A representative at units -/

/-- **Every `ℂ`-point is `Ψ(τ, u)` with `τ ∈ ℍ` and `u ∈ 𝒪̂^×`** (Eichler's class number one, proved). -/
theorem DeligneCore.exists_rep_units {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {Ψ : Y3Hodge.HPM → BAQˣ → (fieldPt ℂ ⟶ Y)} (hc : DeligneCore Y Φ Ψ) (y : fieldPt ℂ ⟶ Y) :
    ∃ (τ : UpperHalfPlane) (u : BAQˣ), u ∈ OhatU ∧ Ψ (Y3Hodge.toPM τ) u = y := by
  obtain ⟨z, g, rfl⟩ := hc.onto y
  obtain ⟨τ₀, g₀, h₀⟩ := Y3Hodge.exists_upper z g
  obtain ⟨gm, hgm, u, hu, hg⟩ := exists_pos_decomp classNumberOneB_proof g₀
  refine ⟨(iotaGL (binv gm) (nrd_binv_pos hgm).ne') • τ₀, u, hu, ?_⟩
  have h2 := dcRel_of_decomp hgm τ₀ hg
  have e1 : Ψ z g = Ψ (Y3Hodge.toPM τ₀) g₀ := (hc.fibre _ _ _ _).mpr h₀
  rw [e1]
  exact ((hc.fibre _ _ _ _).mpr ((Y3Hodge.dcRelPM_iff _ _ _ _).mpr h2)).symm

/-! ## The bound -/

/-- **The class-number bound at a CM point of the CM branch's witness.** -/
theorem exists_cmOrder_card_pic_le_324
    (hModel : _root_.Y3RouteA.Y3FullThreeRepZ30)
    (hDel : _root_.Y3Hodge.DeligneCanonicalModelY3EveryPrint) (hY3j : _root_.Y3P1j.Y3ToP1j)
    {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {π : ToP1 Y.left}
    (hR1 : R1fpProps Y Φ) (hR2 : R2fpProps Y Φ π) (r : ℚ) (y : fieldPt Qbar ⟶ Y)
    (hy : π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar r))
    (P : QML3 Qbar) (hP : Φ Qbar y = M3.mk P) {φ : PkgI3.AbVar.End P.A} (hφ : φ ∈ com P.q)
    (hne : ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End P.A)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsTotallyComplex K)
      (q : K →ₐ[ℚ] LeafQM.B) (P' : QML3 ℂ),
      Module.finrank ℚ K = 2 ∧
      Nat.card (CommRing.Pic (LeafQM.O.comap q.toRingHom)) ≤ 324 ∧
      (∃ T : PkgI3.AbVar.End P.A ≃+* PkgI3.AbVar.End P'.A,
        ∀ a : O, T (P.q.iota a) = P'.q.iota a) ∧
      ∃ e : ordR q ≃+* com P'.q, ∀ t, ((e t : com P'.q) : PkgI3.AbVar.End P'.A) ∈
        Subring.center (PkgI3.AbVar.End P'.A) := by
  -- Deligne's uniformization for this witness, and a representative at units
  obtain ⟨Ψ, hc⟩ := exists_deligneCore hModel hDel hR1
  obtain ⟨τ, u, hu, hτu⟩ := hc.exists_rep_units (fieldMap ιC ≫ y)
  -- the object at `(τ, u)` and the transfer from `P`
  obtain ⟨P', hP', hH⟩ := hc.units u hu τ
  obtain ⟨Φu, hU, hι⟩ := Y3Hodge.lattice_of_print _root_.uniformizationLeafAll_proof hH
  obtain ⟨Q, hQ, hbc⟩ := hR1.2.2.2.1 Qbar ℂ ιC y P hP
  rw [hτu, hQ] at hP'
  obtain ⟨f⟩ := Quotient.exact hP'
  let g : QMIso Q.q P'.q := ⟨f.φ, f.ψ, f.left, f.right, f.equivariant⟩
  obtain ⟨T, hTι⟩ := exists_transfer_equiv t11b_proved hbc g
  let _ : Algebra Qbar ℂ := (ιC : Qbar →+* ℂ).toAlgebra
  have hφ' : T φ ∈ com P'.q := com_map T.toRingHom hTι hφ
  have hne' := nonint_of_injective T.toRingHom T.injective hne
  -- the CM point at `τ`
  obtain ⟨K, _, _, _, hK, q, κ₀, hcm⟩ := exists_cmPoint homLatticeCorr_proved hU hι hφ' hne'
  -- the order and the orbit bound
  have hR := comap_le_integralClosure q
  have hf := conductor_comap_ne_zero q
  obtain ⟨S, hyS, hSfin, hS, hstab⟩ := matched_fibre hY3j hR1 hR2 r y hy
  have hpic := card_pic_le_324_of_stabC hc.fibre hc.recip S hSfin hS hstab y hyS K hK q κ₀ τ u hu
    hcm hτu hR hf (fun s hs => ideleClassArtinMap_ringClassField_eq_one hK q hR hf s hs)
  refine ⟨K, inferInstance, inferInstance, inferInstance, q, P', hK, hpic, ⟨T, hTι⟩,
    comEquivCM hK hU hι q κ₀ hcm, fun t => comEquivCM_mem_center hK hU hι q κ₀ hcm t⟩

end HDec.CMBranch.CMjReroute
