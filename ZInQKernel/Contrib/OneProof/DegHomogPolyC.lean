import ZInQKernel.Contrib.OneProof.CharPolyLattice
import ZInQKernel.Contrib.OneProof.DegEqDetTate

/-!
# degpoly-proof: deg-det's leaf `DegHomogPoly` over every algebraically closed field that embeds into `ℂ`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task degpoly-proof, 2026-11-16);
report `docs/research/degpoly-proof.md`, scratch `scratch/degpoly-proof/`.

`DegDet.DegHomogPoly` (deg-det, `DegEqDetTate/Reduction.lean`): `deg = CharPolyEll.degEnd` is a
homogeneous polynomial function of degree `2g` on `End(A)` (Mumford §19). This file proves it over
every algebraically closed `k` with a ring homomorphism `σ : k → ℂ` (`degHomogPolyC`), from the
bundle's open fields `uniformizationLeafAll` and `mumfordTorsionAlgClosed`: with `Φ : ℂ^g → A(ℂ)` the
uniformization, `Λ = ker Φ` and `U(ψ) = M_ψ|_Λ` the lattice representation (an injective ring
homomorphism `End(A) → End_ℤ(Λ)`, `latRep`),

  `deg ψ = det_ℤ(U(ψ))` for every `ψ ∈ End(A)` (`degEnd_eq_det`),

so `x ↦ deg(∑ xᵢ eᵢ) = det(∑ xᵢ U(eᵢ))` is a homogeneous polynomial of degree `rank Λ = 2g`. The steps:

* (A) for a finite `ψ` and every field `L ⊇ k`, `ker ψ(L)` is in bijection with the fibre
  `ψ⁻¹(e₀)` (`card_ker_eq`): kernel points are determined by their (closed) image point, through
  Mathlib's `residueFieldIsoBase`;
* (B) in characteristic `0`, `deg ψ ≤ #ψ⁻¹(e₀)` (`degEnd_le_card_fibre`): the
  `ψ^*K(A)`-embeddings of `K(A)` into `\overline{K(A)}` give points with equal `ψ`-image, so
  translates of one another by kernel points; there are `deg ψ` of them (separability);
  with deg-det's `#ker ψ ∣ deg ψ` (`KerDvd.kerDvdDeg`) and `deg ψ ≠ 0` for isogenies
  (`degEnd_ne_zero`: quasi-finiteness at the generic point), `deg ψ = #ψ⁻¹(e₀)`;
* (C) `#ker ψ(ℂ) = [Λ : M_ψ Λ] = det_ℤ(U ψ) > 0` (`card_ker_eq_det`; `det_ℤ = det_ℝ = |det_ℂ|²`);
* (D) `det_ℤ(U ψ) ≠ 0 ⇒ ψ` is an isogeny (`isIsogeny_of_det_ne_zero`: Cayley–Hamilton through the
  injective `latRep`, `ψ q(ψ) = q(ψ) ψ = [n]`, and `[n]` is an isogeny in characteristic `0`).

`degHomogPoly_of_noEmb` gives `DegHomogPoly` from the two open fields and the remainder
`DegHomogPolyNoEmb` (fields with no ring homomorphism to `ℂ`). With charpoly-lattice's result this also
gives Mumford §19 Thm 4 (`deg ψ = det V_ℓ(ψ)`) over these fields (`degEqDetTateC`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.OneProof.DegPolyC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj Polynomial
open ZInQ.LeafPush2 (CPts IsUniformization)
open ZInQ.Contrib.OneProof.CharPolyLattice

/-! ## A. Kernel points over any field extension and the fibre over the identity -/

section General

variable {k : Type} [Field k] [IsAlgClosed k] {X : Scheme} (s : X ⟶ Spec (CommRingCat.of k))
  [LocallyOfFiniteType s]

/-- A morphism `Spec L → X` through a closed point `x` is determined by its composite to `Spec k`. -/
theorem eq_of_closed_aux (L : Type) [Field L] (h : Spec (CommRingCat.of L) ⟶ X) (x : X)
    (hx : IsClosed {x}) (hh : h (IsLocalRing.closedPoint L) = x)
    (c : CommRingCat.of k ⟶ CommRingCat.of L) (hc : h ≫ s = Spec.map c) :
    h = Spec.map ((residueFieldIsoBase s x hx).hom ≫ c) ≫ X.fromSpecResidueField x := by
  subst hh
  have e := (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L X h)
  set φ := X.descResidueField (Scheme.stalkClosedPointTo h) with hφ
  have h1 : (residueFieldIsoBase s _ hx).inv ≫ φ = c := by
    apply Spec.map_injective
    rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, ← Category.assoc, e, hc]
  rw [← h1, Iso.hom_inv_id_assoc]
  exact e.symm

theorem eq_of_closed (L : Type) [Field L] (h h' : Spec (CommRingCat.of L) ⟶ X) (x : X)
    (hx : IsClosed {x}) (hh : h (IsLocalRing.closedPoint L) = x)
    (hh' : h' (IsLocalRing.closedPoint L) = x) (hs : h ≫ s = h' ≫ s) : h = h' := by
  have hc := (Spec.map_preimage (h ≫ s)).symm
  rw [eq_of_closed_aux s L h x hx hh _ hc,
    eq_of_closed_aux s L h' x hx hh' _ (by rw [← hs]; exact hc)]

/-- The image of a `k`-point is a closed point. -/
theorem isClosed_of_section (p : Spec (CommRingCat.of k) ⟶ X) (hp : p ≫ s = 𝟙 _) :
    IsClosed {p (IsLocalRing.closedPoint k)} :=
  ((pointEquivClosedPoint s) ⟨p, hp⟩).2

/-- A point of a discrete closed fibre is closed. -/
theorem isClosed_of_mem_fibre {Y : Scheme} (f : X ⟶ Y) [LocallyQuasiFinite f] (y : Y)
    (hy : IsClosed {y}) (x : X) (hx : f x = y) : IsClosed {x} := by
  have hF : IsClosed (f ⁻¹' {y}) := hy.preimage f.continuous
  haveI : DiscreteTopology (f ⁻¹' {y}) := (f.isDiscrete_preimage_singleton y).to_subtype
  rw [← closure_subset_iff_isClosed]
  intro z hz
  have hzF : z ∈ f ⁻¹' {y} := (closure_minimal (by simpa using hx) hF) hz
  have hsp : x ⤳ z := specializes_iff_mem_closure.mpr hz
  have hsp' : (⟨x, hx⟩ : f ⁻¹' {y}) ⤳ ⟨z, hzF⟩ :=
    (Topology.IsInducing.subtypeVal.specializes_iff).mp hsp
  rw [Set.mem_singleton_iff]
  exact (congrArg Subtype.val hsp'.eq).symm

end General

section AbVarPts

variable {k : Type} [Field k] [IsAlgClosed k] (A : PkgI3.AbVar k)

instance : LocallyOfFiniteType A.X.hom := inferInstance

/-- Two `L`-points through the same closed point are equal. -/
theorem pt_eq_of_closed (L : Type) [Field L] [Algebra k L] (P Q : A.Pt L) (x : A.X.left)
    (hx : IsClosed {x}) (hP : P.left (IsLocalRing.closedPoint L) = x)
    (hQ : Q.left (IsLocalRing.closedPoint L) = x) : P = Q := by
  apply Over.OverMorphism.ext
  exact eq_of_closed A.X.hom L P.left Q.left x hx hP hQ ((Over.w P).trans (Over.w Q).symm)

/-- The image of the identity point. -/
def e0 : A.X.left := (1 : A.Pt k).left (IsLocalRing.closedPoint k)

instance : Subsingleton ↥(𝟙_ (Over (Spec (CommRingCat.of k)))).left := by
  change Subsingleton (PrimeSpectrum k)
  infer_instance

theorem one_left_apply (L : Type) [Field L] [Algebra k L] :
    (1 : A.Pt L).left (IsLocalRing.closedPoint L) = e0 A := by
  rw [e0, Hom.one_def, Hom.one_def]
  change (η[A.X]).left ((toUnit (PkgI3.AbVar.ptObj (K := k) L)).left (IsLocalRing.closedPoint L)) =
    (η[A.X]).left ((toUnit (PkgI3.AbVar.ptObj (K := k) k)).left (IsLocalRing.closedPoint k))
  congr 1
  exact Subsingleton.elim _ _

theorem isClosed_e0 : IsClosed {e0 A} := by
  apply isClosed_of_section A.X.hom
  refine (Over.w (1 : A.Pt k)).trans ?_
  simp [PkgI3.AbVar.ptObj, Algebra.algebraMap_self]

variable {A} (ψ : PkgI3.AbVar.End A)

theorem mem_fibre_of_ker (L : Type) [Field L] [Algebra k L] (P : A.Pt L) (hP : P ≫ ψ.hom = 1) :
    ψ.hom.left (P.left (IsLocalRing.closedPoint L)) = e0 A := by
  rw [← one_left_apply A L, ← hP]
  rfl

/-- The fibre `ψ⁻¹(e₀)`. -/
def Fibre : Type := {x : A.X.left // ψ.hom.left x = e0 A}

variable [IsFinite ψ.hom.left]

theorem isClosed_of_fibre (x : A.X.left) (hx : ψ.hom.left x = e0 A) : IsClosed {x} :=
  isClosed_of_mem_fibre ψ.hom.left (e0 A) (isClosed_e0 A) x hx

instance : Finite (Fibre ψ) :=
  (ψ.hom.left.finite_preimage_singleton (e0 A)).to_subtype

/-- Kernel points to fibre points. -/
def kerToFibre (L : Type) [Field L] [Algebra k L] :
    (PkgI3.AbVar.ptMap (L := L) ψ).ker → Fibre ψ := fun P =>
  ⟨P.1.left (IsLocalRing.closedPoint L), mem_fibre_of_ker ψ L P.1 P.2⟩

theorem kerToFibre_injective (L : Type) [Field L] [Algebra k L] :
    Function.Injective (kerToFibre ψ L) := by
  intro P Q h
  have h' := congrArg Subtype.val h
  apply Subtype.ext
  exact pt_eq_of_closed A L P.1 Q.1 _ (isClosed_of_fibre ψ _ (kerToFibre ψ L P).2) rfl h'.symm

/-- The `L`-point through a fibre point. -/
def ptOfFibre (L : Type) [Field L] [Algebra k L] (x : Fibre ψ) : A.Pt L :=
  Over.homMk ((PkgI3.AbVar.ptObj (K := k) L).hom ≫
    pointOfClosedPoint A.X.hom x.1 (isClosed_of_fibre ψ x.1 x.2)) (by
      rw [Category.assoc, pointOfClosedPoint_comp, Category.comp_id])

theorem ptOfFibre_apply (L : Type) [Field L] [Algebra k L] (x : Fibre ψ) :
    (ptOfFibre ψ L x).left (IsLocalRing.closedPoint L) = x.1 := by
  change (pointOfClosedPoint A.X.hom x.1 _) _ = _
  exact pointOfClosedPoint_apply _ _ _ _

theorem ptOfFibre_mem (L : Type) [Field L] [Algebra k L] (x : Fibre ψ) :
    ptOfFibre ψ L x ≫ ψ.hom = 1 := by
  refine pt_eq_of_closed A L _ _ (e0 A) (isClosed_e0 A) ?_ (one_left_apply A L)
  change ψ.hom.left ((ptOfFibre ψ L x).left (IsLocalRing.closedPoint L)) = _
  rw [ptOfFibre_apply]
  exact x.2

theorem kerToFibre_surjective (L : Type) [Field L] [Algebra k L] :
    Function.Surjective (kerToFibre ψ L) := fun x =>
  ⟨⟨ptOfFibre ψ L x, ptOfFibre_mem ψ L x⟩, Subtype.ext (ptOfFibre_apply ψ L x)⟩

/-- **`#ker ψ(L) = #ψ⁻¹(e₀)` for every field `L ⊇ k`.** -/
theorem card_ker_eq (L : Type) [Field L] [Algebra k L] :
    Nat.card (PkgI3.AbVar.ptMap (L := L) ψ).ker = Nat.card (Fibre ψ) :=
  Nat.card_congr (Equiv.ofBijective _ ⟨kerToFibre_injective ψ L, kerToFibre_surjective ψ L⟩)

theorem finite_ker (L : Type) [Field L] [Algebra k L] :
    Finite (PkgI3.AbVar.ptMap (L := L) ψ).ker :=
  Finite.of_injective _ (kerToFibre_injective ψ L)

end AbVarPts

/-! ## B. `deg ψ ≤ #ψ⁻¹(e₀)` in characteristic `0`; `deg ψ = #ψ⁻¹(e₀)` -/

section Upper

open ZInQ.Contrib.OneProof.CharPolyEll

attribute [local instance] isIntegral_left

variable {k : Type} [Field k] [IsAlgClosed k] {A : PkgI3.AbVar k}

/-- **`deg ψ ≤ #ψ⁻¹(e₀)` in characteristic `0`.** The `ψ^*K(A)`-embeddings `τ` of `K(A)` into
`Ω = \overline{K(A)}` give `Ω`-points `P_τ` (through the generic point) with the same image under `ψ`;
`τ ↦ P_τ P_{τ₀}⁻¹` embeds them into `ker ψ(Ω)`, and their number is `deg ψ` (separability). -/
theorem degEnd_le_card_fibre [CharZero k] (ψ : PkgI3.AbVar.End A)
    (hiso : PkgI3.AbVar.IsIsogenyMor ψ.hom) :
    degEnd ψ ≤ Nat.card (Fibre ψ) := by
  classical
  haveI : IsFinite ψ.hom.left := hiso.1
  set X := A.X.left with hXdef
  set gp := genericPoint X with hgp
  have hψe : ψ.hom.left gp = gp :=
    ZInQ.Contrib.OneProof.DegDet.map_genericPoint _ hiso.2.surj
  letI fB : Field (X.presheaf.stalk (ψ.hom.left gp)) :=
    (ZInQ.Contrib.OneProof.DegDet.isField_stalk _ hψe).toField
  letI fK : Field (X.presheaf.stalk gp) :=
    (ZInQ.Contrib.OneProof.DegDet.isField_stalk _ rfl).toField
  letI alg : Algebra (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) :=
    (ψ.hom.left.stalkMap gp).hom.toAlgebra
  have hfr : degEnd ψ = Module.finrank (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) := by
    unfold degEnd; rw [if_pos hiso]
  by_cases h0 : degEnd ψ = 0
  · rw [h0]; exact Nat.zero_le _
  haveI hfd : FiniteDimensional (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) :=
    Module.finite_of_finrank_pos (by rw [← hfr]; omega)
  -- characteristic zero
  have cB : CharZero (X.presheaf.stalk (ψ.hom.left gp)) :=
    (RingHom.charZero_iff (Spec.preimage (X.fromSpecStalk (ψ.hom.left gp) ≫ A.X.hom)).hom.injective).mp
      inferInstance
  -- the algebraic closure of `K(A)` and the embeddings
  let Ω := AlgebraicClosure (X.presheaf.stalk gp)
  have hcard := AlgHom.card (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) Ω
  -- the `k`-structure of `Ω`
  set a : CommRingCat.of k ⟶ CommRingCat.of Ω :=
    Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (ψ.hom.left gp)) Ω)) ≫
      X.fromSpecStalk (ψ.hom.left gp) ≫ A.X.hom) with ha
  letI algkΩ : Algebra k Ω := a.hom.toAlgebra
  have keyψ : ∀ τ : X.presheaf.stalk gp →ₐ[X.presheaf.stalk (ψ.hom.left gp)] Ω,
      Spec.map (CommRingCat.ofHom (τ : X.presheaf.stalk gp →+* Ω)) ≫ X.fromSpecStalk gp ≫ ψ.hom.left =
        Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (ψ.hom.left gp)) Ω)) ≫
          X.fromSpecStalk (ψ.hom.left gp) := by
    intro τ
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext b
    exact τ.commutes b
  let P : (X.presheaf.stalk gp →ₐ[X.presheaf.stalk (ψ.hom.left gp)] Ω) → A.Pt Ω := fun τ =>
    Over.homMk (Spec.map (CommRingCat.ofHom (τ : X.presheaf.stalk gp →+* Ω)) ≫ X.fromSpecStalk gp) (by
      change _ = Spec.map (CommRingCat.ofHom a.hom)
      rw [CommRingCat.ofHom_hom, ha, Spec.map_preimage]
      have h3 := congrArg (· ≫ A.X.hom) (keyψ τ)
      simp only [Category.assoc] at h3
      have h4 : ψ.hom.left ≫ A.X.hom = A.X.hom := Over.w ψ.hom
      erw [h4] at h3
      exact (Category.assoc _ _ _).trans h3)
  have hPψ : ∀ τ τ', P τ ≫ ψ.hom = P τ' ≫ ψ.hom := by
    intro τ τ'
    apply Over.OverMorphism.ext
    change (Spec.map _ ≫ X.fromSpecStalk gp) ≫ ψ.hom.left = (Spec.map _ ≫ X.fromSpecStalk gp) ≫ ψ.hom.left
    rw [Category.assoc, Category.assoc, keyψ, keyψ]
  have hPinj : Function.Injective P := by
    intro τ τ' h
    have h1 := congrArg (fun t => t.left) h
    simp only [P, Over.homMk_left] at h1
    have h2 := Spec.map_injective ((cancel_mono _).mp h1)
    apply AlgHom.toRingHom_injective
    exact congrArg CommRingCat.Hom.hom h2
  let τ0 := IsScalarTower.toAlgHom (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) Ω
  let j : (X.presheaf.stalk gp →ₐ[X.presheaf.stalk (ψ.hom.left gp)] Ω) →
      (PkgI3.AbVar.ptMap (L := Ω) ψ).ker := fun τ =>
    ⟨P τ * (P τ0)⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      change (P τ ≫ ψ.hom) * (P τ0 ≫ ψ.hom)⁻¹ = 1
      rw [hPψ τ τ0, mul_inv_cancel]⟩
  have hj : Function.Injective j := by
    intro τ τ' h
    have h1 := congrArg Subtype.val h
    exact hPinj (mul_right_cancel h1)
  haveI := finite_ker ψ Ω
  have := Nat.card_le_card_of_injective j hj
  rw [card_ker_eq ψ Ω, Nat.card_eq_fintype_card, hcard] at this
  rw [hfr]
  exact this

/-- **An isogeny has nonzero degree** (`K(A)` is finite over `ψ^*K(A)`: finite morphisms are
quasi-finite at the generic point, and a quasi-finite algebra over a field is finite). -/
theorem degEnd_ne_zero (ψ : PkgI3.AbVar.End A) (hiso : PkgI3.AbVar.IsIsogenyMor ψ.hom) :
    degEnd ψ ≠ 0 := by
  classical
  haveI : IsFinite ψ.hom.left := hiso.1
  set X := A.X.left with hXdef
  set gp := genericPoint X with hgp
  have hψe : ψ.hom.left gp = gp :=
    ZInQ.Contrib.OneProof.DegDet.map_genericPoint _ hiso.2.surj
  letI fB : Field (X.presheaf.stalk (ψ.hom.left gp)) :=
    (ZInQ.Contrib.OneProof.DegDet.isField_stalk _ hψe).toField
  letI fK : Field (X.presheaf.stalk gp) :=
    (ZInQ.Contrib.OneProof.DegDet.isField_stalk _ rfl).toField
  letI alg : Algebra (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) :=
    (ψ.hom.left.stalkMap gp).hom.toAlgebra
  have hfr : degEnd ψ = Module.finrank (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) := by
    unfold degEnd; rw [if_pos hiso]
  haveI : Algebra.QuasiFinite (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) :=
    ψ.hom.left.quasiFiniteAt gp
  haveI : Module.Finite (X.presheaf.stalk (ψ.hom.left gp)) (X.presheaf.stalk gp) :=
    Module.Finite.of_quasiFinite
  rw [hfr]
  exact (Module.finrank_pos).ne'

/-- **`deg ψ = #ψ⁻¹(e₀) = #ker ψ(L)` for an isogeny in characteristic `0`.** -/
theorem degEnd_eq_card_fibre [CharZero k] (ψ : PkgI3.AbVar.End A)
    (hiso : PkgI3.AbVar.IsIsogenyMor ψ.hom) : degEnd ψ = Nat.card (Fibre ψ) := by
  haveI : IsFinite ψ.hom.left := hiso.1
  have hd := degEnd_ne_zero ψ hiso
  obtain ⟨-, hdvd⟩ := ZInQ.Contrib.OneProof.DegDet.KerDvd.kerDvdDeg ψ hd
  rw [card_ker_eq ψ (AlgebraicClosure k)] at hdvd
  exact le_antisymm (degEnd_le_card_fibre ψ hiso) (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd)

end Upper


/-! ## C. `#ker ψ(ℂ) = det_ℤ(M_ψ|_Λ) > 0` -/

section Complex

variable {K : Type} [Field K] [Algebra K ℂ] {A : PkgI3.AbVar K} {g : ℕ}
  {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {Φ : (Fin g → ℂ) → CPts A (algebraMap K ℂ)}

theorem unif_nsmul (hA : IsUniformization (algebraMap K ℂ) Λ Φ) (n : ℕ) (z : Fin g → ℂ) :
    Φ (n • z) = Φ z ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    exact (hA.2.1 0).2 (zero_mem _)
  | succ n ih => rw [succ_nsmul, hA.1, ih, pow_succ]

/-- **`#ker ψ(ℂ) = det_ℤ(M_ψ|_Λ)` and `det > 0`, when the kernel is finite.** -/
theorem card_ker_eq_det (hA : IsUniformization (algebraMap K ℂ) Λ Φ) (ψ : PkgI3.AbVar.End A)
    (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hM : ∀ z, Φ (M z) = Φ z ≫ ψ.hom)
    (hMlat : ∀ lam : Λ, M lam ∈ Λ) (hfin : Finite (PkgI3.AbVar.ptMap (L := ℂ) ψ).ker) :
    haveI := ZLattice.module_finite ℝ Λ
    haveI := ZLattice.module_free ℝ Λ
    ((Nat.card (PkgI3.AbVar.ptMap (L := ℂ) ψ).ker : ℕ) : ℤ) = LinearMap.det (latEnd Λ M hMlat) ∧
      0 < LinearMap.det (latEnd Λ M hMlat) := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  set KC := (PkgI3.AbVar.ptMap (L := ℂ) ψ).ker with hKC
  set X := latEnd Λ M hMlat with hX
  have hmem : ∀ z, M z ∈ Λ → (Φ z : PkgI3.AbVar.Pt ℂ A) ∈ KC := by
    intro z hz
    refine MonoidHom.mem_ker.mpr ?_
    change Φ z ≫ ψ.hom = 1
    rw [← hM]
    exact (hA.2.1 _).2 hz
  -- `M` is injective
  have hMinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    set N := Nat.card KC with hNdef
    have hN : 0 < N := Nat.card_pos
    have key : ∀ w, M w = 0 → N • w ∈ Λ := by
      intro w hw
      have hw' : Φ w ∈ KC := hmem w (by rw [hw]; exact zero_mem _)
      have h1 : (⟨Φ w, hw'⟩ : KC) ^ N = 1 := pow_card_eq_one'
      rw [← hA.2.1, unif_nsmul hA]
      exact congrArg Subtype.val h1
    apply HDec.G0Galois.eq_zero_of_real_smul_mem Λ z
    intro t
    have h2 := key (((t / N : ℝ) : ℂ) • z) (by rw [map_smul, hz, smul_zero])
    convert h2 using 1
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Complex.coe_smul]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    push_cast
    field_simp
  have hMsurj : Function.Surjective M := LinearMap.injective_iff_surjective.mp hMinj
  set Me := LinearEquiv.ofBijective M ⟨hMinj, hMsurj⟩ with hMe
  have hMe_apply : ∀ z, M (Me.symm z) = z := fun z => Me.apply_symm_apply z
  have hXinj : Function.Injective X := fun a b h =>
    Subtype.ext (hMinj (congrArg Subtype.val h))
  -- the map `Λ → ker`, `m ↦ Φ(M⁻¹ m)`
  have hmemf : ∀ m : Λ, (Φ (Me.symm m) : PkgI3.AbVar.Pt ℂ A) ∈ KC := fun m =>
    hmem _ (by rw [hMe_apply]; exact m.2)
  let f : Λ →+ Additive KC :=
    { toFun := fun m => Additive.ofMul ⟨Φ (Me.symm m), hmemf m⟩
      map_zero' := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change Φ (Me.symm ((0 : Λ) : Fin g → ℂ)) = 1
        rw [Submodule.coe_zero, map_zero]
        exact (hA.2.1 0).2 (zero_mem _)
      map_add' := fun m n' => by
        apply Additive.toMul.injective
        apply Subtype.ext
        change Φ (Me.symm ((m + n' : Λ) : Fin g → ℂ)) = Φ (Me.symm m) * Φ (Me.symm n')
        rw [Submodule.coe_add, map_add, hA.1] }
  have hfsurj : Function.Surjective f := by
    intro P
    obtain ⟨z, hz⟩ := hA.2.2.1 (Additive.toMul P).1
    have hzΛ : M z ∈ Λ := by
      rw [← hA.2.1, hM, hz]
      exact (Additive.toMul P).2
    refine ⟨⟨M z, hzΛ⟩, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change Φ (Me.symm (M z)) = _
    have : Me.symm (M z) = z := Me.symm_apply_apply z
    rw [this, hz]
  have hker : f.ker = (LinearMap.range X).toAddSubgroup := by
    ext m
    rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
    constructor
    · intro h
      have h1 : Φ (Me.symm m) = 1 := congrArg Subtype.val (congrArg Additive.toMul h)
      rw [hA.2.1] at h1
      exact ⟨⟨_, h1⟩, Subtype.ext (hMe_apply m)⟩
    · rintro ⟨n', rfl⟩
      apply Additive.toMul.injective
      apply Subtype.ext
      change Φ (Me.symm (M n')) = 1
      have : Me.symm (M n') = n' := Me.symm_apply_apply _
      rw [this]
      exact (hA.2.1 _).2 n'.2
  have hidx : Nat.card (Λ ⧸ LinearMap.range X) = Nat.card KC := by
    calc Nat.card (Λ ⧸ LinearMap.range X) = Nat.card (Λ ⧸ (LinearMap.range X).toAddSubgroup) := rfl
      _ = Nat.card (Λ ⧸ f.ker) := by rw [hker]
      _ = Nat.card (Additive KC) :=
        Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv
      _ = Nat.card KC := rfl
  have hdet := Submodule.natAbs_det_equiv (LinearMap.range X) (LinearEquiv.ofInjective X hXinj)
  have hdet2 : (LinearMap.det X).natAbs = Nat.card (Λ ⧸ LinearMap.range X) := by
    convert hdet using 3
    exact LinearMap.ext fun _ => rfl
  rw [hidx] at hdet2
  clear hdet
  have hdet := hdet2
  -- the sign: `det_ℤ X = det_ℝ M = |det_ℂ M|²`
  have hpos : 0 ≤ LinearMap.det X := by
    let bE := Module.Free.chooseBasis ℤ Λ
    let bR := bE.ofZLatticeBasis ℝ Λ
    have h1 : ((LinearMap.det X : ℤ) : ℝ) = LinearMap.det (M.restrictScalars ℝ) := by
      rw [← LinearMap.det_toMatrix bE, ← LinearMap.det_toMatrix bR]
      have hm := (Int.castRingHom ℝ).map_det (LinearMap.toMatrix bE bE X)
      rw [eq_intCast] at hm
      rw [hm]
      congr 1
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
        LinearMap.toMatrix_apply, Module.Basis.ofZLatticeBasis_apply, LinearMap.restrictScalars_apply]
      change _ = bR.repr ((X (bE j) : Λ) : Fin g → ℂ) i
      rw [Module.Basis.ofZLatticeBasis_repr_apply]
      rfl
    have h2 : LinearMap.det (M.restrictScalars ℝ) = Complex.normSq (LinearMap.det M) := by
      rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
    have h3 : (0 : ℝ) ≤ ((LinearMap.det X : ℤ) : ℝ) := by
      rw [h1, h2]; exact Complex.normSq_nonneg _
    exact_mod_cast h3
  have hne : LinearMap.det X ≠ 0 := by
    intro h0
    rw [h0, Int.natAbs_zero] at hdet
    exact (Nat.card_pos (α := KC)).ne' hdet.symm
  refine ⟨?_, lt_of_le_of_ne hpos (Ne.symm hne)⟩
  rw [← hdet, Int.natAbs_of_nonneg hpos]


end Complex

/-! ## D. The lattice representation; `det ≠ 0 ⇒` isogeny -/

section Ring

variable {K : Type} [Field K]

/-- (copied from homfree-proof) A homomorphism trivial on `A(ℂ)_σ` is zero. -/
theorem hom_eq_zero_of_cpts (σ : K →+* ℂ) {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B)
    (h : ∀ p : CPts A σ, p ≫ f.hom = 1) : f = 0 := by
  letI : Algebra K ℂ := σ.toAlgebra
  have hC : ZInQ.Contrib.AVB1.bcHom ℂ A B f = 0 := by
    apply PkgI3.AbVar.Hom.ext'
    apply ZInQ.HomUnify.hom_ext_of_cpts
    intro q
    rw [PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one]
    have h1 := ZInQ.Contrib.AVB1.bcPt_ptMap (A := A) (B := B) ℂ f q
    have h2 : PkgI3.AbVar.ptMap f (ZInQ.Contrib.AbVarBC.bcPt A ℂ q) = 1 :=
      h (ZInQ.Contrib.AbVarBC.bcPt A ℂ q)
    rw [h2] at h1
    have h3 : PkgI3.AbVar.ptMap (ZInQ.Contrib.AVB1.bcHom ℂ A B f) q = 1 :=
      (MulEquiv.map_eq_one_iff _).1 h1
    exact h3
  apply ZInQ.Contrib.AVB1.bcHom_injective (L := ℂ) A B
  rw [hC, map_zero]

section Lift

variable {σ : K →+* ℂ} {A : PkgI3.AbVar K} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
  [DiscreteTopology Λ] [IsZLattice ℝ Λ] {Φ : (Fin g → ℂ) → CPts A σ}

/-- (copied from homfree-proof) Two linear lifts of the same map agree. -/
theorem lift_unique (hA : IsUniformization σ Λ Φ) (ψ : (Fin g → ℂ) → CPts A σ)
    (M M' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ z, Φ (M z) = ψ z) (hM' : ∀ z, Φ (M' z) = ψ z) : M = M' := by
  have key : ∀ w, M w - M' w ∈ Λ := by
    intro w
    rw [← hA.2.1]
    have e : Φ (M w) = Φ (M w - M' w) * Φ (M' w) := by
      rw [← hA.1, sub_add_cancel]
    rw [hM, hM'] at e
    have := congrArg (fun x => x * (ψ w)⁻¹) e
    simpa using this.symm
  apply LinearMap.ext
  intro z
  apply sub_eq_zero.1
  apply HDec.G0Galois.eq_zero_of_real_smul_mem Λ
  intro t
  have := key ((t : ℂ) • z)
  rwa [map_smul, map_smul, ← smul_sub, Complex.coe_smul] at this

/-- The lattice representation `End(A) → End_ℤ(Λ)` as a ring homomorphism. -/
def latRep (hA : IsUniformization σ Λ Φ) (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ) :
    PkgI3.AbVar.End A →+* Module.End ℤ Λ where
  toFun f := latEnd Λ (M f) (hMlat f)
  map_one' := by
    have h1 : M 1 = LinearMap.id := lift_unique hA (fun z => Φ z) _ _
      (fun z => by rw [hM]; exact Category.comp_id _) (fun z => rfl)
    apply LinearMap.ext; intro lam; apply Subtype.ext
    rw [latEnd_apply, h1]; rfl
  map_mul' f f' := by
    have h1 : M (f * f') = M f ∘ₗ M f' := lift_unique hA (fun z => Φ z ≫ (f * f').hom) _ _
      (fun z => hM _ z) (fun z => by
        rw [LinearMap.comp_apply, hM, hM]
        change (Φ z ≫ f'.hom) ≫ f.hom = Φ z ≫ (f'.hom ≫ f.hom)
        rw [Category.assoc])
    apply LinearMap.ext; intro lam; apply Subtype.ext
    rw [latEnd_apply, h1]; rfl
  map_zero' := by
    have h1 : M 0 = 0 := lift_unique hA (fun z => Φ z ≫ (0 : PkgI3.AbVar.End A).hom) _ _
      (fun z => hM _ z) (fun z => by
        rw [LinearMap.zero_apply, PkgI3.AbVar.Hom.hom_zero, MonObj.comp_one]
        exact (hA.2.1 0).2 (zero_mem _))
    apply LinearMap.ext; intro lam; apply Subtype.ext
    rw [latEnd_apply, h1]; rfl
  map_add' f f' := by
    have h1 : M (f + f') = M f + M f' := lift_unique hA (fun z => Φ z ≫ (f + f').hom) _ _
      (fun z => hM _ z) (fun z => by
        rw [LinearMap.add_apply, hA.1, hM, hM, PkgI3.AbVar.Hom.hom_add, MonObj.comp_mul])
    apply LinearMap.ext; intro lam; apply Subtype.ext
    rw [latEnd_apply, h1]; rfl

theorem latRep_apply (hA : IsUniformization σ Λ Φ)
    (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ) (f) :
    latRep hA M hM hMlat f = latEnd Λ (M f) (hMlat f) := rfl

theorem latRep_injective (hA : IsUniformization σ Λ Φ)
    (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ) :
    Function.Injective (latRep hA M hM hMlat) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h0 : ∀ lam ∈ Λ, M f lam = 0 := fun lam hlam => by
    have := congrArg Subtype.val (LinearMap.congr_fun hf ⟨lam, hlam⟩)
    exact this
  have hMR : (M f).restrictScalars ℝ = 0 := by
    apply LinearMap.ext_on_range (v := fun lam : Λ => (lam : Fin g → ℂ))
    · rw [Subtype.range_coe_subtype]
      exact IsZLattice.span_top
    · intro lam
      exact h0 lam lam.2
  apply hom_eq_zero_of_cpts σ f
  intro p
  obtain ⟨z, rfl⟩ := hA.2.2.1 p
  rw [← hM]
  have : M f z = 0 := by
    have := LinearMap.congr_fun hMR z
    simpa using this
  rw [this]
  exact (hA.2.1 0).2 (zero_mem _)

/-- **An endomorphism with `det_ℤ(M_ψ|_Λ) ≠ 0` is an isogeny** (characteristic `0`): by
Cayley–Hamilton and injectivity of `latRep`, `ψ q(ψ) = q(ψ) ψ = [n]` with `n = ±det ≠ 0`, and `[n]`
is finite and surjective. -/
theorem isIsogeny_of_det_ne_zero [CharZero K] (hA : IsUniformization σ Λ Φ)
    (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ)
    (ψ : PkgI3.AbVar.End A) (hdet : LinearMap.det (latEnd Λ (M ψ) (hMlat ψ)) ≠ 0) :
    PkgI3.AbVar.IsIsogenyMor ψ.hom := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  set U := latRep hA M hM hMlat with hU
  set χ := (U ψ).charpoly with hχ
  have hUχ : U (aeval ψ χ) = 0 := by
    change U.toIntAlgHom (aeval ψ χ) = 0
    rw [← Polynomial.aeval_algHom_apply U.toIntAlgHom]
    exact LinearMap.aeval_self_charpoly (U ψ)
  have hχ0 : aeval ψ χ = 0 := latRep_injective hA M hM hMlat (by rw [hUχ, map_zero])
  have hc : χ.coeff 0 = LinearMap.det (U ψ) := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, finrank_lattice Λ, pow_mul, neg_one_sq, one_pow,
      _root_.one_mul]
  set q := aeval ψ χ.divX with hq
  set n : ℤ := -χ.coeff 0 with hn
  have hn0 : n ≠ 0 := by rw [hn, neg_ne_zero, hc]; exact hdet
  have h1 : ψ * q = (n : PkgI3.AbVar.End A) := by
    have := congrArg (aeval ψ) (X_mul_divX_add χ)
    rw [map_add, map_mul, aeval_X, aeval_C, hχ0] at this
    rw [hn, Int.cast_neg, ← add_eq_zero_iff_eq_neg, ← this, hq]
    simp
  have h2 : q * ψ = (n : PkgI3.AbVar.End A) := by
    have := congrArg (aeval ψ) (divX_mul_X_add χ)
    rw [map_add, map_mul, aeval_X, aeval_C, hχ0] at this
    rw [hn, Int.cast_neg, ← add_eq_zero_iff_eq_neg, ← this, hq]
    simp
  have hiso := HDec.HSyn.mulIsogeny_proved K A n hn0
  obtain ⟨hfin, hsurj⟩ := hiso
  have e1 : (n : PkgI3.AbVar.End A).hom.left = q.hom.left ≫ ψ.hom.left := by
    rw [← h1]; rfl
  have e2 : (n : PkgI3.AbVar.End A).hom.left = ψ.hom.left ≫ q.hom.left := by
    rw [← h2]; rfl
  refine ⟨?_, ?_⟩
  · haveI : IsFinite (ψ.hom.left ≫ q.hom.left) := by rw [← e2]; exact hfin
    haveI : IsSeparated (q.hom.left ≫ A.X.hom) := by
      rw [show q.hom.left ≫ A.X.hom = A.X.hom from Over.w q.hom]; infer_instance
    haveI : IsSeparated q.hom.left := IsSeparated.of_comp q.hom.left A.X.hom
    exact IsFinite.of_comp ψ.hom.left q.hom.left
  · constructor
    intro y
    obtain ⟨x, hx⟩ := hsurj.surj y
    refine ⟨q.hom.left x, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← e1, hx]

end Lift


end Ring

/-! ## E. `deg ψ = det_ℤ(U ψ)`; the polynomial -/

section Assembly

open ZInQ.Contrib.OneProof.CharPolyEll

/-- The determinant of a matrix of homogeneous linear forms is homogeneous of degree its size. -/
theorem det_isHomogeneous {I : Type} [Fintype I] [DecidableEq I] {τ R : Type} [CommRing R]
    (P : Matrix I I (MvPolynomial τ R)) (h : ∀ a b, (P a b).IsHomogeneous 1) :
    (P.det).IsHomogeneous (Fintype.card I) := by
  rw [Matrix.det_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro π _
  have hprod : (∏ i, P (π i) i).IsHomogeneous (Fintype.card I) := by
    have := MvPolynomial.IsHomogeneous.prod Finset.univ (fun i => P (π i) i) (fun _ => 1)
      (fun i _ => h _ _)
    simpa using this
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs
  · rw [hs, one_smul]; exact hprod
  · rw [hs, Units.neg_smul, one_smul]; exact hprod.neg

variable {k : Type} [Field k] [IsAlgClosed k] [CharZero k]

/-- **`deg ψ = det_ℤ(M_ψ|_Λ)` for every endomorphism** (`k` algebraically closed of characteristic
`0`, `σ = emb ∘ (k → k̄)`). -/
theorem degEnd_eq_det (emb : AlgebraicClosure k →+* ℂ) {A : PkgI3.AbVar k} {g : ℕ}
    {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Φ : (Fin g → ℂ) → CPts A (emb.comp (algebraMap k (AlgebraicClosure k)))}
    (hA : IsUniformization (emb.comp (algebraMap k (AlgebraicClosure k))) Λ Φ)
    (M : PkgI3.AbVar.End A → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hM : ∀ f z, Φ (M f z) = Φ z ≫ f.hom) (hMlat : ∀ f (lam : Λ), M f lam ∈ Λ)
    (ψ : PkgI3.AbVar.End A) :
    haveI := ZLattice.module_finite ℝ Λ
    haveI := ZLattice.module_free ℝ Λ
    ((degEnd ψ : ℕ) : ℤ) = LinearMap.det (latEnd Λ (M ψ) (hMlat ψ)) := by
  classical
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  by_cases hiso : PkgI3.AbVar.IsIsogenyMor ψ.hom
  · haveI : IsFinite ψ.hom.left := hiso.1
    letI : Algebra k ℂ := (emb.comp (algebraMap k (AlgebraicClosure k))).toAlgebra
    have h1 := degEnd_eq_card_fibre ψ hiso
    have h2 := card_ker_eq ψ ℂ
    have h3 := card_ker_eq_det (K := k) (Φ := Φ) hA ψ (M ψ) (hM ψ) (hMlat ψ) (finite_ker ψ ℂ)
    rw [h1, ← h2]
    exact h3.1
  · have h0 : degEnd ψ = 0 := by
      unfold degEnd; rw [if_neg hiso]
    rw [h0, Nat.cast_zero]
    by_contra hne
    exact hiso (isIsogeny_of_det_ne_zero hA M hM hMlat ψ (Ne.symm hne))

end Assembly

/-! ## F. The narrowed statement and the discharge of `DegHomogPoly` -/

/-- **`DegHomogPoly` over algebraically closed fields that embed into `ℂ`.** deg-det's statement with
the extra hypothesis `σ : k → ℂ`. -/
def DegHomogPolyC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (_ : k →+* ℂ) (A : PkgI3.AbVar k) (r : ℕ)
    (e : Fin r → PkgI3.AbVar.End A),
    ∃ (g : ℕ) (N : MvPolynomial (Fin r) ℚ), A.dim = (g : WithBot ℕ∞) ∧ N.IsHomogeneous (2 * g) ∧
      ∀ x : Fin r → ℤ, ((CharPolyEll.degEnd (∑ i, x i • e i) : ℕ) : ℚ) =
        MvPolynomial.eval (fun i => (x i : ℚ)) N

/-- **`DegHomogPolyC` (proved) from `uniformizationLeafAll` and `mumfordTorsionAlgClosed`.** -/
theorem degHomogPolyC (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : DegHomogPolyC := by
  intro k _ _ σ A r e
  classical
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨emb⟩ := exists_emb σ
  set σ' : k →+* ℂ := emb.comp (algebraMap k (AlgebraicClosure k)) with hσ'
  have h35 := AvSplit.Final.h38 HL HT
  have hN2 := ZInQ.HomLattice.homLinearLift_of_analyticHomLift
    (AvSplit.HomLatticeAN3.analyticHomLift_of_C (ZInQ.HomLattice.analyticHomLiftC_of_leaf HL))
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨Λ, Φ, hd, hlat, hA⟩ := h35 k A σ' g hg
  choose M hM using fun f => hN2 k A A σ' g g Λ Λ Φ Φ hg hg hA hA f
  have hMlat : ∀ f (lam : Λ), M f lam ∈ Λ := fun f lam =>
    HDec.G0Galois.lift_mem_lattice hA hA f (M f) (hM f) lam
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  set U := latRep hA M hM hMlat with hU
  let bE := Module.Free.chooseBasis ℤ Λ
  let C : Fin r → Matrix (Module.Free.ChooseBasisIndex ℤ Λ) (Module.Free.ChooseBasisIndex ℤ Λ) ℤ :=
    fun i => LinearMap.toMatrix bE bE (U (e i))
  let P : Matrix (Module.Free.ChooseBasisIndex ℤ Λ) (Module.Free.ChooseBasisIndex ℤ Λ)
      (MvPolynomial (Fin r) ℚ) :=
    Matrix.of fun a b => ∑ i, MvPolynomial.X i * MvPolynomial.C ((C i a b : ℤ) : ℚ)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ Λ) = 2 * g := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, finrank_lattice Λ]
  refine ⟨g, P.det, hg, ?_, fun x => ?_⟩
  · rw [← hcard]
    apply det_isHomogeneous
    intro a b
    change (∑ i, MvPolynomial.X i * MvPolynomial.C ((C i a b : ℤ) : ℚ)).IsHomogeneous 1
    apply MvPolynomial.IsHomogeneous.sum
    intro i _
    exact (MvPolynomial.isHomogeneous_X ℚ i).mul (MvPolynomial.isHomogeneous_C (Fin r) _)
  · have h1 := degEnd_eq_det emb hA M hM hMlat (∑ i, x i • e i)
    have h2 : latEnd Λ (M (∑ i, x i • e i)) (hMlat _) = ∑ i, x i • U (e i) := by
      rw [← latRep_apply hA M hM hMlat, map_sum]
      congr 1
      ext1 i
      exact map_zsmul U (x i) (e i)
    rw [h2, ← LinearMap.det_toMatrix bE, map_sum] at h1
    have h3 : ((CharPolyEll.degEnd (∑ i, x i • e i) : ℕ) : ℚ) =
        (((∑ i, LinearMap.toMatrix bE bE (x i • U (e i))).det : ℤ) : ℚ) := by
      rw [← h1]; push_cast; rfl
    rw [h3]
    change (Int.castRingHom ℚ) (Matrix.det _) = _
    rw [RingHom.map_det, RingHom.map_det]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, P, C, map_sum,
      map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.sum_apply, eq_intCast]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Matrix.smul_apply, smul_eq_mul, Int.cast_mul]

/-- **The remainder of `DegHomogPoly`: algebraically closed fields with no embedding into `ℂ`**
(characteristic `p > 0`, or characteristic `0` and transcendence degree over `ℚ` above the continuum).
deg-det's statement restricted to them. -/
def DegHomogPolyNoEmb : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k], IsEmpty (k →+* ℂ) → ∀ (A : PkgI3.AbVar k) (r : ℕ)
    (e : Fin r → PkgI3.AbVar.End A),
    ∃ (g : ℕ) (N : MvPolynomial (Fin r) ℚ), A.dim = (g : WithBot ℕ∞) ∧ N.IsHomogeneous (2 * g) ∧
      ∀ x : Fin r → ℤ, ((CharPolyEll.degEnd (∑ i, x i • e i) : ℕ) : ℚ) =
        MvPolynomial.eval (fun i => (x i : ℚ)) N

/-- **`DegHomogPoly` from the two bundle fields and the remainder (proved).** -/
theorem degHomogPoly_of_noEmb (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) (HR : DegHomogPolyNoEmb) : DegDet.DegHomogPoly := by
  intro k _ _ A r e
  rcases isEmpty_or_nonempty (k →+* ℂ) with he | hne
  · exact HR k he A r e
  · obtain ⟨σ⟩ := hne
    exact degHomogPolyC HL HT k σ A r e

/-- **The field `charPolyIndepOfEllAlgClosed` through deg-det's route**, from the open fields
`uniformizationLeafAll`, `mumfordTorsionAlgClosed`, `homFreeFiniteAlgClosed` and the remainder
`DegHomogPolyNoEmb`. -/
theorem charPolyIndepOfEllAlgClosed_of_degHomogPolyNoEmb
    (HL : BPAnalytic.Uniformization.UniformizationLeafAll) (HT : AvSplit.MumfordTorsionAlgClosed)
    (HR : DegHomogPolyNoEmb) (HH : ZInQ.Contrib.AVB1.HomFreeFiniteAlgClosed) :
    ZInQ.Contrib.AVB1.CharPolyIndepOfEllAlgClosed :=
  DegDet.charPolyIndepOfEllAlgClosed_of_degHomogPoly_mumford (degHomogPoly_of_noEmb HL HT HR) HT HH

/-- **Mumford §19 Thm 4, first assertion (`deg ψ = det V_ℓ(ψ)`), over algebraically closed fields
that embed into `ℂ`** (charpoly-ell's `DegEqDetTate` with `σ : k → ℂ` added). -/
def DegEqDetTateC : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (_ : k →+* ℂ) (A : PkgI3.AbVar k) (ψ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        (LinearMap.toMatrix b b ((PkgI3.AbVar.homT (ℓ := ℓ) ψ).baseChange ℚ_[ℓ])).det =
          (CharPolyEll.degEnd ψ : ℚ_[ℓ])

/-- **`DegEqDetTateC` (proved)**: `det V_ℓ(ψ) = det_ℤ(M_ψ|_Λ) = deg ψ`. -/
theorem degEqDetTateC (HL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (HT : AvSplit.MumfordTorsionAlgClosed) : DegEqDetTateC := by
  intro k _ _ σ A ψ ℓ _ hℓ I _ _ b
  classical
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨emb⟩ := exists_emb σ
  set σ' : k →+* ℂ := emb.comp (algebraMap k (AlgebraicClosure k)) with hσ'
  have h35 := AvSplit.Final.h38 HL HT
  have hN2 := ZInQ.HomLattice.homLinearLift_of_analyticHomLift
    (AvSplit.HomLatticeAN3.analyticHomLift_of_C (ZInQ.HomLattice.analyticHomLiftC_of_leaf HL))
  obtain ⟨g, hg⟩ := PkgI3.AbVar.dim_finite A
  obtain ⟨Λ, Φ, hd, hlat, hA⟩ := h35 k A σ' g hg
  choose M hM using fun f => hN2 k A A σ' g g Λ Λ Φ Φ hg hg hA hA f
  have hMlat : ∀ f (lam : Λ), M f lam ∈ Λ := fun f lam =>
    HDec.G0Galois.lift_mem_lattice hA hA f (M f) (hM f) lam
  haveI := ZLattice.module_finite ℝ Λ
  haveI := ZLattice.module_free ℝ Λ
  have hcp := charpoly_V_eq HT emb A ψ g hg Λ hlat Φ hA (M ψ) (hM ψ) (hMlat ψ) ℓ hℓ I b
  have hdeg := degEnd_eq_det emb hA M hM hMlat ψ
  have hI := DegDet.card_basis_V HT A ℓ hℓ g hg b
  rw [Matrix.det_eq_sign_charpoly_coeff, hcp, Polynomial.coeff_map, hI, pow_mul, neg_one_sq,
    one_pow, _root_.one_mul]
  have hX := LinearMap.det_eq_sign_charpoly_coeff (latEnd Λ (M ψ) (hMlat ψ))
  rw [finrank_lattice Λ, pow_mul, neg_one_sq, one_pow, _root_.one_mul] at hX
  rw [← hX, ← hdeg]
  simp

end ZInQ.Contrib.OneProof.DegPolyC
