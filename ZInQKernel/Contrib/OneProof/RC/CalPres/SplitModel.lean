import ZInQKernel.Contrib.OneProof.RC.Local.TameFreeModel
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.Dual

/-! The two disks of the tame model (tex 3470–3481, 4066–4080). -/

noncomputable section

namespace ZInQ.Contrib.RC53Assist.Calibration

open CategoryTheory
open ZInQ.Manuscript.RC.Local
open ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Contrib.CloudB3RC53.SelmerDuality

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]

/-- Direct sum of a degree (0,1) disk and a degree (1,2) disk. -/
def splitLocalModel (F D : V →ₗ[R] V) : GCx R :=
  cx3 (F.prod 0) (D.comp (LinearMap.snd R V V)) (fun x => by simp)

/-- Degree-one classes of the split model have an ordinary and a singular coordinate. -/
def splitLocalH1 (F D : V →ₗ[R] V) :
    (splitLocalModel F D).toCC.homology 1 ≃ₗ[R]
      (V ⧸ LinearMap.range F) × LinearMap.ker D := by
  let C := (splitLocalModel F D).toCC
  let S := C.sc' 0 1 2
  let T := ShortComplex.moduleCatMk (F.prod 0) (D.comp (LinearMap.snd R V V))
    (by ext x; simp)
  let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by ext x; rfl) (by ext x; rfl)
  let f : LinearMap.ker T.g.hom →ₗ[R] (V ⧸ LinearMap.range F) × LinearMap.ker D :=
    (((LinearMap.range F).mkQ.comp (LinearMap.fst R V V)).comp
      (LinearMap.ker T.g.hom).subtype).prod
      (((LinearMap.snd R V V).comp (LinearMap.ker T.g.hom).subtype).codRestrict
        (LinearMap.ker D) (fun z => z.property))
  have hk : LinearMap.range T.moduleCatToCycles = LinearMap.ker f := by
    ext z
    change (∃ x : V, T.moduleCatToCycles x = z) ↔ f z = 0
    constructor
    · rintro ⟨x, rfl⟩
      apply Prod.ext
      · change (LinearMap.range F).mkQ (F x) = 0
        exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ _)
      · apply Subtype.ext
        rfl
    · intro hz
      have hz₁ : (LinearMap.range F).mkQ z.1.1 = 0 := congrArg Prod.fst hz
      have hz₂ : z.1.2 = 0 := congrArg (fun a => a.2.val) hz
      obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).1 hz₁
      exact ⟨x, Subtype.ext (Prod.ext hx hz₂.symm)⟩
  have hsur : Function.Surjective f := by
    rintro ⟨a, b⟩
    obtain ⟨x, rfl⟩ := (LinearMap.range F).mkQ_surjective a
    exact ⟨⟨(x, b.val), b.property⟩, rfl⟩
  exact ((C.homologyIsoSc' 0 1 2
      ((ComplexShape.up ℤ).prev_eq' (show (0 : ℤ) + 1 = 1 from rfl))
      ((ComplexShape.up ℤ).next_eq' (show (1 : ℤ) + 1 = 2 from rfl))) ≪≫ ShortComplex.homologyMapIso e ≪≫
    T.moduleCatHomologyIso).toLinearEquiv.trans
      ((Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hsur))

/-- Degree-two cohomology of the split model is the cokernel of its second disk. -/
def splitLocalH2 (F D : V →ₗ[R] V) :
    (splitLocalModel F D).toCC.homology 2 ≃ₗ[R] V ⧸ LinearMap.range D := by
  let C := (splitLocalModel F D).toCC
  let S := C.sc' 1 2 3
  let T := ShortComplex.moduleCatMk (D.comp (LinearMap.snd R V V))
    (0 : V →ₗ[R] PUnit) (by simp)
  let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by ext x; rfl) (by ext x; rfl)
  let f : LinearMap.ker T.g.hom →ₗ[R] V ⧸ LinearMap.range D :=
    (LinearMap.range D).mkQ.comp (LinearMap.ker T.g.hom).subtype
  have hk : LinearMap.range T.moduleCatToCycles = LinearMap.ker f := by
    ext z
    change (∃ x : V × V, T.moduleCatToCycles x = z) ↔ (LinearMap.range D).mkQ z.val = 0
    constructor
    · rintro ⟨x, hx⟩
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x.2, congrArg Subtype.val hx⟩
    · intro hz
      obtain ⟨x, hx⟩ := (Submodule.Quotient.mk_eq_zero _).1 hz
      exact ⟨(0, x), Subtype.ext hx⟩
  have hsur : Function.Surjective f := by
    intro a
    obtain ⟨x, rfl⟩ := (LinearMap.range D).mkQ_surjective a
    exact ⟨⟨x, rfl⟩, rfl⟩
  exact ((C.homologyIsoSc' 1 2 3
      ((ComplexShape.up ℤ).prev_eq' (show (1 : ℤ) + 1 = 2 from rfl))
      ((ComplexShape.up ℤ).next_eq' (show (2 : ℤ) + 1 = 3 from rfl))) ≪≫ ShortComplex.homologyMapIso e ≪≫
    T.moduleCatHomologyIso).toLinearEquiv.trans
      ((Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hsur))

/-- If the first coordinate restricts bijectively to (P), quotienting by (P) leaves
the second coordinate. This works for a graph in a product, without requiring its second
coordinate to vanish. -/
def quotientOfFirstCoordinate {U : Type} [AddCommGroup U] [Module R U]
    (P : Submodule R (U × V))
    (h : Function.Bijective ((LinearMap.fst R U V).comp P.subtype)) :
    ((U × V) ⧸ P) ≃ₗ[R] V := by
  let e := LinearEquiv.ofBijective ((LinearMap.fst R U V).comp P.subtype) h
  let f : U × V →ₗ[R] V := LinearMap.snd R U V -
    ((LinearMap.snd R U V).comp P.subtype).comp
      (e.symm.toLinearMap.comp (LinearMap.fst R U V))
  have hf (x : U × V) : f x = x.2 - (e.symm x.1).val.2 := rfl
  have hk : P = LinearMap.ker f := by
    ext x
    rw [LinearMap.mem_ker, hf, sub_eq_zero]
    have he : (e.symm x.1).val.1 = x.1 := e.apply_symm_apply x.1
    constructor
    · intro hx
      have hh : e (⟨x, hx⟩ : P) = x.1 := rfl
      rw [← hh, e.symm_apply_apply]
    · intro hx
      have heq : x = (e.symm x.1).val := Prod.ext he.symm hx
      rw [heq]
      exact (e.symm x.1).property
  have hsur : Function.Surjective f := by
    intro v
    refine ⟨(0, v), ?_⟩
    simp [hf]
  exact (Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hsur)

/-- The degree-one change of coordinates for the active case. Here (Phi-1=2T);
(g-1=-2) and (Phi-N_q(g)=2T). In the new coordinates the ordinary component
is minus the inertia coordinate. -/
def activeMiddleCoordinates (T : V →ₗ[R] V) : (V × V) ≃ₗ[R] (V × V) where
  toFun x := (-x.2, x.1 + T x.2)
  invFun y := (y.2 + T y.1, -y.1)
  left_inv x := by ext <;> simp [add_assoc]
  right_inv x := by ext <;> simp [add_assoc]
  map_add' x y := by ext <;> simp <;> abel
  map_smul' a x := by ext <;> simp [smul_add]

/-- Under the active basis change, (d^0(x)=(2Tx,-2x)) becomes ((2x,0)). -/
theorem activeMiddleCoordinates_d0 (T : V →ₗ[R] V) (x : V) :
    activeMiddleCoordinates T ((2 : R) • T x, -(2 : R) • x) = ((2 : R) • x, 0) := by
  ext <;> simp [activeMiddleCoordinates, neg_smul]

/-- Under the active basis change, (d^1(v,w)=2v+2Tw) is twice the second coordinate. -/
theorem activeMiddleCoordinates_d1 (T : V →ₗ[R] V) (x : V × V) :
    (2 : R) • (activeMiddleCoordinates T x).2 = (2 : R) • x.1 + (2 : R) • T x.2 := by
  exact smul_add _ _ _

/-- A map of three-term models with invertible components in degrees zero through two
is an isomorphism of cochain complexes. -/
private theorem cx3Hom_isIso
    {d0 : V →ₗ[R] V × V} {d1 : (V × V) →ₗ[R] V}
    {e0 : V →ₗ[R] V × V} {e1 : (V × V) →ₗ[R] V}
    {hd : ∀ x, d1 (d0 x) = 0} {he : ∀ x, e1 (e0 x) = 0}
    (b : (V × V) ≃ₗ[R] (V × V))
    (c0 : ∀ x, b (d0 x) = e0 x) (c1 : ∀ x, d1 x = e1 (b x)) :
    IsIso (GHom.toCC (cx3Hom (h := hd) (h' := he) LinearMap.id b.toLinearMap LinearMap.id
      c0 c1)) := by
  let f := GHom.toCC (cx3Hom (h := hd) (h' := he) LinearMap.id b.toLinearMap LinearMap.id c0 c1)
  have pointwise (n : ℤ) : IsIso (f.f n) := by
    rcases n with (_ | _ | _ | n) | n
    · exact inferInstanceAs (IsIso (𝟙 (ModuleCat.of R V)))
    · exact b.toModuleIso.isIso_hom
    · exact inferInstanceAs (IsIso (𝟙 (ModuleCat.of R V)))
    · exact inferInstanceAs (IsIso (𝟙 (ModuleCat.of R PUnit)))
    · exact inferInstanceAs (IsIso (𝟙 (ModuleCat.of R PUnit)))
  exact @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ f pointwise

/-- At a moving place the augmented tame model is the split model. -/
def movingTameNormalization (Φ : V →ₗ[R] V) (q : ℕ) (hq : Odd q) :
    (tameFreeModel1 Φ q hq).toCC ≅ (splitLocalModel (frobOne Φ) (frobQ Φ q)).toCC := by
  let b := LinearEquiv.refl R (V × V)
  have c0 (x : V) : (tameFreeModel1 Φ q hq).d 0 1 rfl x = (frobOne Φ x, 0) :=
    tameFreeModel1_d0 Φ q hq x
  have c1 (x : V × V) : (tameFreeModel1 Φ q hq).d 1 2 rfl x = frobQ Φ q x.2 :=
    tameFreeModel1_d1 Φ q hq x.1 x.2
  let hd := freeD1_freeD0 _ _ _ (tame_DC_CA_one Φ q hq)
  let f : GHom (tameFreeModel1 Φ q hq) (splitLocalModel (frobOne Φ) (frobQ Φ q)) :=
    cx3Hom (h := hd) LinearMap.id b.toLinearMap LinearMap.id c0 c1
  haveI : IsIso (GHom.toCC f) :=
    cx3Hom_isIso (hd := hd) (e0 := (frobOne Φ).prod 0)
      (e1 := (frobQ Φ q).comp (LinearMap.snd R V V)) b c0 c1
  exact asIso (GHom.toCC f)

/-- The odd tame norm is the identity when inertia acts by minus one. -/
theorem tameNorm_negId (q : ℕ) (hq : Odd q) :
    tameNorm q (-(LinearMap.id : V →ₗ[R] V)) = LinearMap.id := by
  obtain ⟨k, rfl⟩ := hq
  have h1 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have h2 : (2 * k + 1 - 1) / 2 = k := by omega
  ext x
  simp only [tameNorm, h1, h2, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.neg_apply, add_smul, one_smul, smul_neg]
  abel

/-- When inertia is minus one and the Frobenius minus one is twice an endomorphism,
the active tame model is the split model with multiplication by two in both disks. -/
def activeTameNormalization (Φ T : V →ₗ[R] V) (q : ℕ) (hq : Odd q)
    (hΦ : Φ - LinearMap.id = (2 : R) • T)
    (hg : (-(LinearMap.id : V →ₗ[R] V)) ∘ₗ (-LinearMap.id) = LinearMap.id)
    (hc : Φ ∘ₗ (-LinearMap.id) = (-LinearMap.id) ∘ₗ Φ) :
    (tameFreeModel Φ (-LinearMap.id) q hq hc hg).toCC ≅
      (splitLocalModel ((2 : R) • (LinearMap.id : V →ₗ[R] V)) ((2 : R) • LinearMap.id)).toCC := by
  let b := activeMiddleCoordinates T
  have hgsub : -(LinearMap.id : V →ₗ[R] V) - LinearMap.id = -(2 : R) • LinearMap.id := by
    rw [neg_smul, two_smul]
    abel
  let I : V →ₗ[R] V := LinearMap.id
  have c0 (x : V) :
      b ((tameFreeModel Φ (-LinearMap.id) q hq hc hg).d 0 1 rfl x) = ((2 : R) • x, 0) := by
    change b ((Φ - I) x, (-I - I) x) = _
    dsimp only [I]
    rw [hΦ, hgsub]
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.neg_apply, neg_smul, b] using
      activeMiddleCoordinates_d0 T x
  have c1 (x : V × V) :
      (tameFreeModel Φ (-LinearMap.id) q hq hc hg).d 1 2 rfl x = (2 : R) • (b x).2 := by
    change (-(-I - I)) x.1 + (Φ - tameNorm q (-I)) x.2 = _
    dsimp only [I]
    rw [tameNorm_negId q hq, hΦ, hgsub, neg_smul, neg_neg]
    simpa only [LinearMap.smul_apply, LinearMap.id_apply] using
      (activeMiddleCoordinates_d1 T x).symm
  let hd := freeD1_freeD0 _ _ _ (tame_DC_CA Φ (-LinearMap.id) q hq hc hg)
  let f : GHom (tameFreeModel Φ (-LinearMap.id) q hq hc hg)
      (splitLocalModel ((2 : R) • (LinearMap.id : V →ₗ[R] V)) ((2 : R) • LinearMap.id)) :=
    cx3Hom (h := hd) LinearMap.id b.toLinearMap LinearMap.id c0 c1
  haveI : IsIso (GHom.toCC f) :=
    cx3Hom_isIso (hd := hd) (e0 := ((2 : R) • I).prod 0)
      (e1 := ((2 : R) • I).comp (LinearMap.snd R V V)) b c0 c1
  exact asIso (GHom.toCC f)


end ZInQ.Contrib.RC53Assist.Calibration
