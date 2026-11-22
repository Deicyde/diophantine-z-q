import ZInQKernel.Contrib.OneProof.MumfordGroupLawRed
import ZInQKernel.Contrib.NeronC.NeronGroup
import ZInQKernel.Contrib.OneProof.MumfordGroupLawConn

/-!
# group-law-dvr: *GIT* Thm 6.14 over a DVR from Néron models over a DVR and one comparison step

Task group-law-dvr (2026-11-16); report docs/research/group-law-dvr.md. group-law proved the chain's only use of the
group-law field from Mumford's *GIT* Thm 6.14 over a discrete valuation ring
(`LeafQM.AV.R1UnivRigid.qmFamilyGroupLaw_of_dvr : ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR → QMFamilyGroupLaw`).
This file reduces `MumfordGroupLawDVR` to:

* **LEAF `NeronSchemeExtensionDVR`**: Néron models of abelian varieties over the fraction field of a DVR
  (Bosch–Lütkebohmert–Raynaud, *Néron models*, §1.4 Thm 3 with §1.2 Def. 1, at `S = Spec R`), the DVR case of
  **`NeronSchemeExtensionDedekind`** (the same theorem over any affine Dedekind scheme). The Dedekind form also gives
  the existing field `ZInQ.Contrib.NeronC.NeronSchemeExtensionExists` (`neronSchemeExtensionExists_of_dedekind`), which
  is the case `D = 𝓞_L` and does not reach the chain's DVRs (local rings of curves over `ℚ`).
* **GLUE `NeronGoodModelIso`**: for `F` as in the leaf (proper smooth over a DVR, every field fibre an abelian
  variety), every morphism `ψ : F → N` to a smooth separated `R`-scheme that is an isomorphism on generic fibres is an
  isomorphism.

Proved here (no `sorry`, standard axioms): `mumfordGroupLawDVR_of_neron`. The group law on `F` is the Néron model's
(`NeronC.grpObjOfNeron`, from the mapping property alone), transported along `ψ : F ≅ N` where `ψ` extends the generic
identification `F_K ≅ A ≅ N_K` (mapping property, `F` smooth); its identity is `e` because both are `R`-points of the
separated `N` agreeing on the scheme-theoretically dense generic fibre (`NeronC.pullback_map_injective`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.GroupLawNeron

open LeafQM.AV.R1UnivRigid PkgI3

/-- The generic point `Spec K → Spec R` of a domain `R` with fraction field `K`. -/
abbrev genMap (R K : Type) [CommRing R] [Field K] [Algebra R K] :
    Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R K))

/-! ## §1 The leaves -/

/-- **LEAF `NeronSchemeExtensionDedekind`** (Bosch–Lütkebohmert–Raynaud, *Néron models*, Springer 1990, §1.4 Thm 3,
with §1.2 Def. 1; numbers UNVERIFIED, no network). *Printed* (as recalled): `S` a Dedekind scheme with field of
rational functions `K`, `A_K` an abelian variety over `K`; then `A_K` admits a Néron model over `S`: a smooth,
separated `S`-scheme `N` of finite type with `N_K ≅ A_K` such that every `K`-morphism `Y_K → A_K` from the generic
fibre of a smooth `S`-scheme `Y` extends uniquely to an `S`-morphism `Y → N`. *Lean form*: `S = Spec D` affine,
`L` a fraction field of `D`; finite type as smooth (locally of finite presentation) and quasi-compact; only the
existence of the extension (uniqueness is automatic, `NeronC.pullback_map_injective`). No group structure is asked
for. `D` is not a field (BLR's Dedekind schemes are one-dimensional; reviewer fix 11-16). The existing field `NeronSchemeExtensionExists` is its case `D = 𝓞_L` (`neronSchemeExtensionExists_of_dedekind`). -/
def NeronSchemeExtensionDedekind : Prop :=
  ∀ (D : Type) [CommRing D] [IsDedekindDomain D] (L : Type) [Field L] [Algebra D L] [IsFractionRing D L]
    (A : AbVar L) (_ : ¬ IsField D),
    ∃ (N : Over (Spec (CommRingCat.of D))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (ε : (Over.pullback (genMap D L)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of D))) [Smooth Y.hom],
        Function.Surjective fun f : Y ⟶ N => (Over.pullback (genMap D L)).map f ≫ ε.hom

/-- **LEAF `NeronSchemeExtensionDVR`**: `NeronSchemeExtensionDedekind` for `D = R` a discrete valuation ring
(`dvr_of_dedekind`); source as there (BLR §1.4 Thm 3 at `S = Spec R`; numbers UNVERIFIED). -/
def NeronSchemeExtensionDVR : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K]
    [IsFractionRing R K] (A : AbVar K),
    ∃ (N : Over (Spec (CommRingCat.of R))) (_ : Smooth N.hom) (_ : IsSeparated N.hom)
      (_ : QuasiCompact N.hom) (ε : (Over.pullback (genMap R K)).obj N ≅ A.X),
      ∀ (Y : Over (Spec (CommRingCat.of R))) [Smooth Y.hom],
        Function.Surjective fun f : Y ⟶ N => (Over.pullback (genMap R K)).map f ≫ ε.hom

theorem dvr_of_dedekind (h : NeronSchemeExtensionDedekind) : NeronSchemeExtensionDVR :=
  fun R _ _ _ K _ _ _ A => h R K A (IsDiscreteValuationRing.not_isField R)

/-- The existing field (BLR §1.4 Thm 3 over `𝓞_L`) is the case `D = 𝓞_L` of the Dedekind form. -/
theorem neronSchemeExtensionExists_of_dedekind (h : NeronSchemeExtensionDedekind) :
    ZInQ.Contrib.NeronC.NeronSchemeExtensionExists :=
  fun K _ A L _ _ _ => h (NumberField.RingOfIntegers L) L (A.baseChange L) (NumberField.RingOfIntegers.not_isField L)

/-! ## §2 The glue -/

/-- **GLUE `NeronGoodModelIso`** (comparison of a good model with a smooth separated model). Let `R` be a DVR with
fraction field `K`, `F → Spec R` proper and smooth with geometrically connected fibres and a section `e`, every field
fibre an abelian variety with origin `e(s)` (the hypotheses of `MumfordGroupLawDVR`), and `N → Spec R` smooth and
separated. Then every `R`-morphism `ψ : F → N` whose base change to `K` is an isomorphism is an isomorphism.

Not a printed statement; to be proved by the project. Proof (STANDARD ingredients, numbers UNVERIFIED): `N` is flat
over `R`, so `N_K ≅ F_K` is dense and `N` is irreducible; `ψ` is proper (`F` proper, `N` separated), so it is
surjective, and `ψ_k : F_k → N_k` is a surjection of `g`-dimensional varieties with `F_k` integral, so `ψ` maps the
generic point `ξ` of `F_k` to that of `N_k`; there both local rings are DVRs of the function field, so `ψ` is a
local isomorphism at `ξ`. By van der Waerden's purity theorem (EGA IV₄ 21.12.12; `N` is regular) the locus where
the birational `ψ` is not a local isomorphism is empty or of pure codimension 1 in `F`, hence contained in, so
equal to, `F_k`; it misses `ξ`, so it is empty. A birational proper local isomorphism is an isomorphism.
(Alternative with the Néron model's group law: `ψ_k` is a homomorphism by rigidity, its kernel trivial because
`ψ` is an isomorphism over the dense open where the inverse rational map is defined; then `ψ` is a closed
immersion by the fibrewise criterion, and surjective.) -/
def NeronGoodModelIso : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F N : Over (Spec (CommRingCat.of R))) (e : Spec (CommRingCat.of R) ⟶ F.left),
    IsProper F.hom → Smooth F.hom → GeometricallyConnected F.hom → e ≫ F.hom = 𝟙 _ →
    (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      ∃ (A : AbVar K) (g : A.X.left ⟶ F.left), IsAbVarFibre F e s A g) →
    Smooth N.hom → IsSeparated N.hom → ∀ ψ : F ⟶ N,
      IsIso ((Over.pullback (genMap R (FractionRing R))).map ψ) → IsIso ψ

/-! ## §3 The proof -/

/-- The fibre at `s` as an isomorphism of `K`-schemes `s^*F ≅ A`. -/
def fibreIso {S : Scheme.{0}} (F : Over S) {K : Type} [Field K] (s : Spec (CommRingCat.of K) ⟶ S)
    (A : AbVar K) (g : A.X.left ⟶ F.left) (hpb : IsPullback g A.X.hom F.hom s) :
    (Over.pullback s).obj F ≅ A.X :=
  Over.isoMk hpb.isoPullback.symm (by simp)

@[reassoc]
lemma fibreIso_hom_left_g {S : Scheme.{0}} (F : Over S) {K : Type} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ S) (A : AbVar K) (g : A.X.left ⟶ F.left)
    (hpb : IsPullback g A.X.hom F.hom s) :
    (fibreIso F s A g hpb).hom.left ≫ g = pullback.fst F.hom s := by
  simp [fibreIso]

lemma spec_algebraMap_self (K : Type) [Field K] :
    Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
  rw [Algebra.algebraMap_self]
  exact Spec.map_id _

/-- **`MumfordGroupLawDVR` from Néron models over a DVR and the comparison glue.** -/
theorem mumfordGroupLawDVR_of_neron (hN : NeronSchemeExtensionDVR) (hI : NeronGoodModelIso) :
    ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR := by
  intro R _ _ _ F e hP hS hGC he hfib
  let K := FractionRing R
  let s0 := genMap R K
  obtain ⟨A, g, hpb, hone⟩ := hfib K s0
  obtain ⟨N, hNS, hNsep, hNqc, ε, hext⟩ := hN R K A
  haveI : IsSchemeTheoreticallyDominant s0 :=
    NeronC.isSchemeTheoreticallyDominant_spec_map _ (IsFractionRing.injective R K)
  have hinj : ∀ (Y : Over (Spec (CommRingCat.of R))) [Flat Y.hom],
      Function.Injective fun f : Y ⟶ N => (Over.pullback s0).map f ≫ ε.hom := by
    intro Y _ f f' h
    exact NeronC.pullback_map_injective s0 Y N ((cancel_mono ε.hom).mp h)
  let φ := fibreIso F s0 A g hpb
  haveI : Smooth F.hom := hS
  obtain ⟨ψ, hψ⟩ := hext F φ.hom
  have hψ' : (Over.pullback s0).map ψ = φ.hom ≫ ε.inv := by
    rw [← cancel_mono ε.hom]
    simpa using hψ
  have hiso : IsIso ((Over.pullback s0).map ψ) := by
    rw [hψ']; infer_instance
  haveI hψi : IsIso ψ := hI R F N e hP hS hGC he hfib hNS hNsep ψ hiso
  letI : GrpObj N := NeronC.grpObjOfNeron (Over.pullback s0) (fun Y => Smooth Y.hom)
    (NeronC.smooth_tensorUnit _) (fun X Y hX hY => NeronC.smooth_tensor X Y hX hY) N hNS A.X ε
    (fun Y hY => ⟨@hinj Y inferInstance, @hext Y hY⟩)
  have he' : e ≫ F.hom = (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := he
  let eO : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ F := Over.homMk e he'
  have hη : η[N] = eO ≫ ψ := by
    apply @hinj (𝟙_ _) (by haveI := NeronC.smooth_tensorUnit (Spec (CommRingCat.of R)); infer_instance)
    have h1 : (Over.pullback s0).map η[N] ≫ ε.hom = 1 :=
      NeronC.nPhi_nPsi (Over.pullback s0) (fun Y => Smooth Y.hom) N A.X ε
        (fun Y hY => ⟨@hinj Y inferInstance, @hext Y hY⟩) (NeronC.smooth_tensorUnit _) 1
    simp only
    rw [h1, Functor.map_comp, Category.assoc, hψ', Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Hom.one_def]
    ext1
    rw [Over.comp_left, Over.comp_left, Over.toUnit_left]
    apply hpb.hom_ext
    · rw [Category.assoc, Category.assoc, fibreIso_hom_left_g]
      have h2 : (1 : A.Pt K).left ≫ g = s0 ≫ e := hone
      rw [Hom.one_def, Over.comp_left, Over.toUnit_left] at h2
      simp only [AbVar.ptObj, Over.mk_hom, spec_algebraMap_self] at h2
      have h4 : Over.Hom.left η[A.X] ≫ g = s0 ≫ e := by
        rw [← h2, Category.assoc]; exact (Category.id_comp _).symm
      rw [h4]
      simp only [eO, Over.pullback_map_left, Over.homMk_left, pullback.lift_fst]
      rw [← Category.assoc]
      congr 1
      exact (pullback.condition (f := (𝟙_ (Over (Spec (CommRingCat.of R)))).hom) (g := s0)).symm
    · simp
  refine ⟨GrpObj.ofIso (asIso ψ).symm, ?_⟩
  change (η[N] ≫ (asIso ψ).symm.hom).left = e
  rw [hη]
  simp [eO]


/-- **The chain's use of the group-law field** (`QMFamilyGroupLaw`) from Néron models over a DVR and the comparison
glue (with group-law's `qmFamilyGroupLaw_of_dvr`). -/
theorem qmFamilyGroupLaw_of_neron (hN : NeronSchemeExtensionDVR) (hI : NeronGoodModelIso) :
    QMFamilyGroupLaw :=
  qmFamilyGroupLaw_of_dvr (mumfordGroupLawDVR_of_neron hN hI)

/-- The same from the Dedekind form of the Néron leaf. -/
theorem qmFamilyGroupLaw_of_neronDedekind (hN : NeronSchemeExtensionDedekind) (hI : NeronGoodModelIso) :
    QMFamilyGroupLaw :=
  qmFamilyGroupLaw_of_neron (dvr_of_dedekind hN) hI

/-- `MumfordGroupLawDVR` from the old field `MumfordGroupLawConn` (the spectrum of a DVR is connected and
noetherian), for the narrowing fold. -/
theorem dvr_of_conn (h : DictModels.MumfordConn.MumfordGroupLawConn) :
    ZInQ.Contrib.GroupLaw.MumfordGroupLawDVR :=
  fun R _ _ _ F e h1 h2 h3 h4 h5 => h _ F e inferInstance inferInstance h1 h2 h3 h4 h5

end ZInQ.Contrib.GroupLawNeron

#print axioms ZInQ.Contrib.GroupLawNeron.mumfordGroupLawDVR_of_neron
#print axioms ZInQ.Contrib.GroupLawNeron.qmFamilyGroupLaw_of_neronDedekind
#print axioms ZInQ.Contrib.GroupLawNeron.neronSchemeExtensionExists_of_dedekind
#print axioms ZInQ.Contrib.GroupLawNeron.dvr_of_conn
