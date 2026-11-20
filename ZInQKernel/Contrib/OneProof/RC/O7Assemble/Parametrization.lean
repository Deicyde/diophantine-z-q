import ZInQKernel.Contrib.OneProof.RC.PicardFibers.Assembly
import ZInQKernel.Contrib.OneProof.RC.TorusWeights.Actual

/-! The adelic frame read for the orbit of a specified representative.
This adapter is on-the-spot (c), for tex 9155–9179. -/

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain IsDedekindDomain.FiniteAdeleRing

namespace ZInQ.Manuscript.RC.O7Assemble

open Eichler Adelic O7Actual O7Orbits PicardFibers Visibility

set_option maxHeartbeats 400000 in
/-- A known adelic orbit has a presentation in the very same rational left
order representative read by the theta weights. The orbit equality is
separate from the rational frame change. -/
theorem framePresents {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D : ℤ}
    (s : StageAt O N M hN m) (H : SupportBridge s D)
    {x₀ α : B (-1) (-(s.ell : ℚ))} (hα : 2 * α - 1 = x₀) (hx : x₀.re = 0)
    (hn : nrd x₀ = index s D) (z : FiniteUnits (O7Orbits.ActualOrder s))
    (hz : AdelicAdmissible α z) (P : OrbitSet s.visibility (index s D))
    (hP : P = orbitFromRep s H hα hx hn ⟨z, hz⟩) :
    ∃ q : (B (-1) (-(s.ell : ℚ)))ˣ,
      (Eichler.representative P.1).val = (fromAdelic z).val.translate q ∧
      ∃ x : s.visibility.supp P.1 (index s D),
        x.val = q.val * x₀ * (↑q⁻¹ : B (-1) (-(s.ell : ℚ))) ∧ Quotient.mk _ x = P.2 := by
  subst P
  let q := (exists_frame z).choose
  let r := (exists_frame z).choose_spec.choose
  let hf := (exists_frame z).choose_spec.choose_spec
  refine ⟨q, ?_, supportFromFrame s H hα hx hn hz q r hf, rfl, rfl⟩
  change (Eichler.representative (adelicClass z)).val = (fromAdelic z).val.translate q
  rw [← fromAdelic_classRepresentative (adelicClass z)]
  exact (fromAdelic_translate_iff z (classRepresentative (adelicClass z)) q).mpr ⟨r, hf⟩

section Chart

variable {O : Type} [CommRing O] {N M : ℕ} {hN : 0 < N} {m D : ℤ}
    {F : Type} [Field F] [NumberField F]
    (s : StageAt O N M hN m) (A : AdmissibleD s D) (H : SupportBridge s D)
    (hh : legendreSym s.ell (-(s.weights.m : ℤ)) = -1)
    (Q : QuadraticBasis F (disc s D)) (ι : F →ₐ[ℚ] B (-1) (-(s.ell : ℚ)))
    (T : ∀ p, Nonempty (LocalTorusChart (ActualOrder s) ι
      (referenceUnit s A Q ι) (referenceAffine s Q ι) p))
    (L : ∀ t, HasLocalRealizations s (referenceAffine s Q ι) t)

/-- The base for each tuple is the choice used in `picardFibers_of_local`. -/
abbrev tupleBase (t : Orientations N.primeFactors.card) :
    {z : FiniteUnits (ActualOrder s) // AdelicAdmissible (referenceAffine s Q ι) z} :=
  (realize_tuple s A H (referenceAffine_spec s A Q ι) (referenceUnit_sphere s A Q ι).1
    (referenceUnit_sphere s A Q ι).2 t (L t)).choose

/-- Use the same torus chart and the same base at the zero tuple as the
Picard orbit construction. -/
abbrev chartEquiv :
    (FiniteAdeleRing (𝓞 F) F)ˣ ≃*
      adelicCentralizer (ActualOrder s) (diagonal (ActualOrder s) (referenceUnit s A Q ι)).val :=
  let z := tupleBase s A H Q ι L (fun _ => false)
  ideleCentralizerEquiv (ActualOrder s) ι (referenceUnit s A Q ι) (referenceAffine s Q ι)
    (fun p => (T p).some) z.val z.prop

/-- The embedded chosen idele times the chosen tuple representative. -/
abbrev classFrame (a : (FiniteAdeleRing (𝓞 F) F)ˣ) (t : Orientations N.primeFactors.card) :
    {z : FiniteUnits (ActualOrder s) // AdelicAdmissible (referenceAffine s Q ι) z} :=
  let z := tupleBase s A H Q ι L t
  let e := chartEquiv s A H Q ι T L
  ⟨(e a).val * z.val, centralizer_mul_admissible _ (referenceUnit s A Q ι)
    (referenceAffine_spec s A Q ι) (e a) z.prop⟩

/-- The computation still required of the Picard quotient: its class
label on a specified idele reads the orbit of that idele times the base. -/
def OrbitRead (a : ClassGroup (𝓞 F) → (FiniteAdeleRing (𝓞 F) F)ˣ) : Prop :=
  ∀ t c, (orbitFibers_of_local s A H hh Q ι T L).param (t, c) =
    orbitFromRep s H (referenceAffine_spec s A Q ι) (referenceUnit_sphere s A Q ι).1
      (referenceUnit_sphere s A Q ι).2 (classFrame s A H Q ι T L (a c) t)

variable (a : ClassGroup (𝓞 F) → (FiniteAdeleRing (𝓞 F) F)ˣ)
    (ha : ∀ c, toClassGroup (𝓞 F) F (a c) = c)
    (hr : OrbitRead s A H hh Q ι T L a)

set_option maxHeartbeats 600000 in
/-- Supply the weight parametrization from the existing chart, tuple
representatives and an equality of the two orbit readings. -/
def torusParametrization :
    TorusWeights.TorusParametrization s D Q (orbitFibers_of_local s A H hh Q ι T L) where
  embedding := ι
  embedIdeles := (adelicCentralizer (ActualOrder s)
    (diagonal (ActualOrder s) (referenceUnit s A Q ι)).val).subtype.comp
      (chartEquiv s A H Q ι T L).toMonoidHom
  base t := (tupleBase s A H Q ι L t).val
  idele := a
  idele_class := ha
  centralizes k p := by
    exact ((chartEquiv s A H Q ι T L k).prop p).map
      (Units.coeHom (Bp p.val (-1) (-(s.ell : ℚ))))
  presents t c := by
    let z := classFrame s A H Q ι T L (a c) t
    exact framePresents s H (referenceAffine_spec s A Q ι) (referenceUnit_sphere s A Q ι).1
      (referenceUnit_sphere s A Q ι).2 z.val z.prop _ (hr t c)

set_option maxHeartbeats 500000 in
/-- A block equal to one is sent to one by these local charts. -/
theorem torusParametrization_block_one (u : (FiniteAdeleRing (𝓞 F) F)ˣ) (p : Prime)
    (hu : idelePrimeBlocks F u p = 1) :
    ((torusParametrization s A H hh Q ι T L a ha hr).embedIdeles u).val p = 1 := by
  change ((T p).some.units (idelePrimeBlocks F u p)).val = 1
  rw [hu, map_one]
  rfl

end Chart

end ZInQ.Manuscript.RC.O7Assemble
