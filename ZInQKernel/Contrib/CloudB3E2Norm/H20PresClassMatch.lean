import ZInQKernel.Contrib.CloudB3E2Norm.H20PresClassOf
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate16Frob

/-!
# The actual Heegner classes at the places of a switch, and the condition on the character

Manuscript `diophantine_zq.tex`, tex 2847–2855 (the finite character `θ` of `Δ_f`), 3204–3215
(H20, H21), 4142–4194 (Lemma `ex:arith-common-coordinate`; "Conjugation sends `z` to `z⁻¹`",
tex 4171).

**The place matching.** `H20PresClassOf.gx_step_heegner` gives the step identity at the places
over the anchor's prime `𝔮 ∣ q`, a prime that the print does not name. Lane RC32's presentation
fixes the two places `w₀ = place (p, false)`, `w₁ = place (p, true)` above `q`
(`SplitPlacesAt`: every prime containing `q` is one of them) with
`AnticyclotomicAt α w₀ w₁` (`α(Frob_{w₁}) = α(Frob_{w₀})⁻¹`, lane RC32's
`anticyclotomicAt_of_conj`). **`gx_step_heegner_at`** (PROVED): the step identity holds with the
factor `pointFactor a_q z z⁻¹`, `z = α(Frob_{w₀})`, whichever of `w₀`, `w₁` the anchor's prime is
(`pointFactor_swap`: the factor is symmetric).

**The condition on the character.** The transfer from `H_d` needs `θ = χ_h [π]` trivial on
`G_{H_d}`. The text takes `θ` to be a character of `Δ_f = Gal(H_f/K)` for one conductor `f` and
states this as a hypothesis on the actual finite character ("These are hypotheses on the actual
finite character. Its construction is separate from the descent proved here", tex 2847–2855).
**`ThetaOfDelta f`** (ELLIOT, definition): `χ_h [π]` is trivial on the elements fixing `H_f`. It
splits as `QuadOfDelta f` (genus theory) and `PiOfDelta f` (the moving character factors through
`Gal(H_f/K)`), `thetaOfDelta_of` (PROVED). **`hα_of_theta`** (PROVED): it gives the condition `hα`
of `heegnerActual` at every conductor `d` with `f ∣ d` (`H_f ⊆ H_d`, `RingClassMono`), in particular
at `d` and at `dq` from the one hypothesis. Deriving `ThetaOfDelta` itself is genus theory for the
order of conductor `f` (`K(√q*) ⊆ H_q` for the primes of `h`, through the Artin map of `H_f`)
together with the construction of the moving character, outside this file.

Kinds: definitions, ELLIOT (`ThetaOfDelta`), PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Contrib.CloudB3RC53.HeegnerCohomology.TwistedTransfer
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.KummerMaps ZInQ.Manuscript.RC.Limits
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)
open ZInQ.Manuscript.RC.Central (pointFactor)
open ZInQ.Contrib.CloudB3RC53.UnramifiedComplex ZInQ.Contrib.CloudB3RC53.RankCounts
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve
open ZInQ.Manuscript.RC.PrintsArith ZInQ.Contrib.CloudB3RC53.CST
open TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open scoped WeierstrassCurve

attribute [local instance] TopRep.distribMulAction TopRep.smulCommClass groupRingTop ptSAction

set_option linter.unusedSectionVars false

/-! ### The condition on the character -/

section Theta

variable {K : Type} [Field K] [NumberField K] {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h1 : S₁ ⊆ S) (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h)
  (hs0 : s ≠ 0) {Δ : Type} [CommGroup Δ] (π : GKS K S₀ →* Δ)

/-- `ℤ + d𝒪_K ⊆ ℤ + f𝒪_K` for `f ∣ d`. Kind: PROVED. -/
theorem conductorOrder_le_of_dvd {f d : ℕ} [NeZero f] [NeZero d] (hfd : f ∣ d) :
    (conductorOrder K d).toSubalgebra ≤ (conductorOrder K f).toSubalgebra := by
  obtain ⟨c, rfl⟩ := hfd
  rintro x ⟨a, y, rfl⟩
  exact ⟨a, (c : 𝓞 K) * y, by push_cast; ring⟩

/-- **`θ = χ_h [π]` is a character of `Δ_f = Gal(H_f/K)`** (ELLIOT, a hypothesis on the actual
finite character, tex 2847–2855): it is trivial on the elements of `G_{K,S}` fixing the ring
class field `H_f` (read in `K_{S₁}`). Kind: definition. -/
def ThetaOfDelta (f : ℕ) [NeZero f] : Prop :=
  ∀ g : GKS K S, (∀ z : KS K S₁,
      (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K f)) →
        galS K S₁ (inflMap K h1 g) z = z) →
    alphaInfl hS s hs hs0 π g = 1

/-- **The quadratic part of `ThetaOfDelta`** (ELLIOT; genus theory, `K(√h) ⊆ H_f`, tex 2847–2855):
`χ_h` is trivial on the elements fixing `H_f`. Kind: definition. -/
def QuadOfDelta (f : ℕ) [NeZero f] : Prop :=
  ∀ g : GKS K S, (∀ z : KS K S₁,
      (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K f)) →
        galS K S₁ (inflMap K h1 g) z = z) →
    quadChar s hs hs0 (inflMap K hS g) = 1

/-- **The moving part of `ThetaOfDelta`** (ELLIOT; the moving character factors through
`Gal(H_f/K)`, tex 2847–2855, 3500–3506): `π` is trivial on the elements fixing `H_f`.
Kind: definition. -/
def PiOfDelta (f : ℕ) [NeZero f] : Prop :=
  ∀ g : GKS K S, (∀ z : KS K S₁,
      (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K f)) →
        galS K S₁ (inflMap K h1 g) z = z) →
    π (inflMap K hS g) = 1

/-- `ThetaOfDelta` from its two parts (PROVED). -/
theorem thetaOfDelta_of [Finite Δ] (f : ℕ) [NeZero f] (hq : QuadOfDelta hS h1 s hs hs0 f)
    (hp : PiOfDelta hS h1 π f) : ThetaOfDelta hS h1 s hs hs0 π f := by
  intro g hg
  let := Fintype.ofFinite Δ
  apply Units.ext
  change ((alphaShap s hs hs0 π (inflMap K hS g) : (MonoidAlgebra ℤ Δ)ˣ) :
    MonoidAlgebra ℤ Δ) = 1
  rw [alphaShap_val, hq g hg, hp g hg]
  simp only [Units.val_one, Int.cast_one, one_mul]
  rfl

/-- **The condition `hα` from `ThetaOfDelta f` at every conductor `d` with `f ∣ d`** (PROVED;
`H_f ⊆ H_d`). -/
theorem hα_of_theta {S'' : Set (HeightOneSpectrum (𝓞 K))} (h'' : S'' ⊆ S₁) (f : ℕ) [NeZero f]
    (hθ : ThetaOfDelta hS h1 s hs hs0 π f) {d : ℕ} [NeZero d] (hfd : f ∣ d)
    (hSd : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ S'') :
    fixH (h''.trans h1) (heegnerL d hSd) ≤ (alphaInfl hS s hs hs0 π).ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  apply hθ g
  intro z hz
  have hzd : (z : AlgebraicClosure K) ∈ toAlgClosure (ringClassField (conductorOrder K d)) :=
    IntermediateField.map_mono _ (ringClassField_mono (conductorOrder_le_of_dvd hfd)) hz
  have hzT : (z : AlgebraicClosure K) ∈ unramifiedOutside K S'' :=
    ringClassField_le_KS _ S'' (cond_primes d hSd) hzd
  have hz' : (⟨z, hzT⟩ : KS K S'') ∈ heegnerL d hSd := (mem_heegnerL d hSd _).2 hzd
  rw [mem_fixH, inflMap_trans h'' h1 g] at hg
  have e := ksIncl_infl h'' (inflMap K h1 g) ⟨z, hzT⟩
  rw [hg _ hz'] at e
  have hz0 : (ksIncl h'' ⟨z, hzT⟩ : KS K S₁) = z := Subtype.ext rfl
  rw [hz0] at e
  exact e.symm

end Theta

/-- **The point factor is symmetric** in `z`, `z⁻¹` (PROVED). -/
theorem pointFactor_swap {R : Type} [CommRing R] (a z zi : R) :
    pointFactor a zi z = pointFactor a z zi := by
  simp only [pointFactor]
  ring

/-! ### The step identity at the places of the presentation -/

section At

attribute [local instance] mcoefModuleK

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ S₁ : Set (HeightOneSpectrum (𝓞 K))}
  (hS : S₀ ⊆ S) (h01 : S₀ ⊆ S₁) (h1 : S₁ ⊆ S) [(E.baseChange K).IsElliptic] (i : ℕ)
  [NeZero i] (s : KS K S₀) {h : K} (hs : s ^ 2 = algebraMap K (KS K S₀) h) (hs0 : s ≠ 0)
  (hFull : FullTorsion K S₀ (E.baseChange K) (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  {Δ : Type} [CommGroup Δ] [Finite Δ] (π : GKS K S₀ →* Δ) (ψ : Δ →* (Acoef i)ˣ)
  [IsOpenKer (alphaShap s hs hs0 π)] [IsOpenKer (alphaStage i s hs hs0 π ψ)]
  (P : Set (HeightOneSpectrum (𝓞 K))) (hψ : Function.Injective ψ) (hΨ : PsiTrivialAt2N i π ψ P)
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k] [StageIsoA k i]
  [DecidableEq (Places K S₀)] {ι : Type} [DecidableEq ι] (place : ι × Bool → Places K S)

/-- **The step identity for the actual Heegner points at the places of the presentation**
(PROVED from the anchored norm relations and the ELLIOT `ThetaOfDelta f`,
tex 2847–2855, 2914–2936, 4157–4172). For the two places `w₀`, `w₁` above the split prime `q`
of the switch (every prime containing `q` is one of them, `SplitPlacesAt.above`) with
`AnticyclotomicAt α w₀ w₁`, and `f ∣ d`, the classes of the constructed actual Heegner points
satisfy `g_R = pointFactor a_q z z⁻¹ · g_T + d b` with `z = α(Frob_{w₀})`. -/
theorem gx_step_heegner_at {cp : CSTParam E} {emb : Qbar →ₐ[ℚ] ℂ}
    {κ : Qbar ≃ₐ[ℚ] AlgebraicClosure K}
    (hnorm : ∃ D : HeegnerPointData E, D.NormRelations ∧ FullAnchor E K cp emb κ D) :
    ∃ D : HeegnerPointData E, ∃ hA : FullAnchor E K cp emb κ D, D.NormRelations ∧
      ∀ {d q : ℕ} [NeZero d] [NeZero q] (hadm : D.Admissible d q) (_ : jacobiSym D.DK q = 1)
        {Tp : Finset ι} {p : ι} {ST SR : Set (HeightOneSpectrum (𝓞 K))}
        (hT : ST ⊆ S₁) (hR : SR ⊆ S₁)
        (hSdT : ∀ v : HeightOneSpectrum (𝓞 K), (d : 𝓞 K) ∈ v.asIdeal → v ∈ ST)
        (hSdR : ∀ v : HeightOneSpectrum (𝓞 K), ((d * q : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ SR)
        (hmT : ∀ v : HeightOneSpectrum (𝓞 K), ((2 ^ i : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ ST)
        (hmR : ∀ v : HeightOneSpectrum (𝓞 K), ((2 ^ i : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ SR)
        (hgoodT : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ ST →
          ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt (E.baseChange K) v)
        (hgoodR : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SR →
          ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt (E.baseChange K) v)
        (f : ℕ) [NeZero f] (hθ : ThetaOfDelta hS h1 s hs hs0 π f) (hfd : f ∣ d)
        (hplT : ∀ j, j.1 ∉ Tp → (place j).1 ∉ ST)
        (hplR : ∀ j, j.1 ∉ insert p Tp → (place j).1 ∉ SR)
        (w₀ w₁ : NewPlaces K S₀ S)
        (_ : ∀ I : Ideal (𝓞 K), I.IsPrime → (q : 𝓞 K) ∈ I →
          I = w₀.1.asIdeal ∨ I = w₁.1.asIdeal)
        (_ : AnticyclotomicAt (alphaStage i s hs hs0 π ψ) w₀ w₁)
        (_ : ∀ w ∈ [w₀, w₁], (d : 𝓞 K) ∉ w.1.asIdeal ∧
          w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
            (ZInQ.Contrib.CloudB3RC53.CST.conductorOrder K d).conductorModulus ∧
          w.1.asIdeal ∈ TauCeti.GlobalNumberFields.integralIdealsPrimeTo
            (ZInQ.Contrib.CloudB3E1RingClass.ringClassOrder (K := K) d
              (NeZero.ne d)).conductorModulus),
            ∃ bG : (globalCx k (GKS K S) (MinS hS (E.baseChange K) i
                (alphaStage i s hs hs0 π ψ))).X 0,
              gx hS h01 h1 (E.baseChange K) i s hs hs0 hFull π ψ P k place
                  (heegnerActual E hS h01 h1 i s hs hs0 hFull π ψ P hψ hΨ place hA hR (d * q)
                    (admissible_coprime_dq hadm) hSdR hmR hgoodR
                    (hα_of_theta hS h1 s hs hs0 π hR f hθ (hfd.mul_right q) hSdR) hplR) =
                pointFactor ((E.LFunction q : ℤ) : k)
                    ((eK k i).symm (alphaStage i s hs hs0 π ψ (urFrobElt K w₀) : Acoef i))
                    ((eK k i).symm (((alphaStage i s hs hs0 π ψ (urFrobElt K w₀))⁻¹ :
                      (Acoef i)ˣ) : Acoef i)) •
                  gx hS h01 h1 (E.baseChange K) i s hs hs0 hFull π ψ P k place
                    (heegnerActual E hS h01 h1 i s hs hs0 hFull π ψ P hψ hΨ place hA hT d
                      (admissible_coprime_d hadm) hSdT hmT hgoodT
                      (hα_of_theta hS h1 s hs hs0 π hT f hθ hfd hSdT) hplT) +
                (globalCx k (GKS K S) (MinS hS (E.baseChange K) i
                  (alphaStage i s hs hs0 π ψ))).d 0 1 rfl bG := by
  obtain ⟨D, hA, hD, hall⟩ := gx_step_heegner E hS h01 h1 i s hs hs0 hFull π ψ P hψ hΨ k place
    hnorm
  refine ⟨D, hA, hD, fun {d q} _ _ hadm hsplit Tp p ST SR hT hR hSdT hSdR hmT hmR hgoodT hgoodR f _
    hθ hfd hplT hplR w₀ w₁ habove hanti hwd => ?_⟩
  obtain ⟨𝔮, hq, hw⟩ := hall hadm hsplit hT hR hSdT hSdR hmT hmR hgoodT hgoodR
    (hα_of_theta hS h1 s hs hs0 π hT f hθ hfd hSdT)
    (hα_of_theta hS h1 s hs hs0 π hR f hθ (hfd.mul_right q) hSdR) hplT hplR
  rcases habove 𝔮.asIdeal 𝔮.isPrime hq with h₀ | h₁
  · obtain ⟨a₁, a₂, a₃⟩ := hwd w₀ (by simp)
    exact hw w₀ (HeightOneSpectrum.ext h₀.symm) a₁ a₂ a₃
  · obtain ⟨a₁, a₂, a₃⟩ := hwd w₁ (by simp)
    obtain ⟨bG, hbG⟩ := hw w₁ (HeightOneSpectrum.ext h₁.symm) a₁ a₂ a₃
    refine ⟨bG, ?_⟩
    rw [hbG]
    unfold AnticyclotomicAt at hanti
    rw [hanti, inv_inv, pointFactor_swap]

end At

end ZInQ.Contrib.CloudB3E2.NormCochain
