import ZInQKernel.Contrib.OneProof.RC.TraceLimits.Limits
import ZInQKernel.Contrib.OneProof.RC.AddressGenuine.Constituents

/-!
# The finite trace quotients

Tex 9663–9668, 9524–9554, 9919–9921. The uniformity argument for the right
periods uses compactness of the absolute Galois group (on-the-spot, provenance (c)).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.TraceLimits

open AddressGenuine
open ZInQ.Manuscript.RC.Symbols ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Contrib.CloudB3RC53.CoefficientDictionary
open scoped MatrixGroups

variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2}
variable {I K O : Type} [Field K] [CommRing O] [Algebra O K]
variable {chiType : GalQ →* Multiplicative L}
variable {ρ : I → GalQ →* GL (Fin 2) K} {Λ : Submodule O (I → K)}
variable {m : Ideal O} {F : Finset ℕ → Λ}

/-- Continuity of the type character at one, in terms of the Krull basis. For the
tree's type characters use `exists_fixingSubgroup_le_ker_typChar` or
`exists_fixingSubgroup_le_ker_stageChar` (tex 2016–2025). -/
def OpenTypeKernel (chiType : GalQ →* Multiplicative L) : Prop :=
  ∃ E : IntermediateField ℚ Qbar, FiniteDimensional ℚ E ∧
    ∀ σ ∈ E.fixingSubgroup, chiType σ = 1

variable [TopologicalSpace K] [IsTopologicalRing K]

/-- The defining subgroup `N_U` is open if lattice reduction is discrete and the
constituent trace is continuous (tex 9663–9668). This applies to every finite `U`. -/
theorem consN_isOpen (hchi : OpenTypeKernel chiType)
    (hmathfrak : IsOpen ((m • (⊤ : Submodule O Λ) : Submodule O Λ) : Set Λ))
    (hst : ∀ g, ∀ v ∈ Λ, tV ρ g v ∈ Λ)
    (hcont : ContinuousOperators ρ Λ) (U : Finset ℕ) :
    IsOpen (consN chiType m ρ Λ F U : Set GalQ) := by
  classical
  let H := (chiType.prod (MonoidHom.pi fun s : U => bitChar s)).ker
  have hH : IsOpen (H : Set GalQ) := by
    obtain ⟨E₀, hE₀, h₀⟩ := hchi
    obtain ⟨E₁, hE₁, h₁⟩ := exists_fixingSubgroup_le_ker_bitChar U
    apply (subgroup_isOpen_iff H).2
    refine ⟨E₀ ⊔ E₁, inferInstance, fun σ hσ => MonoidHom.mem_ker.2 ?_⟩
    exact Prod.ext (h₀ _ (IntermediateField.fixingSubgroup_antitone le_sup_left hσ))
      (funext fun s => h₁ _ (IntermediateField.fixingSubgroup_antitone le_sup_right hσ) s s.2)
  let trace (W : Finset ℕ) (g : GalQ) : Λ := ⟨tV ρ g (F W), hst g _ (F W).2⟩
  let P : Submodule O Λ := m • ⊤
  have ht (W : Finset ℕ) : IsOpen {n : GalQ | ∀ g, trace W (g * n) - trace W g ∈ P} :=
    isOpen_rightPeriods (trace W) ((hcont.trace (F W)).subtype_mk _)
      P.toAddSubgroup hmathfrak
  convert hH.inter (isOpen_iInter_of_finite (fun W : U.powerset => ht W)) using 1
  ext n
  rw [Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · intro hn
    refine ⟨MonoidHom.mem_ker.2 (Prod.ext hn.1 (funext fun s => hn.2.1 s s.2)), ?_⟩
    intro W g
    obtain ⟨w, hw, he⟩ := hn.2.2 g W (Finset.mem_powerset.1 W.2)
    exact (Subtype.ext he : w = trace W (g * n) - trace W g) ▸ hw
  · rintro ⟨hn, hp⟩
    have e := MonoidHom.mem_ker.1 hn
    refine ⟨congrArg Prod.fst e, fun s hs => congrFun (congrArg Prod.snd e) ⟨s, hs⟩,
      fun g W hW => ?_⟩
    let w : U.powerset := ⟨W, Finset.mem_powerset.2 hW⟩
    exact ⟨trace W (g * n) - trace W g, hp w g, rfl⟩

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- An open constituent subgroup has finite index (tex 9663–9668). -/
theorem consN_finiteIndex (U : Finset ℕ) (hopen : IsOpen (consN chiType m ρ Λ F U : Set GalQ)) :
    (consN chiType m ρ Λ F U).FiniteIndex := by
  obtain ⟨E, hE, hEN⟩ := (subgroup_isOpen_iff _).1 hopen
  exact finiteIndex_of_fixingSubgroup_le _ E hEN

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- Inertia outside the fixed support and a good set `U` lies in `N_U` when the
constituent representations are unramified there (tex 9524–9554). -/
theorem inertia_le_consN (T : TypeData L ε) {avoid : Finset ℕ}
    (htyp : IsTypeChar T chiType) (hunr : UnramifiedConstituents T avoid ρ)
    {U : Finset ℕ} (hU : ∀ s ∈ U, T.Good s) {q : ℕ} (hq : T.Good q)
    (hqu : q ∉ U) (hqa : q ∉ avoid) {Q : Ideal Zbar} (hQ : Q.IsMaximal)
    (hqQ : ((q : ℤ) : Zbar) ∈ Q) : Q.inertia GalQ ≤ consN chiType m ρ Λ F U := by
  intro σ hσ
  obtain ⟨hc, hb⟩ := chars_eq_one_of_mem_inertia T htyp hU hq hqu hQ hqQ hσ
  refine ⟨hc, hb, fun g W _ => ?_⟩
  have e : tV ρ (g * σ) (F W) = tV ρ g (F W) := by
    funext i
    simp [tV, map_mul, hunr q hq hqa Q hQ hqQ σ hσ i]
  rw [e, sub_self]
  exact Submodule.zero_mem _

omit [TopologicalSpace K] [IsTopologicalRing K] in
/-- The constituent model's Chebotarev field follows from the tree's density theorem,
openness and the known ramification of its constituents (tex 9666–9668, 9919–9921). -/
theorem consN_chebotarev (T : TypeData L ε) {avoid : Finset ℕ} {frob : ℕ → GalQ}
    (htyp : IsTypeChar T chiType) (hfrob : ∀ q, T.Good q → IsFrobAt (frob q) q)
    (hunr : UnramifiedConstituents T avoid ρ) (U : Finset ℕ) (hU : ∀ s ∈ U, T.Good s)
    (hopen : IsOpen (consN chiType m ρ Λ F U : Set GalQ)) (g : GalQ) (S : Finset ℕ) :
    ∃ q h, ∃ n ∈ consN chiType m ρ Λ F U, T.Good q ∧ q ∉ S ∧ frob q = h * g * h⁻¹ * n := by
  obtain ⟨E, hE, hEN⟩ := (subgroup_isOpen_iff _).1 hopen
  obtain ⟨q, h, n, hn, hq, hqa, -, -, e⟩ :=
    exists_frob_eq_conj_mul T hfrob (consN chiType m ρ Λ F U) U avoid E hEN
      (fun _ hq hqu hqa _ hQ hqQ => inertia_le_consN T htyp hunr hU hq hqu hqa hQ hqQ) g S
  exact ⟨q, h, n, hn, hq, hqa, e⟩

/-- The openness result on constituents gives the tree's `GalNOpen` formulation
for the reduced operators and forms. -/
theorem galNOpen_of_consN_open {T : TypeData L ε} {R : Finset ℕ → ZMod 2} {ap : ℕ → ℤ} {B : ℕ}
    (X : GaloisConstituentModel T R ap B chiType)
    (h : ∀ U : Finset ℕ, (∀ s ∈ U, T.Good s) → IsOpen (X.N U : Set GalQ)) :
    letI := X.modMred
    GalNOpen T chiType X.tM X.FM := by
  letI := X.modMred
  change GalNOpen T chiType X.tM X.FM
  intro U hU
  rw [← X.consN_eq_galN U]
  exact (subgroup_isOpen_iff _).1 (h U hU)

#print axioms consN_isOpen
#print axioms consN_finiteIndex
#print axioms inertia_le_consN
#print axioms consN_chebotarev
#print axioms galNOpen_of_consN_open

end ZInQ.Manuscript.RC.TraceLimits
