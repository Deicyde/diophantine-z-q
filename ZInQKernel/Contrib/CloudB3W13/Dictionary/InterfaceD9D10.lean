/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
import ZInQKernel.Contrib.CloudB3W13.Dictionary.InterfaceD6D7

/-!
# W13 dictionary interfaces D9, D10 (UNPROVED obligations, stated as `Prop`s)

The last two clauses of `HDec.CurveSplitGR.IsShimuraModelNoGuard` (`OneProof/H/TailW.lean`), stated
over the actual FLT fine moduli scheme `𝒴 := Over.mk πM` and ANY kernel family `𝒜` over `M` with the
D7 fibre property (so they can be proved independently of how D7 is proved).

* **D9** (`rightMul`): for every unit `u ∈ 𝒪ˣ` there is an automorphism `g` of `𝒴` such that the fibre
  at `y ≫ g` is (up to isomorphism) the right-multiplication twist by `u` of the fibre at `y`.
  Expected route: `IsLevelTwistAction` (FLT `exists_isLevelTwistAction`, `label_surjective` with
  `c = u`, `d = u⁻¹`), the FLT lemma producing `IsTwist` partners, D6, and fibre uniqueness.
* **D10** (`twist`): the same for `α ∈ Aut(𝒪)` and `M3.twist α`; needs the functor `E ↦ E^α`
  (`act ∘ α`, same `P`, `act_trace` preserved since `α` preserves the reduced trace) and the
  Yoneda statement FLT `existsUnique_hom_ptF_comp_eq`. OPEN (no hidden premise).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB2Shimura.Dictionary

open CategoryTheory AlgebraicGeometry Limits
open scoped Quaternion
open ZInQ.Contrib.CloudW03NeronSurj

/-- The D7 fibre property of a kernel family `𝒜` over the FLT moduli scheme `M`. -/
def HasFLTFibres (𝒪 : Type) [CommRing 𝒪] {M : Scheme.{0}} (πM : M ⟶ Spec (CommRingCat.of 𝒪))
    (ptF : PtF 𝒪 πM) (𝒜 : LeafQM.AV.QMFamily M) : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of 𝒪))
    (u : FLTL3 K) (h : AbVarProps u.1) (hs : (abVarOfFakeEC u.1 h).dim = 2)
    (q : LeafQM.AV.QMStr (abVarOfFakeEC u.1 h)) (e : LeafQM.AV.Level3 q),
    IsPackaging u h q e → LeafQM.AV.IsFibreOf 𝒜 (ptF K s u).1 ⟨abVarOfFakeEC u.1 h, hs, q, e⟩

/-- **D9 (UNPROVED obligation; `rightMul` clause).** Hypotheses: those of D7 and a family with the
D7 fibre property. Conclusion: clause 7 of `IsShimuraModelNoGuard` for `𝒴 = Over.mk πM`. -/
def D9_Obligation : Prop :=
  ∀ (𝒪 : Type) [CommRing 𝒪], IsUnit ((2 : ℕ) : 𝒪) → IsUnit ((3 : ℕ) : 𝒪) →
  ∀ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ptF : PtF 𝒪 πM),
    FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF →
    ∀ 𝒜 : LeafQM.AV.QMFamily M, HasFLTFibres 𝒪 πM ptF 𝒜 →
    ∀ u : (LeafQM.O)ˣ, ∃ g : Over.mk πM ≅ Over.mk πM,
      ∀ (y : Spec (CommRingCat.of LeafQM.AV.Qbar) ⟶ M) (P P' : LeafQM.AV.QML3 LeafQM.AV.Qbar),
        LeafQM.AV.IsFibreOf 𝒜 y P → LeafQM.AV.IsFibreOf 𝒜 (y ≫ g.hom.left) P' →
          LeafQM.AV.M3.mk P' = LeafQM.AV.M3.rightMul u (LeafQM.AV.M3.mk P)

/-- **D10 (UNPROVED obligation, OPEN; `twist` clause).** Same hypotheses; clause 6 of
`IsShimuraModelNoGuard` for `𝒴 = Over.mk πM`. -/
def D10_Obligation : Prop :=
  ∀ (𝒪 : Type) [CommRing 𝒪], IsUnit ((2 : ℕ) : 𝒪) → IsUnit ((3 : ℕ) : 𝒪) →
  ∀ (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of 𝒪)) (ptF : PtF 𝒪 πM),
    FLT.CerednikDrinfeld.QM.IsFineModuli Λ 1 3 M πM ptF →
    ∀ 𝒜 : LeafQM.AV.QMFamily M, HasFLTFibres 𝒪 πM ptF 𝒜 →
    ∀ α : LeafQM.O ≃+* LeafQM.O, ∃ g : Over.mk πM ≅ Over.mk πM,
      ∀ (y : Spec (CommRingCat.of LeafQM.AV.Qbar) ⟶ M) (P P' : LeafQM.AV.QML3 LeafQM.AV.Qbar),
        LeafQM.AV.IsFibreOf 𝒜 y P → LeafQM.AV.IsFibreOf 𝒜 (y ≫ g.hom.left) P' →
          LeafQM.AV.M3.mk P' = LeafQM.AV.M3.twist α (LeafQM.AV.M3.mk P)

/-- **Fibre uniqueness (UNPROVED kernel-side lemma used by D8/D9/D10).** Two kernel objects that are
both fibres of the same family at the same `ℚ̄`-point are isomorphic. (The pullback isomorphism
respects `ι` and `η`; that it is a homomorphism of abelian varieties needs rigidity: it preserves the
identity `η 0`.) Purely kernel; no FLT input. -/
def FibreUnique_Obligation : Prop :=
  ∀ (S : Scheme.{0}) (𝒜 : LeafQM.AV.QMFamily S) (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ S) (P P' : LeafQM.AV.QML3 K),
    LeafQM.AV.IsFibreOf 𝒜 y P → LeafQM.AV.IsFibreOf 𝒜 y P' → LeafQM.AV.M3.mk P = LeafQM.AV.M3.mk P'

end ZInQ.Contrib.CloudB2Shimura.Dictionary
