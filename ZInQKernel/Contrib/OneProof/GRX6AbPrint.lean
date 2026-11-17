import ZInQKernel.Contrib.OneProof.GRDict
import ZInQKernel.Contrib.OneProof.UniformizationLeafAll

/-!
# grx6ab-print: the field `gonzalezRotgerX6Ab` from printed statements, one object per leaf

The research field `gonzalezRotgerX6Ab : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab` (`TailZ22`) is rated GLUE
(composite): it asserts, in one `∃`, the fine moduli scheme `Y₃` (`R1fpPropsAb`), the coarse curve
`X₆ = X₀(6,1)` with the forgetful map `Y₃ → X₆` (`X6Props`), and González–Rotger's Thm 5.12 on residue fields of
CM points (`R5ptProps`). gr-dict (`GRDict.lean`) separated Thm 5.12 as a printed statement on every witness
(`GRDict.GonzalezRotgerThm512X6`) and isolated the witness as the composite `GRDict.X6ModuliWitness`.

This file splits the witness itself:
* `Y₃` with `R1fpPropsAb` is taken from the existing research field `shimuraMainThmIDeligneY3AbU`;
* `X₆` is one new leaf, `X6CoarseModuli`: `X₀(6,1)` over `ℚ` is a coarse moduli scheme for abelian surfaces with
  quaternionic multiplication by `𝒪` (one object, its moduli bijection on `ℚ̄`-points and the classifying map of
  a family over a proper smooth curve);
* the forgetful map `fY : Y₃ → X₆` is a Lean proof (`x6ModuliWitness_of_coarse`): the classifying map of the
  universal family of `Y₃` (`R1famAbProps`).

So `gonzalezRotgerX6Ab` follows from Thm 5.12, `X6CoarseModuli`, the existing field `shimuraMainThmIDeligneY3AbU`
and the textbook fields `uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`
(`gonzalezRotgerX6Ab_of_coarse`). No `sorry`; standard axioms only.
-/

set_option linter.style.longLine false

noncomputable section

namespace GRX6AbPrint

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **LEAF `X6CoarseModuli` (printed form: a consequence of the coarse-moduli theorem for `X₀(6,1)`).**
The Shimura curve `X₆ = X₀(6,1)` of discriminant 6 and level 1, in its canonical model over `ℚ`, is a coarse
moduli scheme for abelian surfaces `(A, ι)` with quaternionic multiplication `ι : 𝒪 → End A` by the maximal order
`𝒪` of `B = (2, −3 | ℚ)` (the polarization is unique, rv-qm-polar). The clauses:
* `X` is a proper smooth curve over `ℚ` with a `ℚ̄`-point (Shimura 1967: `X₀(D,N)` is a smooth projective curve over
  `ℚ`; `D = 6` gives a compact quotient, genus 0);
* `Ψ : X(ℚ̄) ≃ {QM pairs over ℚ̄}/≅` (the coarse-moduli bijection on points over an algebraically closed field);
* `Ψ` is `Gal(ℚ̄/ℚ)`-equivariant (naturality of the coarse map on `Spec` of fields; the canonical model over `ℚ`);
* every automorphism `α` of `𝒪` (conjugation by a normalizer element, Skolem–Noether) acts on `X` over `ℚ` by an
  automorphism inducing the twist `(A, ι) ↦ (A, ι ∘ α)` on points (the Atkin–Lehner group `W`; the action of an
  automorphism of the moduli functor on its coarse space);
* the coarse map on families: a QM abelian scheme with level-3 structure over a proper smooth curve `S/ℚ` whose
  field fibres are objects has a classifying morphism `g : S → X` sending each `ℚ̄`-point `s` to the class of the
  fibre `(A_s, ι_s)` (the natural transformation from the moduli functor to `Hom(-, X)`, at such bases and forgetting
  the level structure: a specialization).

*Sources* (no network; locators UNVERIFIED): Shimura, Ann. of Math. 85 (1967), §§2-3 and Main Theorem I (canonical
models); Deligne, Sém. Bourbaki 389 (1971), §§4-5 (canonical model, the PEL moduli interpretation); Buzzard,
Duke Math. J. 87 (1997), §1 (`X₀(D,N)` as a coarse moduli space of QM abelian surfaces with level structure);
the Atkin–Lehner action by `(A, ι) ↦ (A, ι ∘ Ad μ_m)`, `μ_m ∈ {1, i, j, ij}` at `D = 6` (gt-elkies `IsAtkinLehner`;
Rotger's papers on `W`). Mumford, GIT Def. 5.6 for the notion of coarse moduli scheme.

*Not stronger than the print*: one object and its moduli property; no second moduli space, no forgetful map and no
arithmetic statement (those are `R1fpPropsAb`, the glue `x6ModuliWitness_of_coarse` and Thm 5.12). The family clause
is the natural transformation of the coarse moduli space restricted to bases that are proper smooth curves and to
families carrying level-3 structure, with the fibre hypothesis of the kernel's `R1univAbProps`. -/
def X6CoarseModuli : Prop :=
  ∃ (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)),
    IsProper X.hom ∧ SmoothOfRelativeDimension 1 X.hom ∧ Nonempty (fieldPt Qbar ⟶ X) ∧
    (∀ (σ : Qbar ≃ₐ[ℚ] Qbar) (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
      Ψ x = Quotient.mk _ P → ∃ Q : QMPair Qbar,
        Ψ (fieldMap (σ : Qbar →ₐ[ℚ] Qbar) ≫ x) = Quotient.mk _ Q ∧
        IsBaseChangeOfPair (σ : Qbar →+* Qbar) P Q) ∧
    (∀ α : O ≃+* O, ∃ g : X ≅ X, ∀ (x : fieldPt Qbar ⟶ X) (P : QMPair Qbar),
      Ψ x = Quotient.mk _ P → Ψ (x ≫ g.hom) = Quotient.mk _ (P.twist α)) ∧
    (∀ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom → SmoothOfRelativeDimension 1 S.hom →
      ∀ 𝒜' : LeafQM.AV.R1UnivRigid.QMAbScheme S.left,
        (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
          IsFibreOf 𝒜'.toQMFamily s.left P) →
        ∃ g : S ⟶ X, ∀ (s : fieldPt Qbar ⟶ S) (P : QML3 Qbar),
          IsFibreOf 𝒜'.toQMFamily s.left P → Ψ (s ≫ g) = Quotient.mk _ P.forget)

/-- **GLUE (proved): the moduli witness from `Y₃` and the coarse leaf.** `Y₃` with `R1fpPropsAb` from the research
field `shimuraMainThmIDeligneY3AbU`; the forgetful map `fY : Y₃ → X₆` is the classifying map of the universal
family of `Y₃` (`R1famAbProps`), whose fibres are objects since `Φ` is onto the classes. -/
theorem x6ModuliWitness_of_coarse (hY : RayClassCFT.ShimuraMainThmIDeligneY3AbU) (hX : X6CoarseModuli) :
    GRDict.X6ModuliWitness := by
  obtain ⟨Y, Φ, h1, -⟩ := hY
  obtain ⟨X, Ψ, hp, hs, hn, hgal, hal, huniv⟩ := hX
  obtain ⟨hpY, hsY, -, -, ⟨𝒜, h𝒜⟩, -⟩ := id h1
  have hfib : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y), ∃ P : QML3 K,
      IsFibreOf 𝒜.toQMFamily s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K s)
    exact ⟨P, h𝒜 K s P hP.symm⟩
  obtain ⟨g, hg⟩ := huniv Y hpY hsY 𝒜 hfib
  exact ⟨Y, Φ, X, Ψ, g, h1, hp, hs, hn, hgal, hal, fun y P hP => hg y P (h𝒜 Qbar y P hP)⟩

/-- The coarse leaf is never stronger than the composite witness: every witness gives it (the classifying map of a
family over a proper smooth curve factors through `Y₃` by `R1univAbProps`, then `fY`). -/
theorem x6CoarseModuli_of_witness (hW : GRDict.X6ModuliWitness) : X6CoarseModuli := by
  obtain ⟨Y, Φ, X, Ψ, fY, ⟨-, -, -, -, -, huY⟩, hp, hs, hn, hgal, hal, hfY⟩ := hW
  refine ⟨X, Ψ, hp, hs, hn, hgal, hal, fun S hpS hsS 𝒜' hfib => ?_⟩
  obtain ⟨g, hg⟩ := huY S hpS hsS 𝒜' hfib
  refine ⟨g ≫ fY, fun s P hP => ?_⟩
  rw [← Category.assoc]
  exact hfY (s ≫ g) P (hg Qbar s P hP)

/-- **The field `gonzalezRotgerX6Ab`** from González–Rotger Thm 5.12 over their CM points (`GRDict`, printed leaf),
the coarse leaf `X6CoarseModuli`, the existing research field `shimuraMainThmIDeligneY3AbU` and the textbook fields
`uniformizationLeafAll`, `gagaMorphism`, `mumfordTorsionAlgClosed`. -/
theorem gonzalezRotgerX6Ab_of_coarse (h : GRDict.GonzalezRotgerThm512X6)
    (hY : RayClassCFT.ShimuraMainThmIDeligneY3AbU) (hX : X6CoarseModuli)
    (hU : BPAnalytic.Uniformization.UniformizationLeafAll) (hG : ZInQ.HomLattice.GAGAMorphism)
    (hM : AvSplit.MumfordTorsionAlgClosed) : HDec.QMSplit.Moduli.GonzalezRotgerX6Ab :=
  GRDict.gonzalezRotgerX6Ab_of_witness h (x6ModuliWitness_of_coarse hY hX) hU hG hM

/-- **The final form**: `gonzalezRotgerX6Ab` from the two printed leaves (`GonzalezRotgerThm512X6`,
`X6CoarseModuli`), the existing research field `shimuraMainThmIDeligneY3AbU` and the textbook fields `gagaMorphism`,
`mumfordTorsionAlgClosed` (`uniformizationLeafAll` is the proved `uniformizationLeafAll_proof`). -/
theorem gonzalezRotgerX6Ab_of_print (h : GRDict.GonzalezRotgerThm512X6)
    (hY : RayClassCFT.ShimuraMainThmIDeligneY3AbU) (hX : X6CoarseModuli)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) :
    HDec.QMSplit.Moduli.GonzalezRotgerX6Ab :=
  gonzalezRotgerX6Ab_of_coarse h hY hX uniformizationLeafAll_proof hG hM

end GRX6AbPrint
