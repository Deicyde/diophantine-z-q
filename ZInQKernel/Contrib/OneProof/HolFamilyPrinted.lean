import ZInQKernel.Contrib.OneProof.CompositeOut

/-!
# holfam: the holomorphic moduli map on the fine witness from the PEL family with its complex uniformization

Task holfam (2026-11-15). Report: `docs/research/holfam.md`; log: `scratch/holfam/log.md`.

composite-out (`CompositeOut.lean`) proved the three uses of gt-rayclass's composite
`RayClassCFT.ShimuraMainThmIDeligneY3AbU` from qmrec-printed's `MainTheoremCM` and shimura-split2's
`ShimuraHolFamilyAb` / `ShimuraHolModAll`. The latter was rated "pending reading": the printed object is Shimura's
`V_S` or Deligne's model `M_K`, and carrying the holomorphic moduli map to the project's fine witness `(Y, Φ)`
(`R1fpPropsAb`) needs an identification of that object with `Y`.

This file removes the identification step from the leaf. The new leaf `PELHolFamily` speaks only of the printed
object: a proper smooth curve `S/ℚ` (Deligne's `M_K`, `K = K₃`) with a QM abelian scheme with level-3 structure
(its universal family) whose field fibres are objects, and a holomorphic `τ ↦ s_τ ∈ S(ℂ)` (`[τ, 1]`) whose fibre is,
as a QM pair, `ℂ²/ι(𝒪)(τ, 1)ᵀ`. It says nothing about `Y` or `Φ`. The transport to every fine witness is proved
here (`shimuraHolModAll_of_pel`), from the universal property clause `R1univAbProps` of the witness (the map
`S → Y` classifying the family is a morphism of schemes, and holomorphic families compose with morphisms:
shimura-split2's `isHolFamily_comp`).

Results (all proved, standard axioms):
* `shimuraHolModAll_of_pel : PELHolFamily → ShimuraSplit2.ShimuraHolModAll`;
* `shimuraHolFamilyAb_of_pel : DeligneComponentsX6PrintedAb → PELHolFamily → ShimuraSplit2.ShimuraHolFamilyAb`;
* `pelHolFamily_of_hol : ShimuraSplit2.ShimuraHolFamilyAb → PELHolFamily` (the new leaf is not stronger);
* `compositeUses_of_pel`, `y3Connected_of_pel`, `shimuraFamilyAb_of_pel`: the three uses of the composite from
  `PELHolFamily`, `MainTheoremCM`, the fine witness of `deligneComponentsX6PrintedAb`, the textbook fields and
  `mumfordGroupLaw`.
-/

set_option linter.all false

noncomputable section

namespace HolFamilyPrinted

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open ZInQ.LeafPush2 (CPts IsUniformization)

/-- **LEAF `PELHolFamily` (the PEL moduli scheme `M_{K₃}` of QM abelian surfaces with level 3, with its universal
family and its complex uniformization).** There are a curve `S`, proper and smooth of relative dimension 1 over `ℚ`,
a QM abelian scheme `𝒜 → S` with level-3 structure (`QMAbScheme`) all of whose field fibres are objects (`QML3`),
and a holomorphic map `τ ↦ s_τ ∈ S(ℂ)` on `ℍ` (`ShimuraSplit.IsHolFamily`: preimages of Zariski opens are open,
regular functions pull back to analytic functions) such that the fibre of `𝒜` at `s_τ` is, by an `ι`-compatible
analytic uniformization with kernel `Λ_τ = ι(𝒪)(τ, 1)ᵀ`, the torus `ℂ²/Λ_τ` (the level structure is not
described).

*Published statements* (locators recalled, UNVERIFIED; no network):
* Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§4.9–4.17 and Example 5.8: for a Shimura datum of PEL
  type and a neat compact open `K`, the moduli scheme `M_K` over the reflex field (here `ℚ`) with its universal
  abelian scheme, and the description of `M_K(ℂ)` as `G(ℚ)\X × G(𝔸_f)/K`, the point `[x, g]` carrying the abelian
  variety `ℂ^g/Λ(x, g)` as analytic spaces;
* Milne, *Introduction to Shimura varieties* (2005), §8 (PEL Shimura varieties as moduli varieties; the family on
  `Sh_K(ℂ)` is algebraic, by Borel's extension theorem and Riemann's theorem in families, Deligne Hodge II 4.4.3) and
  §14 (the model over the reflex field);
* Shimura, Ann. of Math. 78 (1963) (analytic families of polarized abelian varieties with QM: `τ ↦ ℂ²/ι(𝒪)(τ,1)ᵀ`)
  and Ann. of Math. 85 (1967), Main Theorem I.

*Form*: a consequence of the first, not stronger: `S = M_{K₃}` for `G = B^×`, `K₃ = ker((𝒪⊗ℤ̂)^× → (𝒪/3𝒪)^×)`,
`𝒜` its universal family, `s_τ = [τ, 1]`; one family, on the component through `[τ, 1]`; the fibre is described
only as a QM pair. Unlike `ShimuraSplit2.ShimuraHolModAll` it says nothing about the project's fine witness
`(Y, Φ)`: the identification of the printed `M_K` with `Y` is not part of the leaf (it is the Lean proof
`shimuraHolModAll_of_pel`). It is implied by `ShimuraHolFamilyAb` (`pelHolFamily_of_hol`). -/
def PELHolFamily : Prop :=
  ∃ (S : Over (Spec (CommRingCat.of ℚ))), IsProper S.hom ∧ SmoothOfRelativeDimension 1 S.hom ∧
    ∃ 𝒜 : R1UnivRigid.QMAbScheme S.left,
      (∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ S), ∃ P : QML3 K,
        IsFibreOf 𝒜.toQMFamily s.left P) ∧
      ∃ sτ : UpperHalfPlane → (fieldPt ℂ ⟶ S),
        ShimuraSplit.IsHolFamily (X := S.left) (fun τ => (sτ τ).left) ∧
        ∀ τ : UpperHalfPlane, ∃ P : QML3 ℂ, IsFibreOf 𝒜.toQMFamily (sτ τ).left P ∧
          ∃ Φu : (Fin 2 → ℂ) → CPts P.A (RingHom.id ℂ),
            IsUniformization (RingHom.id ℂ) (BPAnalytic.QM.qmLattice τ.im_pos.ne') Φu ∧
            HDec.HSyn.G0Split.FibreQM.IotaCompatible P Φu

/-- **GLUE (proved): transport to every fine witness.** The universal property clause of `(Y, Φ)` classifies the
family `𝒜` of `PELHolFamily` by a morphism `g : S → Y` over `ℚ`; `τ ↦ s_τ ≫ g` is holomorphic
(`ShimuraSplit2.isHolFamily_comp`) and its object is the fibre of `𝒜` at `s_τ`. -/
theorem shimuraHolModAll_of_pel (hP : PELHolFamily) : ShimuraSplit2.ShimuraHolModAll := by
  obtain ⟨S, hp, hs, 𝒜, hfib, sτ, hhol, hmod⟩ := hP
  intro Y Φ h1
  obtain ⟨g, hg⟩ := h1.2.2.2.2.2 S hp hs 𝒜 hfib
  refine ⟨fun τ => sτ τ ≫ g, fun τ => ?_, ShimuraSplit2.isHolFamily_comp g.left hhol⟩
  obtain ⟨P, hPf, rest⟩ := hmod τ
  exact ⟨P, hg ℂ (sτ τ) P hPf, rest⟩

/-- **The ∃-form `ShimuraHolFamilyAb`** from `PELHolFamily` and the fine witness (clause (R)) of the bundle leaf
`deligneComponentsX6PrintedAb`. -/
theorem shimuraHolFamilyAb_of_pel (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : PELHolFamily) :
    ShimuraSplit2.ShimuraHolFamilyAb :=
  ShimuraSplit2.shimuraHolFamilyAb_of_all (ShimuraSplit2.witness_of_x6 hR) (shimuraHolModAll_of_pel hP)

/-- **`PELHolFamily` is not stronger than `ShimuraHolFamilyAb`**: the fine witness, its universal family
(`R1famAbProps`) and its holomorphic moduli map give the data of `PELHolFamily`. -/
theorem pelHolFamily_of_hol (hH : ShimuraSplit2.ShimuraHolFamilyAb) : PELHolFamily := by
  obtain ⟨Y, Φ, h1, yτ, hmod, hhol⟩ := hH
  obtain ⟨hp, hs, -, -, ⟨𝒜, h𝒜⟩, -⟩ := h1
  refine ⟨Y, hp, hs, 𝒜, fun K _ _ s => ?_, yτ, hhol, fun τ => ?_⟩
  · obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K s)
    exact ⟨P, h𝒜 K s P hP.symm⟩
  · obtain ⟨P, hP, rest⟩ := hmod τ
    exact ⟨P, h𝒜 ℂ (yτ τ) P hP, rest⟩

/-- **`PELHolFamily` ⇔ `ShimuraHolFamilyAb`, given the fine witness of `deligneComponentsX6PrintedAb`.** -/
theorem pelHolFamily_iff_hol (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) :
    PELHolFamily ↔ ShimuraSplit2.ShimuraHolFamilyAb :=
  ⟨shimuraHolFamilyAb_of_pel hR, pelHolFamily_of_hol⟩

/-! ## The three uses of the composite `ShimuraMainThmIDeligneY3AbU` -/

/-- **The field `shimuraFamilyAb`** from `deligneComponentsX6PrintedAb` (its fine witness) and `PELHolFamily`. -/
theorem shimuraFamilyAb_of_pel (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : PELHolFamily) :
    HDec.QMSplit.Moduli.ShimuraFamilyAb :=
  ShimuraSplit2.shimuraFamilyAb_of_leaves2 hR (shimuraHolModAll_of_pel hP)

/-- **The chain's `TSHecke.Y3Connected`** from `PELHolFamily`, `MainTheoremCM` and the bundle fields. -/
theorem y3Connected_of_pel (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw)
    (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : PELHolFamily)
    (hM : QMRecPrinted.MainTheoremCM) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed) : HDec.TSHecke.Y3Connected :=
  CompositeOut.y3Connected_of_modAll hGL hR (shimuraHolModAll_of_pel hP) hM hUL hG hMum

/-- **Everything the composite is used for**, from `PELHolFamily`, `MainTheoremCM`, the fine witness of
`deligneComponentsX6PrintedAb`, the textbook fields and `mumfordGroupLaw`. -/
theorem compositeUses_of_pel (hR : ShimuraGlue.DeligneComponentsX6PrintedAb) (hP : PELHolFamily)
    (hM : QMRecPrinted.MainTheoremCM) (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hMum : AvSplit.MumfordTorsionAlgClosed)
    (hGL : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw) :
    ShimuraGlue.Ray.RayClassCMAb ∧ HDec.QMSplit.Moduli.ShimuraFamilyAb ∧ HDec.TSHecke.Y3Connected :=
  CompositeOut.compositeUses_of_hol (shimuraHolFamilyAb_of_pel hR hP) hM hUL hG hMum hGL

end HolFamilyPrinted

end
