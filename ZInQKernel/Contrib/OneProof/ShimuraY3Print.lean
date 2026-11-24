import ZInQKernel.Contrib.OneProof.RayClassShimura

/-! # y3abu-print: `shimuraMainThmIDeligneY3AbU` from two printed statements, one object each

Task y3abu-print (2026-11-16/17). Report: `docs/research/y3abu-print.md`; log: `scratch/y3abu-print/log.md`.

The research field `RayClassCFT.ShimuraMainThmIDeligneY3AbU` (kinds.tsv: composite, GLUE) is

  `∃ Y Φ, R1fpPropsAb Y Φ ∧ ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ`.

It bundles the existence of the fine moduli scheme `Y₃` (with its universal family) with Deligne's statement
that this scheme, with its complex moduli interpretation, is the canonical model of `Sh_{K₃}(B^×, ℍ^±)`
(Shimura's Main Theorem I in Deligne's adelic form). This file separates the two:

1. `Y3FineModuliAb` (new leaf): the fine moduli scheme `Y₃` exists, i.e. some `(Y, Φ)` satisfies the
   abelian-scheme clause list `R1fpPropsAb` (representability of the moduli problem of abelian surfaces with
   `𝒪`-action and full level-3 structure, over `ℚ`; one object, `Y₃` with its universal family).
2. `DeligneCanonicalModelY3Every` (new leaf): for **every** `(Y, Φ)` with `R1fpPropsAb`, the canonical-model
   clauses hold (`DeligneBodyAt` and `ModuliAtUnits`, verbatim); no existence claim. One object, `Y₃ = Sh_{K₃}`.
3. `shimuraMainThmIDeligneY3AbU_of_print : Y3FineModuliAb → DeligneCanonicalModelY3Every →
   ShimuraMainThmIDeligneY3AbU` (the discharge).
4. **Neither leaf is stronger than the field**: `y3FineModuliAb_of_field` (projection) and
   `deligneCanonicalModelY3Every_of_field`. The second holds because two witnesses of `R1fpPropsAb` are
   isomorphic compatibly with their moduli bijections (`compare_iso_ab`, copied from elkies-print's
   `ElkiesX6StarEvery.lean`, which is not in this base), and every clause of `DeligneBodyAt` and
   `ModuliAtUnits` transports along such an isomorphism (`body_transport`; holomorphy through `regVal_comp`).
   So `Y3FineModuliAb ∧ DeligneCanonicalModelY3Every ↔ ShimuraMainThmIDeligneY3AbU` (`print_iff_field`).

No `sorry`; standard axioms only.
-/

set_option linter.all false

noncomputable section

namespace Y3ABUPrint

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV
open ShimuraCFT RayClassCFT

/-! ## 1. The two leaves and the discharge -/

/-- **LEAF `Y3FineModuliAb`: the fine moduli scheme `Y₃` of QM abelian surfaces with full level-3 structure
over `ℚ`** (one object: `Y₃` with its universal family).

*Published statement* (locators recalled, UNVERIFIED; no network): the moduli functor of abelian schemes
`A/S` of relative dimension 2 with an action `ι : 𝒪 → End_S(A)` of the maximal order `𝒪` of the indefinite
quaternion algebra `B = (2, −3 | ℚ)` of discriminant 6 and a full level-3 structure `η : (𝒪/3𝒪)_S ≅ A[3]`
(`𝒪`-linear), on `ℤ[1/6]`-schemes, is represented by a scheme `M` that is projective and smooth of relative
dimension 1 (proper because `B` is a division algebra): K. Buzzard, *Integral models of certain Shimura
curves*, Duke Math. J. 87 (1997), §1 (moduli problem with level structure `U`, representable for `U` small
enough; full level `N ≥ 3`); also J.-F. Boutot, H. Carayol, *Uniformisation `p`-adique des courbes de Shimura*,
Astérisque 196-197 (1991), Ch. III; J. S. Milne, *Points on Shimura varieties mod p*, Proc. Sympos. Pure Math.
33 (1979), Part 2; Mumford, GIT, Thm 7.9 (abelian schemes with level `≥ 3`). Over `ℚ`, `Y₃ = M_ℚ`.

*Lean form*: some `(Y, Φ)` satisfies `R1fpPropsAb` (r1univ-rigid's clause list): `Y` proper and smooth of
relative dimension 1 over `ℚ` with a `ℚ̄`-point; `Φ` the moduli bijections on field points, natural in the
field; the universal abelian scheme with `𝒪`-action and level-3 structure over `Y` (`R1famAbProps`); and the
classifying map of every such family over a proper smooth curve `S/ℚ` (`R1univAbProps`).

*Form*: a **consequence** of representability (the universal property is used only for families over proper
smooth curves and read on field points; the base is `ℚ` instead of `ℤ[1/6]`). Reading risk: the kernel's
moduli problem has no polarization (`QMAbScheme`; Lemma P: for the fixed `μ` the principal polarization exists
and is unique), while some prints (Milne 1979, Boutot–Carayol) include it; Buzzard 1997 states the
polarization-free problem (UNVERIFIED). -/
def Y3FineModuliAb : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ

/-- **LEAF `DeligneCanonicalModelY3Every`: the fine moduli scheme `Y₃`, with its complex moduli
interpretation, is the canonical model of `Sh_{K₃}(B^×, ℍ^±)`** (Shimura's Main Theorem I in Deligne's adelic
form), stated for **every** witness `(Y, Φ)` of `R1fpPropsAb` (one object: `Y₃ = Sh_{K₃}`; no existence claim).

The body is the field's text after `R1fpPropsAb Y Φ ∧`, verbatim: `∃ Ψ, DeligneBodyAt Y Φ Ψ ∧
ModuliAtUnits Y Φ Ψ`. Its clauses: `Ψ : ℍ × (B ⊗ 𝔸_f)^× → Y(ℂ)` is onto with fibres the
`B^×_+ \ · / K₃` classes; holomorphic in `τ`; the object at `Ψ(τ, u)`, `u ∈ 𝒪̂^×`, is the QM torus
`ℂ²/ι(𝒪)(τ, 1)ᵀ` (moduli interpretation); Shimura's reciprocity law `σ Ψ(z, g) = Ψ(z, q̂(s)^ε g)` at CM points
`z` for `σ = [s, K]` on `K^ab` (signs `ε, δ` existential: the conventions).

*Published statement* (locators recalled, UNVERIFIED; no network): P. Deligne, *Travaux de Shimura*,
Sém. Bourbaki 389 (1971): the moduli scheme of a PEL datum is the canonical model of `Sh_K(G, X)` over the
reflex field (§§4-5; Cor. 5.7 / Ex. 5.8 per docs/research/locators.md row R1), with the moduli interpretation
of `Sh_K(G, X)(ℂ)` (§4: `[τ, g] ↦ (ℂ²/ι(L_g)(τ, 1)ᵀ, ι, η_g)`, `L_g = B ∩ 𝒪̂g⁻¹`) and the defining
reciprocity law of the canonical model (§§2-3); here `G = B^×`, `E(G, X) = ℚ`. Also J. S. Milne,
*Introduction to Shimura varieties* (2005), §8 (moduli interpretation of PEL Shimura varieties) and §14
(the PEL moduli variety is the canonical model); G. Shimura, Ann. of Math. 85 (1967), Main Theorem I
(the original statement, over the fields `k_S`).

*Form*: a **consequence** of the print (rayclass-cft §2, gt-rayclass §3): the biholomorphism is weakened to
"bijective and holomorphic in `τ`"; the moduli clause is kept for `g ∈ 𝒪̂^×` only (`L_u = 𝒪`) and describes
the QM pair, not the level structure; the reciprocity conventions are existential; `ℍ` with `B^×_+` replaces
`ℍ^±` with `B^×`; the field-of-moduli clause is dropped. The every-witness form is a consequence of the print
on the moduli scheme because any two witnesses of `R1fpPropsAb` are isomorphic compatibly with `Φ`
(`compare_iso_ab`) and the clauses transport (`deligneCanonicalModelY3Every_of_field`, proved below).
Reading risk (locators.md R1): the print is for the polarized PEL moduli problem with
polarization-compatible level structure; the kernel's problem is polarization-free (Lemma P). -/
def DeligneCanonicalModelY3Every : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), LeafQM.AV.R1UnivRigid.R1fpPropsAb Y Φ →
    ∃ Ψ, DeligneBodyAt Y Φ Ψ ∧ ModuliAtUnits Y Φ Ψ

/-- **The discharge**: the field from the two leaves. -/
theorem shimuraMainThmIDeligneY3AbU_of_print (hM : Y3FineModuliAb) (hD : DeligneCanonicalModelY3Every) :
    ShimuraMainThmIDeligneY3AbU := by
  obtain ⟨Y, Φ, h1⟩ := hM
  obtain ⟨Ψ, hb, hU⟩ := hD Y Φ h1
  exact ⟨Y, Φ, h1, Ψ, hb, hU⟩

/-- The first leaf is a projection of the field. -/
theorem y3FineModuliAb_of_field (h : ShimuraMainThmIDeligneY3AbU) : Y3FineModuliAb := by
  obtain ⟨Y, Φ, h1, -⟩ := h
  exact ⟨Y, Φ, h1⟩

/-! ## 2. Pinning: two fine witnesses are compatibly isomorphic (copied from elkies-print) -/

open LeafQM.AV.R1UnivRigid in
/-- `phi_part` (Pin.lean) for the abelian-scheme clauses (elkies-print's `phi_part_ab`, verbatim). -/
theorem phi_part_ab {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (hU : R1univAbProps Y Φ) (h1' : R1fpPropsAb Y' Φ') :
    ∃ g : Y' ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g) := by
  obtain ⟨hp', hs', -, -, ⟨𝒜', h𝒜'⟩, -⟩ := h1'
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y'), ∃ P : QML3 K,
      IsFibreOf 𝒜'.toQMFamily s.left P :=
    fun K _ _ s => ⟨Quotient.out (Φ' K s), h𝒜' K s _ (Quotient.out_eq _).symm⟩
  obtain ⟨g, hg⟩ := hU Y' hp' hs' 𝒜' hall
  refine ⟨g, fun K _ _ y => ?_⟩
  rw [hg K y _ (h𝒜' K y _ (Quotient.out_eq _).symm)]
  exact (Quotient.out_eq _).symm

open LeafQM.AV.R1UnivRigid in
/-- `compare_iso` (TailU) for the abelian-scheme clauses: two fine witnesses are compatibly isomorphic
(elkies-print's `compare_iso_ab`, verbatim). -/
theorem compare_iso_ab {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (h : R1fpPropsAb Y Φ) (h' : R1fpPropsAb Y' Φ') :
    ∃ g : Y' ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g.hom) := by
  obtain ⟨g, hg⟩ := phi_part_ab h.2.2.2.2.2 h'
  obtain ⟨g', hg'⟩ := phi_part_ab h'.2.2.2.2.2 h
  have e1 : g' ≫ g = 𝟙 Y := HDec.QMSplit.Moduli.eq_id_of_fieldPts h.1 h.2.1 _ fun K _ _ y =>
    (Φ K).injective (by rw [← Category.assoc, ← hg K (y ≫ g'), ← hg' K y])
  have e2 : g ≫ g' = 𝟙 Y' := HDec.QMSplit.Moduli.eq_id_of_fieldPts h'.1 h'.2.1 _ fun K _ _ y =>
    (Φ' K).injective (by rw [← Category.assoc, ← hg' K (y ≫ g), ← hg K y])
  exact ⟨⟨g, g', e2, e1⟩, hg⟩

/-! ## 3. Transport of the canonical-model clauses along a morphism -/

/-- The point of `y ≫ h` is `h` of the point of `y`. -/
theorem ptC_comp {X X' : Scheme.{0}} (h : X ⟶ X') (y : Spec (CommRingCat.of ℂ) ⟶ X) :
    ShimuraSplit.ptC (y ≫ h) = h (ShimuraSplit.ptC y) :=
  congrArg Sigma.fst (specToEquivOfField_comp_right h y)

/-- **Values of regular functions along a morphism**: `f(h ∘ y) = (h^* f)(y)`. -/
theorem regVal_comp {X X' : Scheme.{0}} (h : X ⟶ X') (U : X'.Opens) (f : Γ(X', U))
    (y : Spec (CommRingCat.of ℂ) ⟶ X) :
    ShimuraSplit.regVal U f (y ≫ h) = ShimuraSplit.regVal (h ⁻¹ᵁ U) (h.app U f) y := by
  unfold ShimuraSplit.regVal ShimuraSplit.ptC
  generalize hp : Scheme.SpecToEquivOfField ℂ X' (y ≫ h) = p
  rw [specToEquivOfField_comp_right] at hp
  subst hp
  dsimp only
  split_ifs with h1 h2 h2
  · rw [ConcreteCategory.comp_apply, Scheme.evaluation_naturality_apply]
  · exact (h2 h1).elim
  · exact (h1 h2).elim
  · rfl

/-- **A holomorphic family composed with a morphism of schemes is holomorphic.** -/
theorem isHolFamily_comp {X X' : Scheme.{0}} (h : X ⟶ X')
    {φ : UpperHalfPlane → (Spec (CommRingCat.of ℂ) ⟶ X)} (hφ : ShimuraSplit.IsHolFamily φ) :
    ShimuraSplit.IsHolFamily (fun τ => φ τ ≫ h) := by
  obtain ⟨ho, hh⟩ := hφ
  refine ⟨fun U => ?_, fun U f τ hτ => ?_⟩
  · have e : {τ | ShimuraSplit.ptC (φ τ ≫ h) ∈ U} = {τ | ShimuraSplit.ptC (φ τ) ∈ h ⁻¹ᵁ U} := by
      ext τ
      simp only [Set.mem_setOf_eq, ptC_comp]
      rfl
    rw [e]
    exact ho (h ⁻¹ᵁ U)
  · rw [ptC_comp] at hτ
    obtain ⟨g, hg, hev⟩ := hh (h ⁻¹ᵁ U) (h.app U f) τ hτ
    refine ⟨g, hg, hev.mono fun z hz hz' => ?_⟩
    rw [regVal_comp]
    exact hz hz'

/-- **The canonical-model clauses transport along a compatible isomorphism of witnesses.** -/
theorem body_transport {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (k : Y' ≅ Y) (hk : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'), Φ' K y = Φ K (y ≫ k.hom))
    {Ψ : UpperHalfPlane → BAQˣ → (fieldPt ℂ ⟶ Y)} (hb : DeligneBodyAt Y Φ Ψ) (hU : ModuliAtUnits Y Φ Ψ) :
    DeligneBodyAt Y' Φ' (fun τ g => Ψ τ g ≫ k.inv) ∧ ModuliAtUnits Y' Φ' (fun τ g => Ψ τ g ≫ k.inv) := by
  obtain ⟨hsurj, hfib, hhol, ⟨hmod, hhol1⟩, ε, δ, hrec⟩ := hb
  have hΦ : ∀ y : fieldPt ℂ ⟶ Y, Φ' ℂ (y ≫ k.inv) = Φ ℂ y := fun y => by
    rw [hk ℂ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨⟨fun y' => ?_, fun τ g τ' g' => ?_, fun g => ?_, ⟨fun τ => ?_, ?_⟩, ε, δ, ?_⟩, fun u hu τ => ?_⟩
  · obtain ⟨τ, g, h⟩ := hsurj (y' ≫ k.hom)
    exact ⟨τ, g, by simp only [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  · rw [← hfib τ g τ' g']
    exact ⟨fun h => by simpa using congrArg (· ≫ k.hom) h, fun h => by show Ψ τ g ≫ k.inv = Ψ τ' g' ≫ k.inv; rw [h]⟩
  · exact isHolFamily_comp k.inv.left (hhol g)
  · obtain ⟨P, hP, rest⟩ := hmod τ
    exact ⟨P, by rw [hΦ]; exact hP, rest⟩
  · exact isHolFamily_comp k.inv.left hhol1
  · intro K _ _ _ hK κ q z hz σ s hs g
    show fieldMap _ ≫ Ψ z g ≫ k.inv = Ψ z _ ≫ k.inv
    rw [← Category.assoc]
    exact congrArg (· ≫ k.inv) (hrec K hK κ q z hz σ s hs g)
  · obtain ⟨P, hP, rest⟩ := hU u hu τ
    exact ⟨P, by rw [hΦ]; exact hP, rest⟩

/-- **The second leaf is no stronger than the field**: the field's witness, with its `Ψ`, gives the clauses on
every witness, through `compare_iso_ab` and `body_transport`. -/
theorem deligneCanonicalModelY3Every_of_field (h : ShimuraMainThmIDeligneY3AbU) :
    DeligneCanonicalModelY3Every := by
  obtain ⟨Y₀, Φ₀, h1₀, Ψ, hb, hU⟩ := h
  intro Y Φ h1
  obtain ⟨k, hk⟩ := compare_iso_ab h1₀ h1
  exact ⟨_, body_transport k hk hb hU⟩

/-- **The two leaves together are equivalent to the field.** -/
theorem print_iff_field :
    (Y3FineModuliAb ∧ DeligneCanonicalModelY3Every) ↔ ShimuraMainThmIDeligneY3AbU :=
  ⟨fun h => shimuraMainThmIDeligneY3AbU_of_print h.1 h.2,
    fun h => ⟨y3FineModuliAb_of_field h, deligneCanonicalModelY3Every_of_field h⟩⟩

end Y3ABUPrint
