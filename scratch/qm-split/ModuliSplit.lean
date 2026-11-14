import TailK

/-!
# qm-split, rows H-1 `R1R2fpRep`, H-20 `r1b`, H-43 `X6ConicModel`, H-59 `Y3Connected`: witness splits

These four rows are statements about *one* witness `(Y, Φ, X, Ψ, fY, π₆)` of the moduli problems
(`Y₃` fine, `X₆` coarse), with several clauses. A published theorem is a statement about the canonical
model; to state the parts separately, each clause is stated here for *every* witness of the defining
property `R1fpProps` (resp. `X6Props`). Each such universal Prop is

* the published statement about the canonical model (named in its docstring), **and**
* the transport of that statement to an arbitrary witness, through the comparison isomorphism of two
  witnesses of `R1fpProps` (qm-pin §3.3: `R1univProps` both ways gives inverse morphisms, identity on all
  field points, hence identity), or the uniqueness of the coarse space given `fY`.

So the universal Props are GLUE (consequence of one published statement + a transport the project owes),
except `CanonicalModelY3` (existence, the published representability statement). The rows are proved here
from them; the proofs are logical assembly (no new mathematics). Check:
`scratch/qm-split/chk.sh scratch/qm-split/ModuliSplit.lean`.
-/

set_option linter.all false

noncomputable section

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-! ## Shared leaf -/

/-- **LEAF (representability of the level-3 QM moduli problem; the canonical model `Y₃ = Sh_{K₃}`).** Some
`ℚ`-scheme `Y` with bijections `Φ : Y(K) ≃ M3(K)` satisfies the clause list `R1fpProps` (proper, smooth of
relative dimension 1, a `ℚ̄`-point, naturality, a universal family `R1famProps`, universality
`R1univProps`). Shimura, Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971),
Thm 4.21, Cor. 5.7 (canonical models of PEL type; fine moduli at the neat level `K₃ = (1 + 3𝒪̂)^×`); with
Lemma QP for the polarization (rv-qm-polar). Locators UNVERIFIED; the audit calls R1 a "qualified
consequence" (the specialization of Deligne's PEL model to this functor needs a human check). -/
def CanonicalModelY3 : Prop := ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ

/-! ## H-1 `R1R2fpRep` -/

/-- **GLUE (project; Yoneda).** On a fine moduli witness, `Aut(𝒪)`-twists and right multiplication by
`𝒪^×` on level structures are induced by automorphisms of `Y`: apply `R1univProps` to the twisted universal
family (both ways) and use that a morphism inducing the identity on all field points is the identity. -/
def HeckeOfFine : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → R1heckeProps Y Φ

/-- **GLUE (coarse space `X₆ = Y₃/G` and its geometric connectedness).** For a fine witness, there are a
coarse witness `X` of the QM pairs, `fY : Y → X` (the forgetful map, surjective on `ℚ̄`-points) and `X` is
geometrically connected. Needs: the quotient of a projective curve by a finite group (SGA 1, Exp. V,
Prop. 1.8; Mumford, *Abelian varieties*, §7 Thm), its moduli interpretation on `ℚ̄`-points, and
`π₀(X₆ ⊗ ℚ̄) = ℤ̂^×/nrd(𝒪̂^×) = 1` (Deligne, Bourbaki 389, §2; Shimura 1967); locators UNVERIFIED. -/
def CoarseX6OfFine : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → R1heckeProps Y Φ →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
      (fY : Y ⟶ X), X6Props Y Φ X Ψ fY ∧ (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x) ∧
        LeafAdopt.R1pi0Props X

/-- **GLUE (the Hauptmodul of `X₆/W`, Baba–Granath).** For a coarse witness `X`, there is `π₆ : X → P¹`
whose fibres on `ℚ̄`-points are the `Aut(𝒪)`-twist classes, with `0, ∞, −16/27` exactly at CM by `ℤ[i]`,
`ℤ[ζ₃]`, `ℤ[√−6]`, surjective on `ℚ̄`-points. Baba–Granath, Canad. J. Math. 60 (2008), Thm 2.1 and §3.1
(`X₆/W ≅ P¹_ℚ`, the three branch points), normalized by a Möbius map; transport to the witness `X`.
Locators UNVERIFIED. -/
def HauptmodulOfX6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ → X6Props Y Φ X Ψ fY →
      ∃ π₆ : ToP1 X.left, LeafAdopt.R2X6PropsIff X Ψ π₆ ∧
        ∀ t : OnePoint Qbar, ∃ x : fieldPt Qbar ⟶ X, π₆.val (K := Qbar) x.left = t

/-- **GLUE (Shimura reciprocity at the CM points; R1rec).** On a fine witness, the residue field of a
`ℚ̄`-point with CM by `ℤ[i]`, `ℤ[ζ₃]` or `ℤ[√−6]` is unramified above 5. Shimura, *Introduction to the
arithmetic theory of automorphic functions*, 1971, Thm 9.6 / Shimura 1967 Main Thm II (reciprocity on the
canonical model: the field of moduli lies in the ray class field of conductor 3), transported. -/
def ReciprocityOfFine : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → R1recProps Y Φ

/-- **GLUE (residue fields of CM points on `X₆`; R5).** González–Rotger, J. Math. Soc. Japan 58 (2006),
Thm 5.12 (fields of definition of CM points on `X₀^D(N)`), transported to every coarse witness. -/
def ResidueOfX6 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ → X6Props Y Φ X Ψ fY → R5ptProps X Ψ

/-- **Row H-1 from the split.** -/
theorem r1r2fpRep_of (hE : CanonicalModelY3) (hH : HeckeOfFine) (hX : CoarseX6OfFine)
    (hP : HauptmodulOfX6) (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : LeafAdopt.R1R2fpRep := by
  obtain ⟨Y, Φ, h1⟩ := hE
  have hh := hH Y Φ h1
  obtain ⟨X, Ψ, fY, h6, hsurj, hpi0⟩ := hX Y Φ h1 hh
  obtain ⟨π₆, h2, ht⟩ := hP Y Φ X Ψ fY h1 h6
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hR Y Φ h1, ⟨ht, hsurj⟩, h5 Y Φ X Ψ fY h1 h6, hpi0⟩

/-! ## H-59 `Y3Connected` -/

/-- **GLUE (connectedness of `Y₃` over `ℚ`).** Every fine witness is connected. Published content: the
geometric components of `Sh_K` are `ℚ^×_{>0}\𝔸_f^×/nrd(K)`, with `Gal(ℚ̄/ℚ)` acting through the cyclotomic
character (Deligne, Bourbaki 389, §§2-3; *Variétés de Shimura*, 1979, Thm 2.6.3; Milne, *Introduction to
Shimura varieties*, §13); for `K₃` two geometric components swapped by `Gal(ℚ(√−3)/ℚ)`. Transport to a
witness: the chain's `exists_surjective_of_R1fp` (compiled), as in `TSHecke.connectedSpace_of_R1fp`. -/
def ConnectedOfFine : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ → ConnectedSpace Y.left

/-- **Row H-59 from the split.** -/
theorem y3Connected_of (hE : CanonicalModelY3) (hC : ConnectedOfFine) : TSHecke.Y3Connected := by
  obtain ⟨Y, Φ, h1⟩ := hE
  exact ⟨Y, Φ, h1, hC Y Φ h1⟩

/-- Conversely (compiled in the chain): `Y3Connected` gives `ConnectedOfFine`, so the split is an
equivalence given the shared leaf. -/
theorem connectedOfFine_of (h : TSHecke.Y3Connected) : ConnectedOfFine :=
  fun _ _ h1 => TSHecke.connectedSpace_of_R1fp h h1

/-! ## H-20 `r1b` -/

/-- **LEAF candidate (Shimura's complex uniformization, family form, composed with every algebraic map to
`P¹`).** Some fine witness `(Y, Φ)` carries `τ ↦ y_τ ∈ Y(ℂ)` with the object at `y_τ` equal to
`ℂ²/ι(𝒪)(τ,1)ᵀ` with its `ι` (`IsR1bFamily`), and `τ ↦ π(y_τ)` continuous and holomorphic into `P¹(ℂ)` for
every `π : Y → P¹`. Shimura, Ann. of Math. 85 (1967), Main Thm I (the holomorphic `φ : ℍ → V(ℂ)`); Deligne,
Bourbaki 389, §4.15 (analytic families); the composition with an algebraic `π` is holomorphic (algebraic maps
are holomorphic on the analytification; GAGA level). Locators UNVERIFIED; the "every `π`" reading is a
consequence of the printed statement plus that composition step (flag). -/
def ShimuraFamily : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y), R1fpProps Y Φ ∧
    ∀ π : ToP1 Y.left, HSyn.G0Split.FibreQM.R1bFamily Y Φ π

/-- **GLUE (project; transport of the family between fine witnesses).** If one fine witness carries the
family for every `π`, so does every other: the comparison isomorphism `g : Y' ≅ Y` (qm-pin §3.3) carries
`y_τ` to `y_τ ≫ g⁻¹`, and `π' ∘ g⁻¹` is a map `Y → P¹` (`ToP1.comp`). -/
def R1bTransport : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (Y' : Over (Spec (CommRingCat.of ℚ)))
    (Φ' : PtEquiv Y'), R1fpProps Y Φ → R1fpProps Y' Φ' →
    (∀ π : ToP1 Y.left, HSyn.G0Split.FibreQM.R1bFamily Y Φ π) →
    ∀ π' : ToP1 Y'.left, HSyn.G0Split.FibreQM.R1bFamily Y' Φ' π'

/-- **Row H-20 from the split** (the research field `r1b` of C4''). -/
theorem r1b_of (hS : ShimuraFamily) (hT : R1bTransport) :
    ∀ h : LeafAdopt.R1R2fpRep,
      HSyn.G0Split.FibreQM.R1bFamily (HSyn.G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
        (HSyn.G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
        (HSyn.G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h)) := by
  intro h
  obtain ⟨Y, Φ, h1, hall⟩ := hS
  exact hT Y Φ _ _ h1 (HSyn.G0Split.FibreQM.own_spec _).1 hall _

/-! ## H-43 `X6ConicModel` -/

/-- **GLUE (the conic model of `X₆`).** For every witness of the leaf bundle's clause list, `X` is, on
`ℚ̄`-points and Galois-equivariantly, the conic `Y² + 3X² + 3Z² = 0` with `π₆ = −16(X² + Z²)/(27Z²)`.
Published: Kurihara, J. Fac. Sci. Univ. Tokyo 25 (1979) (`X₀(6,1) : x² + y² + 3 = 0`); Elkies, ANTS-III,
LNCS 1423 (1998), §3 (the coordinate `t` on `X*(6)` and `X₆ = X*(6)(√−t, √(3(t − 1)))`); locators
UNVERIFIED. Transport to the witness: the isomorphism of the witness with the canonical model (uniqueness of
the coarse space with `fY`; CurveBijIso-type glue, H-85). Alternative derivation from the clause list alone
(leaf-review-a §5.11): Kummer theory of the `(ℤ/2)²`-cover `X₆ → X₆/W ≅ P¹` branched at the three CM values,
with the residue fields `ℚ(i)`, `ℚ(√−3)` from R5. -/
def ConicOfWitness : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    FS5NoCM.R1R2fpFullProps Y Φ X Ψ fY π₆ → X6Kummer.ConicModel X π₆

/-- **Row H-43 from the bundle leaf `r1r2` (H-1) and the conic glue.** -/
theorem x6ConicModel_of (hR : LeafAdopt.R1R2fpRep) (hC : ConicOfWitness) : X6Kummer.X6ConicModel := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h⟩ := LeafAdopt.R1R2fp_of_rep hR
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h, hC Y Φ X Ψ fY π₆ h⟩

/-! ## The comparison isomorphism of fine witnesses; `HeckeOfFine` and `R1bTransport` proved

Reducedness of smooth schemes over a domain: copied verbatim from model-glue
(`scratch/model-glue/ModelGlue5.lean`, Parts 12 and 15 @ av-glue's worktree), itself from smooth-fibre. -/

section Comparison

open CategoryTheory AlgebraicGeometry Limits

/-- An étale algebra over a domain is reduced (copied verbatim from task smooth-fibre,
`ZInQKernel/Contrib/SmoothFibre/Basic.lean`, `ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain`). -/
theorem isReduced_of_etale_of_isDomain' (P S : Type*) [CommRing P] [IsDomain P] [CommRing S]
    [Algebra P S] [Algebra.Etale P S] : IsReduced S := by
  let K := FractionRing P
  let f := Algebra.TensorProduct.includeRight (R := P) (A := K) (B := S)
  have hinj : Function.Injective f := by
    have : ⇑f = (LinearMap.rTensor S (Algebra.ofId P K).toLinearMap).comp
        (Algebra.TensorProduct.lid P S).symm.toLinearMap := by
      ext x; simp [f]
    rw [this]
    exact (Module.Flat.rTensor_preserves_injective_linearMap _
      (IsFractionRing.injective P K)).comp (Algebra.TensorProduct.lid P S).symm.injective
  have : IsReduced (TensorProduct P K S) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (f : S →+* TensorProduct P K S) hinj

/-- A smooth algebra over a domain is reduced (the proof of smooth-fibre's
`isReduced_of_smooth_of_field`, with a domain in place of a field). -/
theorem isReduced_of_smooth_of_isDomain (k A : Type*) [CommRing k] [IsDomain k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  by_contra hne
  let I : Ideal A := (Ideal.span {x} : Submodule A A).annihilator
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ I := h ▸ Submodule.mem_top
    rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
    exact hne h1
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal I hI
  have := hm.isPrime
  have : Algebra.IsSmoothAt k m := inferInstance
  obtain ⟨f, hf, n, inst, -, hst⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := m)
  have : IsReduced (Localization.Away f) :=
    isReduced_of_etale_of_isDomain' (MvPolynomial (Fin n) k) _
  have h0 : algebraMap A (Localization.Away f) x = 0 := (hx.map _).eq_zero
  obtain ⟨⟨_, k', rfl⟩, hk⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) x).1 h0
  apply hf
  apply hm.isPrime.mem_of_pow_mem k'
  apply hle
  rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  exact hk

/-- A smooth scheme over a domain is reduced. -/
theorem isReduced_of_smooth_domain {R : CommRingCat.{0}} [IsDomain R] {X : Scheme.{0}}
    (f : X ⟶ Spec R) [Smooth f] : IsReduced X := by
  refine @IsReduced.of_openCover X X.affineCover (fun i => ?_)
  have hsm : Smooth (X.affineCover.f i ≫ f) := inferInstance
  have hring := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp hsm
  letI := ((X.affineCover.f i ≫ f).appTop).hom.toAlgebra
  haveI : Algebra.Smooth Γ(Spec R, ⊤) Γ(X.affineCover.X i, ⊤) :=
    RingHom.smooth_algebraMap.1 hring
  haveI : _root_.IsReduced Γ(X.affineCover.X i, ⊤) :=
    isReduced_of_smooth_of_isDomain Γ(Spec R, ⊤) _
  exact isReduced_of_isAffine_isReduced _


/-- **A self-map of a fine witness fixing every field point is the identity** (`Y` is reduced, being smooth
over `ℚ`, and separated, being proper; two maps agreeing on all residue-field points agree). -/
theorem eq_id_of_fieldPts {Y : Over (Spec (CommRingCat.of ℚ))} (hP : IsProper Y.hom)
    (hS : SmoothOfRelativeDimension 1 Y.hom) (h : Y ⟶ Y)
    (hpt : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), y ≫ h = y) : h = 𝟙 Y := by
  haveI : Smooth Y.hom := hS.smooth
  haveI : IsReduced Y.left := isReduced_of_smooth_domain Y.hom
  apply Over.OverMorphism.ext
  refine ext_of_fromSpecResidueField_eq h.left (𝟙 _) Y.hom Set.univ dense_univ ?_ (by simp)
  intro x _
  let φ : CommRingCat.of ℚ ⟶ Y.left.residueField x :=
    Spec.preimage (Y.left.fromSpecResidueField x ≫ Y.hom)
  letI : Algebra ℚ (Y.left.residueField x) := φ.hom.toAlgebra
  let y : fieldPt (Y.left.residueField x) ⟶ Y :=
    Over.homMk (Y.left.fromSpecResidueField x) (by
      change _ = Spec.map φ
      exact (Spec.map_preimage _).symm)
  have := congrArg CommaMorphism.left (hpt _ y)
  exact this

theorem eq_id_of_Φ {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h1 : R1fpProps Y Φ) (h : Y ⟶ Y)
    (hpt : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), Φ K (y ≫ h) = Φ K y) : h = 𝟙 Y :=
  eq_id_of_fieldPts h1.1 h1.2.1 h fun K _ _ y => (Φ K).injective (hpt K y)

/-- **The comparison isomorphism of two fine witnesses** (qm-pin §3.3, compiled here): `R1univProps` both
ways gives `g : Y' → Y` and `g' : Y → Y'` compatible with the moduli bijections; both composites fix every
field point, hence are identities. -/
theorem compare_iso {Y Y' : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} {Φ' : PtEquiv Y'}
    (h : R1fpProps Y Φ) (h' : R1fpProps Y' Φ') :
    ∃ g : Y' ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y'),
      Φ' K y = Φ K (y ≫ g.hom) := by
  obtain ⟨g, hg⟩ := LeafQM.AV.Pin.phi_part (LeafQM.AV.Pin.R1fpProps.univ h) h'
  obtain ⟨g', hg'⟩ := LeafQM.AV.Pin.phi_part (LeafQM.AV.Pin.R1fpProps.univ h') h
  have e1 : g' ≫ g = 𝟙 Y := eq_id_of_Φ h _ fun K _ _ y => by
    rw [← Category.assoc, ← hg K (y ≫ g'), ← hg' K y]
  have e2 : g ≫ g' = 𝟙 Y' := eq_id_of_Φ h' _ fun K _ _ y => by
    rw [← Category.assoc, ← hg' K (y ≫ g), ← hg K y]
  exact ⟨⟨g, g', e2, e1⟩, hg⟩

variable {K : Type} [Field K]

set_option maxHeartbeats 2000000 in
/-- `((P.twist α).twist α.symm) ≅ P`. -/
def isoTwistSymm (P : QML3 K) (α : O ≃+* O) : ((P.twist α).twist α.symm).Iso P :=
  { φ := (QML3.Iso.refl P).φ
    ψ := (QML3.Iso.refl P).ψ
    left := (QML3.Iso.refl P).left
    right := (QML3.Iso.refl P).right
    equivariant := fun a => by
      have h : ((P.twist α).twist α.symm).q.iota a = P.q.iota a := by
        show P.q.iota (α (α.symm a)) = P.q.iota a
        rw [RingEquiv.apply_symm_apply]
      rw [h]; exact (QML3.Iso.refl P).equivariant a
    level := fun a => by
      have h : ((P.twist α).twist α.symm).e.eta a = P.e.eta a := by
        show P.e.eta (α (α.symm a)) = P.e.eta a
        rw [RingEquiv.apply_symm_apply]
      rw [h]; exact (QML3.Iso.refl P).level a }

theorem M3.twist_symm_twist (α : O ≃+* O) (c : M3 K) : M3.twist α.symm (M3.twist α c) = c := by
  induction c using Quotient.inductionOn with
  | h P => exact Quotient.sound ⟨isoTwistSymm P α⟩

theorem M3.twist_twist_symm (α : O ≃+* O) (c : M3 K) : M3.twist α (M3.twist α.symm c) = c := by
  have := M3.twist_symm_twist α.symm c
  rwa [RingEquiv.symm_symm] at this

set_option maxHeartbeats 2000000 in
/-- `P.rightMul 1 ≅ P`. -/
def isoRightMulOne (P : QML3 K) : (P.rightMul 1).Iso P :=
  { φ := (QML3.Iso.refl P).φ
    ψ := (QML3.Iso.refl P).ψ
    left := (QML3.Iso.refl P).left
    right := (QML3.Iso.refl P).right
    equivariant := fun a => (QML3.Iso.refl P).equivariant a
    level := fun a => by
      have h : (P.rightMul 1).e.eta a = P.e.eta a := by
        show P.e.eta (a * ((1 : Oˣ) : O)) = P.e.eta a
        rw [Units.val_one, _root_.mul_one]
      rw [h]; exact (QML3.Iso.refl P).level a }

theorem M3.rightMul_inv (u : Oˣ) (c : M3 K) : M3.rightMul u⁻¹ (M3.rightMul u c) = c := by
  rw [M3.rightMul_rightMul, inv_mul_cancel]
  induction c using Quotient.inductionOn with
  | h P => exact Quotient.sound ⟨isoRightMulOne P⟩

theorem M3.rightMul_inv' (u : Oˣ) (c : M3 K) : M3.rightMul u (M3.rightMul u⁻¹ c) = c := by
  have := M3.rightMul_inv u⁻¹ c
  rwa [inv_inv] at this

/-- From a self-map `g` of a fine witness inducing a bijection `τ` on classes with inverse induced by `g'`,
an automorphism. -/
theorem iso_of_pair {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h1 : R1fpProps Y Φ)
    (τ τ' : ∀ (K : Type) [Field K], M3 K → M3 K)
    (hττ' : ∀ (K : Type) [Field K] (c : M3 K), τ' K (τ K c) = c)
    (hτ'τ : ∀ (K : Type) [Field K] (c : M3 K), τ K (τ' K c) = c)
    (g g' : Y ⟶ Y)
    (hg : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), Φ K (y ≫ g) = τ K (Φ K y))
    (hg' : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y), Φ K (y ≫ g') = τ' K (Φ K y)) :
    ∃ e : Y ≅ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y),
      Φ K (y ≫ e.hom) = τ K (Φ K y) := by
  have e1 : g ≫ g' = 𝟙 Y := eq_id_of_Φ h1 _ fun K _ _ y => by
    rw [← Category.assoc, hg' K (y ≫ g), hg K y, hττ']
  have e2 : g' ≫ g = 𝟙 Y := eq_id_of_Φ h1 _ fun K _ _ y => by
    rw [← Category.assoc, hg K (y ≫ g'), hg' K y, hτ'τ]
  exact ⟨⟨g, g', e1, e2⟩, hg⟩

/-- A family twisted by `α` (on `ι` and on `η`). -/
def twistFam {S : Scheme.{0}} (𝒜 : QMFamily S) (α : O ≃+* O) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota a := 𝒜.iota (α a)
  iota_over a := 𝒜.iota_over (α a)
  eta a := 𝒜.eta (α a)
  eta_sec a := 𝒜.eta_sec (α a)

/-- A family with `η` right-multiplied by `u`. -/
def rightMulFam {S : Scheme.{0}} (𝒜 : QMFamily S) (u : Oˣ) : QMFamily S where
  F := 𝒜.F
  proper := 𝒜.proper
  smooth := 𝒜.smooth
  iota := 𝒜.iota
  iota_over := 𝒜.iota_over
  eta a := 𝒜.eta (a * u)
  eta_sec a := 𝒜.eta_sec (a * u)

theorem isFibre_twist {S : Scheme.{0}} {𝒜 : QMFamily S} {L : Type} [Field L]
    {y : Spec (CommRingCat.of L) ⟶ S} {P : QML3 L} (h : IsFibreOf 𝒜 y P) (α : O ≃+* O) :
    IsFibreOf (twistFam 𝒜 α) y (P.twist α) := by
  obtain ⟨g, hpb, hι, hη⟩ := h
  exact ⟨g, hpb, fun a => hι (α a), fun a => hη (α a)⟩

theorem isFibre_rightMul {S : Scheme.{0}} {𝒜 : QMFamily S} {L : Type} [Field L]
    {y : Spec (CommRingCat.of L) ⟶ S} {P : QML3 L} (h : IsFibreOf 𝒜 y P) (u : Oˣ) :
    IsFibreOf (rightMulFam 𝒜 u) y (P.rightMul u) := by
  obtain ⟨g, hpb, hι, hη⟩ := h
  exact ⟨g, hpb, hι, fun a => hη (a * u)⟩

/-- The self-map classifying a modified universal family. -/
theorem classify {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y} (h1 : R1fpProps Y Φ)
    (𝒜 : QMFamily Y.left)
    (h𝒜 : ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
      Φ K y = M3.mk P → IsFibreOf 𝒜 y.left P)
    (𝒜' : QMFamily Y.left) (τ : ∀ (K : Type) [Field K], QML3 K → QML3 K)
    (hτ : ∀ (K : Type) [Field K] (y : Spec (CommRingCat.of K) ⟶ Y.left) (P : QML3 K),
      IsFibreOf 𝒜 y P → IsFibreOf 𝒜' y (τ K P)) :
    ∃ g : Y ⟶ Y, ∀ (K : Type) [Field K] [Algebra ℚ K] (y : fieldPt K ⟶ Y) (P : QML3 K),
      Φ K y = M3.mk P → Φ K (y ≫ g) = M3.mk (τ K P) := by
  have hall : ∀ (K : Type) [Field K] [Algebra ℚ K] (s : fieldPt K ⟶ Y), ∃ P : QML3 K,
      IsFibreOf 𝒜' s.left P := by
    intro K _ _ s
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K s)
    exact ⟨τ K P, hτ K s.left P (h𝒜 K s P hP.symm)⟩
  obtain ⟨g, hg⟩ := (LeafQM.AV.Pin.R1fpProps.univ h1) Y h1.1 h1.2.1 𝒜' hall
  exact ⟨g, fun K _ _ y P hP => hg K y (τ K P) (hτ K y.left P (h𝒜 K y P hP))⟩

/-- **`HeckeOfFine` is a theorem.** -/
theorem heckeOfFine_proof : HeckeOfFine := by
  intro Y Φ h1
  obtain ⟨𝒜, h𝒜⟩ := h1.2.2.2.2.1
  refine ⟨fun α => ?_, fun u => ?_⟩
  · obtain ⟨g, hg⟩ := classify h1 𝒜 h𝒜 (twistFam 𝒜 α) (fun _ _ P => P.twist α)
      (fun _ _ y P h => isFibre_twist h α)
    obtain ⟨g', hg'⟩ := classify h1 𝒜 h𝒜 (twistFam 𝒜 α.symm) (fun _ _ P => P.twist α.symm)
      (fun _ _ y P h => isFibre_twist h α.symm)
    refine iso_of_pair h1 (fun K _ => M3.twist α) (fun K _ => M3.twist α.symm)
      (fun K _ c => M3.twist_symm_twist α c) (fun K _ c => M3.twist_twist_symm α c) g g' ?_ ?_
    · intro K _ _ y
      obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K y)
      rw [hg K y P hP.symm, ← hP]; rfl
    · intro K _ _ y
      obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K y)
      rw [hg' K y P hP.symm, ← hP]; rfl
  · obtain ⟨g, hg⟩ := classify h1 𝒜 h𝒜 (rightMulFam 𝒜 u) (fun _ _ P => P.rightMul u)
      (fun _ _ y P h => isFibre_rightMul h u)
    obtain ⟨g', hg'⟩ := classify h1 𝒜 h𝒜 (rightMulFam 𝒜 u⁻¹) (fun _ _ P => P.rightMul u⁻¹)
      (fun _ _ y P h => isFibre_rightMul h u⁻¹)
    refine iso_of_pair h1 (fun K _ => M3.rightMul u) (fun K _ => M3.rightMul u⁻¹)
      (fun K _ c => M3.rightMul_inv u c) (fun K _ c => M3.rightMul_inv' u c) g g' ?_ ?_
    · intro K _ _ y
      obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K y)
      rw [hg K y P hP.symm, ← hP]; rfl
    · intro K _ _ y
      obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ K y)
      rw [hg' K y P hP.symm, ← hP]; rfl

/-- **`R1bTransport` is a theorem** (the comparison isomorphism carries the family). -/
theorem r1bTransport_proof : R1bTransport := by
  intro Y Φ Y' Φ' h h' hall π'
  obtain ⟨g, hg⟩ := compare_iso h h'
  obtain ⟨yτ, hy1, hy2, hy3⟩ := hall (π'.comp g.inv.left)
  have hfun : (fun τ => π'.val (K := ℂ) (yτ τ ≫ g.inv).left) =
      (fun τ => (π'.comp g.inv.left).val (K := ℂ) (yτ τ).left) := by
    funext τ
    exact (ToP1.val_comp_right π' g.inv.left (yτ τ).left).symm
  refine ⟨fun τ => yτ τ ≫ g.inv, fun τ => ?_, ?_, ?_⟩
  · obtain ⟨P, hP, rest⟩ := hy1 τ
    refine ⟨P, ?_, rest⟩
    rw [hg, Category.assoc, g.inv_hom_id, Category.comp_id]; exact hP
  · simp only at hfun ⊢; rw [hfun]; exact hy2
  · intro τ; simp only at hfun ⊢; rw [hfun]; exact hy3 τ

end Comparison

/-- **Row H-1 with `HeckeOfFine` discharged.** -/
theorem r1r2fpRep_of' (hE : CanonicalModelY3) (hX : CoarseX6OfFine) (hP : HauptmodulOfX6)
    (hR : ReciprocityOfFine) (h5 : ResidueOfX6) : LeafAdopt.R1R2fpRep :=
  r1r2fpRep_of hE heckeOfFine_proof hX hP hR h5

/-- **Row H-20 from the leaf candidate `ShimuraFamily` alone** (`R1bTransport` discharged). -/
theorem r1b_of' (hS : ShimuraFamily) :
    ∀ h : LeafAdopt.R1R2fpRep,
      HSyn.G0Split.FibreQM.R1bFamily (HSyn.G0Split.FibreQM.ownY (LeafAdopt.R1R2fp_of_rep h))
        (HSyn.G0Split.FibreQM.ownΦ (LeafAdopt.R1R2fp_of_rep h))
        (HSyn.G0Split.FibreQM.ownπ (LeafAdopt.R1R2fp_of_rep h)) :=
  r1b_of hS r1bTransport_proof

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of
#print axioms HDec.QMSplit.Moduli.y3Connected_of
#print axioms HDec.QMSplit.Moduli.r1b_of
#print axioms HDec.QMSplit.Moduli.x6ConicModel_of
#print axioms HDec.QMSplit.Moduli.heckeOfFine_proof
#print axioms HDec.QMSplit.Moduli.compare_iso
#print axioms HDec.QMSplit.Moduli.r1bTransport_proof
#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of'
#print axioms HDec.QMSplit.Moduli.r1b_of'

example : HDec.QMSplit.Moduli.CanonicalModelY3 → HDec.QMSplit.Moduli.HeckeOfFine →
    HDec.QMSplit.Moduli.CoarseX6OfFine → HDec.QMSplit.Moduli.HauptmodulOfX6 →
    HDec.QMSplit.Moduli.ReciprocityOfFine → HDec.QMSplit.Moduli.ResidueOfX6 → HDec.LeafAdopt.R1R2fpRep :=
  HDec.QMSplit.Moduli.r1r2fpRep_of
example : HDec.QMSplit.Moduli.CanonicalModelY3 → HDec.QMSplit.Moduli.ConnectedOfFine →
    HDec.TSHecke.Y3Connected := HDec.QMSplit.Moduli.y3Connected_of
example : HDec.LeafAdopt.R1R2fpRep → HDec.QMSplit.Moduli.ConicOfWitness → HDec.X6Kummer.X6ConicModel :=
  HDec.QMSplit.Moduli.x6ConicModel_of
