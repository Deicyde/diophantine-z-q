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

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.r1r2fpRep_of
#print axioms HDec.QMSplit.Moduli.y3Connected_of
#print axioms HDec.QMSplit.Moduli.r1b_of
#print axioms HDec.QMSplit.Moduli.x6ConicModel_of

example : HDec.QMSplit.Moduli.CanonicalModelY3 → HDec.QMSplit.Moduli.HeckeOfFine →
    HDec.QMSplit.Moduli.CoarseX6OfFine → HDec.QMSplit.Moduli.HauptmodulOfX6 →
    HDec.QMSplit.Moduli.ReciprocityOfFine → HDec.QMSplit.Moduli.ResidueOfX6 → HDec.LeafAdopt.R1R2fpRep :=
  HDec.QMSplit.Moduli.r1r2fpRep_of
example : HDec.QMSplit.Moduli.CanonicalModelY3 → HDec.QMSplit.Moduli.ConnectedOfFine →
    HDec.TSHecke.Y3Connected := HDec.QMSplit.Moduli.y3Connected_of
example : HDec.LeafAdopt.R1R2fpRep → HDec.QMSplit.Moduli.ConicOfWitness → HDec.X6Kummer.X6ConicModel :=
  HDec.QMSplit.Moduli.x6ConicModel_of
