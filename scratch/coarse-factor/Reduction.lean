import ZInQKernel.OneProof.H.LPrefix

/-! # coarse-factor: reduction of `CoarseFactor` (qm-glue (d))

`CoarseFactor` and `CanonicalCoarseX6` are copied verbatim from `scratch/qm-glue/ModuliCompare.lean`
(namespace `HDec.QMSplit.Moduli`; they use only kernel definitions: `R1fpProps`, `X6Props`
(`ZInQKernel/HDecomp/QM/Leaves.lean`), `R1pi0Props`, `R1R2fpRep` (`ZInQKernel/OneProof/H/LPrefix.lean`)).

Reduction: `CoarseFactor` follows from
* `PairsLift` (every QM pair over `ℚ̄` is, up to isomorphism, the pair underlying a level-3 object),
  which is a consequence of the leaf-form `CanonicalCoarseX6` already used by qm-glue
  (`pairsLift_of_canonical`) and of the bundle leaf `R1R2fpRep` (`pairsLift_of_rep`), and
* `FactorThroughSurj` (AG glue: over `ℚ`, a morphism of proper smooth curves constant on the
  `ℚ̄`-fibres of a morphism surjective on `ℚ̄`-points factors through it).
-/

set_option linter.all false
set_option autoImplicit false

noncomputable section

namespace HDec.QMSplit.Moduli

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **GLUE (descent of the forgetful map; project).** Two coarse witnesses `(X, Ψ, fY)`, `(X', Ψ', fY')` over
the same fine witness `(Y, Φ)` are related by a morphism `h : X → X'` compatible with the moduli bijections
on `ℚ̄`-points. What it needs: `fY` is finite and surjective (on `ℚ̄`-points every QM pair has a level-3
structure, `A[3] ≅ 𝒪/3𝒪` as `𝒪`-modules), `X` is a normal curve, and `fY'` is constant on the fibres of `fY`
(both are the forgetful map on `ℚ̄`-points); in characteristic 0 a morphism constant on the fibres of a finite
surjective morphism onto a normal variety factors through it (`X` is the quotient of `Y` by the deck group:
SGA 1, Exp. V, Prop. 1.8 and Cor. 1.5; Mumford, *Abelian varieties*, §7, Thm; Stacks, the universal property
of a geometric quotient by a finite group; locators UNVERIFIED). Algebraic geometry of curves, not done here. -/
def CoarseFactor : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X X' : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (Ψ' : (fieldPt Qbar ⟶ X') ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X) (fY' : Y ⟶ X'),
    R1fpProps Y Φ → X6Props Y Φ X Ψ fY → X6Props Y Φ X' Ψ' fY' →
      ∃ h : X ⟶ X', ∀ x : fieldPt Qbar ⟶ X, Ψ' (x ≫ h) = Ψ x

/-- **LEAF-form (the canonical model `Y₃` and its coarse quotient `X₆ = Y₃/G`).** Some fine witness carries
a coarse witness with the forgetful map onto `X₆(ℚ̄)`, and `X₆` geometrically connected. Published: Shimura,
Ann. of Math. 85 (1967), Main Thms I-II; Deligne, Sém. Bourbaki 389 (1971), Thm 4.21 and §2
(`π₀(X₆ ⊗ ℚ̄) = ℤ̂^×/nrd(𝒪̂^×) = 1`); the quotient of a projective curve by a finite group (SGA 1, Exp. V,
Prop. 1.8); locators UNVERIFIED; the audit's "qualified consequence" caveat of `CanonicalModelY3` applies. -/
def CanonicalCoarseX6 : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (X : Over (Spec (CommRingCat.of ℚ)))
    (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)) (fY : Y ⟶ X),
    R1fpProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x) ∧
      LeafAdopt.R1pi0Props X

/-! ## The smaller Props -/

/-- **Every QM pair over `ℚ̄` carries a level-3 structure, up to isomorphism** (step: surjectivity of the
forgetful map `Y₃(ℚ̄) → X₆(ℚ̄)`). Published content: for an abelian surface over an algebraically closed field
of characteristic 0 with QM by the maximal order `𝒪`, `A[3]` is free of rank one over `𝒪/3𝒪` (over `ℂ`,
`H₁(A, ℤ)` is a projective, hence free, left `𝒪`-module of rank one); a generator `v` gives `η(a) = a v`.
Not used as a leaf here: it is *derived* (`pairsLift_of_canonical`, `pairsLift_of_rep`) from the leaf-forms
already in use (`CanonicalCoarseX6`, `R1R2fpRep`), whose forgetful map is surjective on `ℚ̄`-points. -/
def PairsLift : Prop :=
  ∀ Q : QMPair Qbar, ∃ P : QML3 Qbar, Quotient.mk (pairSetoid Qbar) P.forget = Quotient.mk _ Q

/-- **GLUE (algebraic geometry of curves over `ℚ`; descent along a surjective morphism).** Let `Y`, `X`,
`X'` be proper smooth curves over `ℚ`, `f : Y → X` surjective on `ℚ̄`-points and `f' : Y → X'` constant on
the `ℚ̄`-fibres of `f`. Then `f' = f ≫ h` for some `h : X → X'`. (In characteristic 0; textbook: the
scheme-theoretic image `Z` of `(f, f') : Y → X × X'` maps finitely and bijectively, with trivial residue
extensions at closed points, onto the normal curve `X`, hence isomorphically; `h = pr₂ ∘ (pr₁|_Z)⁻¹`.) -/
def FactorThroughSurj : Prop :=
  ∀ (Y X X' : Over (Spec (CommRingCat.of ℚ))), IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    IsProper X.hom → SmoothOfRelativeDimension 1 X.hom → IsProper X'.hom →
    SmoothOfRelativeDimension 1 X'.hom → ∀ (f : Y ⟶ X) (f' : Y ⟶ X'),
    (∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ f = x) →
    (∀ y y' : fieldPt Qbar ⟶ Y, y ≫ f = y' ≫ f → y ≫ f' = y' ≫ f') →
      ∃ h : X ⟶ X', f ≫ h = f'

/-! ## Proofs -/

/-- `PairsLift` from any coarse witness whose forgetful map is onto `X(ℚ̄)`. -/
theorem pairsLift_of_witness {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {X : Over (Spec (CommRingCat.of ℚ))} {Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar)}
    {fY : Y ⟶ X} (h6 : X6Props Y Φ X Ψ fY)
    (hs : ∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x) : PairsLift := by
  intro Q
  obtain ⟨y, hy⟩ := hs (Ψ.symm (Quotient.mk _ Q))
  obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ Qbar y)
  refine ⟨P, ?_⟩
  rw [← h6.2.2.2.2.2 y P hP.symm, hy, Equiv.apply_symm_apply]

theorem pairsLift_of_canonical (h : CanonicalCoarseX6) : PairsLift := by
  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, hs, -⟩ := h
  exact pairsLift_of_witness h6 hs

theorem pairsLift_of_rep (h : LeafAdopt.R1R2fpRep) : PairsLift := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, hs, -, -⟩ := h
  exact pairsLift_of_witness h6 hs.2

/-- **`CoarseFactor` from `PairsLift` and `FactorThroughSurj`.** -/
theorem coarseFactor_of (hL : PairsLift) (hF : FactorThroughSurj) : CoarseFactor := by
  intro Y Φ X X' Ψ Ψ' fY fY' h1 h6 h6'
  have hval : ∀ y : fieldPt Qbar ⟶ Y, Ψ (y ≫ fY) = Ψ' (y ≫ fY') := by
    intro y
    obtain ⟨P, hP⟩ := Quotient.exists_rep (Φ Qbar y)
    rw [h6.2.2.2.2.2 y P hP.symm, h6'.2.2.2.2.2 y P hP.symm]
  have hsurj : ∀ x : fieldPt Qbar ⟶ X, ∃ y : fieldPt Qbar ⟶ Y, y ≫ fY = x := by
    intro x
    obtain ⟨Q, hQ⟩ := Quotient.exists_rep (Ψ x)
    obtain ⟨P, hP⟩ := hL Q
    obtain ⟨y, hy⟩ := h1.2.2.2.2.2 |> fun _ => (Φ Qbar).surjective (M3.mk P)
    refine ⟨y, Ψ.injective ?_⟩
    rw [h6.2.2.2.2.2 y P hy, hP, hQ]
  have hconst : ∀ y y' : fieldPt Qbar ⟶ Y, y ≫ fY = y' ≫ fY → y ≫ fY' = y' ≫ fY' := by
    intro y y' e
    apply Ψ'.injective
    rw [← hval, ← hval, e]
  obtain ⟨h, hh⟩ := hF Y X X' h1.1 h1.2.1 h6.1 h6.2.1 h6'.1 h6'.2.1 fY fY' hsurj hconst
  refine ⟨h, fun x => ?_⟩
  obtain ⟨y, rfl⟩ := hsurj x
  rw [Category.assoc, hh, hval]

/-- `CoarseFactor` from the leaf-form `CanonicalCoarseX6` (already a hypothesis of qm-glue's
`r1r2fpRep_of_canonical`) and the AG glue. -/
theorem coarseFactor_of_canonical (hC : CanonicalCoarseX6) (hF : FactorThroughSurj) : CoarseFactor :=
  coarseFactor_of (pairsLift_of_canonical hC) hF

/-- `CoarseFactor` from the bundle leaf `R1R2fpRep` (the hypothesis of qm-glue's
`x6ConicModel_of_canonical'`) and the AG glue. -/
theorem coarseFactor_of_rep (hR : LeafAdopt.R1R2fpRep) (hF : FactorThroughSurj) : CoarseFactor :=
  coarseFactor_of (pairsLift_of_rep hR) hF

end HDec.QMSplit.Moduli

#print axioms HDec.QMSplit.Moduli.coarseFactor_of
#print axioms HDec.QMSplit.Moduli.coarseFactor_of_canonical
#print axioms HDec.QMSplit.Moduli.coarseFactor_of_rep
