/-
Cloud batch 3 W16 H99 port (2026-11-16).
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b, recovered
StacksFrontier/AlgebraicGeometry/Variety/Geometrically/ConnectedPoint.lean.
Changes: Import paths moved to CloudB3W16Connected.
Citation attributes/commands and registration imports omitted; mathematical references retained.
Only the rational-section consequence of Tag 04KV is retained; the unused residue-field criterion and algebraic-closure/irreducibility imports are omitted.
The older vendoring notice below is retained as provenance, not a claim that
this additional port is unchanged. See LICENSE and NOTICE.md in this family.
-/
/-
H71 lane04 VENDORED copy (root-default, publication decision 2026-11-14) of `StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint`,
from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b (original notices retained below). Original sha256 7b4cfebe34df7e0d493f1de1b4a81060edb3c3feec0905bbff3e96f95239c165.
Modification notice (2026-11-14): module path ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint; 4 import directive rewrite(s) to the
vendored/published module identities; 0 resolved `_c496` family rename(s) of declarations
colliding with the published fork graph; the original package type-inference/printing
options (autoImplicit, relaxedAutoImplicit, maxSynthPendingDepth, pp.unicode.fun) as
explicit `set_option` lines after the imports (diagnostic weak.linter options are left to
the root library). No other change.
-/
module

public import ZInQKernel.Contrib.CloudB3W16Connected.StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true


/-!
# Connected schemes over a field with a distinguished point

A connected scheme over a field is geometrically connected if the field is algebraically closed
in the residue field of one of its points. In particular, a connected scheme with a rational
point is geometrically connected.

## Main results

* `AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_algebraicClosure_eq_bot`
  gives geometric connectedness from a point whose residue field has no new algebraic elements
  over the base field.
* `AlgebraicGeometry.geometricallyConnected_of_connectedSpace_of_section` gives the
  rational-point consequence.

## Implementation notes

In the first result, the algebra structure on the residue field is the one induced by the
structure morphism: it is the composite from the base field to the residue field at the image
point, followed by the residue-field map of the morphism. The second result expresses a rational
point as a section of the structure morphism.

## References

* [Stacks Project, Tag 04KV](https://stacks.math.columbia.edu/tag/04KV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 04KV, rational-point consequence.** A connected scheme
over a field with a rational point is geometrically connected. -/

public theorem geometricallyConnected_of_connectedSpace_of_section
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [ConnectedSpace X] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  have hgc : GeometricallyConnected (𝟙 (Spec (.of k))) := by
    refine ⟨fun K _ y Z fst snd hp ↦ ?_⟩
    let := hp.isIso_snd_of_isIso
    exact (show ObjectProperty Scheme from fun Y ↦ ConnectedSpace Y).prop_of_iso
      (asIso snd).symm inferInstance
  let : GeometricallyConnected (s ≫ f) := hs ▸ hgc
  exact geometricallyConnected_of_comp_of_connectedSpace k s f

end AlgebraicGeometry
