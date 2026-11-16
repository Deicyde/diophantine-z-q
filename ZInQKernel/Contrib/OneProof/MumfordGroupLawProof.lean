import ZInQKernel.Contrib.OneProof.MumfordRigidity
import ZInQKernel.Contrib.CloudB3SC2Mumford.Algebraize
import ZInQKernel.Contrib.CloudB3SC2Mumford.Pipeline.Affine
import ZInQKernel.Contrib.CloudB3SC2Mumford.Glue

/-!
# `MumfordGroupLaw`, proved

`ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw` (Mumford, *Geometric Invariant Theory*, Thm. 6.14 over a
locally noetherian base): a proper smooth geometrically connected family `F → S` with a section `e`, all of
whose field fibres are abelian varieties with identity `e(s)`, is a group object in `Over S` with identity `e`.

The proof has three parts, in `ZInQKernel/Contrib/CloudB3SC2Mumford/`:

* `Algebraize.lean`: morphisms between proper schemes over a complete noetherian adic ring are determined by,
  and can be built from, compatible morphisms of their adic thickenings (`properAlgebraization`; the graph
  construction from the proper-scheme existence theorems of the vendored Fermat development);
* `Pipeline/`: over a noetherian ring, the vendored Fermat proof of the group law (deformation over the adic
  thickenings, algebraization over the completion, faithfully flat descent, spreading out, gluing), with the
  projective algebraization step replaced by `properAlgebraization` (`affineGroupLaw_of_algebraization`);
* `Glue.lean`: the unique affine-local group laws glue to a group object over an arbitrary locally noetherian
  base, and the abelian-variety field fibres give the abelian geometric fibres the affine statement needs
  (`mumfordGroupLaw_of_affine`).

No projectivity or other assumption is added.
-/

namespace ZInQ.Contrib.CloudB3SC2Mumford

theorem mumfordGroupLaw_proof : ZInQ.Contrib.MumfordRigidity.MumfordGroupLaw :=
  mumfordGroupLaw_of_affine (affineGroupLaw_of_algebraization properAlgebraization)

end ZInQ.Contrib.CloudB3SC2Mumford
