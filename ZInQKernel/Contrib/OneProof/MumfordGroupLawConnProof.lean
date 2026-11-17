import ZInQKernel.Contrib.OneProof.MumfordGroupLawConn
import ZInQKernel.Contrib.CloudB3SC2Mumford.MumfordGroupLaw

/-!
# `MumfordGroupLawConn`, proved

`DictModels.MumfordConn.MumfordGroupLawConn` is Mumford's *Geometric Invariant Theory* Thm. 6.14 over a connected
locally noetherian base, in the form of the open hypothesis: a proper smooth geometrically connected family `F → S`
with a section `e`, all of whose field fibres are abelian varieties with identity `e(s)`, is a group object in
`Over S` with identity `e`.

`ZInQKernel/Contrib/CloudB3SC2Mumford/MumfordGroupLaw.lean` proves the same statement without the connectedness
hypothesis (`mumfordGroupLaw_unconditional`), from

* morphism algebraization for proper schemes over a complete noetherian adic ring (`Algebraize.lean`, the graph
  construction from the proper-scheme existence theorems of the vendored Fermat development),
* the vendored Fermat proof of the group law over a noetherian ring with its projective algebraization step replaced
  (`Pipeline/`), and
* gluing of the unique affine-local group laws over the directed affine cover (`Glue.lean`).

The repository's `conn_of_field` turns it into the open hypothesis. No assumption is added.
-/

namespace ZInQ.Contrib.CloudB3SC2Mumford

theorem mumfordGroupLawConn_proof : DictModels.MumfordConn.MumfordGroupLawConn :=
  DictModels.MumfordConn.conn_of_field mumfordGroupLaw_unconditional

end ZInQ.Contrib.CloudB3SC2Mumford
