# gt-rigidity: summary

**Result.** `LeafQM.AV.R1UnivRigid.MumfordRigidityCore` is discharged by a reduction, not proved outright. It
now rests on two published leaves, and its clause (a), Mumford *GIT* Cor. 6.4 (an `S`-endomorphism fixing `e`
is a homomorphism), is a Lean proof. File: `ZInQKernel/Contrib/OneProof/MumfordRigidity.lean` (imports only
`ZInQKernel.OneProof.H.TailZ16`). Report: `docs/research/gt-rigidity.md`.

**What compiles** (VERIFIED, standard axioms only). `#discharges` output (`scratch/gt-rigidity/discharges-output.txt`):
* `mumfordRigidityCore_of_pushforward : MumfordGroupLaw → PushforwardStructureSheaf → MumfordRigidityCore`.
  This is the recommended route.
* `mumfordRigidityCore_of_printed : MumfordGroupLaw → RigidityLemma → MumfordRigidityCore`.
* Both discharge `OpenResearchLeaves16.mumfordRigidityCore`: "67 open hypotheses, 521 theorems checked, 2
  discharge one".

**Leaves** (theorem numbers UNVERIFIED, no network):
* `MumfordGroupLaw`: *GIT* Thm 6.14, the existence of the group law. It is the old leaf with clause (a)
  dropped; `mumfordGroupLaw_of_core` proves it is weaker.
* `PushforwardStructureSheaf`: `𝒪_S ≅ p_*𝒪_X` for `p` proper, smooth and geometrically connected (EGA III
  7.8.6, Stacks 0E0L, cohomology and base change).
* `RigidityLemma`: *GIT* Prop 6.1, needed by the first route only.

**Proved in Lean along the way:**
* Connected components of a locally noetherian scheme are open.
* Local rigidity from `𝒪_S ≅ p_*𝒪_X`.
* The rigidity lemma applied on each connected component.
* The defect `f(xy)(f(x)f(y))⁻¹` is constant on every fibre, by the kernel's field-level rigidity applied to the
  base change to each residue field.
* Cor. 6.4.

**What remains:**
* `MumfordGroupLaw` needs Grothendieck's deformation theory, which is not in Mathlib.
* `PushforwardStructureSheaf` needs cohomology and base change, which is not in Mathlib.
* Not done: stating `MumfordGroupLaw` in its exact printed form (`S` connected, one fibre) and gluing the group
  laws over the connected components in Lean.
