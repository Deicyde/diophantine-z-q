# shimura-split2 (2026-11-15)

**Result.** The GLUE fields `rayClassCMAb` and `shimuraFamilyAb` are proved in Lean without gt-rayclass's composite
`ShimuraMainThmIDeligneY3AbU`. Two new leaves enter, each a single theorem, and all the glue is proved. The file is
`ZInQKernel/Contrib/OneProof/ShimuraSplit2.lean` (imports only RayClassShimura). Report:
`docs/research/shimura-split2.md`.

* `rayClassCMAb_of_leaves2 : DeligneComponentsX6PrintedAb → QMReciprocityL3 → UniformizationLeafAll →
  GAGAMorphism → MumfordTorsionAlgClosed → RayClassCMAb`. Only the fine witness of the first input is used.
* `shimuraFamilyAb_of_leaves2 : DeligneComponentsX6PrintedAb → ShimuraHolModAll → ShimuraFamilyAb`.

**Key idea.** Reciprocity is stated on objects. `MIsAt P z g` says that `P` is `T(z,g) = ℂ²/ι(B∩𝒪̂g⁻¹)(z,1)ᵀ` with its
level structure. `QMReciprocityL3` says: if `P` is `T(z,g)`, then its σ-conjugate is `T(z, q̂(s)^ε g)`. There is no
map `Ψ` and no witness, so there is nothing to normalize. This answers gt-rayclass's objection to splitting the
composite. `QMReciprocityL3` is a consequence of the main theorem of CM for `F⊗K`. `ShimuraHolModAll` is Shimura's
Main Theorem I, complex part, stated for every fine witness. It is proved equivalent to the ∃ form given one witness.

**Glue proved.**
* `DCRelTransport`: `T` is constant on `DCRel` classes.
* `UnifDetermines`: the object is determined by `(τ,g)`, from HomLatticeCorr.
* `ComplexUnifL3`: every object is some `T(τ,u)`. Uses a 72-entry table of units of `𝒪` covering `(𝒪/3)^×`,
  checked by `decide`.
* The ray-class argument on objects.
* `ClassNumberOneB` and rigidity are not used.

**Checks (VERIFIED).**
* The file compiles. `lake build` of Main, Discharges and the file succeeds.
* `#discharges` matches both fields, with only the standard axioms.
* The autofold dry run compiles (`sixContactMin_of_open27`, standard axioms).
* An independent model review found both leaves true and not stronger than their prints. It found one gap in the
  paper derivation, which is now closed in §3.1.

**Count.** 45/13 → 45/13 with honest ratings: `qmReciprocityL3` is kind `consequence`, and `shimuraHolModAll` is
published but pending reading. It becomes 47/11 if readings clear both, against gt-rayclass's 45/12 (46/11 if its
composite were re-rated).

**What remains.**
* Readings: Shimura 1967 §3 and Deligne 1971 §4 for the QM form of reciprocity; Shimura 1963 and Deligne §4 for
  the holomorphic moduli map.
* The fold is not applied: integrator. Spec: `scratch/shimura-split2/autofold-spec.json`.
* This fold and gt-rayclass's are alternatives; only one can be applied.
