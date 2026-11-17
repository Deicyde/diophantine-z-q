# neron-descent (fleet note)

**Verdict: target not reached. `neronSchemeExtensionDedekind` cannot be removed with no new leaf on this host.**
Report: docs/research/neron-descent.md. Log: scratch/neron-descent/log.md.

* **Descent route (a).** The missing step is effective descent of the Néron model from `R^h` (FLT gives it over every
  henselian DVR) to the non-henselian `R = (𝓞_L)_v`.
  * The map `R → R^h` is not finite and cannot be made finite: finite extensions of `(𝓞_L)_v` are never henselian,
    and extending to the finite closure moves the problem to the other primes.
  * Effective descent of objects on this host exists only along finite étale maps (vendored FLT,
    `DescentAction.effective_of_finiteEtale`, with the AF condition). Mathlib 4.35 descends only morphisms and
    morphism properties.
  * Along an étale neighbourhood, the datum is trivial on the special fibre. Effectivity comes down to (SA): every
    special-fibre point has an affine neighbourhood whose generic fibre is defined over `K`. That is Raynaud's
    quasi-projectivity (BLR 6.4/1) plus descent of quasi-projective schemes (BLR 6.1/7, SGA 1 VIII 7.7); numbers
    UNVERIFIED. None of it is in the tree, and it is weeks of formalization.
  * Translates and intersections of conjugates fail for the stated reasons (report §3.3).
* **Consumer route (b).** T41's height rows need global Néron group models over `𝓞_L` at every `L`: the stable height
  is an infimum over global models, and `stableFaltingsHeight_add_le` uses the leaf at an arbitrary `L`. No
  henselian substitute exists without restating the printed height leaves. r6, SS1 and SS3 read
  `HasSemistableReduction` over non-henselian DVRs.
* **Best available fold.** dedekind-free's count-neutral narrowing to `NeronExt.NeronDVRLocal`, a genuine
  literature leaf (BLR 1.4/3 at `(𝓞_L)_v`).
* **Integration bug found (VERIFIED).** dedekind-free's `ZInQKernel/Contrib/OneProof/MumfordGroupLawDescent.lean` does
  not build on fork main d879bb73: L855 omits the `¬ IsField D` argument added by 00f923e24.
  * One-line fix: `h Rv L (A.baseChange L) (IsDiscreteValuationRing.not_isField Rv)`.
  * The fixed copy `scratch/neron-descent/GroupLawDescentFixed.lean` compiles; `mumfordGroupLawDVR_proof` has
    standard axioms.
  * dedekind-free's fold (OpenResearchLeaves31) must be rebased to OpenResearchLeaves38.
* **Compiles.** `scratch/neron-descent/NeronDescent.lean`: verbatim copy of the field (`copy_iff := Iff.rfl`), the
  corrected `neronDVRLocal_of_dedekind`, the readers from `NeronDVRLocal`, and `#check`s of the FLT descent tools.
  Standard axioms.
* **Remains.** Formalizing Raynaud's quasi-projectivity and quasi-projective descent, or (SA) plus affine patching
  along `R → R^h`. No new Prop was introduced and no statement changed; no file under ZInQKernel/ was edited (the
  merge brought in dedekind-free's file as is).
