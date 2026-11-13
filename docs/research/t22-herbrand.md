# T22: Herbrand quotient and transitivity

## Scope and frozen statements

**Both parts of T22 are proved in Lean.** The closed provider is

```lean
ZInQ.Contrib.Herbrand.t22_holds :
  PkgI6.HerbrandQuotient ∧ PkgI6.HerbrandTransitivity
```

in `ZInQKernel/Contrib/Herbrand/Tower.lean`, with separate closed
`herbrandQuotient_holds` and `herbrandTransitivity_holds` providers. The final
source-order compilation of all ten contribution modules and the direct
`Audit.lean` exact-type check exited 0 with no warnings on Lean 4.35.0.
All reported dependencies are exactly `propext`, `Classical.choice`, and
`Quot.sound`. No additional explicit, implicit, typeclass, or `Fact` premise
occurs outside the two actual propositions. Both quantifier ranges are
retained: every real upper index and every real lower index at least `-1`.

This is a focused, author-verified proof contribution. It is not proof of H,
assembled-manuscript acceptance, an official record, or independent Astra
acceptance; those judgments remain separate and are not claimed here.

The working source is main commit
`a5937595cde3e3db00975b81e5171cdef92c801a`. The actual targets are the conjunction

```lean
PkgI6.HerbrandQuotient ∧ PkgI6.HerbrandTransitivity
```

in `ZInQKernel/HDecomp/Conductor/I6Base.lean`, lines 381–408. SHA256 of that
unchanged file:
`3a2688e5271203cb1d28663fefe3c017426a43dd4c5f4a710f0dabe6de96ce2d`.
The PR41 extraction at head
`2757349fbd8ca613340b679bbd149f78c2baba6b` is a frozen engineering reference,
not a registered or accepted target. It is not imported as a proof supplier.
The contribution does not edit the statements, registry, pins, checker,
existing source, manuscript, or protected review records.

The quotient statement quantifies over a tower `A → C → B` of genuine DVRs,
finite and torsion-free over `A`, with separable Galois fraction fields,
`A` adically complete, and `ResidueField A` perfect. It uses the actual ring
homomorphism `r : Aut_A(B) →* Aut_A(C)` with the compatibility equation

```lean
∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)
```

and requires `upperRam A C v = (upperRam A B v).map r` for **every real `v`**.
`Module.Finite C B` is not an extra quotient premise: it follows from finite
`A`-generation by `Module.Finite.of_restrictScalars_finite A C B`.
The transitivity statement also names finite torsion-free `B/C` and requires
`herbrandPhi A B u = herbrandPhi A C (herbrandPhi C B u)` for **every `u ≥ -1`**.
Galoisness of `Frac(B)/Frac(C)` follows from Galoisness over `Frac(A)` and the
actual scalar tower, not from an extra assumption.

## What the locked definitions mean

`lowerRam A B i` is the inertia subgroup of
`(maximalIdeal B ^ (i + 1)).toAddSubgroup`: its members satisfy
`σ b - b ∈ maximalIdeal B ^ (i + 1)` for every `b : B`.
For real `u`, `lowerRamR A B u` is the whole automorphism group if `u ≤ -1`,
and otherwise is `lowerRam A B ⌈u⌉.toNat`. Thus it is constant on `(i-1,i]`,
not on `[i,i+1)`. Its `i+1` ideal-power offset is retained.

The actual Herbrand function is the interval integral

```lean
∫ t in (0 : ℝ)..u,
  (Nat.card (lowerRamR A B t) : ℝ) /
    (Nat.card (lowerRamR A B 0) : ℝ)
```

and the upper group is `lowerRamR` at
`sInf {u : ℝ | -1 ≤ u ∧ v ≤ herbrandPhi A B u}`. The finite-sum formula in the
contribution is **proved from this integral**; it is not substituted for the
locked definition or treated as the quotient/transitivity leaf.

For `-1 < t ≤ 0` the density is one. At the isolated endpoint `t = -1`, the
numerator can instead be the order of the full group. The interval-integral
argument uses equality on the half-open integration interval, so that endpoint
is not incorrectly asserted to have density one. Consequently `φ(u)=u` on the
**closed** interval `[-1,0]`. Every lower subgroup is nonempty and finite, so
`|G₀|>0`; no zero-denominator convention or infinite-group `Nat.card=0` shortcut
supplies a proof.

## Supplier actually located

The advertised theorem exists in
[`TauCeti/NumberTheory/LocalField/Herbrand/UpperQuotient.lean`](https://github.com/TauCetiProject/TauCeti/blob/a6027b1d24fcb935c53bd5b50d11b40991cda418/TauCeti/NumberTheory/LocalField/Herbrand/UpperQuotient.lean),
under the full name
`TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`.
The exact source revision read is
`a6027b1d24fcb935c53bd5b50d11b40991cda418`.
Its transitivity supplier is `herbrand_tower` in the sibling `Tower.lean`, not
merely a theorem about `psiNat`. The upper quotient proof calls both the real
lower quotient theorem and inverse-Herbrand transitivity. The Serre book
locators quoted by these sources remain unverified here against the printed
primary edition; no such citation is used as an added Lean premise.

This revision uses Lean `v4.36.0-rc2` and Mathlib
`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`. The receiving project instead uses
Lean `v4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`; neither pin is changed.
Upstream `LICENSE` and the file notices identify Apache-2.0. The complete
license text is retained below; each adapted source retains its relevant
copyright/authorship notice and a prominent changed/ported notice.

The source's field theorem requires `IsNonarchimedeanLocalField` for all three
fields, compatible valuative extensions, and
`RamificationIndexDomain = Set.Ici (-1 : ℝ)`. Mathlib's local-field class
includes local compactness and supplies **finite** residue fields. Actual T22
allows perfect **infinite** residue fields. A direct application that adds
local compactness or finite residue would not close the target.

The usable route instead extracts the ring proof. Tau Ceti's general
`RingTheory/DiscreteValuationRing/Monogenic.lean` proves that a finite faithful
extension of DVRs with separable residue extension is monogenic; completeness
is not needed once the upstairs ring is already assumed to be a DVR.
`Monogenic.lean` ports the Newton/residue-generator/Nakayama proof, including
its principal-ideal power helper. Perfectness of the actual downstairs residue
field supplies separability, and finite residue extension also transports
perfectness to the intermediate residue field. No finite-residue instance is
introduced.

The checked source slice is listed below. All hashes are SHA256 of complete
UTF-8 files at the same pinned revision; it is not a claim to have ported or
independently accepted the entire upstream field library.

- `LocalField/Herbrand/UpperQuotient.lean`:
  `75c8d6d5d3ba7cbf5bc0762cba269bc2083ea0422490e08ecaad29b75cfd3922`.
- `LocalField/Herbrand/Tower.lean`:
  `cb7150f1a843647adee47fbd0c618d8fc12169221dafa8492e18787a984b17d9`.
- `LocalField/Herbrand/Quotient.lean`:
  `5a706028202abf199fd146af6cd87a6459a9eb8fb85cee8bc2ced2954c581a67`.
- `LocalField/Herbrand/Basic.lean`:
  `a00ea3a1f2d51d1bb7ba9a8c14dee5b6ab47ed244112256e9be1e7b6a0e71c1b`.
- `LocalField/LowerIndex.lean`:
  `a73163eb2c33d1cdc5e6d93250e002b06b7b111ad2d0da33364a53ab85b90fbc`.
- `RingTheory/LocalRing/RamificationGroup.lean`:
  `a4996fc47f3760d111c1c131febdc86ca62c812dffbeb4d4191688ada09113c4`.
- `RingTheory/LocalRing/Monogenic.lean`:
  `f9b301a678c8614f345018152f96dbbb562aa9b4fcb07ef14b2c175759300a99`.
- `RingTheory/DiscreteValuationRing/Monogenic.lean`:
  `aa078f8a606b8c73b7f7aca434b2a829a21b7640aea14da523beded02ac0d6d4`.
- `RingTheory/Ideal/Operations.lean`:
  `ecba32e3decc94eb2083d8696ea1f8cbb79983ba75c13d17232b13d3d7139634`.
- `RingTheory/Invariant/Basic.lean`:
  `566beaa35ae5370f23f02f98deeb99a0cf6ea5a31f0462e7beb0d956b13279d2`.
- `RingTheory/Ideal/Inertia.lean`:
  `23d2a28af75dbbc18bb326c3c28bd2582c6ef10b2dde07079557e7f0785ca165`.
- `Algebra/Ring/Action/End.lean`:
  `1ca2c6d8d8a27118c6f074408ef0c878dafaf4baae1a8d7c0195337ee72d9657`.
- `RingTheory/Valuation/AddValuation.lean`:
  `20202eb862d5e15554fdb8e3233f8bc89fbf24344587772993f0eab84e012ace`.
- `LICENSE`:
  `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.

Here `LocalField/…` abbreviates the source prefix
`TauCeti/NumberTheory/LocalField/…`; the other paths have source prefix
`TauCeti/`.

## Exact connecting arguments and current coverage

1. **Actual groups and maps.** `Restriction.fractionAutEquiv` uses Mathlib's
   `galRestrict A (FractionRing A) (FractionRing B) B`. Finite integrally closed
   ring extensions supply integral-closure and finite automorphism instances.
   Its forward and inverse application lemmas commute with the actual
   fraction-ring algebra map. `canonicalRestriction` transports
   `AlgEquiv.restrictNormalHom (FractionRing C)` through these equivalences.
   Injectivity of `C → B` proves that the target's equation `hr` uniquely
   determines this map. Its surjectivity follows from fraction-field normality.
   Its kernel is exactly the range of the actual
   `AlgEquiv.restrictScalarsHom (S := C) A`. These are compiled bridges, not
   assumptions of the target provider.
2. **Normalization.** `Valuation.addVal_algebraMap` proves
   `v_B(algebraMap A B a) = e(B/A) · v_A(a)`, with
   `e(B/A)=(maximalIdeal B).ramificationIdx A`, including `a=0` in `ℕ∞`.
   It identifies the mapped maximal ideal with `𝔪_B^e`, using uniformizer
   factorizations and the actual ideal ramification index.
   `natCard_lowerRam_zero` proves `|G₀|=e` from Mathlib's invariant-ring and
   separable-residue inertia theorem. Perfectness, rather than finiteness, is
   the residue hypothesis.
3. **Concrete arithmetic supplier.** `LowerIndex.lowerIndex` is
   `⨅ b : B, v_B(σ b-b)`. Generator congruence tests and divisibility are proved
   by algebra induction; monogenicity computes that infimum at an actual
   generator. `Coset.lean` compares the displacement of a generator of `C/A`
   with the value of the transformed orbit polynomial of a generator of
   `B/A`. Its two explicit divisibilities give associated elements and hence
   the exact Serre identity
   `e(B/C)i(rσ)=∑τ i(σ·restrictScalars τ)`. The sign reversal of polynomial
   factors is justified by `AddValuation.map_sub_swap`, not suppressed.
   This concrete coset module has compiled with only the three standard Lean
   axioms. It is an arithmetic supplier, not by itself either complete T22 leaf.
4. **Real analytic supplier.** `Analysis.lean` proves integrability, affine
   formulas on actual constant-filtration intervals, strict monotonicity,
   continuity, and surjectivity on `[-1,∞)` for the locked `herbrandPhi`.
   It proves `upperRam A B (herbrandPhi A B u)=lowerRamR A B u` for every
   `u≥-1` directly from an `IsLeast` argument for the locked `sInf`. There is
   no implicit replacement of `sInf` by an unproved inverse or a rounded index.
5. **Quotient and full assembly.** The maximal-index-in-a-finite-coset argument
   converts the concrete Serre identity into the actual real lower-quotient
   formula. `Quotient.lowerRamR_quotient` and its actual map-times-kernel
   cardinality form are proved. At zero this count gives
   `|G₀|=|(G/H)₀|·|H₀|`; no separate assumed ramification-index tower formula
   is used. The affine integral formulas then identify the slopes of
   `φ_B/A` and `φ_C/A ∘ φ_B/C` on each natural unit interval. Induction, a
   real floor used only to locate the containing interval, and the separately
   proved identity on `[-1,0]` prove `herbrandPhi_tower` on the whole half-line.
   The actual sInf inverse converts this result and the lower quotient to
   `upperRam_quotient` for every real `v`. The `v≤-1` case uses the actual
   whole group and the proved surjectivity of restriction. Both closed leaf
   providers and their conjunction compile with only the three standard
   axioms, and `Audit.lean` checks exactly those main proposition types.
6. **Separate reusable uniformizer interface.** `Uniformizer.lean` exposes
   `adjoin_eq_top_of_residue_surjective_of_span_eq_maximalIdeal`: for a finite
   local algebra, a surjective residue algebra map and `span {π}=𝔪` imply
   `Algebra.adjoin R {π}=⊤`. Its DVR wrapper is
   `dvr_adjoin_eq_top_of_residue_surjective`, for every irreducible `π` in a
   finite torsion-free DVR extension. These are proved from the local-ring
   generation criterion with the polynomial `X`; neither perfectness,
   completeness, finite residue, nor a minpoly-degree equality is assumed.
   This is a coordination helper for the different-bound work, not a hidden
   premise or dependency of the closed T22 provider.

### Convention and exceptional-case checks

- `A,C,B` correspond to upstream integer rings of `K,L,M`; the output has the
  same ring automorphism carrier used by the target, not merely an isomorphic
  but unidentified group.
- Forward transitivity is `φ_B/A = φ_C/A ∘ φ_B/C`. Inverting reverses the
  composition order: `ψ_B/A = ψ_B/C ∘ ψ_C/A`. The quotient source's equality
  has the opposite written direction to the target and must be reversed.
- All noninteger lower indices use the **ceiling**, with cells `(i-1,i]`.
  Natural floors in a finite-sum proof locate a cell only; they do not alter
  the group convention or truncate the quantified real domain.
- At `v≤-1`, the actual sInf upper group is `⊤`; restriction maps it to `⊤`
  because the actual map is proved surjective. The `v=-1` endpoint is not
  omitted or deferred to continuity.
- Identity automorphisms have lower index `⊤`; nonidentity automorphisms have
  finite lower index. `ℕ∞` avoids subtracting one from an infinite value or
  cancelling a zero ramification index. The unramified/maximal-index-zero
  coset case has real endpoint `-1`, not a truncated natural subtraction.
- The lower subgroup rule is valid without normality. Quotient surjectivity
  and the stated transitivity are used only under the target's Galois
  fraction-field conditions. A nonnormal intermediate extension is not
  silently supplied with an automorphism-group version of the missing
  Herbrand function.
- No Frobenius or reciprocity normalization is used in this proof slice.
  Arithmetic versus geometric Frobenius orientation elsewhere is unchanged.

## Verification and acceptance limits

The scoped commands are ordinary Lean commands from the repository root, with
at most two compiler processes and `LEAN_NUM_THREADS=2` / `lean -j2`. With the pinned dependency and main-base build outputs available, the exact
source-order verification from the repository root is:

```sh
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/Herbrand
for module in Monogenic Uniformizer Restriction Valuation LowerIndex Coset Analysis Quotient Tower Audit
do
  LEAN_NUM_THREADS=2 lake env lean -j2 \
    -o ".lake/build/lib/lean/ZInQKernel/Contrib/Herbrand/$module.olean" \
    "ZInQKernel/Contrib/Herbrand/$module.lean" || exit
done
```

The final run recompiled those **ten** modules sequentially from their current
source, in dependency order, and refreshed only their private contribution
oleans. It exited 0 with no warnings. `Audit.lean` gives three closed theorems
of the exact actual conjunction and the two actual component propositions;
`#print` shows no added arguments on `t22_holds`. All axiom reports contain
exactly the three standard axioms listed above. The forbidden-construct,
UTF-8/LF, final-newline, and whitespace checks pass. The public note contains
no private host, session, credential, or absolute-path material, and its
retained license block is byte-identical to the pinned upstream `LICENSE`.

This is author-side compilation and source/application checking, not an
independent acceptance decision. There is no unresolved Lean proof obligation
in the T22 contribution. Independent statement-fidelity, supplier-coverage and
integration review remain open. No dependency-tree writes, downloads of package
caches, update/pin changes, broad root build, commit, push, pull request,
landing, human outreach, or protected acceptance was performed.

AI assistance with Metamate was used to extract and adapt the ring proof,
construct the canonical-map and normalization bridges, and compile the Lean
contribution. No served model identity is asserted. Compilation and source
comparison are not a designated independent Astra decision. A source-first
independent review of the exact final statements, suppliers, conventions, and
consumer remains necessary before integration or acceptance. This is a
non-release proof contribution; current manuscripts, TeX/PDF artifacts,
release manifests, and official-record duties are not changed by it.

## Frozen contribution sources

All paths below are relative to `ZInQKernel/Contrib/Herbrand/`. These are the
source bytes used by the final clean source-order build and exact-type audit;
hashes are SHA256. The public note's own digest is reported separately to
avoid a self-referential binding.

- `Monogenic.lean` —
  `a2b761efd76e4ee50a00d277824f943ee34b4f617c273df0d17faf5a8b68e24d`.
- `Uniformizer.lean` —
  `9dbc8876d60f5ac91d2763a3f8c50de9a2a68b99682727043d5e5fa7e24b0249`.
- `Restriction.lean` —
  `4ed653b6c1f277a5a2ae790fdbccc94bc722ea9a0736ecffda51d1cdf4171183`.
- `Valuation.lean` —
  `3c789d0b86df3d6c6042ec60863726c1e6c6106a054066145d4a778a7c2a4f57`.
- `LowerIndex.lean` —
  `0b2fb1a3942a951e4c4a76ec265f904a457be43fa72576458387ae42969c82a3`.
- `Coset.lean` —
  `a564ce9475de49a0bcec71e7936a5ade15ea092307427c00dbd2ba957dbbbdc1`.
- `Analysis.lean` —
  `01ff825f6891b2f300905072cc086e68358447a162b2cf56eacc1f79e73fe376`.
- `Quotient.lean` —
  `3f4a013dd5f1cc4415a78d3447b3c9039d9024fa97f98e437146c05226f4fa67`.
- `Tower.lean` —
  `ca4fcd36a2b34ea52ed6d0fd0f9b54393a0aaac00befdd822b8b5bcf8a961e8f`.
- `Audit.lean` —
  `2a3702f5d93c853ebcb5c34303d577770db274cff7525ad22831a51e2f1f048a`.

## Retained upstream license

Upstream Tau Ceti source portions are released under the following license.

```text
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright {yyyy} {name of copyright owner}

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
```
