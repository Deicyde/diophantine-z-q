# T13: Skolem–Noether, full embedding form

## Proposed result and scope

`ZInQ.Contrib.SkolemNoether.t13` in
`ZInQKernel/Contrib/SkolemNoether/Basic.lean` proves the exact closed quantified
`SkolemNoether` proposition in research revision
`533aa66cc3485e21f2d90303e3a34f79d081722d`,
`scratch/h-decomposition/Leaves.lean`. That whole scratch file has SHA-256
`e26677d268dc543bd906a1084f9f380df37eed7789c4f54204d7739b062034ae`.
It is a statement reference only and is **not imported**.

For every field `K`, central simple finite-dimensional `K`-algebra `A`, simple
finite-dimensional `K`-algebra `B`, and two algebra homomorphisms `f g : B →ₐ[K] A`,
one unit `u : Aˣ` satisfies
`∀ b : B, g b = (u : A) * f b * ((u⁻¹ : Aˣ) : A)`.
There is no extra hypothesis, including no centrality of `B`, separability,
characteristic restriction, surjectivity of either map, or assumed leaf proof.
`skolemNoether` is the universe-polymorphic version; `t13` explicitly closes all
quantifiers at the exact leaf's universes. The automorphism corollary is separately
named `exists_unit_conj_of_algEquiv` and is **not** being substituted for T13.

This is a proof-only, non-release proposal on main base
`a5937595cde3e3db00975b81e5171cdef92c801a`, branch
`work/issue37-t13-skolem-noether`, with changes deliberately left uncommitted.
It does not discharge H, add a registry entry/provider, change the headline,
modify a manuscript, promote a polynomial record, or publish acceptance.
The exact five modules and this note are the entire proposed source change.
Manuscript/TeX/PDF release duties do not apply to this scoped helper contribution;
any future assembled-proof or record release still has its own obligations.

## Provenance and the upstream statement gap

Repository discovery used GitHub repository search, which identified
[TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti).
The source snapshot read is immutable revision
`61090fff281d0c6cece0176aa8436ab748b53048`, obtained from its GitHub source archive.
Its `lean-toolchain` is `leanprover/lean4:v4.36.0-rc2`; its manifest pins Mathlib
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2` (input revision `master`).
The copied source headers attribute authorship to **The Tau Ceti contributors**,
Copyright (c) 2026, and specify **Apache-2.0**. The snapshot has no root `NOTICE`
file. The full license read from that revision is retained in the appendix below.
The license's SHA-256 is
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.

The actual upstream
[`TauCeti.skolemNoether`](https://github.com/TauCetiProject/TauCeti/blob/61090fff281d0c6cece0176aa8436ab748b53048/TauCeti/Algebra/CentralSimple/SkolemNoether.lean#L105)
requires `Algebra.IsCentral K B` on the **source**. Its prose at lines 68–73
explicitly says the merely-simple-source/central-simple-ambient form is not
formalized there. Consequently, applying that declaration would not prove this
leaf. The present contribution adapts its proof, not its statement: the same
module construction works with the independently proved **central-right**
tensor-product simplicity result at lines 225–227 of its tensor-product module.
Thus `Aᵐᵒᵖ`, not `B`, supplies centrality. This extension is an explicit project
proof; no unproved published theorem or upstream prose assertion is trusted.

The six source files actually used, all at the immutable revision above:

- `TauCeti/Algebra/TensorProduct/Mul.lean`, coordinate lemmas, lines 59–82;
  SHA-256 `da4661717db7ea233049c75285bfca378d78c776263f84b04b3dcd34d2ad65e4`.
- `TauCeti/Algebra/Central/TensorProduct.lean`, elementwise centralizer,
  lines 58–90; SHA-256
  `cc62f685f281c8935e14cfb02eaea338cfae10567c13195f591a2897a7ded54b`.
- `TauCeti/Algebra/CentralSimple/TensorProduct.lean`, minimal-support proof and
  both orientations, lines 104–227; SHA-256
  `4dd924ce78beda349ed8eead2abdc7b4286c55422782dcc0380f64a46f69122a`.
- `TauCeti/RingTheory/Semisimple/SimpleArtinian.lean`, isotypic comparison and
  dimension classification, lines 87–131; SHA-256
  `bb722154cf8256839d5258bb9b289262b2f39ff7501aca7e52e76493df7ff45c`.
- `TauCeti/Algebra/CentralSimple/Bimodule.lean`, selected carrier/action and
  map lemmas, lines 98–151, 175–190, 219–231, 241–271; SHA-256
  `38d9acf373dd471bfc280d43cb339081d0ec08373cf2964902ecd4a22c54a07e`.
- `TauCeti/Algebra/CentralSimple/SkolemNoether.lean`, conjugator proof,
  lines 105–133; SHA-256
  `6e776c80093f2b51fd6d9c74fdaf9651815ce6c3a34821a4038217db82a9122b`.

All modified source files preserve the source notice, name the immutable revision,
and identify the adaptations. No Tau Ceti dependency, umbrella import, quaternion
example, or new compiler/Mathlib pin is added. The entire original import closure
was ten Tau Ceti files; irrelevant examples and machinery were removed. The
retained five-module closure uses only the existing pinned Mathlib.

AI contribution: Metamate selected and adapted the Tau Ceti proof fragments,
extended the proof to ambient centrality, constructed the exact closed theorem,
and ran the local checks. Serving-model identity is not independently known;
no protected reviewer identity or acceptance is asserted.

## Author's direct dependency inventory and connecting derivation

This is the author's inventory, not a substitute for a non-author source-first
reconstruction or a designated Astra coverage decision.

1. **TensorCoordinates.lean** supplies left and right coordinate multiplication
   and `forall_commute_tmul_one_iff`. Its substantive Mathlib input is
   `Subalgebra.centralizer_coe_range_includeLeft_eq_center_tensorProduct`:
   the centralizer is `Z(A) ⊗ B`; centrality identifies `Z(A)` with the bottom
   subalgebra, and tensor induction writes every element there as `1 ⊗ b`.
   That simplification also directly consumes the earlier local
   `tmul_one_mul_eq_smul` lemma; this fine-grained edge was identified in the
   preliminary non-author review and is explicitly retained here.
   A basis/free module over the coefficient field supplies the needed freeness.
2. **TensorSimple.lean** directly consumes those three coordinate/centralizer
   lemmas. A nonzero two-sided ideal has a minimal-support nonzero element.
   Simplicity of the first factor makes one of its coordinates `1` without
   enlarging support. Every additive commutator then has smaller support, hence
   vanishes. The centralizer lemma makes the element `1 ⊗ b`, with `b ≠ 0`.
   The preimage ideal in the second simple factor contains `1`, so the tensor
   ideal contains `1`. `tensorProduct_simple_right` applies this proof with
   factors exchanged and transports simplicity through the actual algebra
   equivalence `Algebra.TensorProduct.comm`.
3. **ModuleClassification.lean** directly consumes Mathlib's
   `IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`,
   `IsSimpleRing.isIsotypic`, `IsSemisimpleModule.exists_simple_submodule`, and
   `IsIsotypicOfType.linearEquiv_fun`. A finite-dimensional simple acting
   algebra is Artinian by `IsArtinianRing.of_finite`. Every finite module is a
   power of the same minimal left ideal `S`. Restriction of scalars preserves
   the given ground-field action; `finrank` gives `n * finrank K S` and
   `m * finrank K S`. The simple ideal is nonzero, so its positive dimension
   can be cancelled. The trivial module case is handled separately.
   Unlike upstream, this helper assumes the acting algebra is finite-dimensional;
   the main proof constructs that fact from the leaf's existing hypotheses.
4. **Bimodule.lean** directly constructs the action through
   `AlgHom.mulLeftRight` composed with `Algebra.TensorProduct.map f id`.
   The two synonyms `Bimodule f` and `Bimodule g` retain the same `K`-vector
   space `A` while separating their enveloping-algebra actions. The explicit
   scalar tower is proved from this representation's `K`-linearity. A pure
   tensor `b ⊗ op a` acts as `x ↦ f b * x * a`. Right linearity makes any
   module map left multiplication by its transported value `u` at `1`;
   left linearity then proves `u * f b = g b * u`. Hitting `1` gives a right
   inverse of `u`.
5. **Basic.lean** directly consumes `tensorProduct_simple_right`,
   `nonempty_linearEquiv_of_finrank_eq`, and the two bimodule map lemmas.
   Its acting ring is **exactly** `R = B ⊗[K] Aᵐᵒᵖ`. Mathlib's
   `Algebra.IsCentral` opposite instance and opposite simple-ring instance
   transfer the ambient hypotheses to `Aᵐᵒᵖ`; no centrality of `B` is used.
   The ground-field equivalence `MulOpposite.opLinearEquiv K` supplies
   finite-dimensionality of the opposite, and tensor-product finiteness
   supplies finite-dimensionality of `R`. Both modules have `finrank K A`,
   so classification gives an `R`-linear equivalence `φ`. Its value at `1`
   supplies `u`; surjectivity supplies `v` with `u * v = 1`.
   The finite-dimensional algebra `A` is Artinian and hence Dedekind-finite,
   so `Units.mkOfMulEqOne` produces a **two-sided unit**, not merely a right
   inverse. Multiplying `u * f b = g b * u` on the right by `v` gives
   `g b = u * f b * v`, the exact requested conjugacy direction.
   `t13` closes the requested quantifiers by applying this theorem; the
   automorphism corollary specializes `B = A` and `f = id`.

### Nine application obligations for the substantive extension

- **Source hypotheses:** the tensor theorem asks one central simple factor and
  one simple factor; they are `Aᵐᵒᵖ` and `B`. The classification helper asks a
  finite-dimensional simple algebra and finite modules with compatible scalar
  towers; these are the explicit `R` and two `Bimodule` structures above.
- **Constructed objects:** all rings, maps, scalar actions, carrier equivalences,
  module equivalence, inverse witness and unit are constructed in the five
  modules; there is no replacement of the source by its center or by `A`.
- **Domain/index coverage:** both input maps have domain all of `B`. The basis
  argument covers the whole tensor product, including arbitrary finite supports;
  the one constructed unit intertwines the two maps for every `b : B`.
- **Transition/comparison maps:** factor swap is the actual tensor algebra
  equivalence; carrier comparisons are `Bimodule.of`; the action is the named
  representation. Restriction of scalars in classification uses the proven towers.
- **Identity of consumed object:** classification is over exactly `B ⊗ Aᵐᵒᵖ`,
  not `B ⊗ A` or a different center. The conjugator is a unit of the original
  `A`; the final equality concerns the original `f` and `g`.
- **Coefficient/normalization conventions:** the coefficient field is the same
  `K` throughout. Opposite multiplication reverses the right factor as required;
  no determinant, sign, scalar normalization or proportionality is introduced.
- **Local conditions:** no localization, completion or topology occurs; no
  local-to-global condition is applicable to this algebraic module argument.
- **Exceptional cases:** simple rings are nontrivial. The module classification
  handles zero modules explicitly. Positive dimension of `S` justifies cancellation.
  No restriction on characteristic, separability or source centrality is imposed;
  no division by a possibly-zero element is used.
- **Downstream consumption:** this change only provides the closed T13 theorem
  and its own automorphism corollary. No main/H/glue consumer is edited or claimed
  discharged. Integrating a future use requires its own source-to-consumer check.

### Finding and bounded related-use check

The upstream source-central theorem is insufficient as a supplier for the leaf.
That is a **statement mismatch**, not a counterexample to either theorem. The
repair is the proved central-right tensor orientation above. Related-use scope is
all five new modules, their exact statement wrapper, the automorphism corollary,
and this note: none may assume source centrality, infer surjectivity of the input
maps, or relabel a special case as T13. Historical Tau Ceti and scratch sources
remain untouched. Independent coverage and final designated review remain separate.

## Verification evidence

Local compiler: Lean 4.35.0, commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
Pinned Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`.
Root `lake-manifest.json` SHA-256:
`f7ce830d517bfbcb4cdcc90bef299da854c9b28653b9accc2b13df2822233779`.
Root `lean-toolchain` SHA-256:
`ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c`.
No dependency setup/update/cache operation was run. Only local root build outputs
were written, never shared package source or build artifacts.

All five modules compiled successfully with `lake env lean`, explicitly including
modules not imported by a root. Initial contribution compilation, with no existing
contribution oleans and the pinned Mathlib cache already available, took:
TensorCoordinates 2.80 s; TensorSimple 3.40 s; ModuleClassification 2.85 s;
Bimodule 3.19 s; Basic 3.09 s (15.33 s sum; maximum RSS 2,187,816 KiB).
This is a **scoped contribution-cold build over warm pinned dependencies**, not a
cold build of Mathlib or the complete repository. A direct-compiler warm rebuild
is measured separately; it is not a Lake no-op/cache-hit benchmark.

Verification completed locally on these exact uncommitted proof sources:

- Independently spelling the full closed quantified leaf and using `t13` as its
  proof elaborated successfully. Additionally, a separate reference module
  importing only Mathlib defined `expectedT13` with a body byte-equal to the
  `SkolemNoether` definition extracted from revision `533aa66`. A separate Lean
  process checked `Kernel.isDefEq` between the full elaborated type of `t13`
  and that independent definition's body, and explicitly checked that `t13`
  has no universe parameters. It passed. The printed theorem has exactly the
  requested quantifiers and hypotheses, with no extra section parameters.
- `#print axioms` for `t13`, `skolemNoether`, the automorphism corollary, both
  tensor-simplicity orientations, and the module classification returned only
  `propext`, `Classical.choice`, `Quot.sound`.
- Unchanged `scripts/audit_kernel.lean` passed on **all five modules / 61 actual
  declarations**. It replayed their serialized declaration bodies against the
  external Mathlib base and traversed the actual dependency bodies. Report:
  `status: passed`, `runtime_declarations_not_replayed: []`,
  `allowed_axioms_used: [Quot.sound, Classical.choice, propext]`,
  `protocol_acceptance: false`. Replay took 16.54 s, maximum RSS 6,767,412 KiB.
- `python3 -B scripts/check_target.py` passed: the original frozen target still
  matches `lean/Frozen/BoundedIntegerPolynomial.lean`. An earlier invocation
  using `python` failed because this node exposes `python3`; the corrected
  standalone invocation above was run and passed.
- Scoped direct-compiler warm rebuild: TensorCoordinates 2.82 s; TensorSimple
  3.27 s; ModuleClassification 2.79 s; Bimodule 3.18 s; Basic 3.04 s;
  wall time 15.13 s, maximum RSS 2,451,744 KiB. Each compiler invocation really
  recompiles that contribution; this is not a cached Lake no-op.
- The embedded license appendix was byte-compared against the fetched source
  license and matches exactly, including the SHA-256 recorded above.
- `git diff --exit-code HEAD` passed: no existing tracked file changed. Only
  the five new proof files and this new note are proposed. No full-root build,
  registry-provider audit or protected protocol acceptance is claimed.

Proof-source SHA-256 (UTF-8, LF):

- `ZInQKernel/Contrib/SkolemNoether/TensorCoordinates.lean`:
  `b18251908dee3fb05281f7651d08b22acdd258bc29554130d76fa8b6d96e3421`.
- `ZInQKernel/Contrib/SkolemNoether/TensorSimple.lean`:
  `770e61e4acc2df019981d83ee7652615ad3051c73e225d3631ed0d4c818ac0ed`.
- `ZInQKernel/Contrib/SkolemNoether/ModuleClassification.lean`:
  `b8e9a8e14114974a03b960d08a29e2afdd8ba7a0ff293d422a9220217884d136`.
- `ZInQKernel/Contrib/SkolemNoether/Bimodule.lean`:
  `50f16a758b6ded51cfa566f97e76a09091a7e36519ebd5263e00fd46ce1bc0cd`.
- `ZInQKernel/Contrib/SkolemNoether/Basic.lean`:
  `31dc3dee86a65080867a2c1b3c70f899e5e1438868af091c0330276f84bd8cbb`.

### Reproduction, without shared-cache writes

From the root of a worktree with the committed pinned Mathlib cache already present:

```sh
mkdir -p .lake/build/lib/lean/ZInQKernel/Contrib/SkolemNoether
for m in TensorCoordinates TensorSimple ModuleClassification Bimodule Basic; do
  lake env lean \
    -o .lake/build/lib/lean/ZInQKernel/Contrib/SkolemNoether/$m.olean \
    ZInQKernel/Contrib/SkolemNoether/$m.lean || exit 1
done
python3 -B scripts/check_target.py
```

The standalone replay uses the unchanged `scripts/audit_kernel.lean`, with
`modules` listing exactly those five modules, `exports` listing the three main
new theorem names, `targets: []`, and `headline.declaration` and
`headline.type_declaration` both naming `ZInQ.Contrib.SkolemNoether.t13`.
Run `lake env lean --run scripts/audit_kernel.lean SPEC.json REPORT.json`.
This replay checks every actual contribution declaration and body plus its axiom
closure; its headline self-comparison is **not** an independent statement lock.
Statement fidelity is checked separately by elaborating the independently spelled
closed leaf proposition with `ZInQ.Contrib.SkolemNoether.t13` as its proof, and by
printing its full type and axioms. The standalone replay is not the entire root
`check_kernel.py`/CI run and does not assert registry recognition or headline discharge.

## Review status

This is an author proof packet. Compilation, axiom checking and kernel replay do
not constitute protected Astra protocol acceptance. No protected check, forged
reviewer receipt, human assignment, commit, push, or PR is produced here. The parent
handles final source-first coverage reconciliation, designated-review gate and
integration.

### Preliminary non-author source-first review

Reviewer: a separate preliminary non-author Metamate agent; serving-model identity
unavailable. The exact private run identity is retained in the non-public verification
record and is not an assertion of designated Astra eligibility.
The reviewer read governance and reconstructed the proof sources before opening
the author's note; no favorable earlier verdict supplied the initial checklist.
The brief and source headers disclosed the upstream identity and orientation issue,
so this was source-first but **not wholly blind**.

The frozen initial reconstruction had canonical-JSON SHA-256
`85a8bb45cea64d5f3689c03164516e39649fd08e2025dce981933d11f9f6778a`.
It named C1/C2 (coordinates/centralizer), S1–S4 (coordinate normalization,
minimal-support commutators, central-left simplicity, central-right transport),
M1/M2 (common simple type/dimension classification), B1–B4 (carrier and action,
right multiplication, intertwining, right inverse), and T1–T3 (acting ring and
classification, unit/conjugacy, closed theorem/corollary). All mathematical
passages in the five source files, including private/generated auxiliaries and
instances, were reviewed. All six borrowed primary files and pivotal pinned
Mathlib implementations were read.

The reviewer independently checked the complete elaborated type, universe
closure, arbitrary noncentral-source instances, and allowed axioms for all
**61** contribution declarations. Both a fresh combined-source elaboration
without contribution-olean reliance and separate byte-identical source-module
checks passed. The reviewer found **no blocking mathematical defect** in the
full embedding proof. This is a preliminary finding, not designated acceptance.
The author’s serialized-declaration replay, full-root CI, cold-dependency builds,
release checks, and future H/glue consumers were **not independently reproduced
or reviewed** by this reviewer.

Reconciliation preserves the initial reconstruction and its one refinement:
C2 directly consumes C1's `tmul_one_mul_eq_smul` through simplification. That
supplier was already reviewed, so this is a valid dependency-inventory refinement,
not a failed proof inference. The author's inventory above now explicitly records
it. Other substantive internal edges agreed, including S4 → S3, M2 → M1,
B3/B4 → B2, and T13/corollary → `skolemNoether`.

The reviewer bound exactly the five proof hashes in the verification section;
they remain unchanged. The note reviewed at the comparison stage had SHA-256
`243142b50fc732d09b0605fa2e352051a2e8204a8f6334593889ba16aaf517db`.
The subsequent documentation additions record this preliminary result and its
refinement; they are not represented as a new independent acceptance of the
updated note. The parent must freeze and review the final packet separately.

## Apache-2.0 license from the source revision

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
