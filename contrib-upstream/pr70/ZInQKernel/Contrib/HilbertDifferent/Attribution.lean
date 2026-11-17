/-!
# Source and license custody for the Hilbert and Serre contribution

This file preserves the already qualified license/provenance records from
trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb. It supplies attribution, not mathematical or protocol acceptance.
T20 admission and T21 independent acceptance in trureturing are not assumed here.
The mathematical attribution is classical Hilbert/Serre ramification theory; the
Lean port derives from the fixed Tau Ceti and other sources identified below.

The following are inherited source records, including their original project-local
references and scope qualifications. Their historical governance statements apply
to their original projects; no such approval is claimed for this contribution.
-/

/-
Original record: Library/ArithUnits/tauceti2026hilbertdifferent.md
Original SHA-256: e23cb6b2a1c726b95f195c2bedb2f7f63e72471db3218bbc800b24136aabb30a

---
bibkey: tauceti2026hilbertdifferent
authors: The Tau Ceti contributors; Michael Stoll; Kevin Buzzard; Andrew Yang; Matthew Jasper; Chris Birkbeck
year: 2026
title: Hilbert different formula and its number-field completion comparison
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/33c2099c678ea391f7ea3e0ddaf945a76a625e5d
claim: The multiplicity of the different at a nonzero prime in a Galois number-field extension equals the finite sum of lower ramification group orders minus one.
strata_touched:
  - D5/S3/Factorization/Dedekind/HilbertDifferent
license: Apache-2.0
triage: anchor
---

# Hilbert different formula

## Local different estimates

The finite-extension structures, additive valuation scaling, ramification-index tower and local Henselian adapter use the same immutable Tau Ceti revision. The p-adic normalization uses `TauCeti/NumberTheory/LocalField/Padic.lean` and `TauCeti/NumberTheory/LocalField/NatCastValuation.lean`. The derivative argument adapts the distinct valuation-class calculation from `TauCeti/NumberTheory/LocalField/Eisenstein/PowerBasis.lean` and invokes Mathlib's finite-sum valuation theorem directly. These are classical local-field results used without a Galois restriction.

## Verified locator

https://github.com/TauCetiProject/TauCeti/tree/33c2099c678ea391f7ea3e0ddaf945a76a625e5d

The global supplier is `IsDedekindDomain.HeightOneSpectrum.multiplicity_differentIdeal_eq_finsum_card_ramificationGroup_sub_one` in `TauCeti/NumberTheory/NumberField/LocalGlobal/Different/Exponent.lean`.
The port retains only the selected declaration dependencies and adapts them to Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The donor uses Lean 4.35.0-rc3 and Mathlib `d870b9068518a0870842d15a0cd42637ec30b587`; direct dependency is incompatible.

The mathematical argument is existing Hilbert different theory. The rational-base change, support truncation, terminating index and exact divisibility pair connect it to the T20 contract. The T21 supplier transports the general local different estimate to every number field through the canonical completions. It identifies the ramification index and different multiplicity and evaluates the rational-place valuation of the ramification index, with no Galois, tame, monogenicity or bounded-degree premise. Together T20 and T21 supply the two arithmetic inputs to the genuine D1 conductor bound and its local-degree and Krasner forms. This is classical support reuse and adaptation; no full Z/Q theorem or new external open problem is claimed.

Retirement: when this project's pinned Mathlib supplies an equivalent declaration under the required hypotheses, replace that declaration and its consumers with direct pinned use.

The normalized multiplicative valuation is reused from `LanglandsFirstMainLemma.normalizedMultiplicativeValuation` in the existing `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/LocalField/Valuation.lean` port. The product-trace dependency directly uses `D5.S3.FiniteGroups.CliffordDecomposition.LinearMap.trace_pi_of_apply_eq_dependent`. Their existing source and license custody are retained.

## Copyright and inherited attribution

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Completion extension and completion valuation material credits Michael Stoll's Apache-2.0 EllipticCurves snapshot `66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e` and the FLT completion work of Kevin Buzzard, Andrew Yang and Matthew Jasper.
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper.
The exact historical FLT revision selected by Stoll is unspecified. Immutable origin and reference states are `c7799b5325323b01ee2e037e49f9fa98cd0669b3` and `44df7744a2a65cdc111875dc1b6f0db85477348f`.
Pertinent Birkbeck source attribution in selected donor files is retained with the source.
The selected TauCeti, Stoll and inspected FLT trees have no NOTICE file. The historical GPL-2.0 Heights snapshot is provenance only and is not a copy source.
The selected TauCeti text and the inherited Stoll/FLT Apache text are both reproduced below.

## License

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

## Inherited Stoll and FLT Apache license

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
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

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

-/

/-
Original record: Library/ArithUnits/tauceti2026tamedifferent.md
Original SHA-256: 84fbd83cac1877c34b598910642dcaff04bb3b17c097a6542f0472cea129686b

---
bibkey: tauceti2026tamedifferent
authors: The Tau Ceti contributors
year: 2026
title: Prime-power quotient traces and Dedekind's different theorem
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/33c2099c678ea391f7ea3e0ddaf945a76a625e5d
claim: The trace on a prime-power quotient is the prime exponent times the residue trace, and a prime power with a coprime complement divides the different exactly when residue separability or nonvanishing of that exponent fails.
strata_touched:
  - D5/S3/Factorization/Dedekind/TameDifferent
  - D5/S3/Factorization/Galois/GoldenCubicBlockCommonDiscriminants
license: Apache-2.0
triage: anchor
---

# Prime-power traces and the different

## Locator

https://github.com/TauCetiProject/TauCeti/tree/33c2099c678ea391f7ea3e0ddaf945a76a625e5d

The immutable source tree contains the selected prime-power trace, different and adic-completion sources listed below.

The immutable source revision is `33c2099c678ea391f7ea3e0ddaf945a76a625e5d`
of TauCeti. The selected source closure is:

- `TauCeti/LinearAlgebra/Trace/Prod.lean`
- `TauCeti/LinearAlgebra/Trace/Exact.lean`
- `TauCeti/RingTheory/DedekindDomain/Ideal/QuotientPow.lean`
- `TauCeti/RingTheory/Trace/QuotientPow.lean`
- `TauCeti/RingTheory/DedekindDomain/Different/Basic.lean`
- `TauCeti/RingTheory/DedekindDomain/Different.lean`
- `TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean`

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
The donor distribution has no `NOTICE` file.

The adapted TameDifferent source has two authored theorem declarations. The first constructs the prime-power
quotient filtration, proves exactness and computes its trace by a split block
presentation. The second constructs the trace-dual criterion and a Chinese
remainder lift with nonzero residue trace. Intermediate helpers are local proof
terms. The source uses pinned Mathlib directly; it imports no TauCeti modules.
This is an adapted source distribution of upstream mathematical proofs.

The common golden cubic discriminant proof adapts the completion-map
construction from `AdicCompletionExtension.lean`. It uses the dense
fraction-field image and continuity to transport the valuation relation
to completions. The actual radicands, ramification indices, prime orbits,
relative different norm and global discriminants are proved separately
for the golden cubic fields.

The donor Lean toolchain is `leanprover/lean4:v4.35.0-rc3`, and the repository
Lean toolchain is `leanprover/lean4:v4.33.0`. Direct package dependency is
incompatible with these toolchain pins. Both transplanted declarations compile
with only `propext`, `Classical.choice` and `Quot.sound` in their axiom closures.

Retirement condition: when the repository's own pinned Mathlib contains
equivalent prime-power quotient trace and different-divisibility declarations,
replace this transplant by direct applications of those pinned declarations.

The quotient trace formula needs a module-finite algebra and a Dedekind target
with a nonzero maximal ideal. The different criterion additionally needs
Dedekind source, torsion freedom, separable fraction-field extension and the
specified coprime prime-power factorization. No actual golden-block ramification
indices or number-field discriminant formulas are consequences without their
separate arithmetic hypotheses.

# License

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

-/

/-
Original record: Library/Fourier/epsilonfml2026hassedavenport.md
Original SHA-256: 95101dd6d51e31ae2072ed4d5f6de935e4aed9df7b935ddbe6355e64f09c0e20

---
bibkey: epsilonfml2026hassedavenport
authors: fukubillueda-web contributors
year: 2026
title: epsilon_FML finite-field Hasse–Davenport supplier
doi: null
url: https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed
claim: The pinned epsilon_FML source supplies the exact Langlands-normalized Hasse–Davenport lift for arbitrary finite extensions and nontrivial additive characters.
strata_touched:
  - D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/Fourier/epsilonfml2026hassedavenport -->
# Exact Hasse–Davenport supplier from epsilon_FML

This source card records the attributed upstream supplier used by the finite-field character-sums port.

## Verified locator

https://github.com/fukubillueda-web/epsilon_FML/tree/b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed

The pinned source locator is `LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.lean`, declaration `LanglandsFirstMainLemma.hasseDavenportLift` (source line 461). The retained source bytes have SHA-256 `2f205c2d7c9720f870934bd332215032d23ab044e36db0baac999a655b4a65fd`. The source manifest and retained proof closure below bind the imported prerequisites. This locator attributes the exact code supplier; no manuscript theorem number or original mathematical priority is claimed.

## Provenance

- Repository: <https://github.com/fukubillueda-web/epsilon_FML>
- Immutable source commit: `b91ad93900a5e6d9207a4e6166ac94bb3bbcf3ed`
- Upstream toolchain: `leanprover/lean4:v4.32.2` with Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`.
- Target toolchain: repository Lean 4.33.0 with Mathlib revision `db584cd6d46c92f209a44c0f1c829460d327499d`.
- Port location: `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma`.
- Namespace preserved: `LanglandsFirstMainLemma`.
- No NOTICE file occurs in the pinned source tree.

## Exact source manifest

The original source manifest has 14 files and 225458 total bytes. The retained proof closure has nine non-target Lean modules plus the target. The original downloaded bytes, including the omitted metadata-only Prelude, remain identified by the hashes below.

| Path | Bytes | SHA-256 |
| --- | ---: | --- |
| `LICENSE` | 11357 | `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4` |
| `lean-toolchain` | 25 | `2bdc48adfa58d0017e538a0ad117c5d73d35deec879978f909406a80c8037273` |
| `lake-manifest.json` | 3904 | `8c68da26c0f6d7994949aa9ff57ddb59f5b4d6ddc74f66224f1d884c7381dcc2` |
| `LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.lean` | 18646 | `2f205c2d7c9720f870934bd332215032d23ab044e36db0baac999a655b4a65fd` |
| `LanglandsFirstMainLemma/FiniteField/CharacterAPI.lean` | 8181 | `2d85103e46bc5ed75c9d2593e62f5dffb67f3b43ef45139c3f13923734b0b555` |
| `LanglandsFirstMainLemma/FiniteField/EulerProduct.lean` | 33840 | `5410cca856f03d5184bb781272813d2b8cf26e7f8072c36bb56a792d6345c517` |
| `LanglandsFirstMainLemma/LocalField/Extension.lean` | 45231 | `dcd038574652cc2b33b7ccb53f54232e012989e328bb039820b4662dca2216a9` |
| `LanglandsFirstMainLemma/Basic/FiniteProducts.lean` | 15465 | `2be274197ca116a61945e92a3b6aa6e505e1e05b40c0f5e33da5d769dc2bedec` |
| `LanglandsFirstMainLemma/LocalField/ResidueField.lean` | 10881 | `4ecc7e8f9e52ea3c30e6eea722487edbe174075d80251f92ad4bc1ebcdd5eab7` |
| `LanglandsFirstMainLemma/FiniteField/PolynomialWeights.lean` | 7463 | `ac18dcb74071925205d5c5e17edef72721bce96c8192327f815f565d5186dc87` |
| `LanglandsFirstMainLemma/Prelude.lean` | 1222 | `de829026dfc3ad0b35b9325f423da4a1465bc8d46c84086520a2fe07eda20907` |
| `LanglandsFirstMainLemma/LocalField/UnitFiltration.lean` | 27606 | `9421870db84fc04026fa9e90fbdb4c3c94385c14f78c25b9e655ed2ebc79f019` |
| `LanglandsFirstMainLemma/LocalField/Lattices.lean` | 22972 | `ff37ebdfbdf904bbcf7d1b0fc0156abe7ca53bc14a63234f23052baf4e063e70` |
| `LanglandsFirstMainLemma/LocalField/Valuation.lean` | 18665 | `d1d40703fde462c5e1023e8aff759ab1956b8111ce1272e8f5c994511a857522` |

## Retained proof closure

The ten retained modules, in import-compatible order, are:

1. `Basic/FiniteProducts.lean`
2. `LocalField/Valuation.lean`
3. `LocalField/Lattices.lean`
4. `LocalField/UnitFiltration.lean`
5. `LocalField/ResidueField.lean`
6. `FiniteField/CharacterAPI.lean`
7. `FiniteField/PolynomialWeights.lean`
8. `FiniteField/EulerProduct.lean`
9. `LocalField/Extension.lean`
10. `FiniteField/HasseDavenportLift.lean`

Paths are relative to the preserved `LanglandsFirstMainLemma` namespace and port location. FiniteProducts and Valuation import Mathlib directly. The upstream `Prelude.lean` contains only `blueprintScaffoldVersion`, `plannedModuleCount`, `authoritativeManuscript`, and `PendingTask := True`; none has a proof consumer in these ten modules. These four metadata definitions and their Blueprint descriptor are omitted from the live port. The Prelude row in the original source manifest records attribution, not a retained mathematical module.

Every mathematical definition, theorem statement, proof body and namespace in the ten modules is retained, including the degree-zero quotient compatibility proofs and explicit normal-subgroup instances required by the target Mathlib revision. Import and attribution normalization introduces no replacement declaration.

## Ported theorem

The public target is the exact upstream declaration `LanglandsFirstMainLemma.hasseDavenportLift` in `D5/S3/Arith/CharacterSums/LanglandsFirstMainLemma/FiniteField/HasseDavenportLift.lean`.

For fields `k` and `K` with finite underlying types and an algebra structure, a finite multiplicative character `χ`, a finite additive character `ψ`, and `ψ ≠ 1`, the theorem states

```text
langlandsGaussSum (normMulChar k K χ) (traceAddChar k K ψ) =
  langlandsGaussSum χ ψ ^ Module.finrank k K
```

The normalization is `langlandsGaussSum(χ, ψ) = -gaussSum(χ⁻¹, ψ)`. The proof uses the actual norm and trace pullbacks, the closed-point power identity, and the Euler-product identity. The multiplicative character is unrestricted, so the trivial character is included; only the additive character is required to be nontrivial. This is upstream reuse, not a new mathematical-priority claim or an open-problem resolution.

The Lean 4.33 port keeps the original proof architecture. It supplies explicit normal-subgroup instances at the degree-zero unit quotient because the target Mathlib revision does not infer those commutative-group instances automatically, and names the quotient parameters explicitly. These edits do not alter the theorem statement or normalization.

## License

The following is the exact `LICENSE` file from the pinned source tree.

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
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

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

-/

/-
Original record: Library/FiniteGroups/tauceti2026finitecharacters.md
Original SHA-256: df85987b6b870684ff6ceb96642926ba0a23fe8b590eafaf7f670074e467032d

---
bibkey: tauceti2026finitecharacters
authors: The Tau Ceti contributors; Claude
year: 2026
title: TauCeti finite representation and character theory
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5
claim: Finite representation theory supplies Schur scalarity, character-degree divisibility, Clifford decomposition, and the Mackey criterion for induced irreducibility.
strata_touched:
  - D5/S3/FiniteGroups/FiniteCharacterAlgebra
  - D5/S3/FiniteGroups/CharacterDegreeDivisibility
  - D5/S3/FiniteGroups/CliffordConstituents
  - D5/S3/FiniteGroups/CliffordDecomposition
  - D5/S3/FiniteGroups/InducedCharacterFormula
  - D5/S3/FiniteGroups/MackeyCharacterFormula
  - D5/S3/FiniteGroups/ComplexCharacterAbelianProducts
  - D5/S3/FiniteGroups/RegularRepresentation/RegularTrace
license: Apache-2.0
triage: anchor
---

# Finite representations and characters

## Verified locator

Source: https://github.com/TauCetiProject/TauCeti/tree/a780c7ad6beb23f60a17351a492d177878020ad5

## Schur scalarity

The source packages the endomorphism algebra of a finite-dimensional simple module over an algebraically closed field as that field itself. This is the Schur input used when a central group element is made into an intertwining endomorphism. See [the source statement](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Semisimple/Schur.lean#L21-L27).

## Immutable sources

Repository: https://github.com/TauCetiProject/TauCeti

Pinned commit: `a780c7ad6beb23f60a17351a492d177878020ad5`.

The port retains the declarations used by the peak-group refutation from these files:

- [TauCeti/Algebra/Group/Subgroup/Pointwise.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Algebra/Group/Subgroup/Pointwise.lean)
- [TauCeti/Algebra/MonoidAlgebra/Conjugation.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Algebra/MonoidAlgebra/Conjugation.lean)
- [TauCeti/Algebra/MonoidAlgebra/Trace.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Algebra/MonoidAlgebra/Trace.lean)
- [TauCeti/GroupTheory/Coset/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/GroupTheory/Coset/Basic.lean)
- [TauCeti/GroupTheory/DoubleCoset/Finite.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/GroupTheory/DoubleCoset/Finite.lean)
- [TauCeti/GroupTheory/DoubleCoset/Identity.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/GroupTheory/DoubleCoset/Identity.lean)
- [TauCeti/GroupTheory/Index/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/GroupTheory/Index/Basic.lean)
- [TauCeti/GroupTheory/QuotientGroup/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/GroupTheory/QuotientGroup/Basic.lean)
- [TauCeti/LinearAlgebra/End/FiniteOrder.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/LinearAlgebra/End/FiniteOrder.lean)
- [TauCeti/LinearAlgebra/Trace/Pi.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/LinearAlgebra/Trace/Pi.lean)
- [TauCeti/RepresentationTheory/AsModule.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/AsModule.lean)
- [TauCeti/RepresentationTheory/CharacterTable/CentralCharacter.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/CentralCharacter.lean)
- [TauCeti/RepresentationTheory/CharacterTable/ClassFunction.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/ClassFunction.lean)
- [TauCeti/RepresentationTheory/CharacterTable/ClassSum/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/ClassSum/Basic.lean)
- [TauCeti/RepresentationTheory/CharacterTable/ClassSum/Basis.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/ClassSum/Basis.lean)
- [TauCeti/RepresentationTheory/CharacterTable/ClassSum/Integral.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/ClassSum/Integral.lean)
- [TauCeti/RepresentationTheory/CharacterTable/ClassSum/Representation.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/ClassSum/Representation.lean)
- [TauCeti/RepresentationTheory/CharacterTable/Degree.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/Degree.lean)
- [TauCeti/RepresentationTheory/CharacterTable/Kernel.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/Kernel.lean)
- [TauCeti/RepresentationTheory/CharacterTable/Pairing.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/Pairing.lean)
- [TauCeti/RepresentationTheory/CharacterTable/Values.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/CharacterTable/Values.lean)
- [TauCeti/RepresentationTheory/FDRep.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/FDRep.lean)
- [TauCeti/RepresentationTheory/Induction/Character.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Character.lean)
- [TauCeti/RepresentationTheory/Induction/ClassFunction.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/ClassFunction.lean)
- [TauCeti/RepresentationTheory/Induction/Clifford/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Clifford/Basic.lean)
- [TauCeti/RepresentationTheory/Induction/Clifford/Dimension.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Clifford/Dimension.lean)
- [TauCeti/RepresentationTheory/Induction/Clifford/Equivalence.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Clifford/Equivalence.lean)
- [TauCeti/RepresentationTheory/Induction/Clifford/Multiplicity.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Clifford/Multiplicity.lean)
- [TauCeti/RepresentationTheory/Induction/Clifford/Orbit/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Clifford/Orbit/Basic.lean)
- [TauCeti/RepresentationTheory/Induction/Clifford/Orbit/Index.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Clifford/Orbit/Index.lean)
- [TauCeti/RepresentationTheory/Induction/Conjugate.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Conjugate.lean)
- [TauCeti/RepresentationTheory/Induction/FiniteDimensional/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/FiniteDimensional/Basic.lean)
- [TauCeti/RepresentationTheory/Induction/FrobeniusReciprocity.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/FrobeniusReciprocity.lean)
- [TauCeti/RepresentationTheory/Induction/Inertia.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Inertia.lean)
- [TauCeti/RepresentationTheory/Induction/Mackey/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Mackey/Basic.lean)
- [TauCeti/RepresentationTheory/Induction/Mackey/Intertwining.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Mackey/Intertwining.lean)
- [TauCeti/RepresentationTheory/Induction/Mackey/Irreducible.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Mackey/Irreducible.lean)
- [TauCeti/RepresentationTheory/Induction/Mackey/LinearCharacter.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Mackey/LinearCharacter.lean)
- [TauCeti/RepresentationTheory/Induction/Mackey/Subgroup.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Mackey/Subgroup.lean)
- [TauCeti/RepresentationTheory/Induction/Restriction.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Induction/Restriction.lean)
- [TauCeti/RepresentationTheory/Irreducible.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Irreducible.lean)
- [TauCeti/RepresentationTheory/LinearCharacter.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/LinearCharacter.lean)
- [TauCeti/RepresentationTheory/OfModule.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/OfModule.lean)
- [TauCeti/RepresentationTheory/Simple/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Simple/Basic.lean)
- [TauCeti/RepresentationTheory/Subrepresentation.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RepresentationTheory/Subrepresentation.lean)
- [TauCeti/RingTheory/IntegralClosure/Rat.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/IntegralClosure/Rat.lean)
- [TauCeti/RingTheory/Semisimple/CentralCharacter.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Semisimple/CentralCharacter.lean)
- [TauCeti/RingTheory/Semisimple/DoubleCentralizer.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Semisimple/DoubleCentralizer.lean)
- [TauCeti/RingTheory/Semisimple/Multiplicity.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Semisimple/Multiplicity.lean)
- [TauCeti/RingTheory/Semisimple/RegularIsotypicComponent.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Semisimple/RegularIsotypicComponent.lean)
- [TauCeti/RingTheory/Semisimple/Schur.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Semisimple/Schur.lean)
- [TauCeti/RingTheory/SimpleModule/Isotypic.lean](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/SimpleModule/Isotypic.lean)

The category End/Aut homomorphism coercions and subgroup-membership proof coercions use the repository’s pinned Mathlib API. The mathematical hypotheses and conclusions are unchanged.

## Regular traces

The trace source proves `TauCeti.trace_leftMulMatrix_monoidAlgebra` and
`TauCeti.MonoidAlgebra.trace_mulLeft`: left multiplication by an arbitrary
weighted element of a finite cancellative monoid algebra has trace equal to
the monoid cardinality times its identity coefficient. For a finite group,
the diagonal proof is ported in `RegularRepresentation/RegularTrace` and
combined with `map_list_prod` to give the ordered-product identity, including
the empty list. Its coefficient ring is an arbitrary commutative ring.

The immutable source uses `leanprover/lean4:v4.35.0-rc3` and Mathlib revision
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`; these differ from the repository's
pinned toolchain and Mathlib revision, so a direct Lake dependency is incompatible.
The port uses the pinned `MonoidAlgebra.basis` coefficient equivalence in place
of the source's additional basis lemmas. The source archive has no root `NOTICE`
file; its copyright and complete Apache 2.0 license are retained below.

## Replacement condition

When the repository’s pinned Mathlib contains an equivalent declaration with the same
hypotheses and conclusion, use that declaration directly and remove the corresponding port.

## Source notices

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.

Copyright (c) 2026 Tau Ceti. All rights reserved.

Copyright (c) 2026 Tau Ceti contributors. All rights reserved.

Authors: The Tau Ceti contributors. The coset source also credits Claude.

## Classical background for the modular additions

The modular additions use the same Schur, density and Clifford infrastructure
as the pinned port. For a directly inspected classical exposition of simultaneous
density and simple-character separation, see Pavel Etingof, Oleg Golberg,
Sebastian Hensel, Tiankai Liu, Alex Schwendner, Dmitry Vaintrob and Elena Yudovina,
Introduction to Representation Theory, https://math.mit.edu/~etingof/replect.pdf,
Theorem 2.5(ii) (simultaneous surjectivity to endomorphism algebras), and
Theorem 2.17(i) (linear independence of characters of pairwise nonisomorphic
finite-dimensional irreducible algebra representations). The two-module
trace-one/trace-zero witness is obtained by choosing a rank-one trace-one block
and a zero block in Theorem 2.5(ii). Equality of simple monoid characters extends
linearly to the monoid algebra, where that separation applies. These are
classical consequences, not mathematical novelty claims. The source's
algebraically closed base-field hypothesis remains in force.

The repository's fixed-point-free twist-rigidity argument and its structural
Frobenius alternative combine these classical inputs with the existing
fixed-point-free commutator and generic Clifford APIs. Their descriptions are
repo-derived, not quotations of a verified external theorem with the complete
same telescope. The integer divisibility comes from natural-number dimensions
in Clifford decomposition. Field-valued traces in characteristic p retain only
the image of those dimensions in the field; the complex integer degree dichotomy
is not asserted in arbitrary characteristic. No external excerpt is reproduced.

## Arbitrary-field descent

The arbitrary-field structural alternative in `FrobeniusCharacterDegrees` is a
repo-derived synthesis of the algebraically closed alternative and scalar
extension; it is not attributed to the pinned port as an exact theorem. Set
A = k[K], B = E[K] for an algebraic closure E of k. Although E tensor_k W need
not be semisimple over B, its restriction to A is semisimple and W-isotypic:
the A-linear maps w ↦ c tensor w have simple or zero images and their images
generate all pure tensors. B-submodules inherit this A-support by inclusion.
For a B-quotient, A-semisimplicity descends along the quotient map, and lifting
each simple A-submodule shows that its isomorphism type is W. Consequently
every B-subquotient retains the original A-support.

A nonzero B-simple factor Q therefore contains an A-linear copy of W. If N
acted trivially on Q, this injection would force trivial N-action on W. When
W has nontrivial N-action, every supported simple factor does too; the
algebraically closed alternative makes N.index divide each factor's
E-dimension. Finite-length induction and dimension additivity give the same
divisibility for E tensor_k W, whose E-dimension equals the k-dimension of W
by base change. Neither B-semisimplicity nor inertia equal to N over the
original nonsplitting field is asserted. No characteristic, perfectness,
separability or coprimality assumption is added, and no literature novelty is
claimed.

The inner-action obstruction in `FrobeniusInnerActionObstruction` uses this
original-module support on a nonzero simple E[N]-submodule. An implementer
and its inverse in the representation image preserve that same submodule;
fixed-point-free rigidity there and an injective support map force the
original action to be trivial. For a finite-dimensional simple quotient of
k[N], a faithful simple module detects that the quotient factors through
the existing standard augmentation and is k-algebra isomorphic to k. This
is a repository derivation, not an exact theorem attributed to TauCeti or
a literature novelty claim. It supplies an ingredient of the arithmetic
Frobenius direction; the stronger normalized-degree statement remains open.

## Complete license

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

-/

/-
Original record: Library/ArithUnits/yamaguchi2026residuelifting.md
Original SHA-256: 981030ed7ce736ea700f75b76b409424be77c790ac7b86d165063e5069664412

---
bibkey: yamaguchi2026residuelifting
authors: Naganori Yamaguchi
year: 2026
title: Separable residue lifting to finite unramified subextensions
doi: null
url: https://github.com/n-yamaguchi-0729/NYLL/tree/fe40c03df1b2b195053fdd63305571d97c73ce48
claim: Hensel lifting of a separable residue element generates a finite unramified subextension with that element in its residue image.
strata_touched:
  - D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField
license: Apache-2.0
triage: anchor
---

# Separable residue lifting

The selected source is `Nyll/ValuedFieldTheory/LocalField/Unramified/ResidueLifting.lean` at the immutable revision above. The native adaptation uses Mathlib's simple-root Henselian interface and the existing ValuativeRel local-field structures. The primitive residue generator and the full residue image require explicit native proofs beyond the source's single-element conclusion.

Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex).

The adapted files are prominently marked modified. Replace each adapted declaration by direct use when this project's pinned Mathlib supplies an equivalent declaration.

The complete upstream license, root NOTICE and applicable entire subtree attribution chain follow. The notices retain their upstream scope and do not assert that every work named in the root NOTICE is used by this adaptation.

## Entire root NOTICE

- [Root NOTICE part 1](yamaguchi2026residueliftingnoticeone.md).
- [Root NOTICE part 2](yamaguchi2026residueliftingnoticetwo.md).

The text blocks in numerical order preserve the complete upstream NOTICE verbatim.

## LICENSE

Source: `LICENSE`. SHA-256: `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.

~~~~~~~~text
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
~~~~~~~~

## ANTHROPIC_FLT_SOURCE.md

Source: `Nyll/ValuedFieldTheory/ANTHROPIC_FLT_SOURCE.md`. SHA-256: `f06f8b0a6977ec45bcdfcc65ad23fb87b953199a3640e641dfee3ea676bb940d`.

~~~~~~~~text
# Anthropic FLT sources included in this extract

[ANTHROPIC_FLT_NOTICE](ANTHROPIC_FLT_NOTICE) and
[ANTHROPIC_FLT_ATTRIBUTION.md](ANTHROPIC_FLT_ATTRIBUTION.md) preserve
the upstream documents byte-for-byte, including earlier FLT and Mathlib
credits. References to “this repository” in those copies mean the upstream
repository, not this extract. The included local source files are listed below.

| Included source | Upstream attribution |
| --- | --- |
| [Nyll/ValuedFieldTheory/Valuation/Completion/AdicCompletion.lean](Valuation/Completion/AdicCompletion.lean) | Source identified by code comparison; exact upstream file unresolved. |
| [Nyll/ValuedFieldTheory/Valuation/Completion/DVRAdicCompletionIsDomainDVRIsAdicComplete.lean](Valuation/Completion/DVRAdicCompletionIsDomainDVRIsAdicComplete.lean) | [S_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsDiscreteValuationRing_adicCompletion_isDomain_isDiscreteValuationRing_isAdicComplete.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Completion/LaurentBaseChange.lean](Valuation/Completion/LaurentBaseChange.lean) | Source identified by code comparison; exact upstream file unresolved. |
| [Nyll/ValuedFieldTheory/Valuation/Completion/ValuationCompletionAlgebra.lean](Valuation/Completion/ValuationCompletionAlgebra.lean) | Source identified by code comparison; exact upstream file unresolved. |
| [Nyll/ValuedFieldTheory/Valuation/Completion/ValuationSubringAlgClosedCompletion.lean](Valuation/Completion/ValuationSubringAlgClosedCompletion.lean) | [S_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_isAlgClosed_completion_of_mulArchimedean_valueGroup.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/AlgebraStandardSmoothDVRLocalizationAtPrime.lean](Valuation/DiscreteValuationField/AlgebraStandardSmoothDVRLocalizationAtPrime.lean) | [S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/DVRFiniteLocallyPrincipalOverring.lean](Valuation/DiscreteValuationField/DVRFiniteLocallyPrincipalOverring.lean) | [S_IsDiscreteValuationRing_exists_finite_locallyPrincipalOverring.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsDiscreteValuationRing_exists_finite_locallyPrincipalOverring.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/DVRPrimesOverIntegralClosureEqRange.lean](Valuation/DiscreteValuationField/DVRPrimesOverIntegralClosureEqRange.lean) | [S_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsDiscreteValuationRing_primesOver_integralClosure_eq_range_of_finrank_le_sum_inertiaDeg.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/DVRValuationSubringEqSubMemNonunits.lean](Valuation/DiscreteValuationField/DVRValuationSubringEqSubMemNonunits.lean) | [S_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsDiscreteValuationRing_forall_valuationSubring_eq_and_forall_exists_sub_mem_nonunits_of_primesOver_integralClosure_eq_singleton.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/IdealHeightEqOneDVRLocalizationAtPrime.lean](Valuation/DiscreteValuationField/IdealHeightEqOneDVRLocalizationAtPrime.lean) | Source identified by code comparison; exact upstream file unresolved. |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/IdealSpanAlgebraNormEq.lean](Valuation/DiscreteValuationField/IdealSpanAlgebraNormEq.lean) | [S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Ideal_span_algebraNorm_eq_of_ker_eq_span_of_isDiscreteValuationRing.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/IntegrallyClosedDVR.lean](Valuation/DiscreteValuationField/IntegrallyClosedDVR.lean) | [S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/IntegrallyClosedDVRLocalization.lean](Valuation/DiscreteValuationField/IntegrallyClosedDVRLocalization.lean) | [S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/IntegrallyClosedValuationSubringMemIffNonunitsIff.lean](Valuation/DiscreteValuationField/IntegrallyClosedValuationSubringMemIffNonunitsIff.lean) | [S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_exists_valuationSubring_mem_iff_and_nonunits_iff_of_height_eq_one.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/LocalRingOfListPairEqMaximalIdealIsRegular.lean](Valuation/DiscreteValuationField/LocalRingOfListPairEqMaximalIdealIsRegular.lean) | [S_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/LocalRingValuationSubringDVRDominates.lean](Valuation/DiscreteValuationField/LocalRingValuationSubringDVRDominates.lean) | [S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/LocalizationAtPrimeDVR.lean](Valuation/DiscreteValuationField/LocalizationAtPrimeDVR.lean) | [S_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/MvPowerSeriesKrullDimensionFinEq.lean](Valuation/DiscreteValuationField/MvPowerSeriesKrullDimensionFinEq.lean) | [S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/PadicIntNatCardQuotientRangeEqPowValuationDet.lean](Valuation/DiscreteValuationField/PadicIntNatCardQuotientRangeEqPowValuationDet.lean) | [S_PadicInt_natCard_quotient_range_eq_pow_valuation_det.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_PadicInt_natCard_quotient_range_eq_pow_valuation_det.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationLeOneIffEqMkEqPowMul.lean](Valuation/DiscreteValuationField/ValuationLeOneIffEqMkEqPowMul.lean) | [S_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valuation_exists_le_one_iff_exists_eq_mk_of_forall_exists_eq_pow_mul.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationRingHomCardinality.lean](Valuation/DiscreteValuationField/ValuationRingHomCardinality.lean) | [S_IsLocalRing_finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal.lean) |
| [Nyll/ValuedFieldTheory/Valuation/DiscreteValuationField/ValuationRingNeZeroSmulEqZero.lean](Valuation/DiscreteValuationField/ValuationRingNeZeroSmulEqZero.lean) | [S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationRing_exists_ne_zero_forall_smul_eq_zero_of_module_finite.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/EqUnitsMulProdSubAlgebraMap.lean](Valuation/Subring/Arithmetic/EqUnitsMulProdSubAlgebraMap.lean) | [S_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_eq_units_mul_prod_sub_algebraMap_of_notMem_map_maximalIdeal.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/FinsetMemSpanMulEq.lean](Valuation/Subring/Arithmetic/FinsetMemSpanMulEq.lean) | [S_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_finset_forall_exists_mem_span_mul_eq_of_intermediateField_le.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/LeMemIffApplyMem.lean](Valuation/Subring/Arithmetic/LeMemIffApplyMem.lean) | [S_ValuationSubring_exists_le_forall_mem_iff_apply_mem.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_le_forall_mem_iff_apply_mem.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/MemIffNotDvd.lean](Valuation/Subring/Arithmetic/MemIffNotDvd.lean) | [S_ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_mem_iff_exists_not_dvd_of_prime_of_forall_mem_maximalIdeal_iff_dvd.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/MemMemIff.lean](Valuation/Subring/Arithmetic/MemMemIff.lean) | [S_ValuationSubring_mem_of_forall_mem_iff_of_subset.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_mem_of_forall_mem_iff_of_subset.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/MemSubMemMaximalIdeal.lean](Valuation/Subring/Arithmetic/MemSubMemMaximalIdeal.lean) | [S_ValuationSubring_mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_mem_and_sub_mem_maximalIdeal_of_gaussPresentation_of_coe_eq_of_coeffMap_residue_comp_eq.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/MemSubMemNonunits.lean](Valuation/Subring/Arithmetic/MemSubMemNonunits.lean) | [S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/MulPowInvMem.lean](Valuation/Subring/Arithmetic/MulPowInvMem.lean) | [S_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_mul_pow_inv_mem_of_finiteDimensional_adjoin.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/PowEqUnitMulZpow.lean](Valuation/Subring/Arithmetic/PowEqUnitMulZpow.lean) | [S_ValuationSubring_exists_pow_eq_unit_mul_zpow_of_isAlgebraic_of_isNoetherianRing.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_pow_eq_unit_mul_zpow_of_isAlgebraic_of_isNoetherianRing.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/PowValuationEqValuationAlgebraMap.lean](Valuation/Subring/Arithmetic/PowValuationEqValuationAlgebraMap.lean) | [S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_pow_valuation_eq_valuation_algebraMap_of_isAlgebraic.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/PowValuationEqValuationNatCastZpow.lean](Valuation/Subring/Arithmetic/PowValuationEqValuationNatCastZpow.lean) | [S_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_pow_valuation_eq_valuation_natCast_zpow_of_isAlgebraic.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/SubMemNonunits.lean](Valuation/Subring/Arithmetic/SubMemNonunits.lean) | [S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_sub_mem_nonunits_of_finrank_le_card.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/UnitApplyEqMul.lean](Valuation/Subring/Arithmetic/UnitApplyEqMul.lean) | [S_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_unit_apply_eq_mul_of_mem_iff_apply_mem_of_rankOne.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Arithmetic/ValuationPowEqValuationZpow.lean](Valuation/Subring/Arithmetic/ValuationPowEqValuationZpow.lean) | [S_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_valuation_pow_eq_valuation_zpow_of_isAlgebraic.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Dimension/KrullDimensionEqKrullDimensionResidueValuationSubringAdd.lean](Valuation/Subring/Dimension/KrullDimensionEqKrullDimensionResidueValuationSubringAdd.lean) | [S_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Dimension/KrullDimensionLeKrullDimensionComapAddTrdeg.lean](Valuation/Subring/Dimension/KrullDimensionLeKrullDimensionComapAddTrdeg.lean) | [S_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Dimension/KrullDimensionLeToENatTrdegRatAddOne.lean](Valuation/Subring/Dimension/KrullDimensionLeToENatTrdegRatAddOne.lean) | [S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Dimension/KrullDimensionResidueValuationSubringOfPrimeEqKrullDimIcc.lean](Valuation/Subring/Dimension/KrullDimensionResidueValuationSubringOfPrimeEqKrullDimIcc.lean) | [S_ValuationSubring_ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_ringKrullDim_residueValuationSubring_ofPrime_eq_krullDim_Icc.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Dimension/MulArchimedeanValueGroup.lean](Valuation/Subring/Dimension/MulArchimedeanValueGroup.lean) | [S_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_mulArchimedean_valueGroup_of_isAlgebraic_of_valuation_natCast_lt_one.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Discrete/DVRAlgebraMapMemFinite.lean](Valuation/Subring/Discrete/DVRAlgebraMapMemFinite.lean) | [S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_isDiscreteValuationRing_of_algebraMap_mem_of_finite.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Discrete/DVRAlgebraMapMemSeparable.lean](Valuation/Subring/Discrete/DVRAlgebraMapMemSeparable.lean) | [S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_isDiscreteValuationRing_of_forall_algebraMap_mem_of_isSeparable.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Discrete/EqValuationSubringAtPrime.lean](Valuation/Subring/Discrete/EqValuationSubringAtPrime.lean) | [S_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Discrete/IsPrincipalIdealRing.lean](Valuation/Subring/Discrete/IsPrincipalIdealRing.lean) | [S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Discrete/LayerDVR.lean](Valuation/Subring/Discrete/LayerDVR.lean) | [S_ValuationSubring_exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_layer_isDiscreteValuationRing_of_finite_of_isAlgebraic_of_irreducible.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Discrete/MaximalIdealPowerDivisibility.lean](Valuation/Subring/Discrete/MaximalIdealPowerDivisibility.lean) | [S_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_dvd_pow_of_mem_maximalIdeal.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Discrete/ToSubringEqIntegralClosureFiniteDVR.lean](Valuation/Subring/Discrete/ToSubringEqIntegralClosureFiniteDVR.lean) | [S_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_toSubring_eq_integralClosure_and_finite_and_isDiscreteValuationRing_of_henselian.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Henselian/HenselianLocalRing.lean](Valuation/Subring/Henselian/HenselianLocalRing.lean) | [S_ValuationSubring_henselianLocalRing_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_henselianLocalRing_of_isAlgClosed.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Henselian/IntermediateFieldFiniteDimensionalHenselianLocalRingComap.lean](Valuation/Subring/Henselian/IntermediateFieldFiniteDimensionalHenselianLocalRingComap.lean) | [S_ValuationSubring_exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_intermediateField_finiteDimensional_henselianLocalRing_comap_of_henselianLocalRing.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Henselian/MonicPolynomialRoot.lean](Valuation/Subring/Henselian/MonicPolynomialRoot.lean) | Source identified by code comparison; exact upstream file unresolved. |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/AevalDivEqAevalDivAddAevalInvDiv.lean](Valuation/Subring/Integral/AevalDivEqAevalDivAddAevalInvDiv.lean) | [S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_aeval_inv_div.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/AevalDivEqAevalDivAddInvPowMulAddAevalInv.lean](Valuation/Subring/Integral/AevalDivEqAevalDivAddInvPowMulAddAevalInv.lean) | [S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/AlgebraAdjoinNeZeroMulValuationSubringMem.lean](Valuation/Subring/Integral/AlgebraAdjoinNeZeroMulValuationSubringMem.lean) | [S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/EqAevalDiv.lean](Valuation/Subring/Integral/EqAevalDiv.lean) | [S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/EqAlgebraMap.lean](Valuation/Subring/Integral/EqAlgebraMap.lean) | [S_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_eq_algebraMap_of_forall_valuationSubring_mul_aeval_mem.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/EqMulPowFinrankAdjoinSimpleEq.lean](Valuation/Subring/Integral/EqMulPowFinrankAdjoinSimpleEq.lean) | [S_ValuationSubring_exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_eq_mul_pow_finrank_and_adjoin_simple_eq_of_forall_valuationSubring_eq.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/FaithfullyFlatIsIntegral.lean](Valuation/Subring/Integral/FaithfullyFlatIsIntegral.lean) | [S_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_faithfullyFlat_and_isIntegral_of_henselianLocalRing_comap.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/IntegralCriterion.lean](Valuation/Subring/Integral/IntegralCriterion.lean) | [S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/MemAdjoinSingletonIsIntegralIsUnitNormAevalDerivativeMinpoly.lean](Valuation/Subring/Integral/MemAdjoinSingletonIsIntegralIsUnitNormAevalDerivativeMinpoly.lean) | [S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_isUnit_norm_aeval_derivative_minpoly.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/MemAdjoinSingletonIsIntegralSeparableMinpoly.lean](Valuation/Subring/Integral/MemAdjoinSingletonIsIntegralSeparableMinpoly.lean) | [S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_separable_minpoly.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_mem_adjoin_singleton_of_isIntegral_of_separable_minpoly.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/NatDegreeMapEqCardRoots.lean](Valuation/Subring/Integral/NatDegreeMapEqCardRoots.lean) | [S_ValuationSubring_natDegree_map_eq_card_roots_of_splits.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_natDegree_map_eq_card_roots_of_splits.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Integral/TensorPrimitiveFactor.lean](Valuation/Subring/Integral/TensorPrimitiveFactor.lean) | [S_ValuationSubring_tensorProduct_exists_primitive_factor.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_tensorProduct_exists_primitive_factor.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/PadicIntApplyEqPowApprMul.lean](Valuation/Subring/PadicIntApplyEqPowApprMul.lean) | [S_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_padicInt_forall_apply_eq_pow_appr_mul_of_pow_eq_of_residue_eq.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Ramification/FinitePrimeSpectrum.lean](Valuation/Subring/Ramification/FinitePrimeSpectrum.lean) | [S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_finite_primeSpectrum_of_ringKrullDim_lt_top.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Ramification/FinsumRamificationIdxMulInertiaDegEqFinrank.lean](Valuation/Subring/Ramification/FinsumRamificationIdxMulInertiaDegEqFinrank.lean) | [S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_finsum_ramificationIdx_mul_inertiaDeg_eq_finrank.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Ramification/NatCardAlgHomComapEqRamificationIdxMulInertiaDeg.lean](Valuation/Subring/Ramification/NatCardAlgHomComapEqRamificationIdxMulInertiaDeg.lean) | [S_ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Ramification/SmulEqCardStabilizerEqRamificationIdxMulInertiaDeg.lean](Valuation/Subring/Ramification/SmulEqCardStabilizerEqRamificationIdxMulInertiaDeg.lean) | [S_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_smul_eq_and_card_stabilizer_eq_ramificationIdx_mul_inertiaDeg.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/AlgClosedResidueField.lean](Valuation/Subring/Residue/AlgClosedResidueField.lean) | [S_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_isAlgClosed_residueField_of_isAlgClosed.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/AlgClosedValuationSubringRingHomRetraction.lean](Valuation/Subring/Residue/AlgClosedValuationSubringRingHomRetraction.lean) | [S_IsAlgClosed_exists_valuationSubring_ringHom_retraction.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsAlgClosed_exists_valuationSubring_ringHom_retraction.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/AlgClosedValuationSubringRingHomRetractionValuationEqOne.lean](Valuation/Subring/Residue/AlgClosedValuationSubringRingHomRetractionValuationEqOne.lean) | [S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/FinrankResidueFieldLeMulInvMemEq.lean](Valuation/Subring/Residue/FinrankResidueFieldLeMulInvMemEq.lean) | [S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_finrank_residueField_le_and_forall_mul_inv_mem_and_forall_eq_of_gauss.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/MapSubtypeEqCInvMulMapResidueNeZero.lean](Valuation/Subring/Residue/MapSubtypeEqCInvMulMapResidueNeZero.lean) | [S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_map_subtype_eq_C_inv_mul_and_map_residue_ne_zero.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/PolynomialMapResidueNeZeroEvalMulMem.lean](Valuation/Subring/Residue/PolynomialMapResidueNeZeroEvalMulMem.lean) | [S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_polynomial_map_residue_ne_zero_eval_mul_mem.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/ResidueInjOnPowEqOneResidueEq.lean](Valuation/Subring/Residue/ResidueInjOnPowEqOneResidueEq.lean) | [S_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/ResidueValuationSubring.lean](Valuation/Subring/Residue/ResidueValuationSubring.lean) | [Def_ValuationSubring_ResidueValuationSubring.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ValuationSubring_ResidueValuationSubring.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/ResidueValuationSubringValuationLtOneIff.lean](Valuation/Subring/Residue/ResidueValuationSubringValuationLtOneIff.lean) | [S_ValuationSubring_residueValuationSubring_valuation_lt_one_iff.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_residueValuationSubring_valuation_lt_one_iff.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/SumFinrankResidueFieldLeFinrank.lean](Valuation/Subring/Residue/SumFinrankResidueFieldLeFinrank.lean) | [S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/TranscendentalResidueScaling.lean](Valuation/Subring/Residue/TranscendentalResidueScaling.lean) | [S_ValuationSubring_exists_smul_mem_of_transcendental_residue.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_smul_mem_of_transcendental_residue.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/Residue/WittVectorValuationSubringResidueFieldEquiv.lean](Valuation/Subring/Residue/WittVectorValuationSubringResidueFieldEquiv.lean) | [S_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/RingHomExtend.lean](Valuation/Subring/RingHomExtend.lean) | [S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/UniqueValuationSubring.lean](Valuation/Subring/UniqueValuationSubring.lean) | [S_existsUnique_valuationSubring_of_pow_eq_mul.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_existsUnique_valuationSubring_of_pow_eq_mul.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/ValuationMulEqOneFinrankLeCard.lean](Valuation/Subring/ValuationMulEqOneFinrankLeCard.lean) | [S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_valuation_mul_eq_one_of_finrank_le_card.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Subring/ValuationMulEqOneSupEqTop.lean](Valuation/Subring/ValuationMulEqOneSupEqTop.lean) | [S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Topology/ValuedIsClosedSubmodule.lean](Valuation/Topology/ValuedIsClosedSubmodule.lean) | [S_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valued_isClosed_submodule_of_finiteDimensional_of_isClosed_subfield.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Topology/ValuedMulVecAddEqVDetEqOne.lean](Valuation/Topology/ValuedMulVecAddEqVDetEqOne.lean) | [S_Valued_exists_mulVec_add_eq_of_v_det_eq_one.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valued_exists_mulVec_add_eq_of_v_det_eq_one.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Topology/ValuedMultipliableOneAdd.lean](Valuation/Topology/ValuedMultipliableOneAdd.lean) | [S_Valued_multipliable_one_add_of_tendsto_cofinite_zero.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valued_multipliable_one_add_of_tendsto_cofinite_zero.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Topology/ValuedVProdSubOneSubSumSubLe.lean](Valuation/Topology/ValuedVProdSubOneSubSumSubLe.lean) | [S_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valued_v_prod_sub_one_sub_sum_sub_le_of_forall_v_sub_sub_mul_sub_le.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Topology/ValuedVSubEqOneVDetEqOne.lean](Valuation/Topology/ValuedVSubEqOneVDetEqOne.lean) | [S_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valued_exists_forall_v_sub_eq_one_and_v_det_eq_one_of_v_sub_sum_div_lt_one.lean) |
| [Nyll/ValuedFieldTheory/Valuation/Topology/ValuedVTprodEqFinsetProd.lean](Valuation/Topology/ValuedVTprodEqFinsetProd.lean) | [S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Valued_v_tprod_eq_finsetProd_of_forall_not_mem_v_eq_one.lean) |
~~~~~~~~

## ANTHROPIC_FLT_NOTICE

Source: `Nyll/ValuedFieldTheory/ANTHROPIC_FLT_NOTICE`. SHA-256: `42b1821f19a6aaa25e6811d22ab8f2fdc6433d4a37bc810b1cfafa5b6dd6b0b6`.

~~~~~~~~text
Fermat's Last Theorem in Lean 4
Copyright 2026 Anthropic, PBC

This repository is made available under the Apache License, Version 2.0 (see the file LICENSE).

Portions of this repository are derived from the third-party works listed in items 1-3 below, each licensed under
the Apache License, Version 2.0; item 4 lists the libraries bundled with the web pages, under their own licences.
The file ATTRIBUTION.md lists, file by file, the files of this repository that contain such material (106 files
with material from items 1 and 2, 54 under Definitions/ and 52 under P2M/Sol/; and, in its §4, the 23 files that
reproduce Mathlib text, item 3), with the upstream file each portion comes from and that file's copyright holder
and authors. The Lean files are published byte-for-byte as they were checked and carry no attribution headers,
apart from five files that retained an FLT-project notice in place (marked in ATTRIBUTION.md) and the Mathlib
provenance header of Definitions/Def_Compat_Mathlib430.lean; for all the others ATTRIBUTION.md is where the
per-file notices are reproduced. The notices below cover the works as a whole.

1. The FLT project — the Lean formalisation of Fermat's Last Theorem led by Kevin Buzzard at
   Imperial College London. https://github.com/ImperialCollegeLondon/FLT
   Material was taken from the project's `main` branch as of 2026-05-21, two files from commit
   8387d589441c1097d606ea89370c4165147255d5 (2026-05-27) and one from commit
   7a87d3b25db19d008cd45b29edd2b92803e785b1, as recorded per file in ATTRIBUTION.md.
   Copyright (c) 2024-2026 Kevin Buzzard, Andrew Yang, Matthew Jasper, Salvatore Mercuri, Javier López-Contreras,
   Madison Crim, Yaël Dillies, David Ledvinka, Ruben Van de Velde and the other authors named in the per-file
   notices (Anatole Dedecker, Bhavik Mehta, Bryan Wang Peng Jun, David Renshaw, James Sundstrom, Michael Rothgang,
   Pietro Monticone, William Coram), and the FLT project contributors.
   Released under the Apache License, Version 2.0 ("Released under Apache 2.0 license as described in the file
   LICENSE" in the per-file notices; that project's LICENSE file is the Apache License, Version 2.0, the same licence as in this
   repository's LICENSE file).
   104 files of this repository contain such material: definition modules under Definitions/ (in particular
   Def_Mathlib_*.lean — the project's "FLT/Mathlib" files —, Def_DedekindDomain_*, Def_Deformations_*, Def_HaarMeasure_*,
   Def_NumberField_*, Def_FLTPrelim_FreyPackage/GaloisRep, Def_AbstractHeckeOperator, Def_Patching_SystemTypes,
   Def_Representation_AbsolutelyIrreducible and others) and proof modules under P2M/Sol/ that inline upstream lemmas
   (patching, depth, adic valuations and finite adeles, restricted products, Haar characters, Frobenius elements,
   the Frey curve); ATTRIBUTION.md §§1-2 is the complete list.

2. flt-regular — the Lean formalisation of Fermat's Last Theorem for regular primes (Kummer's theorem).
   https://github.com/leanprover-community/flt-regular
   A. J. Best, C. Birkbeck, R. Brasca, E. Rodriguez Boidi, R. Van de Velde, A. Yang, "A complete formalization of
   Fermat's Last Theorem for regular primes in Lean", arXiv:2410.01466.
   Copyright (c) the flt-regular authors, as recorded in that repository.
   Released under the Apache License, Version 2.0.
   P2M/Sol/S_flt_regular.lean is a port, with proofs, of that project's FltRegular/NumberTheory/* (regular primes,
   cyclotomic units, Hilbert 90/92/94, Kummer's lemma), FltRegular/MayAssume/*, FltRegular/CaseI/* and FltRegular/CaseII/*
   files, ending in the theorem that Fermat's Last Theorem holds for odd regular prime exponents; it is used here for
   the exponents 7, 11 and 13. P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean adapts FltRegular/SmallNumbers/*.
   That project's per-file headers are not reproduced in this revision; this notice and ATTRIBUTION.md §3 stand in
   their place.

3. Mathlib — https://github.com/leanprover-community/mathlib4
   Copyright (c) the respective Mathlib authors, as recorded in the headers of the Mathlib source files.
   Released under the Apache License, Version 2.0.
   This repository is built against a pinned Mathlib revision (see lake-manifest.json); some files adapt or restate
   Mathlib material. One file copies Mathlib text wholesale: Definitions/Def_Compat_Mathlib430.lean reproduces,
   under new names and without their docstrings, the Mathlib v4.30.0 (commit
   c5ea00351c28e24afc9f0f84379aa41082b1188f) text of a few definitions, lemmas and one notation whose form changed
   in Mathlib v4.33.0 — verbatim apart from four lines marked `-- [port]` — each copied block headed by the Mathlib
   file and line range it is taken from, together with two small bridging declarations of our own
   (Representation.ofMulActionFinsuppEquiv, Rep.ofMulActionFinsuppIso), three one-line `example` checks and, in its
   last block, four lemmas adapted and re-proved from Mathlib/NumberTheory/RamificationInertia/Galois.lean rather
   than copied. In addition, twenty-two other modules (twenty-one under P2M/Sol/, one under Definitions/) inline or
   adapt an individual proof or auxiliary construction from one of thirteen further Mathlib files — for example the
   exactness construction of Mathlib/RingTheory/AdicCompletion/Exactness.lean and the proof of `integral_comp_abs`
   from Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean — typically a private Mathlib lemma re-proved in
   place. ATTRIBUTION.md §4 lists the modules so identified, each with the Mathlib file drawn on and that file's
   copyright and author lines, twenty-one Mathlib files in all. Shorter restatements of Mathlib lemmas elsewhere in
   the tree have not been traced individually; this notice covers Mathlib as a whole.

4. Libraries bundled with the web pages, in html/assets/vendor/ (used only by the html/ documentation, not by the Lean
   build), each distributed under its own licence; html/assets/vendor/LICENSES.txt lists them:
   - KaTeX 0.18.4 (katex/katex.min.js, and katex/katex-embedded.css with the KaTeX fonts inlined).
     Copyright (c) 2013-2020 Khan Academy and other contributors. MIT License, reproduced in
     html/assets/vendor/katex/LICENSE. The bundled KaTeX fonts are Copyright (c) 2009-2010 Design Science, Inc. and
     Copyright (c) 2014-2018 Khan Academy, under the SIL Open Font License 1.1, whose text and the fonts' notice are
     reproduced in html/assets/vendor/katex/FONTS-LICENSE.txt.
   - @hpcc-js/wasm 2.35.0 (graphviz.umd.js: Graphviz compiled to WebAssembly). Apache License, Version 2.0, reproduced
     in html/assets/vendor/graphviz.LICENSE.txt. It includes Graphviz as compiled code, licensed under the Eclipse
     Public License 1.0 / Common Public License; the Graphviz source code is published at
     https://gitlab.com/graphviz/graphviz (Eclipse Public License 1.0).

The Lean 4 toolchain (https://github.com/leanprover/lean4) and the other Lake packages listed in lake-manifest.json
are dependencies fetched at build time and are not distributed in this repository.
~~~~~~~~

## ANTHROPIC_FLT_ATTRIBUTION.md

Source: `Nyll/ValuedFieldTheory/ANTHROPIC_FLT_ATTRIBUTION.md`. SHA-256: `698fb76c8d80b2ed78ebd48b271f2ee5815b3654fb8ec5c699b21b16ce0d9698`.

~~~~~~~~text
# ATTRIBUTION — third-party material in this repository, file by file

This file accompanies `NOTICE`. It lists every file of this repository that we have identified as containing Lean text taken or adapted from a third-party project (106 files with material from the Imperial College London FLT project or the flt-regular project, §§1–3: 54 under `Definitions/`, 52 under `P2M/Sol/`; and the 23 files that reproduce Mathlib text, §4), names the upstream file(s), and reproduces the upstream copyright holder and author list. The Lean files are published byte-for-byte as they were checked and carry no attribution headers, apart from five files that retained an upstream notice in place (marked below) and the Mathlib provenance header of `Definitions/Def_Compat_Mathlib430.lean` (§4); for all the others this table is where the per-file notices are reproduced. Everything listed is licensed upstream under the Apache License, Version 2.0, the licence of this repository.

## How this table was made

The Lean files of this repository were assembled by AI agents and were published without their comments, so upstream headers did not survive in place. To restore the attribution we compared, line by line after normalising whitespace and dropping `import`/`open`/`namespace`/`section` lines, every one of the 60,478 `.lean` files of the tree as it then stood on Lean 4.30.0 (its 60,474 modules, `lakefile.lean` and three Lean files under `verification/`, of which this release keeps two) against the copies of Imperial College London FLT files that had been brought into our working tree in May 2026 with their original headers intact (97 files from the upstream `main` branch as of 2026-05-21, plus three files of ours that were themselves ports of the upstream Frey-package and torsion files), and we cross-checked the result against the provenance notes that the files carried before their comments were removed (two files were ported directly from upstream commit `8387d589` of 2026-05-27 and are identified from those notes). A file is listed when it shares with an upstream file at least five distinctive lines (lines of 20 or more characters that occur in at most three upstream files and at most twelve files of this repository), or at least three such lines covering at least half of the upstream file; a few shorter passages found on review are listed too. "Extent" is the share of the file's non-blank code lines found in the named upstream file(s); it is approximate, and where a file lists several upstream files some of the matched lines are common to those files. The flt-regular rows rest on the pre-publication provenance notes alone (we had no copy of that project to compare against). The files published here are the port of that tree to Lean 4.33.1 and Mathlib v4.33.0: the port renamed Mathlib lemmas and adjusted proofs mechanically in 65 of the 106 listed files (under a tenth of the lines of each, except the 31-line `Definitions/Def_Mathlib_RingTheory_DedekindDomain_AdicValuation.lean`) and left the other 41 byte-identical, so the extents below, computed on the Lean 4.30.0 text, remain approximately right; which files are listed is unaffected. Limits of the method are stated in §5.

## 1. Files containing material from the Imperial College London FLT project

Upstream: <https://github.com/ImperialCollegeLondon/FLT>, branch `main` as of 2026-05-21 (the date our copies were taken; we did not record the commit hash) unless a commit is given. 90 files. Upstream paths are relative to that repository.

| File in this repository | Extent | Upstream file(s) — copyright holder; authors (verbatim from the upstream header) |
|---|---|---|
| `Definitions/Def_AbstractHeckeOperator.lean` | whole file (100%) | `FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Abstract.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper |
| `Definitions/Def_CategoryTheory_Subfunctor_OfIsTerminal.lean` | whole file (100%) | `FLT/Deformations/Subfunctor.lean` — © 2025 Andrew Yang; authors: Andrew Yang |
| `Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean` | whole file (98%) | `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `Definitions/Def_DedekindDomain_Completion_BaseChange.lean` | whole file | `FLT/DedekindDomain/Completion/BaseChange.lean` — commit 8387d589 (2026-05-27); © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper (see §5)<br>`FLT/Mathlib/Algebra/Algebra/Bilinear.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri, Ruben Van de Velde<br>`FLT/Mathlib/Algebra/Algebra/Pi.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/RingTheory/TensorProduct/Basis.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/DedekindDomain/IntegralClosure.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper<br>`FLT/Mathlib/Algebra/Module/Submodule/Basic.lean` — © 2025 Yaël Dillies; authors: Yaël Dillies, Kevin Buzzard, Matthew Jasper<br>`FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper |
| `Definitions/Def_DedekindDomain_FiniteAdeleRing_BaseChange.lean` | whole file | `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean` — commit 8387d589 (2026-05-27); © 2025 Kevin Buzzard; authors: Kevin Buzzard, Matthew Jasper (see §5)<br>`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Module.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/Mathlib/Topology/Algebra/Algebra/Hom.lean` — © 2026 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard<br>`FLT/Mathlib/LinearAlgebra/Pi.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard<br>`FLT/Mathlib/Algebra/Algebra/Hom.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `Definitions/Def_DedekindDomain_FiniteAdeleRing_IsDirectLimitRestricted.lean` | whole file (100%) | `FLT/DedekindDomain/FiniteAdeleRing/IsDirectLimitRestricted.lean` — © 2025 Madison Crim; authors: Madison Crim |
| `Definitions/Def_DedekindDomain_FiniteAdeleRing_TensorPi.lean` | whole file (100%) | `FLT/DedekindDomain/FiniteAdeleRing/TensorPi.lean` — © 2025 Madison Crim; authors: Madison Crim |
| `Definitions/Def_DedekindDomain_FiniteAdeleRing_TensorRestrictedProduct.lean` | whole file (100%) | `FLT/DedekindDomain/FiniteAdeleRing/TensorRestrictedProduct.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper |
| `Definitions/Def_DedekindDomain_IntegralClosure.lean` | whole file (100%) | `FLT/DedekindDomain/IntegralClosure.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper |
| `Definitions/Def_Deformations_ContinuousSMulDiscrete.lean` | whole file (100%) | `FLT/Deformations/RepresentationTheory/ContinuousSMulDiscrete.lean` — © 2025 Andrew Yang; authors: Andrew Yang |
| `Definitions/Def_Deformations_Deformations_Lemmas.lean` | whole file (100%) | `FLT/Deformations/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde<br>`FLT/Deformations/RepresentationTheory/IntegralClosure.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard |
| `Definitions/Def_Deformations_Frobenius.lean` | whole file (100%) | `FLT/Deformations/RepresentationTheory/Frobenius.lean` — © 2025 Andrew Yang; authors: Andrew Yang |
| `Definitions/Def_Deformations_IsProartinian.lean` | whole file (98%) | `FLT/Patching/Utils/AdicTopology.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Deformations/IsProartinian.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde<br>`FLT/Patching/Utils/InverseLimit.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard |
| `Definitions/Def_Deformations_IsResidueAlgebra.lean` | whole file (100%) | `FLT/Deformations/IsResidueAlgebra.lean` — © 2025 Javier López-Contreras; authors: Javier López-Contreras, Kevin Buzzard |
| `Definitions/Def_Deformations_LiftFunctor.lean` | whole file (100%) | `FLT/Deformations/LiftFunctor.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `Definitions/Def_Deformations_MvPowerSeriesObj.lean` | portions (≈8%) | `FLT/Deformations/Categories.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone |
| `Definitions/Def_Deformations_ProartinianCat.lean` | whole file (100%) | `FLT/Deformations/Categories.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone |
| `Definitions/Def_Deformations_ProartinianCompact.lean` | portions (≈16%; about six lines — the proof that a proper open ideal of a pro-Artinian ring has Artinian local quotient — match FLT/Deformations/IsProartinian.lean) | `FLT/Deformations/IsProartinian.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `Definitions/Def_ExtCitation_LocalLevelResidues.lean` | portions (≈20%) | `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde<br>`FLT/Deformations/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `Definitions/Def_HaarMeasure_HaarChar_AddEquiv.lean` | whole file (100%) | `FLT/HaarMeasure/HaarChar/AddEquiv.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, James Sundstrom, Ruben Van de Velde, Anatole Dedecker, Bryan Wang Peng Jun, David Renshaw |
| `Definitions/Def_HaarMeasure_HaarChar_Ring.lean` | whole file (100%) | `FLT/HaarMeasure/HaarChar/Ring.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard |
| `Definitions/Def_M4aHerbrand_FiniteTensorEquiv.lean` | portions (≈3%) | `FLT/DedekindDomain/IntegralClosure.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper |
| `Definitions/Def_Mathlib_Algebra_Algebra_Hom.lean` | whole file (100%) | `FLT/Mathlib/Algebra/Algebra/Hom.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/Topology/Algebra/Algebra/Hom.lean` — © 2026 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `Definitions/Def_Mathlib_Algebra_IsDirectLimit.lean` | whole file (100%) | `FLT/Mathlib/Algebra/IsDirectLimit.lean` — © 2025 Madison Crim; authors: Madison Crim |
| `Definitions/Def_Mathlib_IsModuleTopology.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/Module/ModuleTopology.lean` — © 2024 Kevin Buzzard; authors: Kevin Buzzard, Pietro Monticone, Salvatore Mercuri, Matthew Jasper, Ruben Van de Velde, William Coram<br>`FLT/Mathlib/Algebra/Algebra/Tower.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard<br>`FLT/Deformations/ContinuousRepresentation/IsTopologicalModule.lean` — © 2025 Javier López-Contreras; authors: Javier López-Contreras |
| `Definitions/Def_Mathlib_LinearAlgebra_Countable.lean` | whole file (100%) | `FLT/Mathlib/LinearAlgebra/Countable.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard |
| `Definitions/Def_Mathlib_MeasureTheory_Constructions_BorelSpace_RestrictedProduct.lean` | whole file (100%) | `FLT/Mathlib/MeasureTheory/Constructions/BorelSpace/RestrictedProduct.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard |
| `Definitions/Def_Mathlib_MeasureTheory_Group_Action.lean` | whole file (100%) | `FLT/Mathlib/MeasureTheory/Group/Action.lean` — © 2024 Yaël Dillies; authors: Yaël Dillies, Kevin Buzzard, Ruben Van de Velde, David Ledvinka |
| `Definitions/Def_Mathlib_MeasureTheory_Group_Measure.lean` | whole file (100%) | `FLT/Mathlib/MeasureTheory/Group/Measure.lean` — © 2025 David Ledvinka; authors: David Ledvinka |
| `Definitions/Def_Mathlib_MeasureTheory_Measure_Typeclasses_Finite.lean` | whole file (100%) | `FLT/Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean` — © 2025 David Ledvinka; authors: David Ledvinka |
| `Definitions/Def_Mathlib_Order_Filter_Cofinite.lean` | whole file (100%) | `FLT/Mathlib/Order/Filter/Cofinite.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard |
| `Definitions/Def_Mathlib_RightActionInstances.lean` | whole file (100%) | `FLT/Hacks/RightActionInstances.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Pietro Monticone |
| `Definitions/Def_Mathlib_RingTheory_DedekindDomain_AdicValuation.lean` | whole file (100%) | `FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `Definitions/Def_Mathlib_RingTheory_Ideal_Quotient_Basic.lean` | whole file (100%) | `FLT/Mathlib/RingTheory/Ideal/Quotient/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `Definitions/Def_Mathlib_RingTheory_Localization_BaseChange.lean` | whole file (100%) | `FLT/Mathlib/RingTheory/Localization/BaseChange.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper |
| `Definitions/Def_Mathlib_RingTheory_LocalRing_Defs.lean` | whole file (100%) | `FLT/Mathlib/RingTheory/LocalRing/Defs.lean` — © 2025 Javier López-Contreras; authors: Javier López-Contreras, Kevin Buzzard |
| `Definitions/Def_Mathlib_Topology_Algebra_ContinuousMonoidHom.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/ContinuousMonoidHom.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `Definitions/Def_Mathlib_Topology_Algebra_Group_Units.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/Group/Units.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Ruben Van de Velde |
| `Definitions/Def_Mathlib_Topology_Algebra_Module_Quotient.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/Module/Quotient.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard, Pietro Monticone |
| `Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_Basic.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde<br>`FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun, Pietro Monticone<br>`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_Equiv.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun, Pietro Monticone<br>`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde |
| `Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/RestrictedProduct/TopologicalSpace.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Bhavik Mehta, Ruben Van de Velde, Bryan Wang Peng Jun, Pietro Monticone<br>`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Equiv.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/Topology/Algebra/RestrictedProduct/Basic.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper, Kevin Buzzard, Ruben Van de Velde |
| `Definitions/Def_Mathlib_Topology_Algebra_UniformRing.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/UniformRing.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `Definitions/Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean` | whole file (100%) | `FLT/Mathlib/Topology/Algebra/Valued/WithZeroMulInt.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri |
| `Definitions/Def_Mathlib_Topology_Bases.lean` | whole file (100%) | `FLT/Mathlib/Topology/Bases.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard |
| `Definitions/Def_NumberField_Completion_Finite.lean` | whole file (100%) | `FLT/NumberField/Completion/Finite.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard |
| `Definitions/Def_NumberField_Extension.lean` | whole file (100%) | `FLT/NumberField/InfinitePlace/Extension.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri |
| `Definitions/Def_NumberField_HeightOneSpectrum.lean` | whole file (100%) | `FLT/NumberField/HeightOneSpectrum.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard |
| `Definitions/Def_Patching_SystemTypes.lean` | portions (≈42%; pre-publication provenance note: 'typeclass/predicate definitions of the Taylor–Wiles–Kisin patching set-up, itself ported from ImperialCollegeLondon/FLT (Andrew Yang, Kevin Buzzard et al.)') | `FLT/Patching/Utils/TopologicallyFG.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang<br>`FLT/Patching/Utils/AdicTopology.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Patching/Algebra.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Yaël Dillies<br>`FLT/Patching/Module.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone, David Renshaw |
| `Definitions/Def_Representation_AbsolutelyIrreducible.lean` | whole file (82%) | `FLT/Mathlib/RepresentationTheory/Basic.lean` — © 2024 Javier López-Contreras; authors: Javier López-Contreras, Kevin Buzzard<br>`FLT/Deformations/RepresentationTheory/Irreducible.lean` — © 2024 Javier López-Contreras; authors: Javier López-Contreras, Kevin Buzzard |
| `Definitions/Def_ValuationSubring_RatPlaceCenterHelpers.lean` | portions (≈18%) | `FLT/Deformations/RepresentationTheory/IntegralClosure.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Deformations/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `P2M/Sol/S_Algebra_PatchingDatum_nonempty_patchingLevel_bot.lean` | large part (≈61%); upstream notices also retained in place before the included portions | `FLT/Patching/Module.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone, David Renshaw<br>`FLT/Patching/Over.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone<br>`FLT/Patching/Utils/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Pietro Monticone, Ruben Van de Velde<br>`FLT/Patching/Algebra.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Yaël Dillies<br>`FLT/Patching/System.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde<br>`FLT/Patching/Ultraproduct.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Patching/Utils/StructureFiniteness.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Patching/Utils/AdicTopology.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Patching/Utils/InverseLimit.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Patching/Utils/TopologicallyFG.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Patching/REqualsT.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard<br>`FLT/Deformations/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `P2M/Sol/S_AlgebraicCurve_fibreResidueIdentityAlong_of_separableAlong_of_dCoordGenerates.lean` | one short lemma (`IsLocalRing.maximalIdeal_le`) | `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_AlgebraicCurve_residueTheorem_of_residueTheorem_ratFunc_of_residueTraceCompletionCommute.lean` | one short lemma (`IsLocalRing.maximalIdeal_le`) | `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean` | one short lemma (`IsLocalRing.maximalIdeal_le`) | `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_AlgebraicCurve_tateAgreement_v2.lean` | one short lemma (`IsLocalRing.maximalIdeal_le`) | `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_AlgebraicCurve_tateAgreement.lean` | one short lemma (`IsLocalRing.maximalIdeal_le`) | `FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_AlgebraicCurve_tateChainRule.lean` | a short passage (a few lines) | `FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean` | portions (≈4%) | `FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean` | a short passage (a few lines) | `FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri<br>`FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level.lean` | portions (≈20%) | `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde<br>`FLT/Deformations/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `P2M/Sol/S_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal.lean` | large part (≈44%) | `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde<br>`FLT/Deformations/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `P2M/Sol/S_groupCohomology_exists_mem_split_adjoin_rootsOfUnity_of_padic.lean` | a short passage (a few lines) | `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `P2M/Sol/S_groupCohomology_isMulCoboundary1_of_isMulCocycle1_of_level.lean` | portions (≈9%) | `FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.lean` | large part (≈61%) | `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_sub_algebraMap_mem_adicCompletionIntegers.lean` | portions (≈28%) | `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper |
| `P2M/Sol/S_IsLocalRing_isRegular_of_systemOfParameters.lean` | portions (≈10%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_IsProartinian_finite_quotient_of_isOpen.lean` | portions (≈25%; the same six-line passage as in Def_Deformations_ProartinianCompact) | `FLT/Deformations/IsProartinian.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `P2M/Sol/S_IsRegularLocalRing_depth_self_eq_ringKrullDim.lean` | portions (≈12%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_isSMulRegular_iff_of_free.lean` | whole file (93%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_M4aHerbrand_nonempty_ideleGaloisDescent.lean` | a short passage (a few lines) | `FLT/DedekindDomain/IntegralClosure.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Andrew Yang, Matthew Jasper |
| `P2M/Sol/S_Module_depth_eq_depth_of_finite_of_isLocalHom.lean` | portions (≈8%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_Module_depth_le_ringKrullDim_quotient_of_mem_associatedPrimes.lean` | portions (≈17%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_Module_depth_le_ringKrullDim.lean` | large part (≈75%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_Module_depth_quotient_eq_depth.lean` | portions (≈17%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_Module_depth_quotSMulTop_succ_eq.lean` | portions (≈17%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_Module_free_of_depth_eq_ringKrullDim_of_isRegularLocalRing.lean` | portions (≈12%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_MvPowerSeries_depth_self_eq_ringKrullDim_fin_of_isDiscreteValuationRing.lean` | portions (≈9%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_MvPowerSeries_depth_self_fin_eq_of_isDiscreteValuationRing.lean` | portions (≈9%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_MvPowerSeries_ringKrullDim_fin_eq_of_isDiscreteValuationRing.lean` | portions (≈9%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_NumberField_count_normalizedFactors_differentIdeal_le_of_mem_primesOverFinset_three.lean` | portions (≈9%); upstream notices also retained in place before the included portions | `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/Mathlib/Topology/Algebra/Valued/WithZeroMulInt.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri<br>`FLT/Mathlib/RingTheory/Valuation/ValuationSubring.lean` — © 2025 Ruben Van de Velde; authors: Ruben Van de Velde, Kevin Buzzard, Salvatore Mercuri<br>`FLT/Deformations/RepresentationTheory/AbsoluteGaloisGroup.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde<br>`FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri<br>`FLT/NumberField/Completion/Finite.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard<br>`FLT/Deformations/RepresentationTheory/GaloisRep.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone<br>`FLT/Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard |
| `P2M/Sol/S_NumberField_finrank_le_two_of_isGalois_of_isUnramifiedAt_of_finrank_dvd_sixteen.lean` | portions (≈3%) | `FLT/Deformations/Lemmas.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde |
| `P2M/Sol/S_Representation_isAbsolutelyIrreducible_iff_isIrreducible_and_surjective_algebraMap_end.lean` | portions (≈3%) | `FLT/Mathlib/RepresentationTheory/Basic.lean` — © 2024 Javier López-Contreras; authors: Javier López-Contreras, Kevin Buzzard |
| `P2M/Sol/S_RingTheory_Sequence_isWeaklyRegular_of_free_aux.lean` | large part (≈64%) | `FLT/Patching/Utils/Depth.lean` — © 2025 Andrew Yang; authors: Andrew Yang, Kevin Buzzard, Michael Rothgang |
| `P2M/Sol/S_Submodule_fg_and_span_eq_top_ofFiniteIdele.lean` | portions (≈21%) | `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `P2M/Sol/S_Submodule_finiteAdeleBox_conjByFiniteIdele.lean` | portions (≈20%) | `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `P2M/Sol/S_Submodule_finiteAdeleBox_ofFiniteIdele.lean` | portions (≈26%) | `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `P2M/Sol/S_Submodule_ofFiniteIdele_eq_ofFiniteIdele_iff.lean` | portions (≈26%) | `FLT/DedekindDomain/AdicValuation.lean` — © 2025 Matthew Jasper; authors: Matthew Jasper<br>`FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `P2M/Sol/S_TraceFibrePushforward_exists_forall_tracePushforward_eq_indicator_of_forall_eq_indicator.lean` | a short passage — one short instance (SeparableSpace (v.adicCompletion K)), ≈6 lines | `FLT/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard, Salvatore Mercuri |
| `P2M/Sol/S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean` | a short passage (a few lines); upstream notices also retained in place before the included portions | `FLT/Mathlib/LinearAlgebra/Countable.lean` — © 2025 Kevin Buzzard; authors: Kevin Buzzard |

## 2. Files containing Imperial College London FLT material through an intermediate port

In May 2026 we ported the upstream Frey-package file and the torsion Galois-module file by hand into our working tree, restructuring them and adding material of our own; the files below contain text from those two ports (extents count only lines traceable to them, as best we can tell). The upstream paths and author lists given here are as recorded in our port's notes and have not been re-checked against the upstream repository, whose file headers are authoritative, with one exception: the notice of `FLT/EllipticCurve/Torsion.lean` below is the upstream file's own, at the commit named. 14 files.

| File in this repository | Extent | Upstream file (as recorded) — authors (as recorded) |
|---|---|---|
| `Definitions/Def_FLTPrelim_FreyPackage.lean` | adapted (upstream notice retained in place, from our May port) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `Definitions/Def_FLTPrelim_GaloisRep.lean` | adapted (upstream notice retained in place, from our May port) | `FLT/EllipticCurve/Torsion.lean` (commit 7a87d3b25db1) — © 2024 Kevin Buzzard; authors: Kevin Buzzard (path as recorded in our port; the notice retained inside our file is our May port's generic one, the upstream notice is reproduced here) |
| `Definitions/Def_FreyCurve_Basic.lean` | large part (≈74%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_dvd_freyCurveInt_discr_iff.lean` | portions (≈23%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_frey_exists_p_torsion_integral_abscissa_of_stable_line.lean` | portions (≈3%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_frey_exists_p_torsion_integral_abscissa.lean` | portions (≈3%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_frey_isModular.lean` | portions (≈13%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_frey_isSemistableModel.lean` | portions (≈30%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_freyCurveInt_discr_ne_zero.lean` | portions (≈28%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_freyCurveInt_map.lean` | portions (≈28%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_freyGaloisRep_isUnramifiedAt.lean` | portions (≈22%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_not_dvd_freyCurveInt_c4.lean` | portions (≈27%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_padicValInt_freyCurveInt_discr.lean` | portions (≈28%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |
| `P2M/Sol/S_FreyPackage_padicValInt_two_freyCurveInt_discr.lean` | portions (≈26%) | `FLT/Basic/FreyPackage.lean` — authors recorded in our intermediate port: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone (path as recorded in our port) |

## 3. Files containing material from the flt-regular project

Upstream: <https://github.com/leanprover-community/flt-regular> — *A complete formalization of Fermat's Last Theorem for regular primes in Lean*, Alex J. Best, Christopher Birkbeck, Riccardo Brasca, Eric Rodriguez Boidi, Ruben Van de Velde, Andrew Yang (arXiv:2410.01466). Apache License, Version 2.0. That project's per-file headers are not reproduced in this revision; the project, its authors and the files drawn on are named instead.

| File in this repository | Extent | Upstream files |
|---|---|---|
| `P2M/Sol/S_flt_regular.lean` | large part: a port with proofs (about 4,200 lines) of the regular-prime case — regular primes, cyclotomic units, Hilbert 90/92/94, Kummer's lemma, case I, case II | `FltRegular/NumberTheory/RegularPrimes.lean`, `FltRegular/NumberTheory/Cyclotomic/CyclRat.lean`, `FltRegular/NumberTheory/Cyclotomic/MoreLemmas.lean`, `FltRegular/NumberTheory/Cyclotomic/UnitLemmas.lean`, `FltRegular/NumberTheory/Cyclotomic/CaseI.lean`, `FltRegular/NumberTheory/CyclotomicRing.lean`, `FltRegular/NumberTheory/SystemOfUnits.lean`, `FltRegular/NumberTheory/Hilbert92.lean`, `FltRegular/NumberTheory/Unramified.lean`, `FltRegular/NumberTheory/Hilbert94.lean`, `FltRegular/NumberTheory/KummersLemma/Field.lean`, `FltRegular/MayAssume/Lemmas.lean`, `FltRegular/CaseI/AuxLemmas.lean`, `FltRegular/CaseI/Statement.lean`, `FltRegular/CaseII/AuxLemmas.lean`, `FltRegular/CaseII/InductionStep.lean`, `FltRegular/CaseII/Statement.lean`, `FltRegular/FltRegular.lean` |
| `P2M/Sol/S_IsCyclotomicExtension_Rat_seven_pid.lean` | portions: the class-number-one computation for the 7th cyclotomic field | `FltRegular/SmallNumbers/PID.lean`, `FltRegular/SmallNumbers/Seven/Seven.lean` |

## 4. Mathlib

This repository is built on Mathlib (<https://github.com/leanprover-community/mathlib4>, Apache-2.0, copyright the Mathlib authors as recorded in its file headers), which is fetched at build time and not distributed here. The `Definitions/Def_Mathlib_*` files listed in §1 are the Imperial College London project's "FLT/Mathlib" staging files, not copies of Mathlib files. Mathlib text nevertheless occurs in the tree in two ways.

First, one file copies Mathlib text wholesale. `Definitions/Def_Compat_Mathlib430.lean` reproduces, under new names and without their docstrings, the Mathlib v4.30.0 (commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`) text of a few definitions, lemmas and one notation whose form changed in Mathlib v4.33.0 — verbatim apart from four lines marked `-- [port]` — each copied block headed by the Mathlib file and line range it is taken from; it also contains two small bridging declarations of our own (`Representation.ofMulActionFinsuppEquiv`, `Rep.ofMulActionFinsuppIso`), three one-line `example` checks and, in its last block, four lemmas adapted and re-proved from `Mathlib/NumberTheory/RamificationInertia/Galois.lean` rather than copied. The eight Mathlib files it draws on and their notices (identical at Mathlib v4.30.0 and v4.33.0; each header, here and in the second table, continues "All rights reserved. Released under Apache 2.0 license as described in the file LICENSE.") are listed in the first table below.

Second, some modules re-prove a Mathlib lemma in place — usually a private or auxiliary Mathlib result the module needed — and in doing so reproduce its proof text. To find these we compared every `.lean` file of this repository, line by line after normalising whitespace and dropping `import`/`open`/`namespace`/`section` lines, against every file of Mathlib v4.33.0 (commit `db584cd6d46c92f209a44c0f1c829460d327499d`) and v4.30.0, and list below the modules this comparison identified as sharing a run of roughly eight or more consecutive lines with a Mathlib file, setting aside matches that are only routine structure-instance boilerplate. Twenty-two modules are listed (twenty-one under `P2M/Sol/`, one under `Definitions/`; one of them, `P2M/Sol/S_flt_regular.lean`, also appears in §3 for its flt-regular material); the second table below gives for each the Mathlib file, that file's copyright holder and authors (verbatim from its header), what was taken, and the approximate extent. The comparison is sensitive to how lines are normalised; shorter restatements, and proofs that follow a Mathlib argument without reproducing its text, are not listed individually; Mathlib as a whole is credited in `NOTICE`.

| Mathlib file | Copyright holder; authors (verbatim from the file header) |
|---|---|
| `Mathlib/RepresentationTheory/Basic.lean` | Copyright (c) 2022 Antoine Labelle; Authors: Antoine Labelle |
| `Mathlib/RepresentationTheory/Rep/Basic.lean` | Copyright (c) 2026 Yunzhou Xie; Authors: Edison Xie, Kim Morrison |
| `Mathlib/Algebra/Group/End.lean` | Copyright (c) 2018 Johannes Hölzl; Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov |
| `Mathlib/Algebra/GroupWithZero/Action/Basic.lean` | Copyright (c) 2018 Chris Hughes; Authors: Chris Hughes, Yury Kudryashov |
| `Mathlib/Algebra/Ring/AddAut.lean` | Copyright (c) 2022 Yury Kudryashov; Authors: Yury Kudryashov |
| `Mathlib/Algebra/Ring/Action/Submonoid.lean` | Copyright (c) 2024 David Ang; Authors: David Ang |
| `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` | Copyright (c) 2024 David Kurniadi Angdinata; Authors: David Kurniadi Angdinata |
| `Mathlib/NumberTheory/RamificationInertia/Galois.lean` | Copyright (c) 2024 Yongle Hu; Authors: Yongle Hu, Jiedong Jiang |

| File of this repository | Mathlib file | Copyright holder; authors (verbatim from the file header) | Material taken (approximate extent) |
|---|---|---|---|
| `P2M/Sol/S_AdicCompletion_map_algebraLinearMap_injective_and_mem_range_iff_of_isInvariant.lean` | `Mathlib/RingTheory/AdicCompletion/Exactness.lean` | Copyright (c) 2024 Judith Ludwig, Christian Merten; Authors: Judith Ludwig, Christian Merten | the auxiliary construction `mapExactAuxDelta` / `mapExactAux` and the proofs of `AdicCompletion.map_injective` and `AdicCompletion.map_exact`, adapted (≈65 lines, about three fifths of the Mathlib file's proof text) |
| `P2M/Sol/S_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one.lean` | `Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean` | Copyright (c) 2017 Johannes Hölzl; Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov | the proof of `integral_comp_abs`, inlined (≈18 lines) |
| `P2M/Sol/S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.lean` | `Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean` | Copyright (c) 2017 Johannes Hölzl; Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov | the proof of `integral_comp_abs`, inlined (≈18 lines) |
| `P2M/Sol/S_NumberField_TateGlobal_exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one.lean` | `Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean` | Copyright (c) 2017 Johannes Hölzl; Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov | the proof of `integral_comp_abs`, inlined (≈18 lines) |
| `P2M/Sol/S_LanglandsTunnell_ArchPlace_complexZeta_complexTestFun_complexCharFun_eq_pi_mul_GammaComplex.lean` | `Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean` | Copyright (c) 2017 Johannes Hölzl; Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov | the proof of `integral_comp_abs`, inlined (≈18 lines) |
| `P2M/Sol/S_LanglandsTunnell_ArchPlace_realZeta_realTestFun_realCharFun_eq_GammaReal.lean` | `Mathlib/MeasureTheory/Measure/Lebesgue/Integral.lean` | Copyright (c) 2017 Johannes Hölzl; Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov | the proof of `integral_comp_abs`, inlined (≈18 lines) |
| `P2M/Sol/S_NumberField_exists_isBigO_card_absNorm_le_mk_eq_sub.lean` | `Mathlib/NumberTheory/NumberField/Ideal/Asymptotics.lean` | Copyright (c) 2025 Xavier Roblot; Authors: Xavier Roblot | the auxiliary statements `tendsto_norm_le_and_mk_eq_div_atTop_aux₁` / `_aux₂` (the ideal-counting bijection), adapted (≈25 lines) |
| `Definitions/Def_AlgebraicGeometry_LocalRepresentabilityULift.lean` | `Mathlib/AlgebraicGeometry/Sites/Representability.lean` | Copyright (c) 2024 Calle Sönne; Authors: Calle Sönne, Joël Riou, Ravi Vakil | the `glueData` construction for a locally representable functor and `glueData_openCover_map`, adapted to a universe-lifted setting (≈20–35 lines) |
| `P2M/Sol/S_AlgebraicGeometry_exists_etale_nhd_of_flat_stalkMap_of_map_maximalIdeal_eq_of_isIso_residueFieldMap.lean` | `Mathlib/RingTheory/Smooth/Fiber.lean` | Copyright (c) 2026 Andrew Yang; Authors: Andrew Yang | the proof of `Algebra.IsSmoothAt.of_formallySmooth_fiber`, adapted (≈20 lines) |
| `P2M/Sol/S_ExtCitation_Cyclotomic_thaine_relation_plusField.lean` | `Mathlib/RepresentationTheory/Homological/GroupCohomology/Hilbert90.lean` | Copyright (c) 2023 Amelia Livingston; Authors: Riccardo Brasca, Amelia Livingston | the proof of `exists_mul_galRestrict_of_norm_eq_one` (integral form of Hilbert's Theorem 90), restated as a private lemma (≈17 lines) |
| `P2M/Sol/S_AutomorphicForm_setIntegral_residualProj_mul_conj_eq_sum_integral_maximalCompact_residue_pairing_slab.lean` | `Mathlib/Analysis/MellinInversion.lean` | Copyright (c) 2024 Lawrence Wu; Authors: Lawrence Wu | the private auxiliary lemmas `rexp_neg_deriv_aux`, `rexp_neg_image_aux`, `rexp_neg_injOn_aux`, `rexp_cexp_aux`, verbatim (≈13 lines) |
| `P2M/Sol/S_NumberField_not_tendsto_tprod_eulerProduct_nhdsGT_one_nhds_zero_of_three_four_one.lean` | `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` | Copyright (c) 2024 Michael Stoll; Authors: Michael Stoll, David Loeffler | the proof of the private lemma `re_log_comb_nonneg'` (the 3-4-1 inequality), inlined (≈10 lines) |
| `P2M/Sol/S_NumberField_TateGlobal_exists_forall_one_le_mul_norm_apply_of_differentiable_of_eq_partialEulerProduct.lean` | `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` | Copyright (c) 2024 Michael Stoll; Authors: Michael Stoll, David Loeffler | the proof of the private lemma `re_log_comb_nonneg'`, inlined (≈10 lines) |
| `P2M/Sol/S_NumberField_TateGlobal_exists_one_le_mul_norm_of_eq_sub_mul_partialEulerProduct_normPowChar.lean` | `Mathlib/NumberTheory/LSeries/Nonvanishing.lean` | Copyright (c) 2024 Michael Stoll; Authors: Michael Stoll, David Loeffler | the proof of the private lemma `re_log_comb_nonneg'`, inlined (≈10 lines) |
| `P2M/Sol/S_AlgebraicGeometry_locallyOfFinitePresentation_diagonal_of_locallyOfFiniteType.lean` | `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` | Copyright (c) 2024 Christian Merten; Authors: Christian Merten, Andrew Yang | the opening of the proof of `isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange` (the cover `U` and `hU`), adapted (≈8 lines) |
| `P2M/Sol/S_AlgebraicGeometry_exists_ideal_eq_bot_iff_eq_and_map_and_fg_of_locallyOfFiniteType.lean` | `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` | Copyright (c) 2024 Christian Merten; Authors: Christian Merten, Andrew Yang | the same passage of `isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange`, adapted (≈8 lines) |
| `P2M/Sol/S_AlgebraicCurve_TwoChartIntegralModel_mem_chartAlg_image_iff_exists_eq_sum_mul_pow_of_powerBasis_of_isUnit_discr.lean` | `Mathlib/RingTheory/Discriminant.lean` | Copyright (c) 2021 Riccardo Brasca; Authors: Riccardo Brasca | most of the proof of `Algebra.discr_mul_isIntegral_mem_adjoin`, adapted (≈18 lines) |
| `P2M/Sol/S_flt_regular.lean` | `Mathlib/LinearAlgebra/LinearIndependent/Lemmas.lean` | Copyright (c) 2020 Anne Baanen; Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen | the statement and proof of `LinearIndependent.update`, restated as a private lemma (≈15 lines); this file is also listed in §3 |
| `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_isInvertible_of_isInvertible_comap.lean` | `Mathlib/RingTheory/Finiteness/Descent.lean` | Copyright (c) 2026 Christian Merten; Authors: Christian Merten | the map `f` and the range computation from the proof of `Ideal.FG.of_FG_map_of_faithfullyFlat`, adapted to a flat algebra (≈18 lines) |
| `P2M/Sol/S_EisensteinSeries_exists_modularForm_coe_eq_eisensteinG.lean` | `Mathlib/NumberTheory/ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean` | Copyright (c) 2024 Chris Birkbeck; Authors: Chris Birkbeck | the proof of `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF` with its auxiliary norm bound, adapted to this repository's `eisensteinG` (≈15 lines) |
| `P2M/Sol/S_EisensteinSeries_qExpansion_eisensteinG_coeff.lean` | `Mathlib/NumberTheory/ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean` | Copyright (c) 2024 Chris Birkbeck; Authors: Chris Birkbeck | the same proof of `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF`, adapted (≈15 lines) |
| `P2M/Sol/S_EisensteinSeries_exists_modularForm_gamma_apply_eq_tsum_eisSummand.lean` | `Mathlib/NumberTheory/ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean` | Copyright (c) 2024 Chris Birkbeck; Authors: Chris Birkbeck | the same proof of `EisensteinSeries.isBoundedAtImInfty_eisensteinSeriesSIF` with its auxiliary norm bound under another name, adapted (≈13 lines) |

## 5. What we are not certain of

- **Coverage.** The comparison corpus was the set of upstream files present in our working tree (100 files). Upstream files that were never copied into our tree cannot be detected by this method; for those we relied on the pre-publication provenance notes, which name no further Imperial College London or flt-regular files beyond those listed. If further material is recognised, the omission is ours and unintentional.
- **Two headers supplied from upstream.** `Definitions/Def_DedekindDomain_Completion_BaseChange.lean` and `Definitions/Def_DedekindDomain_FiniteAdeleRing_BaseChange.lean` are ports of `FLT/DedekindDomain/Completion/BaseChange.lean` and `FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean` at upstream commit `8387d589441c1097d606ea89370c4165147255d5`; our copies did not retain those two files' notices, so the copyright and author lines given for them in §1 were read from the upstream files at that commit and are reproduced here.
- **Upstream revision.** Our copies record the upstream branch (`main`) and the date (2026-05-21), not a commit hash; one file (`FLT/EllipticCurve/Torsion.lean`) was recorded at commit `7a87d3b25db19d008cd45b29edd2b92803e785b1`, two at `8387d589…` as above.
- **§2 paths and author lists** come from our own May porting notes ("FLT/Basic/FreyPackage.lean … Kevin Buzzard, Ruben Van de Velde, Pietro Monticone"; "FLT/EllipticCurve/Torsion.lean"), as does the notice retained in `Definitions/Def_FLTPrelim_FreyPackage.lean`; apart from the notice of `FLT/EllipticCurve/Torsion.lean`, read from the upstream file at commit `7a87d3b25db19d008cd45b29edd2b92803e785b1` and reproduced in §2, none has been re-checked against the upstream repository.
- **flt-regular per-file headers** are not reproduced in this revision; §3 names the project and its authors instead.
- **Small passages.** Below the thresholds above (a handful of shared lines) we did not attribute systematically; such passages are typically routine instance declarations or one-line lemmas. A few found on review are listed.
~~~~~~~~

-/
