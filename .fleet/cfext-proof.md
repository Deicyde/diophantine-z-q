# cfext-proof (2026-11-17): done — field proved outright

**Verdict.** `JavanpeykarRebase.ConstantFieldExtensionUnramifiedFinite` (Stichtenoth 3.6.3(a), finite constant
field extension unramified; research field `constantFieldExtensionUnramifiedFinite`, strict GLUE) is **proved
from Mathlib alone**, statement unchanged, no new leaf: `CFExtProof.constantFieldExtensionUnramifiedFinite_proof`.

**What compiles (VERIFIED).**
* `scratch/cfext-proof/CFExt.lean`: verbatim copy of the def + proof, `import Mathlib`, axioms standard.
* `ZInQKernel/Contrib/OneProof/ConstantFieldExtensionUnramifiedFinite.lean` (new file, targeted Mathlib imports):
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.ConstantFieldExtensionUnramifiedFinite`
  succeeds; `#discharges`: discharges `OpenResearchLeaves38.constantFieldExtensionUnramifiedFinite`,
  `still assumes: []`, axioms [propext, Classical.choice, Quot.sound].
* `scratch/cfext-proof/autofold.json`; `autofold.py --dry-run`: strict 16/18 on 34 → 16/17 on 33 (strictest
  16/18 → 16/17); the generated `sixContactMin_of_open56` module compiles with standard axioms.

**Proof.** O ⊗_K L is formally unramified over O = w ∩ F (separable L/K); Mathlib's
`FormallyUnramified.map_maximalIdeal` at p = m_w ∩ (O ⊗ L) gives s·a = π·b for a ∈ p; x = ι c·φ a by
surjectivity of F ⊗ L → FL; trdeg F/K = 1 and π transcendental (full constant field) give π^m ∈ dO for d ∈ O∖0;
iterating (c,a,s) ↦ (cπ,b,ss') reaches c ∈ πO. Only surjectivity of the tensor map is used.

**Remains.** Lead: run the fold (`autofold.py scratch/cfext-proof/autofold.json`, no `--allow-rise`) and the
usual post-fold checks. Report: docs/research/cfext-proof.md.
