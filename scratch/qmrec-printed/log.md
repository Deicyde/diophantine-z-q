# qmrec-printed results log

* 05:20 Start. Base 838a7430 (shimura-split2). Build tree copied from ~/dzq-wt/shimura-split2 (.lake/build, lean/.lake/build).
* 05:40 Kernel's existing CM statements checked (VERIFIED, read):
  - `G0Split.FibreQM.PeriodMapH.QMSplitSTQM.ShimuraTaniyamaQbar` (TailU.lean:1603): "CM abelian surfaces over ℂ are
    defined over ℚ̄" — not the main theorem of CM (no Galois action, no reflex norm).
  - `ShimuraMainCM` (Contrib/OneProof/RingClassLattice.lean:911): main theorem of CM for elliptic curves (Shimura 1971
    Thm 5.4, Weierstrass coordinates) — dimension 1 only; no bridge to the QM surfaces T(z,g).
  So neither is the printed main theorem for an abelian variety with CM by a CM field; a new leaf is needed.
* 06:10 `scratch/qmrec-printed/Defs.lean`: leaf `MainTheoremCM` (Shimura's adelic main theorem of CM, any CM type,
  reflex field = Subfield.closure of type traces, reflex norm = det_E on a model V with V ⊗_{E*} ℂ ≅ ℂ^Φ, Tau Ceti Artin
  map, torsion via 𝔞̂ = ℤ̂-span of 𝔞 in 𝔸_f ⊗ E). Compiles. VERIFIED.
* 06:30 §A of Main.lean (E = K(√2) = AdjoinRoot, NumberField instance, √2 ∉ K, basis 1, √2, embeddings φ₁, φ₂
  extending κ) compiles. VERIFIED.
* (actual clock) 05:55 §B–§E compile: reflex field = κ(K) (`reflex_eq`), Φ a CM type (`type_inj`), model V = E with
  N_Φ*(s) = image of s under 𝔸_{K,f} → 𝔸_f ⊗ E (`reflexNorm_rhoK`); β : E ≅ B with ι(β e)(z,1)ᵀ = (z φ₁ e, φ₂ e)
  (`vec_beta`); ℤ̂ L_h = 𝒪̂ h⁻¹ (`lg`), approximation (`exists_approx`), β̂ : 𝔸_f ⊗ E ↪ B ⊗ 𝔸_f with
  𝔞̂ = β̂⁻¹(𝒪̂ h⁻¹) (`mem_latHat_iff`) and β̂(N(s) w) = β̂(w) q̂(s) (`betaHat_inclA_mul`). VERIFIED (compiled).
* 06:04 **`qmReciprocityL3_of_printed : MainTheoremCM → HomLatticeCorr → QMReciprocityL3`** compiles with no sorry;
  `#print axioms` = [propext, Classical.choice, Quot.sound]. VERIFIED. (ι-compatibility of θ' from HomLinearLift +
  agreement on torsion + ∩ N L = 0; level structure from the torsion clause + approximation.)
* 06:20 Added `[IsCMField E]` to the leaf (fidelity: the print is for CM fields); proved `isCMField_EK` via Mathlib's
  `IsCMField.ofCMExtension` with F = ℚ(√2) totally real. Main.lean recompiles, axioms standard. VERIFIED.
* 06:20 Independent model review of `MainTheoremCM` launched (adversarial, no Lean).
