# htnew-det log

Base c7fbc273 (wip/leaf-fold33b); `git merge origin/main`: already up to date. Build tree copied from
~/dzq-wt/leaf-fold33b (same commit, byte-identical Main.lean).

## Findings (read in the tree; VERIFIED unless marked)
- r13 := HodgeLF7.eigenformHT (eigenformHT_of_kato_ds r.eigenformHTNew ...) at TailX l.198; consumers of r13: only
  g12 / g12_pz (TailA l.2211, PicZeroCharZeroCopy l.72) via g8_g12, which pass hR13 to G12Weight (TailA l.2059).
- G12Weight (TailA l.2059) is a general implication (R14 → R13 → R15 → T18 → T19 → ∀ r g k ψ ...), with no abelian
  variety in it; g12 calls it with Pan∘Berger's (k, g, ψ) BEFORE using G12Det; ψ is an arbitrary continuous
  GaloisChar 5 (PanFor, LPrefix l.2252); finiteness of ψ is derived afterwards by GlueAssembly.twist_finite, which
  needs k = 2 (G12Det is stated at weight 2).
- Pan's printed conclusion (locators.md R12): "cuspidal eigenform up to twist"; no weight/twist control.
- So the determinant argument is circular: needs ψ finite to get k = 2, and k = 2 to get ψ finite.

## Lean: ZInQKernel/Contrib/OneProof/HTNewDet.lean (lake env lean: OK, no errors, no warnings)
- twist_sq_mul_cyc_finite: weight-k determinant data ⇒ ψ²χ^{k−2} finite image (generalizes twist_finite).
- det_data_weight_shift: r = εχ^{k−1}ψ² ⇒ r = εχ^{k+2m−1}(ψχ^{−m})².
- twist_shift_not_finite: ψ finite, χ^m infinite ⇒ ψχ^{−m} infinite.
- charpoly_smul_fin_two, frobPoly_weight_shift: DS 9.6.5 polynomial X²−a_qX+e q^{k−1} for ρ ⇒ X²−q^m a_q X+e q^{k+2m−1}
  for q^m ρ (θ^m-twist).
- traceTwist_weight_shift: Pan's trace form invariant under (ψ, a) ↦ (ψχ^{−m}, χ^m a).
- NoHighWeightTwist5 (def, GLUE, not printed form), G12WeightNoR13 (def),
  g12Weight_of_noR13, g12WeightNoR13_of (from SenTwist, FiniteImageHT, NoHighWeightTwist5 + proved glue),
  g12Weight_of_noHighWeight, noHighWeightTwist5_of_g12Weight (implied by the r13 route).
