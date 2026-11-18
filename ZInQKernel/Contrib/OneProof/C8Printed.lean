import ZInQKernel.Contrib.OneProof.C8Dicts
import ZInQKernel.Contrib.OneProof.C8Twist
import ZInQKernel.Contrib.OneProof.C8Poincare

/-! # c8-conrad3, conrad-b3: step C8 from one printed leaf, Conrad's App. B

c8-conrad2's C8 reroute (`C8Poincare.C8Inputs`) had two leaves and three open glue Props. c8-conrad3 proved the three glue
Props (`twistCharHTWt0_proof` in `C8Twist`, `inertiaAtPDecomp_proof` and `minkowskiInertiaQ_proof` in `C8Dicts`).
conrad-b3 replaced the two leaves `conradAppBQp` (Conrad App. B p. 32) and `tateTwistInvariantsInertia` (Tate 1967
§3.3 Thm 2 over the completion of `K^{ur}`, a source the manuscript does not cite) by one leaf:

* `conradAppB` — Conrad, *Lifting global representations with local properties* (author preprint, Dec. 11, 2011),
  App. B, pp. 32-33, base field `ℚ_p`: p. 32 (Hodge–Tate ⇒ locally algebraic, `ConradAppBQp`) and Prop. B.3, p. 33 (the
  Hodge–Tate weight is the exponent, `ConradPropB3Qp`); the manuscript's citation at step C8 (diophantine_zq.tex
  L760-762, bibitem `conrad-local-characters` L11046-11049).

`g12DetPZ_of_printed` is the term for the C8 swap at `g8_g12_of_leaves3_hf_pz_eb` with this leaf only. -/

set_option linter.style.longLine false

noncomputable section

namespace HDec.G0Galois.C8Conrad

/-- **The printed leaf of the C8 reroute** (every glue input of `C8Inputs` is proved). -/
structure C8Leaves : Prop where
  conradAppB : ConradAppB

/-- `C8Inputs` from the leaf (the three glue fields are theorems). -/
theorem c8Inputs_of_leaves (l : C8Leaves) : C8Inputs where
  conradAppB := l.conradAppB
  twistCharHTWt0 := twistCharHTWt0_proof
  inertiaAtPDecomp := inertiaAtPDecomp_proof
  minkowskiInertiaQ := minkowskiInertiaQ_proof

/-- **C8 (the twist has finite image) from Conrad's App. B**, with R13 and R14 (diophantine_zq.tex L758-766). -/
theorem c8TwistFinite_of_printed (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (hC : ConradAppB) : C8TwistFinite :=
  c8TwistFinite_of_conradB hR hHT hC twistCharHTWt0_proof inertiaAtPDecomp_proof minkowskiInertiaQ_proof

/-- **C8's consumer `G12DetPZ` from the printed leaf** (the replacement term at `g8_g12_of_leaves3_hf_pz_eb`:
`g12DetPZ_of_printed r.r14 r.r13 m.c8.conradAppB h9 r.r10`). -/
theorem g12DetPZ_of_printed (hR : HSyn.EigenformRepExists) (hHT : PkgI4.EigenformHT)
    (hC : ConradAppB) (h9 : G9GlueNoT23) (hdR : PkgI4.DeRhamComparison) :
    G12DetPZ :=
  g12DetPZ_of_twistFinite (c8TwistFinite_of_printed hR hHT hC) h9 hdR

end HDec.G0Galois.C8Conrad
