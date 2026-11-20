import ZInQKernel.Contrib.OneProof.Abhyankar.Assembly
import ZInQKernel.Contrib.OneProof.Abhyankar.Transport
import ZInQKernel.Contrib.OneProof.Abhyankar.KummerBase
import ZInQKernel.Contrib.OneProof.Abhyankar.EtaleBranch
import ZInQKernel.Contrib.OneProof.Abhyankar.Descent
import ZInQKernel.Contrib.OneProof.Abhyankar.KummerUnram
import ZInQKernel.Contrib.OneProof.Abhyankar.KummerBranchFinal

/-!
# abhyankar: `SGRDirect.NVLocal.TameBranchNormal` is proved

Task abhyankar (docs/research/abhyankar.md). `TameBranchNormal` (nv-local; `SGRDirectNVLocal.lean:627`) is the
dimension-two case of Abhyankar's lemma in the form "at a closed point of the normalization of a tame Galois cover
of a regular surface germ `R_m`, `m = (f, g)`, ramified only along `fg = 0`, the branch of `f = 0` is unique and
normal". It is proved here with the standard axioms and no new leaf (`tameBranchNormal`), hence so is the glue
field `nvLocalInertia : SGRDirect.NVLocalInertia` of sgr-fold's `OpenGlue8` (`nvLocalInertia`, through nv-local's
`SGRDirect.NVLocal.nvLocalInertia_of_tame`).

The proof goes through the named steps of `Abhyankar/Defs.lean`, all proved:
* `tameBranchNormal_of_local` (Transport): localize at `m`;
* `tbnLocal_of_pieces` (Assembly): the Kummer field `Ω = L(f^{1/N}, g^{1/N})`, `N = [L : K] < p`
  (`exists_kummer_field`, `[Ω : L]` prime to `p`), purity of the branch locus in dimension 2
  (`TPurity3.purityGlobalDim2'`, proved in the chain) applied to the integral closure of `A[t, u]` in `Ω`;
* `kummerBase` (KummerBase): `A[t, u]` is regular local of dimension 2 with maximal ideal `(t, u)`;
* `kummerUnram_of_branch` + `kummerUnramBranch` (KummerUnram, KummerBranch, KummerBranchFinal): the integral
  closure of `A[t, u]` in `Ω` is unramified in codimension one: base change of `L/K` (unramified off `fg = 0`)
  along `A_{P₀} → A[t,u]_P` (`TsKummer.unramBaseChange`), and at `(t)`, `(u)` Abhyankar's lemma for DVRs
  (`HDec.HSyn.t2_proved`, proved in the chain) at `A_(f)`, `A_(g)`, then base change from `A[t]_(t)`;
* `etaleBranch` (EtaleBranch): a finite étale domain over a 2-dimensional regular local ring with maximal ideal
  `(t, u)` has, at each maximal ideal, a unique branch of `t = 0`, and it is a DVR;
* `branchDescent` (Descent): going down for uniqueness; the trace `Tr_{Ω/L}` as a Reynolds operator for
  normality.
-/

set_option linter.all false

noncomputable section

namespace Abhyankar

/-- **`TameBranchNormal` from `KummerUnram`** (compiled). -/
theorem tameBranchNormal_of_kummerUnram (hU : KummerUnram) : SGRDirect.NVLocal.TameBranchNormal :=
  tameBranchNormal_of_local (tbnLocal_of_pieces kummerBase hU etaleBranch branchDescent)

/-- **`NVLocalInertia` from `KummerUnram`** (compiled). -/
theorem nvLocalInertia_of_kummerUnram (hU : KummerUnram) : SGRDirect.NVLocalInertia :=
  SGRDirect.NVLocal.nvLocalInertia_of_tame (tameBranchNormal_of_kummerUnram hU)

/-- **`TameBranchNormal` from `KummerUnramBranch`** (compiled). -/
theorem tameBranchNormal_of_branch (hBr : KummerUnramBranch) : SGRDirect.NVLocal.TameBranchNormal :=
  tameBranchNormal_of_kummerUnram (kummerUnram_of_branch hBr)

/-- **`NVLocalInertia` from `KummerUnramBranch`** (compiled). -/
theorem nvLocalInertia_of_branch (hBr : KummerUnramBranch) : SGRDirect.NVLocalInertia :=
  SGRDirect.NVLocal.nvLocalInertia_of_tame (tameBranchNormal_of_branch hBr)

/-- **`TameBranchNormal` is proved** (standard axioms). -/
theorem tameBranchNormal : SGRDirect.NVLocal.TameBranchNormal :=
  tameBranchNormal_of_branch kummerUnramBranch

/-- **`NVLocalInertia` is proved** (the glue field `nvLocalInertia` of sgr-fold; standard axioms). -/
theorem nvLocalInertia : SGRDirect.NVLocalInertia :=
  SGRDirect.NVLocal.nvLocalInertia_of_tame tameBranchNormal

end Abhyankar
