# General-level modular curve model and O.7 reduction

`X0Model3.exists_stabilizer_germ_match` proves the exact comparison
left open by the previous model. Equal valuative points have local
overlap in an étale coordinate on the smooth normalization. Proper
discontinuity and the analytic identity principle turn this into
agreement of the punctured second-coordinate germs after an element of
the center stabilizer. Consequently `X0Model3.complexPoint_eq_iff`
classifies the fibres by Γ₀(N), and `X0Model3.model N` is the complete
`PreparedParam.X0Model N` at every nonzero level. The port comes from
the comparison already used by the fixed-scale parametrization.

`Specialize.lean` identifies the reduction of the rational
parametrization on each chosen CM conjugate with the precise
`StageKummer.reduceDatum` value, given the chosen source point at the
datum's embedding. It proves the specialization square when the
integral diagram is available. For `hπ` the remaining ELLIOT input is
the identification of the PM quotient's values with the specialization
of that fixed rational map on the actual coarse CM reductions at the
detector's place (tex 8476–8479, used at 9283–9291). The alignment of the
source reductions with the reference labels is separate (tex
9265–9279). No print was added.

All five modules build serially; the 35 axiom checks report only
`propext`, `Classical.choice` and `Quot.sound`. The exact boundary
and build results are in `docs/research/rc-x0-model-3.md` and
`scratch/rc-x0-model-3/log.md`.

Inherited citation issues: Jetchev–Kane as cited at tex 8468–8474
omits level one; the Milne locators at tex 1784–1788 do not supply the
normalized newform or the Hecke identity. Neither is used to prove
the normalized branch comparison.

Final implementation and report SHA:
`c883c89b274ef80d02cf5df96b821e36ede7927d`.
The final handoff commit's SHA is returned by
`git log -1 --format=%H -- .fleet/rc-x0-model-3.md`;
the commit cannot record its own SHA.
