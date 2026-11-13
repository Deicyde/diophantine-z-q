# h5-glue results log

Base: wip/h5-glue at 883c4ddf, merged origin/wip/h5-neron (b7c1dc21) for scratch/h5-neron and
docs/research/h5-neron.md.

## 1. Glue H4b `GroupModelBaseChangeExists` — PROVED (compiled 01:51, scratch/h5-glue/BaseChange.lean)
- `genBC` (generic-fibre identification of a base change, for abstract morphisms
  a,b,c,d,k,k' with a≫b = c≫d, c≫k = k') and `genBC_isMonHom` (it is a monoid morphism):
  compiled, axioms [propext, Classical.choice, Quot.sound].
- `GroupModel.baseChange L L' 𝒢 : GroupModel A L'` and `groupModelBaseChangeExists :
  GroupModelBaseChangeExists` (statement copied verbatim from h5-neron): compiled, axioms
  [propext, Classical.choice, Quot.sound]. Whole file ~7 s elaboration.
- FINDING: h5-neron's kernel deterministic timeout disappears when the IsMonHom proof is done
  over abstract morphisms and instantiated afterwards (the kernel never unfolds the concrete
  Spec.map/algebraMap (𝓞 L) L terms).
