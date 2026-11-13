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

## 2. NeronModelMinimal reduced to one glue `HeightAntitone` (compiled 02:00, scratch/h5-glue/Minimal.lean)
- `isMonHom_of_map` (general: a strong monoidal F injective on Hom(𝟙,Y), Hom(X⊗X,Y) reflects
  IsMonHom): compiled.
- `neron_lift_isMonHom`: the Néron comparison map 𝒢 → 𝒩 is IsMonHom and its generic fibre
  F.map f is an iso: compiled.
- `HeightAntitone` (glue, STATED): f : 𝒢.G ⟶ 𝒩.G, IsMonHom f, IsIso (F.map f) ⇒ 𝒩.height ≤ 𝒢.height.
- `neronModelMinimal_of_heightAntitone : HeightAntitone → NeronModelMinimal`: compiled.
  All three #print axioms: [propext, Classical.choice, Quot.sound].

## 3. Open subgroup models are generic isomorphisms — PROVED (compiled 02:12, scratch/h5-glue/OpenSub.lean)
- `isOpenImmersion_pullback_map`: Over.pullback j sends open immersions to open immersions
  (IsPullback.of_bot pasting + MorphismProperty.of_isPullback).
- `isIso_of_openImmersion_self`: an open immersion B.X ⟶ B.X over Spec L of an AbVar is an iso
  (universally closed via proper + separated; image clopen nonempty in the irreducible B.X —
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton; isIso_iff_isOpenImmersion_and_surjective).
- `genericIso_of_openImmersion`: f : 𝒰.G ⟶ 𝒢.G with f.left an open immersion ⇒ IsIso (F.map f).
  All three: axioms [propext, Classical.choice, Quot.sound]. This is the "on generic fibres it is an
  isomorphism" clause of h5-neron's OpenSubgroupHeight docstring, now a Lean proof.
