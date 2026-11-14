# av-glue results log

Task: the two glue Props under `SimpleImageIsogeny` in `ZInQKernel/Contrib/AVB1/Poincare.lean`:
`ImageFactorization`, `SimpleSurjIsogeny`.

## Part A: SimpleSurjIsogeny (scratch/av-glue/SurjIsog.lean)

- Verbatim copy `AVGlue.SimpleSurjIsogeny`, `simpleSurjIsogeny_iff : ... ↔ ZInQ.Contrib.AVB1.SimpleSurjIsogeny := Iff.rfl` (VERIFIED, compiled).
- `AVGlue.simpleSurjIsogeny_of_leaves (hP : ZInQ.Contrib.AVB1.PoincareComplement) (hQ : IsogenyQuasiInverse) (hK : KernelAbSubvariety) : SimpleSurjIsogeny`
  compiled, axioms [propext, Classical.choice, Quot.sound] (VERIFIED, `lake env lean scratch/av-glue/SurjIsog.lean`, ~10 s after `lake build ZInQKernel.Contrib.AVB1.Poincare`).
- Leaves: PoincareComplement (existing LEAF, av-b1), IsogenyQuasiInverse (existing LEAF text of HSyn.G0RevIsog, ported to PkgI3.AbVar), KernelAbSubvariety (new LEAF: not locally quasi-finite ⇒ positive-dimensional abelian subvariety killed by h).
- Mathlib inputs used: ZMT `IsFinite.of_isProper_of_locallyQuasiFinite`, `isIso_of_isClosedImmersion_of_surjective`, `Scheme.Hom.isDiscrete_preimage_singleton`, `topologicalKrullDim_zero_of_discreteTopology`, `GeometricallyIntegral.isIntegral_of_subsingleton`.

## Part B: ImageFactorization (scratch/av-glue/ImageFact.lean)

- Verbatim copy `AVGlue.ImageFactorization`, `imageFactorization_iff : ... ↔ ZInQ.Contrib.AVB1.ImageFactorization := Iff.rfl` (VERIFIED, compiled).
- `AVGlue.imageFactorization_of_cartier (hC : CartierSmooth) : ImageFactorization` compiled, axioms [propext, Classical.choice, Quot.sound] (VERIFIED).
- Only leaf: `CartierSmooth` (group scheme loc. finite type over a char-0 field is smooth; Cartier 1962 / Oort 1966 / Mumford §11; locators UNVERIFIED).
- Construction: B = Mathlib's scheme-theoretic image `f.left.image` over k; group law by `grpObjOfMono` (closure under μ, η, inverse from `IsSchemeTheoreticallyDominant` of `A×A → f(A)×f(A)`, Mathlib's flat-base-change lemma `IsSchemeTheoreticallyDominant.of_isPullback`, and `IsClosedImmersion.lift`); `ker toImage = ⊥` proved; proper (closed immersion into proper); smooth by Cartier; geometrically connected (base change of the surjective `A → f(A)`); geometrically integral by vendored Tau Ceti `Smooth.geometricallyIntegral`; `A → f(A)` surjective (proper + dominant).
