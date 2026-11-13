p='docs/research/h-decomposition.md'; L=open(p).read()
def r(a,b):
    global L
    assert L.count(a)==1,(a[:70],L.count(a)); L=L.replace(a,b)
r("`LeafB3b` (T32's two\n  parts)", "`LeafB3b` (forms of\n  T32's two parts)")
r("| E | new defs (polarizations; medium) | none |", "| C | **yes** (hsyn-fold, from leaf-push): `LeafPush.T09_WeilPairing`, finite level, polarization existentially hidden (consequence) | none |")
r("| E | statable (pkg-I1 I1-f; glue-repo calls it elementary), not drafted: placeholder `HSyn.T29_LocalNormalizers` | none found |",
  "| E | **yes** (leaf-push): `LeafPush.T29a_DivisionNormalizer`, `T29b_SplitNormalizer`; for N5's order every fact A3(a) uses is **proved** (glue-vigneras, `scratch/glue-vigneras/`, not in `Leaves.lean`) | glue-vigneras |")
r("| E | new defs (inertia subgroups of `G_ℚ`; cheap): placeholder `HSyn.T32_TameQuadratic` | none |",
  "| C | **yes** (leaf-push): `LeafPush.T32a_TameQuadratic`, `T32b_QuadraticRamification`, over `inertiaQ` (Mathlib's `inertiaSubgroup`); glue-b3-unram uses its own forms `LeafB3a`, `LeafB3b` plus a new leaf `LeafConj` | none |")
r("| E | new defs (large) | none |\n", "| E | **yes** (leaf-push): `PkgI4.T23_FontaineClosure`, matrix form, `ℚ_p` coefficients (the `E`-coefficient reduction is glue) | none |\n")
r("""after two wording repairs) and proved in Lean modulo the algebra Prop `QuatUnipotentTrivial`;
adopting it would drop R8 (21 research-level leaves). The count below keeps R8 until
`QuatUnipotentTrivial` is proved.""",
"""after two wording repairs) and proved in Lean (hsyn-fold: `QuatUnipotentTrivial` is now proved,
glue-a6-alg, so A6 needs only R6, R7(a), T5). So R8 is needed by no step of the proof any more
and can be dropped (21 research-level leaves); the counts below still list it for comparability
with the first version. Lean (leaf-push): the monodromy form `PkgI2.GrothendieckMonodromy` is now
R8's concrete statement in the bundle (consequence form; `LeafPush.R08_GrothendieckMonodromy` is
the same Prop).""")
open(p,'w').write(L); print('ok')
