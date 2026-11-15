# faltings-cm results log

Base: 43513d873 (leaf-fold25). Fields: `OpenResearchLeaves22.r9a : _root_.PkgI3.FaltingsSemisimple`,
`OpenResearchLeaves22.r9b : _root_.PkgI3.FaltingsTate` (TailZ35.lean L16-17). Definitions: HDecomp/Objects.lean
L423 (`FaltingsSemisimple`), L430 (`FaltingsTate`) (VERIFIED, read).

Setup: worktree lacked `lean/.lake/build` ("unknown module prefix 'ZInQ'"); reflink-copied from ~/dzq (same HEAD
43513d873) (VERIFIED).

## Consumers on the route (Closure.lean, BFS over getUsedConstants from ZInQ.OneProof.frozenTarget)

closure_out.txt (VERIFIED, compiled 1st run): closure constants whose type mentions `PkgI3.FaltingsSemisimple` /
`PkgI3.FaltingsTate`, besides bundle projections/constructors (OpenResearchLeaves2..22, ResearchLeaves3,
G0ModNewform.NewformLeaves):
C9Rhof.{c9_core, rhoF_isSemisimpleModule, rhoF_semisimple}; E1Sub.{homVK_surjective, rhoF_subrep_of_surj,
vSurjOfSurjective}; HDec.G0Galois.{faltingsV, g10Out_of_conjTwist, g8, g8_g11, g8_g12};
HDec.G0ModNewform.{commonConstituent_of_attached, g13, jSide}; HDec.HSyn.{faltingsSemisimple_ofK5,
faltingsTate_ofK5}; PkgI3.{C2_absolutelyIrreducible, E1_exists_hom_ne_zero, exists_hom_ne_zero_of_equivariant,
finrank_equivEnd}.

## Instances (read in source, VERIFIED)

r9a (hS K A ℓ):
- C9.lean L119 `rhoF_semisimple`: hS ℚ Af ℓ, Af = R16's Shimura quotient of J₁(N) over ℚ (via c9_core in
  TailA `commonConstituent_of_attached`, ℓ = 5).
- E1Sub.lean L350 `rhoF_subrep_of_surj`: hS ℚ J ℓ, J = J₁(N) over ℚ (via TailA `jSide`).
- E1Sub.lean L134 `homVK_surjective`: hS ℚ Af ℓ (via vSurjOfSurjective in jSide).
- C2.lean L751 `C2_absolutelyIrreducible`: hS K A ℓ, A the QM model over K (TailA `g8`, ℓ = 5 and 3).
- C2.lean L784 `E1_exists_hom_ne_zero`: hS L' A_{L'} ℓ (TailD `hom_of_common3`, LPrefix L12319).
r9b (hF K A B ℓ):
- `.1` (injectivity): Objects.lean `finrank_equivEnd` (A, A); E1Sub.lean L190 (J, Af) over ℚ.
- `.2` (range = equivariant, used only as `⊇`): Objects.lean L610 `exists_hom_ne_zero_of_equivariant`
  (A_{L'}, J₁(M)_{L'}); `finrank_equivEnd` (A, A) QM model; E1Sub.lean L188 (Af, Af) over ℚ;
  TailB L2057 `faltingsV` via `conjTwistNontrivial_of_*` (A, conjVar A s), QM model.

## Finding 1: no CM reduction (VERIFIED by reading)
The A of AfterG7 (TailA L2977) is `IsQMModel`/`G7Data` of a QM surface P over J(u), u ∈ ℚ \ contactSet,
contactSet = {0,-15,-20,-24,-30,-60} (Hypotheses/Height.lean L84): a general (non-CM) QM surface. J₁(N), Af
are general abelian varieties over ℚ. `hCM : ShimuraMainCM` is used only on the TYZ branch (Main.lean L64-70).
So neither field follows from CM theory.

Closure scan rerun with suffix match (any namespace `*.FaltingsSemisimple`/`*.FaltingsTate`) (VERIFIED, compiled):
only the root `PkgI3.*` constants are in the closure; same consumer list; plus closure defs whose body (not type)
mentions them: `HDec.G0Galois.ConjTwistNontrivial`, `HDec.G0Galois.G10Glue` (they take `hF : FaltingsTate` as a
premise; their proofs `conjTwistNontrivial_of_*` (TailB L2225/L2972) apply `faltingsV` to (A, B) / (A, conjVar A s)).
