# HeightModelM2: the two GR1 argument steps as Lean theorems

The fidelity reading of the rows `GaudronRemondThm14GR1` and `GaudronRemondSec9LowerGR1`
recorded two steps as non-blocking but not Lean theorems. Both are proved here.

1. **Commutativity** (`Commutative.lean`, from `Separated.lean`). `groupModel_isCommMonObj`:
   every `GroupModel A L` is a commutative group object. Morphisms out of a flat scheme into a
   separated one are determined on the generic fibre (`ext_of_flat_of_generic`), and the generic
   fibre `A_L` is commutative. `groupModel_commutator_eq_one`: the commutator morphism is the
   constant unit morphism. `isSemiAbelianModel_iff_and_comm`: adding commutativity to
   `IsSemiAbelianModel` changes nothing.
2. **Stalks and global sections** (`GlobalSections.lean`, `GlobalDet.lean`, `Arith.lean`).
   Sections of `e*Ω¹` over opens of `Spec 𝓞_L` are built from Kähler differentials of opens of
   the model; global sections are the elements that are sections near every point.
   `globalOmega_eq`: the global sections of `e*Ω¹` are the intersection of the stalks, so the
   tree's `printedOmega` is `Γ(S, e*Ω¹)` (`printedOmega_eq_comap_globalOmega`).
   `globalDetLattice_eq`: the global sections of `ε*Ω^g = ⋀^g e*Ω¹` are `printedDetLattice`.
3. **Wiring** (`GR1Rows.lean`). `IsGR1StableHeightGlobal` asks for a commutative semi-abelian
   model and takes the lattice of global sections. `isGR1StableHeightGlobal_iff`: it is
   `IsGR1StableHeightOriginal`. The rows over it are equivalent to the current rows
   (`gaudronRemondThm14GR1Global_iff`, `gaudronRemondSec9LowerGR1Global_iff`,
   `gaudronRemondSec9LowerGR1WeakGlobal_iff`).

`Check.lean` prints the axioms of the main theorems.

Readings left here (not Lean theorems in this directory; `HeightModelM3` and `HeightModelM4` have
since proved them, item 2 for `g ≥ 1`, up to the one definitional reading in
`HeightModelM4/README.md`):
1. The sections are taken in the generic fibre, i.e. of the image of `e*Ω¹` there. For a smooth
   model `e*Ω¹` is locally free, so this is `e*Ω¹` itself.
2. `secOmega`, `detSec` and `printedOmegaAt` are `𝓞_L`-spans. The sections of the sheaf are
   `𝒪_S(V)`-modules. The two agree because the generators `c|_η·(1⊗d(b|_ξ))` already range over
   all `c ∈ 𝒪_S(V)`, so the span is `𝒪_S(V)`-stable, and `c·(v₁∧…∧v_g) = (c v₁)∧…∧v_g`.
3. `detSec` wedges sections of `e*Ω¹` lying in the image of `θ : 𝔪_ξ/𝔪_ξ² → (e*Ω¹)_η`. This is all
   of `(e*Ω¹)_η` because `θ` is also surjective (conormal sequence; `Ω_{L/𝓞_L} = 0`). The tree
   proves `theta_injective`, and `HeightModelM3` proves `theta_surjective`
   (`HeightModelM3/Theta.lean`).
