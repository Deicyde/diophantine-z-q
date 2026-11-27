# bst-regular: status

**Proved targets: all three, but each is conditional on two open Props.** The Props are `BstFracInvariants` (step
(c), `(Frac B_st)^{G_K} ⊆ B_st`) and `BstLineUnits` (step (d), `G_K`-stable `ℚ_p`-lines of `B_st` are spanned by
units). The tree does not prove either one. **No count change:** this task retires no frozen field and edits no
existing file.

- Target 1: `HDec.PkgI4.BstRegular.isAdmissibleT_of_isAdmissible : BstFracInvariants → BstLineUnits → ∀ K [FiniteDimensional ℚ_[p] K] h w hw (hgen) ρ, IsAdmissible p (BstFOf p h w hw) K.fixingSubgroup ρ → IsAdmissibleT p (BstFOf p h w hw) K.fixingSubgroup ρ`
- Target 2: `isPstFBasis_iff_isPstF` and `localIsPstFBasis_iff_localIsPstF`. Both take the same two Props, plus `hgen : ker θ = (w)`.
- Target 3: `colmezThm01_iff_bergerSurveyF : BstFracInvariants → BstLineUnits → (ColmezThm01 ↔ BergerSurveyF)`. The forward direction needs neither Prop.
- Unconditional: (a) `isAdmissibleT_of_isAdmissible_of_regular`. For any `H`-regular `B ⊆ B_dR` (`IsRegularB`), the dimension form implies the basis form. (b) `isDomain_sub`: every `ℚ_p`-subalgebra of `B_dR` is a domain.
- `#print axioms` for all of the above: `[propext, Classical.choice, Quot.sound]`.

**What compiles:** `lake build ZInQKernel.Contrib.OneProof.BstRegular.Abstract` and
`lake build ZInQKernel.Contrib.OneProof.BstRegular.Bst` both succeed. There is no sorry and no axiom.

**What remains** (details in `docs/research/bst-regular.md` §4):
- (c) needs three things. c1: an element form of `B_dR^{G_K} = K`. It is implicit in the bdr-inv proof but not
  exported. c2: Fontaine's injectivity of `K ⊗_{K_0} B_st → B_dR`. This is deep: the tree has no Frobenius on
  `B_cris`. c3: `K_0 ⊆ B_st`, of which only partial pieces exist.
- (d) needs two things. d1: a degree argument in `X = log [p̃]`, which needs c1 and c2 at general `K`. d2: lines in
  `B_cris` are units. This is deep: it needs Frobenius, the fundamental exact sequence, and Sen's theorem.
- Printed source for (c) and (d): Fontaine, Astérisque 223, Exp. II/III ("`B_st` is `G_K`-regular"). Locator
  UNVERIFIED.

Last content commit: 96ce6391f1354a9058342701174ce15e15f21c5d. This file is committed on top of it.
