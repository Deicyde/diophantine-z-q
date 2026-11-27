# The Colmez row over Colmez's own `B_dR`

This note covers `Algebra.lean`, `RowPrinted.lean` and `Check2.lean`. It complements `README.md` in
this directory.

## What is proved

**ℤ_p-structures** (`Algebra.lean`). Colmez's rings get their `ℤ_p = W(F_p)`-structure through
`W(F_p) → W(R)`:

* `colmezZpToW : ℤ_[p] →+* W(ColmezR 𝓞_ℂ_[p] p)` is
  `(WittVector.map (ZMod.castHom _ _)).comp (WittVector.equiv p).symm`, the same recipe as the tree's
  `zpToW`. `wittEquiv_colmezZpToW : wittEquiv (colmezZpToW p z) = zpToW p z` is proved by
  `RingHom.ext_zmod`.
* `Printed.algZpPlus` is a scoped instance: the `ℤ_p`-algebra structure on
  `ColmezBdRPlus 𝓞_ℂ_[p] p` through `ℤ_p → W(R) → W(R)[1/p] → B⁺_dR`. Its fraction field inherits a
  `ℤ_p`-algebra structure.
* `colmezBdRPlusEquiv_algebraMap_zp`: `colmezBdRPlusEquiv` sends `z` to `ofLoc p (zpToW p z)`.
  `colmezBdRPlusAlgEquiv` is the same map as an isomorphism of `ℤ_p`-algebras, with the tree's
  structure `algZpTree` on `BDeRhamPlus`.
* **`colmezBdRAlgEquiv : FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ≃ₐ[ℤ_[p]] BdR p`** is
  `colmezBdREquiv` as an isomorphism of `ℤ_p`-algebras. On the tree side it uses the structure
  `Tp.algZp` (through `qpToBdR`), which is the one the `T_p` row uses.
* `colmezThetaPlus_algebraMap_zp`: `colmezThetaPlus (z) = (z : ℚ_p) ∈ ℂ_p`. The proof uses
  `ringHom_ext_padicInt`: two ring maps out of `ℤ_p` into a `p`-adically separated ring agree.
* `ker_awayEquivCp_comp_colmezThetaInvertP`: reading `θ[1/p]` in `ℂ_p` through `awayEquivCp` does not
  change its kernel. So `ColmezBdRPlus` is the printed `lim← W(R)[p^{-1}]/(Ker θ)^n` with
  `θ : W(R)[p^{-1}] → C_p`.

**Filtration** (`RowPrinted.lean`). `colmezBdREquiv_mem_filB_zero_iff`:
`colmezBdREquiv p y ∈ filB p 0 ↔ ∃ b : ColmezBdRPlus 𝓞_ℂ_[p] p, algebraMap _ _ b = y`.

**The row over Colmez's rings** (`RowPrinted.lean`). `Colmez1992DeRhamAbVarPrinted` has:

* `P ω : TCp p A →ₗ[ℤ_[p]] FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p)`;
* values in Colmez's `B⁺_dR`;
* `P ω (galTCp p A σ u) = colmezBdRAct p (gfToGqp p F σ) (P ω u)`;
* non-degeneracy on `FractionRing (ColmezBdRPlus 𝓞_ℂ_[p] p) ⊗[ℤ_[p]] TCp p A`.

It is proved equivalent to the existing rows:

* `colmez1992DeRhamAbVarPrinted_iff_tp : Colmez1992DeRhamAbVarPrinted ↔ Colmez1992DeRhamAbVarTp`,
  via `shapeB_iff`. That is the transport of the row's shape along `colmezBdRAlgEquiv`, using the
  intertwining `colmezBdREquiv_act` and the filtration lemma.
* `colmez1992DeRhamAbVar_iff_printed : Colmez1992DeRhamAbVar ↔ Colmez1992DeRhamAbVarPrinted`, and
  `colmez1992DeRhamAbVar_of_printed`.

The row inherits the weakenings of `Colmez1992DeRhamAbVarCp`:

* `H¹_dR(X)` is an existential type;
* bilinearity in `ω` is dropped;
* the `Fil¹` clause and (iii) are dropped.

`Check2.lean` prints `#print axioms` for every declaration added here.

## Not formalized: the proper model (Colmez, p. 638)

Since #239 (`ColmezProperModel/`) the points identification below is a Lean theorem
(`modelPtsEquiv`, `modelPtsEquiv_gal`), and `properModelPoints_iff` proves
`ProperModelPoints ↔ ProperModelExists`; only the existence of a proper model remains
(`ColmezProperModel/README.md`). The rest of this section is the note as written at #235.

Colmez fixes a proper model `𝒳` of `X` over `O_K` and writes `u_n ∈ 𝒳(O_{C_p})`, using "Par
construction, 𝒳(O_{C_p}) s'identifie à X(C_p)" (p. 638). The theorem's statement depends only on
`X(C_p)` and its Galois action, and the proof shows the pairing does not depend on `𝒳` (p. 640). The
Lean rows build `T_p` from `A(ℂ_p)` (`TCp`). The step from `𝒳(O_{C_p})` to `X(C_p)` is therefore
the one remaining presupposition. It is not formalized here; it is proposed for a ruling by Jack or
the maintainer.

The following Lean statement would discharge it. It is schematic and not compiled. Here
`O_F := integralClosure ℤ_[p] F`, with `F` a `ℤ_p`-algebra through `ℚ_p`, and `ι : O_F →+* 𝓞_ℂ_[p]`
is the restriction of `algCp`.

```lean
def ProperModelPoints : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (𝒳 : Scheme) (π : 𝒳 ⟶ Spec (CommRingCat.of O_F)) (_ : IsProper π)
      -- the generic fibre of 𝒳 is A, as F-schemes
      (e : pullback π (Spec.map (CommRingCat.ofHom (algebraMap O_F F))) ≅ A.X.left)
      (he : e.hom ≫ A.X.hom = pullback.snd _ _),
      -- 𝒳(O_{C_p}) := {x : Spec 𝓞_ℂ_p ⟶ 𝒳 | x ≫ π = Spec.map ι}
      ∃ φ : {x : Spec (CommRingCat.of 𝓞_ℂ_[p]) ⟶ 𝒳 //
              x ≫ π = Spec.map (CommRingCat.ofHom ι)} ≃ A.Pt ℂ_[p],
        -- G_F-equivariant, σ acting on 𝒳(O_{C_p}) by x ↦ Spec.map (oAct (gfToGqp p F σ)) ≫ x
        ∀ σ x, φ (σ • x) = A.galAct (cpGal p F σ) (φ x)
```

Given `ProperModelPoints`, `φ` identifies `lim 𝒳(O_{C_p})[pⁿ]` with `TCp p A`, `G_F`-equivariantly.
The rows above are stated on `TCp p A`, so they become statements on Colmez's
`T_p(X) = lim 𝒳(O_{C_p})[pⁿ]` with no further reading step. One input is in neither the tree nor
Mathlib, and one is in Mathlib but not yet applied:

* existence of a proper model, for instance the closure of `A` in a projective embedding over `O_F`
  (this also needs the projectivity of `A`);
* the valuative criterion of properness is in Mathlib (`AlgebraicGeometry.IsProper.eq_valuativeCriterion`,
  Stacks 0BX5, for any valuation ring). Applying it to `𝓞_ℂ_[p] → ℂ_[p]` (the `ValuationRing` and
  `IsFractionRing` instances, and the identification with `A.Pt ℂ_[p]`) is not done. It makes
  `𝒳(O_{C_p}) → 𝒳(C_p) = A(C_p)` a bijection.

The group law on `𝒳(O_{C_p})` is transported from `A(ℂ_p)` along this bijection.
