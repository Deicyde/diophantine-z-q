# ColmezTorsionIso: `A[p^n](F̄) ≅ A[p^n](C_p)`, `G_F`-equivariantly

The lead's LEAF path for what was, until y3-colmez-1127 (`ZInQKernel/OneProof/H/TailZ113.lean`),
the open hypothesis `colmez1992DeRhamAbVar`
(`HDec.HSyn.OpenAddedLeaves30.colmez1992DeRhamAbVar`, statement
`DeRhamScholze.TatePrints.Colmez1992DeRhamAbVar` in `TatePrints/Rows.lean`), from the row flag (as
it stood at #228) in `docs/one-proof/kinds.tsv`: "a named Lean theorem identifying A[p^n](F̄) with
A[p^n](C_p), G_F-equivariantly, with the model step ruled". This is the readers' non-blocking point
(1) in `docs/research/tate-prints-adversarial-readings.md`, now a Lean theorem.

Add-only. Imports: `G9/Galois.lean`, `AbVarBC/Main.lean` (`Basic`, `Shape`), and
`TatePrints/Rows.lean` (`Row` only). No new hypothesis; its axioms are not separately recorded.

## The setting in the tree

* The row's abelian variety is `A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F` (`G9/I4Layer.lean`): a
  commutative group scheme over `Spec F`, proper, smooth, geometrically integral, for an abstract
  finite extension `F/ℚ_p`. There is no integral model.
* `A.T p = Tate.T p (Additive (A.Pt (AlgebraicClosure F)))` (`G9/I4Layer.lean`, `AbVar.T`): the
  inverse limit of the `p^n`-torsion of the `F̄`-points, `F̄ = AlgebraicClosure F`; `A.V p` is
  `ℚ_p ⊗ A.T p`, and `A.galRep p` lets `σ ∈ G_F` act on coordinates.
* `G_F` acts on `B_dR` through `gfToGqp p F : G_F → G_{ℚ_p}`, restriction along the isomorphism
  `embF : ℚ̄_p ≃ F̄` (`G9.embF_gfToGqp`, `G9.embF_bijective`); `phiF : F → ℚ̄_p` and
  `F' = fieldF p F` are the corresponding copy of `F` in `ℚ̄_p`.

## The model step

* Colmez's `K` is `F` and his `X` is `A`. His identification `𝒳(O_{C_p}) = X(C_p)` for a proper
  model `𝒳` over `O_K` (p. 638, "Par construction") is a Lean theorem since #239
  (`ColmezProperModel.modelPtsEquiv`, `modelPtsEquiv_gal`). The model step reduces to the existence
  of such a model for every `A` (`ColmezProperModel.ProperModelExists`), which the tree derives
  from Milne's Theorem 7.1 (`ColmezProperModel.properModelExists_of_milne`), the row
  `milneThm71Projective` since y3-colmez-1127 (see What remains). The
  row's Lean form uses only `X(C_p)` and its Galois action, both read off `A` over `F`; as printed,
  5.2(i) builds the limit from `F_ω(a_n)`, which goes through the model.
* `C_p` is an `F`-algebra through `F → ℚ̄_p ⊂ C_p`, `y ↦ phiF y` (`algCp`, a local instance only),
  whose image is the tree's `F'`. The embedding `F̄ → C_p` is `x ↦ embF⁻¹ x` (`iotaFbar`), the
  same isomorphism `ℚ̄_p ≃ F̄` that defines `gfToGqp`; it is an `F`-algebra map.
* `σ ∈ G_F` acts on `C_p` by `cpAct (gfToGqp σ)` (`cpGal`), the continuous extension of `σ`, which
  is the action the row uses on `B_dR` (`bdrAct (gfToGqp σ)`); `iotaFbar` is `G_F`-equivariant
  (`iotaFbar_galF`). On points, `G_F` acts on coordinates (`galAct`).

## Statements (namespace `ZInQ.Contrib.ColmezTorsionIso`)

`Basic.lean`:

* `exists_extPt_eq_of_pow`: for a kernel abelian variety `B` over a field `K` of characteristic
  `0`, a `K`-embedding `κ : Ω → Ω₂` with `Ω` algebraically closed, and `N ≠ 0`, every `q ∈ B(Ω₂)`
  with `q ^ N = 1` is `extPt κ x` for some `x ∈ B(Ω)`. Proof: `[N]` is finite (the tree's proved
  `AbVarBC.mulIsogeny`), so `q` is a point of the finite `K`-scheme `B[N]`, whose `Ω₂`-points have
  coordinates integral over `K`, hence in `κ(Ω)` (`AbVarBC.exists_lift_of_isFinite`).
* `extCp p A : A.Pt (AlgebraicClosure F) →* A.Pt ℂ_[p]`, the natural map `P ↦ P ∘ Spec(ι)`;
  `extCp_injective` (any field extension), `extCp_surj_torsion` (on `N`-torsion, `N ≠ 0`),
  `extCp_galAct` (`extCp (σ • x) = cpGal σ • extCp x`).
* `torsCp p A N hN : tors (Additive A(F̄)) N ≃+ tors (Additive A(ℂ_p)) N`, with `torsCp_apply`
  (it is `extCp`) and `torsCp_galAct` (`G_F`-equivariance).
* **`torsion_iso`**: for `N ≠ 0`, the natural map `A[N](F̄) → A[N](ℂ_p)` is bijective, additive,
  and commutes with `G_F`; `torsion_iso_pow` is the case `N = p^n`.
* `TCp p A = Tate.T p (Additive A(ℂ_p))`, `VCp p A = ℚ_p ⊗ TCp p A`, `galRepCp p A` (Colmez's
  `T_p(X)`, `V_p(X)` and Galois action); `tateCp p A : A.T p ≃ₗ[ℤ_p] TCp p A` with `tateCp_galT`;
  `vCp p A : A.V p ≃ₗ[ℚ_p] VCp p A` with **`vCp_galRep`**:
  `vCp (A.galRep p σ v) = galRepCp p A σ (vCp v)`.

`Shape.lean`: `ColmezShape p F Q ρ` (the row's conclusion for a representation `ρ`, with `B_dR⁺`
abstracted as `Q`), `colmezShape_transfer` (invariance under a `G_F`-equivariant linear
isomorphism), `colmezShape_iff_cp`.

`Row.lean` (namespace `DeRhamScholze.TatePrints.ColmezCp`):

* `Colmez1992DeRhamAbVarCp : Prop`: the row word for word, with `A.V p`, `A.galRep p` replaced by
  `VCp p A`, `galRepCp p A` (`T_p` from the `C_p`-points, as printed on pp. 638-639).
* **`colmez1992DeRhamAbVar_iff_cp : Colmez1992DeRhamAbVar ↔ Colmez1992DeRhamAbVarCp`**, and
  `colmez1992DeRhamAbVar_of_cp : Colmez1992DeRhamAbVarCp → Colmez1992DeRhamAbVar`.

## What remains for the lead

y3-colmez-1127 (`ZInQKernel/OneProof/H/TailZ113.lean`) replaced the row by `milneThm71Projective`
(Milne's Theorem 7.1; `properModelExists_of_milne` gives `ProperModelExists` from it) and
`colmez1992DeRhamAbVarModel` (Théorème 5.2 with `T_p(X) = lim 𝒳(O_{C_p})[pⁿ]`);
`ColmezProperModel.colmez1992DeRhamAbVar_of_model_milne` proves the row from them, through
`colmez1992DeRhamAbVar_iff_cp`. The points below are as written after #239.

* The identification of the two Tate modules is now a Lean theorem, so the reading step of the
  ruling is gone: `Colmez1992DeRhamAbVarCp` states Théorème 5.2 (i)-(ii) with Colmez's own
  `T_p(X)`, and the row follows from it by `colmez1992DeRhamAbVar_of_cp`. If the lead accepts
  this, the row can be re-rated against `Colmez1992DeRhamAbVarCp` (a fidelity reading of the new
  statement against p. 639 is needed; it differs from the read row only in `T_p` and its action).
* A ruling by Jack or the maintainer on the model step, proposed and not given
  (`docs/one-proof/kinds.tsv` lists it as open, and `docs/one-proof/STATEMENT-CHECKS.md` leaves
  count verdicts to them). Since #239 Colmez's `𝒳(O_{C_p}) = X(C_p)` for a proper model over
  `O_K` (p. 638) is a Lean theorem (`ColmezProperModel.modelPtsEquiv`, `modelPtsEquiv_gal`, through
  Mathlib's valuative criterion), and the step reduces to `ProperModelExists`, a proper model with
  generic fibre `A` for every `A` (`properModelPoints_iff`). That is in neither the tree nor
  Mathlib: it needs the projectivity of abelian varieties (`ColmezProperModel/README.md`); the print
  takes a model as given, pp. 629 and 638. The ruling, or a Lean proof, is on `ProperModelExists`.
* The readers' non-blocking points (2) (`ℤ_p`-linearity in `u`) and (3) (dropped clauses) are
  unchanged.
* The ledgers (`kinds.tsv`, `reviews.tsv`, the open list) are not edited here (add-only).
