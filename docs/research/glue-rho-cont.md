# glue-rho-cont: continuity of pkg-I3's ρ_ℓ

## Main result (VERIFIED: compiled, no sorry, axioms propext, Classical.choice, Quot.sound)

The gap flagged by rv-leaves-b (table row "`V_ℓ`, `ρ_ℓ` (I3)" and its open-items list:
"Continuity of `ρ_ℓ` (I3 `galRep`): not defined, needed for C10") is closed in Lean, in
`scratch/glue-rho-cont/RhoCont.lean`, over the unchanged definitions of pkg-I3 (`Tate.T`,
`AbVar`, `Pt`, `galAct`, `galT`, `galRep`; sections 1-2 of the file are a verbatim copy of
`scratch/pkg-I3/I3.lean` lines 15-335):

* `PkgI3.RhoCont.continuous_galT` (**unconditional**): for every field `K`, abelian variety
  `A/K` and prime `ℓ`, the action map `G_K × T_ℓ(A) → T_ℓ(A)`, `(σ, x) ↦ σ x`, is continuous
  for the Krull topology on `G_K = Field.absoluteGaloisGroup K` (Mathlib's instance) and the
  inverse-limit topology on `T_ℓ(A)`.
* `PkgI3.RhoCont.continuous_galRep`: if `T_ℓ(A)` is free of finite rank over `ℤ_ℓ`,
  the action map `G_K × V_ℓ(A) → V_ℓ(A)` is continuous for the `ℓ`-adic topology on `V_ℓ(A)`.
* `PkgI3.RhoCont.continuous_toMatrix_galRep`: under the same hypothesis, for **every** finite
  `ℚ_ℓ`-basis `b` of `V_ℓ(A)`, `σ ↦ LinearMap.toMatrix b b (ρ_ℓ σ)` is continuous
  `G_K → Matrix I I ℚ_ℓ`. This is the statement "`ρ_ℓ : G_K → GL_r(ℚ_ℓ)` is continuous".
* `PkgI3.RhoCont.continuous_trace_galRep`: `σ ↦ tr ρ_ℓ(σ)` is continuous (the form C10 uses:
  Chebotarev density together with Brauer–Nesbitt compares traces on Frobenius elements).
* `PkgI3.continuous_galRep_of_tateModuleFree`: from pkg-I3's leaf I3.M0 `TateModuleFree`
  (definition copied verbatim), for `(ℓ : K) ≠ 0` (every `ℓ` when `K` is a number field), both
  the joint continuity and the continuity of traces hold. So for C10 continuity costs no new
  leaf: it is glue plus the existing leaf I3.M0.

## Topologies (definitions, no invented structure)

* `A(K̄)` (`Additive (A.Pt (AlgebraicClosure K))`) gets the discrete topology (`⊥`), a file-local
  instance. `T ℓ M` is pkg-I3's subgroup of `ℕ → M`; it gets Mathlib's subspace topology of the
  product. That is exactly the inverse-limit topology of the discrete groups `M[ℓⁿ]`. No
  finiteness of `A[ℓⁿ](K̄)` is needed for continuity (finiteness would give compactness, which
  nothing here uses).
* `Tate.nhds_zero_hasBasis` and `Tate.coord_eq_zero_iff` (compiled, for any discrete abelian
  group `M`): the sets `{x | xₙ = 0}` form a neighbourhood basis of `0`, and
  `{x | xₙ = 0} = ℓⁿ · T_ℓ(M)`. So the inverse-limit topology **is** the `ℓ`-adic topology of
  the `ℤ_ℓ`-module `T_ℓ(M)`. `Tate.continuous_of_linearMap_padicInt`: every `ℤ_ℓ`-linear
  `T_ℓ(M) → ℤ_ℓ` is continuous.
* `V_ℓ(A) = ℚ_ℓ ⊗_{ℤ_ℓ} T_ℓ(A)` gets Mathlib's `moduleTopology ℚ_[ℓ]`. When `T_ℓ(A) ≅ ℤ_ℓ^r`,
  `V_ℓ(A) ≅ ℚ_ℓ^r` and this is the product (`ℓ`-adic) topology. That is STANDARD: a finite
  free module has the product topology as its module topology (Mathlib
  `IsModuleTopology` for finite products). The matrix form above holds for every basis, which
  makes the identification explicit.

## The geometric input: open stabilizers (`exists_openSubgroup_galAct_eq`, compiled)

Every `K̄`-point `P` of `A`, that is a `K`-morphism `Spec K̄ → A`, is fixed by
`Gal(K̄/E) = E.fixingSubgroup` for an intermediate field `E` finite over `K`; that subgroup is
open (`IntermediateField.fixingSubgroup_isOpen`). Proof as formalized:
`P = Spec(s) ≫ fromSpecStalk x`, where `s = stalkClosedPointTo P : 𝒪_{A,x} → K̄`
(`Scheme.Spec_stalkClosedPointTo_fromSpecStalk`). The stalk map `𝒪_{Spec K} → 𝒪_{A,x}` is
essentially of finite type because `A → Spec K` is locally of finite type (it is proper):
`LocallyOfFiniteType.stalkMap`. So `s` and `σ ∘ s` are equal once they agree on the image of
`𝒪_{Spec K}` and on a finite set of essential generators (`RingHom.EssFiniteType.ext`).
* On `𝒪_{Spec K}`, both maps are `K → K̄`, which `σ` fixes. The proof works through
  `Scheme.stalkClosedPointTo_comp`, the structure condition `P ≫ (A → Spec K) = Spec(K → K̄)`,
  every element of the stalk of `Spec K` being a germ on `⊤`, and
  `Scheme.germ_stalkClosedPointTo_Spec`.
* On the generators: `E := K(s(generators))` is finite over `K` because `K̄/K` is algebraic
  (`IntermediateField.finiteDimensional_adjoin`).
Then `galAct σ P = Spec(σ) ≫ P = Spec(σ ∘ s) ≫ fromSpecStalk x = P`. The argument uses only
that `A → Spec K` is locally of finite type, so it holds for every `K`-scheme of finite type.

`RhoCont.continuous_act` is the topological glue: an action of a topological group on a discrete
set, by maps with `act (g h) = act g ∘ act h`, whose stabilizers contain open subgroups, is
jointly continuous. `Tate.continuous_map_action` passes from `M` to `T_ℓ(M)`. The passage from
`T_ℓ(A)` to `V_ℓ(A)` uses a `ℤ_ℓ`-basis of `T_ℓ(A)`, its base change to `ℚ_ℓ`, and the
continuity of `ℤ_ℓ`-linear functionals.

## Compile record

`lake env lean scratch/glue-rho-cont/RhoCont.lean` (Lean 4.35.0, Mathlib v4.35.0, about 35 s):
0 errors, 0 warnings. `#print axioms` for `exists_openSubgroup_galAct_eq`, `continuous_galT`,
`continuous_of_linearMap_padicInt`, `nhds_zero_hasBasis`,
`continuous_galRep_of_tateModuleFree` and `continuous_toMatrix_galRep` all give
`[propext, Classical.choice, Quot.sound]` (VERIFIED, 2026-11-11 23:57 PST).

## What remains / caveats

* Integration: when pkg-I3 is moved into `ZInQKernel/`, section 3 of `RhoCont.lean` can be
  appended to it unchanged (it uses only the I3 names). The discrete-topology instance on
  `Additive (A.Pt K̄)` and the module-topology instance on `A.V ℓ` should stay scoped, or become
  `def`s plus local instances, so that they do not clash with other topologies.
* C10 itself (Chebotarev, Brauer–Nesbitt, the comparison of traces) is not touched here. This
  task supplies only its continuity hypothesis, in three equivalent forms (joint, matrix, trace).
* Compactness of `T_ℓ(A)` (needs `A[ℓⁿ](K̄)` finite, Mumford) is not proved and not needed for
  continuity.
