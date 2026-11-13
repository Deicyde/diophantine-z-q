
/-! ## §3′. g0-split: the glue G1-G17, G19 split into named pieces (task g0-split, 2026-11-12;
folded into this file by leaf-adopt3, 2026-11-13, following g0-split's recipe, doc §4)

`GlueAssembly.GlueOutputs Mult.S_mul` asks, for each `u ∉ 𝒞`, for a number field `K'`, a point
`z ∈ K'¹⁰`, a real `h_A`, and

* (o1) `Φ(z) = J(u)` (step F1, glue G19),
* (o2) Pazuki's bound `h(z) ≤ …(h_A)` (step F3, glue G19, leaf R22),
* (o3) `NonCMOutput Q M h_A`: a level `N` with `1 ≤ N ≤ QM²` (G13-G16), `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`
  (G18/E2, leaf R18), `2 ≤ g ≤ N²` (G17 for `2 ≤ g`; E2 for `g ≤ N²`, proved from T34),
  `1 ≤ d = [L':ℚ] ≤ QM` (G7, B3), Gaudron-Rémond's `log deg φ` (E3, R19, on the isogeny of G17),
  Faltings' variation with additivity (E4, R20 + additivity) and Bost (R21); or the CM branch,
  which the route does not use (G6, NoCM).

Below, `h_A` is the stable Faltings height (def-faltings) of an abelian surface `A` over a number
field `L'` attached to `u` (`FibreOver`). Proved pieces applied: A4 (`exists_fibre_object`,
leaf-qm-fp), `model_dim`, H5's finiteness, E1 (`PkgI3.E1_exists_hom_ne_zero` with glue-ssbc's
`SemisimpleBaseChange`, copied in section `GlueSSBCSec`), T8 (Poincaré, a leaf), E2's
`dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34), `javanpeykarJ1` (from leaf-push2's
concrete R18), `thetaPazuki` (from leaf-push2's concrete R22) and the E3-E4 numerics
(`transfer_core`, from R19, R20, R21), `isogenousProduct`. leaf-adopt3: R18 and R22 are now the bundle
fields `r.r18`, `r.r22` (leaf-push2's statements over `ZInQ.LeafPush2.stableFaltingsHeight`);
g0-split's transported forms `R18_JavanpeykarConcrete`, `R22_PazukiConcrete` (over def-faltings'
height) are derived from them with the glue piece `HSyn.HeightCopiesAgree` (leaf-adopt2's glue
target, pure transport between the two textual copies of the height): `r18Concrete_of`,
`r22Concrete_of`. g0-split's copies of leaf-push2's R22 definitions and of `ffAlgebra`,
`javanpeykarBound` are replaced by the `ZInQ.LeafPush2` originals (identical text). The ten
missing glue pieces, smallest first (sizes SPECULATIVE), and `HeightCopiesAgree` form the bundle
`HSyn.GluePieces`:
1. `DimFinite` (an abelian variety has finite dimension),
2. `DimBaseChange` (dimension invariant under field extension),
3. `X1BelyiOnModel` (`BelyiX1` on the model of `IsJ1`),
4. `FibreSimple` (G5-G6 on `A`),
5. `HeightAdditivity` (E4),
6. `StableHeightBaseChange` (stable height invariant under base change),
7. `ProductExists` (G17: `A × Z` is an abelian variety),
8. `ReverseIsogeny` (G17: the isogeny `J → A × Z`),
9. `ThetaPointOfFibre` (G19, F1 on `A`),
10. `ModularConstituent` (G2, G4, G7-G16).
`glueOutputs_of_leaves` takes them as the bundle `HSyn.GluePieces`. -/

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

/-- `A`, an abelian variety over the number field `K` (def-faltings' `AbVar`), is (up to
isomorphism of `ℚ̄`-schemes, after some embedding `K → ℚ̄`) the abelian surface of an object
`(A, ι, η)` of `Y₃` at a `ℚ̄`-point `y` of `Y₃` lying over `J(u)` (for the moduli data
`(Y, Φ, π)` that R1-R2 provide). -/
def FibreOver (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K) : Prop :=
  ∃ (emb : K.K →+* Qbar) (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar),
    Φ Qbar y = M3.mk P ∧ π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) ∧
    (letI : Algebra K.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X))

/-- `P ≅ A × Z` as group schemes: homomorphisms `p₁ : P → A`, `p₂ : P → Z` with
`(p₁, p₂) : P → A × Z` an isomorphism. -/
def IsProductOf {K : Type} [Field K] (P A Z : Over (Spec (CommRingCat.of K))) [MonObj P]
    [MonObj A] [MonObj Z] : Prop :=
  ∃ (p₁ : P ⟶ A) (p₂ : P ⟶ Z), IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)

/-- The hypotheses of E1 (`PkgI3.E1_exists_hom_ne_zero`): for some prime `ℓ` and field `E ⊇ ℚ_ℓ`,
`V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a common nonzero constituent, as `G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-! ### The missing pieces, smallest first -/

/-- **Missing piece 2 (definition-level glue; used by G18/E2 and G17).** The dimension of an
abelian variety is invariant under extension of the base field (Stacks, Tag 00P4 for finitely
generated algebras over a field; STANDARD). -/
def DimBaseChange : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K),
    (A.baseChange L).dim = A.dim

/-- **Missing piece 6 (definition-level glue; used by E3-E4).** The *stable* Faltings
height is invariant under finite extension of the number field (Faltings 1983 §1; Deligne,
Sém. Bourbaki 616). For def-faltings' infimum this needs semistable reduction and the Néron
models of H5 (`NeronModelMinimal`); it is a property of the definition, not a literature leaf. -/
def StableHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K),
    stableFaltingsHeight (A.baseChange L) = stableFaltingsHeight A

/-- **R18 (Javanpeykar, ANT 8 (2014), Thm 1.1.1), transported: leaf-push2's `R18_Javanpeykar`**
(`ResearchLeaves.r18`) on this file's copies (`LeafModCurves.IsCurve`, `IsJacobian`,
`IsBelyiFunction` are textual copies of leaf-push2's; the height is def-faltings'
`stableFaltingsHeight` through `LeafAdopt.abVarEquiv`). leaf-adopt3: no longer a hypothesis; it is
derived (`r18Concrete_of`) from `r.r18` and the glue piece `HSyn.HeightCopiesAgree`. -/
def R18_JavanpeykarConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (X : Over (Spec (CommRingCat.of K)))
    [LeafModCurves.IsCurve X] [IsIntegral X.left] (P₀ : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ X)
    (J : PkgI3.AbVar K) (aj : X ⟶ J.X), LeafModCurves.IsJacobian X P₀ J aj →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ t : X.left.functionField,
      letI := ZInQ.LeafPush2.ffAlgebra X
      LeafModCurves.IsBelyiFunction K X.left.functionField t →
      ∀ d : ℕ, Module.finrank (IntermediateField.adjoin K {t}) X.left.functionField = d → 0 < d →
        stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm J) ≤ ((ZInQ.LeafPush2.javanpeykarBound g d : ℝ) : EReal)

/-- **Missing piece 3 (glue E2, Belyi half: `LeafModCurves.BelyiX1` on the model of `IsJ1`).**
Every `J₁(N)` over `ℚ` (`IsJ1 N J`) is the Jacobian of a pointed curve `X` whose function field
carries a Belyi function `t` (`j/1728`) of degree `[ℚ(X) : ℚ(t)] ≤ N²`. From `BelyiX1` (a glue
target of leaf-modcurves: good reduction of `E_j` away from `j = 0, 1728, ∞`, and
`[K_N : ℚ(j)] ≤ N²`) by transport along `ℚ(X) ≅ K_N` (`IsX1Model`); the transport is not done
here. -/
def X1BelyiOnModel : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∃ (X : Over (Spec (CommRingCat.of ℚ))) (_ : LeafModCurves.IsCurve X) (_ : IsIntegral X.left)
      (P₀ : 𝟙_ (Over (Spec (CommRingCat.of ℚ))) ⟶ X) (aj : X ⟶ J.X),
      LeafModCurves.IsJacobian X P₀ J aj ∧ ∃ t : X.left.functionField,
        (letI := ZInQ.LeafPush2.ffAlgebra X; LeafModCurves.IsBelyiFunction ℚ X.left.functionField t) ∧
        ∃ d : ℕ,
          (letI := ZInQ.LeafPush2.ffAlgebra X
           Module.finrank (IntermediateField.adjoin ℚ {t}) X.left.functionField = d) ∧
          0 < d ∧ d ≤ N ^ 2

/-- **G18/E2: R18 applied to `X₁(N)` (proved below, `javanpeykarJ1`, from
`R18_JavanpeykarConcrete`, `X1BelyiOnModel` and T34).** For every `N ≥ 1` and every `J₁(N)` of
positive dimension over `ℚ`, `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`. -/
def JavanpeykarJ1 : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∀ g : ℕ, J.dim = (g : WithBot ℕ∞) → 1 ≤ g →
    ∀ x : ℝ, stableFaltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) = x →
      x ≤ 13000000 * (N : ℝ) ^ 12

/-- **Missing piece 5 (glue E4, the additivity half that the transfer uses).**
`h_F(A) + h_F(Z) ≤ h_F(A × Z)` for abelian varieties over a number field (equality holds;
Faltings 1983 §1; needs Néron models and H5, rv-blueprints F1). -/
def HeightAdditivity : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L),
    IsProductOf P.X A.X Z.X → ∀ a z p : ℝ, stableFaltingsHeight A = a →
      stableFaltingsHeight Z = z → stableFaltingsHeight P = p → a + z ≤ p

/-- **Missing piece 1 (definition-level glue).** An abelian variety has finite dimension: its
Krull dimension is a natural number (a scheme of finite type over a field; STANDARD). -/
def DimFinite : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), ∃ n : ℕ, A.dim = (n : WithBot ℕ∞)

/-- **Missing piece 7 (definition-level glue; G17).** The product `A × Z` of abelian varieties is an
abelian variety `P` (proper, smooth, geometrically integral group scheme), with
`dim P = dim A + dim Z` (Mumford §4; STANDARD; geometric integrality of products is not in
Mathlib). -/
def ProductExists : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A Z : PkgI3.AbVar L),
    ∃ P : ZInQ.DefFaltings.AbVar L, IsProductOf P.X A.X Z.X ∧ P.dim = A.dim + Z.dim

/-- **Missing piece 8 (glue G17, after Poincaré).** If `(f, g) : A × Z → J` is finite and surjective
(T8's output) and `P ≅ A × Z`, there is an isogeny `J → P` in the other direction, and
`dim J = dim P` (Mumford §8, Thm 4 / Remark, UNVERIFIED: an isogeny of degree `n` has a
quasi-inverse `ψ` with `φψ = [n]`). Needs finite group schemes and quotients, not in Mathlib. -/
def ReverseIsogeny : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A J Z : PkgI3.AbVar L) (P : ZInQ.DefFaltings.AbVar L)
    (f : PkgI3.AbVar.Hom A J) (g : PkgI3.AbVar.Hom Z J), IsProductOf P.X A.X Z.X →
    PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) →
    ∃ φ : ((LeafAdopt.abVarEquiv L).symm J).X ⟶ P.X, ZInQ.DefFaltings.IsIsogeny φ ∧ J.dim = P.dim

/-- **G17 after Poincaré (proved below, `isogenousProduct`, from `DimFinite`, `ProductExists`,
`ReverseIsogeny`).** From T8's isogeny `(f, g) : A × Z → J` to Gaudron-Rémond's input: `P ≅ A × Z`,
an isogeny `J → P`, and `dim J = dim A + dim Z`. -/
def IsogenousProduct : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A J Z : PkgI3.AbVar L) (f : PkgI3.AbVar.Hom A J)
    (g : PkgI3.AbVar.Hom Z J),
    PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) →
    ∃ (P : ZInQ.DefFaltings.AbVar L) (φ : ((LeafAdopt.abVarEquiv L).symm J).X ⟶ P.X),
      ZInQ.DefFaltings.IsIsogeny φ ∧ IsProductOf P.X A.X Z.X ∧
      ∀ a n : ℕ, A.dim = a → J.dim = n → ∃ m : ℕ, Z.dim = m ∧ a + m = n

/-- **Missing piece 4 (glue G5-G6 on the actual `A`: QM dichotomy and NoCM).** For `u ∉ 𝒞`, the
fibre surface `A` (any number-field model of it) is simple over its field: every nonzero
endomorphism is an isogeny (because `End⁰(A_ℚ̄) = B` is a division algebra). Proved parts: T27 at
`B = (2,-3)` (`PkgI3.qmDichotomy_B6`), the Elkies identities and the free `W`-orbit
(`GlueRepo.PR.fibre_free`), `cm_of_val`. Missing: the instantiation on `A` and the counting with
R5 (h-decomposition G6). -/
def FibreSimple : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K.K A)

/-- **R22 (Pazuki, Bull. SMF 140 (2012), Cor. 1.3(2)), transported: leaf-push2's `R22_Pazuki`**
(`ResearchLeaves.r22`; same statement, the height is def-faltings' `stableFaltingsHeight` through
`LeafAdopt.abVarEquiv`). leaf-adopt3: no longer a hypothesis; it is derived (`r22Concrete_of`)
from `r.r22` and the glue piece `HSyn.HeightCopiesAgree`. -/
def R22_PazukiConcrete : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∀ x : ℝ, stableFaltingsHeight ((LeafAdopt.abVarEquiv K).symm A) = x →
    ∀ X : ℝ, max 1 (x + Real.log Real.pi) ≤ X →
    ∀ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φ : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts A σ),
      ZInQ.LeafPush2.IsUniformization σ Λ Φ →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, ZInQ.LeafPush2.IsSiegel Ω → ZInQ.LeafPush2.IsPeriodMatrix Λ Ω →
    ∀ (L : Type) [Field L] [NumberField L] (emb : L →+* ℂ) (z : ZInQ.LeafPush2.Char2 → L) (c : ℂ), c ≠ 0 →
      (∀ m, emb (z m) = c * ZInQ.LeafPush2.thetaConst Ω m) →
      ZInQ.LeafPush2.absLogHeight z ≤ X / 2 + ZInQ.LeafPush2.pazukiC2 * Real.log (X + 2)

/-- **Missing piece 9 (glue G19, F1 on the actual `A`).** For `u ∉ 𝒞` and the fibre surface `A`
over `J(u)` (any number-field model): at some complex place `σ` there are an analytic
uniformization `Φ` of `A(ℂ)_σ` with kernel `Λ`, a period matrix `Ω ∈ 𝔥₂` of `Λ` (for the principal
polarization), and an algebraic representative `z ∈ L¹⁶` of the theta-null point `[θ_m(0, Ω)]`;
and its ten even coordinates `z'` (in a number field `K'`) satisfy `Φ(z') = J(u)` with
`h(z') ≤ h(z)` (the six odd theta nulls vanish). F1: Lin-Yang's Igusa invariants on the QM locus
(R3) with the theta expressions of `ψ₄`, `χ₁₀` (R4). Proved parts: F1's algebra
(`PkgI1.f1_algebra`), theta-structure independence (`PkgI1.thetaRatio_invariant`), leaf-push2's
`linYangTuple_onQMLocus` (not copied). Missing: the analytic side (R1(b), uniformization:
leaf-push2's `UniformizationExists`), R3 and R4 applied to `A`, algebraicity of the theta point,
the odd-zero height comparison. -/
def ThetaPointOfFibre : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → ZInQ.LeafPush2.CPts (LeafAdopt.abVarEquiv K.K A) σ), ZInQ.LeafPush2.IsUniformization σ Λ Φu ∧
    ∃ Ω : Matrix (Fin 2) (Fin 2) ℂ, ZInQ.LeafPush2.IsSiegel Ω ∧ ZInQ.LeafPush2.IsPeriodMatrix Λ Ω ∧
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : ZInQ.LeafPush2.Char2 → L.K) (c : ℂ), c ≠ 0 ∧
      (∀ m, emb (z m) = c * ZInQ.LeafPush2.thetaConst Ω m) ∧
    ∃ (K' : GlueAssembly.NF) (z' : Fin 10 → K'.K),
      3779136 * (∏ i, z' i) ^ 4 / (∑ i, z' i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
      Height.logHeight z' / Module.finrank ℚ K'.K ≤ ZInQ.LeafPush2.absLogHeight z

/-- **G19: F1 and F3 on the actual `A` (proved below, `thetaPazuki`, from
`R22_PazukiConcrete` and `ThetaPointOfFibre`).** For `u ∉ 𝒞` and the fibre surface `A` over
`J(u)` with stable height `x`, a point `z ∈ K'¹⁰` with `Φ(z) = J(u)` and Pazuki's bound. -/
def ThetaPazuki : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    A.dim = 2 → ∀ x : ℝ, stableFaltingsHeight A = x →
      ∃ (K' : GlueAssembly.NF) (z : Fin 10 → K'.K),
        3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
        GlueAssembly.PazukiOutput (Height.logHeight z / Module.finrank ℚ K'.K) x

/-- **Missing piece 10 (glue G2, G4, G7-G16: fibre field, scalar descent, modularity, conductor).**
For `u ∉ 𝒞` and an object `P` of `Y₃` over `ℚ̄` at a point over `J(u)`: there are a number field
`L' ⊆ ℚ̄` with `[L':ℚ] ≤ QM` (G2, G4, G7: the fibre field, the Hom field and B3) and a model `A`
of `P`'s surface over `L'`, a level `1 ≤ N ≤ QM²` (G13-G16: the conductor of the newform `f`), a
`J₁(N)` over `ℚ`, and a common constituent of `V_ℓ(A)` and `V_ℓ(J₁(N)_{L'})` as
`G_{L'}`-representations (G8-G14: `r_ℓ`, its twist, Pan-Berger modularity, the newform and
Eichler-Shimura). Here `Q = Q_D`, `M = M_{S_mul}(u)`. The model and the field are produced
together because `[L':ℚ] ≤ QM` bounds the field of `A`: quantifying over all models would make the
piece false. Proved cores (not on the actual `A`): `GlueDescent.B3Q.b3_degree_le_QM` (B3),
`GlueConductor.level_le` (G16), `GlueConductor.D1_genuine` (D1), `PkgI2.D2_fixed_of_raynaud`,
`PkgI6.artinConductor_le_of_upper`, `PkgI3.C2_absolutelyIrreducible`, `HSyn.weight_match`,
`GlueAssembly.twist_finite`, `LeafModCurves.g13_constituent`, `GlueC10.c10`,
`PkgI2.goodReduction_of_QM_rational3` (G3), `PkgI2.inertiaTrivial_of_goodReduction` (G11).
Missing: the instantiation of all of these on `A`, the appendix lemma (G9), oddness (G10, needs
T11-T12, placeholders) and Carayol's conductor (R17, a placeholder). -/
def ModularConstituent : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : ZInQ.DefFaltings.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent (LeafAdopt.abVarEquiv L.K A)
        (LeafAdopt.abVarEquiv L.K (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K))

/-! ### Proved connective pieces -/

/-- **R18 transported (proved, leaf-adopt3)** from leaf-push2's `R18_Javanpeykar` (the bundle
field `r18`) and `HeightCopiesAgree`. The curve, Jacobian and Belyi predicates of
`LeafModCurves` and `ZInQ.LeafPush2` are textual copies, converted field by field. -/
theorem r18Concrete_of (h : ZInQ.LeafPush2.R18_Javanpeykar) (hH : HeightCopiesAgree) :
    R18_JavanpeykarConcrete := by
  intro K _ _ X hX _ P₀ J aj hJac g hg hg1 t ht d hd hd0
  haveI : ZInQ.LeafPush2.IsCurve X := ⟨hX.proper, hX.smooth, hX.geomConnected⟩
  rw [← hH K J]
  exact h K X P₀ J aj ⟨hJac.base, hJac.univ⟩ g hg hg1 t ht d hd hd0

/-- **R22 transported (proved, leaf-adopt3)** from leaf-push2's `R22_Pazuki` (the bundle field
`r22`) and `HeightCopiesAgree`. -/
theorem r22Concrete_of (h : ZInQ.LeafPush2.R22_Pazuki) (hH : HeightCopiesAgree) :
    R22_PazukiConcrete := by
  intro K _ _ A hA x hx
  rw [← hH K A] at hx
  exact h K A hA x hx

/-- Isomorphic schemes over `S` have the same Krull dimension. -/
theorem dim_eq_of_iso {S : Scheme} {X Y : Over S} (e : X ≅ Y) :
    topologicalKrullDim X.left = topologicalKrullDim Y.left :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso ((Over.forget S).mapIso e)).isHomeomorph

/-- **The model is a surface (proved from `DimBaseChange`).** A model over `L` of an abelian
surface over `ℚ̄` has dimension `2`. -/
theorem model_dim (hDim : DimBaseChange) {L : Type} [Field L] (emb : L →+* Qbar)
    (A : ZInQ.DefFaltings.AbVar L) (B : PkgI3.AbVar Qbar)
    (hiso : letI : Algebra L Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ B.X))
    (hB : B.dim = 2) : A.dim = 2 := by
  letI : Algebra L Qbar := emb.toAlgebra
  obtain ⟨e⟩ : Nonempty ((A.baseChange Qbar).X ≅ B.X) := hiso
  rw [← hDim L Qbar A, ← hB]
  exact dim_eq_of_iso e

/-- **G18/E2, Javanpeykar on `J₁(N)` (proved).** From the concrete R18, the Belyi data on the
model (`X1BelyiOnModel`) and E2's `dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34):
`13·10⁶·g·d⁵ ≤ 13·10⁶·N²·(N²)⁵`. -/
theorem javanpeykarJ1 (hR18 : R18_JavanpeykarConcrete) (hB : X1BelyiOnModel)
    (hT34 : LeafModCurves.DimJ1Genus) : JavanpeykarJ1 := by
  intro N hN J hJ g hg hg1 x hx
  obtain ⟨X, _, _, P₀, aj, hJac, t, ht, d, hd, hd0, hdN⟩ := hB N hN J hJ
  have h := hR18 ℚ X P₀ J aj hJac g hg hg1 t ht d hd hd0
  rw [hx] at h
  have hxb : x ≤ ZInQ.LeafPush2.javanpeykarBound g d := EReal.coe_le_coe_iff.mp h
  obtain ⟨g', hg', hgN⟩ := LeafModCurves.dim_J1_le hT34 N hN J hJ
  have hgg : g = g' := by
    have : (g : WithBot ℕ∞) = (g' : WithBot ℕ∞) := hg.symm.trans hg'
    exact_mod_cast this
  subst hgg
  have hgR : (g : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  have hdR : (d : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hdN
  calc x ≤ ZInQ.LeafPush2.javanpeykarBound g d := hxb
    _ = 13 * 10 ^ 6 * (g : ℝ) * (d : ℝ) ^ 5 := rfl
    _ ≤ 13 * 10 ^ 6 * ((N : ℝ) ^ 2) * ((N : ℝ) ^ 2) ^ 5 := by gcongr
    _ = 13000000 * (N : ℝ) ^ 12 := by ring

/-- **G19, F1 + F3 (proved)** from the concrete R22 at `X = max(1, h_F(A) + 3) ≥ max(1, h_F(A) +
log π)` (the hardened form of `PazukiOutput`, rv-leaves-a) and the
theta point of `ThetaPointOfFibre`. -/
theorem thetaPazuki (hR22 : R22_PazukiConcrete) (hT : ThetaPointOfFibre) : ThetaPazuki := by
  intro Y Φ π h1 h2 u hu K A hFib hA2 x hx
  obtain ⟨σ, Λ, Φu, hΦu, Ω, hΩ, hP, L, emb, z, c, hc, hz, K', z', hF1, hle⟩ :=
    hT Y Φ π h1 h2 u hu K A hFib
  refine ⟨K', z', hF1, ?_⟩
  have hx' : stableFaltingsHeight ((LeafAdopt.abVarEquiv K.K).symm
      (LeafAdopt.abVarEquiv K.K A)) = x := by
    rw [Equiv.symm_apply_apply]; exact hx
  have hpi : Real.log Real.pi ≤ 3 := by
    have h4 : Real.log Real.pi ≤ Real.log 4 :=
      Real.log_le_log Real.pi_pos (by linarith [Real.pi_lt_four])
    have h42 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  have h := hR22 K.K (LeafAdopt.abVarEquiv K.K A) hA2 x hx' (max 1 (x + 3))
    (max_le_max le_rfl (by linarith)) σ Λ Φu hΦu Ω hΩ hP L.K emb z c hc hz
  unfold GlueAssembly.PazukiOutput
  unfold ZInQ.LeafPush2.pazukiC2 at h
  linarith

/-- **G17 after Poincaré (proved)** from `DimFinite`, `ProductExists`, `ReverseIsogeny`. -/
theorem isogenousProduct (hF : DimFinite) (hP : ProductExists) (hR : ReverseIsogeny) :
    IsogenousProduct := by
  intro L _ _ A J Z f g hiso
  obtain ⟨P, hPA, hPd⟩ := hP L A Z
  obtain ⟨φ, hφ, hJd⟩ := hR L A J Z P f g hPA hiso
  refine ⟨P, φ, hφ, hPA, fun a n ha hn => ?_⟩
  obtain ⟨m, hm⟩ := hF L Z
  refine ⟨m, hm, ?_⟩
  have h : ((n : ℕ) : WithBot ℕ∞) = ((a + m : ℕ) : WithBot ℕ∞) := by
    rw [← hn, hJd, hPd, ha, hm, Nat.cast_add]
  exact_mod_cast h.symm

/-- `log κ` of Gaudron-Rémond, computed. -/
theorem log_grKappa (g d : ℕ) (x : ℝ) (hg : 1 ≤ g) (hd : 1 ≤ d) :
    Real.log (grKappa g d x) = 1024 * (g : ℝ) ^ 3 * (64 * (g : ℝ) ^ 2 * Real.log (14 * g) +
      Real.log d + 2 * Real.log (max x (max (Real.log d) 1))) := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (0 : ℝ) < 14 * g := by positivity
  have hm : (1 : ℝ) ≤ max (max x (Real.log d)) 1 := le_max_right _ _
  have ha : ((14 * g : ℝ) ^ (64 * g ^ 2)) ≠ 0 := (pow_pos h14 _).ne'
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hm2 : (max (max x (Real.log d)) 1) ^ 2 ≠ 0 := (pow_pos (by linarith) _).ne'
  unfold grKappa
  rw [Real.log_pow, Real.log_mul (mul_ne_zero ha hd0) hm2, Real.log_mul ha hd0, Real.log_pow,
    Real.log_pow, max_assoc]
  push_cast
  ring

theorem one_le_grKappa (g d : ℕ) (x : ℝ) (hg : 1 ≤ g) (hd : 1 ≤ d) : 1 ≤ grKappa g d x := by
  have hg' : (1 : ℝ) ≤ g := by exact_mod_cast hg
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h14 : (1 : ℝ) ≤ 14 * g := by linarith
  have hm : (1 : ℝ) ≤ max (max x (Real.log d)) 1 := le_max_right _ _
  unfold grKappa
  apply one_le_pow₀
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ h14) hd')
    (one_le_pow₀ hm)

/-- **E3-E4 numerics on concrete objects (proved from R19, R20, R21).** Over a number field `L`,
for `J` of dimension `g ≥ 2` with an isogeny `J → P`, `h_F(A) + h_F(Z) ≤ h_F(P)`, `dim Z ≤ g`,
the bounds on `N`, `[L:ℚ]`, `h_F(J)` and `g ≤ N²` give glue-assembly's `NonCMOutput`. -/
theorem transfer_core (r19 : R19_GaudronRemond) (r20 : R20_FaltingsLemma5) (r21 : R21_Bost)
    {L : Type} [Field L] [NumberField L] (J P A Z : ZInQ.DefFaltings.AbVar L) (g gZ : ℕ)
    (hJd : J.dim = (g : WithBot ℕ∞)) (hZd : Z.dim = (gZ : WithBot ℕ∞)) (hgZ : gZ ≤ g)
    (hg2 : 2 ≤ g) (φ : J.X ⟶ P.X) (hφ : IsIsogeny φ) (x y a z : ℝ)
    (hx : stableFaltingsHeight J = x) (hy : stableFaltingsHeight P = y)
    (hz : stableFaltingsHeight Z = z) (hadd : a + z ≤ y) {Q M N : ℝ} (hN1 : 1 ≤ N)
    (hN : N ≤ Q * M ^ 2) (hJav : x ≤ 13000000 * N ^ 12) (hgN : (g : ℝ) ≤ N ^ 2)
    (hd : (Module.finrank ℚ L : ℝ) ≤ Q * M) :
    GlueAssembly.NonCMOutput Q M a := by
  obtain ⟨⟨ψ, hψ, hdeg⟩, -⟩ := r19 L J P g x hJd hx ⟨φ, hφ⟩
  have hvar := r20 L J P ψ hψ x y hx hy
  have hB := r21 L Z gZ hZd
  rw [hz] at hB
  have hB' : -(3 / 2) * (gZ : ℝ) ≤ z := EReal.coe_le_coe_iff.mp hB
  set d := Module.finrank ℚ L with hdd
  have hd1 : 1 ≤ d := Module.finrank_pos
  have hg1 : 1 ≤ g := by omega
  have hκ := log_grKappa g d x hg1 hd1
  have hκ1 := one_le_grKappa g d x hg1 hd1
  have hlogdeg : Real.log (isogDeg ψ) ≤ Real.log (grKappa g d x) := by
    rcases Nat.eq_zero_or_pos (isogDeg ψ) with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact Real.log_nonneg hκ1
    · exact Real.log_le_log (by exact_mod_cast hpos) hdeg
  refine ⟨N, g, d, x, Real.log (isogDeg ψ), z, hN1, hN, hJav, by exact_mod_cast hg2, hgN,
    by exact_mod_cast hd1, hd, ?_, ?_, ?_⟩
  · rw [hκ] at hlogdeg; exact hlogdeg
  · have := (abs_le.mp hvar).1
    linarith
  · have hgZr : (gZ : ℝ) ≤ g := by exact_mod_cast hgZ
    linarith

/-- glue-ssbc's theorem in `GlueI3`'s statement. -/
theorem semisimpleBaseChange : GlueI3.SemisimpleBaseChange :=
  fun k E G V _ _ _ _ _ _ _ _ ρ hρ => GlueSSBC.semisimpleBaseChange k E G V ρ hρ

/-- **E1 on a common constituent (proved)**: `PkgI3.E1_exists_hom_ne_zero` with R9 (Faltings),
T26 and glue-ssbc. -/
theorem hom_of_common (r : ResearchLeaves) (t : TextbookLeaves) {K : Type} [Field K]
    [NumberField K] (A J : PkgI3.AbVar K) (h : CommonConstituent A J) :
    ∃ f : PkgI3.AbVar.Hom A J, f ≠ 0 := by
  obtain ⟨ℓ, _, E, _, _, U, U', e, hU, he⟩ := h
  exact PkgI3.E1_exists_hom_ne_zero r.r9a r.r9b t.t26 semisimpleBaseChange A J ℓ E U U' hU e he

end G0Split

/-- **The glue pieces** (g0-split's ten missing pieces, smallest first, and leaf-adopt2's
`HeightCopiesAgree`), bundled (leaf-adopt3). Each is a `def … : Prop` whose docstring names its
glue step; none is a literature leaf, and each is to be proved in Lean by the project. -/
structure GluePieces : Prop where
  /-- 1. An abelian variety has finite dimension (definition level). -/
  dimFinite : G0Split.DimFinite
  /-- 2. Dimension is invariant under field extension (Stacks 00P4). -/
  dimBaseChange : G0Split.DimBaseChange
  /-- 3. E2, Belyi half: `BelyiX1` on the model of `IsJ1`. -/
  belyi : G0Split.X1BelyiOnModel
  /-- 4. G5-G6 on the fibre surface: simplicity. -/
  fibreSimple : G0Split.FibreSimple
  /-- 5. E4: additivity of the stable height on products. -/
  additivity : G0Split.HeightAdditivity
  /-- 6. Stable height invariant under base change. -/
  stableHeightBaseChange : G0Split.StableHeightBaseChange
  /-- 7. G17: products of abelian varieties exist. -/
  productExists : G0Split.ProductExists
  /-- 8. G17: the reverse isogeny `J → A × Z`. -/
  reverseIsogeny : G0Split.ReverseIsogeny
  /-- 9. G19, F1 on the fibre surface: the theta point. -/
  thetaPoint : G0Split.ThetaPointOfFibre
  /-- 10. G2, G4, G7-G16: field, model, level and common constituent. -/
  modularConstituent : G0Split.ModularConstituent
  /-- 11. The two textual copies of the stable Faltings height agree (leaf-adopt2's target). -/
  heightCopies : HeightCopiesAgree

open G0Split in
/-- **The glue G1-G17 and G19 (non-Arakelov part), split (g0-split).** The leaves and the ten
missing glue pieces (each a `def … : Prop` in `G0Split` whose docstring names its glue step) give
glue-assembly's interface `GlueOutputs` at `S = Mult.S_mul`. Applied proved pieces: A4
(`LeafQM.AV.exists_fibre_object`, from R1-R2), `model_dim`, H5's finiteness
(`faltingsHeight_coe`), E1 (`hom_of_common`: R9, T26, glue-ssbc), T8 (Poincaré, a leaf), E2's
`dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34), `javanpeykarJ1` (concrete R18),
`thetaPazuki` (concrete R22), `isogenousProduct`, and the E3-E4 numerics (`transfer_core`, from
R19-R21). The non-CM disjunct is used (G6, NoCM). -/
theorem glueOutputs_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  obtain ⟨hDimF, hDim, hBelyi, hSimp, hAdd, hBC, hProdE, hRev, hThetaPt, hMod, hCopies⟩ := gp
  have hR18 : R18_JavanpeykarConcrete := r18Concrete_of r.r18 hCopies
  have hR22 : R22_PazukiConcrete := r22Concrete_of r.r22 hCopies
  -- A4: the moduli data and an object over every value
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ :=
    LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r.r1r2)
  intro u hu
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)))
  -- G2-G16 (missing piece 10, `ModularConstituent`): the field `L'`, the model `A`, the level `N`, `J₁(N)`
  obtain ⟨L, emb, A, N, J, hiso, hN0, hJ1, hNQ, hdQ, hCC⟩ := hMod Y Φ π h1 h2 u hu y P hP hy
  have hFib : FibreOver Y Φ π u L A := ⟨emb, y, P, hP, hy, hiso⟩
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  -- H5: the stable height of `A` is real
  have hfin := r.h5.1
  have hx : ZInQ.DefFaltings.stableFaltingsHeight A = ZInQ.DefFaltings.faltingsHeight A :=
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm
  -- G19: the theta point (missing piece 9, `ThetaPointOfFibre`) and Pazuki (R22)
  obtain ⟨K', z, hF1, hPaz⟩ := thetaPazuki hR22 hThetaPt Y Φ π h1 h2 u hu L A hFib hA2 _ hx
  refine ⟨K', z, ZInQ.DefFaltings.faltingsHeight A, hF1, hPaz, Or.inl ?_⟩
  -- E1: a nonzero homomorphism `A → J₁(N)_{L'}`
  obtain ⟨f, hf⟩ := hom_of_common r t _ _ hCC
  -- G5-G6 (missing piece 4, `FibreSimple`): `A` simple; T8: Poincaré
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu L A hFib) f hf
  -- G17 after Poincaré (`isogenousProduct`, from missing pieces 1, 7, 8): `A × Z`, the isogeny `J₁(N)_{L'} → A × Z`
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ :=
    isogenousProduct hDimF hProdE hRev L.K _ _ _ f g hisoZ
  -- E2: `dim J₁(N) ≤ N²`
  obtain ⟨gJ, hgJ, hgN⟩ := LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1
  have hJLd : (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K).dim = (gJ : WithBot ℕ∞) :=
    (hDim ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)).trans hgJ
  have hALd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hA2]; rfl
  obtain ⟨gZ, hZd, hsum⟩ := hdims 2 gJ hALd hJLd
  -- heights (H5; missing pieces 5, 6; R18 with missing pieces 2, 3)
  have hxJ : ZInQ.DefFaltings.stableFaltingsHeight
      (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) =
      ZInQ.DefFaltings.faltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) := by
    rw [hBC ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)]
    exact (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hyP := (ZInQ.DefFaltings.faltingsHeight_coe hfin Pr).symm
  have hzZ := (ZInQ.DefFaltings.faltingsHeight_coe hfin ((LeafAdopt.abVarEquiv L.K).symm Z)).symm
  have hadd := hAdd L.K Pr A ((LeafAdopt.abVarEquiv L.K).symm Z) hPprod _ _ _ hx hzZ hyP
  have hJb := javanpeykarJ1 hR18 hBelyi t.t34 N hN0 J hJ1 gJ hgJ (by omega) _
    (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN0
  have hgN' : (gJ : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hgN
  -- E3-E4 (proved from R19-R21)
  exact transfer_core r.r19 r.r20 r.r21 (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) Pr A
    ((LeafAdopt.abVarEquiv L.K).symm Z) gJ gZ hJLd hZd (by omega) (by omega) φ hφ _ _ _ _ hxJ hyP
    hzZ hadd hN1 hNQ hJb hgN' hdQ

/-- **G18-G20, proved** (glue-assembly): `GlueOutputs Mult.S_mul → SixContactMin`, through F2
over Mathlib's Weil heights, the E2-E4 and F3 arithmetic, the final constant, and F4.
`GlueAssembly.SixContactMinAt Mult.S_mul` is `ZInQ.SixContactMin` by definition. -/
theorem sixContactMin_of_glueOutputs (h : GlueAssembly.GlueOutputs ZInQ.Mult.S_mul) :
    ZInQ.SixContactMin :=
  GlueAssembly.sixContactMinAt_of_glueOutputs h

/-- The scratch copy of `JHeightBound` in glue-assembly is the repository's. -/
theorem jHeightBound_copy_iff :
    GlueAssembly.JHeightBound ZInQ.Mult.S_mul ↔ ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul :=
  Iff.rfl

/-- **G0. The leaves and the glue pieces imply `SixContactMin`** (no `sorry`). Hypotheses: exactly
the three bundles `ResearchLeaves`, `TextbookLeaves`, `GluePieces`. -/
theorem sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces) :
    ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves r t gp)

/-- **G20 alone** (the existing proof in `ZInQKernel`), for reference. -/
example (h : ZInQ.JHeight.JHeightBound ZInQ.Mult.S_mul) : ZInQ.SixContactMin :=
  ZInQ.JHeight.sixContactMin_of_jHeightBound h

end HSyn
