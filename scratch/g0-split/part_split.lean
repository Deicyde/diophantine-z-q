
/-! ## §3′. g0-split: the glue G1-G17, G19 split into named pieces (task g0-split, 2026-11-12)

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
field `K` attached to `u` (`FibreOver`). The proved pieces are applied: A4 (`exists_fibre_object`,
leaf-qm-fp), E1 (`PkgI3.E1_exists_hom_ne_zero` with glue-ssbc's `SemisimpleBaseChange`), T8
(Poincaré, a leaf), E2's `dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34), H5's finiteness,
and the E3-E4 numerics (`transfer_core`, proved here from R19, R20, R21). Each missing piece is a
`def … : Prop` with a docstring naming its glue step; `glueOutputs_of_leaves` takes them as
hypotheses. -/

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

/-- **Missing piece 1 (definition-level glue; used by G18/E2 and G17).** The dimension of an
abelian variety is invariant under extension of the base field (Stacks, Tag 00P4 for finitely
generated algebras over a field; STANDARD). -/
def DimBaseChange : Prop :=
  ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K),
    (A.baseChange L).dim = A.dim

/-- **Missing piece 2 (definition-level glue; used by E3-E4 and F3).** The *stable* Faltings
height is invariant under finite extension of the number field (Faltings 1983 §1; Deligne,
Sém. Bourbaki 616). For def-faltings' infimum this needs semistable reduction and the Néron
models of H5 (`NeronModelMinimal`); it is a property of the definition, not a literature leaf. -/
def StableHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K),
    stableFaltingsHeight (A.baseChange L) = stableFaltingsHeight A

/-- **Missing piece 3 (glue G18/E2: R18 applied to `X₁(N)`).** For every `N ≥ 1` and every
`J₁(N)` over `ℚ` (`IsJ1`), `h_F(J₁(N)) ≤ 1.3·10⁷N¹²` (Javanpeykar, ANT 8 (2014), Thm 1.1.1 with
§2.3, applied with `g, deg_B ≤ [SL₂(ℤ):Γ₁(N)] ≤ N²`). Proved parts: the index bound
(`GlueAssembly.index_Gamma1_le`, `LeafModCurves.belyiDeg_Gamma1_le`, `genus_Gamma1_le`). Missing:
R18 itself (a placeholder `opaque`), the Belyi map of `X₁(N)` (`LeafModCurves.BelyiX1`, a glue
target) and the genus of `X₁(N)` as a curve. -/
def JavanpeykarJ1 : Prop :=
  ∀ (N : ℕ), 0 < N → ∀ J : PkgI3.AbVar ℚ, LeafModCurves.IsJ1 N J →
    ∀ x : ℝ, stableFaltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) = x →
      x ≤ 13000000 * (N : ℝ) ^ 12

/-- **Missing piece 4 (glue E4, the additivity half that the transfer uses).**
`h_F(A) + h_F(Z) ≤ h_F(A × Z)` for abelian varieties over a number field (equality holds;
Faltings 1983 §1; needs Néron models and H5, rv-blueprints F1). -/
def HeightAdditivity : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L),
    IsProductOf P.X A.X Z.X → ∀ a z p : ℝ, stableFaltingsHeight A = a →
      stableFaltingsHeight Z = z → stableFaltingsHeight P = p → a + z ≤ p

/-- **Missing piece 5 (glue G17, after Poincaré).** From T8's isogeny `(f, g) : A × Z → J`
(finite and surjective) to Gaudron-Rémond's input: the product `P = A × Z` exists as an abelian
variety, there is an isogeny `J → P` in the other direction (Mumford §8, Thm 4 / Remark,
UNVERIFIED), and `dim J = dim A + dim Z`. Definition-level glue (products of abelian varieties,
quasi-inverse isogenies, dimension of an isogeny). -/
def IsogenousProduct : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A J Z : PkgI3.AbVar L) (f : PkgI3.AbVar.Hom A J)
    (g : PkgI3.AbVar.Hom Z J),
    PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) →
    ∃ (P : ZInQ.DefFaltings.AbVar L) (φ : ((LeafAdopt.abVarEquiv L).symm J).X ⟶ P.X),
      ZInQ.DefFaltings.IsIsogeny φ ∧ IsProductOf P.X A.X Z.X ∧
      ∀ a n : ℕ, A.dim = a → J.dim = n → ∃ m : ℕ, Z.dim = m ∧ a + m = n

/-- **Missing piece 6 (glue G5-G6 on the actual `A`: QM dichotomy and NoCM).** For `u ∉ 𝒞`, the
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

/-- **Missing piece 7 (glue G19: F1 and F3 on the actual `A`).** For `u ∉ 𝒞` and the fibre
surface `A` over `J(u)` with stable height `x`, the ten even theta nulls `z` of `A` (with its
principal polarization) lie in a number field `K'`, satisfy `Φ(z) = J(u)` (F1: Lin-Yang's Igusa
invariants, R3, with the theta expression of R4) and Pazuki's bound (F3: R22, Cor. 1.3(2), Deligne
metric). Proved parts: F1's algebra (`PkgI1.f1_algebra`), theta-structure independence
(`PkgI1.thetaRatio_invariant`); F2 and F3's numerics are downstream in glue-assembly. Missing: the
theta point of `A` (R1(b), R3, R22 are placeholders; R3, R22 concrete in scratch/leaf-push2, not
folded in). -/
def ThetaPazuki : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∀ x : ℝ, stableFaltingsHeight A = x →
      ∃ (K' : GlueAssembly.NF) (z : Fin 10 → K'.K),
        3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K'.K (Jmap u) ∧
        GlueAssembly.PazukiOutput (Height.logHeight z / Module.finrank ℚ K'.K) x

/-- **Missing piece 8 (glue G2, G4, G7-G16: fibre field, scalar descent, modularity, conductor).**
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

/-- The eight missing pieces, bundled. -/
structure MissingPieces : Prop where
  dimBaseChange : DimBaseChange
  stableHeightBaseChange : StableHeightBaseChange
  javanpeykar : JavanpeykarJ1
  additivity : HeightAdditivity
  isogenousProduct : IsogenousProduct
  fibreSimple : FibreSimple
  thetaPazuki : ThetaPazuki
  modularConstituent : ModularConstituent

/-! ### Proved connective pieces -/

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

open G0Split in
/-- **The glue G1-G17 and G19 (non-Arakelov part), split (g0-split).** The leaves and the eight
missing glue pieces (each a `def … : Prop` in `G0Split` whose docstring names its glue step) give
glue-assembly's interface `GlueOutputs` at `S = Mult.S_mul`. Applied proved pieces: A4
(`LeafQM.AV.exists_fibre_object`, from R1-R2), `model_dim`, H5's finiteness
(`faltingsHeight_coe`), E1 (`hom_of_common`: R9, T26, glue-ssbc), T8 (Poincaré, a leaf), E2's
`dim J₁(N) ≤ N²` (`LeafModCurves.dim_J1_le`, from T34), and the E3-E4 numerics (`transfer_core`,
from R19-R21). The non-CM disjunct is used (G6, NoCM). -/
theorem glueOutputs_of_leaves (r : ResearchLeaves) (t : TextbookLeaves)
    (hDim : DimBaseChange) (hBC : StableHeightBaseChange) (hJav : JavanpeykarJ1)
    (hAdd : HeightAdditivity) (hProd : IsogenousProduct) (hSimp : FibreSimple)
    (hTheta : ThetaPazuki) (hMod : ModularConstituent) :
    GlueAssembly.GlueOutputs ZInQ.Mult.S_mul := by
  -- A4: the moduli data and an object over every value
  obtain ⟨Y, Φ, π, h1, h2, hfib⟩ :=
    LeafQM.AV.exists_fibre_object (LeafAdopt.R1R2fp_of_rep r.r1r2)
  intro u hu
  obtain ⟨y, P, hP, hy⟩ := hfib (OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)))
  -- G2-G16 (missing piece 8): the field `L'`, the model `A`, the level `N`, `J₁(N)`
  obtain ⟨L, emb, A, N, J, hiso, hN0, hJ1, hNQ, hdQ, hCC⟩ := hMod Y Φ π h1 h2 u hu y P hP hy
  have hFib : FibreOver Y Φ π u L A := ⟨emb, y, P, hP, hy, hiso⟩
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  -- H5: the stable height of `A` is real
  have hfin := r.h5.1
  have hx : ZInQ.DefFaltings.stableFaltingsHeight A = ZInQ.DefFaltings.faltingsHeight A :=
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm
  -- G19 (missing piece 7): the theta point and Pazuki
  obtain ⟨K', z, hF1, hPaz⟩ := hTheta Y Φ π h1 h2 u hu L A hFib _ hx
  refine ⟨K', z, ZInQ.DefFaltings.faltingsHeight A, hF1, hPaz, Or.inl ?_⟩
  -- E1: a nonzero homomorphism `A → J₁(N)_{L'}`
  obtain ⟨f, hf⟩ := hom_of_common r t _ _ hCC
  -- G5-G6 (missing piece 6): `A` simple; T8: Poincaré
  obtain ⟨Z, g, hisoZ⟩ := t.t8 L.K _ _ (hSimp Y Φ π h1 h2 u hu L A hFib) f hf
  -- missing piece 5: `A × Z` and the isogeny `J₁(N)_{L'} → A × Z`
  obtain ⟨Pr, φ, hφ, hPprod, hdims⟩ := hProd L.K _ _ _ f g hisoZ
  -- E2: `dim J₁(N) ≤ N²`
  obtain ⟨gJ, hgJ, hgN⟩ := LeafModCurves.dim_J1_le t.t34 N hN0 J hJ1
  have hJLd : (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K).dim = (gJ : WithBot ℕ∞) :=
    (hDim ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)).trans hgJ
  have hALd : A.dim = ((2 : ℕ) : WithBot ℕ∞) := by rw [hA2]; rfl
  obtain ⟨gZ, hZd, hsum⟩ := hdims 2 gJ hALd hJLd
  -- heights (H5, missing pieces 2-4)
  have hxJ : ZInQ.DefFaltings.stableFaltingsHeight
      (((LeafAdopt.abVarEquiv ℚ).symm J).baseChange L.K) =
      ZInQ.DefFaltings.faltingsHeight ((LeafAdopt.abVarEquiv ℚ).symm J) := by
    rw [hBC ℚ L.K ((LeafAdopt.abVarEquiv ℚ).symm J)]
    exact (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
  have hyP := (ZInQ.DefFaltings.faltingsHeight_coe hfin Pr).symm
  have hzZ := (ZInQ.DefFaltings.faltingsHeight_coe hfin ((LeafAdopt.abVarEquiv L.K).symm Z)).symm
  have hadd := hAdd L.K Pr A ((LeafAdopt.abVarEquiv L.K).symm Z) hPprod _ _ _ hx hzZ hyP
  have hJb := hJav N hN0 J hJ1 _ (ZInQ.DefFaltings.faltingsHeight_coe hfin _).symm
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

/-- **G0. The leaves and the eight missing glue pieces imply `SixContactMin`** (no `sorry`). -/
theorem sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves)
    (m : G0Split.MissingPieces) : ZInQ.SixContactMin :=
  sixContactMin_of_glueOutputs (glueOutputs_of_leaves r t m.dimBaseChange
    m.stableHeightBaseChange m.javanpeykar m.additivity m.isogenousProduct m.fibreSimple
    m.thetaPazuki m.modularConstituent)

end HSyn

end

#print axioms HSyn.glueOutputs_of_leaves
#print axioms HSyn.sixContactMin_of_leaves
#print axioms HSyn.G0Split.transfer_core
#print axioms HSyn.G0Split.semisimpleBaseChange
