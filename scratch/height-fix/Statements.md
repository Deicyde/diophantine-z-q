# Verbatim copies of the statements (height-fix)

From `ZInQKernel/OneProof/H/TailY.lean` (namespace `ZInQ.HeightSplit`), at base 4d9056fc. VERIFIED (copied by script).

```lean
    simp only [algPt, Over.mk_hom]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.comp_algebraMap])

end Points

/-- **Semi-abelian identity component** of a group scheme `G` over a field `k` (applied below with
`k` algebraically closed): there is an open connected subgroup scheme `U ⊆ G` (necessarily the
identity component `G⁰`, an open and closed subgroup) and a faithfully flat homomorphism
`π : U → B` onto an abelian variety `B` whose kernel is a split torus `𝔾_m^r`, in the functor of
points: for every `k`-algebra `R` a group isomorphism `(Rˣ)^r ≅ ker(U(R) → B(R))`, natural in `R`
(by Yoneda, `ker π ≅ 𝔾_m^r` as group schemes). This is "`G⁰` is an extension of an abelian variety
by a torus" (SGA 7 IX Déf. 2.2 / 3.1, BLR 7.4, UNVERIFIED locators; over `k̄` every torus is split). -/
def HasSemiAbelianIdentityComponent {k : Type} [Field k] (G : Over (Spec (CommRingCat.of k)))
    [GrpObj G] : Prop :=
  ∃ (U : Over (Spec (CommRingCat.of k))) (_ : GrpObj U) (inc : U ⟶ G),
    IsOpenImmersion inc.left ∧ IsMonHom inc ∧ ConnectedSpace U.left ∧
    ∃ (B : PkgI3.AbVar k) (π : U ⟶ B.X), IsMonHom π ∧ Flat π.left ∧ Surjective π.left ∧
    ∃ (r : ℕ) (e : ∀ (R : Type) [CommRing R] [Algebra k R], (Fin r → Rˣ) →* (algPt k R ⟶ U)),
      (∀ (R : Type) [CommRing R] [Algebra k R], Function.Injective (e R)) ∧
      (∀ (R : Type) [CommRing R] [Algebra k R] (u : algPt k R ⟶ U),
        u ≫ π = 1 ↔ u ∈ (e R).range) ∧
      (∀ (R S : Type) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] (f : R →ₐ[k] S)
        (t : Fin r → Rˣ), e S (fun i => Units.map (f : R →* S) (t i)) = algPtMap f ≫ e R t)

section Fibres

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `κ̄(𝔭)`, an algebraic closure of the residue field of `𝓞_L` at `𝔭`. -/
abbrev ResBar (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] : Type := AlgebraicClosure 𝔭.ResidueField

/-- The geometric fibre `𝒢 ×_{𝓞_L} κ̄(𝔭)` of a group model at `𝔭`, a group scheme over `κ̄(𝔭)`. -/
noncomputable def geomFibre (𝒢 : GroupModel A L) (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    Over (Spec (CommRingCat.of (ResBar 𝔭))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (ResBar 𝔭))))).obj 𝒢.G

noncomputable instance (𝒢 : GroupModel A L) (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    GrpObj (geomFibre 𝒢 𝔭) :=
  Functor.grpObjObj

/-- **Semistable reduction everywhere** (applied to a Néron model `𝒩` of `A_L`): at every maximal
ideal `𝔭` of `𝓞_L`, the identity component of the geometric special fibre `𝒩_{κ̄(𝔭)}` is
semi-abelian. (SGA 7 IX Déf. 3.1/3.2, UNVERIFIED locators; the special fibre of the global Néron
model at `𝔭` is that of the Néron model over `𝓞_{L,𝔭}`: Néron models localize, BLR §1.2 Prop. 4,
number UNVERIFIED.) -/
def IsSemistable (𝒢 : GroupModel A L) : Prop :=
  ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], HasSemiAbelianIdentityComponent (geomFibre 𝒢 𝔭)

end Fibres

/-- **Faltings' stable height (original normalization `(i/2)^g`), the published definition**:
`x` is the height of the Néron model of `A_L` for some number field `L ⊇ K` over which `A` has
semistable reduction everywhere (Faltings 1983 §1; Deligne, Sém. Bourbaki 616, §1; UNVERIFIED

locators). The height of a group model `𝒩.height` is the kernel's (the metrized Hodge line
`⋀^g ω_𝒩`, `‖η‖²_σ = (i/2)^g ∫ η ∧ η̄`; one value for all metrizations given the uniqueness
half of AN3, `MetrizedModel.modelHeight_eq_of_model_eq`). Independence of `L` is
`isStableFaltingsHeight_unique` below (from SGA 7 IX 3.3). -/
def IsStableFaltingsHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L),
    𝒩.IsNeronModel ∧ IsSemistable 𝒩 ∧ 𝒩.height = (x : EReal)


UNVERIFIED: locators.md could not read it). Recalled display: `h(A) ≥ −(g/2) log(2π)` for every
abelian variety of dimension `g` over a number field, `h` the stable height in Deligne's
normalization `(i/2π)^g`, `h_D = h_F + (g/2) log π`. Stated in Deligne's normalization, the weaker of
the two readings (a Faltings-normalized display `h_F ≥ −(g/2) log 2π` implies it, as `h_D ≥ h_F`; the
Faltings-normalized reading is false for `E` with `j = 0`, `h_F ≈ −1.32`, so Deligne's is the one
meant). Residual risk: if Bost printed in a third normalization giving larger heights, e.g.
`(i/4π)^g`, this leaf would be stronger than the print; R21 itself needs only `h_F ≥ −(3/2)g`. -/
def BostLowerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsStableFaltingsHeight A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi

/-- **The form printed by Gaudron–Rémond** (Duke Math. J. 163 (2014), §9, proof of Lemma 9.1,

end R22Sec

/-! ## §H. Bonus: H-15, R19 (Gaudron–Rémond), the same identification -/

/-- **Leaf R19-GR over the published height** (Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4,
p. 2060; `κ` and `α(g) = 1024g³`, p. 2058; read by the locator audit): the kernel's
`R19_GaudronRemond` with `stableFaltingsHeight A = x` replaced by `IsStableFaltingsHeight A x`
(GR use the stable height in Faltings' original normalization). -/
def GaudronRemondThm14 : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsStableFaltingsHeight A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **H-15: R19 from Gaudron–Rémond over the published height and N1, SS1, SS2.** -/
theorem r19_of_leaves (hGR : GaudronRemondThm14) (hN1 : NeronModelExists)
```
