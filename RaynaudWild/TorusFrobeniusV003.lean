import RaynaudWild.FrobSpreadV006

/-!
# The residue Frobenius power acts on actual torus points by the `q^N`-power map

Let `k` be a finite field with `q` elements, `Ω / k` an algebraic extension with residue
Frobenius `σ` (`σ x = x ^ q`), `M` a commutative group (the character lattice) and `X` a
`k`-scheme locally of finite presentation (the special fibre of the Néron model, or its identity
component).  A split-torus presentation of `X` over `Ω` is a family of maps
`e_R : Hom(M, Rˣ) → X(R)` on `Ω`-algebras `R`, natural in `Ω`-algebra maps, where `Spec R` is a
`k`-scheme through `k → Ω → R` (the shape of the torus data of a semistable special fibre).

* `univ`, `ev`, `e_eq_ev_comp`: by naturality every `e_Ω(χ)` is the specialization of the single
  universal point `e_{Ω[M]}(univ)` along `ev_χ : Ω[M] → Ω`;
* `frob_comp_ev`: `σ ∘ ev_χ = ev_{σ ∘ χ} ∘ σ_M`, `σ_M` the coefficientwise action;
* the universal point is a `k`-morphism `Spec Ω[M] → X`; spreading out (`exists_frob_invariant`)
  gives `n` such that `σ ^ n!` fixes it;
* `frob_pow_torus_point`: there is `N ≥ 1` such that for every `χ`, precomposition of the actual
  `Ω`-point `e_Ω(χ)` with `Spec(σ ^ N)` is `e_Ω(χ ^ (q ^ N))`.
No descent, finite field of definition or Frobenius eigenvalue is assumed: they are derived.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace RaynaudWild.FrobDescent

variable {k Ω : Type} [Field k] [Finite k] [Field Ω] [Algebra k Ω]

/-- `Spec R` as a `k`-scheme, for an `Ω`-algebra `R`, through `k → Ω → R`. -/
def kPt (R : Type) [CommRing R] [Algebra Ω R] : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom ((algebraMap Ω R).comp (algebraMap k Ω))))

/-- A ring map compatible with the `k`-structures, as a `k`-morphism of spectra. -/
def kPtSemi {R S : Type} [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S] (φ : R →+* S)
    (hφ : φ.comp ((algebraMap Ω R).comp (algebraMap k Ω)) =
      (algebraMap Ω S).comp (algebraMap k Ω)) :
    kPt (k := k) (Ω := Ω) S ⟶ kPt (k := k) (Ω := Ω) R :=
  Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    change Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap Ω R).comp (algebraMap k Ω))) =
      Spec.map (CommRingCat.ofHom ((algebraMap Ω S).comp (algebraMap k Ω)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ])

/-- An `Ω`-algebra map as a `k`-morphism of spectra. -/
def kPtMap {R S : Type} [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S] (f : R →ₐ[Ω] S) :
    kPt (k := k) (Ω := Ω) S ⟶ kPt (k := k) (Ω := Ω) R :=
  kPtSemi (k := k) f.toRingHom (by
    ext a
    simp)

/-- The Galois action on `Ω`-points: precomposition with `Spec σ`. -/
def galK (σ : Ω ≃ₐ[k] Ω) : kPt (k := k) (Ω := Ω) Ω ⟶ kPt (k := k) (Ω := Ω) Ω :=
  kPtSemi (k := k) (σ : Ω →+* Ω) (by
    ext a
    simp)

variable (M : Type) [CommGroup M]

/-- The universal character `M → Ω[M]ˣ`. -/
def univ : M →* (MonoidAlgebra Ω M)ˣ := (MonoidAlgebra.of Ω M).toHomUnits

variable {M}

/-- Evaluation of the group ring at a character. -/
def ev (χ : M →* Ωˣ) : MonoidAlgebra Ω M →ₐ[Ω] Ω :=
  MonoidAlgebra.lift Ω Ω M ((Units.coeHom Ω).comp χ)

theorem ev_single (χ : M →* Ωˣ) (m : M) (a : Ω) :
    ev χ (MonoidAlgebra.single m a) = a * (χ m : Ω) := by
  simp [ev, MonoidAlgebra.lift_single]

theorem ev_univ (χ : M →* Ωˣ) : (Units.map (ev χ : MonoidAlgebra Ω M →* Ω)).comp (univ M) = χ := by
  ext m
  simp [univ, ev_single, MonoidAlgebra.of]

/-- The coefficientwise action of `τ` on `Ω[M]`. -/
def coeffAct (τ : Ω ≃ₐ[k] Ω) : MonoidAlgebra Ω M →+* MonoidAlgebra Ω M :=
  (MonoidAlgebra.mapAlgHom M (τ : Ω →ₐ[k] Ω)).toRingHom

theorem coeffAct_compat (τ : Ω ≃ₐ[k] Ω) :
    (coeffAct (M := M) τ).comp ((algebraMap Ω (MonoidAlgebra Ω M)).comp (algebraMap k Ω)) =
      (algebraMap Ω (MonoidAlgebra Ω M)).comp (algebraMap k Ω) := by
  ext a
  simp [coeffAct]

/-- **Semilinearity of evaluation.** `τ ∘ ev_χ = ev_{τ ∘ χ} ∘ τ_M`. -/
theorem frob_comp_ev (τ : Ω ≃ₐ[k] Ω) (χ : M →* Ωˣ) :
    (τ : Ω →+* Ω).comp (ev χ).toRingHom =
      (ev ((Units.map (τ : Ω →* Ω)).comp χ)).toRingHom.comp (coeffAct τ) := by
  apply MonoidAlgebra.ringHom_ext
  · intro r
    simp [ev_single, coeffAct]
  · intro m
    simp [ev_single, coeffAct]

variable (X : Over (Spec (CommRingCat.of k)))

/-- **Residue Frobenius power on actual torus points.** For a torus presentation `e` of a
`k`-scheme `X` locally of finite presentation, natural in `Ω`-algebra maps, there is `N ≥ 1`
such that `Spec(σ ^ N)` acts on every torus point `e_Ω(χ)` by `χ ↦ χ ^ (q ^ N)`. -/
theorem frob_pow_torus_point [Algebra.IsAlgebraic k Ω] (σ : Ω ≃ₐ[k] Ω)
    (hσ : ∀ x : Ω, σ x = x ^ Nat.card k) [LocallyOfFinitePresentation X.hom]
    (e : ∀ (R : Type) [CommRing R] [Algebra Ω R], (M →* Rˣ) → (kPt (k := k) (Ω := Ω) R ⟶ X))
    (he : ∀ (R S : Type) [CommRing R] [Algebra Ω R] [CommRing S] [Algebra Ω S]
      (f : R →ₐ[Ω] S) (χ : M →* Rˣ),
      e S ((Units.map (f : R →* S)).comp χ) = kPtMap f ≫ e R χ) :
    ∃ N : ℕ, 0 < N ∧ ∀ χ : M →* Ωˣ,
      galK (σ ^ N) ≫ e Ω χ = e Ω (χ ^ (Nat.card k ^ N)) := by
  have hx : (e (MonoidAlgebra Ω M) (univ M)).left ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (MonoidAlgebra Ω M))) := by
    rw [Over.w (e (MonoidAlgebra Ω M) (univ M))]
    change Spec.map (CommRingCat.ofHom
      ((algebraMap Ω (MonoidAlgebra Ω M)).comp (algebraMap k Ω))) = _
    rw [← IsScalarTower.algebraMap_eq]
  obtain ⟨n, hn⟩ := exists_frob_invariant σ M hσ X (e (MonoidAlgebra Ω M) (univ M)).left hx
  refine ⟨n.factorial, Nat.factorial_pos n, fun χ => ?_⟩
  have hspec : ∀ ψ : M →* Ωˣ, e Ω ψ = kPtMap (ev ψ) ≫ e (MonoidAlgebra Ω M) (univ M) := by
    intro ψ
    have h := he (MonoidAlgebra Ω M) Ω (ev ψ) (univ M)
    rw [ev_univ] at h
    exact h
  have hχ' : (Units.map ((σ ^ n.factorial : Ω ≃ₐ[k] Ω) : Ω →* Ω)).comp χ =
      χ ^ (Nat.card k ^ n.factorial) := by
    ext m
    simp [pow_apply_eq σ hσ]
  have hsemi : galK (σ ^ n.factorial) ≫ kPtMap (ev χ) =
      kPtMap (ev (χ ^ (Nat.card k ^ n.factorial))) ≫
        kPtSemi (coeffAct (σ ^ n.factorial)) (coeffAct_compat _) := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom ((σ ^ n.factorial : Ω ≃ₐ[k] Ω) : Ω →+* Ω)) ≫
        Spec.map (CommRingCat.ofHom (ev χ).toRingHom) =
      Spec.map (CommRingCat.ofHom (ev (χ ^ (Nat.card k ^ n.factorial))).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (coeffAct (σ ^ n.factorial)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      frob_comp_ev, hχ']
  have hinv : kPtSemi (coeffAct (σ ^ n.factorial)) (coeffAct_compat _) ≫
      e (MonoidAlgebra Ω M) (univ M) = e (MonoidAlgebra Ω M) (univ M) := by
    apply Over.OverMorphism.ext
    exact hn
  calc galK (σ ^ n.factorial) ≫ e Ω χ
      = galK (σ ^ n.factorial) ≫ (kPtMap (ev χ) ≫ e (MonoidAlgebra Ω M) (univ M)) := by
        rw [← hspec]
    _ = (galK (σ ^ n.factorial) ≫ kPtMap (ev χ)) ≫ e (MonoidAlgebra Ω M) (univ M) :=
        (Category.assoc _ _ _).symm
    _ = (kPtMap (ev (χ ^ (Nat.card k ^ n.factorial))) ≫
          kPtSemi (coeffAct (σ ^ n.factorial)) (coeffAct_compat _)) ≫
          e (MonoidAlgebra Ω M) (univ M) := by rw [hsemi]
    _ = kPtMap (ev (χ ^ (Nat.card k ^ n.factorial))) ≫
          (kPtSemi (coeffAct (σ ^ n.factorial)) (coeffAct_compat _) ≫
            e (MonoidAlgebra Ω M) (univ M)) := Category.assoc _ _ _
    _ = kPtMap (ev (χ ^ (Nat.card k ^ n.factorial))) ≫ e (MonoidAlgebra Ω M) (univ M) := by
        rw [hinv]
    _ = e Ω (χ ^ (Nat.card k ^ n.factorial)) := (hspec _).symm

end RaynaudWild.FrobDescent
