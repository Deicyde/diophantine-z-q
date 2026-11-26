import ZInQKernel.Contrib.CloudB3E2Norm.H20Untwisted
import ZInQKernel.Contrib.CloudB3E2Norm.RingClassKS

/-!
# The `ℚ̄ → K̄` Heegner dictionary: point-level compatibilities from field-level data

Manuscript `diophantine_zq.tex`, tex 2914–2936 (the Heegner points `y_d = π(x_d) ∈ E(H_d)` over the
ring class fields, the transfer `Tr_{H_{dq}/H_d}` and the Frobenius `σ_q`) and tex 4157–4170.

`H20Untwisted.heegnerTransportOn_of_dictionaryU` transports the Heegner point data
`HeegnerPointData E` (abstract, in `ℚ̄`: its fields `H`, `y`, `relGal`, `frob` carry no stated
relations) into the untwisted ambient module of points `ℤ[Δ] ⊗ E(K_{S₀})` from a point-level
dictionary along `κ : ℚ̄ → K̄`. Here every point-level hypothesis is **proved** from field-level
data, which is all that remains named:

* (i) `hy`: `D.y n` has coordinates in `D.H n` (the Heegner point is defined over the ring class
  field);
* (ii) `hκS`: `κ(D.H n) ⊆ K_{S₀}`; `kappa_mem_KS_of_ringClass` (PROVED) derives it from
  `κ(D.H n) ⊆ H_{O_n}` (Tau Ceti's ring class field of the order of conductor `n`, read in `K̄`) and
  the primes dividing the conductor lying in `S₀` (`RingClassKS.ringClassField_le_KS`);
* (iii) `hτ`: a bijection `e : H_P/U ≃ relGal d q` with `κ ∘ (e τ) = t_τ ∘ κ` on `D.H (dq)`
  (the lifts
  of `Gal(H_{dq}/H_d)` match the transversal);
* (iv) `hf`: `κ ∘ frob = σ ∘ κ` on `D.H d`, with `D.H d` stable under `frob⁻¹`
  (e.g. `H_d/ℚ` normal).

Declarations:

* `castPt_some`, `compQ_zero`, `compQ_some` (PROVED): `compQ κ` on coordinates.
* `realize` (definition), **`compQ_realize`** (PROVED): the point `P_n ∈ E(K_{S₀})` realizing
  `κ(D.y n)`.
* **`compQ_map_of_agree`** (PROVED): if `κ ∘ τ = g ∘ κ` on `D.H n`, then `κ(τ y_n) = g · P_n`.
* `agree_inv` (PROVED): the agreement passes to inverses on a stable field.
* **`heegnerTransportOn_of_fields`** (PROVED): `HeegnerTransportOn` into the untwisted ambient
  module
  with `y_R = 1 ⊗ P_{dq}`, `y_P = 1 ⊗ P_d` from (i)–(iv); **`hnorm_of_fields`** (PROVED): the input
  `hnorm` of `h1_shapiro` from the unweighted norm relations (4.1) of the datum (derived from the
  Cai–Chen–Liu print `CCLThm2_15AppliedWithUnits` when `D_K < -4`; via
  `hnorm_of_normRelations_on`) and (i)–(iv).

Kinds: definitions and PROVED; (i)–(iv) are the GLUE (the CM-point construction of the Heegner
points).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.NormCochain

open ZInQ.Manuscript.RC.PrintsArith
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Contrib.CloudB3RC53.RankCounts (unramifiedOutside IsUnramifiedOutside)
open NumberField IsDedekindDomain TensorProduct WeierstrassCurve
open scoped WeierstrassCurve

attribute [local instance] ptSAction

set_option linter.unusedSectionVars false

/-! ### `compQ` on coordinates -/

section Coords

/-- A cast of points along an equality of curves keeps the coordinates. Kind: PROVED. -/
theorem castPt_some {L : Type} [Field L] [DecidableEq L] {V V' : WeierstrassCurve L} (e : V = V')
    {x y : L}
    (h : V.toAffine.Nonsingular x y) :
    AddEquiv.cast (M := fun V : WeierstrassCurve L => V.toAffine.Point) e
        (Affine.Point.some x y h) =
      Affine.Point.some x y (e ▸ h) := by
  subst e
  rfl

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)

/-- `compQ κ` on the zero point. Kind: PROVED. -/
theorem compQ_zero (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) : compQ (K := K) E κ 0 = 0 := map_zero _

/-- `compQ κ` on coordinates. Kind: PROVED. -/
theorem compQ_some (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) {x y : Qbar}
    (h : (E⁄Qbar).toAffine.Nonsingular x y) :
    ∃ h' : ((E.baseChange K).baseChange (AlgebraicClosure K)).toAffine.Nonsingular (κ x) (κ y),
      compQ (K := K) E κ (.some x y h) = .some (κ x) (κ y) h' := by
  classical
  change ∃ h', AddEquiv.cast (M := fun V : WeierstrassCurve (AlgebraicClosure K) =>
    V.toAffine.Point) (bc_eq E).symm (Affine.Point.map (W' := E) κ (.some x y h)) = _
  rw [Affine.Point.map_some, castPt_some]
  exact ⟨_, rfl⟩

end Coords

/-! ### Realization and Galois agreement -/

section Realize

open scoped Classical

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  (S₀ : Set (HeightOneSpectrum (𝓞 K))) (κ : Qbar →ₐ[ℚ] AlgebraicClosure K)
  (L : IntermediateField ℚ Qbar) (hκS : ∀ x ∈ L, κ x ∈ unramifiedOutside K S₀)

include hκS in
/-- A point of `E(ℚ̄)` with coordinates in `L` (`κ(L) ⊆ K_{S₀}`) is realized in `E(K_{S₀})` along
`κ`. Kind: PROVED. -/
theorem exists_realize (Y : (E⁄Qbar).toAffine.Point)
    (hY : ∃ Y' : (E.baseChange L).toAffine.Point, Affine.Point.map (W' := E) L.val Y' = Y) :
    ∃ P : PtS K S₀ (E.baseChange K), incS S₀ (E.baseChange K) P = compQ E κ Y := by
  obtain ⟨Y', rfl⟩ := hY
  rcases Y' with _ | ⟨x, y, h⟩
  · exact ⟨0, by rw [← Affine.Point.zero_def, map_zero, map_zero, map_zero]⟩
  · rw [Affine.Point.map_some]
    obtain ⟨h', hc⟩ := compQ_some E κ ((E.toAffine.baseChange_nonsingular L.val.injective x y).2 h)
    rw [hc]
    refine (Affine.Point.exists_map_eq_iff _ (unramifiedOutside K S₀).val).2 ⟨?_, ?_⟩
    · exact ⟨⟨_, hκS _ x.2⟩, rfl⟩
    · exact ⟨⟨_, hκS _ y.2⟩, rfl⟩

/-- **The realization `P ∈ E(K_{S₀})` of `κ(Y)`**. Kind: definition. -/
def realize (Y : (E⁄Qbar).toAffine.Point)
    (hY : ∃ Y' : (E.baseChange L).toAffine.Point, Affine.Point.map (W' := E) L.val Y' = Y) :
    PtS K S₀ (E.baseChange K) :=
  Classical.choose (exists_realize E S₀ κ L hκS Y hY)

theorem compQ_realize (Y : (E⁄Qbar).toAffine.Point)
    (hY : ∃ Y' : (E.baseChange L).toAffine.Point, Affine.Point.map (W' := E) L.val Y' = Y) :
    compQ E κ Y = incS S₀ (E.baseChange K) (realize E S₀ κ L hκS Y hY) :=
  (Classical.choose_spec (exists_realize E S₀ κ L hκS Y hY)).symm

/-- **Galois agreement on `L` gives agreement on points with coordinates in `L`** (PROVED): if
`κ(τ x) = g(κ x)` for `x ∈ L` (`g ∈ G_{K,S₀}` acting on `K_{S₀}`), then `κ(τ Y) = g · P`. -/
theorem compQ_map_of_agree (Y : (E⁄Qbar).toAffine.Point)
    (hY : ∃ Y' : (E.baseChange L).toAffine.Point, Affine.Point.map (W' := E) L.val Y' = Y)
    (τ : GalQ) (g : GKS K S₀)
    (hag : ∀ x (hx : x ∈ L), κ (τ x) = (galS K S₀ g ⟨κ x, hκS x hx⟩ : AlgebraicClosure K)) :
    compQ E κ (Affine.Point.map τ.toAlgHom Y) =
      incS S₀ (E.baseChange K) (g • realize E S₀ κ L hκS Y hY) := by
  have hP := compQ_realize E S₀ κ L hκS Y hY
  set P := realize E S₀ κ L hκS Y hY
  obtain ⟨Y', rfl⟩ := hY
  rcases Y' with _ | ⟨x, y, h⟩
  · have hP0 : P = 0 := by
      apply incS_injective S₀ (E.baseChange K)
      rw [← hP, ← Affine.Point.zero_def, map_zero, map_zero, map_zero]
    rw [hP0, smul_zero, ← Affine.Point.zero_def, map_zero, map_zero, map_zero, map_zero]
  · rw [Affine.Point.map_some] at hP ⊢
    rw [Affine.Point.map_some]
    obtain ⟨h₁, hc₁⟩ := compQ_some E κ ((E.toAffine.baseChange_nonsingular L.val.injective x y).2 h)
    rw [hc₁] at hP
    rcases hPc : P with _ | ⟨px, py, hp⟩
    · rw [hPc, ← Affine.Point.zero_def, map_zero] at hP
      exact absurd hP.symm (by simp)
    · rw [hPc, Affine.Point.map_some] at hP
      simp only [Affine.Point.some.injEq] at hP
      obtain ⟨hx, hy⟩ := hP
      obtain ⟨h₂, hc₂⟩ := compQ_some E κ (x := τ.toAlgHom (L.val x)) (y := τ.toAlgHom (L.val y))
        ((E.toAffine.baseChange_nonsingular τ.toAlgHom.injective _ _).2
          ((E.toAffine.baseChange_nonsingular L.val.injective x y).2 h))
      rw [hc₂, ptS_smul_def, Affine.Point.map_some, Affine.Point.map_some]
      simp only [Affine.Point.some.injEq]
      have ex : (px : AlgebraicClosure K) = κ x := hx.symm
      have ey : (py : AlgebraicClosure K) = κ y := hy.symm
      refine ⟨?_, ?_⟩
      · change κ (τ x) = ((galS K S₀ g px : unramifiedOutside K S₀) : AlgebraicClosure K)
        rw [hag x x.2]
        congr 2
        exact Subtype.ext ex.symm
      · change κ (τ y) = ((galS K S₀ g py : unramifiedOutside K S₀) : AlgebraicClosure K)
        rw [hag y y.2]
        congr 2
        exact Subtype.ext ey.symm

/-- **The agreement passes to inverses on a stable field** (PROVED). -/
theorem agree_inv (τ : GalQ) (g : GKS K S₀) (hstab : ∀ x ∈ L, τ⁻¹ x ∈ L)
    (hag : ∀ x (hx : x ∈ L), κ (τ x) = (galS K S₀ g ⟨κ x, hκS x hx⟩ : AlgebraicClosure K)) :
    ∀ x (hx : x ∈ L), κ (τ⁻¹ x) = (galS K S₀ g⁻¹ ⟨κ x, hκS x hx⟩ : AlgebraicClosure K) := by
  intro x hx
  have h1 := hag (τ⁻¹ x) (hstab x hx)
  have h2 : τ (τ⁻¹ x) = x := AlgEquiv.apply_symm_apply τ x
  rw [h2] at h1
  have h3 : (⟨κ x, hκS x hx⟩ : unramifiedOutside K S₀) =
      galS K S₀ g ⟨κ (τ⁻¹ x), hκS _ (hstab x hx)⟩ := Subtype.ext h1
  rw [h3]
  change _ = (((galS K S₀ g).symm (galS K S₀ g ⟨κ (τ⁻¹ x), hκS _ (hstab x hx)⟩) :
    unramifiedOutside K S₀) : AlgebraicClosure K)
  rw [AlgEquiv.symm_apply_apply]

end Realize

/-! ### The ring class fields lie in `K_{S₀}` -/

section RingClass

open TauCeti.GlobalNumberFields

variable {K : Type} [Field K] [NumberField K] (S₀ : Set (HeightOneSpectrum (𝓞 K)))
  (κ : Qbar →ₐ[ℚ] AlgebraicClosure K) (L : IntermediateField ℚ Qbar)

/-- **(ii) from the ring class field** (PROVED): if `κ(L)` lies in Tau Ceti's ring class field of
an order `O` (read in `K̄`) and `S₀` contains the primes dividing the conductor of `O`, then
`κ(L) ⊆ K_{S₀}` (`RingClassKS.ringClassField_le_KS`). -/
theorem kappa_mem_KS_of_ringClass (O : NumberFieldOrder K)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ O.conductor → v ∈ S₀)
    (hL : ∀ x ∈ L, κ x ∈ toAlgClosure (TauCeti.ClassFieldTheory.ringClassField O)) :
    ∀ x ∈ L, κ x ∈ unramifiedOutside K S₀ :=
  fun x hx => ringClassField_le_KS O S₀ hS (hL x hx)

end RingClass

/-! ### The transport from the field-level dictionary -/

section Transport

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) [(E.baseChange K).IsElliptic]
  {Δ : Type} [CommGroup Δ] [Finite Δ]
  (HP : Subgroup (GKS K S)) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP)

/-- **`HeegnerTransportOn` from the field-level dictionary** (PROVED; tex 2914–2936): along
`κ : ℚ̄ → K̄`, with
* (i) `hyR`, `hyP` (GLUE, tex 2915–2917: `y_n = π(x_n) ∈ E(H_n)`): `D.y (dq)`, `D.y d` have
  coordinates in `D.H (dq)`, `D.H d`;
* (ii) `hκR`, `hκP` (GLUE, tex 2914–2917; from the ring class fields by
  `kappa_mem_KS_of_ringClass`):
  `κ(D.H (dq)), κ(D.H d) ⊆ K_{S₀}`;
* (iii) `e`, `hτ` (GLUE, tex 2924–2929: `relGal d q` lifts `Gal(H_{dq}/H_d)`): `κ ∘ (e τ) = t_τ ∘ κ`
  on `D.H (dq)`;
* (iv) `hf`, `hstab` (GLUE, tex 2931–2932: `frob d q` lifts `σ_q ∈ Gal(H_d/K)`): `κ ∘ frob = σ ∘ κ`
  on `D.H d`, `D.H d` stable under `frob⁻¹`,
the Heegner point data is transported into the untwisted ambient module with
`y_R = 1 ⊗ P_{dq}`, `y_P = 1 ⊗ P_d` (`P_n` the realizations). -/
theorem heegnerTransportOn_of_fields (D : HeegnerPointData E) (d q : ℕ) (σ : GKS K S)
    (κ : Qbar →ₐ[ℚ] AlgebraicClosure K)
    (hyR : ∃ Y' : (E.baseChange (D.H (d * q))).toAffine.Point,
      Affine.Point.map (W' := E) (D.H (d * q)).val Y' = D.y (d * q))
    (hyP : ∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
      Affine.Point.map (W' := E) (D.H d).val Y' = D.y d)
    (hκR : ∀ x ∈ D.H (d * q), κ x ∈ unramifiedOutside K S₀)
    (hκP : ∀ x ∈ D.H d, κ x ∈ unramifiedOutside K S₀)
    (e : HP ⧸ U ≃ D.relGal d q)
    (hτ : ∀ τ (x) (hx : x ∈ D.H (d * q)), κ ((e τ).1 x) =
      (galS K S₀ (inflMap K hS (t τ : GKS K S)) ⟨κ x, hκR x hx⟩ : AlgebraicClosure K))
    (hf : ∀ x (hx : x ∈ D.H d), κ (D.frob d q x) =
      (galS K S₀ (inflMap K hS σ) ⟨κ x, hκP x hx⟩ : AlgebraicClosure K))
    (hstab : ∀ x ∈ D.H d, (D.frob d q)⁻¹ x ∈ D.H d) :
    HeegnerTransportOn (ambRhoU hS (E.baseChange K) Δ) HP U t D d q σ
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ realize E S₀ κ (D.H (d * q)) hκR (D.y (d * q)) hyR :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K))
      ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ realize E S₀ κ (D.H d) hκP (D.y d) hyP :
        MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K)) := by
  refine heegnerTransportOn_of_dictionaryU E hS HP U t D d q σ κ _ _
    (compQ_realize E S₀ κ _ hκR _ hyR) (compQ_realize E S₀ κ _ hκP _ hyP) e
    (fun τ => compQ_map_of_agree E S₀ κ _ hκR _ hyR (e τ).1 _ (hτ τ))
    (compQ_map_of_agree E S₀ κ _ hκP _ hyP (D.frob d q) _ hf) ?_
  rw [map_inv]
  exact compQ_map_of_agree E S₀ κ _ hκP _ hyP (D.frob d q)⁻¹ _
    (agree_inv S₀ κ _ hκP (D.frob d q) (inflMap K hS σ) hstab hf)

end Transport

/-! ### The norm relation from the print and the field-level dictionary -/

section Norm

variable {K : Type} [Field K] [NumberField K] (E : WeierstrassCurve ℚ)
  {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) [(E.baseChange K).IsElliptic]
  {Δ : Type} [CommGroup Δ] [Finite Δ]
  (HP : Subgroup (GKS K S)) (U : Subgroup HP) [Fintype (HP ⧸ U)] (t : HP ⧸ U → HP)

/-- `1 ⊗ P` in the untwisted ambient module. Kind: definition. -/
abbrev yPt (P : PtS K S₀ (E.baseChange K)) : ambU hS (E.baseChange K) Δ :=
  ((1 : MonoidAlgebra ℤ Δ) ⊗ₜ P : MonoidAlgebra ℤ Δ ⊗[ℤ] PtS K S₀ (E.baseChange K))

/-- **The norm relation (4.1) in the twisted-transfer form for the realized Heegner points**
(PROVED from the unweighted norm relations and the field-level dictionary (i)–(iv), tex 2914–2936):
for a datum `D` satisfying the unweighted norm relations (derived from the print
`CCLThm2_15AppliedWithUnits` by `CCLThm2_15AppliedWithUnits.exists_normRelations` when the unit
index is one, `D_K < -4`), admissible `(d, q)` with `q`
split, `∑_τ ρ₀(t_τ) y_R = a_q y_P − ρ₀(σ) y_P − ρ₀(σ)⁻¹ y_P` with `y_R = 1 ⊗ P_{dq}`,
`y_P = 1 ⊗ P_d` — the input `hnorm` of `h1_shapiro`. -/
theorem hnorm_of_fields (D : HeegnerPointData E) (hD : D.NormRelations) {d q : ℕ}
    (hadm : D.Admissible d q) (hsplit : jacobiSym D.DK q = 1) (σ : GKS K S)
    (κ : Qbar →ₐ[ℚ] AlgebraicClosure K)
    (hyR : ∃ Y' : (E.baseChange (D.H (d * q))).toAffine.Point,
      Affine.Point.map (W' := E) (D.H (d * q)).val Y' = D.y (d * q))
    (hyP : ∃ Y' : (E.baseChange (D.H d)).toAffine.Point,
      Affine.Point.map (W' := E) (D.H d).val Y' = D.y d)
    (hκR : ∀ x ∈ D.H (d * q), κ x ∈ unramifiedOutside K S₀)
    (hκP : ∀ x ∈ D.H d, κ x ∈ unramifiedOutside K S₀)
    (e : HP ⧸ U ≃ D.relGal d q)
    (hτ : ∀ τ (x) (hx : x ∈ D.H (d * q)), κ ((e τ).1 x) =
      (galS K S₀ (inflMap K hS (t τ : GKS K S)) ⟨κ x, hκR x hx⟩ : AlgebraicClosure K))
    (hf : ∀ x (hx : x ∈ D.H d), κ (D.frob d q x) =
      (galS K S₀ (inflMap K hS σ) ⟨κ x, hκP x hx⟩ : AlgebraicClosure K))
    (hstab : ∀ x ∈ D.H d, (D.frob d q)⁻¹ x ∈ D.H d) :
    ∑ τ : HP ⧸ U, ambRhoU hS (E.baseChange K) Δ (t τ : GKS K S)
        (yPt E hS (Δ := Δ) (realize E S₀ κ (D.H (d * q)) hκR (D.y (d * q)) hyR)) =
      (E.LFunction q : ℤ) • yPt E hS (Δ := Δ) (realize E S₀ κ (D.H d) hκP (D.y d) hyP) -
        ambRhoU hS (E.baseChange K) Δ σ
          (yPt E hS (Δ := Δ) (realize E S₀ κ (D.H d) hκP (D.y d) hyP)) -
        ambRhoU hS (E.baseChange K) Δ σ⁻¹
          (yPt E hS (Δ := Δ) (realize E S₀ κ (D.H d) hκP (D.y d) hyP)) :=
  hnorm_of_normRelations_on (ambRhoU hS (E.baseChange K) Δ) HP U t D hD hadm hsplit
    (heegnerTransportOn_of_fields E hS HP U t D d q σ κ hyR hyP hκR hκP e hτ hf hstab)

end Norm

end ZInQ.Contrib.CloudB3E2.NormCochain
