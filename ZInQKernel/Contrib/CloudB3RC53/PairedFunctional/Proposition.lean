import ZInQKernel.Contrib.CloudB3RC53.PairedFunctional.TameComplex

/-!
# RC53 PairedFunctional: the algebraic form of Proposition `ex:arith-paired-functional`

Manuscript `diophantine_zq.tex`, Proposition `ex:arith-paired-functional` (statement tex
L3704–3726, proof L3727–3880).

The proposition defines `λ_z = PD(−, j⁻¹ c(z))` (tex L3752–3754, L3850–3858) and asserts that it
has an integral closed representative over `S = 𝒪[G]`, with one fixed exponent `a` (in fact
`a = 0`, tex L3864–3869: "With the conventions of this paper the actual class `z` already
contains the fixed multiplier `L`. Thus the preceding construction permits `a = 0`"), and that
representatives built at different localizations have the same generic value (tex L3755–3758).

`PairedFunctionalIntegral` is the algebraic content of this argument, over an arbitrary
commutative ring `S`:

* the comparison `j : C_{U^⊥} → τ^* C_U` of complexes of `S`-modules, the conjugate transport
  `c : Z → τ^* C_U` and the class `z` (a degree-one cocycle);
* the retained duality, through its components `PD₁, PD₂, PD₃` with their Leibniz rules
  (`DEPARTURE`, form only, as in `ConeInverse.lean`);
* a finite family of tame local models (4.4) `(M_v, A_v, C_v, D_v)` with `D_v C_v = C_v A_v`, at
  each of which either the Frobenius operators `A_v, D_v` are units (tex L3730–3735, L3753–3754;
  at `(t)` the adjugate form, L3758–3760) or inertia minus one `C_v` is a unit (tex L3755–3765);
* the hypothesis that the cone of `j` is homotopy equivalent to the direct sum of these local
  models, each in an arbitrary degree shift `⟦n_v⟧` (the shifts are immaterial: contractibility is
  shift invariant, `contractible_shift`).

The last hypothesis is `ELLIOT`/`GLUE`: tex L3842–3846, "Over `S = 𝒪[G]` the only remaining
differences between the transported conditions and their orthogonal conditions occur at the active
and moving places. Their full local complexes have the integral contractions displayed above."
That the cone of a change of local conditions of Selmer complexes is the sum of the local complexes
at the changed places is the Selmer-complex formalism the text cites (Nekovář, Sections
6.2.5–6.2.8 and Theorem 6.3.4, UNVERIFIED); the genuine Galois Selmer complexes are not defined in
Lean (only the abstract model `selCx` of `SelmerPairing.lean`), so it enters
here as an explicit hypothesis. The old-support comparisons (tex L3766–3817) are integral homotopy
equivalences by `QuasiIsoFreeHomotopyInverse` and do not enter the cone.

Conclusion (PROVED from these hypotheses): there is an *integral* homotopy inverse
`e.inv = j⁻¹` over `S` such that `z^⊥ = j⁻¹ c(z)` is a cocycle, `j(z^⊥) − c(z)` is a boundary,
`λ_z` is closed, and any other homotopy inverse gives a functional differing from `λ_z` by a
coboundary. All maps are over `S`, so the integral representative needs no power of `2`
(exponent `a = 0`).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.PairedFunctional

open CategoryTheory Limits

/-- Two contractible complexes are homotopy equivalent (by zero maps). -/
noncomputable def homotopyEquivOfContractible {V : Type*} [Category V] [Preadditive V]
    {c : ComplexShape ℤ} {K L : HomologicalComplex V c} (hK : Homotopy (𝟙 K) 0)
    (hL : Homotopy (𝟙 L) 0) : HomotopyEquiv K L where
  hom := 0
  inv := 0
  homotopyHomInvId := (Homotopy.ofEq (by simp)).trans hK.symm
  homotopyInvHomId := (Homotopy.ofEq (by simp)).trans hL.symm

/-- **Proposition `ex:arith-paired-functional`, algebraic form** (tex L3704–3726, proof
L3727–3880). Over any commutative ring `S`: if the cone of the comparison `j : C' → C`
(`C' = C_{U^⊥}`, `C = τ^* C_U`) is homotopy equivalent to the direct sum of finitely many shifted tame
local models (4.4), each with Frobenius units or with an inertia unit (the active and moving
places; `ELLIOT`/`GLUE` hypothesis, tex L3842–3846), then there is a homotopy equivalence `e`
over `S` with `e.hom = j` such that, for the degree-one cocycle `z` and the conjugate transport
`c`:
(i) `z^⊥ = e.inv (c z)` is a cocycle (tex L3858–3859);
(ii) `j(z^⊥) − c(z)` is a boundary over `S` (tex L3859–3860);
(iii) `λ_z = PD(−, z^⊥)` is closed: it vanishes on `d(C_U^1)` (tex L3860–3863);
(iv) every homotopy equivalence `e'` with `e'.hom = j` gives a functional differing from `λ_z` by a
coboundary `w ↦ ε' PD₃(dw, y)` (tex L3755–3758: the same generic functional).
The representative is integral over `S` itself (exponent `a = 0`, tex L3864–3869).
Classification: PROVED (from the stated cone hypothesis). -/
def PairedFunctionalIntegral : Prop :=
  ∀ (S : Type) [CommRing S] (CU C' C Z : CochainComplex (ModuleCat.{0} S) ℤ) (j : C' ⟶ C)
    (c : Z ⟶ C) (z : Z.X 1) (pd1 : CU.X 1 →ₗ[S] C'.X 2 →ₗ[S] S)
    (pd2 : CU.X 2 →ₗ[S] C'.X 1 →ₗ[S] S) (pd3 : CU.X 3 →ₗ[S] C'.X 0 →ₗ[S] S) (ε ε' : S)
    (ι : Type) [Fintype ι] (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module S (M v)]
    (A Cin D : ∀ v, Module.End S (M v)) (hDC : ∀ v, D v * Cin v = Cin v * A v) (n : ι → ℤ),
    (∀ v, (IsUnit (A v) ∧ IsUnit (D v)) ∨ IsUnit (Cin v)) →
    Nonempty (HomotopyEquiv (CochainComplex.mappingCone j)
      (⨁ fun v => (tameComplex (A v) (Cin v) (D v) (hDC v))⟦n v⟧)) →
    (Z.d 1 2).hom z = 0 →
    (∀ w y, pd2 ((CU.d 1 2).hom w) y = ε * pd1 w ((C'.d 1 2).hom y)) →
    (∀ w y, pd2 w ((C'.d 0 1).hom y) = ε' * pd3 ((CU.d 2 3).hom w) y) →
    ∃ e : HomotopyEquiv C' C, e.hom = j ∧
      (C'.d 1 2).hom ((e.inv.f 1).hom ((c.f 1).hom z)) = 0 ∧
      (∃ b : C.X 0,
        (j.f 1).hom ((e.inv.f 1).hom ((c.f 1).hom z)) - (c.f 1).hom z = (C.d 0 1).hom b) ∧
      (∀ w : CU.X 1, pairedFunctional pd2 e.inv ((c.f 1).hom z) ((CU.d 1 2).hom w) = 0) ∧
      ∀ e' : HomotopyEquiv C' C, e'.hom = j → ∃ y : C'.X 0, ∀ w : CU.X 2,
        pairedFunctional pd2 e.inv ((c.f 1).hom z) w -
          pairedFunctional pd2 e'.inv ((c.f 1).hom z) w = ε' * pd3 ((CU.d 2 3).hom w) y

/-- A shift of a contractible cochain complex is contractible. -/
theorem contractible_shift {S : Type} [CommRing S] (K : CochainComplex (ModuleCat.{0} S) ℤ) (m : ℤ)
    (h : Nonempty (Homotopy (𝟙 K) 0)) : Nonempty (Homotopy (𝟙 (K⟦m⟧)) 0) := by
  obtain ⟨h⟩ := h
  have h' := h.shift m
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at h'
  exact ⟨h'⟩

theorem pairedFunctionalIntegral_proof : PairedFunctionalIntegral := by
  intro S _ CU C' C Z j c z pd1 pd2 pd3 ε ε' ι _ M _ _ A Cin D hDC n hunit ⟨eCone⟩ hz hL1 hL2
  -- the direct sum of the (shifted) local models is contractible
  have hsum : Nonempty (Homotopy
      (𝟙 (⨁ fun v => (tameComplex (A v) (Cin v) (D v) (hDC v))⟦n v⟧)) 0) :=
    contractible_biproduct _ fun v =>
      contractible_shift _ (n v)
        (tameComplexContractible_proof S (M v) (A v) (Cin v) (D v) (hDC v) (hunit v))
  -- hence so is the cone of `j`
  obtain ⟨hcone⟩ := contractible_of_homotopyEquiv eCone hsum
  obtain ⟨e, he⟩ := homotopyEquiv_of_cone_contractible j hcone
  subst he
  have hcz : (C.d 1 2).hom ((c.f 1).hom z) = 0 := by
    have h' := congrArg (fun f => ModuleCat.Hom.hom f z) (c.comm 1 2)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
    rw [h', hz, map_zero]
  exact ⟨e, rfl, zperp_cocycle e.inv hcz, image_zperp_sub_mem_boundary e hcz,
    pairedFunctional_closed pd1 pd2 ε hL1 e.inv hcz,
    fun e' he' => pairedFunctional_sub_eq_coboundary pd2 pd3 ε' hL2 e e' he'.symm hcz⟩

/-- **Non-vacuity of the cone hypothesis** of `PairedFunctionalIntegral`: for `j = 𝟙` and every
finite family of tame local models satisfying the unit hypotheses, the cone of `j` is homotopy
equivalent to the direct sum of the local models (both are contractible). PROVED. -/
theorem cone_hypothesis_satisfiable (S : Type) [CommRing S] (C : CochainComplex (ModuleCat.{0} S) ℤ)
    (ι : Type) [Fintype ι] (M : ι → Type) [∀ v, AddCommGroup (M v)] [∀ v, Module S (M v)]
    (A Cin D : ∀ v, Module.End S (M v)) (hDC : ∀ v, D v * Cin v = Cin v * A v)
    (hunit : ∀ v, (IsUnit (A v) ∧ IsUnit (D v)) ∨ IsUnit (Cin v)) (n : ι → ℤ) :
    Nonempty (HomotopyEquiv (CochainComplex.mappingCone (𝟙 C))
      (⨁ fun v => (tameComplex (A v) (Cin v) (D v) (hDC v))⟦n v⟧)) := by
  obtain ⟨h1⟩ := cone_id_contractible C
  obtain ⟨h2⟩ := contractible_biproduct (fun v => (tameComplex (A v) (Cin v) (D v) (hDC v))⟦n v⟧)
    fun v => contractible_shift _ (n v)
      (tameComplexContractible_proof S (M v) (A v) (Cin v) (D v) (hDC v) (hunit v))
  exact ⟨homotopyEquivOfContractible h1 h2⟩

/-- **Non-vacuity of the unit hypotheses**: a tame model with Frobenius units (`M = S`, `A = D = 1`,
`C = 0`) and one with an inertia unit (`M = S`, `C = 1`, `A = D = 0`) over any commutative ring.
PROVED. -/
theorem tame_unit_hypotheses_satisfiable (S : Type) [CommRing S] :
    ((1 : Module.End S S) * 0 = 0 * 1 ∧ IsUnit (1 : Module.End S S)) ∧
    ((0 : Module.End S S) * 1 = 1 * 0 ∧ IsUnit (1 : Module.End S S)) :=
  ⟨⟨by simp, isUnit_one⟩, ⟨by simp, isUnit_one⟩⟩

end ZInQ.Contrib.CloudB3RC53.PairedFunctional
