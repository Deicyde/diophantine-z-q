import ZInQKernel.Contrib.CloudB3RC53.CommonCoordinate.Naturality
import ZInQKernel.Contrib.CloudB3RC53.SelmerDuality.NonVacuity

/-!
# Common coordinate, part 7: the retained pairing from place-by-place retention data

Lemma `ex:arith-common-coordinate` (`diophantine_zq.tex`, tex L4159–4166):

> Let `i : C_P → C_R` be the primitive-to-relaxed map, and let `j : C_S → C_{P⊥}` be the paired
> strict-to-primitive map. All old orthogonal conditions and their homotopies are retained. At `q`
> these are the maps from the unramified condition to the full condition and from zero to the
> unramified condition.

Repair of CommonCoordinate review items 3 and 8: `RetainedPairing` (`Naturality.lean`) assumed the
equality `h_R(u, f_P v) = h_P(f_S u, v)` directly. `PlaceRetention` states the retention datum place
by place, in the shape of the support-change data (`SelmerDuality/SupportChange.lean`):

* the local conditions decompose by places: projections of `U_R`, `U_P`, `U_S`, `U_{P⊥}` onto the
  old local conditions `U_v`, `U_v^⊥` at every old place `v`, and onto the full complex `L_q`, the
  unramified condition `U_q^{ur}` (an `UnramifiedNewPlace`) and its orthogonal at `q`;
* the isotropy homotopies are the sums of the per-place homotopies `h_v` (the **same** `h_v` for
  both pairings) and, for the primitive pairing, the homotopy `h_q` at `q` (on the strict side the
  condition at `q` is zero, so `h_R` has no `q`-term);
* every old condition is retained: `f_P` and `f_S` are the identity on every old summand; at `q`,
  `f_P` is the inclusion `U_q^{ur} → L_q` and `f_S` is `0 → U_q^{ur}`.

`PlaceRetention.toRetainedPairing` then PROVES the retained-homotopy equality and produces the
`RetainedPairing` consumed by `cup_naturality` and `pairedFunctional_natural`.

Non-vacuity of the model itself (LESSON 2): `examplePlaceRetention`, over Selmer data with
`ι_R = id` (so the functionals below are nonzero), one old place and the zero new place.

Caveat: the new place `NP : UnramifiedNewPlace S` requires degreewise isomorphisms of the full local
complex at `q` with the 3-term tame model `M → M ⊕ M → M`; genuine continuous cochains
`C^•(G_{K_q}, M)` are only quasi-isomorphic to it (they are nonzero in every degree `≥ 0`), so this
hypothesis is consistent (zero witnesses) but not instantiable by genuine continuous cochains;
re-pointing to the genuine Galois support data is pending.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.CommonCoordinate

open CategoryTheory ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

universe u

variable {S : Type u} [CommRing S]

/-- **Place-by-place retention data** for the primitive/relaxed and strict/orthogonal Selmer
complexes (tex L4159–4166). `DR` is the relaxed data (condition `U_R`), `DPp` the orthogonal data
(condition `U_{P⊥}`), `fP : U_P → U_R` and `fS : U_S → U_{P⊥}` the condition maps.

Caveat: the field `NP : UnramifiedNewPlace S` requires degreewise isomorphisms of the full local
complex at `q` with the 3-term tame model `M → M ⊕ M → M`; genuine continuous cochains
`C^•(G_{K_q}, M)` are only quasi-isomorphic to it (they are nonzero in every degree `≥ 0`), so this
hypothesis is consistent (zero witnesses) but not instantiable by genuine continuous cochains;
re-pointing to the genuine Galois support data is pending. -/
structure PlaceRetention (DR DPp : SelData S) {UP US : GCx S} (fP : GHom UP DR.U)
    (fS : GHom US DPp.U) where
  /-- Global target. -/
  E : GCx S
  /-- Local target. -/
  EL : GCx S
  /-- Restriction on the target. -/
  resE : GHom E EL
  /-- Global cup product (shared by both pairings). -/
  cupG : GPair DPp.G DR.G E
  /-- Local cup product (shared by both pairings). -/
  cupL : GPair DPp.L DR.L EL
  compat : ∀ (i j k i' j' k' : ℤ) (h : i + j = k) (h' : i' + j' = k') (hi : i = i') (hj : j = j')
    (hk : k = k') (a : DPp.G.X i) (b : DR.G.X j),
    resE.f k k' hk (cupG.P i j k h a b) =
      cupL.P i' j' k' h' (DPp.res.f i i' hi a) (DR.res.f j j' hj b)
  /-- The index type of places. -/
  ι : Type
  /-- The old places. -/
  old : Finset ι
  /-- The old local condition at `v` (primitive/relaxed side). -/
  Uo : ι → GCx S
  /-- The old orthogonal local condition at `v` (strict/orthogonal side). -/
  Uo' : ι → GCx S
  /-- The old isotropy homotopy at `v`. -/
  hv : ∀ (v : ι) (i j k : ℤ), i + j = k + 1 → (Uo' v).X i →ₗ[S] (Uo v).X j →ₗ[S] EL.X k
  /-- The new place `q`: full complex `L_q` and unramified condition `U_q^{ur}`. -/
  NP : UnramifiedNewPlace S
  /-- The orthogonal of the unramified condition at `q`. -/
  Uq' : GCx S
  /-- The isotropy homotopy at `q` for the primitive pairing. -/
  hq : ∀ i j k : ℤ, i + j = k + 1 → Uq'.X i →ₗ[S] NP.Uq.X j →ₗ[S] EL.X k
  /-- Old components of `U_R`. -/
  pR : ∀ (v : ι) (j : ℤ), DR.U.X j →ₗ[S] (Uo v).X j
  /-- Old components of `U_P`. -/
  pP : ∀ (v : ι) (j : ℤ), UP.X j →ₗ[S] (Uo v).X j
  /-- Old components of `U_S`. -/
  pS : ∀ (v : ι) (i : ℤ), US.X i →ₗ[S] (Uo' v).X i
  /-- Old components of `U_{P⊥}`. -/
  pPp : ∀ (v : ι) (i : ℤ), DPp.U.X i →ₗ[S] (Uo' v).X i
  /-- The `q`-component of `U_R` (the full complex at `q`). -/
  qR : ∀ j : ℤ, DR.U.X j →ₗ[S] NP.Lq.X j
  /-- The `q`-component of `U_P` (the unramified condition). -/
  qP : ∀ j : ℤ, UP.X j →ₗ[S] NP.Uq.X j
  /-- The `q`-component of `U_{P⊥}`. -/
  qPp : ∀ i : ℤ, DPp.U.X i →ₗ[S] Uq'.X i
  /-- The relaxed homotopy on `U_S × U_R`. -/
  hR : ∀ i j k : ℤ, i + j = k + 1 → US.X i →ₗ[S] DR.U.X j →ₗ[S] EL.X k
  /-- … is the sum of the old per-place homotopies (the strict condition at `q` is zero). -/
  hR_eq : ∀ (i j k : ℤ) (h : i + j = k + 1) (x : US.X i) (y : DR.U.X j),
    hR i j k h x y = ∑ v ∈ old, hv v i j k h (pS v i x) (pR v j y)
  isoR : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (x : US.X i) (y : DR.U.X j),
    EL.d k k₁ hk (hR i j k h x y) + hR i₁ j k₁ (by omega) (US.d i i₁ hi x) y +
        sgn i • hR i j₁ k₁ (by omega) x (DR.U.d j j₁ hj y) =
      cupL.P i j k₁ (by omega) ((ghomComp fS DPp.ι).f i i rfl x) (DR.ι.f j j rfl y)
  /-- The primitive homotopy on `U_{P⊥} × U_P`. -/
  hP : ∀ i j k : ℤ, i + j = k + 1 → DPp.U.X i →ₗ[S] UP.X j →ₗ[S] EL.X k
  /-- … is the sum of the same old per-place homotopies and the homotopy at `q`. -/
  hP_eq : ∀ (i j k : ℤ) (h : i + j = k + 1) (x : DPp.U.X i) (y : UP.X j),
    hP i j k h x y = ∑ v ∈ old, hv v i j k h (pPp v i x) (pP v j y) + hq i j k h (qPp i x) (qP j y)
  isoP : ∀ (i i₁ j j₁ k k₁ : ℤ) (h : i + j = k + 1) (hi : i + 1 = i₁) (hj : j + 1 = j₁)
    (hk : k + 1 = k₁) (x : DPp.U.X i) (y : UP.X j),
    EL.d k k₁ hk (hP i j k h x y) + hP i₁ j k₁ (by omega) (DPp.U.d i i₁ hi x) y +
        sgn i • hP i j₁ k₁ (by omega) x (UP.d j j₁ hj y) =
      cupL.P i j k₁ (by omega) (DPp.ι.f i i rfl x) ((ghomComp fP DR.ι).f j j rfl y)
  /-- Every old condition is retained by `f_P`: it is the identity on each old summand. -/
  ret_P : ∀ (v : ι) (j : ℤ) (y : UP.X j), pR v j (fP.f j j rfl y) = pP v j y
  /-- Every old orthogonal condition is retained by `f_S`. -/
  ret_S : ∀ (v : ι) (i : ℤ) (x : US.X i), pPp v i (fS.f i i rfl x) = pS v i x
  /-- At `q`, `f_P` is the inclusion of the unramified condition into the full complex. -/
  q_P : ∀ (j : ℤ) (y : UP.X j), qR j (fP.f j j rfl y) = NP.ιq.f j j rfl (qP j y)
  /-- At `q`, `f_S` is `0 → U_q^{ur}`: the strict condition at `q` is zero. -/
  q_S : ∀ (i : ℤ) (x : US.X i), qPp i (fS.f i i rfl x) = 0

variable {DR DPp : SelData S} {UP US : GCx S} {fP : GHom UP DR.U} {fS : GHom US DPp.U}

/-- **The retained homotopies** (tex L4163–4165), PROVED from the place-by-place retention:
`h_R(u, f_P v) = h_P(f_S u, v)`. -/
theorem PlaceRetention.retained (R : PlaceRetention DR DPp fP fS) (i j k : ℤ) (h : i + j = k + 1)
    (x : US.X i) (y : UP.X j) : R.hR i j k h x (fP.f j j rfl y) = R.hP i j k h (fS.f i i rfl x) y := by
  rw [R.hR_eq, R.hP_eq, R.q_S, map_zero, LinearMap.zero_apply, add_zero]
  exact Finset.sum_congr rfl fun v _ => by rw [R.ret_P, R.ret_S]

/-- **The `RetainedPairing` of the place-by-place retention data.** -/
def PlaceRetention.toRetainedPairing (R : PlaceRetention DR DPp fP fS) :
    RetainedPairing DR DPp fP fS where
  E := R.E
  EL := R.EL
  resE := R.resE
  cupG := R.cupG
  cupL := R.cupL
  compat := R.compat
  hR := R.hR
  isoR := R.isoR
  hP := R.hP
  isoP := R.isoP
  retained := R.retained

/-! ### Non-vacuity -/

/-- Selmer data `constCx --id--> constCx <--id-- constCx` (the local condition maps isomorphically
onto the local complex). -/
def relSel (S : Type u) [CommRing S] : SelData S :=
  ⟨constCx S, constCx S, constCx S, constId S, constId S⟩

/-- The zero new place, in universe `u`. -/
abbrev zeroNP (S : Type u) [CommRing S] : UnramifiedNewPlace S := zeroNewPlace S

/-- **Non-vacuity of `PlaceRetention`** (LESSON 2): relaxed data `relSel` (`ι_R = id`), orthogonal
data `constSel` (`ι = 0`), identity condition maps, one old place with zero homotopy, the zero new
place. -/
def examplePlaceRetention (S : Type u) [CommRing S] :
    PlaceRetention (relSel S) (constSel S) (constId S) (constId S) where
  E := constCx S
  EL := constCx S
  resE := constId S
  cupG := constMul S
  cupL := constMul S
  compat _ _ _ _ _ _ _ _ _ _ _ _ _ := rfl
  ι := Unit
  old := {()}
  Uo _ := constCx S
  Uo' _ := constCx S
  hv _ _ _ _ _ := 0
  NP := zeroNP S
  Uq' := zeroCx S
  hq _ _ _ _ := 0
  pR _ _ := LinearMap.id
  pP _ _ := LinearMap.id
  pS _ _ := LinearMap.id
  pPp _ _ := LinearMap.id
  qR _ := 0
  qP _ := 0
  qPp _ := 0
  hR _ _ _ _ := 0
  hR_eq _ _ _ _ _ _ := by simp
  isoR i _ _ _ _ _ _ _ _ _ x y := by
    change (0 : S) + 0 + sgn i • (0 : S) = (0 : S) * (show S from y)
    rw [smul_zero, add_zero, add_zero, zero_mul]
  hP _ _ _ _ := 0
  hP_eq _ _ _ _ _ _ := by simp
  isoP i _ _ _ _ _ _ _ _ _ x y := by
    change (0 : S) + 0 + sgn i • (0 : S) = (0 : S) * (show S from y)
    rw [smul_zero, add_zero, add_zero, zero_mul]
  ret_P _ _ _ := rfl
  ret_S _ _ _ := rfl
  q_P _ _ := Subsingleton.elim _ _
  q_S _ _ := rfl

end ZInQ.Contrib.CloudB3RC53.CommonCoordinate
