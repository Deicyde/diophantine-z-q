import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthActual

/-!
# Lane RC29 (round 2): the per-place Kummer inputs from local duality

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer` (tex 3413–3463: "Its Kummer image
is its exact local annihilator, and the comparison has integral isotropy homotopies"; tex
3439–3443: "The local finite dualities … make the Kummer map adjoint to
`H¹(F, B[2^a]) → H¹(F, B)[2^a]`. The latter has Kummer image as kernel, so the Kummer image is its
exact annihilator").

**(A) The generic theorem** `orthLD_cone_acyclic` / `orthLD_quasiIso` (PROVED): let
`P : C × C' → E` be a pairing of complexes and `tr : E² → R` a trace killing coboundaries, and
assume that the **local duality** map `C → Hom_R(C', R)[−2]`, `x ↦ (y ↦ tr(x ∪ y))`, is a
quasi-isomorphism. For the Galois data this map is `adjHom P 2 tr`, and its quasi-isomorphy is the
conclusion of lane RC26's PRINT `NekovarProp524` (Nekovář 5.2.4). Let `U → C`, `U' → C'` be local
conditions concentrated in degrees `0, 1`, with `C`, `C'` vanishing in negative degrees, such that:
* `H⁰(U) ≅ H⁰(C)`, `H⁰(U') ≅ H⁰(C')`, `H¹(U) ↪ H¹(C)` and `H¹(U') ↪ H¹(C')`;
* the **annihilator condition** holds: a `1`-cocycle of `C` orthogonal to `i'(U'¹)` under `tr ∘ ∪`
  lies in `i(U¹) + B¹(C)`.

If `R` is self-injective, the per-place local duality map `Cone(U → C)[−1] → Hom_R(U', R)[−3]` of
`OrthPlaces` is a quasi-isomorphism, for every isotropy homotopy. The proof computes the
cohomology of its cone degree by degree, using lane RC26's `coneAdj_solve` for the local duality
and the extension of linear forms (`Module.Injective R R`, `orthLD_extend`) for the duals. Only
this one annihilator direction and only the local duality for `β` (not `β.flip`) are used.
* `orthLD_isotropic` (PROVED): the isotropy `OrthIsotropicAt` follows from `tr(i u ∪ i' u') = 0`
  and `InducesIsoH2`.
* Galois form: `orthPerPlace_of_localDuality`, with the predicates `OrthH01At` (the `H⁰`/`H¹`
  comparisons) and `OrthKummerAnnihilator` (ISO and ANN at the cocycle level).

**Kummer conditions.**
* `orth_kummerAt_h01` (PROVED): lane RC28's `kummerAt` satisfies `OrthH01At`.
* `orthKummerAnnihilator_of_cup` (PROVED): the bridge from the coboundary forms (with `contCup`,
  `contD`, `contB1`, `kummerZ'`) to `OrthKummerAnnihilator`.
* Non-vacuity (PROVED): `orth_fullAt_h01` and `orth_fullAt_zeroAt_annihilator`.

**(B) The actual data.** `orthogonalComplementsT_actualKummer_of_annihilator` and
`orthSelmerDuality_actualKummer_of_annihilator` are the theorems of `OrthActual` with the ELLIOT
hypotheses `hisoK`, `hperfK` replaced by:
* `NekovarProp524` (PRINT, lane RC26);
* `OrthKummerAnnihilator` at the places of `S₀`;
* `InducesIsoH2` at every place;
* the GLUE `hT`: the inflation of `A_i(1)` to `G_{K,S}` is a cyclotomic twist.

Kinds: PROVED (from the hypotheses named in each statement).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Manuscript.RC.SelmerComplex
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)

/-! ### Extension of linear forms over a self-injective ring -/

section Extend

variable {R : Type} [CommRing R]

/-- **Extension of linear forms** (`R` self-injective): a linear form `g` on `X` vanishing on the
kernel of `f : X → Y` is `h ∘ f` for a linear form `h` on `Y`. PROVED. -/
theorem orthLD_extend [Module.Injective R R] {X Y : Type} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (f : X →ₗ[R] Y) (g : X →ₗ[R] R)
    (hfg : ∀ x, f x = 0 → g x = 0) : ∃ h : Y →ₗ[R] R, ∀ x, h (f x) = g x := by
  have hf₁ : Function.Injective ((LinearMap.ker f).liftQ f le_rfl) := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl
  obtain ⟨h, hh⟩ := Module.Injective.out _ hf₁ ((LinearMap.ker f).liftQ g fun x hx => hfg x hx)
  exact ⟨h, fun x => hh (Submodule.Quotient.mk x)⟩

end Extend

/-! ### The cone of the per-place map, in components -/

section Components

variable {R : Type} [CommRing R] {U U' C C' E : GCx R} (iU : GHom U C) (iU' : GHom U' C')
  (P : GPair C C' E) (J : LocalTruncIsotropy iU iU' P) (trv : E.X 2 →ₗ[R] R)
  (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0)

/-- For conditions concentrated in degrees `0, 1` the isotropy homotopy never contributes to the
per-place map. PROVED. -/
theorem orthLD_h_zero (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
    (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i)) (i j : ℤ) (h : i + j = 2 + 1)
    (u : U.X i) (y : U'.X j) : J.h i j 2 h u y = 0 := by
  by_cases hi : i = 0 ∨ i = 1
  · have : Subsingleton (U'.X j) := hU' j (by omega) (by omega)
    rw [Subsingleton.elim y 0, map_zero]
  · have : Subsingleton (U.X i) := hU i (by omega) (by omega)
    rw [Subsingleton.elim u 0, map_zero, LinearMap.zero_apply]

/-- The per-place map for conditions concentrated in degrees `0, 1`: `(u, x) ↦ (y ↦ tr(x ∪ i'y))`.
PROVED. -/
theorem orthLD_F_apply (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
    (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i)) (i j : ℤ) (h : i = j) (u : U.X i)
    (x : C.X (i - 1)) (y : U'.X (3 - j)) :
    asDual ((orthLocalMap iU iU' P J trv htrv).f i j h ((u, x) : coneT (orthNeg iU) i)) y =
      trv (P.P (i - 1) (3 - j) 2 (by omega) x (iU'.f (3 - j) (3 - j) rfl y)) := by
  rw [orthLocalMap_apply, orthLD_h_zero iU iU' P J hU hU', add_zero]

/-- **The cocycle conditions in the cone of the per-place map.** PROVED. -/
theorem orthLD_cocycle (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
    (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i)) (j k : ℤ) (hjk : j + 1 = k)
    (u : U.X j) (x : C.X (j - 1)) (φ : Module.Dual R (U'.X (3 - (j - 1))))
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d j k hjk
      ((((u, x) : coneT (orthNeg iU) j), (φ : (dualCx U' 3).X (j - 1))) :
        coneT (orthLocalMap iU iU' P J trv htrv) j) = 0) :
    U.d j k hjk u = 0 ∧ iU.f j (k - 1) (by omega) u + C.d (j - 1) (k - 1) (by omega) x = 0 ∧
      ∀ y : U'.X (3 - (k - 1)), trv (P.P (j - 1) (3 - (k - 1)) 2 (by omega) x
        (iU'.f (3 - (k - 1)) (3 - (k - 1)) rfl y)) =
        (-(sgn (j - 1))) • φ (U'.d (3 - (k - 1)) (3 - (j - 1)) (by omega) y) := by
  refine ⟨congrArg (fun w : coneT (orthLocalMap iU iU' P J trv htrv) k => w.1.1) hc, ?_, ?_⟩
  · have h2 : -(iU.f j (k - 1) (by omega) u) - C.d (j - 1) (k - 1) (by omega) x = 0 :=
      congrArg (fun w : coneT (orthLocalMap iU iU' P J trv htrv) k => w.1.2) hc
    rw [← neg_add', neg_eq_zero] at h2
    exact h2
  · intro y
    have h3 := congrArg (fun w : coneT (orthLocalMap iU iU' P J trv htrv) k => asDual w.2 y) hc
    change asDual ((orthLocalMap iU iU' P J trv htrv).f j (k - 1) (by omega)
        ((u, x) : coneT (orthNeg iU) j)) y -
      asDual ((dualCx U' 3).d (j - 1) (k - 1) (by omega) (φ : (dualCx U' 3).X (j - 1))) y = 0
      at h3
    rw [orthLD_F_apply iU iU' P J trv htrv hU hU'] at h3
    exact sub_eq_zero.mp h3

/-- **Solving in the cone of the per-place map**: a triple `(u₀, x₀, ψ)` maps to `(u, x, φ)` under
the differential as soon as the three component equations hold. PROVED. -/
theorem orthLD_coneD_eq (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
    (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i)) (i j : ℤ) (hij : i + 1 = j)
    (u₀ : U.X i) (x₀ : C.X (i - 1)) (ψ : Module.Dual R (U'.X (3 - (i - 1))))
    (u : U.X j) (x : C.X (j - 1)) (φ : Module.Dual R (U'.X (3 - (j - 1))))
    (h1 : U.d i j hij u₀ = u)
    (h2 : -(iU.f i (j - 1) (by omega) u₀) - C.d (i - 1) (j - 1) (by omega) x₀ = x)
    (h3 : ∀ y : U'.X (3 - (j - 1)), trv (P.P (i - 1) (3 - (j - 1)) 2 (by omega) x₀
        (iU'.f (3 - (j - 1)) (3 - (j - 1)) rfl y)) -
      (-(sgn (i - 1))) • ψ (U'.d (3 - (j - 1)) (3 - (i - 1)) (by omega) y) = φ y) :
    (coneCx (orthLocalMap iU iU' P J trv htrv)).d i j hij
      ((((u₀, x₀) : coneT (orthNeg iU) i), (ψ : (dualCx U' 3).X (i - 1))) :
        coneT (orthLocalMap iU iU' P J trv htrv) i) =
      ((((u, x) : coneT (orthNeg iU) j), (φ : (dualCx U' 3).X (j - 1))) :
        coneT (orthLocalMap iU iU' P J trv htrv) j) := by
  refine Prod.ext (Prod.ext h1 h2) (dualCx_ext fun y => ?_)
  change asDual ((orthLocalMap iU iU' P J trv htrv).f i (j - 1) (by omega)
        ((u₀, x₀) : coneT (orthNeg iU) i)) y -
      asDual ((dualCx U' 3).d (i - 1) (j - 1) (by omega) (ψ : (dualCx U' 3).X (i - 1))) y = φ y
  rw [orthLD_F_apply iU iU' P J trv htrv hU hU']
  exact h3 y

end Components


/-! ### The cone of the per-place map is acyclic -/

section Acyclic

variable {R : Type} [CommRing R] {U U' C C' E : GCx R} (iU : GHom U C) (iU' : GHom U' C')
  (P : GPair C C' E) (J : LocalTruncIsotropy iU iU' P) (trv : E.X 2 →ₗ[R] R)
  (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0)
  (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
  (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i))

omit [CommRing R] in
/-- A linear form on a subsingleton module is zero. -/
theorem orthLD_dual_eq_zero [CommRing R] {X : Type} [AddCommGroup X] [Module R X] [Subsingleton X]
    (φ : Module.Dual R X) : φ = 0 :=
  LinearMap.ext fun y => by rw [Subsingleton.elim y 0, map_zero, LinearMap.zero_apply]

include htrv in
/-- The Leibniz rule under the trace: `tr(x₁ ∪ dy) = tr(dx₁ ∪ y)` for `x₁ ∈ C¹`, `y ∈ C'⁰`.
PROVED. -/
theorem orthLD_leib_tr (x₁ : C.X 1) (y : C'.X 0) :
    trv (P.P 1 1 2 rfl x₁ (C'.d 0 1 rfl y)) = trv (P.P 2 0 2 rfl (C.d 1 2 rfl x₁) y) := by
  have hl := P.leib 1 2 0 1 1 2 rfl rfl rfl rfl x₁ y
  have h0 := htrv (P.P 1 0 1 rfl x₁ y)
  rw [hl, map_add, map_zsmul, sgn_one, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0
  exact h0.symm

include hU hU' in
/-- Degrees `≤ 0`: the cocycles of the cone vanish (`H⁰(U) ↪ H⁰(C)`). PROVED. -/
theorem orthLD_case_nonpos (hCneg : ∀ i : ℤ, i < 0 → Subsingleton (C.X i))
    (h0inj : ∀ u : U.X 0, U.d 0 1 rfl u = 0 → iU.f 0 0 rfl u = 0 → u = 0)
    (j : ℤ) (hj : j ≤ 0) (c : (coneCx (orthLocalMap iU iU' P J trv htrv)).X j)
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d j (j + 1) rfl c = 0) : c = 0 := by
  obtain ⟨⟨u, x⟩, φ⟩ := c
  change Module.Dual R (U'.X (3 - (j - 1))) at φ
  obtain ⟨hu, hx, -⟩ := orthLD_cocycle iU iU' P J trv htrv hU hU' j (j + 1) rfl u x φ hc
  have : Subsingleton (C.X (j - 1)) := hCneg (j - 1) (by omega)
  have : Subsingleton (U'.X (3 - (j - 1))) := hU' _ (by omega) (by omega)
  have hx0 : x = 0 := Subsingleton.elim _ _
  have hφ0 : φ = 0 := orthLD_dual_eq_zero φ
  rw [hx0, map_zero, add_zero] at hx
  have hu0 : u = 0 := by
    rcases lt_or_eq_of_le hj with h | rfl
    · have : Subsingleton (U.X j) := hU j (by omega) (by omega)
      exact Subsingleton.elim _ _
    · exact h0inj u hu hx
  subst hx0 hu0 hφ0
  rfl

include hU hU' in
/-- Degree `1` (`H¹(U) ↪ H¹(C)`, `H⁰(U) ↠ H⁰(C)`). PROVED. -/
theorem orthLD_case1 (hCneg : ∀ i : ℤ, i < 0 → Subsingleton (C.X i))
    (h0surj : ∀ z : C.X 0, C.d 0 1 rfl z = 0 → ∃ u : U.X 0, U.d 0 1 rfl u = 0 ∧ iU.f 0 0 rfl u = z)
    (h1inj : ∀ (u : U.X 1) (x : C.X 0), C.d 0 1 rfl x = iU.f 1 1 rfl u →
      ∃ u₀ : U.X 0, U.d 0 1 rfl u₀ = u)
    (c : (coneCx (orthLocalMap iU iU' P J trv htrv)).X 1)
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d 1 2 rfl c = 0) :
    ∃ y, (coneCx (orthLocalMap iU iU' P J trv htrv)).d 0 1 rfl y = c := by
  obtain ⟨⟨u, x⟩, φ⟩ := c
  change C.X 0 at x
  change Module.Dual R (U'.X 3) at φ
  obtain ⟨-, hx, -⟩ := orthLD_cocycle iU iU' P J trv htrv hU hU' 1 2 rfl u x φ hc
  have hx' : C.d 0 1 rfl (-x) = iU.f 1 1 rfl u := by
    rw [map_neg, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm]
    exact hx
  obtain ⟨u₁, hu₁⟩ := h1inj u (-x) hx'
  have hz : C.d 0 1 rfl (iU.f 0 0 rfl u₁ + x) = 0 := by
    rw [map_add, ← iU.comm 0 1 0 1 rfl rfl rfl rfl u₁, hu₁]
    exact hx
  obtain ⟨u₂, hu₂, hiu₂⟩ := h0surj _ hz
  have : Subsingleton (C.X (0 - 1)) := hCneg _ (by norm_num)
  have : Subsingleton (U'.X (3 - (1 - 1))) := hU' _ (by norm_num) (by norm_num)
  refine ⟨(((u₁ - u₂, 0) : coneT (orthNeg iU) 0), (0 : (dualCx U' 3).X (0 - 1))), ?_⟩
  refine orthLD_coneD_eq iU iU' P J trv htrv hU hU' 0 1 rfl (u₁ - u₂) 0 0 u x φ ?_ ?_ ?_
  · rw [map_sub, hu₁, hu₂, sub_zero]
  · rw [map_zero, sub_zero, map_sub]
    change -(iU.f 0 0 rfl u₁ - iU.f 0 0 rfl u₂) = x
    rw [hiu₂]
    abel
  · intro y
    rw [Subsingleton.elim y 0]
    simp

include hU hU' in
/-- Degree `2` (the annihilator condition). PROVED. -/
theorem orthLD_case2
    (hann : ∀ x : C.X 1, C.d 1 2 rfl x = 0 →
      (∀ y : U'.X 1, trv (P.P 1 1 2 rfl x (iU'.f 1 1 rfl y)) = 0) →
        ∃ (u : U.X 1) (c : C.X 0), x = iU.f 1 1 rfl u + C.d 0 1 rfl c)
    (c : (coneCx (orthLocalMap iU iU' P J trv htrv)).X 2)
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d 2 3 rfl c = 0) :
    ∃ y, (coneCx (orthLocalMap iU iU' P J trv htrv)).d 1 2 rfl y = c := by
  obtain ⟨⟨u, x⟩, φ⟩ := c
  change C.X 1 at x
  change Module.Dual R (U'.X 2) at φ
  obtain ⟨-, hx, hφ⟩ := orthLD_cocycle iU iU' P J trv htrv hU hU' 2 3 rfl u x φ hc
  have : Subsingleton (U.X 2) := hU 2 (by norm_num) (by norm_num)
  have : Subsingleton (U'.X 2) := hU' 2 (by norm_num) (by norm_num)
  have hu0 : u = 0 := Subsingleton.elim _ _
  rw [hu0, map_zero, zero_add] at hx
  have horth : ∀ y : U'.X 1, trv (P.P 1 1 2 rfl x (iU'.f 1 1 rfl y)) = 0 := by
    intro y
    have h := hφ y
    rw [orthLD_dual_eq_zero φ, LinearMap.zero_apply, smul_zero] at h
    exact h
  obtain ⟨u', c₀, hxc⟩ := hann x hx horth
  refine ⟨(((-u', -c₀) : coneT (orthNeg iU) 1), (0 : (dualCx U' 3).X (1 - 1))), ?_⟩
  refine orthLD_coneD_eq iU iU' P J trv htrv hU hU' 1 2 rfl (-u') (-c₀) 0 u x φ ?_ ?_ ?_
  · exact Subsingleton.elim _ _
  · rw [map_neg, map_neg, neg_neg, sub_neg_eq_add]
    exact hxc.symm
  · intro y
    have : Subsingleton (U'.X (3 - (2 - 1))) := hU' _ (by norm_num) (by norm_num)
    rw [Subsingleton.elim y 0]
    simp

include hU hU' in
/-- Degree `3` (local duality in degrees `2` and `1`, `H⁰(U') ↠ H⁰(C')`, `H¹(U') ↪ H¹(C')`, and
the extension of linear forms). PROVED. -/
theorem orthLD_case3 [Module.Injective R R] (hacyc : GAcyclic (coneCx (adjHom P 2 trv htrv)))
    (h0surj' : ∀ z : C'.X 0, C'.d 0 1 rfl z = 0 →
      ∃ u : U'.X 0, U'.d 0 1 rfl u = 0 ∧ iU'.f 0 0 rfl u = z)
    (h1inj' : ∀ (u : U'.X 1) (x : C'.X 0), C'.d 0 1 rfl x = iU'.f 1 1 rfl u →
      ∃ u₀ : U'.X 0, U'.d 0 1 rfl u₀ = u)
    (c : (coneCx (orthLocalMap iU iU' P J trv htrv)).X 3)
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d 3 4 rfl c = 0) :
    ∃ y, (coneCx (orthLocalMap iU iU' P J trv htrv)).d 2 3 rfl y = c := by
  obtain ⟨⟨u, x⟩, φ⟩ := c
  change C.X 2 at x
  change Module.Dual R (U'.X 1) at φ
  obtain ⟨-, hx, hφ⟩ := orthLD_cocycle iU iU' P J trv htrv hU hU' 3 4 rfl u x φ hc
  have : Subsingleton (U.X 3) := hU 3 (by norm_num) (by norm_num)
  have : Subsingleton (U'.X 2) := hU' 2 (by norm_num) (by norm_num)
  have hu0 : u = 0 := Subsingleton.elim _ _
  rw [hu0, map_zero, zero_add] at hx
  have hdx : C.d 2 3 rfl x = 0 := hx
  have hφ' : ∀ y : U'.X 0, trv (P.P 2 0 2 rfl x (iU'.f 0 0 rfl y)) = -(φ (U'.d 0 1 rfl y)) := by
    intro y
    have h := hφ y
    rw [show sgn (3 - 1) = 1 from sgn_two, neg_smul, one_smul] at h
    exact h
  -- `x` is a coboundary: local duality in degree two
  obtain ⟨ψ, hψ⟩ := orthLD_extend (C'.d 0 1 rfl) (trv ∘ₗ P.P 2 0 2 rfl x) (by
    intro y' hy'
    obtain ⟨y, hy, rfl⟩ := h0surj' y' hy'
    change trv (P.P 2 0 2 rfl x (iU'.f 0 0 rfl y)) = 0
    rw [hφ' y, hy, map_zero, neg_zero])
  obtain ⟨x₁, -, hx₁, -⟩ := coneAdj_solve P trv htrv hacyc 1 2 3 rfl rfl 0 1 2 rfl rfl rfl x ψ hdx
    (by
      intro y
      rw [hψ y, show sgn (2 - 1) = -1 from sgn_one, neg_neg, one_smul]
      rfl)
  -- the correction: local duality in degree one
  obtain ⟨ψ', hψ'⟩ := orthLD_extend (LinearMap.coprod (iU'.f 1 1 rfl) (C'.d 0 1 rfl))
    ((φ + trv ∘ₗ (P.P 1 1 2 rfl x₁ ∘ₗ iU'.f 1 1 rfl)) ∘ₗ
      LinearMap.fst R (U'.X 1) (C'.X 0)) (by
    rintro ⟨y, c⟩ hp
    change iU'.f 1 1 rfl y + C'.d 0 1 rfl c = 0 at hp
    have hc' : C'.d 0 1 rfl (-c) = iU'.f 1 1 rfl y := by
      rw [map_neg, neg_eq_iff_eq_neg, eq_neg_iff_add_eq_zero, add_comm]
      exact hp
    obtain ⟨y₀, hy₀⟩ := h1inj' y (-c) hc'
    change φ y + trv (P.P 1 1 2 rfl x₁ (iU'.f 1 1 rfl y)) = 0
    rw [← hy₀, iU'.comm 0 1 0 1 rfl rfl rfl rfl y₀, orthLD_leib_tr P trv htrv, hx₁, hφ' y₀]
    exact add_neg_cancel _)
  have hψ'1 : ∀ y : U'.X 1, ψ' (iU'.f 1 1 rfl y) =
      φ y + trv (P.P 1 1 2 rfl x₁ (iU'.f 1 1 rfl y)) := by
    intro y
    have h := hψ' (y, 0)
    change ψ' (iU'.f 1 1 rfl y + C'.d 0 1 rfl 0) =
      φ y + trv (P.P 1 1 2 rfl x₁ (iU'.f 1 1 rfl y)) at h
    rw [map_zero, add_zero] at h
    exact h
  have hψ'2 : ∀ c : C'.X 0, ψ' (C'.d 0 1 rfl c) = 0 := by
    intro c
    have h := hψ' (0, c)
    change ψ' (iU'.f 1 1 rfl 0 + C'.d 0 1 rfl c) =
      φ 0 + trv (P.P 1 1 2 rfl x₁ (iU'.f 1 1 rfl 0)) at h
    rw [map_zero, zero_add] at h
    rw [h]
    simp
  obtain ⟨z₁, z₂, hz₁, hz₁'⟩ := coneAdj_solve P trv htrv hacyc 1 2 3 rfl rfl 0 1 2 rfl rfl rfl
    (0 : C.X 2) ψ' (map_zero _) (by
      intro y
      rw [hψ'2 y, smul_zero]
      simp)
  refine ⟨(((0, z₁ - x₁) : coneT (orthNeg iU) 2), (0 : (dualCx U' 3).X (2 - 1))), ?_⟩
  refine orthLD_coneD_eq iU iU' P J trv htrv hU hU' 2 3 rfl 0 (z₁ - x₁) 0 u x φ ?_ ?_ ?_
  · exact Subsingleton.elim _ _
  · rw [map_zero, neg_zero, zero_sub, map_sub]
    change -(C.d 1 2 rfl z₁ - C.d 1 2 rfl x₁) = x
    rw [hz₁, hx₁, zero_sub, neg_neg]
  · intro y
    change trv (P.P 1 1 2 rfl (z₁ - x₁) (iU'.f 1 1 rfl y)) -
      (-(sgn (2 - 1))) • (0 : Module.Dual R (U'.X 2)) (U'.d 1 2 rfl y) = φ y
    rw [LinearMap.zero_apply, smul_zero, sub_zero, map_sub, LinearMap.sub_apply, map_sub]
    have e1 := hz₁' (iU'.f 1 1 rfl y)
    have e2 : C'.d 1 2 rfl (iU'.f 1 1 rfl y) = 0 := by
      rw [← iU'.comm 1 2 1 2 rfl rfl rfl rfl y, Subsingleton.elim (U'.d 1 2 rfl y) 0, map_zero]
    rw [e2, map_zero, smul_zero, sub_zero, hψ'1 y] at e1
    change trv (P.P 1 1 2 rfl z₁ (iU'.f 1 1 rfl y)) - trv (P.P 1 1 2 rfl x₁ (iU'.f 1 1 rfl y)) =
      φ y
    rw [e1, add_sub_cancel_right]

include hU hU' in
/-- Degree `4` (local duality in degrees `3` and `2`, `H⁰(U') ↪ H⁰(C')`, and the extension of
linear forms). PROVED. -/
theorem orthLD_case4 [Module.Injective R R] (hacyc : GAcyclic (coneCx (adjHom P 2 trv htrv)))
    (hC'neg : ∀ i : ℤ, i < 0 → Subsingleton (C'.X i))
    (h0inj' : ∀ u : U'.X 0, U'.d 0 1 rfl u = 0 → iU'.f 0 0 rfl u = 0 → u = 0)
    (c : (coneCx (orthLocalMap iU iU' P J trv htrv)).X 4)
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d 4 5 rfl c = 0) :
    ∃ y, (coneCx (orthLocalMap iU iU' P J trv htrv)).d 3 4 rfl y = c := by
  obtain ⟨⟨u, x⟩, φ⟩ := c
  change C.X 3 at x
  change Module.Dual R (U'.X 0) at φ
  obtain ⟨-, hx, -⟩ := orthLD_cocycle iU iU' P J trv htrv hU hU' 4 5 rfl u x φ hc
  have : Subsingleton (U.X 4) := hU 4 (by norm_num) (by norm_num)
  have : Subsingleton (C'.X (-1)) := hC'neg (-1) (by norm_num)
  have hu0 : u = 0 := Subsingleton.elim _ _
  rw [hu0, map_zero, zero_add] at hx
  have hdx : C.d 3 4 rfl x = 0 := hx
  -- `x` is a coboundary: local duality in degree three
  obtain ⟨x₂, -, hx₂, -⟩ := coneAdj_solve P trv htrv hacyc 2 3 4 rfl rfl (-1) 0 1 rfl rfl
    (by norm_num) x (0 : Module.Dual R (C'.X 0)) hdx (by
      intro y
      rw [Subsingleton.elim y 0]
      simp)
  -- the correction on `Z⁰(U')`: local duality in degree two
  obtain ⟨ψ'', hψ''⟩ := orthLD_extend (iU'.f 0 0 rfl ∘ₗ (LinearMap.ker (U'.d 0 1 rfl)).subtype)
    ((φ + trv ∘ₗ (P.P 2 0 2 rfl x₂ ∘ₗ iU'.f 0 0 rfl)) ∘ₗ
      (LinearMap.ker (U'.d 0 1 rfl)).subtype) (by
    intro y hy
    have hy0 : (y : U'.X 0) = 0 := h0inj' y (LinearMap.mem_ker.mp y.2) hy
    change φ (y : U'.X 0) + trv (P.P 2 0 2 rfl x₂ (iU'.f 0 0 rfl (y : U'.X 0))) = 0
    rw [hy0]
    simp)
  obtain ⟨w, z₃, hw, hw'⟩ := coneAdj_solve P trv htrv hacyc 2 3 4 rfl rfl (-1) 0 1 rfl rfl
    (by norm_num) (0 : C.X 3) ψ'' (map_zero _) (by
      intro y
      rw [Subsingleton.elim y 0]
      simp)
  -- the remaining correction on `U'⁰ / Z⁰(U')`
  obtain ⟨ψ, hψ⟩ := orthLD_extend (U'.d 0 1 rfl)
    ((φ + trv ∘ₗ (P.P 2 0 2 rfl x₂ ∘ₗ iU'.f 0 0 rfl)) -
      trv ∘ₗ (P.P 2 0 2 rfl w ∘ₗ iU'.f 0 0 rfl)) (by
    intro y hy
    have h1 := hw' (iU'.f 0 0 rfl y)
    have h2 : ψ'' (iU'.f 0 0 rfl y) =
        φ y + trv (P.P 2 0 2 rfl x₂ (iU'.f 0 0 rfl y)) := hψ'' ⟨y, hy⟩
    have h3 : C'.d 0 1 rfl (iU'.f 0 0 rfl y) = 0 := by
      rw [← iU'.comm 0 1 0 1 rfl rfl rfl rfl y, hy, map_zero]
    rw [h3, map_zero, smul_zero, sub_zero, h2] at h1
    change φ y + trv (P.P 2 0 2 rfl x₂ (iU'.f 0 0 rfl y)) -
      trv (P.P 2 0 2 rfl w (iU'.f 0 0 rfl y)) = 0
    rw [h1, sub_self])
  refine ⟨(((0, w - x₂) : coneT (orthNeg iU) 3), (ψ : (dualCx U' 3).X (3 - 1))), ?_⟩
  refine orthLD_coneD_eq iU iU' P J trv htrv hU hU' 3 4 rfl 0 (w - x₂) ψ u x φ ?_ ?_ ?_
  · exact Subsingleton.elim _ _
  · rw [map_zero, neg_zero, zero_sub, map_sub]
    change -(C.d 2 3 rfl w - C.d 2 3 rfl x₂) = x
    rw [hw, hx₂, zero_sub, neg_neg]
  · intro y
    change trv (P.P 2 0 2 rfl (w - x₂) (iU'.f 0 0 rfl y)) -
      (-(sgn (3 - 1))) • ψ (U'.d 0 1 rfl y) = φ y
    rw [hψ y, show sgn (3 - 1) = 1 from sgn_two, neg_smul, one_smul, sub_neg_eq_add, map_sub,
      LinearMap.sub_apply, map_sub]
    change trv (P.P 2 0 2 rfl w (iU'.f 0 0 rfl y)) - trv (P.P 2 0 2 rfl x₂ (iU'.f 0 0 rfl y)) +
      (φ y + trv (P.P 2 0 2 rfl x₂ (iU'.f 0 0 rfl y)) - trv (P.P 2 0 2 rfl w (iU'.f 0 0 rfl y))) =
        φ y
    abel

include hU hU' in
/-- Degrees `≥ 5` (local duality in degrees `≥ 4`). PROVED. -/
theorem orthLD_case_ge5 (hacyc : GAcyclic (coneCx (adjHom P 2 trv htrv)))
    (hC'neg : ∀ i : ℤ, i < 0 → Subsingleton (C'.X i)) (j : ℤ) (hj : 5 ≤ j)
    (c : (coneCx (orthLocalMap iU iU' P J trv htrv)).X j)
    (hc : (coneCx (orthLocalMap iU iU' P J trv htrv)).d j (j + 1) rfl c = 0) :
    ∃ y, (coneCx (orthLocalMap iU iU' P J trv htrv)).d (j - 1) j (by omega) y = c := by
  obtain ⟨⟨u, x⟩, φ⟩ := c
  change Module.Dual R (U'.X (3 - (j - 1))) at φ
  obtain ⟨-, hx, -⟩ := orthLD_cocycle iU iU' P J trv htrv hU hU' j (j + 1) rfl u x φ hc
  have : Subsingleton (U.X j) := hU j (by omega) (by omega)
  have : Subsingleton (U'.X (3 - (j - 1))) := hU' _ (by omega) (by omega)
  have : Subsingleton (C'.X (3 - j)) := hC'neg _ (by omega)
  have hu0 : u = 0 := Subsingleton.elim _ _
  rw [hu0, map_zero, zero_add] at hx
  obtain ⟨e', -, he', -⟩ := coneAdj_solve P trv htrv hacyc (j - 1 - 1) (j - 1) (j + 1 - 1)
    (by omega) (by omega) (3 - j) (4 - j) (5 - j) (by omega) (by omega)
    (by omega) x (0 : Module.Dual R (C'.X (4 - j))) hx (by
      intro y
      rw [Subsingleton.elim y 0]
      simp)
  refine ⟨(((0, -e') : coneT (orthNeg iU) (j - 1)), (0 : (dualCx U' 3).X (j - 1 - 1))), ?_⟩
  refine orthLD_coneD_eq iU iU' P J trv htrv hU hU' (j - 1) j (by omega) 0 (-e') 0 u x φ ?_ ?_ ?_
  · exact Subsingleton.elim _ _
  · rw [map_zero, neg_zero, zero_sub, map_neg, neg_neg]
    exact he'
  · intro y
    rw [Subsingleton.elim y 0]
    simp

include hU hU' in
/-- **(A), acyclic form: the cone of the per-place map is acyclic**, for conditions concentrated in
degrees `0, 1` satisfying the `H⁰`/`H¹` comparisons and the annihilator condition, from the
acyclicity of the cone of the local duality map and the self-injectivity of `R`. PROVED. -/
theorem orthLD_cone_acyclic [Module.Injective R R]
    (hacyc : GAcyclic (coneCx (adjHom P 2 trv htrv)))
    (hCneg : ∀ i : ℤ, i < 0 → Subsingleton (C.X i))
    (hC'neg : ∀ i : ℤ, i < 0 → Subsingleton (C'.X i))
    (h0inj : ∀ u : U.X 0, U.d 0 1 rfl u = 0 → iU.f 0 0 rfl u = 0 → u = 0)
    (h0surj : ∀ z : C.X 0, C.d 0 1 rfl z = 0 → ∃ u : U.X 0, U.d 0 1 rfl u = 0 ∧ iU.f 0 0 rfl u = z)
    (h1inj : ∀ (u : U.X 1) (x : C.X 0), C.d 0 1 rfl x = iU.f 1 1 rfl u →
      ∃ u₀ : U.X 0, U.d 0 1 rfl u₀ = u)
    (h0inj' : ∀ u : U'.X 0, U'.d 0 1 rfl u = 0 → iU'.f 0 0 rfl u = 0 → u = 0)
    (h0surj' : ∀ z : C'.X 0, C'.d 0 1 rfl z = 0 →
      ∃ u : U'.X 0, U'.d 0 1 rfl u = 0 ∧ iU'.f 0 0 rfl u = z)
    (h1inj' : ∀ (u : U'.X 1) (x : C'.X 0), C'.d 0 1 rfl x = iU'.f 1 1 rfl u →
      ∃ u₀ : U'.X 0, U'.d 0 1 rfl u₀ = u)
    (hann : ∀ x : C.X 1, C.d 1 2 rfl x = 0 →
      (∀ y : U'.X 1, trv (P.P 1 1 2 rfl x (iU'.f 1 1 rfl y)) = 0) →
        ∃ (u : U.X 1) (c : C.X 0), x = iU.f 1 1 rfl u + C.d 0 1 rfl c) :
    GAcyclic (coneCx (orthLocalMap iU iU' P J trv htrv)) := by
  intro i j k hij hjk c hc
  obtain rfl : i = j - 1 := by omega
  obtain rfl : k = j + 1 := by omega
  rcases (show j ≤ 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ 5 ≤ j by omega) with
    h | rfl | rfl | rfl | rfl | h
  · refine ⟨0, ?_⟩
    rw [map_zero, orthLD_case_nonpos iU iU' P J trv htrv hU hU' hCneg h0inj j h c hc]
  · exact orthLD_case1 iU iU' P J trv htrv hU hU' hCneg h0surj h1inj c hc
  · exact orthLD_case2 iU iU' P J trv htrv hU hU' hann c hc
  · exact orthLD_case3 iU iU' P J trv htrv hU hU' hacyc h0surj' h1inj' c hc
  · exact orthLD_case4 iU iU' P J trv htrv hU hU' hacyc hC'neg h0inj' c hc
  · exact orthLD_case_ge5 iU iU' P J trv htrv hU hU' hacyc hC'neg j h c hc

end Acyclic


/-! ### (A) Quasi-isomorphism and isotropy -/

section QuasiIsoGeneric

variable {R : Type} [CommRing R] {U U' C C' E : GCx R} (iU : GHom U C) (iU' : GHom U' C')
  (P : GPair C C' E) (J : LocalTruncIsotropy iU iU' P) (trv : E.X 2 →ₗ[R] R)
  (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0)
  (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
  (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i))

include hU hU' in
/-- **(A), generic form: the per-place map is a quasi-isomorphism** when the local duality map
`C → Hom_R(C', R)[−2]` is one (see `orthLD_cone_acyclic` for the hypotheses). PROVED. -/
theorem orthLD_quasiIso [Module.Injective R R]
    (hLD : QuasiIso (GHom.toCC (adjHom P 2 trv htrv)))
    (hCneg : ∀ i : ℤ, i < 0 → Subsingleton (C.X i))
    (hC'neg : ∀ i : ℤ, i < 0 → Subsingleton (C'.X i))
    (h0inj : ∀ u : U.X 0, U.d 0 1 rfl u = 0 → iU.f 0 0 rfl u = 0 → u = 0)
    (h0surj : ∀ z : C.X 0, C.d 0 1 rfl z = 0 → ∃ u : U.X 0, U.d 0 1 rfl u = 0 ∧ iU.f 0 0 rfl u = z)
    (h1inj : ∀ (u : U.X 1) (x : C.X 0), C.d 0 1 rfl x = iU.f 1 1 rfl u →
      ∃ u₀ : U.X 0, U.d 0 1 rfl u₀ = u)
    (h0inj' : ∀ u : U'.X 0, U'.d 0 1 rfl u = 0 → iU'.f 0 0 rfl u = 0 → u = 0)
    (h0surj' : ∀ z : C'.X 0, C'.d 0 1 rfl z = 0 →
      ∃ u : U'.X 0, U'.d 0 1 rfl u = 0 ∧ iU'.f 0 0 rfl u = z)
    (h1inj' : ∀ (u : U'.X 1) (x : C'.X 0), C'.d 0 1 rfl x = iU'.f 1 1 rfl u →
      ∃ u₀ : U'.X 0, U'.d 0 1 rfl u₀ = u)
    (hann : ∀ x : C.X 1, C.d 1 2 rfl x = 0 →
      (∀ y : U'.X 1, trv (P.P 1 1 2 rfl x (iU'.f 1 1 rfl y)) = 0) →
        ∃ (u : U.X 1) (c : C.X 0), x = iU.f 1 1 rfl u + C.d 0 1 rfl c) :
    QuasiIso (GHom.toCC (orthLocalMap iU iU' P J trv htrv)) :=
  quasiIso_of_coneCx_acyclic _ (orthLD_cone_acyclic iU iU' P J trv htrv hU hU'
    (coneCx_acyclic_of_quasiIso _ hLD) hCneg hC'neg h0inj h0surj h1inj h0inj' h0surj' h1inj' hann)

include hU hU' in
/-- **Isotropy from the traces**: if `tr(i u ∪ i' u') = 0` for all degree-one `u, u'` and `tr`
induces `H²(E) ≅ R`, the `(1, 1)` products are coboundaries (they are cocycles since `U², U'²`
vanish). PROVED. -/
theorem orthLD_isotropic
    (hiso : ∀ (u : U.X 1) (y : U'.X 1), trv (P.P 1 1 2 rfl (iU.f 1 1 rfl u) (iU'.f 1 1 rfl y)) = 0)
    (h2 : ZInQ.Manuscript.RC.SelmerComplex.InducesIsoH2 trv) (u : U.X 1) (y : U'.X 1) :
    P.P 1 1 2 rfl (iU.f 1 1 rfl u) (iU'.f 1 1 rfl y) ∈ LinearMap.range (E.d 1 2 rfl) := by
  have : Subsingleton (U.X 2) := hU 2 (by norm_num) (by norm_num)
  have : Subsingleton (U'.X 2) := hU' 2 (by norm_num) (by norm_num)
  have hcoc : E.d 2 3 rfl (P.P 1 1 2 rfl (iU.f 1 1 rfl u) (iU'.f 1 1 rfl y)) = 0 := by
    rw [P.leib 1 2 1 2 2 3 rfl rfl rfl rfl (iU.f 1 1 rfl u) (iU'.f 1 1 rfl y),
      ← iU.comm 1 2 1 2 rfl rfl rfl rfl u, ← iU'.comm 1 2 1 2 rfl rfl rfl rfl y,
      Subsingleton.elim (U.d 1 2 rfl u) 0, Subsingleton.elim (U'.d 1 2 rfl y) 0]
    simp
  obtain ⟨z, hz⟩ := h2.1 _ hcoc (hiso u y)
  exact ⟨z, hz⟩

end QuasiIsoGeneric

/-! ### (A) for the Galois data of lane RC26 -/

section Galois

open ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]

/-- The genuine local complex vanishes in negative degrees. PROVED. -/
theorem orth_locAt_neg (v : Places K S) (i : ℤ) (hi : i < 0) :
    Subsingleton ((locAt K S R M v).X i) :=
  match i, hi with
  | Int.negSucc _, _ => inferInstanceAs (Subsingleton PUnit)
  | Int.ofNat n, h => absurd h (by change ¬ ((n : ℤ) < 0); omega)

/-- **The cohomology comparisons of a local condition in degrees `0, 1`**: `H⁰(U) → H⁰(C)` is
injective and surjective, and `H¹(U) → H¹(C)` is injective (for a condition concentrated in
degrees `0, 1`). -/
def OrthH01At {v : Places K S} (c : CondAt K S R M v) : Prop :=
  (∀ u : c.U.X 0, c.U.d 0 1 rfl u = 0 → c.i.f 0 0 rfl u = 0 → u = 0) ∧
  (∀ z : (locAt K S R M v).X 0, (locAt K S R M v).d 0 1 rfl z = 0 →
    ∃ u : c.U.X 0, c.U.d 0 1 rfl u = 0 ∧ c.i.f 0 0 rfl u = z) ∧
  (∀ (u : c.U.X 1) (x : (locAt K S R M v).X 0), (locAt K S R M v).d 0 1 rfl x = c.i.f 1 1 rfl u →
    ∃ u₀ : c.U.X 0, c.U.d 0 1 rfl u₀ = u)

variable (β : M →ₗ[R] M' →ₗ[R] T)
  (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- **The annihilator condition of a pair of local conditions at `v`** (cocycle form of "the Kummer
image is its exact local annihilator", tex 3423, 3439–3443): (ISO) the trace of the cup product of
two degree-one elements vanishes; (ANN) a `1`-cocycle of `C(G_{K_v}, M)` whose cup products with
`i'(U'¹)` have trace zero lies in `i(U¹) + B¹`. -/
def OrthKummerAnnihilator {v : Places K S} (c : CondAt K S R M v) (c' : CondAt K S R M' v)
    (trv : (locAt K S R T v).X 2 →ₗ[R] R) : Prop :=
  (∀ (u : c.U.X 1) (y : c'.U.X 1),
    trv ((orthGaloisPair K β hβ v).P 1 1 2 rfl (c.i.f 1 1 rfl u) (c'.i.f 1 1 rfl y)) = 0) ∧
  (∀ x : (locAt K S R M v).X 1, (locAt K S R M v).d 1 2 rfl x = 0 →
    (∀ y : c'.U.X 1, trv ((orthGaloisPair K β hβ v).P 1 1 2 rfl x (c'.i.f 1 1 rfl y)) = 0) →
      ∃ (u : c.U.X 1) (z : (locAt K S R M v).X 0), x = c.i.f 1 1 rfl u + (locAt K S R M v).d 0 1 rfl z)

/-- **Isotropy from (ISO)**: the annihilator condition and `InducesIsoH2` give `OrthIsotropicAt`.
PROVED. -/
theorem orthLD_isotropicAt {v : Places K S} (c : CondAt K S R M v) (c' : CondAt K S R M' v)
    (trv : (locAt K S R T v).X 2 →ₗ[R] R) (hc : OrthConcentratedAt c) (hc' : OrthConcentratedAt c')
    (hann : OrthKummerAnnihilator β hβ c c' trv) (h2 : InducesIsoH2 trv) :
    OrthIsotropicAt β hβ c c' :=
  orthLD_isotropic c.i c'.i (orthGaloisPair K β hβ v) trv hc hc' hann.1 h2

/-- **(A) `orthPerPlace_of_localDuality`: the per-place map is a quasi-isomorphism, from local
duality.** At a place `v`, for a self-injective coefficient ring, local conditions concentrated in
degrees `0, 1` with the `H⁰`/`H¹` comparisons (`OrthH01At`), the annihilator condition
(`OrthKummerAnnihilator`), and the local duality quasi-isomorphism
`C(G_{K_v}, M) → Hom_R(C(G_{K_v}, M'), R)[−2]` (the conclusion of lane RC26's PRINT
`NekovarProp524`), the per-place local duality map of `OrthPlaces` is a quasi-isomorphism, for
every `τ≥2` isotropy homotopy. PROVED. -/
theorem orthPerPlace_of_localDuality [Module.Injective R R] {v : Places K S}
    (c : CondAt K S R M v) (c' : CondAt K S R M' v)
    (J : LocalTruncIsotropy c.i c'.i (orthGaloisPair K β hβ v))
    (trv : (locAt K S R T v).X 2 →ₗ[R] R) (htrv : ∀ z, trv ((locAt K S R T v).d 1 2 rfl z) = 0)
    (hLD : QuasiIso (GHom.toCC (adjHom (orthGaloisPair K β hβ v) 2 trv htrv)))
    (hc : OrthConcentratedAt c) (hc' : OrthConcentratedAt c') (hH : OrthH01At c)
    (hH' : OrthH01At c') (hann : OrthKummerAnnihilator β hβ c c' trv) :
    QuasiIso (GHom.toCC (orthLocalMap c.i c'.i (orthGaloisPair K β hβ v) J trv htrv)) :=
  orthLD_quasiIso c.i c'.i (orthGaloisPair K β hβ v) J trv htrv hc hc' hLD
    (orth_locAt_neg (R := R) (M := M) v) (orth_locAt_neg (R := R) (M := M') v) hH.1 hH.2.1 hH.2.2
    hH'.1 hH'.2.1 hH'.2.2 hann.2

end Galois


/-! ### The `H⁰`/`H¹` comparisons and non-vacuity -/

section Comparisons

open ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {R : Type} [CommRing R] {M M' T : Type}
  [AddCommGroup M] [Module R M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) R M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module R M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) R M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module R T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) R T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]

/-- **Lane RC28's Kummer condition satisfies the `H⁰`/`H¹` comparisons** (`U⁰ = C⁰` and
`U¹ ⊇ B¹`, with the inclusions). PROVED. -/
theorem orth_kummerAt_h01 (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (B : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] (m : ℕ) [NeZero m]
    (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t) :
    OrthH01At (kummerAt (k := R) v B m ι hι) := by
  refine ⟨fun u _ hu => Subtype.ext hu, ?_, ?_⟩
  · intro z hz
    refine ⟨⟨z, trivial⟩, Subtype.ext ?_, rfl⟩
    exact (cocycleCondition_d₀ (kummerZ' R ι) (kummerZ'_cocycle R ι hι) ⟨z, trivial⟩).trans hz
  · intro u x hx
    refine ⟨⟨x, trivial⟩, Subtype.ext ?_⟩
    exact (cocycleCondition_d₀ (kummerZ' R ι) (kummerZ'_cocycle R ι hι) ⟨x, trivial⟩).trans hx

/-- Non-vacuity of `OrthH01At`: the full condition. PROVED. -/
theorem orth_fullAt_h01 (v : Places K S) : OrthH01At (fullAt K S R M v) :=
  ⟨fun _ _ hu => hu, fun z hz => ⟨z, hz, rfl⟩, fun _ x hx => ⟨x, hx⟩⟩

variable (β : M →ₗ[R] M' →ₗ[R] T)
  (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- Non-vacuity of `OrthKummerAnnihilator`: the pair (full condition, zero condition), for every
trace. PROVED. -/
theorem orth_fullAt_zeroAt_annihilator (v : Places K S) (trv : (locAt K S R T v).X 2 →ₗ[R] R) :
    OrthKummerAnnihilator β hβ (fullAt K S R M v) (zeroAt K S R M' v) trv := by
  refine ⟨fun u y => ?_, fun x _ _ => ⟨x, 0, by rw [map_zero, add_zero]; rfl⟩⟩
  have hy : (zeroAt K S R M' v).i.f 1 1 rfl y = 0 := rfl
  rw [hy, map_zero, map_zero]

/-- **The bridge from the coboundary forms to `OrthKummerAnnihilator`**, for two Kummer conditions
of lane RC28 (`kummerAt`, the cocycle conditions `[C⁰ --d⁰--> kummerZ' ⊔ B¹]`), stated with lane
RC26's `contCup`, `contD`, `contB1` and lane RC28's `kummerZ'`: (ISO) the cup products of elements of
`kummerZ' ⊔ B¹` on both sides are coboundaries; (ANN) a `1`-cocycle of `C(G_{K_v}, M)` whose cup
products with all of `kummerZ' ⊔ B¹` (dual side) are coboundaries lies in `kummerZ' ⊔ B¹`. With a
trace killing coboundaries and inducing `H² ≅ R`, these give `OrthKummerAnnihilator`. PROVED. -/
theorem orthKummerAnnihilator_of_cup (v : Places K S) [DecidableEq (v.1.adicCompletion K)]
    (B B' : WeierstrassCurve (v.1.adicCompletion K)) [B.IsElliptic] [B'.IsElliptic] (m : ℕ)
    [NeZero m] (ι : TorsAlg (v.1.adicCompletion K) B m →+ ResMod (locMap K S v.1) M)
    (hι : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B m), ι (σ • t) = σ • ι t)
    (ι' : TorsAlg (v.1.adicCompletion K) B' m →+ ResMod (locMap K S v.1) M')
    (hι' : ∀ (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) B' m), ι' (σ • t) = σ • ι' t)
    (trv : (locAt K S R T v).X 2 →ₗ[R] R) (htrv : ∀ z, trv ((locAt K S R T v).d 1 2 rfl z) = 0)
    (h2 : InducesIsoH2 trv)
    (hISO : ∀ u : contCochain R (Gloc K v.1) (ResMod (locMap K S v.1) M) 1,
      u ∈ kummerZ' R ι ⊔ contB1 R (Gloc K v.1) (ResMod (locMap K S v.1) M) →
      ∀ u' : contCochain R (Gloc K v.1) (ResMod (locMap K S v.1) M') 1,
      u' ∈ kummerZ' R ι' ⊔ contB1 R (Gloc K v.1) (ResMod (locMap K S v.1) M') →
        contCup (resPairing R (GKS K S) β (locMap K S v.1)) (continuous_pairing _) 1 1 2 rfl u u' ∈
          LinearMap.range (contD R (Gloc K v.1) (ResMod (locMap K S v.1) T) 1))
    (hANN : ∀ y : contCochain R (Gloc K v.1) (ResMod (locMap K S v.1) M) 1,
      contD R (Gloc K v.1) (ResMod (locMap K S v.1) M) 1 y = 0 →
      (∀ u' : contCochain R (Gloc K v.1) (ResMod (locMap K S v.1) M') 1,
        u' ∈ kummerZ' R ι' ⊔ contB1 R (Gloc K v.1) (ResMod (locMap K S v.1) M') →
          contCup (resPairing R (GKS K S) β (locMap K S v.1)) (continuous_pairing _) 1 1 2 rfl y u' ∈
            LinearMap.range (contD R (Gloc K v.1) (ResMod (locMap K S v.1) T) 1)) →
        y ∈ kummerZ' R ι ⊔ contB1 R (Gloc K v.1) (ResMod (locMap K S v.1) M)) :
    OrthKummerAnnihilator β hβ (kummerAt (k := R) v B m ι hι) (kummerAt (k := R) v B' m ι' hι')
      trv := by
  refine ⟨fun u y => ?_, fun x hx horth => ?_⟩
  · change ↥(kummerZ' R ι ⊔ contB1 R (Gloc K v.1) (ResMod (locMap K S v.1) M)) at u
    change ↥(kummerZ' R ι' ⊔ contB1 R (Gloc K v.1) (ResMod (locMap K S v.1) M')) at y
    obtain ⟨z, hz⟩ := hISO u.1 u.2 y.1 y.2
    change trv (contCup (resPairing R (GKS K S) β (locMap K S v.1)) (continuous_pairing _) 1 1 2 rfl
      u.1 y.1) = 0
    rw [← hz]
    exact htrv z
  · have hc' := orth_kummerAt_concentrated (R := R) v B' m ι' hι'
    have hmem : x ∈ kummerZ' R ι ⊔ contB1 R (Gloc K v.1) (ResMod (locMap K S v.1) M) := by
      refine hANN x hx fun u' hu' => ?_
      have : Subsingleton ((kummerAt (k := R) v B' m ι' hι').U.X 2) := hc' 2 (by norm_num) (by norm_num)
      have hdu' : (locAt K S R M' v).d 1 2 rfl u' = 0 := by
        have e := (kummerAt (k := R) v B' m ι' hι').i.comm 1 2 1 2 rfl rfl rfl rfl
          (⟨u', hu'⟩ : (kummerAt (k := R) v B' m ι' hι').U.X 1)
        rw [Subsingleton.elim ((kummerAt (k := R) v B' m ι' hι').U.d 1 2 rfl ⟨u', hu'⟩) 0,
          map_zero] at e
        exact e.symm
      have hcoc : (locAt K S R T v).d 2 3 rfl
          ((orthGaloisPair K β hβ v).P 1 1 2 rfl x u') = 0 := by
        rw [(orthGaloisPair K β hβ v).leib 1 2 1 2 2 3 rfl rfl rfl rfl x u']
        change (orthGaloisPair K β hβ v).P 2 1 3 _ ((locAt K S R M v).d 1 2 rfl x) u' +
          sgn 1 • (orthGaloisPair K β hβ v).P 1 2 3 _ x ((locAt K S R M' v).d 1 2 rfl u') = 0
        rw [hx, hdu', map_zero, map_zero, smul_zero, add_zero]
        rfl
      obtain ⟨w, hw⟩ := h2.1 _ hcoc (horth ⟨u', hu'⟩)
      exact ⟨w, hw⟩
    exact ⟨⟨x, hmem⟩, 0, by rw [map_zero, add_zero]; rfl⟩

end Comparisons

/-! ### (B) The actual Kummer pair: the per-place inputs from local duality -/

section ActualKummer

open ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (W : WeierstrassCurve K) [W.IsElliptic] (i : ℕ) [NeZero i] (α : GKS K S₀ →* (Acoef i)ˣ)
  [IsOpenKer α] (hμ₀ : HasRootsOfUnity K S₀ (2 ^ i))
  [TopologicalSpace (Acoef i)] [DiscreteTopology (Acoef i)]
  [∀ v : Places K S, DecidableEq (v.1.adicCompletion K)]
  (B B' : ∀ v : Places K S, WeierstrassCurve (v.1.adicCompletion K)) [∀ v, (B v).IsElliptic]
  [∀ v, (B' v).IsElliptic]
  (ι : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B v) (2 ^ i) →+
    ResMod (locMap K S v.1) (MinS hS W i α))
  (hι : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B v) (2 ^ i)),
    ι v (σ • t) = σ • ι v t)
  (ι' : ∀ v : Places K S, TorsAlg (v.1.adicCompletion K) (B' v) (2 ^ i) →+
    ResMod (locMap K S v.1) (MinS hS W i (charInv α)))
  (hι' : ∀ v (σ : Gloc K v.1) (t : TorsAlg (v.1.adicCompletion K) (B' v) (2 ^ i)),
    ι' v (σ • t) = σ • ι' v t)
  (trv : ∀ v : Places K S, (localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).X 2 →ₗ[Acoef i] Acoef i)

/-- **The isotropy of the actual Kummer pair, from the annihilator condition** (ISO) and
`InducesIsoH2` at the places of `S₀`. PROVED. -/
theorem orthKummerIsotropic
    (hannK : ∀ (v : Places K S) (h : v.1 ∈ S₀), OrthKummerAnnihilator
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h) (trv v))
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v)) :
    ∀ v h, OrthIsotropicAt (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h) :=
  fun v h => orthLD_isotropicAt _ _ _ _ (trv v)
    (orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
    (orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v)) (hannK v h) (htrv2 v)

variable (htrv : ∀ v z, trv v ((localCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
    (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀)) v).d 1 2 rfl z) = 0)

/-- **The per-place quasi-isomorphism for the actual Kummer pair, from local duality**: lane
RC26's PRINT `NekovarProp524` (Nekovář 5.2.4) at the Selmer support `S`, the annihilator
condition, and the PROVED shape of `kummerAt`. Hypotheses besides the annihilator condition: the
standing setting for `S` (`hK`, `hSfin`, the primes above `2` in `S₀ ⊆ S`), `FullTorsion` (GLUE of
lane RC28) and `hT` (GLUE: the inflation of `A_i(1)` to `G_{K,S}` is a cyclotomic twist).
PROVED (from these). -/
theorem orthKummerPerf (h524 : NekovarProp524 K) (hK : IsTotallyComplex K) (hSfin : S.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hW : FullTorsion K S₀ W (2 ^ i))
    (hT : IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (hannK : ∀ (v : Places K S) (h : v.1 ∈ S₀), OrthKummerAnnihilator
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h) (trv v))
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v)) (v : Places K S) (h : v.1 ∈ S₀)
    (J : LocalTruncIsotropy (kummerAt v (B v) (2 ^ i) (ι v) (hι v)).i
      (kummerAt v (B' v) (2 ^ i) (ι' v) (hι' v)).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) v)) :
    QuasiIso (GHom.toCC (orthLocalMap (kummerAt v (B v) (2 ^ i) (ι v) (hι v)).i
      (kummerAt v (B' v) (2 ^ i) (ι' v) (hι' v)).i
      (orthUrPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α)
        (weilPairingM_smul W hμ₀ (Acoef i) α) v) J (trv v) (htrv v))) := by
  have hset := nekovarFiniteSetting_acoef K hK S hSfin (fun v hv => hS (h2₀ v hv)) i
  have := hset.selfInjective
  have : Finite (MinS hS W i α) := inferInstanceAs (Finite (Mcoef K S₀ W i α))
  have : Finite (MinS hS W i (charInv α)) := inferInstanceAs (Finite (Mcoef K S₀ W i (charInv α)))
  exact orthPerPlace_of_localDuality _ _ (kummerAt v (B v) (2 ^ i) (ι v) (hι v))
    (kummerAt v (B' v) (2 ^ i) (ι' v) (hι' v)) J (trv v) (htrv v)
    (h524 S 2 (Acoef i) hset (MinS hS W i α) (MinS hS W i (charInv α))
      (InflMod hS (Tate1 (Acoef i) hμ₀)) (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (weilPairingM_bijective W hμ₀ (Acoef i) α hW)
      (weilPairingM_flip_bijective W hμ₀ (Acoef i) α hW) hT v (trv v) (htrv v) (htrv2 v))
    (orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
    (orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v))
    (orth_kummerAt_h01 v (B v) (2 ^ i) (ι v) (hι v))
    (orth_kummerAt_h01 v (B' v) (2 ^ i) (ι' v) (hι' v)) (hannK v h)


include htrv in
/-- **(B) `OrthogonalComplementsT` for the actual Kummer data, with the Kummer inputs derived from
local duality**: as `orthogonalComplementsT_actualKummer` (lane RC28's actual conditions, Kummer at
`S₀`, unramified at `S − S₀`, `M_i` against `M_i(α⁻¹)`), with the ELLIOT hypotheses `hisoK`,
`hperfK` replaced by lane RC26's PRINT `NekovarProp524` (Nekovář 5.2.4, local duality), the
cocycle-level annihilator condition `OrthKummerAnnihilator` at the places of `S₀` (the content of
"the Kummer image is its exact local annihilator", tex 3423, 3439–3443; see
`orthKummerAnnihilator_of_cup` for its coboundary form), `InducesIsoH2` at every place, and the
GLUE `hT` (the inflation of `A_i(1)` to `G_{K,S}` is a cyclotomic twist). PROVED (from these). -/
theorem orthogonalComplementsT_actualKummer_of_annihilator [Fintype (Places K S)]
    (h524 : NekovarProp524 K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hS₀fin : S₀.Finite) (hSfin : S.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hW : FullTorsion K S₀ W (2 ^ i))
    (hT : IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))
    (hannK : ∀ (v : Places K S) (h : v.1 ∈ S₀), OrthKummerAnnihilator
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h) (trv v))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v))
        (orthKummerIsotropic hS W i α hμ₀ B B' ι hι ι' hι' trv hannK htrv2))).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v))
        (orthKummerIsotropic hS W i α hμ₀ B B' ι hι ι' hι' trv hannK htrv2))).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v)) :
    OrthogonalComplementsT K
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v))
        (orthKummerIsotropic hS W i α hμ₀ B B' ι hι ι' hι' trv hannK htrv2)) tr htr :=
  orthogonalComplementsT_actualKummer hS W i α hμ₀ B B' ι hι ι' hι' (h756 := h756) (hK := hK)
    (hS₀fin := hS₀fin) (h2₀ := h2₀) (hW := hW)
    (hisoK := orthKummerIsotropic hS W i α hμ₀ B B' ι hι ι' hι' trv hannK htrv2) (trv := trv)
    (htrv := htrv) (htrv2 := fun v _ => htrv2 v)
    (hperfK := fun v h => orthKummerPerf hS W i α hμ₀ B B' ι hι ι' hι' trv htrv h524 hK hSfin h2₀ hW
      hT hannK htrv2 v h _) (tr := tr) (htr := htr) (hsum := hsum)

include htrv in
/-- **(B) Finite Selmer duality for the actual Kummer data, with the Kummer inputs derived from
local duality** (Lemma `ex:arith-conjugate-duality`, tex 2761–2830; Nekovář 6.3.4 through lane
RC26's `genuineSelmerDualityT`): as `orthSelmerDuality_actualKummer`, with `hisoK`, `hperfK`
replaced as in `orthogonalComplementsT_actualKummer_of_annihilator`. PROVED (from the PRINTs
`NekovarProp543T`, `NekovarProp524`, `NekovarProp756`, the GLUE `FullTorsion`, `hT`, the
annihilator condition and the trace hypotheses). -/
theorem orthSelmerDuality_actualKummer_of_annihilator [Fintype (Places K S)]
    (h543 : NekovarProp543T K) (h524 : NekovarProp524 K) (h756 : NekovarProp756 K)
    (hK : IsTotallyComplex K) (hS₀fin : S₀.Finite) (hSfin : S.Finite)
    (h2₀ : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S₀)
    (hW : FullTorsion K S₀ W (2 ^ i))
    (hT : IsCyclotomicTwist K S (Acoef i) (InflMod hS (Tate1 (Acoef i) hμ₀)))
    (htrv2 : ∀ v : Places K S, InducesIsoH2 (trv v))
    (hannK : ∀ (v : Places K S) (h : v.1 ∈ S₀), OrthKummerAnnihilator
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (orthKummerC hS W i α B ι hι v h) (orthKummerC' hS W i α B' ι' hι' v h) (trv v))
    (tr : (galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v))
        (orthKummerIsotropic hS W i α hμ₀ B B' ι hι ι' hι' trv hannK htrv2))).X 3 →ₗ[Acoef i] Acoef i)
    (htr : ∀ z, tr ((galoisCompactTT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v))
        (orthKummerIsotropic hS W i α hμ₀ B B' ι hι ι' hι' trv hannK htrv2))).d 2 3 rfl z) = 0)
    (hsum : ∀ z : (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))).X (3 - 1),
      tr ((0 : (globalCx (Acoef i) (GKS K S) (InflMod hS (Tate1 (Acoef i) hμ₀))).X 3),
        (truncSub (localSumCx (Acoef i) (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS (Tate1 (Acoef i) hμ₀))) (3 - 1)).mkQ z) =
        ∑ v, trv v (z v))
    (htr3 : InducesIsoH3 tr) :
    QuasiIso (GHom.toCC (selmerDualityMap (galoisPairDataT K S (Acoef i)
      (orthInflPair hS (Acoef i) (weilPairingM W hμ₀ (Acoef i) α))
      (orthInflPair_smul hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α))
      (ofCondAt K S (Acoef i) (MinS hS W i α)
        (urOutside hS (Acoef i) (Mcoef K S₀ W i α) (orthKummerC hS W i α B ι hι)))
      (ofCondAt K S (Acoef i) (MinS hS W i (charInv α))
        (urOutside hS (Acoef i) (Mcoef K S₀ W i (charInv α)) (orthKummerC' hS W i α B' ι' hι')))
      (orthOutsideTrunc hS (Acoef i) _ (weilPairingM_smul W hμ₀ (Acoef i) α)
        (orthKummerC hS W i α B ι hι) (orthKummerC' hS W i α B' ι' hι')
        (fun v _ => orth_kummerAt_concentrated v (B v) (2 ^ i) (ι v) (hι v))
        (fun v _ => orth_kummerAt_concentrated v (B' v) (2 ^ i) (ι' v) (hι' v))
        (orthKummerIsotropic hS W i α hμ₀ B B' ι hι ι' hι' trv hannK htrv2))) tr htr)) :=
  orthSelmerDuality_actualKummer hS W i α hμ₀ B B' ι hι ι' hι' (h543 := h543) (h756 := h756)
    (hSfin := hSfin) (hT := hT) (hK := hK) (hS₀fin := hS₀fin) (h2₀ := h2₀) (hW := hW)
    (hisoK := orthKummerIsotropic hS W i α hμ₀ B B' ι hι ι' hι' trv hannK htrv2) (trv := trv)
    (htrv := htrv) (htrv2 := fun v _ => htrv2 v)
    (hperfK := fun v h => orthKummerPerf hS W i α hμ₀ B B' ι hι ι' hι' trv htrv h524 hK hSfin h2₀ hW
      hT hannK htrv2 v h _) (tr := tr) (htr := htr) (hsum := hsum) (htr3 := htr3)

end ActualKummer

end ZInQ.Manuscript.RC.KummerMaps
