import Mathlib
import ZInQKernel.Contrib.OneProof.RC.HeegnerAlgebra.Descent

/-!
# Lane RC10 (Heegner algebra): the sequence (H8) over Mathlib's genuine group cohomology

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
paragraph 4 "Descend once, before twisting", tex 3004–3017 (H8).

`Descent.lean` records the inflation–restriction sequence
`0 → H¹(Γ, V^{G_M}) → H¹(B, V) → H¹(M, V)^Γ → H²(Γ, V^{G_M})` (Nekovář, *Selmer complexes*,
Astérisque 310, (4.1.4.1)) as abstract exactness data `FiveTerm`.  This file proves its first
two exactness properties for Mathlib's group cohomology `groupCohomology A n` of a group `G`
(an abstract, i.e. discrete, group) with coefficients `A : Rep k G` over a commutative ring `k`,
and a normal subgroup `S` of `G`.  In the manuscript's notation `G = G_B`, `S = G_M`,
`G ⧸ S = Γ`, `A = V` and `A^S = V^{G_M}`.  Mathlib's `groupCohomology.H1InfRes A S` is the short
complex `H¹(G ⧸ S, A^S) → H¹(G, A) → H¹(S, A)` (inflation, restriction).

* `infRes_injective_genuine`: inflation is injective (`FiveTerm.inf_injective`);
* `infRes_exact_genuine`: exactness at `H¹(G, A)`, both directions (`FiveTerm.exact_B`);
* `groupCohomology_smul_eq_zero` and its `ℤ`-forms: a scalar killing `A` kills every `Hⁿ(G, A)`;
  so `2^e` kills `Hⁿ(G ⧸ S, A^S)` when it kills `A` (the inputs `killA`, and `killD` when the
  fourth term is `H²(G ⧸ S, A^S)`, of `InfResInput`);
* `conjH1`, `invariantsH1`, `resInvariantsH1`: the conjugation action of `G` on `H¹(S, A)`
  (trivial on `S`, so an action of `Γ`), the invariant classes `H¹(S, A)^Γ`, and restriction
  into them;
* `fiveTermOfGenuine` (third term `H¹(S, A)`), `fiveTermOfGenuineInvariants` (third term
  `H¹(S, A)^Γ`, as in (4.1.4.1)) and `fiveTermOfGenuineFactor` (any subgroup through which
  restriction factors): `FiveTerm` data whose fields `inf_injective` and `exact_B` are proved;
  the fourth term, the transgression and `exact_C` are hypotheses.

All `PROVED` for discrete groups.  Not covered here, and still the `PRINT` input Nekovář
(4.1.4.1): the profinite (continuous) cohomology of Galois groups, the transgression
`H¹(M, V)^Γ → H²(Γ, V^{G_M})` and the exactness at `H¹(M, V)^Γ`.
-/

universe u

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open CategoryTheory

section Genuine

variable {k G : Type u} [CommRing k] [Group G]

/-! ## Inflation and restriction in degree one -/

/-- tex 3004–3017 (H8), `PROVED` (Lean proof, by definition, over Mathlib's group cohomology of
discrete groups; the profinite/continuous version and the transgression term remain the `PRINT`
input Nekovář (4.1.4.1)): the first map of Mathlib's short complex `H1InfRes A S` is inflation
`H¹(G ⧸ S, A^S) → H¹(G, A)`, the map induced by the projection `G → G ⧸ S` and the inclusion
`A^S → A`. -/
theorem infRes_f_eq_inflation (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] :
    (groupCohomology.H1InfRes A S).f =
      groupCohomology.map (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 1 :=
  rfl

/-- tex 3004–3017 (H8), `PROVED` (Lean proof, by definition, over Mathlib's group cohomology of
discrete groups; the profinite/continuous version and the transgression term remain the `PRINT`
input Nekovář (4.1.4.1)): the second map of Mathlib's short complex `H1InfRes A S` is restriction
`H¹(G, A) → H¹(S, A)`, the map induced by the inclusion `S → G`. -/
theorem infRes_g_eq_restriction (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] :
    (groupCohomology.H1InfRes A S).g =
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 1 :=
  rfl

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): inflation `H¹(G ⧸ S, A^S) → H¹(G, A)` is injective, as a function on the underlying
types (the field `inf_injective` of `FiveTerm`). -/
theorem infRes_injective_genuine (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] :
    Function.Injective (groupCohomology.H1InfRes A S).f :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): exactness of `H¹(G ⧸ S, A^S) → H¹(G, A) → H¹(S, A)` at `H¹(G, A)` (the field
`exact_B` of `FiveTerm`): a class restricts to zero if and only if it is inflated.  The
direction `←` is `res ∘ inf = 0`. -/
theorem infRes_exact_genuine (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (b : groupCohomology A 1) :
    (groupCohomology.H1InfRes A S).g b = 0 ↔ ∃ x, (groupCohomology.H1InfRes A S).f x = b := by
  constructor
  · intro h
    exact (ShortComplex.moduleCat_exact_iff _).1 (groupCohomology.H1InfRes_exact A S) b h
  · rintro ⟨x, rfl⟩
    exact ShortComplex.moduleCat_zero_apply _ x

/-! ## A scalar killing the coefficients kills the cohomology -/

/-- tex 3004–3017 (H8), "hence on every cochain and cohomology group", `PROVED` (Lean proof over
Mathlib's group cohomology of discrete groups; the profinite/continuous version and the
transgression term remain the `PRINT` input Nekovář (4.1.4.1)): if `c : k` kills `A`, then `c`
kills `Hⁿ(G, A)` for every `n`.  It kills every inhomogeneous cochain `Gⁿ → A`, hence every
cocycle (the cocycles inject into the cochains), hence every class (each class is the image of a
cocycle under a `k`-linear map). -/
theorem groupCohomology_smul_eq_zero (A : Rep.{u} k G) (c : k) (hc : ∀ a : A, c • a = 0)
    (n : ℕ) (x : groupCohomology A n) : c • x = 0 := by
  induction x using groupCohomology_induction_on with
  | h y =>
    have hy : c • y = 0 := by
      apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles A n)).1 inferInstance
      rw [map_smul, map_zero]
      ext g
      exact hc _
    rw [← map_smul, hy, map_zero]

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): the `ℤ`-form of `groupCohomology_smul_eq_zero`, in the shape
`∀ x, ((2 : ℤ) ^ e) • x = 0` of the hypotheses of `FiveTerm.descend_eq`: an integer killing `A`
kills `Hⁿ(G, A)` for every `n`. -/
theorem groupCohomology_zsmul_eq_zero (A : Rep.{u} k G) (m : ℤ) (hm : ∀ a : A, m • a = 0)
    (n : ℕ) (x : groupCohomology A n) : m • x = 0 := by
  rw [← Int.cast_smul_eq_zsmul k]
  exact groupCohomology_smul_eq_zero A (m : k)
    (fun a => by rw [Int.cast_smul_eq_zsmul]; exact hm a) n x

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): an integer killing `A` kills `Hⁿ(G ⧸ S, A^S)` for every `n`.  With `m = 2^e` (by
(H2), `2^e` kills `V`) this is the vanishing of `2^e` on `H¹(Γ, V^{G_M})` (`killA`, the hypothesis
`hA` of `FiveTerm.descend_eq`) and on `H²(Γ, V^{G_M})` (`killD`, `hD`). -/
theorem groupCohomology_quotientToInvariants_zsmul_eq_zero (A : Rep.{u} k G) (S : Subgroup G)
    [S.Normal] (m : ℤ) (hm : ∀ a : A, m • a = 0) (n : ℕ)
    (x : groupCohomology (A.quotientToInvariants S) n) : m • x = 0 :=
  groupCohomology_zsmul_eq_zero (A.quotientToInvariants S) m
    (fun a => Subtype.ext (by simpa using hm a)) n x

/-! ## The conjugation action on `H¹(S, A)` and the invariant classes `H¹(S, A)^Γ` -/

/-- tex 3004–3017 (H8), `PROVED` (Lean definition, with its proof obligations, over Mathlib's
group cohomology of discrete groups; the profinite/continuous version and the transgression term
remain the `PRINT` input Nekovář (4.1.4.1)): conjugation `s ↦ g⁻¹ s g` of the normal subgroup
`S` by `g : G`, as a monoid endomorphism of `S`. -/
def conjOnNormal (S : Subgroup G) [hS : S.Normal] (g : G) : S →* S where
  toFun s := ⟨g⁻¹ * s * g, hS.conj_mem' s s.2 g⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

/-- tex 3004–3017 (H8), `PROVED` (Lean proof, by definition, over Mathlib's group cohomology of
discrete groups; the profinite/continuous version and the transgression term remain the `PRINT`
input Nekovář (4.1.4.1)): the value of `conjOnNormal`. -/
@[simp]
theorem conjOnNormal_apply (S : Subgroup G) [S.Normal] (g : G) (s : S) :
    (conjOnNormal S g s : G) = g⁻¹ * s * g :=
  rfl

/-- tex 3004–3017 (H8), `PROVED` (Lean definition, with its proof obligation, over Mathlib's
group cohomology of discrete groups; the profinite/continuous version and the transgression term
remain the `PRINT` input Nekovář (4.1.4.1)): the action `ρ(g)` of `g : G` on `A` as a morphism
of `S`-representations from `A` restricted along `conjOnNormal S g` to `A`:
`ρ(g) ρ(g⁻¹ s g) = ρ(s) ρ(g)`. -/
noncomputable def conjIntertwiner (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] (g : G) :
    Rep.res (conjOnNormal S g) (Rep.res S.subtype A) ⟶ Rep.res S.subtype A :=
  Rep.ofHom ⟨A.ρ g, fun s => by
    ext a
    simp [← Module.End.mul_apply, ← map_mul, mul_assoc]⟩

/-- tex 3004–3017 (H8), `PROVED` (Lean definition over Mathlib's group cohomology of discrete
groups; the profinite/continuous version and the transgression term remain the `PRINT` input
Nekovář (4.1.4.1)): the conjugation action of `g : G` on `H¹(S, A)`, sending the class of a
cocycle `x` to the class of `s ↦ g · x(g⁻¹ s g)` (Mathlib's `groupCohomology.map` for the
compatible pair `(conjOnNormal S g, conjIntertwiner A S g)`).  It is an action (`conjH1_mul`)
and `S` acts trivially (`conjH1_of_mem`), so it is the action of `Γ = G ⧸ S` on `H¹(M, V)`. -/
noncomputable def conjH1 (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] (g : G) :
    groupCohomology (Rep.res S.subtype A) 1 ⟶ groupCohomology (Rep.res S.subtype A) 1 :=
  groupCohomology.map (conjOnNormal S g) (conjIntertwiner A S g) 1

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): `conjH1` is a (left) action: `(g h) · c = g · (h · c)`. -/
theorem conjH1_mul (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] (g h : G) :
    conjH1 A S (g * h) = conjH1 A S h ≫ conjH1 A S g := by
  rw [conjH1, conjH1, conjH1, ← groupCohomology.map_comp]
  refine groupCohomology.map_congr ?_ ?_ 1
  · ext s; simp [mul_assoc]
  · ext a; simp [conjIntertwiner]

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): `S` acts trivially on `H¹(S, A)` (so `conjH1` factors through `Γ = G ⧸ S`; with
`t = 1` this is also the unit law of the action).  For a cocycle `y` on `S` and `t ∈ S`, the
cocycle `s ↦ t · y(t⁻¹ s t)` differs from `y` by the coboundary of `y(t)`. -/
theorem conjH1_of_mem (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] (t : G) (ht : t ∈ S)
    (c : groupCohomology (Rep.res S.subtype A) 1) : conjH1 A S t c = c := by
  induction c using groupCohomology.H1_induction_on with | h y => ?_
  rw [conjH1, groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_eq_iff]
  refine ⟨y ⟨t, ht⟩, ?_⟩
  funext s
  have h1 := (groupCohomology.mem_cocycles₁_iff (y : S → A)).1 y.2
  have hs : conjOnNormal S t s = (⟨t, ht⟩ : S)⁻¹ * (s * ⟨t, ht⟩) := by
    ext; simp [mul_assoc]
  have e : A.ρ t (y (conjOnNormal S t s)) = A.ρ s (y ⟨t, ht⟩) + y s - y ⟨t, ht⟩ := by
    rw [hs, h1, h1]
    have hi := groupCohomology.cocycles₁_map_inv y ⟨t, ht⟩
    simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      InvMemClass.coe_inv, map_add] at hi ⊢
    simp only [Representation.self_inv_apply, hi]
    abel
  change A.ρ s (y ⟨t, ht⟩) - y ⟨t, ht⟩ = A.ρ t (y (conjOnNormal S t s)) - y s
  rw [e]
  abel

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): restriction lands in the invariant classes.  For a cocycle `x` on `G`,
`g · x(g⁻¹ s g) - x(s) = s · x(g) - x(g)` on `S`, the coboundary of `x(g)`. -/
theorem conjH1_res (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] (g : G)
    (b : groupCohomology A 1) :
    conjH1 A S g ((groupCohomology.H1InfRes A S).g b) = (groupCohomology.H1InfRes A S).g b := by
  induction b using groupCohomology.H1_induction_on with | h x => ?_
  simp only [conjH1, groupCohomology.HInfRes_g, groupCohomology.HInfRes_X₂,
    groupCohomology.HInfRes_X₃]
  rw [groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_comp_map_apply,
    groupCohomology.H1π_eq_iff]
  refine ⟨x g, ?_⟩
  funext s
  have h1 := (groupCohomology.mem_cocycles₁_iff (x : G → A)).1 x.2
  have e : A.ρ g (x (g⁻¹ * s * g)) = A.ρ s (x g) + x s - x g := by
    rw [mul_assoc, h1, h1]
    simp only [map_add, Representation.self_inv_apply, groupCohomology.cocycles₁_map_inv]
    abel
  change A.ρ s (x g) - x g = A.ρ g (x (g⁻¹ * s * g)) - x s
  rw [e]
  abel

/-- tex 3004–3017 (H8), `PROVED` (Lean definition over Mathlib's group cohomology of discrete
groups; the profinite/continuous version and the transgression term remain the `PRINT` input
Nekovář (4.1.4.1)): the invariant classes `H¹(S, A)^Γ` (the manuscript's `H¹(M, V)^Γ`), as the
submodule of classes fixed by `conjH1 A S g` for every `g : G`. -/
noncomputable def invariantsH1 (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] :
    Submodule k (groupCohomology (Rep.res S.subtype A) 1) :=
  ⨅ g : G, LinearMap.ker ((conjH1 A S g).hom - LinearMap.id)

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): membership in `invariantsH1`. -/
theorem mem_invariantsH1 (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (c : groupCohomology (Rep.res S.subtype A) 1) :
    c ∈ invariantsH1 A S ↔ ∀ g : G, conjH1 A S g c = c := by
  simp only [invariantsH1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): restricted classes are invariant, `res H¹(G, A) ⊆ H¹(S, A)^Γ`. -/
theorem res_mem_invariantsH1 (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (b : groupCohomology A 1) : (groupCohomology.H1InfRes A S).g b ∈ invariantsH1 A S :=
  (mem_invariantsH1 A S _).2 fun g => conjH1_res A S g b

/-- tex 3004–3017 (H8), `PROVED` (Lean definition over Mathlib's group cohomology of discrete
groups; the profinite/continuous version and the transgression term remain the `PRINT` input
Nekovář (4.1.4.1)): restriction `H¹(G, A) → H¹(S, A)^Γ`, the second map of (4.1.4.1). -/
noncomputable def resInvariantsH1 (A : Rep.{u} k G) (S : Subgroup G) [S.Normal] :
    groupCohomology A 1 →ₗ[k] invariantsH1 A S :=
  (groupCohomology.H1InfRes A S).g.hom.codRestrict _ (res_mem_invariantsH1 A S)

/-- tex 3004–3017 (H8), `PROVED` (Lean proof, by definition, over Mathlib's group cohomology of
discrete groups; the profinite/continuous version and the transgression term remain the `PRINT`
input Nekovář (4.1.4.1)): followed by the inclusion `H¹(S, A)^Γ ⊆ H¹(S, A)`, `resInvariantsH1` is
Mathlib's restriction. -/
theorem coe_resInvariantsH1 (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    (b : groupCohomology A 1) :
    (resInvariantsH1 A S b : groupCohomology (Rep.res S.subtype A) 1) =
      (groupCohomology.H1InfRes A S).g b :=
  rfl

/-! ## `FiveTerm` data from genuine cohomology -/

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): `FiveTerm` data for genuine cohomology whose third term is any group `C` through
which restriction factors injectively, `ι ∘ res' = res` with `ι : C → H¹(S, A)` injective.  The
fields `inf_injective` and `exact_B` come from `infRes_injective_genuine` and
`infRes_exact_genuine`; the fourth term `D`, the transgression `tg` and the exactness `exact_C`
at `C` are hypotheses. -/
noncomputable def fiveTermOfGenuineFactor (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    {C D : Type*} [AddCommGroup C] [AddCommGroup D]
    (ι : C →+ groupCohomology (Rep.res S.subtype A) 1) (hι : Function.Injective ι)
    (res' : groupCohomology A 1 →+ C)
    (hres' : ∀ b, ι (res' b) = (groupCohomology.H1InfRes A S).g b)
    (tg : C →+ D) (exact_C : ∀ c, tg c = 0 ↔ ∃ b, res' b = c) :
    FiveTerm (groupCohomology (A.quotientToInvariants S) 1) (groupCohomology A 1) C D where
  inf := (groupCohomology.H1InfRes A S).f.hom.toAddMonoidHom
  res := res'
  tg := tg
  inf_injective := infRes_injective_genuine A S
  exact_B b := by
    refine Iff.trans ?_ (infRes_exact_genuine A S b)
    rw [← hres', ← map_zero ι]
    exact hι.eq_iff.symm
  exact_C := exact_C

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): `FiveTerm (H¹(G ⧸ S, A^S)) (H¹(G, A)) (H¹(S, A)) D` with the genuine inflation and
restriction maps.  This uses `H¹(S, A)` in place of the invariants `H¹(M, V)^Γ` of the
manuscript (for those, see `fiveTermOfGenuineInvariants`).  The fields `inf_injective` and
`exact_B` are `infRes_injective_genuine` and `infRes_exact_genuine`; the fourth term `D`, the map
`tg : H¹(S, A) →+ D` and the exactness `exact_C` are hypotheses. -/
noncomputable def fiveTermOfGenuine (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    {D : Type*} [AddCommGroup D] (tg : groupCohomology (Rep.res S.subtype A) 1 →+ D)
    (exact_C : ∀ c, tg c = 0 ↔ ∃ b, (groupCohomology.H1InfRes A S).g b = c) :
    FiveTerm (groupCohomology (A.quotientToInvariants S) 1) (groupCohomology A 1)
      (groupCohomology (Rep.res S.subtype A) 1) D where
  inf := (groupCohomology.H1InfRes A S).f.hom.toAddMonoidHom
  res := (groupCohomology.H1InfRes A S).g.hom.toAddMonoidHom
  tg := tg
  inf_injective := infRes_injective_genuine A S
  exact_B := infRes_exact_genuine A S
  exact_C := exact_C

/-- tex 3004–3017 (H8), `PROVED` (Lean proof over Mathlib's group cohomology of discrete groups;
the profinite/continuous version and the transgression term remain the `PRINT` input Nekovář
(4.1.4.1)): `FiveTerm (H¹(G ⧸ S, A^S)) (H¹(G, A)) (H¹(S, A)^Γ) D`, with the third term the
invariant classes as in (4.1.4.1), the genuine inflation and the restriction `resInvariantsH1`.
The fields `inf_injective` and `exact_B` are proved (`fiveTermOfGenuineFactor`); the fourth term
`D` (in the manuscript `H²(Γ, V^{G_M})`), the transgression `tg` and the exactness `exact_C` at
`H¹(S, A)^Γ` are hypotheses. -/
noncomputable def fiveTermOfGenuineInvariants (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    {D : Type*} [AddCommGroup D] (tg : invariantsH1 A S →+ D)
    (exact_C : ∀ c, tg c = 0 ↔ ∃ b, resInvariantsH1 A S b = c) :
    FiveTerm (groupCohomology (A.quotientToInvariants S) 1) (groupCohomology A 1)
      (invariantsH1 A S) D :=
  fiveTermOfGenuineFactor A S (invariantsH1 A S).subtype.toAddMonoidHom Subtype.val_injective
    (resInvariantsH1 A S).toAddMonoidHom (fun _ => rfl) tg exact_C

end Genuine

end ZInQ.Manuscript.RC.HeegnerAlgebra
