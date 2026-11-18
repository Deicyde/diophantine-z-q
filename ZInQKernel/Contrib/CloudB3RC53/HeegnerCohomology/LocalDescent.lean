import ZInQKernel.Contrib.CloudB3RC53.HeegnerCohomology.InfRes
import Mathlib.FieldTheory.Galois.NormalBasis

/-!
# HeegnerCohomology, part 2: integral local descent at the old places, (H10)

Manuscript `diophantine_zq.tex`, proof of Proposition `ex:arith-finite-heegner`, paragraph 5
"Integral local descent at the old places", tex 3034–3067.

Elliot's claim (H10): for a finite unramified extension `F'/F` of nonarchimedean local fields and
an elliptic curve `B/F`,

`H¹(Gal(F'/F), B₀(F')) = 0`,  `c_B H¹(Gal(F'/F), B(F')) = 0`,

`c_B = #Φ_B(k̄_F)`.  His proof (tex 3041–3057): reduce a cocycle to the connected smooth special
fibre, where Lang's theorem kills `H¹`; lift the coboundary through the smooth reduction map; the
remaining cocycle lies in the formal group, whose successive quotients are additive copies of the
residue field `k'` of `F'`, induced modules by the normal basis theorem; correct successively; the
corrections converge in `B₁(F')`.  The second assertion follows from the component sequence.

Néron models, formal groups and the reduction map of an elliptic curve over a local field are
not available in Lean.  We therefore prove Elliot's argument in the following form, with every
geometric input an explicit hypothesis on a group `Γ` (for `Gal(F'/F)`) acting on an abelian group
`B` (for `B(F')`):

* `coboundary_of_filtration` (`PROVED`): a complete separated `Γ`-stable filtration
  `B₀ = F 0 ⊇ F 1 ⊇ ⋯` with `Γ`-equivariant surjections `π i : F i → Q i` of kernel `F (i+1)` and
  `H¹(Γ, Q i) = 0` for all `i` has `H¹(Γ, B₀) = 0`.  This is the successive-correction argument
  of tex 3043–3053.  For `i = 0`, `Q 0 = B̃₀(k')` (points of the connected smooth special fibre)
  and `H¹(Γ, Q 0) = 0` is Lang's theorem (hypothesis `hLang`, the printed result
  [Lang 1956, Theorem 1 and its corollary] as cited, `UNVERIFIED`; lane RC9 states Lang).  For
  `i ≥ 1`, `Q i = k'` with its additive Galois action [Silverman IV.3.2(a), p. 124, `UNVERIFIED`],
  and `H¹(Γ, k') = 0` is proved below from the normal basis theorem.
* `additive_H1_eq_zero_of_trace_one`, `galois_additive_coboundary` (`PROVED`): for a finite
  Galois extension `L/K`, `H¹(Gal(L/K), L) = 0`.  Elliot: "a normal basis makes this an induced
  module, so its positive-degree cohomology vanishes"; we use the normal basis
  (`IsGalois.normalBasis` input `exists_linearIndependent_algEquiv_apply`) to produce an element
  of trace one, which is the contracting homotopy of the induced module.
* `component_kills` (`PROVED`): if `c_B` maps `B` into `B₀` (the component group
  `B(F')/B₀(F') ⊂ Φ_B(k̄)` has exponent dividing `c_B`) and `H¹(Γ, B₀) = 0`, then `c_B` kills
  `H¹(Γ, B)` (tex 3056–3057, "the component exact sequence proves the second assertion").
* `H10_killH1` (`PROVED`): the same statement for Tau Ceti's continuous `H1`, which is the field
  `hH10` of RC10's interface `LocalDescentInput` with `Hinf = H¹(Gal(F'/F), B(F'))`.
* `exInf_genuine` (`PROVED`): the field `exInf` of `LocalDescentInput` (the kernel of
  `res : H¹(F, B) → H¹(F', B)` is the image of inflation, tex 3060–3061) for continuous
  cohomology.
-/

namespace ZInQ.Contrib.CloudB3RC53.HeegnerCohomology

open groupCohomology

section Filtration

variable {Γ B : Type*} [Group Γ] [AddCommGroup B] [DistribMulAction Γ B]

/-- The successive corrections: a sequence of cocycles `f i` with values in `F i`, together with
the chosen primitives `m i ∈ F i` with `f (i+1) = f i - d(m i)`. -/
private noncomputable def corr (F : ℕ → AddSubgroup B)
    (hstep : ∀ i (f : Γ → B), IsCocycle₁ f → (∀ g, f g ∈ F i) →
      ∃ m ∈ F i, ∀ g, f g - (g • m - m) ∈ F (i + 1))
    (f : Γ → B) (hf : IsCocycle₁ f) (hf0 : ∀ g, f g ∈ F 0) :
    (i : ℕ) → {p : (Γ → B) × B // IsCocycle₁ p.1 ∧ (∀ g, p.1 g ∈ F i) ∧ p.2 ∈ F i ∧
      ∀ g, p.1 g - (g • p.2 - p.2) ∈ F (i + 1)}
  | 0 => ⟨(f, (hstep 0 f hf hf0).choose), hf, hf0, (hstep 0 f hf hf0).choose_spec.1,
      (hstep 0 f hf hf0).choose_spec.2⟩
  | i + 1 =>
    let p := corr F hstep f hf hf0 i
    let f' : Γ → B := fun g => p.1.1 g - (g • p.1.2 - p.1.2)
    have hf' : IsCocycle₁ f' := by
      intro g h
      simp only [f', p.2.1 g h, mul_smul, smul_sub]
      abel
    ⟨(f', (hstep (i + 1) f' hf' p.2.2.2.2).choose), hf', p.2.2.2.2,
      (hstep (i + 1) f' hf' p.2.2.2.2).choose_spec.1,
      (hstep (i + 1) f' hf' p.2.2.2.2).choose_spec.2⟩

/-- **The successive-correction argument** (tex 3043–3053), `PROVED`.  Let `F` be a decreasing
`Γ`-stable filtration of `B` by subgroups which is separated (`⋂ F i = 0`) and complete (every
series `∑ x i` with `x i ∈ F i` converges: some `s` has `s - ∑_{j<i} x j ∈ F i` for all `i`).
Suppose that for each `i`, every cocycle with values in `F i` is a coboundary of an element of
`F i` modulo `F (i+1)`.  Then every cocycle with values in `F 0` is the coboundary of an element
of `F 0`. -/
theorem coboundary_of_filtration_step (F : ℕ → AddSubgroup B)
    (hstable : ∀ i (g : Γ), ∀ x ∈ F i, g • x ∈ F i)
    (hsep : ∀ x : B, (∀ i, x ∈ F i) → x = 0)
    (hcomplete : ∀ x : ℕ → B, (∀ i, x i ∈ F i) →
      ∃ s : B, ∀ i, s - ∑ j ∈ Finset.range i, x j ∈ F i)
    (hstep : ∀ i (f : Γ → B), IsCocycle₁ f → (∀ g, f g ∈ F i) →
      ∃ m ∈ F i, ∀ g, f g - (g • m - m) ∈ F (i + 1))
    (f : Γ → B) (hf : IsCocycle₁ f) (hf0 : ∀ g, f g ∈ F 0) :
    ∃ s ∈ F 0, ∀ g, g • s - s = f g := by
  set c := corr F hstep f hf hf0
  -- `f i = f - d(∑_{j<i} m j)`
  have hrel : ∀ i g, (c i).1.1 g =
      f g - (g • (∑ j ∈ Finset.range i, (c j).1.2) - ∑ j ∈ Finset.range i, (c j).1.2) := by
    intro i
    induction i with
    | zero => intro g; simp [c, corr]
    | succ i ih =>
      intro g
      show (c i).1.1 g - (g • (c i).1.2 - (c i).1.2) = _
      rw [ih g, Finset.sum_range_succ, smul_add]
      abel
  obtain ⟨s, hs⟩ := hcomplete (fun j => (c j).1.2) (fun j => (c j).2.2.2.1)
  refine ⟨s, by simpa using hs 0, fun g => ?_⟩
  have : f g - (g • s - s) = 0 := by
    apply hsep
    intro i
    set S := ∑ j ∈ Finset.range i, (c j).1.2
    have h1 : f g - (g • s - s) = (c i).1.1 g - (g • (s - S) - (s - S)) := by
      rw [hrel i g, smul_sub]; abel
    rw [h1]
    exact (F i).sub_mem ((c i).2.2.1 g)
      ((F i).sub_mem (hstable i g _ (hs i)) (hs i))
  rw [sub_eq_zero] at this
  exact this.symm

/-- The graded hypothesis of `coboundary_of_filtration_step` from `H¹(Γ, F i / F (i+1)) = 0`,
presented by a `Γ`-equivariant surjection `π : F i → Q` with kernel `F (i+1)` and the vanishing
of `H¹(Γ, Q)` (every cocycle is a coboundary): "reduce a cocycle …; its `H¹` is zero; lift the
resulting coboundary" (tex 3043–3046). -/
theorem step_of_quotient {Q : Type*} [AddCommGroup Q] [DistribMulAction Γ Q]
    (Fi Fi1 : AddSubgroup B) (hstable : ∀ (g : Γ), ∀ x ∈ Fi, g • x ∈ Fi)
    (π : Fi →+ Q) (hπs : Function.Surjective π)
    (hπk : ∀ x : Fi, π x = 0 ↔ (x : B) ∈ Fi1)
    (hπe : ∀ (g : Γ) (x : Fi), π ⟨g • (x : B), hstable g x x.2⟩ = g • π x)
    (hH1 : ∀ f : Γ → Q, IsCocycle₁ f → IsCoboundary₁ f)
    (f : Γ → B) (hf : IsCocycle₁ f) (hfi : ∀ g, f g ∈ Fi) :
    ∃ m ∈ Fi, ∀ g, f g - (g • m - m) ∈ Fi1 := by
  let f' : Γ → Fi := fun g => ⟨f g, hfi g⟩
  have hc : IsCocycle₁ (fun g => π (f' g)) := by
    intro g h
    have : f' (g * h) = ⟨g • (f' h : B), hstable g _ (f' h).2⟩ + f' g :=
      Subtype.ext (by simp [f', hf g h])
    show π (f' (g * h)) = g • π (f' h) + π (f' g)
    rw [this, map_add, hπe]
  obtain ⟨q, hq⟩ := hH1 _ hc
  obtain ⟨m, rfl⟩ := hπs q
  refine ⟨m, m.2, fun g => ?_⟩
  have hk : π (f' g - (⟨g • (m : B), hstable g m m.2⟩ - m)) = 0 := by
    rw [map_sub, map_sub, hπe, hq g, sub_self]
  have := (hπk _).mp hk
  simpa [f'] using this

/-- **(H10), first assertion, abstract form** (tex 3041–3055), `PROVED`.  `Γ = Gal(F'/F)` acts
on `B` (for `B(F')`) with a decreasing `Γ`-stable filtration `F 0 = B₀(F') ⊇ F 1 = B₁(F') ⊇ ⋯`,
separated and complete, and equivariant surjections `π i : F i → Q i` with kernel `F (i+1)`:
`π 0` is the reduction map onto `Q 0 = B̃₀(k')` (smooth reduction; surjective by Hensel), and for
`i ≥ 1`, `Q i ≅ k'` (successive formal quotients).  If `H¹(Γ, Q 0) = 0` (`hLang`: Lang's theorem
with inflation–restriction for the finite residue extension, as Elliot says) and
`H¹(Γ, Q i) = 0` for `i ≥ 1` (`hInd`: the induced module `k'`, `galois_additive_coboundary`), then
`H¹(Γ, B₀(F')) = 0`: every cocycle with values in `B₀(F')` is the coboundary of an element of
`B₀(F')`. -/
theorem coboundary_of_filtration (F : ℕ → AddSubgroup B)
    (hstable : ∀ i (g : Γ), ∀ x ∈ F i, g • x ∈ F i)
    (hsep : ∀ x : B, (∀ i, x ∈ F i) → x = 0)
    (hcomplete : ∀ x : ℕ → B, (∀ i, x i ∈ F i) →
      ∃ s : B, ∀ i, s - ∑ j ∈ Finset.range i, x j ∈ F i)
    (Q : ℕ → Type*) [∀ i, AddCommGroup (Q i)] [∀ i, DistribMulAction Γ (Q i)]
    (π : ∀ i, F i →+ Q i) (hπs : ∀ i, Function.Surjective (π i))
    (hπk : ∀ i (x : F i), π i x = 0 ↔ (x : B) ∈ F (i + 1))
    (hπe : ∀ i (g : Γ) (x : F i), π i ⟨g • (x : B), hstable i g x x.2⟩ = g • π i x)
    (hLang : ∀ f : Γ → Q 0, IsCocycle₁ f → IsCoboundary₁ f)
    (hInd : ∀ i, 1 ≤ i → ∀ f : Γ → Q i, IsCocycle₁ f → IsCoboundary₁ f)
    (f : Γ → B) (hf : IsCocycle₁ f) (hf0 : ∀ g, f g ∈ F 0) :
    ∃ s ∈ F 0, ∀ g, g • s - s = f g := by
  refine coboundary_of_filtration_step F hstable hsep hcomplete (fun i f hf hfi => ?_) f hf hf0
  refine step_of_quotient (F i) (F (i + 1)) (hstable i) (π i) (hπs i) (hπk i) (hπe i) ?_ f hf hfi
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact hLang
  · exact hInd i hi

end Filtration

section AdditiveHilbert90

/-- **The induced-module vanishing** (tex 3050–3051), `PROVED`: if a finite group `Γ` acts on a
commutative ring `L` by ring automorphisms and some `c` has `∑_γ γ • c = 1`, then every additive
cocycle `Γ → L` is a coboundary.  (With `b = ∑_τ f(τ) τ(c)` one has `σ b = b - f(σ)`.) -/
theorem additive_H1_eq_zero_of_trace_one {Γ L : Type*} [Group Γ] [Fintype Γ] [CommRing L]
    [MulSemiringAction Γ L] (c : L) (hc : ∑ γ : Γ, γ • c = 1) (f : Γ → L) (hf : IsCocycle₁ f) :
    IsCoboundary₁ f := by
  refine ⟨-∑ τ : Γ, f τ * (τ • c), fun σ => ?_⟩
  have key : σ • ∑ τ : Γ, f τ * (τ • c) = ∑ τ : Γ, f τ * (τ • c) - f σ := by
    rw [Finset.smul_sum]
    have : ∀ τ : Γ, σ • (f τ * (τ • c)) = f (σ * τ) * ((σ * τ) • c) - f σ * ((σ * τ) • c) := by
      intro τ
      rw [smul_mul', hf σ τ, mul_smul]; ring
    simp only [this, Finset.sum_sub_distrib]
    rw [Fintype.sum_equiv (Equiv.mulLeft σ) (fun τ => f (σ * τ) * ((σ * τ) • c))
        (fun τ => f τ * (τ • c)) (fun τ => rfl)]
    rw [← Finset.mul_sum,
      Fintype.sum_equiv (Equiv.mulLeft σ) (fun τ => (σ * τ) • c) (fun τ => τ • c) (fun τ => rfl),
      hc, mul_one]
  rw [smul_neg, key]
  ring

/-- **`H¹(Gal(L/K), L) = 0` for a finite Galois extension** (tex 3049–3051: "each successive formal
quotient is an additive copy of the residue field of `F'`; a normal basis makes this an induced
module, so its positive-degree cohomology vanishes"), `PROVED`, from the normal basis theorem. -/
theorem galois_additive_coboundary (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (f : Gal(L/K) → L) (hf : IsCocycle₁ f) :
    IsCoboundary₁ f := by
  obtain ⟨x, hx⟩ := exists_linearIndependent_algEquiv_apply K L
  have hsum : ∑ σ : Gal(L/K), σ x ≠ 0 := by
    intro h0
    have := Fintype.linearIndependent_iff.mp hx (fun _ => 1) (by simpa using h0) 1
    exact one_ne_zero this
  have htr : algebraMap K L (Algebra.trace K L x) ≠ 0 := by
    rwa [trace_eq_sum_automorphisms]
  refine additive_H1_eq_zero_of_trace_one ((algebraMap K L (Algebra.trace K L x))⁻¹ * x) ?_ f hf
  have hfix : ∀ σ : Gal(L/K), σ ((algebraMap K L (Algebra.trace K L x))⁻¹) =
      (algebraMap K L (Algebra.trace K L x))⁻¹ := fun σ => by
    rw [map_inv₀, AlgEquiv.commutes]
  simp only [AlgEquiv.smul_def, map_mul, hfix, ← Finset.mul_sum]
  rw [← trace_eq_sum_automorphisms, inv_mul_cancel₀ htr]

end AdditiveHilbert90

section Component

variable {Γ B : Type*} [Group Γ] [AddCommGroup B] [DistribMulAction Γ B]

/-- **(H10), second assertion, abstract form** (tex 3056–3057), `PROVED`: if `c_B • B ⊆ B₀`
(the component group `B(F')/B₀(F')` embeds in `Φ_B(k̄)`, of order `c_B`) and `H¹(Γ, B₀) = 0`
(every cocycle with values in `B₀` is the coboundary of an element of `B₀`), then `c_B` kills
`H¹(Γ, B)`: `c_B • f` is a coboundary for every cocycle `f`. -/
theorem component_kills (B₀ : AddSubgroup B) (cB : ℤ) (hcB : ∀ x : B, cB • x ∈ B₀)
    (hH1 : ∀ f : Γ → B, IsCocycle₁ f → (∀ g, f g ∈ B₀) → ∃ s ∈ B₀, ∀ g, g • s - s = f g)
    (f : Γ → B) (hf : IsCocycle₁ f) : IsCoboundary₁ (fun g => cB • f g) := by
  have hcf : IsCocycle₁ (fun g => cB • f g) := by
    intro g h; simp only [hf g h, smul_add, smul_comm g cB]
  obtain ⟨s, -, hs⟩ := hH1 _ hcf (fun g => hcB _)
  exact ⟨s, hs⟩

end Component

section Continuous

open TauCeti.ContCohomology

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {V : Type*} [AddCommGroup V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [DistribMulAction Γ V] [ContinuousSMul Γ V]

/-- **(H10) for continuous cohomology** (tex 3038–3057), `PROVED`: with `Γ = Gal(F'/F)` and
`V = B(F')`, the hypotheses of `coboundary_of_filtration` on `B₀(F') ⊆ V` and `c_B • V ⊆ B₀(F')`
give `c_B • H¹(Γ, V) = 0`.  This is the field `hH10` of RC10's `LocalDescentInput`
(`ZInQKernel/Contrib/OneProof/RC/HeegnerAlgebra/Interfaces.lean`) for
`Hinf = H1 Γ V`. -/
theorem H10_killH1 (F : ℕ → AddSubgroup V)
    (hstable : ∀ i (g : Γ), ∀ x ∈ F i, g • x ∈ F i)
    (hsep : ∀ x : V, (∀ i, x ∈ F i) → x = 0)
    (hcomplete : ∀ x : ℕ → V, (∀ i, x i ∈ F i) →
      ∃ s : V, ∀ i, s - ∑ j ∈ Finset.range i, x j ∈ F i)
    (Q : ℕ → Type*) [∀ i, AddCommGroup (Q i)] [∀ i, DistribMulAction Γ (Q i)]
    (π : ∀ i, F i →+ Q i) (hπs : ∀ i, Function.Surjective (π i))
    (hπk : ∀ i (x : F i), π i x = 0 ↔ (x : V) ∈ F (i + 1))
    (hπe : ∀ i (g : Γ) (x : F i), π i ⟨g • (x : V), hstable i g x x.2⟩ = g • π i x)
    (hLang : ∀ f : Γ → Q 0, IsCocycle₁ f → IsCoboundary₁ f)
    (hInd : ∀ i, 1 ≤ i → ∀ f : Γ → Q i, IsCocycle₁ f → IsCoboundary₁ f)
    (cB : ℤ) (hcB : ∀ x : V, cB • x ∈ F 0) :
    ∀ z : H1 Γ V, cB • z = 0 := by
  intro z
  induction z using QuotientAddGroup.induction_on with
  | H f =>
    show cB • H1pi Γ V f = 0
    rw [← map_zsmul]
    refine H1pi_eq_zero_iff.mpr ?_
    rw [AddSubgroup.coe_zsmul, mem_B1_iff]
    have hf : IsCocycle₁ (f : Γ → V) := ((mem_Z1_iff (G := Γ) (M := V)).mp f.2).2
    exact component_kills (F 0) cB hcB
      (fun f hf hf0 => coboundary_of_filtration F hstable hsep hcomplete Q π hπs hπk hπe hLang
        hInd f hf hf0) f hf

variable (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [DistribMulAction G M] [ContinuousSMul G M]
  (N : Subgroup G) [N.Normal] [ContinuousSMul (G ⧸ N) (FixedPoints.addSubgroup N M)]

/-- **The field `exInf` of `LocalDescentInput`** (tex 3058–3061: "that kernel is the image of
`H¹(Gal(F'/F), B(F'))`"), `PROVED` for continuous cohomology: with `G = G_F`, `N = G_{F'}` and
`M = B(F̄)`, every class of `H¹(G, M)` restricting to zero on `N` is inflated from
`H¹(G/N, M^N)`, `M^N = B(F')`. -/
theorem exInf_genuine (w : H1 G M) (hw : explicitRes1 G M N w = 0) :
    ∃ z, explicitInfl1 G M N z = w := by
  have : w ∈ (explicitRes1 G M N).ker := hw
  rw [← explicitInfRes_exact] at this
  exact this

end Continuous

/-! ## The node -/

/-- **Node (H10)**, tex 3038–3067 (ex:arith-finite-heegner, paragraph 5), status `PROVED` modulo the
named geometric inputs, which are hypotheses (Néron models and formal groups are not in Lean).
`Γ = Gal(F'/F)` acts on `V = B(F')`; `F i = B_i(F')` is the filtration by the identity component
(`i = 0`) and the formal-group levels (`i ≥ 1`), separated and complete; `π 0 : B₀(F') → B̃₀(k')`
is smooth reduction and `π i : B_i(F') → k'` (`i ≥ 1`) the formal quotients [Silverman IV.3.2(a),
p. 124, `UNVERIFIED`], all surjective, equivariant, with kernels `B_{i+1}(F')`; `hLang` is
Lang's theorem [Lang 1956, Theorem 1 and its corollary, `UNVERIFIED`; an RC print] with
inflation–restriction to the finite residue extension; `hInd` is the vanishing for the induced
module `k'` (`galois_additive_coboundary` for `Gal(k'/k) ≅ Gal(F'/F)`); `hcB` says that the
component group `B(F')/B₀(F') ⊂ Φ_B(k̄)` is killed by `c_B = #Φ_B(k̄)`.  Conclusions:
`H¹(Gal(F'/F), B₀(F')) = 0` and `c_B H¹(Gal(F'/F), B(F')) = 0`. -/
def H10Node : Prop :=
  ∀ (Γ V : Type) [Group Γ] [AddCommGroup V] [DistribMulAction Γ V] (F : ℕ → AddSubgroup V)
    (hstable : ∀ i (g : Γ), ∀ x ∈ F i, g • x ∈ F i)
    (_hsep : ∀ x : V, (∀ i, x ∈ F i) → x = 0)
    (_hcomplete : ∀ x : ℕ → V, (∀ i, x i ∈ F i) →
      ∃ s : V, ∀ i, s - ∑ j ∈ Finset.range i, x j ∈ F i)
    (Q : ℕ → Type) [∀ i, AddCommGroup (Q i)] [∀ i, DistribMulAction Γ (Q i)]
    (π : ∀ i, F i →+ Q i) (_hπs : ∀ i, Function.Surjective (π i))
    (_hπk : ∀ i (x : F i), π i x = 0 ↔ (x : V) ∈ F (i + 1))
    (_hπe : ∀ i (g : Γ) (x : F i), π i ⟨g • (x : V), hstable i g x x.2⟩ = g • π i x)
    (_hLang : ∀ f : Γ → Q 0, IsCocycle₁ f → IsCoboundary₁ f)
    (_hInd : ∀ i, 1 ≤ i → ∀ f : Γ → Q i, IsCocycle₁ f → IsCoboundary₁ f)
    (cB : ℤ) (_hcB : ∀ x : V, cB • x ∈ F 0),
    (∀ f : Γ → V, IsCocycle₁ f → (∀ g, f g ∈ F 0) → ∃ s ∈ F 0, ∀ g, g • s - s = f g) ∧
    (∀ f : Γ → V, IsCocycle₁ f → IsCoboundary₁ (fun g => cB • f g))

theorem h10Node_proof : H10Node := by
  intro Γ V _ _ _ F hstable hsep hcomplete Q _ _ π hπs hπk hπe hLang hInd cB hcB
  have h0 := fun f hf hf0 =>
    coboundary_of_filtration F hstable hsep hcomplete Q π hπs hπk hπe hLang hInd f hf hf0
  exact ⟨h0, fun f hf => component_kills (F 0) cB hcB h0 f hf⟩

/-- **Node: `H¹(Gal(L/K), L) = 0`** for a finite Galois extension (the induced-module input of
(H10) at the formal-group levels, tex 3049–3051), `PROVED`. -/
def AdditiveH90Node : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (f : Gal(L/K) → L), IsCocycle₁ f → IsCoboundary₁ f

theorem additiveH90Node_proof : AdditiveH90Node := by
  intro K L _ _ _ _ _ f hf
  exact galois_additive_coboundary K L f hf

end ZInQ.Contrib.CloudB3RC53.HeegnerCohomology
