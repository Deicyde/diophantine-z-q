import ZInQKernel.Contrib.OneProof.RC.KummerMaps.OrthPlaces

/-!
# Lane RC29 (item 2 (b)(i)): the unramified conditions are orthogonal complements

Manuscript `diophantine_zq.tex`: the support comparisons (tex 3466–3499: "at augmentation `g = 1`,
this is the direct sum of the unramified complex `[Φ−1]` in degrees zero and one …"; "Use it only
when the actual coefficient representation is unramified at the removed place"), and tex 3815–3818
("The remaining good unramified conditions use the integral unramified comparison"); the
unramified conditions are lane RC28's `urAt` (the inflation of the `ℤ̂`-cocycles of
`[M₀ --(Φ−1)--> M₀]`, lane RC26's `urToLocal_galois`) at the places `w ∈ S − S₀` where the
coefficients are unramified.

**The published statement.** Nekovář, *Selmer complexes*, Astérisque 310 (2006), §7.5 "Duality"
(pp. 168–170; read in the Numdam scan, prose legible, displayed formulas OCR-garbled):
* Lemma 7.5.2 (p. 168): for admissible `R[G_v/P_v]`-modules `M, N` (the tame case `v ∤ p`), the
  composite `C⁺(M) ⊗ C⁺(N) → C(M) ⊗ C(N) → C(G_v, M) ⊗ C(G_v, N) → C(G_v, M ⊗ N) →
  τ_{≥2} C(G_v, M ⊗ N)` is zero. ("We must check that for every `m ∈ M^{t=1}` and
  `n ∈ N^{t=1}` the 2-cochain `z = μ₁(m, 0) ∪ μ₁(n, 0)` is a coboundary.")
* Proposition 7.5.5 (p. 169): if `M` is of finite or cofinite type over `R`, all three vertical
  maps of (7.5.4.1) (built from the truncated cup product with `D(M)(1)`, `D = Hom_R(−, I)`, and
  `r_v`) are quasi-isomorphisms.
* 7.5.6 (p. 170): "Proposition 7.5.5 is nothing else than an 'explicit' form of Tate's local
  duality in the tame case `v ∤ p`. It can be reformulated as follows: for every `M` of finite or
  cofinite type over `R`, the local conditions `Δ^ur(M)` … and the corresponding local conditions
  for `D(M)(1)` are exact orthogonal complements: `Δ^ur(M) ⊥⊥_{ev₂,0} Δ^ur(D(M)(1))`."

**This file.**
* Lemma 7.5.2 is **PROVED** here for lane RC28's unramified conditions, by an explicit primitive
  (no print needed): `orthUr_cup_coboundary` (generic: a decomposition group `G`, its unramified
  quotient `H ≃ ℤ̂`, unramified finite modules) — the cup product of two inflated unramified
  `1`-cocycles is the coboundary of `g ↦ −∑_{0≤j<l<χ(g)} B(Φ^j u, Φ^l y)`;
  `orthUr_cup_mem_range` (at `w ∈ S − S₀` for `urAt`); hence **the zero homotopy is a `τ≥2`
  isotropy homotopy** for (unramified, unramified): `orthUrIsotropy` (Nekovář's `h_v = 0`).
* `orthLocalMap_indep`: the per-place local duality map of conditions concentrated in degrees
  `0, 1` (such as (unramified, unramified)) does not depend on the isotropy homotopy;
  `orthUr_quasiIso_of_print`: the print then holds for every `τ≥2` isotropy homotopy.
* `NekovarProp756` (**PRINT**, Nekovář 7.5.6 with 7.5.5, pp. 169–170; read): the per-place local
  duality map of (unramified, unramified) with `h = 0` is a quasi-isomorphism, for perfect
  coefficient pairings into `R(1)` and local traces inducing `H² ≅ R`.

DEPARTUREs (form). (1) Nekovář's `Δ^ur(M)` maps `C⁺(M^{I_v}) = [M^{I_v} --(f−1)--> M^{I_v}]`
through his explicit tame complex `C(M)` and the resolution maps `μ` (7.2–7.4) into
`C(G_v, M)`; lane RC28's `urAt` maps `[M₀ --(Φ−1)--> M₀]` by inflation of the `ℤ̂`-cocycles
`c_x(Frob^n) = Σ_{j<n} Φ^j x`. In degree zero both are the constant cochains and in degree one both
send `m` to `g ↦ Σ_{j<a} f^j m` on `g ↦ f^a`, as read in the proof of 7.5.2; Nekovář's `f` is a
Frobenius lift whose action on `μ_{p^n}` is through `q^{−1}` (7.5.3), RC26's `Frob` is the
arithmetic Frobenius. Replacing a topological generator by its inverse changes
`[M --(F−1)--> M] → C(G_v, M)` by the automorphism `(id, −F)` of the source (the image subcomplex
is the same), so orthogonality is unaffected; this identification is GLUE (not formalized). (2) The
coefficients are a perfect pairing `β : M₀ × M₀' → T₀` with `T₀ ≅ R(1)` instead of
`D(M)(1) = Hom_R(M, I)(1)` with `ev₂`, and `R` is self-injective (`I = R`), as in lane RC26's
`NekovarProp524`/`NekovarProp543`; the trace is any local trace inducing `H²(G_{K_w}, T) ≅ R`
(Nekovář's `r_v` up to a unit and homotopy, which does not change quasi-isomorphy).

Kinds: definitions and PROVED, except `NekovarProp756` (PRINT, read).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open CategoryTheory NumberField IsDedekindDomain
open ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.SwitchInputs ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.UnramifiedComplex
open ZInQ.Contrib.CloudB3RC53.Duality (LocalTruncIsotropy)

attribute [local instance] TopRep.distribMulAction

/-! ### The triangle sums -/

section Tri

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (X X' : TopRep.{0} k H)
  {T : Type} [AddCommGroup T] [Module k T] (B : X.V →ₗ[k] X'.V →ₗ[k] T)

/-- **The triangle sum** `Δ_{u,y}(n) = Σ_{0 ≤ j < l < n} B(Φ^j u, Φ^l y)` (`Φ` the Frobenius);
`−Δ` is the primitive of the cup product of two unramified cocycles. -/
def orthTri (u : X.V) (y : X'.V) (n : ℕ) : T :=
  ∑ l ∈ Finset.range n, ∑ j ∈ Finset.range l, B (frobElt e ^ j • u) (frobElt e ^ l • y)

/-- **The cocycle identity of the triangle sums**:
`Δ_{u,y}(a + b) = Δ_{u,y}(a) + B(S_u(a), Φ^a S_y(b)) + Δ_{Φ^a u, Φ^a y}(b)`, with
`S_u(a) = Σ_{j<a} Φ^j u` (`psum`). PROVED. -/
theorem orthTri_add (u : X.V) (y : X'.V) (a b : ℕ) :
    orthTri e X X' B u y (a + b) = orthTri e X X' B u y a +
      B (psum e X u a) (frobElt e ^ a • psum e X' y b) +
      orthTri e X X' B (frobElt e ^ a • u) (frobElt e ^ a • y) b := by
  unfold orthTri psum
  rw [Finset.sum_range_add, add_assoc]
  congr 1
  have h1 : ∀ l, ∑ j ∈ Finset.range (a + l), B (frobElt e ^ j • u) (frobElt e ^ (a + l) • y) =
      ∑ j ∈ Finset.range a, B (frobElt e ^ j • u) (frobElt e ^ (a + l) • y) +
      ∑ j ∈ Finset.range l, B (frobElt e ^ j • frobElt e ^ a • u)
        (frobElt e ^ l • frobElt e ^ a • y) := by
    intro l
    rw [Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_smul, ← mul_smul, ← pow_add, ← pow_add, add_comm j a, add_comm l a]
  simp only [h1, Finset.sum_add_distrib]
  congr 1
  rw [map_sum, LinearMap.sum_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_smul, ← pow_add]

/-- The triangle sums are killed by `|X|`. PROVED. -/
theorem orthTri_card_nsmul [Finite X.V] (u : X.V) (y : X'.V) (n : ℕ) :
    Nat.card X.V • orthTri e X X' B u y n = 0 := by
  unfold orthTri
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← LinearMap.smul_apply, ← map_nsmul, card_nsmul_eq_zero', map_zero, LinearMap.zero_apply]

/-- Adding a good period `p` (Frobenius trivial on `X`, `X'`, `S_u(p) = 0`). PROVED. -/
theorem orthTri_period_add (u : X.V) (y : X'.V) (p : ℕ)
    (hX : ∀ x : X.V, frobElt e ^ p • x = x) (hX' : ∀ x : X'.V, frobElt e ^ p • x = x)
    (hp : psum e X u p = 0) (N : ℕ) :
    orthTri e X X' B u y (p + N) = orthTri e X X' B u y p + orthTri e X X' B u y N := by
  rw [orthTri_add, hp, map_zero, LinearMap.zero_apply, add_zero, hX u, hX' y]

end Tri

/-! ### Periods -/

section Periods

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (X X' : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  [ContinuousSMul H X'.V] [DiscreteTopology X'.V] [Finite X'.V]

/-- The period `P_X` of the cocycles `urCocycle e X` (lane RC26's choice). -/
abbrev orthPerX : ℕ := period X (urPeriod e X)

/-- The common modulus `P = P_X · P_{X'} · |X|` used for the primitive. -/
abbrev orthMod : ℕ := orthPerX e X * orthPerX e X' * Nat.card X.V

instance orthMod_neZero : NeZero (orthMod e X X') :=
  ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)) Nat.card_pos.ne'⟩

/-- `Φ^{P_X t}` acts trivially on `X`. -/
theorem orth_pow_perX_mul_smul (t : ℕ) (x : X.V) : frobElt e ^ (orthPerX e X * t) • x = x :=
  pow_period_smul e X (urPeriod_spec e X) t x

/-- `S_u(P_X t) = 0`. -/
theorem orth_psum_perX_mul (u : X.V) (t : ℕ) : psum e X u (orthPerX e X * t) = 0 := by
  have hP : ∀ x : X.V, frobElt e ^ orthPerX e X • x = x := fun x => by
    simpa using orth_pow_perX_mul_smul e X 1 x
  rw [psum_mul e X u hP, psum_period e X u (urPeriod_spec e X), smul_zero]

/-- `Φ^m x = Φ^{m mod P_X} x`. -/
theorem orth_pow_mod_smul (m : ℕ) (x : X.V) :
    frobElt e ^ (m % orthPerX e X) • x = frobElt e ^ m • x := by
  conv_rhs => rw [← Nat.mod_add_div m (orthPerX e X), pow_add, mul_smul,
    orth_pow_perX_mul_smul e X]

/-- **Compatibility of the characters `χ_P : H → ℤ/P`** (`Frob ↦ 1`) for `P ∣ Q`:
`χ_Q(h) mod P = χ_P(h)`. PROVED (density of the powers of the Frobenius). -/
theorem orth_chi_val_mod (P Q : ℕ) [NeZero P] [NeZero Q] (hPQ : P ∣ Q) (h : H) :
    (chi e Q h).toAdd.val % P = (chi e P h).toAdd.val := by
  have key : (fun h : H => (((chi e Q h).toAdd.val : ℕ) : ZMod P)) =
      fun h : H => (chi e P h).toAdd := by
    refine eq_of_eq_zpow e ?_ ?_ fun n => ?_
    · exact (continuous_of_discreteTopology (f := fun a : Multiplicative (ZMod Q) =>
        ((a.toAdd.val : ℕ) : ZMod P))).comp (map_continuous (chi e Q))
    · exact (continuous_of_discreteTopology (f := fun a : Multiplicative (ZMod P) =>
        a.toAdd)).comp (map_continuous (chi e P))
    · simp only [chi_zpow, toAdd_ofAdd]
      rw [← ZMod.cast_eq_val, ZMod.cast_intCast hPQ]
  have h2 := congrArg (fun φ : H → ZMod P => (φ h).val) key
  simp only [ZMod.val_natCast] at h2
  exact h2

variable {X} in
/-- **The cocycle at a multiple modulus**: `c_u(h) = S_u(χ_Q(h))` for `P_X ∣ Q`. PROVED. -/
theorem orth_urCocycle_eq (Q : ℕ) [NeZero Q] (hQ : orthPerX e X ∣ Q) (u : X.V) (h : H) :
    urCocycle e X u h = psum e X u (chi e Q h).toAdd.val := by
  change psum e X u (chi e (orthPerX e X) h).toAdd.val = _
  rw [← orth_chi_val_mod e (orthPerX e X) Q hQ h, psum_mod e X u (urPeriod_spec e X)]

variable {X} in
/-- **The action at a multiple modulus**: `h • x = Φ^{χ_Q(h)} x` for `P_X ∣ Q`. PROVED. -/
theorem orth_smul_eq (Q : ℕ) [NeZero Q] (hQ : orthPerX e X ∣ Q) (h : H) (x : X.V) :
    h • x = frobElt e ^ (chi e Q h).toAdd.val • x := by
  rw [smul_eq_chi e X (urPeriod_spec e X) h x, ← orth_chi_val_mod e (orthPerX e X) Q hQ h,
    orth_pow_mod_smul e X]

theorem orthPerX_dvd_mod : orthPerX e X ∣ orthMod e X X' :=
  Dvd.intro (orthPerX e X' * Nat.card X.V) (by ring)

theorem orthPerX'_dvd_mod : orthPerX e X' ∣ orthMod e X X' :=
  Dvd.intro (orthPerX e X * Nat.card X.V) (by ring)

end Periods

/-! ### The primitive of the cup product of unramified cocycles (Nekovář 7.5.2) -/

section Primitive

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (X X' : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  [ContinuousSMul H X'.V] [DiscreteTopology X'.V] [Finite X'.V]
  {T : Type} [AddCommGroup T] [Module k T] (B : X.V →ₗ[k] X'.V →ₗ[k] T)

/-- **Periodicity of the triangle sums**: `Δ(N mod P) = Δ(N)` for the common modulus `P`.
PROVED. -/
theorem orthTri_mod (u : X.V) (y : X'.V) (N : ℕ) :
    orthTri e X X' B u y (N % orthMod e X X') = orthTri e X X' B u y N := by
  set P₀ := orthPerX e X * orthPerX e X'
  have hP₀X : ∀ t (x : X.V), frobElt e ^ (P₀ * t) • x = x := fun t x => by
    rw [show P₀ * t = orthPerX e X * (orthPerX e X' * t) by ring]
    exact orth_pow_perX_mul_smul e X _ x
  have hP₀X' : ∀ t (x : X'.V), frobElt e ^ (P₀ * t) • x = x := fun t x => by
    rw [show P₀ * t = orthPerX e X' * (orthPerX e X * t) by ring]
    exact orth_pow_perX_mul_smul e X' _ x
  have hP₀u : ∀ t, psum e X u (P₀ * t) = 0 := fun t => by
    rw [show P₀ * t = orthPerX e X * (orthPerX e X' * t) by ring]
    exact orth_psum_perX_mul e X u _
  have hmul : ∀ t, orthTri e X X' B u y (P₀ * t) = t • orthTri e X X' B u y P₀ := by
    intro t
    induction t with
    | zero => simp [orthTri]
    | succ t ih =>
      rw [show P₀ * (t + 1) = P₀ * 1 + P₀ * t by ring, mul_one,
        orthTri_period_add e X X' B u y P₀ (by simpa using hP₀X 1) (by simpa using hP₀X' 1)
          (by simpa using hP₀u 1), ih, succ_nsmul, add_comm]
  have hP : orthTri e X X' B u y (orthMod e X X') = 0 := by
    change orthTri e X X' B u y (P₀ * Nat.card X.V) = 0
    rw [hmul, orthTri_card_nsmul]
  have hadd : ∀ M, orthTri e X X' B u y (orthMod e X X' + M) = orthTri e X X' B u y M := by
    intro M
    rw [orthTri_period_add e X X' B u y (orthMod e X X') (hP₀X _) (hP₀X' _) (hP₀u _), hP,
      zero_add]
  conv_rhs => rw [← Nat.mod_add_div N (orthMod e X X')]
  generalize N / orthMod e X X' = q
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show N % orthMod e X X' + orthMod e X X' * (q + 1) =
      orthMod e X X' + (N % orthMod e X X' + orthMod e X X' * q) by ring, hadd]
    exact ih

end Primitive

/-! ### Lemma 7.5.2 at cochain level: the primitive -/

section Cochain

variable {k : Type} [CommRing k] [TopologicalSpace k]
  {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (e : H ≃ₜ* TauCeti.zHat.{0}) (π : G →ₜ* H) (X X' : TopRep.{0} k H)
  [ContinuousSMul H X.V] [DiscreteTopology X.V] [Finite X.V]
  [ContinuousSMul H X'.V] [DiscreteTopology X'.V] [Finite X'.V]
  {M M' T : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  [AddCommGroup M'] [Module k M'] [DistribMulAction G M'] [SMulCommClass G k M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul G M']
  [AddCommGroup T] [Module k T] [DistribMulAction G T] [SMulCommClass G k T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul G T]
  (f : X.V →ₗ[k] M) (f' : X'.V →ₗ[k] M') (β : M →ₗ[k] M' →ₗ[k] T)

/-- **The primitive** `g ↦ −Δ_{u,y}(χ_P(π g))` (`Δ` the triangle sum of `B = β ∘ (f × f')`,
`χ_P : H → ℤ/P` the character with `Frob ↦ 1`, `P` the common modulus): a continuous
`1`-cochain on `G` with values in `T`. -/
def orthUrPrim (u : X.V) (y : X'.V) : contCochain k G T 1 :=
  ⟨(fun g => -orthTri e X X' (β.compl₁₂ f f') u y (chi e (orthMod e X X') (π (g 0))).toAdd.val :
      (Fin 1 → G) → T),
    (continuous_of_discreteTopology (f := fun a : Multiplicative (ZMod (orthMod e X X')) =>
      -orthTri e X X' (β.compl₁₂ f f') u y a.toAdd.val)).comp
      ((map_continuous (chi e (orthMod e X X'))).comp ((map_continuous π).comp
        (continuous_apply 0)))⟩

variable {f f' β}
variable (hf : ∀ (g : G) (x : X.V), f (π g • x) = g • f x)
  (hf' : ∀ (g : G) (x : X'.V), f' (π g • x) = g • f' x)
  (hβ : ∀ (g : G) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

include hf hf' hβ in
/-- **`G` acts on the triangle sums through the Frobenius power `χ_P(π g)`**:
`g • Δ_{u,y}(n) = Δ_{Φ^m u, Φ^m y}(n)`, `m = χ_P(π g)`. PROVED. -/
theorem orthTri_smul (g : G) (u : X.V) (y : X'.V) (n : ℕ) :
    g • orthTri e X X' (β.compl₁₂ f f') u y n =
      orthTri e X X' (β.compl₁₂ f f')
        (frobElt e ^ (chi e (orthMod e X X') (π g)).toAdd.val • u)
        (frobElt e ^ (chi e (orthMod e X X') (π g)).toAdd.val • y) n := by
  unfold orthTri
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change g • β (f (frobElt e ^ j • u)) (f' (frobElt e ^ l • y)) =
    β (f (frobElt e ^ j • frobElt e ^ (chi e (orthMod e X X') (π g)).toAdd.val • u))
      (f' (frobElt e ^ l • frobElt e ^ (chi e (orthMod e X X') (π g)).toAdd.val • y))
  rw [← hβ, ← hf, ← hf', orth_smul_eq e (orthMod e X X') (orthPerX_dvd_mod e X X'),
    orth_smul_eq e (orthMod e X X') (orthPerX'_dvd_mod e X X'), ← mul_smul, ← mul_smul,
    ← mul_smul, ← mul_smul, ← pow_add, ← pow_add, ← pow_add, ← pow_add, add_comm j,
    add_comm l]

include hf hf' hβ in
/-- **Lemma 7.5.2 of Nekovář, at cochain level, for inflated unramified cocycles** (PROVED; the
statement Nekovář proves on p. 168 via `λ₂`, here by an explicit primitive): for unramified finite
modules `X`, `X'` of `H ≃ ℤ̂` mapped equivariantly into discrete `G`-modules `M`, `M'` (`π : G → H`)
and an equivariant pairing `β : M × M' → T`, the cup product of the inflated cocycles
`g ↦ f(c_u(π g))` and `g ↦ f'(c_y(π g))` is the coboundary of the primitive `orthUrPrim`:
`d(−Δ_{u,y} ∘ χ_P ∘ π) = (f ∘ c_u ∘ π) ∪ (f' ∘ c_y ∘ π)`. -/
theorem orthUr_cup_coboundary (u : X.V) (y : X'.V) :
    ((contCochains k G T).d 1 2).hom ((contSubCx k G T).ofSub (orthUrPrim e π X X' f f' β u y)) =
      contCup β (continuous_pairing β) 1 1 2 rfl (urLin₁ e π X f u) (urLin₁ e π X' f' y) := by
  apply Subtype.ext
  funext g
  have h1 := contCochains_d_apply (k := k) (G := G) (M := T) 1
    ((contSubCx k G T).ofSub (orthUrPrim e π X X' f f' β u y)) g
  refine h1.trans ?_
  rw [Fin.sum_univ_two]
  have hhead : headProd 1 2 (by omega) g = g 0 := by
    change headProd (0 + 1) 2 (by omega) g = g 0
    rw [headProd_succ, headProd_zero, one_mul]
    rfl
  change g 0 • (-orthTri e X X' (β.compl₁₂ f f') u y
        (chi e (orthMod e X X') (π (g 1))).toAdd.val) +
      ((-1 : k) ^ ((0 : ℕ) + 1) • (-orthTri e X X' (β.compl₁₂ f f') u y
        (chi e (orthMod e X X') (π (g 0 * g 1))).toAdd.val) +
      (-1 : k) ^ ((1 : ℕ) + 1) • (-orthTri e X X' (β.compl₁₂ f f') u y
        (chi e (orthMod e X X') (π (g 0))).toAdd.val)) =
    β (f (urCocycle e X u (π (g 0))))
      (headProd 1 2 (by omega) g • f' (urCocycle e X' y (π (g 1))))
  rw [hhead, ← hf', orth_urCocycle_eq e (orthMod e X X') (orthPerX_dvd_mod e X X'),
    orth_urCocycle_eq e (orthMod e X X') (orthPerX'_dvd_mod e X X'),
    orth_smul_eq e (orthMod e X X') (orthPerX'_dvd_mod e X X'), smul_neg,
    orthTri_smul e π X X' hf hf' hβ, map_mul, map_mul, toAdd_mul, ZMod.val_add,
    orthTri_mod, orthTri_add]
  simp only [zero_add, pow_one, neg_one_smul, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_smul, neg_neg]
  change _ = (β.compl₁₂ f f') _ _
  abel

end Cochain

/-! ### Zero homotopies for conditions concentrated in degrees `0, 1` -/

section ZeroIsotropy

variable {k : Type} [CommRing k] {U U' L L' E : GCx k} {iU : GHom U L} {iU' : GHom U' L'}
  {P : GPair L L' E}

/-- **The zero homotopy is a `τ≥2` isotropy homotopy** for local conditions concentrated in
degrees `0, 1` whose `(1, 1)` products `iU u ∪ iU' v` are coboundaries in `E²` (Nekovář 6.2.1.5:
`prod_v = 0` after `τ≥2`, so `Δ_v(X₁) ⊥_{π,0} Δ_v(X₂)`). -/
def orthZeroIsotropy (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
    (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i))
    (h11 : ∀ (u : U.X 1) (v : U'.X 1),
      P.P 1 1 2 rfl (iU.f 1 1 rfl u) (iU'.f 1 1 rfl v) ∈ LinearMap.range (E.d 1 2 rfl)) :
    LocalTruncIsotropy iU iU' P :=
  ZInQ.Contrib.CloudB3RC53.Duality.ofTruncZero fun i j l h u v => by
    change (truncSub E l).mkQ (P.P i j l h (iU.f i i rfl u) (iU'.f j j rfl v)) = 0
    by_cases hi : i = 0 ∨ i = 1
    · by_cases hj : j = 0 ∨ j = 1
      · by_cases hl : l ≤ 1
        · rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_le E hl]
          trivial
        · obtain rfl : i = 1 := by omega
          obtain rfl : j = 1 := by omega
          obtain rfl : l = 2 := by omega
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, truncSub_of_eq E rfl]
          exact h11 u v
      · have : Subsingleton (U'.X j) := hU' j (by omega) (by omega)
        rw [Subsingleton.elim v 0]
        simp
    · have : Subsingleton (U.X i) := hU i (by omega) (by omega)
      rw [Subsingleton.elim u 0]
      simp

/-- **For conditions concentrated in degrees `0, 1` the per-place local duality map does not
depend on the isotropy homotopy** (the homotopy only enters through `h(u, y)` with
`deg u + deg y = 3`). PROVED. -/
theorem orthLocalMap_indep (J J' : LocalTruncIsotropy iU iU' P) (trv : E.X 2 →ₗ[k] k)
    (htrv : ∀ z, trv (E.d 1 2 rfl z) = 0)
    (hU : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U.X i))
    (hU' : ∀ i : ℤ, i ≠ 0 → i ≠ 1 → Subsingleton (U'.X i)) :
    GHom.toCC (orthLocalMap iU iU' P J trv htrv) = GHom.toCC (orthLocalMap iU iU' P J' trv htrv) := by
  refine GHom.toCC_ext fun i c => dualCx_ext fun y => ?_
  obtain ⟨u, x⟩ := c
  rw [orthLocalMap_apply, orthLocalMap_apply]
  congr 2
  by_cases hi : i = 0 ∨ i = 1
  · have : Subsingleton (U'.X (3 - i)) := hU' (3 - i) (by omega) (by omega)
    rw [Subsingleton.elim y 0]
    simp
  · have : Subsingleton (U.X i) := hU i (by omega) (by omega)
    rw [Subsingleton.elim u 0]
    simp

end ZeroIsotropy

/-! ### Lemma 7.5.2 for lane RC26's unramified local conditions -/

section UrGeneric

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {k : Type} [CommRing k] [TopologicalSpace k]
  {M M' T : Type}
  [AddCommGroup M] [Module k M] [DistribMulAction (GKS K S) M] [SMulCommClass (GKS K S) k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul (GKS K S) M]
  [AddCommGroup M'] [Module k M'] [DistribMulAction (GKS K S) M'] [SMulCommClass (GKS K S) k M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul (GKS K S) M']
  [AddCommGroup T] [Module k T] [DistribMulAction (GKS K S) T] [SMulCommClass (GKS K S) k T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul (GKS K S) T]
  (β : M →ₗ[k] M' →ₗ[k] T) (hβ : ∀ (g : GKS K S) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- **Lemma 7.5.2 for lane RC26's unramified conditions** (`urToLocal_galois`, PROVED): at a place
`w ∈ S`, for finite unramified modules `X`, `X'` of `Gal(K_w^ur/K_w)` mapped equivariantly into
discrete `G_{K,S}`-modules and an equivariant pairing `β`, the cup product of two degree-one
elements of the unramified conditions is a coboundary in `C²_cont(G_{K_w}, T)`. -/
theorem orthUr_cup_mem_range_gen (w : Places K S)
    (X X' : TopRep.{0} k (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K w.1))
    [ContinuousSMul (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K w.1) X.V] [DiscreteTopology X.V]
    [Finite X.V]
    [ContinuousSMul (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K w.1) X'.V] [DiscreteTopology X'.V]
    [Finite X'.V]
    (f : X.V →ₗ[k] M)
    (hf : ∀ (g : Gloc K w.1) (x : X.V), f (resUr K w.1 g • x) = locMap K S w.1 g • f x)
    (f' : X'.V →ₗ[k] M')
    (hf' : ∀ (g : Gloc K w.1) (x : X'.V), f' (resUr K w.1 g • x) = locMap K S w.1 g • f' x)
    (u : (urCx K w.1 X).X 1) (y : (urCx K w.1 X').X 1) :
    (localPair k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1) β hβ
      (continuous_pairing β) w).P 1 1 2 rfl (((urToLocal_galois K S w X f hf).f 1).hom u)
      (((urToLocal_galois K S w X' f' hf').f 1).hom y) ∈
      LinearMap.range ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) T w).d 1 2 rfl) := by
  -- the instance arguments for the restricted modules are passed explicitly (as in lane RC26)
  have h1 : (urToLocal_galois K S w X f hf).f 1 = _ :=
    @urToLocal_f₁ k _ _ (Gloc K w.1) _ _ _ (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K w.1) _ _ _
      (eUr K w.1) (resUr K w.1) X _ _ _ (ResMod (locMap K S w.1) M) inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance f hf
  have h2 : (urToLocal_galois K S w X' f' hf').f 1 = _ :=
    @urToLocal_f₁ k _ _ (Gloc K w.1) _ _ _ (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K w.1) _ _ _
      (eUr K w.1) (resUr K w.1) X' _ _ _ (ResMod (locMap K S w.1) M') inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance f' hf'
  rw [h1, h2]
  exact ⟨_, @orthUr_cup_coboundary k _ _ (Gloc K w.1) _ _ _
    (ZInQ.Contrib.CloudB3RC53.RankCounts.GUr K w.1) _ _ _ (eUr K w.1) (resUr K w.1) X X'
    _ _ _ _ _ _ (ResMod (locMap K S w.1) M) (ResMod (locMap K S w.1) M')
    (ResMod (locMap K S w.1) T)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    f f' (resPairing k (GKS K S) β (locMap K S w.1)) hf hf'
    (fun g a b => hβ (locMap K S w.1 g) a b)
    (((HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (frob (eUr K w.1) X - 1)) rel01
      (by decide)).hom).hom u)
    (((HomologicalComplex.doubleXIso₁ (ModuleCat.ofHom (frob (eUr K w.1) X' - 1)) rel01
      (by decide)).hom).hom y)⟩

end UrGeneric

/-! ### The unramified conditions of lane RC28 -/

section UrGalois

open ZInQ.Manuscript.RC.CoefModules

variable {K : Type} [Field K] [NumberField K] {S S₀ : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S)
  (k : Type) [CommRing k] [TopologicalSpace k] [DiscreteTopology k]
  {M₀ M₀' T₀ : Type}
  [AddCommGroup M₀] [Module k M₀] [DistribMulAction (GKS K S₀) M₀] [SMulCommClass (GKS K S₀) k M₀]
  [TopologicalSpace M₀] [DiscreteTopology M₀] [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
  [AddCommGroup M₀'] [Module k M₀'] [DistribMulAction (GKS K S₀) M₀']
  [SMulCommClass (GKS K S₀) k M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
  [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀']
  [AddCommGroup T₀] [Module k T₀] [DistribMulAction (GKS K S₀) T₀] [SMulCommClass (GKS K S₀) k T₀]
  [TopologicalSpace T₀] [DiscreteTopology T₀] [ContinuousSMul (GKS K S₀) T₀]
  (β₀ : M₀ →ₗ[k] M₀' →ₗ[k] T₀)
  (hβ₀ : ∀ (g : GKS K S₀) (a : M₀) (b : M₀'), β₀ (g • a) (g • b) = g • β₀ a b)

/-- The coefficient pairing `M₀ × M₀' → T₀` of `G_{K,S₀}`-modules, on the modules inflated to
`G_{K,S}` (the same map). -/
abbrev orthInflPair : InflMod hS M₀ →ₗ[k] InflMod hS M₀' →ₗ[k] InflMod hS T₀ := β₀

include hβ₀ in
theorem orthInflPair_smul (g : GKS K S) (a : InflMod hS M₀) (b : InflMod hS M₀') :
    orthInflPair hS k β₀ (g • a) (g • b) = g • orthInflPair hS k β₀ a b :=
  hβ₀ (inflMap K hS g) a b

/-- The local cup product at `w` for the inflated coefficient pairing. -/
abbrev orthUrPair (w : Places K S) :=
  localPair k (GKS K S) (fun v : Places K S => Gloc K v.1) (fun v => locMap K S v.1)
    (orthInflPair hS k β₀) (orthInflPair_smul hS k β₀ hβ₀) (continuous_pairing _) w

/-- The unramified condition `[M₀ --(Φ−1)--> M₀]` vanishes outside degrees `0, 1`. -/
theorem orth_urAt_vanishes (M₁ : Type) [AddCommGroup M₁] [Module k M₁]
    [DistribMulAction (GKS K S₀) M₁] [SMulCommClass (GKS K S₀) k M₁] [TopologicalSpace M₁]
    [DiscreteTopology M₁] [ContinuousSMul (GKS K S₀) M₁] [Finite M₁]
    (w : Places K S) (hw : w.1 ∉ S₀) (i : ℤ) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    Subsingleton ((urAt hS k M₁ w hw).U.X i) :=
  ModuleCat.subsingleton_of_isZero (HomologicalComplex.isZero_double_X
    (ModuleCat.ofHom (frob (eUr K w.1) (urRep k M₁ (newPlace w hw)) - 1)) rel01 i h0 h1)

include hβ₀ in
/-- **Lemma 7.5.2 for lane RC28's unramified conditions** (PROVED): at `w ∈ S − S₀`, the cup
product of two degree-one elements of the unramified conditions on `M₀` and `M₀'` is a coboundary
in `C²_cont(G_{K_w}, T₀)`. -/
theorem orthUr_cup_mem_range (w : Places K S) (hw : w.1 ∉ S₀)
    (u : (urAt hS k M₀ w hw).U.X 1) (y : (urAt hS k M₀' w hw).U.X 1) :
    (orthUrPair hS k β₀ hβ₀ w).P 1 1 2 rfl ((urAt hS k M₀ w hw).i.f 1 1 rfl u)
      ((urAt hS k M₀' w hw).i.f 1 1 rfl y) ∈
      LinearMap.range ((localCx k (GKS K S) (fun v : Places K S => Gloc K v.1)
        (fun v => locMap K S v.1) (InflMod hS T₀) w).d 1 2 rfl) := by
  haveI := urRep_continuousSMul k M₀ (newPlace w hw)
  haveI := urRep_continuousSMul k M₀' (newPlace w hw)
  exact orthUr_cup_mem_range_gen (orthInflPair hS k β₀) (orthInflPair_smul hS k β₀ hβ₀) w
    (urRep k M₀ (newPlace w hw)) (urRep k M₀' (newPlace w hw)) (urId hS k M₀ (newPlace w hw))
    (urId_compat hS k M₀ w hw) (urId hS k M₀' (newPlace w hw)) (urId_compat hS k M₀' w hw) u y

/-- **The isotropy homotopies of (unramified, unramified)** at `w ∈ S − S₀`: the zero homotopy
(Nekovář's `h_v = 0` in 7.5.6), a `τ≥2` isotropy homotopy by `orthUr_cup_mem_range`. -/
def orthUrIsotropy (w : Places K S) (hw : w.1 ∉ S₀) :
    LocalTruncIsotropy (urAt hS k M₀ w hw).i (urAt hS k M₀' w hw).i (orthUrPair hS k β₀ hβ₀ w) :=
  orthZeroIsotropy (orth_urAt_vanishes hS k M₀ w hw) (orth_urAt_vanishes hS k M₀' w hw)
    (orthUr_cup_mem_range hS k β₀ hβ₀ w hw)

/-- The isotropy homotopy of (unramified, unramified) is zero. -/
theorem orthUrIsotropy_h (w : Places K S) (hw : w.1 ∉ S₀) :
    (orthUrIsotropy hS k β₀ hβ₀ w hw).h = fun _ _ _ _ => 0 :=
  rfl

end UrGalois

/-! ### The PRINT: unramified conditions are orthogonal complements (Nekovář 7.5.6) -/

section Print

open ZInQ.Manuscript.RC.CoefModules

/-- **PRINT — Nekovář, *Selmer complexes*, Astérisque 310 (2006), 7.5.6 (p. 170), the
reformulation of Proposition 7.5.5 (p. 169), with Lemma 7.5.2 (p. 168)** (read; cited at tex
3483–3498, 3815–3818 for "the integral unramified comparison"): for the tame case `v ∤ p` and
coefficients of finite type over `R`, the unramified local conditions of `M` and of `D(M)(1)` are
exact orthogonal complements with respect to `ev₂` and the zero homotopy,
`Δ^ur(M) ⊥⊥_{ev₂,0} Δ^ur(D(M)(1))` — i.e. the local map `u⁻_{ev₂,0}` of 6.2.2 is a
quasi-isomorphism. Stated for lane RC28's unramified conditions `urAt` at a place `w ∈ S − S₀`
(where `M₀`, `M₀'` are unramified; `w ∤ p` since the primes above `p` lie in `S₀` by the standing
hypotheses for `S₀`), for finite discrete `R[G_{K,S₀}]`-modules `M₀`, `M₀'` with a perfect
equivariant pairing `β₀ : M₀ × M₀' → T₀`, `T₀ ≅ R(1)`, the zero isotropy homotopy
(`orthUrIsotropy`, which is a `τ≥2` isotropy homotopy by the PROVED Lemma 7.5.2,
`orthUr_cup_mem_range`) and any local trace `tr_w` on `C²_cont(G_{K_w}, T₀)` killing coboundaries
and inducing `H²(G_{K_w}, T₀) ≅ R`. DEPARTUREs (form, see the module docstring): the inflation
model of `Δ^ur`, a perfect `β₀` into `R(1)` instead of `ev₂`, and any trace inducing `H² ≅ R`
instead of `r_v`. -/
def NekovarProp756 (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ (S₀ S : Set (HeightOneSpectrum (𝓞 K))) (hS : S₀ ⊆ S) (p : ℕ) (R : Type) [CommRing R]
    [IsLocalRing R] [TopologicalSpace R] [DiscreteTopology R],
    NekovarFiniteSetting K S₀ p R →
    ∀ (M₀ M₀' T₀ : Type)
      [AddCommGroup M₀] [Module R M₀] [DistribMulAction (GKS K S₀) M₀]
      [SMulCommClass (GKS K S₀) R M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
      [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
      [AddCommGroup M₀'] [Module R M₀'] [DistribMulAction (GKS K S₀) M₀']
      [SMulCommClass (GKS K S₀) R M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
      [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀']
      [AddCommGroup T₀] [Module R T₀] [DistribMulAction (GKS K S₀) T₀]
      [SMulCommClass (GKS K S₀) R T₀] [TopologicalSpace T₀] [DiscreteTopology T₀]
      [ContinuousSMul (GKS K S₀) T₀]
      (β₀ : M₀ →ₗ[R] M₀' →ₗ[R] T₀)
      (hβ₀ : ∀ (g : GKS K S₀) (a : M₀) (b : M₀'), β₀ (g • a) (g • b) = g • β₀ a b),
      Function.Bijective β₀ → Function.Bijective β₀.flip → IsCyclotomicTwist K S₀ R T₀ →
      ∀ (w : Places K S) (hw : w.1 ∉ S₀)
        (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS T₀) w).X 2 →ₗ[R] R)
        (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
          (fun v => locMap K S v.1) (InflMod hS T₀) w).d 1 2 rfl z) = 0),
        InducesIsoH2 trv →
        QuasiIso (GHom.toCC (orthLocalMap (urAt hS R M₀ w hw).i (urAt hS R M₀' w hw).i
          (orthUrPair hS R β₀ hβ₀ w) (orthUrIsotropy hS R β₀ hβ₀ w hw) trv htrv))

/-- **The print for every isotropy homotopy**: since the per-place map of (unramified,
unramified) does not depend on the isotropy homotopy (`orthLocalMap_indep`), `NekovarProp756`
gives the quasi-isomorphy for any `τ≥2` isotropy homotopy `J`. PROVED (from the PRINT). -/
theorem orthUr_quasiIso_of_print {K : Type} [Field K] [NumberField K] (h : NekovarProp756 K)
    {S₀ S : Set (HeightOneSpectrum (𝓞 K))} (hS : S₀ ⊆ S) (p : ℕ) {R : Type} [CommRing R]
    [IsLocalRing R] [TopologicalSpace R] [DiscreteTopology R] (hset : NekovarFiniteSetting K S₀ p R)
    {M₀ M₀' T₀ : Type}
    [AddCommGroup M₀] [Module R M₀] [DistribMulAction (GKS K S₀) M₀]
    [SMulCommClass (GKS K S₀) R M₀] [TopologicalSpace M₀] [DiscreteTopology M₀]
    [ContinuousSMul (GKS K S₀) M₀] [Finite M₀]
    [AddCommGroup M₀'] [Module R M₀'] [DistribMulAction (GKS K S₀) M₀']
    [SMulCommClass (GKS K S₀) R M₀'] [TopologicalSpace M₀'] [DiscreteTopology M₀']
    [ContinuousSMul (GKS K S₀) M₀'] [Finite M₀']
    [AddCommGroup T₀] [Module R T₀] [DistribMulAction (GKS K S₀) T₀]
    [SMulCommClass (GKS K S₀) R T₀] [TopologicalSpace T₀] [DiscreteTopology T₀]
    [ContinuousSMul (GKS K S₀) T₀]
    (β₀ : M₀ →ₗ[R] M₀' →ₗ[R] T₀)
    (hβ₀ : ∀ (g : GKS K S₀) (a : M₀) (b : M₀'), β₀ (g • a) (g • b) = g • β₀ a b)
    (hb : Function.Bijective β₀) (hb' : Function.Bijective β₀.flip)
    (hT : IsCyclotomicTwist K S₀ R T₀) (w : Places K S) (hw : w.1 ∉ S₀)
    (J : LocalTruncIsotropy (urAt hS R M₀ w hw).i (urAt hS R M₀' w hw).i
      (orthUrPair hS R β₀ hβ₀ w))
    (trv : (localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS T₀) w).X 2 →ₗ[R] R)
    (htrv : ∀ z, trv ((localCx R (GKS K S) (fun v : Places K S => Gloc K v.1)
      (fun v => locMap K S v.1) (InflMod hS T₀) w).d 1 2 rfl z) = 0)
    (htrv2 : InducesIsoH2 trv) :
    QuasiIso (GHom.toCC (orthLocalMap (urAt hS R M₀ w hw).i (urAt hS R M₀' w hw).i
      (orthUrPair hS R β₀ hβ₀ w) J trv htrv)) := by
  rw [orthLocalMap_indep J (orthUrIsotropy hS R β₀ hβ₀ w hw) trv htrv
    (orth_urAt_vanishes hS R M₀ w hw) (orth_urAt_vanishes hS R M₀' w hw)]
  exact h S₀ S hS p R hset M₀ M₀' T₀ β₀ hβ₀ hb hb' hT w hw trv htrv htrv2

end Print

end ZInQ.Manuscript.RC.KummerMaps
