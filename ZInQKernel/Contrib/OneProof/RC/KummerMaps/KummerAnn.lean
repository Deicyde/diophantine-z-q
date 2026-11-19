import ZInQKernel.Contrib.OneProof.RC.KummerMaps.Iota
import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.CupOne

/-!
# Lane RC29 (round 2, item 1): the exact annihilator after coefficient extension

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, tex 3423 ("Its Kummer image is
its exact local annihilator"), tex 3429–3432 ("At `v ∣ 2N`, … derived coefficient extension
defines the scalar `A_i` condition") and tex 3439–3445 (the local finite dualities make the Kummer
map adjoint to `H¹(F, B[2^a]) → H¹(F, B)[2^a]`, whose kernel is the Kummer image).

The text derives the exact annihilator for the Kummer condition with coefficients in the finite
ring `A_i` from the one for `B[2^a]` itself, the coefficient ring `A_i` being free over `ℤ/2^a`.
This file proves that step on genuine continuous cochains (lanes RC26, RC28), for an arbitrary
coefficient ring `A` and an arbitrary finite family `b` of elements of `A` along which the
coefficient modules decompose:

* `kannPost`: post-composition of a continuous cochain with an additive map of discrete modules;
  `kannPost_contD_one`, `kannPost_contD_zero`: it commutes with the differentials for an
  equivariant map.
* `kannCup_comm`: graded commutativity of the cup product of two `1`-cocycles up to an explicit
  coboundary, for an arbitrary pairing `β : M × M' → T` and its flip.
* **`kannCoef_ann`** (PROVED): let `ι' : B(F̄)[m] → M'` be equivariant, `π'_k : M' → B(F̄)[m]`
  equivariant with `x = ∑_k b_k • ι'(π'_k x)`, and `τ_k : T → T₀` equivariant with
  `τ_k (β (ι s) x) = ψ₀ (s, π'_k x)` for a pairing `ψ₀ : B(F̄)[m] × B(F̄)[m] → T₀`. If the Kummer
  image is its own annihilator for `ψ₀` (the hypothesis `hann`, in its trace-free form: the cup
  products with all Kummer cocycles are coboundaries), then every `1`-cocycle `y'` of
  `C^•_cont(G_F, M')` whose cup products with all extended Kummer cocycles `ι ∘ κ_P` are
  coboundaries lies in the extended Kummer condition `kummerZ' A ι' + B¹`.
* **`kannCoef_iso`** (PROVED): conversely the cup products of the degree-one terms of the two
  extended Kummer conditions are coboundaries, from the isotropy of the Kummer image for `ψ₀`.

Kinds: all declarations are definitions or PROVED. The hypotheses `hann`/`hiso` on `ψ₀` are the
inputs from Milne's local duality (another file of this lane derives them from the existing
print); the decomposition data `b, π', τ, j` are constructed for the actual modules in
`KummerAnnActual.lean`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules

/-! ### Post-composition with additive maps -/

section Post

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- PROVED. The underlying function of the differential of a continuous cochain is the
inhomogeneous differential `dFun` of its underlying function. -/
theorem kann_cfun_contD {k : Type} [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
    [DistribMulAction G M] [SMulCommClass G k M] [TopologicalSpace M] [ContinuousAdd M]
    [ContinuousConstSMul k M] [ContinuousSMul G M] (n : ℕ) (c : contCochain k G M n) :
    cfun (contD k G M n c) = dFun k n (cfun c) := by
  funext g
  exact contCochains_d_apply (k := k) (G := G) (M := M) n c g

variable {k k' : Type} [CommRing k] [CommRing k']
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  {N : Type} [AddCommGroup N] [Module k' N] [DistribMulAction G N] [SMulCommClass G k' N]
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- Definition. **Post-composition** of a continuous cochain `c : Gⁿ → M` with an additive map
`f : M → N` of discrete modules (continuous since `M` is discrete). -/
def kannPost (f : M →+ N) {n : ℕ} (c : contCochain k G M n) : contCochain k' G N n :=
  ⟨(fun g => f (cfun c g) : (Fin n → G) → N),
    (continuous_of_discreteTopology (f := f)).comp (mem_contCochain.1 c.2)⟩

/-- PROVED. The values of a post-composed cochain. -/
@[simp]
theorem cfun_kannPost (f : M →+ N) {n : ℕ} (c : contCochain k G M n) (g : Fin n → G) :
    cfun (kannPost (k' := k') f c) g = f (cfun c g) :=
  rfl

/-- PROVED. **Post-composition with an equivariant map commutes with `d¹`.** -/
theorem kannPost_contD_one (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (c : contCochain k G M 1) :
    kannPost (k' := k') f (contD k G M 1 c) = contD k' G N 1 (kannPost f c) := by
  apply Subtype.ext
  funext g
  change f (cfun (contD k G M 1 c) g) = cfun (contD k' G N 1 (kannPost f c)) g
  rw [kann_cfun_contD, kann_cfun_contD, dFun_one_apply, dFun_one_apply]
  simp only [map_add, map_sub, hf, cfun_kannPost]

/-- PROVED. **Post-composition with an equivariant map commutes with `d⁰`.** -/
theorem kannPost_contD_zero (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    (c : contCochain k G M 0) :
    kannPost (k' := k') f (contD k G M 0 c) = contD k' G N 0 (kannPost f c) := by
  apply Subtype.ext
  funext g
  change f (cfun (contD k G M 0 c) g) = cfun (contD k' G N 0 (kannPost f c)) g
  rw [contD_zero_apply, contD_zero_apply]
  simp only [map_sub, hf, cfun_kannPost]

/-- PROVED. Post-composition with an equivariant map sends `1`-cocycles to `1`-cocycles. -/
theorem kannPost_cocycle (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    {c : contCochain k G M 1} (hc : contD k G M 1 c = 0) :
    contD k' G N 1 (kannPost f c) = 0 := by
  rw [← kannPost_contD_one f hf, hc]
  apply Subtype.ext
  funext g
  exact map_zero f

/-- PROVED. Post-composition with an equivariant map sends `2`-coboundaries to `2`-coboundaries. -/
theorem kannPost_mem_range_two (f : M →+ N) (hf : ∀ (g : G) (x : M), f (g • x) = g • f x)
    {c : contCochain k G M 2} (hc : c ∈ LinearMap.range (contD k G M 1)) :
    kannPost (k' := k') f c ∈ LinearMap.range (contD k' G N 1) := by
  obtain ⟨e, rfl⟩ := hc
  exact ⟨kannPost f e, (kannPost_contD_one f hf e).symm⟩

/-- PROVED. Values of a finite linear combination of cochains. -/
theorem kann_cfun_sum_smul {ι₀ : Type} (s : Finset ι₀) (c : ι₀ → k) {n : ℕ}
    (y : ι₀ → contCochain k G M n) (g : Fin n → G) :
    cfun (∑ i ∈ s, c i • y i) g = ∑ i ∈ s, c i • cfun (y i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

end Post

/-! ### Graded commutativity in degree `(1, 1)` for a pairing and its flip -/

section Comm

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {k : Type} [CommRing k]
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction G M] [SMulCommClass G k M]
  [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul G M]
  {M' : Type} [AddCommGroup M'] [Module k M'] [DistribMulAction G M'] [SMulCommClass G k M']
  [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul G M']
  {T : Type} [AddCommGroup T] [Module k T] [DistribMulAction G T] [SMulCommClass G k T]
  [TopologicalSpace T] [DiscreteTopology T] [ContinuousSMul G T]
  (β : M →ₗ[k] M' →ₗ[k] T) (hβ : ∀ (g : G) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)

/-- PROVED. Any bilinear map between discrete modules is jointly continuous. -/
theorem kann_continuous_pairing {M₁ M₂ M₃ : Type} [TopologicalSpace M₁] [DiscreteTopology M₁]
    [TopologicalSpace M₂] [DiscreteTopology M₂] [TopologicalSpace M₃] (β : M₁ → M₂ → M₃) :
    Continuous fun x : M₁ × M₂ => β x.1 x.2 :=
  continuous_of_discreteTopology

/-- PROVED. A bilinear map between discrete modules is jointly continuous (the hypothesis `hβc`
of lane RC26's cup products). -/
theorem kann_contPair {R : Type} [CommRing R] {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] [TopologicalSpace M₁]
    [DiscreteTopology M₁] [TopologicalSpace M₂] [DiscreteTopology M₂] [TopologicalSpace M₃]
    (β : M₁ →ₗ[R] M₂ →ₗ[R] M₃) : Continuous fun x : M₁ × M₂ => β x.1 x.2 :=
  continuous_of_discreteTopology

/-- Definition. The `1`-cochain `g ↦ β(a(g), b(g))` (the correction term of the graded
commutativity of the cup product in degree `(1, 1)`, Nekovář, *Selmer complexes*, 3.4.5). -/
def kannProd (a : contCochain k G M 1) (b : contCochain k G M' 1) : contCochain k G T 1 :=
  ⟨(fun g => β (cfun a g) (cfun b g) : (Fin 1 → G) → T),
    (kann_continuous_pairing (fun x y => β x y)).comp
      ((mem_contCochain.1 a.2).prodMk (mem_contCochain.1 b.2))⟩

/-- Definition. The cup product `C¹_cont(G, M) × C¹_cont(G, M') → C²_cont(G, T)` of lane RC26
(`contCup β _ 1 1 2`), with domain and codomain written as the submodules of continuous cochains. -/
def kannCup : contCochain k G M 1 →ₗ[k] contCochain k G M' 1 →ₗ[k] contCochain k G T 2 :=
  contCup β (kann_contPair β) 1 1 2 rfl

/-- PROVED. `kannCup` is lane RC26's cup product. -/
theorem kannCup_apply (a : contCochain k G M 1) (b : contCochain k G M' 1) :
    kannCup β a b = contCup β (kann_contPair β) 1 1 2 rfl a b :=
  rfl

include hβ in
/-- PROVED. **Graded commutativity of the cup product of two `1`-cocycles up to an explicit
coboundary** (Nekovář, *Selmer complexes*, 3.4.5, in degree `(1, 1)`): for cocycles `a, b`,
`a ∪_β b + b ∪_{β^t} a = −d(g ↦ β(a(g), b(g)))`. -/
theorem kannCup_comm (a : contCochain k G M 1) (b : contCochain k G M' 1)
    (ha : contD k G M 1 a = 0) (hb : contD k G M' 1 b = 0) :
    contCup β (kann_contPair β) 1 1 2 rfl a b +
        contCup β.flip (kann_contPair β.flip) 1 1 2 rfl b a =
      -contD k G T 1 (kannProd β a b) := by
  have ha' : ∀ g : Fin 2 → G,
      cfun a (fun _ => g 0 * g 1) = g 0 • cfun a (fun _ => g 1) + cfun a (fun _ => g 0) := by
    intro g
    have h := congrArg (fun c : contCochain k G M 2 => cfun c g) ha
    simp only at h
    rw [kann_cfun_contD, dFun_one_apply] at h
    have h0 : cfun (0 : contCochain k G M 2) g = 0 := rfl
    rw [h0] at h
    rw [← sub_eq_zero, ← neg_eq_zero, ← h]
    abel
  have hb' : ∀ g : Fin 2 → G,
      cfun b (fun _ => g 0 * g 1) = g 0 • cfun b (fun _ => g 1) + cfun b (fun _ => g 0) := by
    intro g
    have h := congrArg (fun c : contCochain k G M' 2 => cfun c g) hb
    simp only at h
    rw [kann_cfun_contD, dFun_one_apply] at h
    have h0 : cfun (0 : contCochain k G M' 2) g = 0 := rfl
    rw [h0] at h
    rw [← sub_eq_zero, ← neg_eq_zero, ← h]
    abel
  apply Subtype.ext
  funext g
  change cupFun β 1 1 2 rfl (cfun a) (cfun b) g + cupFun β.flip 1 1 2 rfl (cfun b) (cfun a) g =
    -cfun (contD k G T 1 (kannProd β a b)) g
  rw [kann_cfun_contD, dFun_one_apply, cupFun_one_one_apply, cupFun_one_one_apply]
  change β (cfun a fun _ => g 0) (g 0 • cfun b fun _ => g 1) +
      β (g 0 • cfun a fun _ => g 1) (cfun b fun _ => g 0) =
    -(g 0 • β (cfun a fun _ => g 1) (cfun b fun _ => g 1) -
      β (cfun a fun _ => g 0 * g 1) (cfun b fun _ => g 0 * g 1) +
        β (cfun a fun _ => g 0) (cfun b fun _ => g 0))
  rw [ha' g, hb' g, ← hβ]
  simp only [map_add, LinearMap.add_apply]
  abel

end Comm

/-! ### The exact annihilator after coefficient extension -/

section Ann

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m]
  {A : Type} [CommRing A]
  {M : Type} [AddCommGroup M] [Module A M] [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) A M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M]
  {M' : Type} [AddCommGroup M'] [Module A M'] [DistribMulAction (Field.absoluteGaloisGroup F) M']
  [SMulCommClass (Field.absoluteGaloisGroup F) A M'] [TopologicalSpace M'] [DiscreteTopology M']
  [ContinuousSMul (Field.absoluteGaloisGroup F) M']
  {T : Type} [AddCommGroup T] [Module A T] [DistribMulAction (Field.absoluteGaloisGroup F) T]
  [SMulCommClass (Field.absoluteGaloisGroup F) A T] [TopologicalSpace T] [DiscreteTopology T]
  [ContinuousSMul (Field.absoluteGaloisGroup F) T]
  {T₀ : Type} [AddCommGroup T₀] [DistribMulAction (Field.absoluteGaloisGroup F) T₀]
  [TopologicalSpace T₀] [DiscreteTopology T₀] [ContinuousSMul (Field.absoluteGaloisGroup F) T₀]
  (β : M →ₗ[A] M' →ₗ[A] T)
  (ψ₀ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T₀)
  (ι : TorsAlg F B m →+ M) (ι' : TorsAlg F B m →+ M')
  {ιb : Type} [Fintype ιb] (b : ιb → A)

/-- PROVED. The cup product of an extended Kummer cocycle with a cochain `y'`, read through a
coefficient map `τ_k`, is the cup product of the Kummer cocycle with `π'_k ∘ y'` for `ψ₀`. -/
theorem kannPost_cup (π' : M' →+ TorsAlg F B m)
    (hπ' : ∀ (g : Field.absoluteGaloisGroup F) (x : M'), π' (g • x) = g • π' x)
    (τ : T →+ T₀) (hτβ : ∀ (s : TorsAlg F B m) (x : M'), τ (β (ι s) x) = ψ₀ s (π' x))
    (P : B.toAffine.Point) (y' : contCochain A (Field.absoluteGaloisGroup F) M' 1) :
    kannPost (k' := ℤ) τ (contCup β (kann_contPair β) 1 1 2 rfl
        (kummerCocycleIn ι (1 : A) P) y') =
      contCup ψ₀ (kann_contPair ψ₀) 1 1 2 rfl (kummerCocycle F B m P)
        (kannPost (k' := ℤ) π' y') := by
  apply Subtype.ext
  funext g
  change τ (cupFun β 1 1 2 rfl (cfun (kummerCocycleIn ι (1 : A) P)) (cfun y') g) =
    cupFun ψ₀ 1 1 2 rfl (cfun (kummerCocycle F B m P)) (cfun (kannPost (k' := ℤ) π' y')) g
  rw [cupFun_one_one_apply, cupFun_one_one_apply, cfun_kummerCocycleIn, cfun_kummerCocycle,
    cfun_kannPost, one_smul, hτβ, hπ']

/-- PROVED (tex 3423, 3429–3432, 3439–3445). **The exact annihilator after coefficient
extension.** Let `ι' : B(F̄)[m] → M'` be equivariant and let `M'` decompose along a finite family
`b` of scalars: equivariant additive maps `π'_k : M' → B(F̄)[m]` with `x = ∑_k b_k • ι'(π'_k x)`.
Let `τ_k : T → T₀` be equivariant with `τ_k (β (ι s) x) = ψ₀ (s, π'_k x)`. If the Kummer image of
`B(F)` is its own exact annihilator for `ψ₀` in the trace-free form `hann` (a `1`-cocycle whose
cup products with all Kummer cocycles are coboundaries is a Kummer cocycle up to a coboundary),
then every `1`-cocycle `y'` of `C^•_cont(G_F, M')` whose cup products (for `β`) with all extended
Kummer cocycles `ι ∘ κ_P` are coboundaries lies in `kummerZ' A ι' ⊔ B¹`, the degree-one term of
the extended Kummer condition. -/
theorem kannCoef_ann
    (hann : ∀ y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1,
      contD ℤ _ _ 1 y = 0 →
      (∀ P : B.toAffine.Point, contCup ψ₀ (kann_contPair ψ₀) 1 1 2 rfl
        (kummerCocycle F B m P) y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₀ 1)) →
      ∃ P : B.toAffine.Point, y - kummerCocycle F B m P ∈
        contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))
    (hι' : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι' (g • t) = g • ι' t)
    (π' : ιb → (M' →+ TorsAlg F B m))
    (hπ' : ∀ k (g : Field.absoluteGaloisGroup F) (x : M'), π' k (g • x) = g • π' k x)
    (hrec : ∀ x : M', ∑ k, b k • ι' (π' k x) = x)
    (τ : ιb → (T →+ T₀))
    (hτ : ∀ k (g : Field.absoluteGaloisGroup F) (w : T), τ k (g • w) = g • τ k w)
    (hτβ : ∀ k (s : TorsAlg F B m) (x : M'), τ k (β (ι s) x) = ψ₀ s (π' k x))
    (y' : contCochain A (Field.absoluteGaloisGroup F) M' 1)
    (hy' : contD A (Field.absoluteGaloisGroup F) M' 1 y' = 0)
    (hcup : ∀ P : B.toAffine.Point, contCup β (kann_contPair β) 1 1 2 rfl
      (kummerCocycleIn ι (1 : A) P) y' ∈
        LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1)) :
    y' ∈ kummerZ' A ι' ⊔ contB1 A (Field.absoluteGaloisGroup F) M' := by
  classical
  have key : ∀ k, ∃ P : B.toAffine.Point, ∃ d : TorsAlg F B m,
      ∀ g : Fin 1 → Field.absoluteGaloisGroup F,
        π' k (cfun y' g) = kummerFun F B m P (g 0) + (g 0 • d - d) := by
    intro k
    have hyk := kannPost_cocycle (k' := ℤ) (π' k) (hπ' k) hy'
    have hcupk : ∀ P : B.toAffine.Point, contCup ψ₀ (kann_contPair ψ₀) 1 1 2 rfl
        (kummerCocycle F B m P) (kannPost (k' := ℤ) (π' k) y') ∈
          LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₀ 1) := by
      intro P
      rw [← kannPost_cup β ψ₀ ι (π' k) (hπ' k) (τ k) (hτβ k) P y']
      exact kannPost_mem_range_two (τ k) (hτ k) (hcup P)
    obtain ⟨P, hP⟩ := hann _ hyk hcupk
    obtain ⟨c, hc⟩ := (mem_contB1_iff _).1 hP
    refine ⟨P, cfun c default, fun g => ?_⟩
    have h1 := congrArg (fun f : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1 =>
      cfun f g) hc
    simp only at h1
    rw [contD_zero_apply] at h1
    have h2 : cfun (kannPost (k' := ℤ) (π' k) y' - kummerCocycle F B m P) g =
        π' k (cfun y' g) - kummerFun F B m P (g 0) := rfl
    rw [h2] at h1
    rw [← sub_eq_iff_eq_add', ← h1]
  choose P d hPd using key
  have hdecomp : y' = ∑ k, kummerCocycleIn ι' (b k) (P k) +
      contD A (Field.absoluteGaloisGroup F) M' 0 (constCochain (∑ k, b k • ι' (d k))) := by
    apply Subtype.ext
    funext g
    have hsum' : ∀ s : Finset ιb, cfun (∑ k ∈ s, kummerCocycleIn ι' (b k) (P k)) g =
        ∑ k ∈ s, b k • ι' (kummerFun F B m (P k) (g 0)) := by
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
        rfl
    have hsum := hsum' Finset.univ
    change cfun y' g = cfun (∑ k, kummerCocycleIn ι' (b k) (P k) +
      contD A (Field.absoluteGaloisGroup F) M' 0 (constCochain (∑ k, b k • ι' (d k)))) g
    have hadd : cfun (∑ k, kummerCocycleIn ι' (b k) (P k) +
        contD A (Field.absoluteGaloisGroup F) M' 0 (constCochain (∑ k, b k • ι' (d k)))) g =
        cfun (∑ k, kummerCocycleIn ι' (b k) (P k)) g +
          cfun (contD A (Field.absoluteGaloisGroup F) M' 0
            (constCochain (∑ k, b k • ι' (d k)))) g := rfl
    rw [hadd, hsum, cfun_contD_constCochain, ← hrec (cfun y' g)]
    simp only [hPd, map_add, map_sub, hι', smul_add, smul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.smul_sum, smul_comm (g 0) (b _)]
  rw [hdecomp]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun k _ => kummerCocycleIn_mem ι' (b k) (P k))
    ⟨_, rfl⟩

/-- PROVED. The degree-one terms of an extended Kummer condition are cocycles. -/
theorem kann_mem_cocycle {N : Type} [AddCommGroup N] [Module A N]
    [DistribMulAction (Field.absoluteGaloisGroup F) N]
    [SMulCommClass (Field.absoluteGaloisGroup F) A N] [TopologicalSpace N] [DiscreteTopology N]
    [ContinuousSMul (Field.absoluteGaloisGroup F) N] (κ : TorsAlg F B m →+ N)
    (hκ : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), κ (g • t) = g • κ t)
    {u : contCochain A (Field.absoluteGaloisGroup F) N 1}
    (hu : u ∈ kummerZ' A κ ⊔ contB1 A (Field.absoluteGaloisGroup F) N) :
    contD A (Field.absoluteGaloisGroup F) N 1 u = 0 := by
  obtain ⟨z, hz, c, hc, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨e, rfl⟩ := (mem_contB1_iff c).1 hc
  rw [map_add, kummerZ'_cocycle A κ hκ z hz, contD_contD, add_zero]

/-- PROVED. **A coboundary cupped with a `1`-cocycle is a coboundary** (Leibniz rule of lane
RC26's `contNatPair`). -/
theorem kann_cup_coboundary_left
    (hβ : ∀ (g : Field.absoluteGaloisGroup F) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
    (e : contCochain A (Field.absoluteGaloisGroup F) M 0)
    (u' : contCochain A (Field.absoluteGaloisGroup F) M' 1)
    (hu' : contD A (Field.absoluteGaloisGroup F) M' 1 u' = 0) :
    contCup β (kann_contPair β) 1 1 2 rfl (contD A (Field.absoluteGaloisGroup F) M 0 e) u' ∈
      LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1) := by
  refine ⟨contCup β (kann_contPair β) 0 1 1 rfl e u', ?_⟩
  have h := (contNatPair β hβ (kann_contPair β)).leib 0 1 1 rfl e u'
  change contD A _ T 1 (contCup β (kann_contPair β) 0 1 1 rfl e u') =
    contCup β (kann_contPair β) 1 1 2 rfl (contD A _ M 0 e) u' +
      ((-1 : ℤ) ^ 0) • contCup β (kann_contPair β) 0 2 2 rfl e (contD A _ M' 1 u') at h
  have hz : contCup β (kann_contPair β) 0 2 2 rfl e (contD A _ M' 1 u') = 0 := by
    rw [hu']
    exact map_zero _
  rw [h, hz, smul_zero, add_zero]

/-- PROVED. **A `1`-cocycle cupped with a coboundary is a coboundary** (Leibniz rule). -/
theorem kann_cup_coboundary_right
    (hβ : ∀ (g : Field.absoluteGaloisGroup F) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
    (u : contCochain A (Field.absoluteGaloisGroup F) M 1)
    (hu : contD A (Field.absoluteGaloisGroup F) M 1 u = 0)
    (e : contCochain A (Field.absoluteGaloisGroup F) M' 0) :
    kannCup β u (contD A (Field.absoluteGaloisGroup F) M' 0 e) ∈
      LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1) := by
  let c10 : contCochain A (Field.absoluteGaloisGroup F) M 1 →ₗ[A]
      contCochain A (Field.absoluteGaloisGroup F) M' 0 →ₗ[A]
        contCochain A (Field.absoluteGaloisGroup F) T 1 :=
    contCup β (kann_contPair β) 1 0 1 rfl
  let c20 : contCochain A (Field.absoluteGaloisGroup F) M 2 →ₗ[A]
      contCochain A (Field.absoluteGaloisGroup F) M' 0 →ₗ[A]
        contCochain A (Field.absoluteGaloisGroup F) T 2 :=
    contCup β (kann_contPair β) 2 0 2 rfl
  have h : contD A (Field.absoluteGaloisGroup F) T 1 (c10 u e) =
      c20 (contD A (Field.absoluteGaloisGroup F) M 1 u) e +
        ((-1 : ℤ) ^ 1) • kannCup β u (contD A (Field.absoluteGaloisGroup F) M' 0 e) :=
    (contNatPair β hβ (kann_contPair β)).leib 1 0 1 rfl u e
  refine ⟨-c10 u e, ?_⟩
  rw [map_neg, h, hu, map_zero, LinearMap.zero_apply, zero_add, pow_one, neg_one_smul, neg_neg]

/-- PROVED (tex 3423, 3439–3445). **Isotropy of the extended Kummer conditions.** If the Kummer
image is isotropic for `ψ₀` (cup products of Kummer cocycles are coboundaries), `π'_k ∘ ι'` is
multiplication by integers `r_k`, and `T` decomposes along `b` through an equivariant
`j : T₀ → T` (`w = ∑_k b_k • j(τ_k w)`), then the cup product of any two elements of the
degree-one terms `kummerZ' A ι ⊔ B¹`, `kummerZ' A ι' ⊔ B¹` of the extended Kummer conditions is a
coboundary. -/
theorem kannCoef_iso
    (hiso₀ : ∀ P Q : B.toAffine.Point, contCup ψ₀ (kann_contPair ψ₀) 1 1 2 rfl
      (kummerCocycle F B m P) (kummerCocycle F B m Q) ∈
        LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₀ 1))
    (hβ : ∀ (g : Field.absoluteGaloisGroup F) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
    (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (g • t) = g • ι t)
    (hι' : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι' (g • t) = g • ι' t)
    (π' : ιb → (M' →+ TorsAlg F B m))
    (hπ' : ∀ k (g : Field.absoluteGaloisGroup F) (x : M'), π' k (g • x) = g • π' k x)
    (r : ιb → ℤ) (hπι : ∀ k (t : TorsAlg F B m), π' k (ι' t) = r k • t)
    (τ : ιb → (T →+ T₀))
    (hτβ : ∀ k (s : TorsAlg F B m) (x : M'), τ k (β (ι s) x) = ψ₀ s (π' k x))
    (j : T₀ →+ T) (hj : ∀ (g : Field.absoluteGaloisGroup F) (w : T₀), j (g • w) = g • j w)
    (hrecT : ∀ w : T, ∑ k, b k • j (τ k w) = w)
    {u : contCochain A (Field.absoluteGaloisGroup F) M 1}
    (hu : u ∈ kummerZ' A ι ⊔ contB1 A (Field.absoluteGaloisGroup F) M)
    {u' : contCochain A (Field.absoluteGaloisGroup F) M' 1}
    (hu' : u' ∈ kummerZ' A ι' ⊔ contB1 A (Field.absoluteGaloisGroup F) M') :
    contCup β (kann_contPair β) 1 1 2 rfl u u' ∈
      LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1) := by
  classical
  -- the core: two extended Kummer cocycles
  have core : ∀ P Q : B.toAffine.Point, contCup β (kann_contPair β) 1 1 2 rfl
      (kummerCocycleIn ι (1 : A) P) (kummerCocycleIn ι' (1 : A) Q) ∈
        LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1) := by
    intro P Q
    set w := contCup β (kann_contPair β) 1 1 2 rfl
      (kummerCocycleIn ι (1 : A) P) (kummerCocycleIn ι' (1 : A) Q) with hw
    have hk : ∀ k, kannPost (k' := ℤ) (τ k) w ∈
        LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₀ 1) := by
      intro k
      have h1 : kannPost (k' := ℤ) (π' k) (kummerCocycleIn ι' (1 : A) Q) =
          r k • kummerCocycle F B m Q := by
        apply Subtype.ext
        funext g
        change π' k ((1 : A) • ι' (kummerFun F B m Q (g 0))) = r k • kummerFun F B m Q (g 0)
        rw [one_smul, hπι]
      have h2 : contCup ψ₀ (kann_contPair ψ₀) 1 1 2 rfl (kummerCocycle F B m P)
          (r k • kummerCocycle F B m Q) =
            r k • contCup ψ₀ (kann_contPair ψ₀) 1 1 2 rfl (kummerCocycle F B m P)
              (kummerCocycle F B m Q) :=
        map_zsmul _ _ _
      rw [hw, kannPost_cup β ψ₀ ι (π' k) (hπ' k) (τ k) (hτβ k) P, h1, h2]
      exact Submodule.smul_mem _ _ (hiso₀ P Q)
    choose e he using hk
    refine ⟨∑ k, b k • kannPost (k' := A) j (e k), ?_⟩
    apply Subtype.ext
    funext g
    change cfun (contD A (Field.absoluteGaloisGroup F) T 1 (∑ k, b k • kannPost j (e k))) g =
      cfun w g
    rw [map_sum]
    simp only [map_smul]
    rw [kann_cfun_sum_smul, ← hrecT (cfun w g)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← kannPost_contD_one j hj (e k), he k]
    rfl
  -- generalize in the second variable
  have hsecond : ∀ P : B.toAffine.Point, ∀ {u' : contCochain A (Field.absoluteGaloisGroup F) M' 1},
      u' ∈ kummerZ' A ι' ⊔ contB1 A (Field.absoluteGaloisGroup F) M' →
      contCup β (kann_contPair β) 1 1 2 rfl (kummerCocycleIn ι (1 : A) P) u' ∈
        LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1) := by
    intro P u' hu'
    have hle : kummerZ' A ι' ⊔ contB1 A (Field.absoluteGaloisGroup F) M' ≤
        Submodule.comap (kannCup β (kummerCocycleIn ι (1 : A) P))
          (LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1)) := by
      refine sup_le (Submodule.span_le.2 ?_) ?_
      · rintro _ ⟨⟨a, Q⟩, rfl⟩
        show kannCup β (kummerCocycleIn ι (1 : A) P) (kummerCocycleIn ι' a Q) ∈
          LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1)
        rw [kummerCocycleIn_eq_smul ι' a Q, map_smul]
        exact Submodule.smul_mem _ _ (core P Q)
      · rintro _ ⟨e, rfl⟩
        exact kann_cup_coboundary_right β hβ _ (kummerCocycleIn_isCocycle ι hι 1 P) e
    exact hle hu'
  -- generalize in the first variable
  have hle : kummerZ' A ι ⊔ contB1 A (Field.absoluteGaloisGroup F) M ≤
      Submodule.comap ((kannCup β).flip u')
        (LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1)) := by
    refine sup_le (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨⟨a, P⟩, rfl⟩
      show kannCup β (kummerCocycleIn ι a P) u' ∈
        LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1)
      rw [kummerCocycleIn_eq_smul ι a P, map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hsecond P hu')
    · rintro _ ⟨e, rfl⟩
      exact kann_cup_coboundary_left β hβ e u' (kann_mem_cocycle ι' hι' hu')
  exact hle hu

/-- PROVED (tex 3423, 3439–3445). **The exact annihilator after coefficient extension, other
side.** A `1`-cocycle `y` of `C^•_cont(G_F, M)` whose cup products `y ∪ (ι' ∘ κ_Q)` with all
extended Kummer cocycles of `M'` are coboundaries lies in `kummerZ' A ι ⊔ B¹`. From
`kannCoef_ann` for the flipped pairing and the graded commutativity `kannCup_comm`. -/
theorem kannCoef_ann_left
    (hannF : ∀ y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1,
      contD ℤ _ _ 1 y = 0 →
      (∀ P : B.toAffine.Point, contCup ψ₀.flip (kann_contPair ψ₀.flip) 1 1 2 rfl
        (kummerCocycle F B m P) y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₀ 1)) →
      ∃ P : B.toAffine.Point, y - kummerCocycle F B m P ∈
        contB1 ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m))
    (hβ : ∀ (g : Field.absoluteGaloisGroup F) (a : M) (b : M'), β (g • a) (g • b) = g • β a b)
    (hι : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (g • t) = g • ι t)
    (hι' : ∀ (g : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι' (g • t) = g • ι' t)
    (π : ιb → (M →+ TorsAlg F B m))
    (hπ : ∀ k (g : Field.absoluteGaloisGroup F) (x : M), π k (g • x) = g • π k x)
    (hrec : ∀ x : M, ∑ k, b k • ι (π k x) = x)
    (τ : ιb → (T →+ T₀))
    (hτ : ∀ k (g : Field.absoluteGaloisGroup F) (w : T), τ k (g • w) = g • τ k w)
    (hτβ' : ∀ k (x : M) (t : TorsAlg F B m), τ k (β x (ι' t)) = ψ₀ (π k x) t)
    (y : contCochain A (Field.absoluteGaloisGroup F) M 1)
    (hy : contD A (Field.absoluteGaloisGroup F) M 1 y = 0)
    (hcup : ∀ Q : B.toAffine.Point, contCup β (kann_contPair β) 1 1 2 rfl y
      (kummerCocycleIn ι' (1 : A) Q) ∈ LinearMap.range (contD A (Field.absoluteGaloisGroup F) T 1)) :
    y ∈ kummerZ' A ι ⊔ contB1 A (Field.absoluteGaloisGroup F) M := by
  refine kannCoef_ann β.flip ψ₀.flip ι' ι b hannF hι π hπ hrec τ hτ
    (fun k t x => hτβ' k x t) y hy fun Q => ?_
  have hc := kannCup_comm β hβ y (kummerCocycleIn ι' (1 : A) Q) hy
    (kummerCocycleIn_isCocycle ι' hι' 1 Q)
  have hc' : kannCup β y (kummerCocycleIn ι' (1 : A) Q) +
      kannCup β.flip (kummerCocycleIn ι' (1 : A) Q) y =
        -contD A (Field.absoluteGaloisGroup F) T 1 (kannProd β y (kummerCocycleIn ι' (1 : A) Q)) :=
    hc
  have h2 : kannCup β.flip (kummerCocycleIn ι' (1 : A) Q) y =
      -contD A (Field.absoluteGaloisGroup F) T 1 (kannProd β y (kummerCocycleIn ι' (1 : A) Q)) -
        kannCup β y (kummerCocycleIn ι' (1 : A) Q) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hc'
  show kannCup β.flip (kummerCocycleIn ι' (1 : A) Q) y ∈ _
  rw [h2]
  exact Submodule.sub_mem _ (Submodule.neg_mem _ ⟨_, rfl⟩) (hcup Q)

end Ann

/-! ### Changing the target of the coefficient pairing -/

section Transport

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m]
  {T₁ : Type} [AddCommGroup T₁] [DistribMulAction (Field.absoluteGaloisGroup F) T₁]
  [TopologicalSpace T₁] [DiscreteTopology T₁] [ContinuousSMul (Field.absoluteGaloisGroup F) T₁]
  {T₂ : Type} [AddCommGroup T₂] [DistribMulAction (Field.absoluteGaloisGroup F) T₂]
  [TopologicalSpace T₂] [DiscreteTopology T₂] [ContinuousSMul (Field.absoluteGaloisGroup F) T₂]

/-- PROVED. **Cup products into isomorphic targets.** If `e₂ = f ∘ e₁` for an equivariant
additive isomorphism `f : T₁ ≃ T₂`, the cup product of two `1`-cochains for `e₂` is a coboundary
iff the one for `e₁` is. -/
theorem kann_cup_range_transport (e₁ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T₁)
    (e₂ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T₂) (f : T₁ ≃+ T₂)
    (hf : ∀ (g : Field.absoluteGaloisGroup F) (w : T₁), f (g • w) = g • f w)
    (he : ∀ s t, e₂ s t = f (e₁ s t))
    (x y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1) :
    kannCup e₂ x y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₂ 1) ↔
      kannCup e₁ x y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₁ 1) := by
  have hfs : ∀ (g : Field.absoluteGaloisGroup F) (w : T₂), f.symm (g • w) = g • f.symm w := by
    intro g w
    apply f.injective
    rw [AddEquiv.apply_symm_apply, hf, AddEquiv.apply_symm_apply]
  have h12 : kannPost (k' := ℤ) f.toAddMonoidHom (kannCup e₁ x y) = kannCup e₂ x y := by
    apply Subtype.ext
    funext g
    change f (cupFun e₁ 1 1 2 rfl (cfun x) (cfun y) g) = cupFun e₂ 1 1 2 rfl (cfun x) (cfun y) g
    rw [cupFun_one_one_apply, cupFun_one_one_apply, he]
  have h21 : kannPost (k' := ℤ) f.symm.toAddMonoidHom (kannCup e₂ x y) = kannCup e₁ x y := by
    rw [← h12]
    apply Subtype.ext
    funext g
    exact f.symm_apply_apply _
  constructor
  · intro h
    rw [← h21]
    exact kannPost_mem_range_two f.symm.toAddMonoidHom hfs h
  · intro h
    rw [← h12]
    exact kannPost_mem_range_two f.toAddMonoidHom hf h

/-- PROVED. **Negating the coefficient pairing.** If `e₂ = −e₁`, the cup product of two
`1`-cochains for `e₂` is a coboundary iff the one for `e₁` is. -/
theorem kann_cup_range_neg (e₁ e₂ : TorsAlg F B m →ₗ[ℤ] TorsAlg F B m →ₗ[ℤ] T₁)
    (he : ∀ s t, e₂ s t = -e₁ s t)
    (x y : contCochain ℤ (Field.absoluteGaloisGroup F) (TorsAlg F B m) 1) :
    kannCup e₂ x y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₁ 1) ↔
      kannCup e₁ x y ∈ LinearMap.range (contD ℤ (Field.absoluteGaloisGroup F) T₁ 1) := by
  have h : kannCup e₂ x y = -kannCup e₁ x y := by
    apply Subtype.ext
    funext g
    change cupFun e₂ 1 1 2 rfl (cfun x) (cfun y) g = -cupFun e₁ 1 1 2 rfl (cfun x) (cfun y) g
    rw [cupFun_one_one_apply, cupFun_one_one_apply, he]
  rw [h, Submodule.neg_mem_iff]

end Transport

end ZInQ.Manuscript.RC.KummerMaps
