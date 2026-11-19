import ZInQKernel.Contrib.OneProof.RC.CoefModules.Kummer

/-!
# Old Kummer, part 1: the cohomology of a coefficient-extended Kummer condition

Manuscript `diophantine_zq.tex`, Lemma `ex:arith-local-kummer`, tex 3413–3438: the Kummer condition
`U_F` "has `B(F)[2^a]` in degree zero and `B(F)/2^aB(F)` in degree one", and "derived coefficient
extension defines the scalar `A_i` condition".

Lane RC28 computes the cohomology of the scalar Kummer condition (`kummerH0AddEquiv`,
`kummerH1AddEquiv`). Here the same is shown for the coefficient-extended condition
`kummerConditionIn k ι hι` when the coefficient map `ι : B(F̄)[m] → M` is a bijection and every
scalar of `k` acts on `M` as an integer (`IntScalars k M`):

* `natCard_kummerConditionIn_H0`: `|H⁰(U)| = |B(F)[m]|` (the invariants `M^{G_F}`, transported
  along `ι`; Galois descent `exists_baseTors_of_fixed`);
* `natCard_kummerConditionIn_H1`: `|H¹(U)| = |B(F) / m B(F)|` (`P ↦ [ι ∘ κ_P]`, with kernel
  `m B(F)` by `kummerCocycle_mem_coboundaries_iff` pulled back along `ι⁻¹`, and onto by
  `exists_kummerToQuot_eq`).

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.OldKummer

open CategoryTheory WeierstrassCurve ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SelmerDuality

/-- Every scalar of `k` acts on `M` as an integer. -/
def IntScalars (k M : Type*) [CommRing k] [AddCommGroup M] [Module k M] : Prop :=
  ∀ a : k, ∃ n : ℤ, ∀ x : M, a • x = n • x

section Push

variable {F : Type} [Field F] (k : Type) [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) k M] [TopologicalSpace M] [DiscreteTopology M]
  {N : Type} [AddCommGroup N] [DistribMulAction (Field.absoluteGaloisGroup F) N]
  [TopologicalSpace N] [DiscreteTopology N]
  {k' : Type} [CommRing k'] [Module k' N] [SMulCommClass (Field.absoluteGaloisGroup F) k' N]
  (f : N →+ M)

/-- Push a continuous cochain forward along an additive map `f`: `c ↦ f ∘ c`. -/
def pushC {n : ℕ} (c : contCochain k' (Field.absoluteGaloisGroup F) N n) :
    contCochain k (Field.absoluteGaloisGroup F) M n :=
  ⟨(fun g => f (cfun c g) : (Fin n → Field.absoluteGaloisGroup F) → M),
    (continuous_of_discreteTopology (f := f)).comp (mem_contCochain.1 c.2)⟩

variable {k}

theorem cfun_pushC {n : ℕ} (c : contCochain k' (Field.absoluteGaloisGroup F) N n)
    (g : Fin n → Field.absoluteGaloisGroup F) : cfun (pushC k f c) g = f (cfun c g) :=
  rfl

theorem pushC_add {n : ℕ} (c c' : contCochain k' (Field.absoluteGaloisGroup F) N n) :
    pushC k f (c + c') = pushC k f c + pushC k f c' := by
  apply Subtype.ext; funext g; exact map_add f _ _

theorem pushC_sub {n : ℕ} (c c' : contCochain k' (Field.absoluteGaloisGroup F) N n) :
    pushC k f (c - c') = pushC k f c - pushC k f c' := by
  apply Subtype.ext; funext g; exact map_sub f _ _

theorem pushC_zsmul {n : ℕ} (z : ℤ) (c : contCochain k' (Field.absoluteGaloisGroup F) N n) :
    pushC k f (z • c) = z • pushC k f c := by
  apply Subtype.ext; funext g
  change f (z • cfun c g) = z • f (cfun c g)
  exact map_zsmul f z _

theorem pushC_zero {n : ℕ} : pushC k f (0 : contCochain k' (Field.absoluteGaloisGroup F) N n) = 0 := by
  apply Subtype.ext; funext g; exact map_zero f

/-- Pushing forward along an equivariant map commutes with `d⁰`. -/
theorem pushC_contD_zero [ContinuousSMul (Field.absoluteGaloisGroup F) M]
    [ContinuousSMul (Field.absoluteGaloisGroup F) N] (hf : ∀ (σ : Field.absoluteGaloisGroup F) (t : N), f (σ • t) = σ • f t)
    (c : contCochain k' (Field.absoluteGaloisGroup F) N 0) :
    pushC k f (contD k' (Field.absoluteGaloisGroup F) N 0 c) =
      contD k (Field.absoluteGaloisGroup F) M 0 (pushC k f c) := by
  apply Subtype.ext; funext g
  change f (cfun (contD k' (Field.absoluteGaloisGroup F) N 0 c) g) =
    cfun (contD k (Field.absoluteGaloisGroup F) M 0 (pushC k f c)) g
  rw [contD_zero_apply, contD_zero_apply, map_sub, hf]
  rfl

/-- Pushing forward along an equivariant map preserves `B¹`. -/
theorem pushC_mem_contB1 [ContinuousSMul (Field.absoluteGaloisGroup F) M]
    [ContinuousSMul (Field.absoluteGaloisGroup F) N] (hf : ∀ (σ : Field.absoluteGaloisGroup F) (t : N), f (σ • t) = σ • f t)
    {b : contCochain k' (Field.absoluteGaloisGroup F) N 1}
    (hb : b ∈ contB1 k' (Field.absoluteGaloisGroup F) N) :
    pushC k f b ∈ contB1 k (Field.absoluteGaloisGroup F) M := by
  obtain ⟨c, rfl⟩ := (mem_contB1_iff _).1 hb
  exact (mem_contB1_iff _).2 ⟨pushC k f c, (pushC_contD_zero f hf c).symm⟩

end Push

section Card

variable {F : Type} [Field F] [CharZero F] [DecidableEq F] {B : WeierstrassCurve F} [B.IsElliptic]
  {m : ℕ} [NeZero m]
  (k : Type) [CommRing k] {M : Type} [AddCommGroup M] [Module k M]
  [DistribMulAction (Field.absoluteGaloisGroup F) M]
  [SMulCommClass (Field.absoluteGaloisGroup F) k M] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul (Field.absoluteGaloisGroup F) M]

variable (ι : TorsAlg F B m →+ M)
  (hι : ∀ (σ : Field.absoluteGaloisGroup F) (t : TorsAlg F B m), ι (σ • t) = σ • ι t)
  (hbij : Function.Bijective ι)

omit [CharZero F] [DecidableEq F] [B.IsElliptic] [NeZero m] [TopologicalSpace M]
  [DiscreteTopology M] [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
include hι in
/-- The inverse of a bijective equivariant map is equivariant. -/
theorem symm_smul (σ : Field.absoluteGaloisGroup F) (x : M) :
    (AddEquiv.ofBijective ι hbij).symm (σ • x) = σ • (AddEquiv.ofBijective ι hbij).symm x := by
  apply hbij.1
  rw [hι]
  change (AddEquiv.ofBijective ι hbij) ((AddEquiv.ofBijective ι hbij).symm (σ • x)) =
    σ • (AddEquiv.ofBijective ι hbij) ((AddEquiv.ofBijective ι hbij).symm x)
  rw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/-- `B(F)[m] ≃ M^{G_F}`, `T ↦ ι(T)`. -/
def torsInvEquiv : AddSubgroup.torsionBy B.toAffine.Point (m : ℤ) ≃
    invariantsSub k (Field.absoluteGaloisGroup F) M :=
  Equiv.ofBijective (fun T => ⟨ι (baseTors F B m T), fun σ => by rw [← hι, smul_baseTors]⟩)
    ⟨fun T T' h => baseTors_injective (F := F) (B := B) m (hbij.1 (congrArg Subtype.val h)),
      fun x => by
        obtain ⟨T, hT⟩ := exists_baseTors_of_fixed (F := F) (B := B) (m := m)
          (Q := (AddEquiv.ofBijective ι hbij).symm x.1) (fun σ => by
            rw [← symm_smul ι hι hbij, x.2 σ])
        refine ⟨T, Subtype.ext ?_⟩
        change ι (baseTors F B m T) = x.1
        rw [hT]
        exact (AddEquiv.ofBijective ι hbij).apply_symm_apply x.1⟩

include hbij in
/-- **`|H⁰|` of the coefficient-extended Kummer condition is `|B(F)[m]|`** (tex 3415–3417), for a
bijective equivariant coefficient map. PROVED. -/
theorem natCard_kummerConditionIn_H0 :
    Nat.card ((kummerConditionIn k ι hι).toCC.homology 0) =
      Nat.card (AddSubgroup.torsionBy B.toAffine.Point (m : ℤ)) :=
  (Nat.card_congr (cocycleConditionH0IsoInvariants (kummerZ' k ι)
    (kummerZ'_cocycle k ι hι)).toLinearEquiv.toEquiv).trans
    (Nat.card_congr (torsInvEquiv k ι hι hbij).symm)

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
/-- `ι ∘ κ_P` is the extended Kummer cocycle `kummerCocycleIn ι 1 P`. -/
theorem pushC_kummerCocycle (P : B.toAffine.Point) :
    pushC k ι (kummerCocycle F B m P) = kummerCocycleIn ι (1 : k) P := by
  apply Subtype.ext; funext g
  change ι (kummerFun F B m P (g 0)) = (1 : k) • ι (kummerFun F B m P (g 0))
  rw [one_smul]

/-- The Kummer map into `H¹` of the coefficient-extended condition, `P ↦ [ι ∘ κ_P]`. -/
def kummerInH1Hom :
    B.toAffine.Point →+ ((kummerConditionIn k ι hι).X 1 ⧸
      condB1 (kummerZ' k ι) (kummerZ'_cocycle k ι hι)) :=
  AddMonoidHom.mk' (fun P => Submodule.Quotient.mk (ofCondOne (kummerZ' k ι)
      (kummerZ'_cocycle k ι hι) ⟨kummerCocycleIn ι (1 : k) P,
        Submodule.mem_sup_left (kummerCocycleIn_mem ι 1 P)⟩))
    fun P P' => by
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      change kummerCocycleIn ι (1 : k) (P + P') -
        (kummerCocycleIn ι (1 : k) P + kummerCocycleIn ι (1 : k) P') ∈
          contB1 k (Field.absoluteGaloisGroup F) M
      rw [← pushC_kummerCocycle, ← pushC_kummerCocycle, ← pushC_kummerCocycle, ← sub_sub,
        ← pushC_sub, ← pushC_sub]
      exact pushC_mem_contB1 ι hι (kummerCocycle_add F B m P P')

include hbij in
theorem kummerInH1Hom_eq_zero_iff (P : B.toAffine.Point) :
    kummerInH1Hom k ι hι P = 0 ↔ ∃ P' : B.toAffine.Point, m • P' = P := by
  rw [← kummerCocycle_mem_coboundaries_iff]
  refine (Submodule.Quotient.mk_eq_zero _).trans ?_
  change kummerCocycleIn ι (1 : k) P ∈ contB1 k (Field.absoluteGaloisGroup F) M ↔ _
  rw [← pushC_kummerCocycle]
  constructor
  · intro h
    have h' := pushC_mem_contB1 (k := ℤ) (AddEquiv.ofBijective ι hbij).symm.toAddMonoidHom
      (symm_smul ι hι hbij) h
    have he : pushC ℤ (AddEquiv.ofBijective ι hbij).symm.toAddMonoidHom
        (pushC k ι (kummerCocycle F B m P)) = kummerCocycle F B m P := by
      apply Subtype.ext; funext g
      exact (AddEquiv.ofBijective ι hbij).symm_apply_apply _
    rwa [he] at h'
  · exact pushC_mem_contB1 ι hι

include hbij in
theorem kummerInH1Hom_ker :
    (kummerInH1Hom k ι hι).ker = (nsmulAddMonoidHom (α := B.toAffine.Point) m).range := by
  ext P
  rw [AddMonoidHom.mem_ker, kummerInH1Hom_eq_zero_iff k ι hι hbij, AddMonoidHom.mem_range]
  rfl

variable (hint : IntScalars k M)

omit [ContinuousSMul (Field.absoluteGaloisGroup F) M] in
include hint in
/-- Every element of the extended Kummer submodule is `ι ∘ z₀` for some `z₀` in the scalar Kummer
submodule (every scalar acts as an integer). -/
theorem exists_pushC_of_mem (z : contCochain k (Field.absoluteGaloisGroup F) M 1)
    (hz : z ∈ kummerZ' k ι) : ∃ z₀ ∈ kummerZ F B m, pushC k ι z₀ = z := by
  have hsm : ∀ (a : k) (c : contCochain k (Field.absoluteGaloisGroup F) M 1), ∃ n : ℤ,
      a • c = n • c := fun a c => by
    obtain ⟨n, hn⟩ := hint a
    refine ⟨n, Subtype.ext ?_⟩
    funext g
    exact hn _
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, P⟩, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hsm a (kummerCocycleIn ι (1 : k) P)
    refine ⟨n • kummerCocycle F B m P, Submodule.smul_mem _ n (Submodule.subset_span ⟨P, rfl⟩), ?_⟩
    change pushC k ι (n • kummerCocycle F B m P) = kummerCocycleIn ι a P
    rw [pushC_zsmul, pushC_kummerCocycle, kummerCocycleIn_eq_smul ι a P, hn]
  | zero => exact ⟨0, Submodule.zero_mem _, pushC_zero ι⟩
  | add x y _ _ hx hy =>
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    exact ⟨x₀ + y₀, Submodule.add_mem _ hx₀ hy₀, pushC_add ι _ _⟩
  | smul a x _ hx =>
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hsm a (pushC k ι x₀)
    exact ⟨n • x₀, Submodule.smul_mem _ n hx₀, by rw [hn, pushC_zsmul]⟩

include hint in
theorem kummerInH1Hom_surjective : Function.Surjective (kummerInH1Hom k ι hι) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨z, hz, b, hb, hzb⟩ := Submodule.mem_sup.1 (condOne (kummerZ' k ι)
    (kummerZ'_cocycle k ι hι) x).2
  obtain ⟨z₀, hz₀, rfl⟩ := exists_pushC_of_mem k ι hint z hz
  obtain ⟨P, hP⟩ := exists_kummerToQuot_eq F B m z₀ hz₀
  rw [kummerToQuot_apply, Submodule.Quotient.eq] at hP
  refine ⟨P, ?_⟩
  rw [Submodule.mkQ_apply]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  change kummerCocycleIn ι (1 : k) P - (condOne (kummerZ' k ι) (kummerZ'_cocycle k ι hι) x :
    contCochain k (Field.absoluteGaloisGroup F) M 1) ∈ contB1 k (Field.absoluteGaloisGroup F) M
  rw [← hzb, ← sub_sub, ← pushC_kummerCocycle, ← pushC_sub]
  exact sub_mem (pushC_mem_contB1 ι hι hP) hb

/-- **`B(F)/mB(F) ≅ H¹` of the coefficient-extended Kummer condition** (`P ↦ [ι ∘ κ_P]`). -/
def kummerInH1Equiv :
    (B.toAffine.Point ⧸ (nsmulAddMonoidHom (α := B.toAffine.Point) m).range) ≃+
      ((kummerConditionIn k ι hι).X 1 ⧸ condB1 (kummerZ' k ι) (kummerZ'_cocycle k ι hι)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (kummerInH1Hom_ker k ι hι hbij).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (kummerInH1Hom_surjective k ι hι hint))

include hbij hint in
/-- **`|H¹|` of the coefficient-extended Kummer condition is `|B(F)/mB(F)|`** (tex 3415–3418), for
a bijective equivariant coefficient map and integer scalars. PROVED. -/
theorem natCard_kummerConditionIn_H1 :
    Nat.card ((kummerConditionIn k ι hι).toCC.homology 1) =
      Nat.card (B.toAffine.Point ⧸ (nsmulAddMonoidHom (α := B.toAffine.Point) m).range) :=
  (Nat.card_congr (kummerConditionInH1Iso k ι hι).toLinearEquiv.toEquiv).trans
    (Nat.card_congr (kummerInH1Equiv k ι hι hbij hint).toEquiv.symm)

end Card

end ZInQ.Contrib.CloudB3RC53.OldKummer
