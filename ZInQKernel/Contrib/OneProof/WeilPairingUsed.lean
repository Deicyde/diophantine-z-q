import ZInQKernel.OneProof.H.TailZ24

/-! # weil-used: what the route reads of `weilPairingMumford`, and its split into printed properties

The added field `HDec.HSyn.OpenAddedLeaves17.weilPairingMumford : T09Pic.WeilPairingMumford` (TailZ34; statement
`ZInQKernel/OneProof/H/TailZ24.lean:708`) bundles six clauses about one pairing
`e_n : A[n] × Pic⁰[n] → μ_n`: (1) perfect, (2) `G_K`-equivariant, (3) compatible in `n`, (4) adjoint for the genuine
`f^∨`, (5) `e_n(x, λ_L x) = 1` for ample `L`, (6) values `weilScalar` (Mumford's `ē_n`).

**Consumers** (probe `scratch/weil-used/FieldUse.lean` over the closure of `ZInQ.OneProof.frozenTarget`): the only
consumer is `T09Pic.t09SymmIsogenyExists_of_four` (in `addedLeaves12_of_open13`, TailZ24). It discards clause (6)
(`weilPairingPicZeroPrinted_of_mumford`) and reads (1)-(5) to build `WeilPairing.WeilDual.mk` and
`WeilPairing.SymmIsogeny.mk`. Downstream of `T09_SymmIsogenyExists` no constant reads `WeilDual.dualEnd` (clause 4)
nor the right half of `IsPerfect` (clause 1): those structure fields are inert.

This file gives:
* §1 the split of the field into six statements about Mumford's genuine `ē_n`, one printed property each (t09-pic's
  L4a-f, copied verbatim), `weilPairingMumford_of_split` (they give the field), and `split_of_weilPairingMumford`
  (the field gives each of them: none is stronger);
* §2 the field restated as the conjunction its consumer reads (`T09Pic.WeilPairingPicZero`: clause 6 dropped,
  existential dual, very ample `L`), with both implications;
* §3 `WeilPairingRead`, the conjunction read below `T09_SymmIsogenyExists` (left kernel, Galois, compatibility,
  alternation), implied by the field; recorded for a later change of `WeilDual`, not a fold. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace WeilUsed

open PkgI3 PkgI3.AbVar T09Pic HDec.WeilPairing

variable {K : Type} [Field K]

/-! ## §1. The six printed properties of `ē_n` (one leaf each)

Copied verbatim from `scratch/t09-pic/Pic.lean`, lines 751-811 (t09-pic, commit 131fc43a1), namespace `T09Pic`
replaced by `WeilUsed`. -/

section LeafSplit

open HDec.WeilPairing

/-- `e` is Mumford's pairing: its values are `weilScalar` (as constants of `Γ(A_K̄, 𝒪)`) for every
`n ≥ 1` invertible in `K`. Since `constK` is injective, this pins `e n` for those `n`. -/
def IsMumfordPairing {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) {B : AbVar K} (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n) : Prop :=
  ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ (x : tors A n) (y : tors B n),
    constK A ((e n x y).val : AlgebraicClosure K) =
      weilScalar rep j n (Additive.toMul (x : HDec.WeilPairing.P A)) (Additive.toMul (y : HDec.WeilPairing.P B))

/-- **LEAF L4a (`ē_n` is a bilinear `μ_n`-valued pairing).** Mumford §20 (definition of `ē_n`;
values in `μ_n`, bilinear), with Kleiman 9.2.5 and Mumford §8 (iv); UNVERIFIED numbering. -/
def WeilPairingExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j → ∃ e : ∀ n : ℕ, Pairing A B n, IsMumfordPairing rep j e

/-- **LEAF L4b (`ē_n` is perfect).** Mumford §20 (n prime to the characteristic); UNVERIFIED. -/
def WeilPairingPerfect : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → IsPerfect (e n)

/-- **LEAF L4c (`ē_n` is Galois-equivariant).** `ē_n` is defined over `K` (Milne 1986 §16);
UNVERIFIED. -/
def WeilPairingGalois : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)

/-- **LEAF L4d (compatibility `ē_{mn}(x, y) = ē_n(mx, y)` for `y ∈ Â[n]`).** Mumford §20;
UNVERIFIED. -/
def WeilPairingCompat : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
      ∀ (x : tors A (m * n)) (y : tors B n),
        (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val

/-- **LEAF L4e (adjunction `ē_n(x, f^∨ y) = ē_n(f x, y)`).** Mumford §20 (5) for isogenies;
Milne 1986 Lemma 16.2(c) for all homomorphisms; UNVERIFIED. -/
def WeilPairingDual : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ (f : End A) (fv : End B), fv.hom ≫ j = j ≫ dualP rep f.hom → ∀ n : ℕ, 0 < n →
      (n : K) ≠ 0 → ∀ x y, e n x (torsMap fv n y) = e n (torsMap f n x) y

/-- **LEAF L4f (`e^L_n(x, x) = 1`).** Mumford §23 (`e^L_n(x, y) = ē_n(x, φ_L(y))` is
skew-symmetric with `e^L_n(x, x) = 1`; stated for ample `L`); UNVERIFIED. -/
def WeilPairingAlternating : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P)
    (e : ∀ n : ℕ, Pairing A B n), IsPicZero rep B j → IsMumfordPairing rep j e →
    ∀ L : A.X.left.Pic, IsAmple A.X.left L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
      ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0


end LeafSplit

/-- The six split leaves give the field `weilPairingMumford` (t09-pic's `weilPairingMumford_of_split`,
`scratch/t09-pic/Pic.lean:815`, verbatim). -/
theorem weilPairingMumford_of_split (ha : WeilPairingExists) (hb : WeilPairingPerfect)
    (hc : WeilPairingGalois) (hd : WeilPairingCompat) (he : WeilPairingDual)
    (hf : WeilPairingAlternating) : WeilPairingMumford := by
  intro K _ A P rep B j hj
  obtain ⟨e, hM⟩ := ha K A P rep B j hj
  exact ⟨e, hb K A P rep B j e hj hM, hc K A P rep B j e hj hM, hd K A P rep B j e hj hM,
    he K A P rep B j e hj hM, hf K A P rep B j e hj hM, hM⟩

/-! ### No split leaf is stronger than the field

`constK` is injective (`A ×_K K̄` is nonempty, so `Γ(A_K̄, 𝒪)` is a nonzero ring), so `IsMumfordPairing` pins `e n`
for every `n ≥ 1` invertible in `K`; the field's witness then gives each property for every Mumford pairing. -/

/-- `constK A : K̄ → Γ(A_K̄, 𝒪)` is injective. -/
theorem constK_injective (A : AbVar K) : Function.Injective (constK A) := by
  have : Nonempty (𝟙_ (Over (Spec (CommRingCat.of K)))).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of K)))
  have : Nonempty A.X.left := ⟨η[A.X].left (Nonempty.some inferInstance)⟩
  have : Nonempty (ptK K).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of (AlgebraicClosure K))))
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hX : Nonempty ↥(pullback A.X.hom (ptK K).hom : Scheme.{0}) := inferInstance
  have : Nonempty (⊤ : (pullback A.X.hom (ptK K).hom : Scheme.{0}).Opens) :=
    ⟨⟨hX.some, trivial⟩⟩
  exact (constK A).injective

/-- Two Mumford pairings agree at every `n ≥ 1` invertible in `K`. -/
theorem isMumfordPairing_eq {A : AbVar K} {P : Over (Spec (CommRingCat.of K))}
    {rep : (picardFunctor A.X.hom).obj.RepresentableBy P} {B : AbVar K} {j : B.X ⟶ P}
    {e e' : ∀ n : ℕ, Pairing A B n} (h : IsMumfordPairing rep j e) (h' : IsMumfordPairing rep j e')
    {n : ℕ} (hn : 0 < n) (hnK : (n : K) ≠ 0) : e n = e' n := by
  refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun y => ?_
  apply Mu.val_injective
  apply Units.ext
  apply constK_injective A
  rw [h n hn hnK x y, h' n hn hnK x y]

/-- **The field gives each of the six split leaves** (so the split is never stronger than the field). -/
theorem split_of_weilPairingMumford (h : WeilPairingMumford) :
    WeilPairingExists ∧ WeilPairingPerfect ∧ WeilPairingGalois ∧ WeilPairingCompat ∧ WeilPairingDual ∧
      WeilPairingAlternating := by
  refine ⟨fun K _ A P rep B j hj => ?_, fun K _ A P rep B j e hj hM => ?_,
    fun K _ A P rep B j e hj hM => ?_, fun K _ A P rep B j e hj hM => ?_,
    fun K _ A P rep B j e hj hM => ?_, fun K _ A P rep B j e hj hM => ?_⟩
  · obtain ⟨e', -, -, -, -, -, h6⟩ := h K A P rep B j hj
    exact ⟨e', h6⟩
  · obtain ⟨e', h1, -, -, -, -, h6⟩ := h K A P rep B j hj
    intro n hn hnK
    rw [isMumfordPairing_eq hM h6 hn hnK]
    exact h1 n hn hnK
  · obtain ⟨e', -, h2, -, -, -, h6⟩ := h K A P rep B j hj
    intro n hn hnK
    rw [isMumfordPairing_eq hM h6 hn hnK]
    exact h2 n hn hnK
  · obtain ⟨e', -, -, h3, -, -, h6⟩ := h K A P rep B j hj
    intro m n hm hn hmnK x y
    have hnK : (n : K) ≠ 0 := by
      rw [Nat.cast_mul] at hmnK
      exact right_ne_zero_of_mul hmnK
    rw [isMumfordPairing_eq hM h6 (Nat.mul_pos hm hn) hmnK, isMumfordPairing_eq hM h6 hn hnK]
    exact h3 m n hm hn hmnK x y
  · obtain ⟨e', -, -, -, h4, -, h6⟩ := h K A P rep B j hj
    intro f fv hfv n hn hnK x y
    rw [isMumfordPairing_eq hM h6 hn hnK]
    exact h4 f fv hfv n hn hnK x y
  · obtain ⟨e', -, -, -, -, h5, h6⟩ := h K A P rep B j hj
    intro L hL lam hlam n hn hnK x
    rw [isMumfordPairing_eq hM h6 hn hnK]
    exact h5 L hL lam hlam n hn hnK x

/-- **`t09SymmIsogenyExists` from L1-L3 and the six split leaves.** -/
theorem t09SymmIsogenyExists_of_split (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (h3 : PhiAmpleIsogeny) (ha : WeilPairingExists) (hb : WeilPairingPerfect) (hc : WeilPairingGalois)
    (hd : WeilPairingCompat) (he : WeilPairingDual) (hf : WeilPairingAlternating) :
    HDec.WeilPairing.T09_SymmIsogenyExists :=
  t09SymmIsogenyExists_of_four h1 h2 h3 (weilPairingMumford_of_split ha hb hc hd he hf)

/-! ## §2. The field restated as what its consumer reads

`T09Pic.WeilPairingPicZero` (TailZ24) is the field without clause (6), with an existential dual in clause (4) and
clause (5) for very ample `L`: exactly what `t09SymmIsogenyExists_of_leaves` reads. -/

/-- The field implies the restatement (never stronger). -/
theorem weilPairingPicZero_of_mumford (h : WeilPairingMumford) : WeilPairingPicZero :=
  weilPairingPicZero_of_printed veryAmpleIsAmple (weilPairingPicZeroPrinted_of_mumford h)

/-- The restatement suffices for the field's only consumer. -/
theorem t09SymmIsogenyExists_of_picZero (h1 : PicRepresentableAbVar) (h2 : PicZeroAbVar)
    (h3 : PhiAmpleIsogeny) (h4 : WeilPairingPicZero) : HDec.WeilPairing.T09_SymmIsogenyExists :=
  t09SymmIsogenyExists_of_leaves h1 h2 (phiVeryAmpleIsogeny_of_printed veryAmpleIsAmple h3) h4

/-! ## §3. What is read below `T09_SymmIsogenyExists`

No constant in the closure of `ZInQ.OneProof.frozenTarget` reads `WeilDual.dualEnd`, and the only reader of
`WeilDual.perfect` (`WeilPairing.weil_nondeg`) uses its left half. Dropping clause (4) and the right half of (1)
would need a weaker `WeilDual` and the consumers of `T09_SymmIsogenyExists` (`tatePairingZl_of_leaves4`,
`oldT9_of_symmIsogeny`) rerouted; this is recorded, not folded. -/

/-- **The properties of the Weil pairing read on the route** (below `T09_SymmIsogenyExists`): a pairing
`e_n : A[n] × Pic⁰[n] → μ_n` with trivial left kernel, `G_K`-equivariant and compatible in `n`, with
`e_n(x, λ_L x) = 1` for very ample `L` (Mumford §20 and §23; Milne 1986 §16; UNVERIFIED numbering). Implied by the
field (`weilPairingRead_of_mumford`). -/
def WeilPairingRead : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P) (B : AbVar K) (j : B.X ⟶ P),
    IsPicZero rep B j →
    ∃ e : ∀ n : ℕ, Pairing A B n,
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x, (∀ y, e n x y = 0) → x = 0) ∧
      (∀ n : ℕ, 0 < n → (n : K) ≠ 0 → HDec.WeilPairing.IsGalEquivariant (e n)) ∧
      (∀ m n : ℕ, 0 < m → 0 < n → ((m * n : ℕ) : K) ≠ 0 →
        ∀ (x : tors A (m * n)) (y : tors B n),
          (e (m * n) x (torsIncl B (dvd_mul_left n m) y)).val = (e n (torsSmul A m n x) y).val) ∧
      (∀ L : A.X.left.Pic, IsVeryAmple A L → ∀ lam : Hom A B, lam.hom ≫ j = phiL rep L →
        ∀ n : ℕ, 0 < n → (n : K) ≠ 0 → ∀ x : tors A n, e n x (torsMap lam n x) = 0)

/-- The restatement of §2 implies `WeilPairingRead`. -/
theorem weilPairingRead_of_picZero (h : WeilPairingPicZero) : WeilPairingRead := by
  intro K _ A P rep B j hj
  obtain ⟨e, h1, h2, h3, -, h5⟩ := h K A P rep B j hj
  exact ⟨e, fun n hn hnK => (h1 n hn hnK).1, h2, h3, h5⟩

/-- The field implies `WeilPairingRead`. -/
theorem weilPairingRead_of_mumford (h : WeilPairingMumford) : WeilPairingRead :=
  weilPairingRead_of_picZero (weilPairingPicZero_of_mumford h)

end WeilUsed
