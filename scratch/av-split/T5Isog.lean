import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.Contrib.AbVarBC.Torsion

/-!
# av-split, rows H-25 (`PkgI2.TorsionStructure`) and H-54 (`WeilPairing.IsogenyQuasiInverse`)

* H-25: the row is imported from `ZInQKernel/HDecomp/Objects.lean` (unchanged). LEAF
  `MumfordTorsionAlgClosed` (Mumford, *Abelian varieties*, §4, Application 2 (iv), over an
  algebraically closed field, points over that field). Proof of the row from the leaf:
  base change to `K̄` (`ObjBridge.isAbelianVariety_baseChange`), `dim A_{K̄} = dim A`
  (`dim_baseChange_scheme`), `A_{K̄}(K̄) ≃* A(K̄)` (`AbVarBC.bcPt`).
* H-54: the row and its definitions `P`, `homP`, `IsQuasiInverse` are copied verbatim from
  `scratch/g0-assemble2/parts/a35_g12det.lean` (namespace `WeilPairing`). LEAF
  `MilneIsogenyQuasiInverse` (the printed statement as an equality of morphisms, with `deg f`
  weakened to some `d ≥ 1`). Proof: evaluate on `K̄`-points (`AbVarBC.comp_natCast_hom`).
-/

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

/-! ## Row H-54: verbatim copy (namespace `WeilPairing`, `a35_g12det.lean` L1-L20, L100, L303-L306,
L400-L404) -/

namespace WeilPairing

open PkgI3 PkgI3.AbVar

variable {K : Type} [Field K]

/-- The group `A(K̄)`, written additively. -/
abbrev P (A : AbVar K) : Type := Additive (A.Pt (AlgebraicClosure K))

/-- A homomorphism `f : A → B` acting on `K̄`-points. -/
def homP {A B : AbVar K} (f : Hom A B) : P A →+ P B := MonoidHom.toAdditive (ptMap f)

/-- `ψ : Â → A` is a quasi-inverse of `λ` of exponent `d`: `λ ψ = [d]` on `Â(K̄)` and
`ψ λ = [d]` on `A(K̄)`. -/
def IsQuasiInverse {A B : AbVar K} (f : Hom A B) (g : Hom B A) (d : ℕ) : Prop :=
  (∀ z : P B, homP f (homP g z) = d • z) ∧ ∀ x : P A, homP g (homP f x) = d • x

/-- **Quasi-inverse of an isogeny.** For an isogeny `f : A → B` (finite and surjective) there are
`d ≥ 1` and `g : B → A` with `f g = [d]`, `g f = [d]` (take `d = deg f`, which kills `ker f`;
Mumford §7, Remark after Thm 4, and §8 Thm 1 (UNVERIFIED numbering); Milne 1986, Prop. 7.1 /
Rem. 8.4 (UNVERIFIED)). Stated on `K̄`-points, a consequence. -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A, IsQuasiInverse f g d

end WeilPairing

namespace AvSplit

open PkgI3 PkgI3.AbVar

/-! ## Row H-54: the leaf and the proof -/

/-- **LEAF (H-54; published form).** Milne, *Abelian varieties*, in Cornell–Silverman (eds.),
*Arithmetic Geometry* (1986), §8, Remark 8.4 (UNVERIFIED number; also Milne's online notes
*Abelian Varieties* (2008), Prop. 7.1 / Rem. 7.3, UNVERIFIED): "for an isogeny `f : A → B` of
degree `n` there is an isogeny `g : B → A` with `g ∘ f = n_A` and `f ∘ g = n_B`", over any field.
Specialization read off the same display: the degree `n` is weakened to "some `d ≥ 1`", the
conclusion "`g` is an isogeny" is dropped, and the hypothesis "isogeny" is given as "finite and
surjective" (`IsIsogenyMor`), which implies Milne's "surjective with finite kernel" (the kernel is
the base change of the finite `f` along the zero section). `[d]_A` is `((d : ℤ) : End A)`, the
`d`-fold sum of the identity in `Hom(A, A)`. Over an algebraically closed field this is also
Mumford, *Abelian varieties* (1970), §7, Remark after Thm 4 (UNVERIFIED). -/
def MilneIsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : AbVar K) (f : Hom A B), IsIsogenyMor f.hom →
    ∃ d : ℕ, 0 < d ∧ ∃ g : Hom B A,
      f.hom ≫ g.hom = (((d : ℤ) : End A)).hom ∧ g.hom ≫ f.hom = (((d : ℤ) : End B)).hom

/-- On points, `homP f` is composition with `f`. -/
theorem homP_apply {K : Type} [Field K] {A B : AbVar K} (f : Hom A B) (x : WeilPairing.P A) :
    WeilPairing.homP f x = Additive.ofMul (Additive.toMul x ≫ f.hom) := rfl

/-- `x ≫ [d] = d • x` on additive points. -/
theorem ofMul_comp_natCast {K : Type} [Field K] (A : AbVar K) (x : WeilPairing.P A) (d : ℕ) :
    Additive.ofMul (Additive.toMul x ≫ (((d : ℤ) : End A)).hom) = d • x := by
  rw [ZInQ.Contrib.AbVarBC.comp_natCast_hom]
  rfl

/-- **Row H-54 from its published-form leaf (proved).** -/
theorem isogenyQuasiInverse_of_milne (h : MilneIsogenyQuasiInverse) :
    WeilPairing.IsogenyQuasiInverse := by
  intro K _ A B f hf
  obtain ⟨d, hd, g, hfg, hgf⟩ := h K A B f hf
  refine ⟨d, hd, g, fun z => ?_, fun x => ?_⟩
  · rw [homP_apply, homP_apply]
    change Additive.ofMul (Additive.toMul z ≫ g.hom ≫ f.hom) = d • z
    rw [hgf, ofMul_comp_natCast]
  · rw [homP_apply, homP_apply]
    change Additive.ofMul (Additive.toMul x ≫ f.hom ≫ g.hom) = d • x
    rw [hfg, ofMul_comp_natCast]

/-! ## Row H-25: the leaf and the proof -/

open PkgI2 (IsAbelianVariety Pts torsion)

/-- **LEAF (H-25; published form).** Mumford, *Abelian varieties* (1970; 2nd ed. 1974), §4,
Application 2, (iv) (UNVERIFIED locator): for an abelian variety `X` of dimension `g` over an
algebraically closed field `k` and an integer `n` with `char k ∤ n`, the group
`X_n = {x ∈ X : nx = 0}` of `n`-torsion points is isomorphic to `(ℤ/nℤ)^{2g}`. Mumford's points
are the closed points, i.e. the `k`-points (`Pts A k`); `dim` is the topological Krull dimension
of the underlying space; "`char k ∤ n`" with `n ≥ 1` is `(n : k) ≠ 0`; the group isomorphism is a
bijection `e` with `e(x + y) = e x + e y` (written multiplicatively on points). -/
def MumfordTorsionAlgClosed : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Grp (Over (Spec (.of k)))) [IsAbelianVariety A]
    (g n : ℕ), topologicalKrullDim A.X.left = (g : WithBot ℕ∞) → 0 < n → (n : k) ≠ 0 →
      ∃ e : torsion A k n ≃ (Fin (2 * g) → ZMod n),
        ∀ x y : torsion A k n,
          ∀ h : x.1 * y.1 ∈ torsion A k n, e ⟨x.1 * y.1, h⟩ = e x + e y

section T5

variable {K : Type} [Field K] (A : Grp (Over (Spec (.of K)))) [IsAbelianVariety A]

local notation "Kb" => AlgebraicClosure K

/-- The base change `A_{K̄}` (I2's `baseChange`). -/
abbrev Ab : Grp (Over (Spec (.of (AlgebraicClosure K)))) := PkgI2.baseChange A (AlgebraicClosure K)

/-- `A_{K̄}(K̄) ≃* A(K̄)` on I2's points (task unram-tate's `bcPt` through the bridge). -/
def bcPts : Pts (Ab A) Kb ≃* Pts A Kb :=
  ZInQ.Contrib.AbVarBC.bcPt (L := Kb) (ObjBridge.ofGrp A) Kb

/-- `bcPts` restricted to `n`-torsion. -/
def bcTors (n : ℕ) : torsion (Ab A) Kb n ≃ torsion A Kb n where
  toFun x := ⟨bcPts A x.1, by
    change bcPts A x.1 ^ n = 1
    rw [← map_pow]
    have : x.1 ^ n = 1 := x.2
    rw [this, map_one]⟩
  invFun y := ⟨(bcPts A).symm y.1, by
    change (bcPts A).symm y.1 ^ n = 1
    rw [← map_pow]
    have : y.1 ^ n = 1 := y.2
    rw [this, map_one]⟩
  left_inv x := Subtype.ext ((bcPts A).symm_apply_apply x.1)
  right_inv y := Subtype.ext ((bcPts A).apply_symm_apply y.1)

/-- `dim A_{K̄} = dim A`. -/
theorem dim_Ab : topologicalKrullDim (Ab A).X.left = topologicalKrullDim A.X.left := by
  haveI := PkgI2.IsAbelianVariety.smooth (A := A)
  exact ZInQ.Contrib.AbVarBC.dim_baseChange_scheme (AlgebraicClosure K) A.X.left A.X.hom

end T5

/-- **Row H-25 from its published-form leaf (proved).** The kernel's `PkgI2.TorsionStructure` at
universe `0` (the universe of every consumer: `K : Type`). -/
theorem torsionStructure_of_mumford (h : MumfordTorsionAlgClosed) :
    PkgI2.TorsionStructure.{0} := by
  intro K _ A _ g n hg hn hnK
  haveI : IsAbelianVariety (Ab A) := ObjBridge.isAbelianVariety_baseChange A (AlgebraicClosure K)
  have hnK' : ((n : ℕ) : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast (algebraMap K (AlgebraicClosure K))]
    exact (map_ne_zero _).2 hnK
  obtain ⟨e, he⟩ := h (AlgebraicClosure K) (Ab A) g n ((dim_Ab A).trans hg) hn hnK'
  refine ⟨(bcTors A n).symm.trans e, fun x y hxy => ?_⟩
  simp only [Equiv.trans_apply]
  have hmem : ((bcTors A n).symm x).1 * ((bcTors A n).symm y).1 ∈ torsion (Ab A) _ n := by
    change (((bcTors A n).symm x).1 * ((bcTors A n).symm y).1) ^ n = 1
    rw [mul_pow, ((bcTors A n).symm x).2, ((bcTors A n).symm y).2, _root_.one_mul]
  rw [← he _ _ hmem]
  congr 1
  apply Subtype.ext
  change (bcPts A).symm (x.1 * y.1) = _
  rw [map_mul]
  rfl

end AvSplit

#print axioms AvSplit.isogenyQuasiInverse_of_milne
#print axioms AvSplit.torsionStructure_of_mumford
