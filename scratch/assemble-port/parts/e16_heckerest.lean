/-! ## assemble-port: hecke-rest, its new parts (mk/mk_heckerest.py; two edits documented there) -/

/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 1: `HeckeFibreSizes` from three leaves on QM pairs and `TorsionStructure`

The count (computed in `fibre_sizes.py`): a twist fibre is the set of classes of
`(A, ι ∘ t_k, η)`, `k ∈ Fin 4`, `η` one of the `72` level structures on `(A, ι ∘ t_k)`.
`(A, ι ∘ t_k, η) ≅ (A, ι ∘ t_l, η')` iff some `φ : (A, ι ∘ t_k) ≅ (A, ι ∘ t_l)` carries `η` to
`η'`; distinct `φ` give distinct `η'` (Serre's lemma). So each class has `s · a` members, where
`a = |Aut(A, ι)|` and `s = #{m | (A, ι ∘ t_m) ≅ (A, ι)}`, and `n · s · a = 4 · 72 = 288`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRest

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.Exact LeafQM.AV.Pin.NormO PkgI3 TSHecke
open TSHeckeUnits
open scoped MonObj
open Classical

/-! ## The three leaves -/

/-- **Leaf (Shimura's classification of the centralizer of `ι(𝒪)`; units of imaginary quadratic
orders).** For an abelian surface `A` over `ℚ̄` with QM `ι : 𝒪 ↪ End(A)` by the maximal order of
the indefinite quaternion algebra `B = (2, −3)` of discriminant `6`, the centralizer
`End_𝒪(A) = com(ι)` is `ℤ` or an order in one imaginary quadratic field (Shimura, *On analytic
families of polarized abelian varieties and automorphic functions*, Ann. of Math. 78 (1963), and
the standard classification of `End⁰(A) ⊇ B`: `End⁰(A) = B` or `M₂(K)` with `K` imaginary
quadratic splitting `B`; e.g. Rotger, *Quaternions, polarizations and class numbers*, J. reine
angew. Math. 561 (2003), §2; locators UNVERIFIED). Consequences stated here: the automorphism
group of the pair, `com(ι)^×`, has `4` elements under CM by `ℤ[i]` (a maximal order, so
`com = ℤ[i]`), `6` under CM by `ℤ[ζ₃]`, and `2` (`±1`) otherwise; and no two of the three CM
types occur together (the three fields `ℚ(i)`, `ℚ(√−3)`, `ℚ(√−6)` are distinct). -/
def QMAutCard : Prop :=
  ∀ (A : AbVar Qbar), A.dim = 2 → ∀ q : QMStr A,
    Nat.card (QMIso q q) = (if HasCM4 q then 4 else if HasCM3 q then 6 else 2) ∧
    ¬ (HasCM4 q ∧ HasCM3 q) ∧ ¬ (HasCM4 q ∧ HasCM24 q) ∧ ¬ (HasCM3 q ∧ HasCM24 q)

/-- **Leaf (Serre's lemma, level 3).** An endomorphism of finite order of an abelian variety
over `ℚ̄` that fixes every `3`-torsion point is the identity (Serre's lemma in its finite-order
form: J.-P. Serre, *Rigidité du foncteur de Jacobi d'échelon n ≥ 3*, appendix to Sém. H. Cartan
13 (1960/61), exp. 17; Silverberg–Zarhin, J. Pure Appl. Algebra 111 (1996); Mumford,
*Abelian varieties*, §21, Theorem 5 is the polarized form; locators UNVERIFIED. Proof: `φ − 1`
kills `A[3]`, so `φ = 1 + 3β` with `β ∈ End(A)`; an eigenvalue `ζ ≠ 1` of the semisimple `φ`
would make `(ζ − 1)/3` integral). Stated over the kernel's genuine abelian varieties
`PkgI3.AbVar` and their `ℚ̄`-points. -/
def SerreRigidity3 : Prop :=
  ∀ (A : AbVar Qbar) (φ : AbVar.End A), (∃ m : ℕ, 0 < m ∧ φ ^ m = 1) →
    (∀ x : A.Pt Qbar, x ^ 3 = 1 → x ≫ φ.hom = x) → φ = 1

/-- **Leaf (fixed points of the Atkin–Lehner involutions on `X₆ = X₀^6(1)`).** The twists
`rep 1, rep 2, rep 3` (conjugation by `i, j, ij`, of reduced norms `−2, 3, −6`) represent
`w₂, w₃, w₆` (Rotger, *Modular Shimura varieties and forgetful maps*, Trans. AMS 356 (2004),
§§2-4; Ogg, *Real points on Shimura curves* (1983), fixed points of `w_m`; locators UNVERIFIED).
A pair isomorphic to its `w_m`-twist is a fixed point of `w_m`, hence a CM point by an order
containing `ℤ[μ]` for an elliptic `μ ∈ 𝒪` of norm `m`; by the embedding check of
`fibre_sizes.py` §5 (`ℚ(√−2)`, `ℚ(√−7)`, `ℚ(√−11)`, `ℚ(√−5)`, `ℚ(√−15)`, `ℚ(√−23)` do not
embed in `B`; for `m = 3` the field is `ℚ(√−3)` and `𝒪 ⊗ ℤ₂` is the maximal order of the
division algebra, so the CM order contains `ℤ[ζ₃]`) the CM is by `ℤ[i]`, `ℤ[ζ₃]`, `ℤ[√−6]`. -/
def ALFixedPoints : Prop :=
  ∀ (A : AbVar Qbar), A.dim = 2 → ∀ q : QMStr A,
    (Nonempty (QMIso (q.twist (rep 1)) q) → HasCM4 q) ∧
    (Nonempty (QMIso (q.twist (rep 2)) q) → HasCM3 q) ∧
    (Nonempty (QMIso (q.twist (rep 3)) q) → HasCM24 q)

/-! ## Generalities on QM isomorphisms -/

section General

variable {K : Type} [Field K]

theorem qmIso_ext {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} {G G' : QMIso q q'}
    (h : G.φ.hom = G'.φ.hom) : G = G' := by
  have hφ : G.φ = G'.φ := AbVar.Hom.ext' h
  have hψ : G.ψ = G'.ψ := by
    apply AbVar.Hom.ext'
    calc G.ψ.hom = G.ψ.hom ≫ G'.φ.hom ≫ G'.ψ.hom := by rw [G'.left, Category.comp_id]
      _ = G.ψ.hom ≫ G.φ.hom ≫ G'.ψ.hom := by rw [h]
      _ = G'.ψ.hom := by rw [← Category.assoc, G.right, Category.id_comp]
  cases G; cases G'; cases hφ; cases hψ; rfl

/-- Re-index a QM isomorphism along `g0 : 𝒪 → 𝒪` (same underlying maps). -/
def qmCongr {A A' : AbVar K} {q₁ q₁' : QMStr A} {q₂ q₂' : QMStr A'} (G : QMIso q₁ q₂)
    (g0 : O → O) (h₁ : ∀ a, q₁'.iota a = q₁.iota (g0 a)) (h₂ : ∀ a, q₂'.iota a = q₂.iota (g0 a)) :
    QMIso q₁' q₂' where
  φ := G.φ
  ψ := G.ψ
  left := G.left
  right := G.right
  equivariant a := by rw [h₁, h₂]; exact G.equivariant (g0 a)

/-- `Aut(A, ι ∘ α) = Aut(A, ι)`. -/
def autTwistEquiv {A : AbVar K} (q : QMStr A) (α : O ≃+* O) :
    QMIso (q.twist α) (q.twist α) ≃ QMIso q q where
  toFun G := qmCongr G α.symm
    (fun a => by
      show q.iota a = q.iota (α (α.symm a))
      rw [RingEquiv.apply_symm_apply])
    (fun a => by
      show q.iota a = q.iota (α (α.symm a))
      rw [RingEquiv.apply_symm_apply])
  invFun G := qmCongr G α (fun _ => rfl) (fun _ => rfl)
  left_inv G := qmIso_ext rfl
  right_inv G := qmIso_ext rfl

/-- `Iso(q, q') ≃ Aut(q)` once one isomorphism is fixed. -/
def isoEquivAut {A A' : AbVar K} {q : QMStr A} {q' : QMStr A'} (G₀ : QMIso q q') :
    QMIso q q ≃ QMIso q q' where
  toFun G := G.trans G₀
  invFun G := G.trans G₀.symm
  left_inv G := qmIso_ext (by
    show (G.φ.hom ≫ G₀.φ.hom) ≫ G₀.ψ.hom = G.φ.hom
    rw [Category.assoc, G₀.left, Category.comp_id])
  right_inv G := qmIso_ext (by
    show (G.φ.hom ≫ G₀.ψ.hom) ≫ G₀.φ.hom = G.φ.hom
    rw [Category.assoc, G₀.right, Category.comp_id])

/-- An automorphism of a pair with finitely many automorphisms has finite order in `End(A)`. -/
theorem exists_pow_eq_one {A : AbVar K} {q : QMStr A} [Finite (QMIso q q)] (θ : QMIso q q) :
    ∃ m : ℕ, 0 < m ∧ θ.φ ^ m = 1 := by
  let pw : ℕ → QMIso q q := fun n => Nat.rec (QMIso.refl q) (fun _ G => G.trans θ) n
  have hpw : ∀ n, (pw n).φ = θ.φ ^ n := by
    intro n
    induction n with
    | zero => exact AbVar.Hom.ext' rfl
    | succ n ih =>
      apply AbVar.Hom.ext'
      show (pw n).φ.hom ≫ θ.φ.hom = (θ.φ ^ (n + 1)).hom
      rw [pow_succ', end_mul_hom, ih]
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite pw
  have hu : IsUnit θ.φ := by
    refine ⟨⟨θ.φ, θ.ψ, AbVar.Hom.ext' ?_, AbVar.Hom.ext' ?_⟩, rfl⟩
    · show θ.ψ.hom ≫ θ.φ.hom = 𝟙 _
      exact θ.right
    · show θ.φ.hom ≫ θ.ψ.hom = 𝟙 _
      exact θ.left
  have hij' : θ.φ ^ i = θ.φ ^ j := by rw [← hpw, ← hpw, h]
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have : θ.φ ^ i * θ.φ ^ (j - i) = θ.φ ^ i * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, hij']
    exact (hu.pow i).mul_left_cancel this
  · refine ⟨i - j, Nat.sub_pos_of_lt hlt, ?_⟩
    have : θ.φ ^ j * θ.φ ^ (i - j) = θ.φ ^ j * 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hlt.le, mul_one, hij']
    exact (hu.pow j).mul_left_cancel this

end General

/-! ## Level structures on a fixed pair: exactly `72`, indexed by `(𝒪/3𝒪)^×` -/

/-- Residues of nonzero reduced norm mod 3, i.e. `(𝒪/3𝒪)^×` in coordinates. -/
abbrev Good : Type := {c : Fin 4 → ZMod 3 // nrd3 c ≠ 0}

theorem card_good : Fintype.card Good = 72 := by decide +kernel

theorem tbl_unit (c : Good) : nrdC (tbl c.1) * nrdC (tbl c.1) = 1 := by
  rcases (tbl_spec c.1 c.2).2 with h | h <;> rw [h] <;> norm_num

/-- The table unit of `𝒪` reducing to `c`. -/
def uc (c : Good) : Oˣ := unitOf (tbl c.1) (nrdC (tbl c.1)) rfl (tbl_unit c)

theorem uc_congr (c : Good) : ∃ d : O, ((uc c : Oˣ) : O) - liftO c.1 = 3 * d := by
  obtain ⟨hred, -⟩ := tbl_spec c.1 c.2
  have hdvd : ∀ i, (3 : ℤ) ∣ tbl c.1 i - ((c.1 i).val : ℤ) := by
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1
    rw [Int.cast_sub, hred i]
    simp
  refine ⟨⟨ofInt (fun i => (tbl c.1 i - ((c.1 i).val : ℤ)) / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  change ofInt (tbl c.1) - ofInt (fun i => ((c.1 i).val : ℤ)) = ((3 : O) : B) * ofInt _
  rw [h33, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  exact (Int.mul_ediv_cancel' (hdvd i)).symm

theorem liftO_inj3 {c c' : Fin 4 → ZMod 3} (h : ∃ d : O, liftO c - liftO c' = 3 * d) :
    c = c' := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨k, hk⟩ := d.2
  have h3 : ofInt (fun i => ((c i).val : ℤ)) - ofInt (fun i => ((c' i).val : ℤ)) =
      3 * ofInt k := by
    have := congrArg Subtype.val hd
    have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
    simp only [liftO, hk, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33] at this
    exact this
  rw [ofInt_sub, three_mul_ofInt] at h3
  have h4 := ofInt_injective h3
  funext i
  have h5 := congrFun h4 i
  simp only [Pi.sub_apply] at h5
  have h6 : (((c i).val : ℤ) : ZMod 3) - (((c' i).val : ℤ) : ZMod 3) = 0 := by
    rw [← Int.cast_sub, h5]; push_cast
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
  simpa [sub_eq_zero] using h6

theorem sub_liftO_coord (n : Fin 4 → ℤ) (u : O) (hu : (u : B) = ofInt n) :
    ∃ d : O, u - liftO (fun i => (n i : ZMod 3)) = 3 * d := by
  refine ⟨⟨ofInt (fun i => n i / 3), _, rfl⟩, ?_⟩
  apply Subtype.ext
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  simp only [liftO, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, h33]
  rw [hu, ofInt_sub, three_mul_ofInt]
  congr 1
  funext i
  simp only [Pi.sub_apply, ZMod.val_intCast]
  have := Int.emod_def (n i) 3
  omega

/-- An element of `𝒪` invertible mod `3𝒪` has reduced norm `≢ 0 mod 3` (the argument of
`TSHeckeUnits.exists_unit_congr`). -/
theorem nrd3_ne_zero_of_inv (u₀ v₀ : O) (h : ∃ c : O, v₀ * u₀ - 1 = 3 * c) (nu : Fin 4 → ℤ)
    (hnu : (u₀ : B) = ofInt nu) : nrd3 (fun i => (nu i : ZMod 3)) ≠ 0 := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨nv, hnv⟩ := v₀.2
  obtain ⟨nc, hnc⟩ := c.2
  have h33 : ((3 : O) : B) = 3 := map_ofNat O.subtype 3
  have h1 : ((1 : O) : B) = ofInt ![1, 0, 0, 0] := by rw [ofInt_one]; rfl
  have hcoord : mulCoord nv nu - ![1, 0, 0, 0] = fun i => 3 * nc i := by
    apply ofInt_injective
    rw [← ofInt_sub, ← ofInt_mul, ← three_mul_ofInt, ← hnu, ← hnv, ← hnc, ← h1, ← h33]
    exact congrArg Subtype.val hc
  have hn1 : ((nrdC (mulCoord nv nu) : ℤ) : ZMod 3) = 1 := by
    have : mulCoord nv nu = fun i => ![1, 0, 0, 0] i + 3 * nc i := by
      funext i
      have := congrFun hcoord i
      simp only [Pi.sub_apply] at this
      linarith
    rw [this, nrdC_cast]
    simp only [nrd3]
    simp [show (3 : ZMod 3) = 0 from rfl]
  intro h0
  rw [nrdC_mul, Int.cast_mul, nrdC_cast nu, h0, mul_zero] at hn1
  exact zero_ne_one hn1

/-- The level structure `η ∘ (· u_c)` on the pair of `P`. -/
def lv (P : QML3 Qbar) (c : Good) : Level3 P.q := P.e.rightMul (uc c)

theorem lv_eta (P : QML3 Qbar) (c : Good) (a : O) :
    (lv P c).eta a = P.e.eta (a * ((uc c : Oˣ) : O)) := rfl

theorem lv_injective (P : QML3 Qbar) : Function.Injective (lv P) := by
  intro c c' h
  have h1 : P.e.eta (1 * ((uc c : Oˣ) : O)) = P.e.eta (1 * ((uc c' : Oˣ) : O)) := by
    rw [← lv_eta, ← lv_eta, h]
  rw [_root_.one_mul, _root_.one_mul, P.e.eq_iff] at h1
  obtain ⟨d, hd⟩ := h1
  obtain ⟨d1, h1'⟩ := uc_congr c
  obtain ⟨d2, h2'⟩ := uc_congr c'
  apply Subtype.ext
  apply liftO_inj3
  refine ⟨d - d1 + d2, ?_⟩
  rw [mul_add, mul_sub, ← hd, ← h1', ← h2']
  abel

theorem lv_surjective (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar) :
    Function.Surjective (lv P) := by
  intro et
  obtain ⟨u₀, v₀, hinv, hu⟩ := Level3.torsor hT P et
  obtain ⟨nu, hnu⟩ := u₀.2
  have hgood := nrd3_ne_zero_of_inv u₀ v₀ hinv nu hnu
  obtain ⟨d, hd⟩ := sub_liftO_coord nu u₀ hnu
  refine ⟨⟨_, hgood⟩, Level3.ext' (AddMonoidHom.ext fun a => ?_)⟩
  rw [lv_eta, hu a, P.e.eq_iff]
  obtain ⟨d1, h1⟩ := uc_congr ⟨_, hgood⟩
  refine ⟨a * d1 - a * d, ?_⟩
  calc a * ((uc ⟨_, hgood⟩ : Oˣ) : O) - a * u₀
      = a * (((uc ⟨_, hgood⟩ : Oˣ) : O) - liftO (fun i => (nu i : ZMod 3))) -
        a * (u₀ - liftO (fun i => (nu i : ZMod 3))) := by noncomm_ring
    _ = a * (3 * d1) - a * (3 * d) := by rw [h1, hd]
    _ = 3 * (a * d1 - a * d) := by noncomm_ring

/-- **The level structures on a fixed pair over `ℚ̄`: `72` of them** (given `TorsionStructure`). -/
def lvEquiv (hT : ObjBridge.TorsionStructure) (P : QML3 Qbar) : Good ≃ Level3 P.q :=
  Equiv.ofBijective (lv P) ⟨lv_injective P, lv_surjective hT P⟩

/-! ## The twisted pairs `ι ∘ t_k` and their composition law -/

/-- `t_k ∘ t_l = t_{k ⊕ l}` (the group `W = (ℤ/2)²`). -/
def xr (k l : Fin 4) : Fin 4 := ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] k l

theorem xr_xr_left (k l : Fin 4) : xr k (xr k l) = l := by revert k l; decide
theorem xr_xr_right (k l : Fin 4) : xr (xr k l) l = k := by revert k l; decide
theorem xr_self (l : Fin 4) : xr l l = 0 := by revert l; decide

/-- The values `1, i, j, k` of the representatives `tt`. -/
def ttv : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

theorem tt_val (k : Fin 4) : ((tt k : Bˣ) : B) = ttv k := by
  fin_cases k
  · ext <;> simp [tt, ttv]
  · change ofInt ei = _
    ext <;> simp [ofInt, ei, ttv]
  · change ofInt ej = _
    ext <;> simp [ofInt, ej, ttv]
  · change ofInt ei * ofInt ej = _
    ext <;> simp [ofInt, ei, ej, ttv]

theorem ttv_mul : ∀ k l : Fin 4, ∃ c : ℚ, c ≠ 0 ∧ ttv k * ttv l = algebraMap ℚ B c * ttv (xr k l)
  | 0, 0 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 0, 1 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 0, 2 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 0, 3 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 1, 0 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 1, 1 => ⟨2, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 1, 2 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 1, 3 => ⟨2, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 2, 0 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 2, 1 => ⟨-1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 2, 2 => ⟨-3, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 2, 3 => ⟨3, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 3, 0 => ⟨1, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 3, 1 => ⟨-2, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 3, 2 => ⟨-3, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩
  | 3, 3 => ⟨6, by norm_num, by ext <;> simp [ttv, xr, QuaternionAlgebra.re_ofNat, QuaternionAlgebra.imI_ofNat, QuaternionAlgebra.imJ_ofNat, QuaternionAlgebra.imK_ofNat] <;> norm_num⟩

theorem tt_mul (k l : Fin 4) : ∃ c : ℚ, c ≠ 0 ∧
    ((tt k : Bˣ) : B) * ((tt l : Bˣ) : B) = algebraMap ℚ B c * ((tt (xr k l) : Bˣ) : B) := by
  rw [tt_val, tt_val, tt_val]
  exact ttv_mul k l

theorem conj_conj (u v w : Bˣ) (c : ℚ) (hc : c ≠ 0)
    (h : (u : B) * (v : B) = algebraMap ℚ B c * (w : B)) (a : B) :
    (u : B) * ((v : B) * a * ((v⁻¹ : Bˣ) : B)) * ((u⁻¹ : Bˣ) : B) =
      (w : B) * a * ((w⁻¹ : Bˣ) : B) := by
  have hC'C : algebraMap ℚ B c⁻¹ * algebraMap ℚ B c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  set x := (u : B) * ((v : B) * a * ((v⁻¹ : Bˣ) : B)) * ((u⁻¹ : Bˣ) : B) with hx
  have h1 : x * ((u : B) * (v : B)) = ((u : B) * (v : B)) * a := by
    simp only [hx, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
  rw [h] at h1
  have h2 : algebraMap ℚ B c * (x * w) = algebraMap ℚ B c * ((w : B) * a) := by
    rw [← mul_assoc, Algebra.commutes, mul_assoc, h1, mul_assoc]
  have h3 : x * w = (w : B) * a := by
    have := congrArg (fun y => algebraMap ℚ B c⁻¹ * y) h2
    simp only [← mul_assoc, hC'C, one_mul] at this
    exact this
  calc x = x * (w : B) * ((w⁻¹ : Bˣ) : B) := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = (w : B) * a * ((w⁻¹ : Bˣ) : B) := by rw [h3]

theorem rep_rep (k l : Fin 4) (a : O) : rep k (rep l a) = rep (xr k l) a := by
  obtain ⟨c, hc, h⟩ := tt_mul k l
  apply Subtype.ext
  simp only [rep, conjO_apply]
  exact conj_conj _ _ _ c hc h a

theorem rep_zero (a : O) : rep 0 a = a := by
  apply Subtype.ext
  simp only [rep, conjO_apply]
  simp [tt]

/-! ## The count -/

section Count

variable (P : QML3 Qbar)

/-- The object `(A, ι ∘ t_k, η ∘ t_k)`. -/
abbrev Pk (k : Fin 4) : QML3 Qbar := P.twist (rep k)

/-- `(k, c) ↦` the class of `(A, ι ∘ t_k, et_k ∘ (· u_c))`. -/
def Ψ (x : Fin 4 × Good) : M3 Qbar :=
  M3.mk ⟨P.A, P.surface, (Pk P x.1).q, lv (Pk P x.1) x.2⟩

/-- `Rk k l`: the pairs `ι ∘ t_k` and `ι ∘ t_l` are isomorphic. -/
def Rk (k l : Fin 4) : Prop := Nonempty (QMIso (Pk P k).q (Pk P l).q)

/-- `a = |Aut(A, ι)|`. -/
def aP : ℕ := Nat.card (QMIso P.q P.q)

/-- `s = #{m | (A, ι ∘ t_m) ≅ (A, ι)}`. -/
def sP : ℕ := (Finset.univ.filter fun m : Fin 4 => Nonempty (QMIso (P.q.twist (rep m)) P.q)).card

theorem range_Ψ (hT : ObjBridge.TorsionStructure) : Set.range (Ψ P) = twistFibre P := by
  ext c
  constructor
  · rintro ⟨⟨k, d⟩, rfl⟩
    exact ⟨⟨P.A, P.surface, (Pk P k).q, lv (Pk P k) d⟩, rfl, rep k, ⟨QMIso.refl _⟩⟩
  · rintro ⟨Q, rfl, α, ⟨g⟩⟩
    obtain ⟨k, v, hv⟩ := rep_cover α
    let G : QMIso (Pk P k).q Q.q := (innerIso P.q (rep k) α v hv).symm.trans g
    obtain ⟨d, hd⟩ := lv_surjective hT (Pk P k) (pullLevel G Q.e)
    refine ⟨(k, d), ?_⟩
    exact (congrArg (fun e : Level3 (Pk P k).q =>
      M3.mk (⟨P.A, P.surface, (Pk P k).q, e⟩ : QML3 Qbar)) hd).trans
      (Quotient.sound ⟨pullIso P.surface Q.surface G Q.e⟩)

theorem rk_iff (k l : Fin 4) :
    Rk P k l ↔ Nonempty (QMIso (P.q.twist (rep (xr k l))) P.q) := by
  constructor
  · rintro ⟨G⟩
    refine ⟨qmCongr G (rep l) (fun a => ?_) (fun a => ?_)⟩
    · show P.q.iota (rep (xr k l) a) = P.q.iota (rep k (rep l a))
      rw [rep_rep]
    · show P.q.iota a = P.q.iota (rep l (rep l a))
      rw [rep_rep, xr_self, rep_zero]
  · rintro ⟨G⟩
    refine ⟨qmCongr G (rep l) (fun a => ?_) (fun _ => rfl)⟩
    show P.q.iota (rep k a) = P.q.iota (rep (xr k l) (rep l a))
    rw [rep_rep, xr_xr_right]

theorem card_rk (k : Fin 4) : (Finset.univ.filter (Rk P k)).card = sP P := by
  apply Finset.card_nbij' (xr k) (xr k)
  · intro l hl
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl ⊢
    exact (rk_iff P k l).1 hl
  · intro m hm
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm ⊢
    rw [rk_iff, xr_xr_left]
    exact hm
  · intro l _
    exact xr_xr_left k l
  · intro m _
    exact xr_xr_left k m

theorem finite_aut_k (hfin : Finite (QMIso P.q P.q)) (k : Fin 4) :
    Finite (QMIso (Pk P k).q (Pk P k).q) :=
  Finite.of_equiv _ (autTwistEquiv P.q (rep k)).symm

theorem card_iso (k l : Fin 4) :
    Nat.card (QMIso (Pk P k).q (Pk P l).q) = if Rk P k l then aP P else 0 := by
  split_ifs with h
  · obtain ⟨G₀⟩ := h
    exact (Nat.card_congr (isoEquivAut G₀)).symm.trans (Nat.card_congr (autTwistEquiv P.q (rep k)))
  · haveI : IsEmpty (QMIso (Pk P k).q (Pk P l).q) := ⟨fun G => h ⟨G⟩⟩
    exact Nat.card_of_isEmpty

theorem finite_iso (hfin : Finite (QMIso P.q P.q)) (k l : Fin 4) :
    Finite (QMIso (Pk P k).q (Pk P l).q) := by
  by_cases h : Rk P k l
  · obtain ⟨G₀⟩ := h
    haveI := finite_aut_k P hfin k
    exact Finite.of_equiv _ (isoEquivAut G₀)
  · haveI : IsEmpty (QMIso (Pk P k).q (Pk P l).q) := ⟨fun G => h ⟨G⟩⟩
    infer_instance

/-- Push a level structure forward along a QM isomorphism. -/
def push {A : AbVar Qbar} {q₁ q₂ : QMStr A} (φ : QMIso q₁ q₂) (et : Level3 q₁) : Level3 q₂ :=
  pullLevel φ.symm et

theorem push_eta {A : AbVar Qbar} {q₁ q₂ : QMStr A} (φ : QMIso q₁ q₂) (et : Level3 q₁) (a : O) :
    (push φ et).eta a = Additive.ofMul (Additive.toMul (et.eta a) ≫ φ.φ.hom) := rfl

/-- **Freeness (Serre's lemma)**: distinct isomorphisms push a level structure to distinct
level structures. -/
theorem push_injective (hT : ObjBridge.TorsionStructure) (hS : SerreRigidity3) (X : QML3 Qbar)
    [Finite (QMIso X.q X.q)] {q₂ : QMStr X.A} (φ φ' : QMIso X.q q₂)
    (h : push φ X.e = push φ' X.e) : φ = φ' := by
  let θ : QMIso X.q X.q := φ.trans φ'.symm
  have hθ : θ.φ.hom = φ.φ.hom ≫ φ'.ψ.hom := rfl
  have hfix : ∀ a, Additive.toMul (X.e.eta a) ≫ θ.φ.hom = Additive.toMul (X.e.eta a) := by
    intro a
    have h1 : Additive.toMul (X.e.eta a) ≫ φ.φ.hom = Additive.toMul (X.e.eta a) ≫ φ'.φ.hom := by
      have := congrArg (fun e : Level3 q₂ => Additive.toMul (e.eta a)) h
      exact this
    rw [hθ, ← Category.assoc, h1, Category.assoc, φ'.left, Category.comp_id]
  have htors : ∀ x : X.A.Pt Qbar, x ^ 3 = 1 → x ≫ θ.φ.hom = x := by
    intro x hx
    have hx' : LeafQM.AV.bcPt X.A x ^ 3 = 1 := by
      rw [LeafQM.AV.bcPt, ← MonObj.comp_pow, hx]
      exact MonObj.comp_one _
    obtain ⟨a, ha⟩ := Level3.onto hT X (LeafQM.AV.bcPt X.A x) hx'
    have := bcPt_injective X.A ha
    rw [← this]
    exact hfix a
  have h1 : θ.φ = 1 := hS X.A θ.φ (exists_pow_eq_one θ) htors
  have h2 : φ.φ.hom ≫ φ'.ψ.hom = 𝟙 _ := by
    rw [← hθ, h1]; rfl
  apply qmIso_ext
  calc φ.φ.hom = φ.φ.hom ≫ φ'.ψ.hom ≫ φ'.φ.hom := by rw [φ'.right, Category.comp_id]
    _ = φ'.φ.hom := by rw [← Category.assoc, h2, Category.id_comp]

/-- **The fibre of `Ψ` through `(k, c)` has `s · a` elements.** -/
theorem fibre_card (hT : ObjBridge.TorsionStructure) (hS : SerreRigidity3)
    (hfin : Finite (QMIso P.q P.q)) (x : Fin 4 × Good) :
    Nat.card {y : Fin 4 × Good // Ψ P y = Ψ P x} = sP P * aP P := by
  obtain ⟨k, c⟩ := x
  let et : Level3 (Pk P k).q := lv (Pk P k) c
  let X : QML3 Qbar := ⟨P.A, P.surface, (Pk P k).q, et⟩
  haveI : Finite (QMIso X.q X.q) := finite_aut_k P hfin k
  haveI : ∀ l, Finite (QMIso (Pk P k).q (Pk P l).q) := finite_iso P hfin k
  let f : (Σ l : Fin 4, QMIso (Pk P k).q (Pk P l).q) → {y : Fin 4 × Good // Ψ P y = Ψ P (k, c)} :=
    fun z => ⟨(z.1, (lvEquiv hT (Pk P z.1)).symm (push z.2 et)), by
      have : lv (Pk P z.1) ((lvEquiv hT (Pk P z.1)).symm (push z.2 et)) = push z.2 et :=
        (lvEquiv hT (Pk P z.1)).apply_symm_apply _
      exact (congrArg (fun e : Level3 (Pk P z.1).q =>
        M3.mk (⟨P.A, P.surface, (Pk P z.1).q, e⟩ : QML3 Qbar)) this).trans
        (Quotient.sound ⟨pullIso P.surface P.surface z.2.symm et⟩)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨l, φ⟩ ⟨l', φ'⟩ hz
      have h1 := congrArg (fun y => y.1.1) hz
      simp only [f] at h1
      subst h1
      have h2 := congrArg (fun y => y.1.2) hz
      simp only [f] at h2
      have h3 : push φ et = push φ' et := (lvEquiv hT (Pk P l)).symm.injective h2
      have := push_injective hT hS X φ φ' h3
      subst this
      rfl
    · rintro ⟨⟨l, d⟩, hy⟩
      have hy' : Quotient.mk (isoSetoid Qbar)
          (⟨P.A, P.surface, (Pk P l).q, lv (Pk P l) d⟩ : QML3 Qbar) =
          Quotient.mk (isoSetoid Qbar) X := hy
      have hI : Nonempty (QML3.Iso (⟨P.A, P.surface, (Pk P l).q, lv (Pk P l) d⟩ : QML3 Qbar) X) :=
        Quotient.exact hy'
      obtain ⟨I⟩ := hI
      let J := I.symm
      let φ : QMIso (Pk P k).q (Pk P l).q := ⟨J.φ, J.ψ, J.left, J.right, J.equivariant⟩
      refine ⟨⟨l, φ⟩, Subtype.ext ?_⟩
      show (l, (lvEquiv hT (Pk P l)).symm (push φ et)) = (l, d)
      congr 1
      rw [Equiv.symm_apply_eq]
      apply Level3.ext'
      apply AddMonoidHom.ext
      intro a
      exact J.level a
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_sigma]
  simp only [card_iso]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, card_rk]

/-- **The count**: `#(twist fibre) · s · a = 4 · 72 = 288`. -/
theorem ncard_mul (hT : ObjBridge.TorsionStructure) (hS : SerreRigidity3)
    (hfin : Finite (QMIso P.q P.q)) :
    (twistFibre P).ncard * (sP P * aP P) = 288 := by
  have hcard : (Finset.univ : Finset (Fin 4 × Good)).card = 288 := by
    rw [Finset.card_univ, Fintype.card_prod, card_good, Fintype.card_fin]
  have hsum := Finset.card_eq_sum_card_image (Ψ P) (Finset.univ : Finset (Fin 4 × Good))
  have hterm : ∀ y ∈ (Finset.univ : Finset (Fin 4 × Good)).image (Ψ P),
      (Finset.univ.filter (fun z => Ψ P z = y)).card = sP P * aP P := by
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hy
    rw [← fibre_card P hT hS hfin x, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hcard] at hsum
  have himg : twistFibre P = ↑((Finset.univ : Finset (Fin 4 × Good)).image (Ψ P)) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, range_Ψ P hT]
  rw [himg, Set.ncard_coe_finset]
  exact hsum.symm

end Count

/-! ## `HeckeFibreSizes` -/

theorem sP_pos (P : QML3 Qbar) : 1 ≤ sP P := by
  apply Finset.card_pos.2
  refine ⟨0, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨qmCongr (QMIso.refl P.q) id
    (fun a => ?_) (fun _ => rfl)⟩⟩⟩
  show P.q.iota (rep 0 a) = P.q.iota a
  rw [rep_zero]

theorem sP_le (P : QML3 Qbar) (m₀ : Fin 4)
    (h : ∀ m : Fin 4, m ≠ 0 → m ≠ m₀ → Nonempty (QMIso (P.q.twist (rep m)) P.q) → False) :
    sP P ≤ 2 := by
  calc sP P ≤ ({0, m₀} : Finset (Fin 4)).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter] at hm
        by_cases h0 : m = 0
        · simp [h0]
        by_cases h1 : m = m₀
        · simp [h1]
        exact (h m h0 h1 hm.2).elim
    _ ≤ 2 := Finset.card_le_two

theorem sP_eq_one (P : QML3 Qbar)
    (h : ∀ m : Fin 4, m ≠ 0 → Nonempty (QMIso (P.q.twist (rep m)) P.q) → False) :
    sP P = 1 := by
  apply le_antisymm _ (sP_pos P)
  calc sP P ≤ ({0} : Finset (Fin 4)).card := by
        apply Finset.card_le_card
        intro m hm
        rw [Finset.mem_filter] at hm
        by_cases h0 : m = 0
        · simp [h0]
        exact (h m h0 hm.2).elim
    _ = 1 := Finset.card_singleton _

/-- hecke-rest's statement of `HeckeFibreSizes` (ts-hecke's text before 8015f0d6, verbatim; it has the extra first
clause). -/
def HeckeFibreSizesHR : Prop :=
  ∃ M : ℕ, (∀ P : QML3 Qbar, (twistFibre P).ncard ≤ M) ∧
    (∀ P : QML3 Qbar, ¬ HasCM4 P.q → ¬ HasCM3 P.q → ¬ HasCM24 P.q →
      (twistFibre P).ncard = M) ∧
    (∀ P : QML3 Qbar, HasCM4 P.q → M ∣ 4 * (twistFibre P).ncard) ∧
    (∀ P : QML3 Qbar, HasCM3 P.q → M ∣ 6 * (twistFibre P).ncard) ∧
    (∀ P : QML3 Qbar, HasCM24 P.q → M ∣ 2 * (twistFibre P).ncard)

/-- **`HeckeFibreSizes` from the leaves** `QMAutCard`, `SerreRigidity3`, `ALFixedPoints` and the
kernel's `TorsionStructure` (with `M = 144`). -/
theorem heckeFibreSizes_of (hT : ObjBridge.TorsionStructure) (hA : QMAutCard)
    (hS : SerreRigidity3) (hW : ALFixedPoints) : HeckeFibreSizesHR := by
  have key : ∀ P : QML3 Qbar, (twistFibre P).ncard * (sP P * aP P) = 288 ∧
      aP P = (if HasCM4 P.q then 4 else if HasCM3 P.q then 6 else 2) ∧
      ¬ (HasCM4 P.q ∧ HasCM3 P.q) ∧ ¬ (HasCM4 P.q ∧ HasCM24 P.q) ∧
      ¬ (HasCM3 P.q ∧ HasCM24 P.q) := by
    intro P
    obtain ⟨ha, hx⟩ := hA P.A P.surface P.q
    have hpos : 0 < Nat.card (QMIso P.q P.q) := by
      rw [ha]; split_ifs <;> norm_num
    haveI : Finite (QMIso P.q P.q) := (Nat.card_pos_iff.1 hpos).2
    exact ⟨ncard_mul P hT hS inferInstance, ha, hx⟩
  have hAL := fun P : QML3 Qbar => hW P.A P.surface P.q
  refine ⟨144, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    obtain ⟨h, ha, -⟩ := key P
    have hs := sP_pos P
    have ha2 : 2 ≤ aP P := by rw [ha]; split_ifs <;> norm_num
    have : 2 ≤ sP P * aP P := le_trans ha2 (Nat.le_mul_of_pos_left _ hs)
    nlinarith
  · intro P h4 h3 h24
    obtain ⟨h, ha, -⟩ := key P
    rw [if_neg h4, if_neg h3] at ha
    have hs : sP P = 1 := sP_eq_one P (fun m hm hI => by
      obtain ⟨w1, w2, w3⟩ := hAL P
      fin_cases m
      · exact hm rfl
      · exact h4 (w1 hI)
      · exact h3 (w2 hI)
      · exact h24 (w3 hI))
    rw [hs, ha] at h
    omega
  · intro P h4
    obtain ⟨h, ha, -, x2, -⟩ := key P
    rw [if_pos h4] at ha
    have hs := sP_pos P
    have hs2 : sP P ≤ 2 := sP_le P 1 (fun m hm hm1 hI => by
      obtain ⟨w1, w2, w3⟩ := hAL P
      fin_cases m
      · exact hm rfl
      · exact hm1 rfl
      · exact (key P).2.2.1 ⟨h4, w2 hI⟩
      · exact x2 ⟨h4, w3 hI⟩)
    rw [ha] at h
    interval_cases (sP P) <;> omega
  · intro P h3
    obtain ⟨h, ha, x1, -, x3⟩ := key P
    rw [if_neg (fun h4 => x1 ⟨h4, h3⟩), if_pos h3] at ha
    have hs := sP_pos P
    have hs2 : sP P ≤ 2 := sP_le P 2 (fun m hm hm2 hI => by
      obtain ⟨w1, w2, w3⟩ := hAL P
      fin_cases m
      · exact hm rfl
      · exact x1 ⟨w1 hI, h3⟩
      · exact hm2 rfl
      · exact x3 ⟨h3, w3 hI⟩)
    rw [ha] at h
    interval_cases (sP P) <;> omega
  · intro P h24
    obtain ⟨h, ha, -, x2, x3⟩ := key P
    rw [if_neg (fun h4 => x2 ⟨h4, h24⟩), if_neg (fun h3 => x3 ⟨h3, h24⟩)] at ha
    have hs := sP_pos P
    have hs2 : sP P ≤ 2 := sP_le P 3 (fun m hm hm3 hI => by
      obtain ⟨w1, w2, w3⟩ := hAL P
      fin_cases m
      · exact hm rfl
      · exact x2 ⟨w1 hI, h24⟩
      · exact x3 ⟨w2 hI, h24⟩
      · exact hm3 rfl)
    rw [ha] at h
    interval_cases (sP P) <;> omega

/-- ts-hecke's current `HeckeFibreSizes` from hecke-rest's stronger statement (drop its first clause). -/
theorem heckeFibreSizes_of' (hT : ObjBridge.TorsionStructure) (hA : QMAutCard)
    (hS : SerreRigidity3) (hW : ALFixedPoints) : HeckeFibreSizes :=
  let ⟨M, _, h1, h2, h3, h4⟩ := heckeFibreSizes_of hT hA hS hW
  ⟨M, h1, h2, h3, h4⟩

end HeckeRest

end


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 2: `HeckeNoVertRam` reduced to one unramified vertical prime

`NoVerticalRam E p` asks every prime of `B = ` (integral closure of `ℤ[X]` in `E`) over `p ℤ[X]`
to have ramification index `1`. For `E/ℚ(X)` Galois, `Gal(E/ℚ(X))` acts on `B` and permutes the
primes over `p ℤ[X]` transitively, preserving ramification indices; so one such prime with
`e = 1` suffices (`noVerticalRam_of_witness`, compiled). What is left (`HeckeVertWitness`) is the
existence, for the Hecke cover and `p > 324`, of one vertical prime with `e = 1`: the valuation
of `E` at the generic point of a component of the special fibre of a smooth model of `Y₃` over
`ℤ_(p)` (good reduction, Morita; see docs/research/hecke-rest.md §3).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestNV

open Polynomial G0ModField PropTSRed PropTSGlue
open CategoryTheory AlgebraicGeometry Limits LeafQM.AV

/-! ## Galois transitivity on the primes of an integral closure -/

section Generic

variable {A F E : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field F] [Algebra A F] [IsFractionRing A F]
  [Field E] [Algebra F E] [Algebra A E] [IsScalarTower A F E] [FiniteDimensional F E]
  [IsGalois F E]

include F in
/-- **Primes of the integral closure over the same prime have the same ramification index**
(Galois case; `A` an integrally closed domain, not necessarily Dedekind). -/
theorem ramIdx_eq_of_under_eq (Q₀ Q : Ideal (integralClosure A E)) [Q₀.IsPrime] [Q.IsPrime]
    (h : Q₀.under A = Q.under A) : Q.ramificationIdx A = Q₀.ramificationIdx A := by
  have hinjAE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A F E]
    exact (algebraMap F E).injective.comp (IsFractionRing.injective A F)
  haveI : Module.IsTorsionFree A E := Module.isTorsionFree_iff_algebraMap_injective.2 hinjAE
  haveI : IsFractionRing (integralClosure A E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension A F E _
  haveI : SMulCommClass Gal(E/F) A E := ⟨fun g a x => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul,
      IsScalarTower.algebraMap_apply A F E, AlgEquiv.commutes]⟩
  haveI : IsGaloisGroup Gal(E/F) A (integralClosure A E) :=
    IsGaloisGroup.of_isFractionRing Gal(E/F) A (integralClosure A E) F E
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq A (integralClosure A E) Gal(E/F) Q₀ Q h
  rw [hg, Ideal.ramificationIdx_smul]

end Generic

/-! ## `ℚ(X)` is the fraction field of `ℤ[X]` -/

/-- `ℤ[X] → ℚ(X)` through `ℚ[X]`. -/
@[reducible] def intRatAlg : Algebra ℤ[X] (RatFunc ℚ) :=
  ((algebraMap ℚ[X] (RatFunc ℚ)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ))).toAlgebra

theorem isFractionRing_int : letI := intRatAlg; IsFractionRing ℤ[X] (RatFunc ℚ) := by
  letI := intRatAlg
  have e : ∀ g : ℤ[X], algebraMap ℤ[X] (RatFunc ℚ) g =
      algebraMap ℚ[X] (RatFunc ℚ) (g.map (Int.castRingHom ℚ)) := fun g => rfl
  have hinj : Function.Injective (algebraMap ℤ[X] (RatFunc ℚ)) := by
    intro a b hab
    rw [e, e] at hab
    exact Polynomial.map_injective _ Int.cast_injective (IsFractionRing.injective ℚ[X] _ hab)
  haveI : FaithfulSMul ℤ[X] (RatFunc ℚ) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  refine IsFractionRing.of_field ℤ[X] (RatFunc ℚ) fun z => ?_
  obtain ⟨bN, hbNm, hN⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (RatFunc.num z)
  obtain ⟨bD, hbDm, hD⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (RatFunc.denom z)
  set gN := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (RatFunc.num z)
  set gD := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (RatFunc.denom z)
  have hbN : (bN : ℚ) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hbNm)
  have hbD : (bD : ℚ) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hbDm)
  have hmapN : gN.map (Int.castRingHom ℚ) = C (bN : ℚ) * RatFunc.num z := by
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hN, zsmul_eq_mul]
    simp
  have hmapD : gD.map (Int.castRingHom ℚ) = C (bD : ℚ) * RatFunc.denom z := by
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hD, zsmul_eq_mul]
    simp
  refine ⟨C bD * gN, C bN * gD, ?_⟩
  rw [e, e, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C, hmapN,
    hmapD]
  set c : RatFunc ℚ := algebraMap ℚ[X] (RatFunc ℚ) (C (bD : ℚ) * C (bN : ℚ))
  have hc : c ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] _), ← C_mul, C_eq_zero]
    exact mul_ne_zero hbD hbN
  have h1 : algebraMap ℚ[X] (RatFunc ℚ)
      (C ((Int.castRingHom ℚ) bD) * (C (bN : ℚ) * RatFunc.num z)) =
      c * algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.num z) := by
    rw [← map_mul]; congr 1; simp only [eq_intCast]; ring
  have h2 : algebraMap ℚ[X] (RatFunc ℚ)
      (C ((Int.castRingHom ℚ) bN) * (C (bD : ℚ) * RatFunc.denom z)) =
      c * algebraMap ℚ[X] (RatFunc ℚ) (RatFunc.denom z) := by
    rw [← map_mul]; congr 1; simp only [eq_intCast]; ring
  rw [h1, h2, mul_div_mul_left _ _ hc, RatFunc.num_div_denom]

/-! ## The reduction -/

/-- **Glue (arithmetic input of Lemma NV / good reduction): one unramified vertical prime.**
Some prime of the integral closure of `ℤ[X]` in `E` over `p ℤ[X]` has ramification index `1`. -/
def VertUnramWitness (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∃ Q : Ideal (integralClosure ℤ[X] E), Q.IsPrime ∧ Q.under ℤ[X] = vertPrime p ∧
    Q.ramificationIdx ℤ[X] = 1

/-- **One unramified vertical prime gives no vertical ramification** (Galois case; compiled). -/
theorem noVerticalRam_of_witness (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
    [IsGalois (RatFunc ℚ) E] (p : ℕ) (h : VertUnramWitness E p) : NoVerticalRam E p := by
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  haveI := isFractionRing_int
  obtain ⟨Q₀, hQ₀, hu₀, he₀⟩ := h
  intro Q hQ hu
  rw [ramIdx_eq_of_under_eq (F := RatFunc ℚ) Q₀ Q (hu₀.trans hu.symm), he₀]

/-- **Glue (h-b1 §3 Lemma NV, or good reduction of `Y₃` at `p ∤ 6`): one unramified vertical
prime for the Hecke cover.** For a triple with R1fp, R1hecke, R2fp and any `E` carrying the
normalization chart, for every prime `p > 324` some prime of the integral closure of `ℤ[X]` in
`E` over `p ℤ[X]` is unramified. *Route GR* (STANDARD inputs, locators UNVERIFIED): `Y₃` has a
smooth proper model `𝒴` over `ℤ_(p)` (Morita 1981; Carayol 1986); `π` is regular at the generic
point `ξ` of a component of the special fibre with nonconstant reduction (the tame quotient of
`𝒴` by `Γ'` is `P¹_{ℤ_(p)}` in the coordinate `j`); the local ring `𝒪_{𝒴,ξ}` is a DVR of
`E = ℚ(Y₃)` with uniformizer `p` (reduced special fibre) containing `ℤ[X]`, so its centre on the
integral closure is a vertical prime with `e = 1`. *Route NV*: h-b1 §3 (tameness, unramified
branch fibres, Abhyankar at `(p, X − b)`, the `W`-quotient). Glue, not a leaf. -/
def HeckeVertWitness : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∀ p : ℕ, p.Prime → 324 < p → VertUnramWitness E p

/-- **`HeckeNoVertRam` from one unramified vertical prime** (compiled). -/
theorem heckeNoVertRam_of_witness (h : HeckeVertWitness) : HeckeNoVertRam := by
  intro Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324
  exact noVerticalRam_of_witness E p (h Y Φ π h1 hh h2 E hN p hp hp324)

/-! ## A local-ring witness suffices (commutative algebra, compiled)

If a ring map `ψ : B → R` to a local ring has `ψ⁻¹(𝔪_R) = Q` over `p ℤ[X]` and `ψ(p) ∉ 𝔪_R²`, then
`e(Q) = 1`. Here `B = ` the integral closure of `ℤ[X]` in `E`, which is Noetherian and normal, so
`B_Q` is a DVR (`Q` has height one over the height-one `p ℤ[X]`), and `p` is a uniformizer of `B_Q`
since its image avoids `𝔪_R²`. This is the shape of the good-reduction input: `R` is the local ring
of a smooth model at the generic point of a component of the special fibre. -/

/-- A nonzero prime of `ℤ[X]` inside `p ℤ[X]` is `p ℤ[X]` (`ℤ[X]` is a UFD, `p` is prime). -/
theorem eq_vertPrime {p : ℕ} (hp : p.Prime) (I : Ideal ℤ[X]) [hI : I.IsPrime] (h0 : I ≠ ⊥)
    (hle : I ≤ vertPrime p) : I = vertPrime p := by
  have hv : vertPrime p = Ideal.span {C (p : ℤ)} := by
    rw [vertPrime, Ideal.map_span, Set.image_singleton]
  have hCp : Prime (C (p : ℤ)) := Polynomial.prime_C_iff.2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨r, hrI, hr⟩ := hI.exists_mem_prime_of_ne_bot h0
  have hdvd : C (p : ℤ) ∣ r := by
    rw [hv] at hle
    exact Ideal.mem_span_singleton.1 (hle hrI)
  obtain ⟨u, hu⟩ := hdvd
  have hunit : IsUnit u := by
    rcases hr.irreducible.isUnit_or_isUnit hu with h | h
    · exact absurd h hCp.not_unit
    · exact h
  apply le_antisymm hle
  rw [hv, Ideal.span_le, Set.singleton_subset_iff]
  have : C (p : ℤ) = r * ↑hunit.unit⁻¹ := by
    rw [hu, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [SetLike.mem_coe, this]
  exact I.mul_mem_right _ hrI

/-- **Glue (good-reduction input, local form): a local-ring witness.** A prime `Q` of the integral
closure of `ℤ[X]` in `E` over `p ℤ[X]`, cut out by a ring map `ψ` to a local ring `R` with
`ψ(p) ∉ 𝔪_R²` (e.g. `R` the local ring at the generic point of a component of the special fibre of a
smooth model, `p` a uniformizer there). Glue, not a leaf. -/
def VertLocalWitness (E : Type) [Field E] [Algebra ℚ[X] E] (p : ℕ) : Prop :=
  letI := intPolyAlg E
  ∃ (Q : Ideal (integralClosure ℤ[X] E)) (R : Type) (_ : CommRing R) (_ : IsLocalRing R)
    (ψ : integralClosure ℤ[X] E →+* R),
    Q = (IsLocalRing.maximalIdeal R).comap ψ ∧ Q.under ℤ[X] = vertPrime p ∧
    ψ (algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ))) ∉ (IsLocalRing.maximalIdeal R) ^ 2

/-- **A local-ring witness gives an unramified vertical prime** (compiled). -/
theorem vertUnramWitness_of_local (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
    [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E] (p : ℕ) (hp : p.Prime)
    (h : VertLocalWitness E p) : VertUnramWitness E p := by
  letI := intPolyAlg E
  letI := intRatAlg
  haveI : IsScalarTower ℤ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq (fun a => by
    show algebraMap ℚ[X] E (a.map (Int.castRingHom ℚ)) =
      algebraMap (RatFunc ℚ) E (algebraMap ℚ[X] (RatFunc ℚ) (a.map (Int.castRingHom ℚ)))
    rw [IsScalarTower.algebraMap_apply ℚ[X] (RatFunc ℚ) E])
  haveI := isFractionRing_int
  obtain ⟨Q, R, _, _, ψ, hQ, hQu, hψ⟩ := h
  haveI hQp : Q.IsPrime := by rw [hQ]; exact Ideal.comap_isPrime _ _
  refine ⟨Q, hQp, hQu, ?_⟩
  -- `B` is Noetherian and normal; `B_Q` is a Noetherian normal local domain
  haveI : IsNoetherianRing (integralClosure ℤ[X] E) :=
    IsIntegralClosure.isNoetherianRing ℤ[X] (RatFunc ℚ) E (integralClosure ℤ[X] E)
  haveI : IsIntegrallyClosed (integralClosure ℤ[X] E) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (RatFunc ℚ)
  set BQ := Localization.AtPrime Q
  haveI : IsNoetherianRing BQ := IsLocalization.isNoetherianRing Q.primeCompl BQ inferInstance
  haveI : IsIntegrallyClosed BQ :=
    isIntegrallyClosed_of_isLocalization BQ Q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors Q)
  -- `p ∈ Q`, and `p ≠ 0` in `B`
  set pB : integralClosure ℤ[X] E := algebraMap ℤ[X] (integralClosure ℤ[X] E) (C (p : ℤ))
    with hpBdef
  have hpQ : pB ∈ Q := by
    have : C (p : ℤ) ∈ Q.under ℤ[X] := by
      rw [hQu, vertPrime]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
    exact this
  -- the local hom `B_Q → R`
  have hmemQ : ∀ b, b ∈ Q ↔ ψ b ∈ IsLocalRing.maximalIdeal R := fun b => by rw [hQ]; rfl
  have hunitψ : ∀ y : Q.primeCompl, IsUnit (ψ y) := by
    intro y
    have hy : (y : integralClosure ℤ[X] E) ∉ Q := y.2
    by_contra hn
    exact hy ((hmemQ _).2 ((IsLocalRing.mem_maximalIdeal _).2 hn))
  let φ : BQ →+* R := IsLocalization.lift hunitψ
  have hφ : ∀ b, φ (algebraMap _ BQ b) = ψ b := fun b => IsLocalization.lift_eq hunitψ b
  have hmap : (IsLocalRing.maximalIdeal BQ).map φ ≤ IsLocalRing.maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, RingHom.comp_apply, hφ]
    exact (hmemQ b).1 hb
  set x := algebraMap (integralClosure ℤ[X] E) BQ pB with hxdef
  have hxm : x ∈ IsLocalRing.maximalIdeal BQ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hpQ
  have hxm2 : x ∉ (IsLocalRing.maximalIdeal BQ) ^ 2 := by
    intro hx
    apply hψ
    have h1 : φ x ∈ ((IsLocalRing.maximalIdeal BQ).map φ) ^ 2 := by
      rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hx
    have h2 : ((IsLocalRing.maximalIdeal BQ).map φ) ^ 2 ≤ (IsLocalRing.maximalIdeal R) ^ 2 := by
      rw [sq, sq]; exact Ideal.mul_mono hmap hmap
    have h3 := h2 h1
    rwa [hxdef, hφ] at h3
  have hx0 : x ≠ 0 := fun h => hxm2 (by rw [h]; exact zero_mem _)
  haveI : IsDomain BQ := IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors Q)
  -- the unique nonzero prime of `B_Q`
  have huniq : ∃! P : Ideal BQ, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨IsLocalRing.maximalIdeal BQ, ⟨?_, inferInstance⟩, ?_⟩
    · intro h
      rw [h] at hxm
      exact hx0 (Ideal.mem_bot.1 hxm)
    · rintro P' ⟨hne, hprime⟩
      set Q' := P'.comap (algebraMap (integralClosure ℤ[X] E) BQ) with hQ'def
      haveI : Q'.IsPrime := Ideal.comap_isPrime _ _
      have hQ'le : Q' ≤ Q := by
        intro b hb
        by_contra hbQ
        have hu : IsUnit (algebraMap (integralClosure ℤ[X] E) BQ b) :=
          IsLocalization.map_units BQ (⟨b, hbQ⟩ : Q.primeCompl)
        exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ hb hu)
      have hmc : Q'.map (algebraMap (integralClosure ℤ[X] E) BQ) = P' :=
        IsLocalization.map_comap Q.primeCompl BQ P'
      have hQ'ne : Q' ≠ ⊥ := by
        intro h0
        apply hne
        rw [← hmc, h0, Ideal.map_bot]
      have hQ'eq : Q' = Q := by
        by_contra hneq
        have hlt : Q' < Q := lt_of_le_of_ne hQ'le hneq
        have h1 := Ideal.IsIntegral.under_lt_under (R := ℤ[X]) hlt
        have h2 : Q'.under ℤ[X] ≠ ⊥ := fun h => hQ'ne (Ideal.eq_bot_of_under_eq_bot h)
        have h3 := eq_vertPrime hp (Q'.under ℤ[X]) h2 (by rw [← hQu]; exact h1.le)
        rw [h3, hQu] at h1
        exact lt_irrefl _ h1
      rw [← hmc, hQ'eq]
      exact Localization.AtPrime.map_eq_maximalIdeal
  have hnf : ¬ IsField BQ := by
    intro hf
    have hm0 := (IsLocalRing.isField_iff_maximalIdeal_eq.1 hf)
    rw [hm0] at hxm
    exact hx0 (Ideal.mem_bot.1 hxm)
  have key : (IsIntegrallyClosed BQ ∧ ∃! P : Ideal BQ, P ≠ ⊥ ∧ P.IsPrime) ↔
      IsDiscreteValuationRing BQ := (IsDiscreteValuationRing.TFAE BQ hnf).out 4 1
  haveI : IsDiscreteValuationRing BQ := key.mp ⟨inferInstance, huniq⟩
  -- `x` is a uniformizer
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible BQ
  obtain ⟨n, u, hxu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖm : ϖ ∈ IsLocalRing.maximalIdeal BQ := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at hxu
      exact (IsLocalRing.mem_maximalIdeal _).1 hxm (hxu ▸ u.isUnit)
    · rfl
    · exfalso
      apply hxm2
      have e : (u : BQ) * ϖ ^ (n + 1 + 1) = ((u : BQ) * ϖ ^ n * ϖ) * ϖ := by ring
      rw [hxu, e, sq]
      exact Ideal.mul_mem_mul ((IsLocalRing.maximalIdeal BQ).mul_mem_left _ hϖm) hϖm
  rw [hn1, pow_one] at hxu
  have hPm : (Q.under ℤ[X]).map (algebraMap ℤ[X] BQ) = IsLocalRing.maximalIdeal BQ := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply ℤ[X] (integralClosure ℤ[X] E) BQ,
        ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ ha
    · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.span_le,
        Set.singleton_subset_iff]
      have hϖx : ϖ = ↑u⁻¹ * x := by rw [hxu, ← mul_assoc, Units.inv_mul, one_mul]
      rw [SetLike.mem_coe, hϖx]
      apply Ideal.mul_mem_left
      rw [hxdef, hpBdef, ← IsScalarTower.algebraMap_apply]
      apply Ideal.mem_map_of_mem
      rw [hQu, vertPrime]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  rw [Ideal.ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff]
  exact hPm

/-- **Glue (good-reduction input, local form) for the Hecke cover.** For a triple with R1fp,
R1hecke, R2fp and any `E` carrying the chart, every prime `p > 324` has a local-ring witness
(`VertLocalWitness`): the local ring of a smooth model of `Y₃` over `ℤ_(p)` at the generic point of
a component of the special fibre, with `p` a uniformizer and `X` of transcendental reduction (route
GR, §3 of docs/research/hecke-rest.md). Glue, not a leaf. -/
def HeckeVertLocal : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R1heckeProps Y Φ → R2fpProps Y Φ π →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E]
      [IsGalois (RatFunc ℚ) E], NormalizationModel Y π E →
      ∀ p : ℕ, p.Prime → 324 < p → VertLocalWitness E p

/-- **`HeckeNoVertRam` from local-ring witnesses** (compiled). -/
theorem heckeNoVertRam_of_local (h : HeckeVertLocal) : HeckeNoVertRam :=
  heckeNoVertRam_of_witness fun Y Φ π h1 hh h2 E _ _ _ _ _ _ hN p hp hp324 =>
    vertUnramWitness_of_local E p hp (h Y Φ π h1 hh h2 E hN p hp hp324)

end HeckeRestNV

end


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 3: `CurveNormChart` from `ChartFinite` and `ChartNormal`

`CurveNormChart` asks for a finite `E/ℚ(X)` with an open immersion `Spec B → Y`
(`B = ` integral closure of `ℚ[X]` in `E`) through which every `ℚ̄`-point with `π ≠ ∞` factors and
along which `π` is the coordinate `X`. Given that `U = π⁻¹(𝔸¹)` is affine with `Γ(Y, U)` a finite
`ℚ[X]`-algebra via `X ↦ π.f` (`ChartFinite`) and a normal domain (`ChartNormal`), the field
`E = Frac Γ(Y, U)` does it: `Γ(Y, U)` is the integral closure of `ℚ[X]` in `E`, and the chart is
`Spec B ≅ Spec Γ(Y, U) ≅ U ⊆ Y` (compiled below).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestCurve

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane PropTSRed TSHecke

/-- `ℚ → Γ(Y, U)` through the structure morphism `Y → Spec ℚ`. -/
def cQ (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens) : ℚ →+* Γ(Y.left, U) :=
  (res (le_top : U ≤ ⊤)).comp
    ((Y.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom)

/-- `ℚ[X] → Γ(Y, π⁻¹(𝔸¹))`, `X ↦ π.f` (the chart of `π` over `𝔸¹` on rings). -/
def chartHom (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) : ℚ[X] →+* Γ(Y.left, π.U) :=
  Polynomial.eval₂RingHom (cQ Y π.U) π.f

/-- **Glue (curve theory: `π` is finite over `𝔸¹`).** For a proper smooth irreducible curve `Y/ℚ`
and `π : Y → P¹` with finite `ℚ̄`-fibres, `U = π⁻¹(𝔸¹)` is a nonempty affine open and `Γ(Y, U)` is
a finite `ℚ[X]`-algebra via `X ↦ π.f`, with `ℚ[X] → Γ(Y, U)` injective. *Proof* (STANDARD;
Hartshorne II.6.8 and Ex. II.3.5, Stacks 02OG (= Mathlib's
`IsFinite.of_isProper_of_locallyQuasiFinite`), 01WN; locators UNVERIFIED): `U → 𝔸¹` is proper
(valuative criterion: a valuation-ring point of `Y` over `𝔸¹` cannot meet `π = ∞`, since `f g = 1`
on `U ∩ V`) and quasi-finite (closed fibres: finite `ℚ̄`-fibres; generic fibre: the generic point
of `Y`), hence finite (Zariski's main theorem), hence affine; it is surjective onto `𝔸¹` (finite and
dominant), so `ℚ[X] → Γ(Y, U)` is injective. Glue, not a leaf. -/
def ChartFinite : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    IsAffineOpen π.U ∧ (π.U : Set Y.left).Nonempty ∧ Function.Injective (chartHom Y π) ∧
      @Module.Finite ℚ[X] Γ(Y.left, π.U) _ _ (chartHom Y π).toAlgebra.toModule

/-- **Glue (smooth curves are normal).** On a smooth irreducible curve `Y/ℚ`, the sections over a
nonempty affine open form an integrally closed domain. *Proof* (STANDARD; Hartshorne I.6,
II.6.2A, Stacks 033B/0567; locators UNVERIFIED): `Y` is reduced and irreducible, hence integral;
its local rings at closed points are regular of dimension 1 (curve-glue, infra-smooth-dim:
`isDomain_of_dim_one`, stalk dimensions), hence DVRs; a domain whose localizations at all maximal
ideals are integrally closed is integrally closed. Glue; **proved below** (`chartNormal`). -/
def ChartNormal : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens),
    SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left → IsAffineOpen U →
    (U : Set Y.left).Nonempty → IsDomain Γ(Y.left, U) ∧ IsIntegrallyClosed Γ(Y.left, U)

/-- The value at `Spec χ → Spec Γ(X, U) → X` of a section over the affine open `U` is `χ s`. -/
theorem ev_fromSpec {K : Type} [Field K] {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (χ : Γ(X, U) ⟶ CommRingCat.of K) (hx : ptOf (Spec.map χ ≫ hU.fromSpec) ∈ U) (s : Γ(X, U)) :
    ev (Spec.map χ ≫ hU.fromSpec) hx s = χ s := by
  rw [ev_comp, hU.fromSpec_app_self_apply]
  change ev (Spec.map χ) _ (res (le_top : hU.fromSpec ⁻¹ᵁ U ≤ ⊤)
    ((Scheme.ΓSpecIso Γ(X, U)).inv s)) = _
  rw [ev_res]
  exact ev_spec_top (R := Γ(X, U)) χ s

/-- **`CurveNormChart` from `ChartFinite` and `ChartNormal`** (compiled). -/
theorem curveNormChart_of (hF : ChartFinite) (hN : ChartNormal) : CurveNormChart := by
  intro Y π hP hS hI hfin
  obtain ⟨hU, hne, hinj, hfinM⟩ := hF Y π hP hS hI hfin
  obtain ⟨hdom, hic⟩ := hN Y π.U hS hI hU hne
  letI : Algebra ℚ[X] Γ(Y.left, π.U) := (chartHom Y π).toAlgebra
  haveI : Module.Finite ℚ[X] Γ(Y.left, π.U) := hfinM
  haveI := hdom
  haveI := hic
  let E := FractionRing Γ(Y.left, π.U)
  have hinjE : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] Γ(Y.left, π.U) E]
    exact (IsFractionRing.injective Γ(Y.left, π.U) E).comp hinj
  letI : Algebra (RatFunc ℚ) E := (IsFractionRing.lift (K := RatFunc ℚ) hinjE).toAlgebra
  haveI : IsScalarTower ℚ[X] (RatFunc ℚ) E := IsScalarTower.of_algebraMap_eq
    (fun a => (IsFractionRing.lift_algebraMap (K := RatFunc ℚ) hinjE a).symm)
  haveI : IsIntegralClosure Γ(Y.left, π.U) ℚ[X] E :=
    IsIntegralClosure.of_isIntegrallyClosed Γ(Y.left, π.U) ℚ[X] E
  haveI : Algebra.IsAlgebraic (RatFunc ℚ) E :=
    isAlgebraic_of_isFractionRing ℚ[X] Γ(Y.left, π.U) (RatFunc ℚ) E
  haveI : IsLocalization (Algebra.algebraMapSubmonoid Γ(Y.left, π.U) (nonZeroDivisors ℚ[X])) E :=
    IsIntegralClosure.isLocalization ℚ[X] (RatFunc ℚ) E Γ(Y.left, π.U)
  haveI : Module.Finite (RatFunc ℚ) E :=
    Module.Finite.of_isLocalization ℚ[X] Γ(Y.left, π.U) (nonZeroDivisors ℚ[X])
  let e : Γ(Y.left, π.U) ≃ₐ[ℚ[X]] integralClosure ℚ[X] E :=
    IsIntegralClosure.equiv ℚ[X] Γ(Y.left, π.U) E (integralClosure ℚ[X] E)
  let eH : Γ(Y.left, π.U) ⟶ CommRingCat.of (integralClosure ℚ[X] E) :=
    CommRingCat.ofHom (e : Γ(Y.left, π.U) →+* integralClosure ℚ[X] E)
  let eH' : CommRingCat.of (integralClosure ℚ[X] E) ⟶ Γ(Y.left, π.U) :=
    CommRingCat.ofHom (e.symm : integralClosure ℚ[X] E →+* Γ(Y.left, π.U))
  have heH : eH ≫ eH' = 𝟙 _ := by
    ext x
    exact e.symm_apply_apply x
  haveI : IsIso eH := ⟨⟨eH', heH, by ext x; exact congrArg Subtype.val (e.apply_symm_apply x)⟩⟩
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map eH ≫ hU.fromSpec, inferInstance, ?_, ?_⟩
  · intro y hy
    have hmem : ptOf y ∈ π.U := by
      by_contra h
      exact hy (val_of_not_mem π y h)
    have hr : Set.range y.base ⊆ Set.range hU.fromSpec.base := by
      rintro _ ⟨z, rfl⟩
      rw [hU.range_fromSpec]
      have hz : z = IsLocalRing.closedPoint Qbar := Subsingleton.elim _ _
      rw [hz]
      exact hmem
    refine ⟨IsOpenImmersion.lift hU.fromSpec y hr ≫ Spec.map eH', ?_⟩
    rw [Category.assoc, ← Category.assoc (Spec.map eH'), ← Spec.map_comp, heH, Spec.map_id,
      Category.id_comp, IsOpenImmersion.lift_fac]
  · intro ψ
    let χ : Γ(Y.left, π.U) ⟶ CommRingCat.of Qbar := eH ≫ CommRingCat.ofHom ψ
    have hpt : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map eH ≫ hU.fromSpec =
        Spec.map χ ≫ hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]
    have hmem : ptOf (Spec.map χ ≫ hU.fromSpec) ∈ π.U := by
      have h0 : ptOf (Spec.map χ ≫ hU.fromSpec) ∈ Set.range hU.fromSpec.base := by
        rw [ptOf_comp]; exact ⟨_, rfl⟩
      rw [hU.range_fromSpec] at h0
      exact h0
    rw [hpt, val_of_mem π _ hmem, ev_fromSpec hU χ hmem π.f]
    congr 1
    have hf : π.f = algebraMap ℚ[X] Γ(Y.left, π.U) X := by
      show π.f = Polynomial.eval₂ (cQ Y π.U) π.f X
      rw [Polynomial.eval₂_X]
    rw [hf]
    show ψ (e (algebraMap ℚ[X] Γ(Y.left, π.U) X)) = _
    rw [AlgEquiv.commutes]

/-! ## `CurveChartInf` from `ChartFiniteInf`, `ChartNormalD` and `InfFnField`

The same construction over `P¹ ∖ {0}`: `V = π⁻¹(P¹ ∖ {0})`, `ℚ[s] → Γ(Y, V)`, `s ↦ π.g`. The given
`E` enters through `InfFnField`: `E` is the fraction field of `Γ(Y, V)` with `π.g ↦ 1/X`. -/

/-- `ℚ[s] → Γ(Y, π⁻¹(P¹ ∖ {0}))`, `s ↦ π.g`. -/
def chartHomInf (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left) :
    InfCoord →+* Γ(Y.left, π.V) :=
  (Polynomial.eval₂RingHom (cQ Y π.V) π.g : ℚ[X] →+* Γ(Y.left, π.V))

/-- **Glue (curve theory: `π` is finite over `P¹ ∖ {0}`).** As `ChartFinite`, for
`V = π⁻¹(P¹ ∖ {0})` and the coordinate `s = 1/X` (`π.g`). Same proof (Hartshorne II.6.8,
Stacks 02OG; locators UNVERIFIED); irreducibility is not needed, nonemptiness is (for `Y = ∅`,
`Γ(Y, V) = 0` and injectivity fails). Glue, not a leaf. -/
def ChartFiniteInf : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → Nonempty Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    IsAffineOpen π.V ∧ Function.Injective (chartHomInf Y π) ∧
      @Module.Finite InfCoord Γ(Y.left, π.V) _ _ (chartHomInf Y π).toAlgebra.toModule

/-- **Glue (smooth curves are normal), domain form.** On a smooth curve `Y/ℚ`, if the sections over
an affine open form a domain, the domain is integrally closed (local rings at closed points are
DVRs; Hartshorne I.6, Stacks 033B; locators UNVERIFIED). Glue; **proved below** (`chartNormalD`). -/
def ChartNormalD : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens),
    SmoothOfRelativeDimension 1 Y.hom → IsAffineOpen U → IsDomain Γ(Y.left, U) →
    IsIntegrallyClosed Γ(Y.left, U)

/-- **Glue (curve theory: the function field seen from `∞`).** If `E` carries the chart of `π` over
`𝔸¹`, then `E` is the fraction field of `Γ(Y, π⁻¹(P¹ ∖ {0}))` through a ring map sending `π.g` to
`1/X`. *Proof* (STANDARD; Hartshorne I.6, II.6.7): finite fibres force every component of `Y` to
meet `π⁻¹(𝔸¹)`, whose image under the chart is `Spec B` with `B` a domain; so `Y` is integral with
function field `Frac B = E`; restriction `Γ(Y, V) → Γ(Y, U ∩ V) → E` is injective, and `π.g = 1/π.f`
on `U ∩ V` with `π.f ↦ X`; `E` is finite over `ℚ(X)` and `Γ(Y, V)` contains `ℚ[1/X]`, so `E` is its
fraction field. Glue, not a leaf. -/
def InfFnField : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E],
      NormalizationModel Y π E →
      ∃ φ : Γ(Y.left, π.V) →+* E, φ π.g = algebraMap (RatFunc ℚ) E (RatFunc.X : RatFunc ℚ)⁻¹ ∧
        @IsFractionRing Γ(Y.left, π.V) _ E _ φ.toAlgebra

/-- **`CurveChartInf` from `ChartFiniteInf`, `ChartNormalD` and `InfFnField`** (compiled). -/
theorem curveChartInf_of (hF : ChartFiniteInf) (hND : ChartNormalD) (hFF : InfFnField) :
    CurveChartInf := by
  intro Y π hP hS hfin E _ _ _ _ _ hN
  have hne : Nonempty Y.left := by
    obtain ⟨h, -, -⟩ := hN
    obtain ⟨z⟩ : Nonempty (Spec (CommRingCat.of (integralClosure ℚ[X] E))) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (integralClosure ℚ[X] E)))
    exact ⟨h.base z⟩
  obtain ⟨hV, hinj, hfinM⟩ := hF Y π hP hS hne hfin
  obtain ⟨φ, hφg, hfrac⟩ := hFF Y π hP hS hfin E hN
  letI : Algebra InfCoord Γ(Y.left, π.V) := (chartHomInf Y π).toAlgebra
  haveI : Module.Finite InfCoord Γ(Y.left, π.V) := hfinM
  letI : Algebra Γ(Y.left, π.V) E := φ.toAlgebra
  haveI : IsFractionRing Γ(Y.left, π.V) E := hfrac
  haveI : IsDomain Γ(Y.left, π.V) :=
    (IsFractionRing.injective Γ(Y.left, π.V) E).isDomain _
  haveI : IsIntegrallyClosed Γ(Y.left, π.V) := hND Y π.V hS hV inferInstance
  letI := infAlg E
  have hcomp : (φ.comp (chartHomInf Y π) : ℚ[X] →+* E) = (algebraMap InfCoord E : ℚ[X] →+* E) := by
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (Subsingleton.elim
        (((φ.comp (chartHomInf Y π) : ℚ[X] →+* E)).comp Polynomial.C)
        (((algebraMap InfCoord E : ℚ[X] →+* E)).comp Polynomial.C)) a
    · show φ (Polynomial.eval₂ (cQ Y π.V) π.g Polynomial.X) =
        algebraMap (RatFunc ℚ) E (Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹)
          Polynomial.X)
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X, hφg]
  haveI : IsScalarTower InfCoord Γ(Y.left, π.V) E := IsScalarTower.of_algebraMap_eq
    (fun a => (RingHom.congr_fun hcomp a).symm)
  haveI : IsIntegralClosure Γ(Y.left, π.V) InfCoord E :=
    IsIntegralClosure.of_isIntegrallyClosed Γ(Y.left, π.V) InfCoord E
  let e : Γ(Y.left, π.V) ≃ₐ[InfCoord] integralClosure InfCoord E :=
    IsIntegralClosure.equiv InfCoord Γ(Y.left, π.V) E (integralClosure InfCoord E)
  let eH : Γ(Y.left, π.V) ⟶ CommRingCat.of (integralClosure InfCoord E) :=
    CommRingCat.ofHom (e : Γ(Y.left, π.V) →+* integralClosure InfCoord E)
  let eH' : CommRingCat.of (integralClosure InfCoord E) ⟶ Γ(Y.left, π.V) :=
    CommRingCat.ofHom (e.symm : integralClosure InfCoord E →+* Γ(Y.left, π.V))
  have heH : eH ≫ eH' = 𝟙 _ := by
    ext x
    exact e.symm_apply_apply x
  haveI : IsIso eH :=
    ⟨⟨eH', heH, by ext x; exact congrArg Subtype.val (e.apply_symm_apply x)⟩⟩
  refine ⟨Spec.map eH ≫ hV.fromSpec, inferInstance, ?_, ?_⟩
  · intro y hy
    have hmem : ptOf y ∈ π.V := by
      by_contra hv
      have hu : ptOf y ∈ π.U := by
        have : ptOf y ∈ π.U ⊔ π.V := by rw [π.cover]; trivial
        rcases this with h | h
        · exact h
        · exact absurd h hv
      apply hy
      rw [val_of_mem π y hu]
      congr 1
      rw [ev_eq_zero_iff, π.basicOpen_f]
      exact fun h => hv h.2
    have hr : Set.range y.base ⊆ Set.range hV.fromSpec.base := by
      rintro _ ⟨z, rfl⟩
      rw [hV.range_fromSpec]
      have hz : z = IsLocalRing.closedPoint Qbar := Subsingleton.elim _ _
      rw [hz]
      exact hmem
    refine ⟨IsOpenImmersion.lift hV.fromSpec y hr ≫ Spec.map eH', ?_⟩
    rw [Category.assoc, ← Category.assoc (Spec.map eH'), ← Spec.map_comp, heH, Spec.map_id,
      Category.id_comp, IsOpenImmersion.lift_fac]
  · intro ψ
    let χ : Γ(Y.left, π.V) ⟶ CommRingCat.of Qbar := eH ≫ CommRingCat.ofHom ψ
    have hpt : Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map eH ≫ hV.fromSpec =
        Spec.map χ ≫ hV.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]
    have hmem : ptOf (Spec.map χ ≫ hV.fromSpec) ∈ π.V := by
      have h0 : ptOf (Spec.map χ ≫ hV.fromSpec) ∈ Set.range hV.fromSpec.base := by
        rw [ptOf_comp]; exact ⟨_, rfl⟩
      rw [hV.range_fromSpec] at h0
      exact h0
    have hg : π.g = algebraMap InfCoord Γ(Y.left, π.V) infUnif := by
      show π.g = Polynomial.eval₂ (cQ Y π.V) π.g Polynomial.X
      rw [Polynomial.eval₂_X]
    have hval : ψ (algebraMap InfCoord (integralClosure InfCoord E) infUnif) = χ π.g := by
      rw [hg]
      show _ = ψ (e (algebraMap InfCoord Γ(Y.left, π.V) infUnif))
      rw [AlgEquiv.commutes]
    rw [hpt, hval, ← ev_fromSpec hV χ hmem π.g, ev_eq_zero_iff, π.basicOpen_g]
    constructor
    · intro h hUV
      rw [val_of_mem π _ hUV.1] at h
      exact OnePoint.coe_ne_infty _ h
    · intro h
      apply val_of_not_mem
      exact fun hU => h ⟨hU, hmem⟩

/-! ## `ChartNormalD` proved; `ChartNormal` reduced to its domain part -/

/-- **The localizations of `Γ(Y, U)` at maximal ideals are discrete valuation rings** (as domains
that are integrally closed): they are the local rings of `Y` at closed points, regular of
dimension 1 (infra-smooth-dim's `stalk_dim_of_smoothOfRelativeDimension`, curve-glue's
`isDomain_of_dim_one`, Mathlib's DVR TFAE). -/
theorem loc_max_dvr (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens)
    (hS : SmoothOfRelativeDimension 1 Y.hom) (hU : IsAffineOpen U) (p : Ideal Γ(Y.left, U))
    (hpm : p.IsMaximal) :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let q : PrimeSpectrum Γ(Y.left, U) := ⟨p, hpm.isPrime⟩
  let x : Y.left := hU.fromSpec q
  have hxU : x ∈ U := by
    have : x ∈ Set.range hU.fromSpec.base := ⟨q, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hxc : IsClosed ({x} : Set Y.left) := by
    apply isClosed_singleton_of_isLocallyClosed_singleton
    have hq : IsClosed ({q} : Set ↥(Spec Γ(Y.left, U))) :=
      (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).2 hpm
    have h2 := hq.isLocallyClosed.image hU.fromSpec.isOpenEmbedding.isInducing
      hU.fromSpec.isOpenEmbedding.isOpen_range.isLocallyClosed
    have e2 : (hU.fromSpec.base '' {q} : Set Y.left) = {x} := Set.image_singleton
    rw [e2] at h2
    exact h2
  obtain ⟨hdim, hspan⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension Y.hom 1 x hxc
  have hdim' : ringKrullDim (Y.left.presheaf.stalk x) = 1 := by rw [hdim]; rfl
  have hspan' : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x)).spanFinrank = 1 := hspan
  haveI : IsDomain (Y.left.presheaf.stalk x) := CIcopy.CurveGlueCI.isDomain_of_dim_one hdim' hspan'
  have hnf : ¬ IsField (Y.left.presheaf.stalk x) := fun h => by
    have h0 := ringKrullDim_eq_zero_of_isField h
    rw [hdim'] at h0
    exact one_ne_zero h0
  have hprin : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x)).IsPrincipal := by
    have hfg : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x)).FG := IsNoetherian.noetherian _
    obtain ⟨s, hs, hsp⟩ := Submodule.FG.exists_span_set_encard_eq_spanFinrank hfg
    rw [hspan'] at hs
    obtain ⟨t, rfl⟩ := Set.encard_eq_one.1 (by exact_mod_cast hs)
    exact ⟨⟨t, hsp.symm⟩⟩
  have key : (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk x)).IsPrincipal ↔
      (IsIntegrallyClosed (Y.left.presheaf.stalk x) ∧
        ∃! P : Ideal (Y.left.presheaf.stalk x), P ≠ ⊥ ∧ P.IsPrime) :=
    (IsDiscreteValuationRing.TFAE _ hnf).out 5 4
  haveI : IsIntegrallyClosed (Y.left.presheaf.stalk x) := (key.mp hprin).1
  letI : Algebra Γ(Y.left, U) (Y.left.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk Y.left.presheaf ⟨x, hxU⟩
  haveI : IsLocalization.AtPrime (Y.left.presheaf.stalk x) p := hU.isLocalization_stalk' q hxU
  let eq := (IsLocalization.algEquiv p.primeCompl (Y.left.presheaf.stalk x)
      (Localization.AtPrime p)).toRingEquiv
  exact ⟨eq.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv eq⟩

/-- **`ChartNormalD` holds** (compiled). -/
theorem chartNormalD : ChartNormalD := by
  intro Y U hS hU hdom
  exact IsIntegrallyClosed.of_localization_maximal fun p _ hpm => (loc_max_dvr Y U hS hU p hpm).2

/-- **Glue (smooth irreducible curves are integral).** The sections of a smooth irreducible curve
over a nonempty affine open form a domain. -/
def CurveSectionsDomain : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (U : Y.left.Opens),
    SmoothOfRelativeDimension 1 Y.hom → IrreducibleSpace Y.left → IsAffineOpen U →
    (U : Set Y.left).Nonempty → IsDomain Γ(Y.left, U)

/-- **`CurveSectionsDomain` holds** (compiled): `Γ(Y, U)` is reduced (its localizations at maximal
ideals are domains) and `Spec Γ(Y, U) ≅ U` is irreducible, so `Spec Γ(Y, U)` is integral. -/
theorem curveSectionsDomain : CurveSectionsDomain := by
  intro Y U hS hI hU hne
  haveI : IsReduced Γ(Y.left, U) := isReduced_ofLocalizationMaximal _ fun J hJ => by
    haveI := (loc_max_dvr Y U hS hU J hJ).1
    infer_instance
  have hUirr : IsIrreducible (U : Set Y.left) :=
    ⟨hne, (IrreducibleSpace.isIrreducible_univ Y.left).2.open_subset U.isOpen
      (Set.subset_univ _)⟩
  haveI : IrreducibleSpace (Spec Γ(Y.left, U)) :=
    @Function.Surjective.irreducibleSpace _ _ _ _ hU.isoSpec.hom.base
      hU.isoSpec.hom.base.hom.continuous hU.isoSpec.hom.surjective
      (Subtype.irreducibleSpace hUirr)
  exact (affine_isIntegral_iff _).1 (isIntegral_of_irreducibleSpace_of_isReduced _)

/-- **`ChartNormal` holds** (compiled), from `curveSectionsDomain` and `chartNormalD`. -/
theorem chartNormal : ChartNormal := by
  intro Y U hS hI hU hne
  haveI := curveSectionsDomain Y U hS hI hU hne
  exact ⟨inferInstance, chartNormalD Y U hS hU inferInstance⟩

/-- **`CurveNormChart` from `ChartFinite` alone** (compiled). -/
theorem curveNormChart_of' (hF : ChartFinite) : CurveNormChart :=
  curveNormChart_of hF chartNormal

/-- **`CurveChartInf` from `ChartFiniteInf` and `InfFnField`** (compiled). -/
theorem curveChartInf_of' (hF : ChartFiniteInf) (hFF : InfFnField) : CurveChartInf :=
  curveChartInf_of hF chartNormalD hFF

/-! ## `ChartFinite`, `ChartFiniteInf` from properness, quasi-finiteness and dominance

Mathlib's Zariski main theorem corollary `IsFinite.of_isProper_of_locallyQuasiFinite` (Stacks 02OG)
turns a proper, locally quasi-finite chart into a finite one; a finite morphism to an affine scheme
has affine source; and `IsFinite (Spec.map φ) ↔ φ` finite (compiled). -/

/-- `ℚ[X] → Γ(Y, W)`, `X ↦ s`. -/
def secHom (Y : Over (Spec (CommRingCat.of ℚ))) (W : Y.left.Opens) (s : Γ(Y.left, W)) :
    ℚ[X] →+* Γ(Y.left, W) :=
  Polynomial.eval₂RingHom (cQ Y W) s

/-- The morphism `W → 𝔸¹ = Spec ℚ[X]` given by `s ∈ Γ(Y, W)`. -/
def secMor (Y : Over (Spec (CommRingCat.of ℚ))) (W : Y.left.Opens) (s : Γ(Y.left, W)) :
    W.toScheme ⟶ Spec (CommRingCat.of ℚ[X]) :=
  W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (secHom Y W s))

/-- **A proper, locally quasi-finite `W → 𝔸¹` has affine source and finite ring map** (compiled). -/
theorem finite_of_proper_qf (Y : Over (Spec (CommRingCat.of ℚ))) (W : Y.left.Opens)
    (s : Γ(Y.left, W)) [IsProper (secMor Y W s)] [LocallyQuasiFinite (secMor Y W s)] :
    IsAffineOpen W ∧ @Module.Finite ℚ[X] Γ(Y.left, W) _ _ (secHom Y W s).toAlgebra.toModule := by
  haveI : IsFinite (secMor Y W s) := IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : IsAffine W.toScheme := isAffine_of_isAffineHom (secMor Y W s)
  have hW : IsAffineOpen W := inferInstanceAs (IsAffine W.toScheme)
  refine ⟨hW, ?_⟩
  have h5 : IsFinite (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (secHom Y W s))) := by
    rw [hW.isoSpec_hom]
    exact (inferInstance : IsFinite (secMor Y W s))
  haveI := h5
  have h6 : IsFinite (Spec.map (CommRingCat.ofHom (secHom Y W s))) := by
    have e : Spec.map (CommRingCat.ofHom (secHom Y W s)) =
        hW.isoSpec.inv ≫ (hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (secHom Y W s))) := by
      rw [Iso.inv_hom_id_assoc]
    rw [e]
    infer_instance
  rw [IsFinite.SpecMap_iff] at h6
  exact h6

/-- **Glue (curve theory: the two charts of `π` are proper).** For a proper smooth curve `Y/ℚ` and
`π : Y → P¹` with finite `ℚ̄`-fibres, `π⁻¹(𝔸¹) → 𝔸¹` (by `π.f`) and `π⁻¹(P¹ ∖ {0}) → 𝔸¹` (by
`π.g = 1/π.f`) are proper. *Proof* (STANDARD; valuative criterion, Hartshorne II.4.7 and
II.4.8(f); locators UNVERIFIED): separated and of finite type by cancellation from `Y → Spec ℚ`;
universally closed since a valuation-ring point of `Y` (which exists by properness of `Y`) whose
generic point lies in `U` and whose `π.f`-value is integral cannot meet `π = ∞`, because
`π.f · π.g = 1` on `U ∩ V`. Glue, not a leaf. -/
def ChartProper : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    IsProper (secMor Y π.U π.f) ∧ IsProper (secMor Y π.V π.g)

/-- **Glue (curve theory: the two charts of `π` are quasi-finite).** Under the same hypotheses
both charts are locally quasi-finite. *Proof* (STANDARD; Stacks 01TD/02NH; locators UNVERIFIED):
the points over a closed point of `𝔸¹` are closed points of `Y`, each with a `ℚ̄`-point in the
corresponding finite `π`-fibre; over the generic point of `𝔸¹` lie only generic points of
components of `Y` (finitely many). Glue, not a leaf. -/
def ChartQuasiFinite : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    LocallyQuasiFinite (secMor Y π.U π.f) ∧ LocallyQuasiFinite (secMor Y π.V π.g)

/-- **Glue (curve theory: the two charts are dominant).** Under the same hypotheses `π⁻¹(𝔸¹)` is
nonempty and `ℚ[X] → Γ(Y, π⁻¹(𝔸¹))`, `ℚ[s] → Γ(Y, π⁻¹(P¹ ∖ {0}))` are injective (a polynomial
relation for `π.f` on a component would make a `π`-fibre infinite: `π` would take finitely many
values on the infinitely many `ℚ̄`-points of that component; `Y ≠ ∅` is needed, since for `Y = ∅`
both clauses fail). Glue, not a leaf. -/
def ChartDominant : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom → Nonempty Y.left →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    (π.U : Set Y.left).Nonempty ∧ Function.Injective (secHom Y π.U π.f) ∧
      Function.Injective (secHom Y π.V π.g)

/-- **`ChartFinite` from `ChartProper`, `ChartQuasiFinite`, `ChartDominant`** (compiled). -/
theorem chartFinite_of (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant) :
    ChartFinite := by
  intro Y π h1 h2 h3 h4
  haveI := (hP Y π h1 h2 h4).1
  haveI := (hQ Y π h1 h2 h4).1
  obtain ⟨hU, hfin⟩ := finite_of_proper_qf Y π.U π.f
  obtain ⟨hne, hinj, -⟩ := hD Y π h1 h2 inferInstance h4
  exact ⟨hU, hne, hinj, hfin⟩

/-- **`ChartFiniteInf` from `ChartProper`, `ChartQuasiFinite`, `ChartDominant`** (compiled). -/
theorem chartFiniteInf_of (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant) :
    ChartFiniteInf := by
  intro Y π h1 h2 h3 h4
  haveI := (hP Y π h1 h2 h4).2
  haveI := (hQ Y π h1 h2 h4).2
  obtain ⟨hV, hfin⟩ := finite_of_proper_qf Y π.V π.g
  obtain ⟨-, -, hinj⟩ := hD Y π h1 h2 h3 h4
  exact ⟨hV, hinj, hfin⟩

/-- **`CurveNormChart` from the three chart Props** (compiled). -/
theorem curveNormChart_of_charts (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant) :
    CurveNormChart :=
  curveNormChart_of' (chartFinite_of hP hQ hD)

/-- **`CurveChartInf` from the three chart Props and `InfFnField`** (compiled). -/
theorem curveChartInf_of_charts (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant)
    (hFF : InfFnField) : CurveChartInf :=
  curveChartInf_of' (chartFiniteInf_of hP hQ hD) hFF

end HeckeRestCurve

end


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 3b: `InfFnField` from `ChartFiniteInf` and `ChartIrreducible`

Given the chart `h : Spec B → Y` over `𝔸¹` (`NormalizationModel`): its range is `U = π⁻¹(𝔸¹)`
(Jacobson); `h^*π.f = X` (separation by `ℚ̄`-points); `h⁻¹(V) = D(X) ⊆ Spec B`; and
`Γ(Y, V) → Γ(Spec B, D(X)) = B[1/X] ⊆ E` is the required map (`π.g ↦ 1/X`), injective because
`Γ(Y, V)` is a domain integral over `ℚ[s]` (incomparability), with fraction field `E` because
`Γ(Spec B, D(X)) ≅ Γ(Y, U ∩ V) = Γ(Y, V)[1/π.g]`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestCurve

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane PropTSRed TSHecke

/-- **Glue (curve theory: the curve is irreducible).** A proper smooth curve `Y/ℚ` with
`π : Y → P¹` of finite `ℚ̄`-fibres and a normalization chart over `𝔸¹` is irreducible. *Proof*
(STANDARD; Hartshorne II.6.7; locators UNVERIFIED): the chart's image `U = π⁻¹(𝔸¹)` is irreducible
(the image of `Spec B`, `B` a domain); its complement is the fibre over `∞`; a nonempty open set
outside `closure U` would have infinitely many closed points (no point of a smooth curve is open:
local rings have dimension 1), all in the finite fibre over `∞`. Glue, not a leaf. -/
def ChartIrreducible : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (π : ToP1 Y.left),
    IsProper Y.hom → SmoothOfRelativeDimension 1 Y.hom →
    (∀ t : OnePoint Qbar, {y : fieldPt Qbar ⟶ Y | π.val (K := Qbar) y.left = t}.Finite) →
    ∀ (E : Type) [Field E] [Algebra (RatFunc ℚ) E] [Algebra ℚ[X] E]
      [IsScalarTower ℚ[X] (RatFunc ℚ) E] [FiniteDimensional (RatFunc ℚ) E],
      NormalizationModel Y π E → IrreducibleSpace Y.left

section Chart

variable {Y : Over (Spec (CommRingCat.of ℚ))} {π : ToP1 Y.left} {E : Type} [Field E]
  [Algebra ℚ[X] E]

/-- **The chart's range is `π⁻¹(𝔸¹)`** (compiled; Jacobson, as in ts-hecke's `range_comp_subset`). -/
theorem range_chart_eq [LocallyOfFiniteType Y.hom]
    (h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left) [IsOpenImmersion h]
    (himg : ∀ y : Spec (CommRingCat.of Qbar) ⟶ Y.left, π.val (K := Qbar) y ≠ OnePoint.infty →
      ∃ y' : Spec (CommRingCat.of Qbar) ⟶ Spec (CommRingCat.of (integralClosure ℚ[X] E)),
        y = y' ≫ h)
    (hval : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X))) :
    Set.range h = (π.U : Set Y.left) := by
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  apply Set.Subset.antisymm
  · by_contra hcon
    rw [Set.not_subset] at hcon
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := hcon
    set W : Set Y.left := Set.range h ∩ (π.U : Set Y.left)ᶜ
    have hWne : W.Nonempty := ⟨h x, ⟨x, rfl⟩, hx⟩
    have hWlc : IsLocallyClosed W :=
      (h.isOpenEmbedding.isOpen_range).isLocallyClosed.inter
        π.U.isOpen.isClosed_compl.isLocallyClosed
    obtain ⟨z, ⟨hzh, hzU⟩, hzc⟩ := nonempty_inter_closedPoints hWne hWlc
    obtain ⟨y, hy⟩ := TSHeckeGal.exists_qbar_point Y.hom z (mem_closedPoints_iff.mp hzc)
    have hyr : Set.range y ⊆ Set.range h := by
      rintro _ ⟨s, rfl⟩; rw [hy s]; exact hzh
    set y'' := IsOpenImmersion.lift h y hyr
    have hy'' : y'' ≫ h = y := IsOpenImmersion.lift_fac h y hyr
    have hfin : π.val (K := Qbar) y ≠ OnePoint.infty := by
      rw [← hy'', ← Spec.map_preimage y'', ← CommRingCat.ofHom_hom (Spec.preimage y''), hval]
      exact OnePoint.coe_ne_infty _
    have hmem : ptOf y ∈ π.U := by
      by_contra hn
      exact hfin (val_of_not_mem π y hn)
    have hpt : ptOf y = z := hy _
    exact hzU (hpt ▸ hmem)
  · intro z hzU
    by_contra hz
    set W : Set Y.left := (π.U : Set Y.left) ∩ (Set.range h)ᶜ
    have hWne : W.Nonempty := ⟨z, hzU, hz⟩
    have hWlc : IsLocallyClosed W :=
      π.U.isOpen.isLocallyClosed.inter
        (h.isOpenEmbedding.isOpen_range).isClosed_compl.isLocallyClosed
    obtain ⟨z', ⟨hz'U, hz'h⟩, hz'c⟩ := nonempty_inter_closedPoints hWne hWlc
    obtain ⟨y, hy⟩ := TSHeckeGal.exists_qbar_point Y.hom z' (mem_closedPoints_iff.mp hz'c)
    have hpt : ptOf y = z' := hy _
    have hmem : ptOf y ∈ π.U := hpt ▸ hz'U
    have hfin : π.val (K := Qbar) y ≠ OnePoint.infty := by
      rw [val_of_mem π y hmem]
      exact OnePoint.coe_ne_infty _
    obtain ⟨y', hy'⟩ := himg y hfin
    apply hz'h
    obtain ⟨s⟩ : Nonempty (Spec (CommRingCat.of Qbar)) := inferInstance
    refine ⟨y' s, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hy', hy s]

/-- **`h^* π.f = X`** (compiled; separation by `ℚ̄`-points in the Jacobson domain `B`). -/
theorem app_f_eq [Algebra (RatFunc ℚ) E] [IsScalarTower ℚ[X] (RatFunc ℚ) E]
    (h : Spec (CommRingCat.of (integralClosure ℚ[X] E)) ⟶ Y.left)
    (hval : ∀ ψ : integralClosure ℚ[X] E →+* Qbar,
      π.val (K := Qbar) (Spec.map (CommRingCat.ofHom ψ) ≫ h) =
        OnePoint.some (ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X)))
    (htop : h ⁻¹ᵁ π.U = ⊤) :
    (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom
        (res htop.ge (h.app π.U π.f)) = algebraMap ℚ[X] (integralClosure ℚ[X] E) X := by
  have hinjQE : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    apply hinjQE
    have := congrArg (fun x : integralClosure ℚ[X] E => (x : E)) hab
    simpa using this
  apply TSHeckeGal.eq_of_forall_qbar hinjB
  intro ψ
  have hx : ptOf (Spec.map (CommRingCat.ofHom ψ) ≫ h) ∈ π.U := by
    show h.base (ptOf (Spec.map (CommRingCat.ofHom ψ))) ∈ π.U
    have : ptOf (Spec.map (CommRingCat.ofHom ψ)) ∈ h ⁻¹ᵁ π.U := by rw [htop]; trivial
    exact this
  have h1 := hval ψ
  rw [val_of_mem π _ hx] at h1
  have h2 : ev (Spec.map (CommRingCat.ofHom ψ) ≫ h) hx π.f =
      ψ (algebraMap ℚ[X] (integralClosure ℚ[X] E) X) := OnePoint.coe_injective h1
  rw [← h2, ev_comp, ← ev_res _ htop.ge (show ptOf (Spec.map (CommRingCat.ofHom ψ)) ∈
    (⊤ : (Spec (CommRingCat.of (integralClosure ℚ[X] E))).Opens) from trivial)]
  set w := res htop.ge (h.app π.U π.f)
  have hw : w = (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv
      ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom w) :=
    (Iso.hom_inv_id_apply _ _).symm
  conv_rhs => rw [hw]
  rw [ev_spec_top]
  rfl

/-- `ℚ[s] → ℚ(X)`, `s ↦ 1/X`, is injective (ts-hecke's argument in `isFractionRing_infCoord`). -/
theorem infCoord_injective : Function.Injective (algebraMap InfCoord (RatFunc ℚ)) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  letI : Invertible (RatFunc.X : RatFunc ℚ) := invertibleOfNonzero hX
  have hev : Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) RatFunc.X =
      algebraMap ℚ[X] (RatFunc ℚ) :=
    Polynomial.ringHom_ext (fun a => RingHom.congr_fun (Subsingleton.elim
      ((Polynomial.eval₂RingHom (algebraMap ℚ (RatFunc ℚ)) RatFunc.X).comp Polynomial.C)
      ((algebraMap ℚ[X] (RatFunc ℚ)).comp Polynomial.C)) a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RatFunc.algebraMap_X])
  rw [injective_iff_map_eq_zero]
  show ∀ p : ℚ[X], algebraMap InfCoord (RatFunc ℚ) p = 0 → p = 0
  intro p hp
  have h1 := Polynomial.eval₂_reflect_mul_pow (algebraMap ℚ (RatFunc ℚ)) RatFunc.X p.natDegree
    (Polynomial.reflect p.natDegree p) (Polynomial.natDegree_reflect_le.trans (by simp))
  rw [Polynomial.reflect_reflect] at h1
  have hp' : Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (⅟RatFunc.X) p = 0 := by
    rw [invOf_eq_inv]; exact hp
  rw [hp', zero_mul, ← Polynomial.coe_eval₂RingHom, hev] at h1
  have h2 := (map_eq_zero_iff _ (IsFractionRing.injective ℚ[X] (RatFunc ℚ))).1 h1.symm
  rwa [Polynomial.reflect_eq_zero_iff] at h2

/-- Restriction after `appLE`. -/
theorem res_appLE {X Y' : Scheme.{0}} (h : X ⟶ Y') {U : Y'.Opens} {D D' : X.Opens}
    (e : D ≤ h ⁻¹ᵁ U) (hDD : D' ≤ D) (s : Γ(Y', U)) :
    res hDD (h.appLE U D e s) = h.appLE U D' (hDD.trans e) s := by
  rw [res, ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]

/-- `appLE` after restriction. -/
theorem appLE_res {X Y' : Scheme.{0}} (h : X ⟶ Y') {U U' : Y'.Opens} {D : X.Opens}
    (hUU : U' ≤ U) (e : D ≤ h ⁻¹ᵁ U') (s : Γ(Y', U)) :
    h.appLE U' D e (res hUU s) = h.appLE U D (e.trans (h.preimage_mono hUU)) s := by
  rw [res, ← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]

/-- Sections over `W = D(g)` are fractions `a / g^n` (helper, by `subst`). -/
theorem loc_helper {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) (g : Γ(X, V))
    (W : X.Opens) (hW : W = X.basicOpen g) (hWV : W ≤ V) (w : Γ(X, W)) :
    ∃ (a : Γ(X, V)) (n : ℕ), w * res hWV (g ^ n) = res hWV a := by
  subst hW
  haveI := hV.isLocalization_basicOpen g
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hw⟩ := IsLocalization.surj (Submonoid.powers g) w
  exact ⟨a, n, hw⟩

end Chart

/-- **`InfFnField` from `ChartFiniteInf` and `ChartIrreducible`** (compiled). -/
theorem infFnField_of (hFI : ChartFiniteInf) (hIrr : ChartIrreducible) : InfFnField := by
  intro Y π hP hS hfin E _ _ _ _ _ hN
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI hirr : IrreducibleSpace Y.left := hIrr Y π hP hS hfin E hN
  obtain ⟨h, hO, himg, hval⟩ := hN
  haveI := hO
  -- the ring `B` and its fraction field `E`
  have hinjQE : Function.Injective (algebraMap ℚ[X] E) := by
    rw [IsScalarTower.algebraMap_eq ℚ[X] (RatFunc ℚ) E]
    exact (algebraMap (RatFunc ℚ) E).injective.comp (IsFractionRing.injective ℚ[X] (RatFunc ℚ))
  have hinjB : Function.Injective (algebraMap ℚ[X] (integralClosure ℚ[X] E)) := by
    intro a b hab
    apply hinjQE
    have := congrArg (fun x : integralClosure ℚ[X] E => (x : E)) hab
    simpa using this
  haveI : Module.IsTorsionFree ℚ[X] E := Module.isTorsionFree_iff_algebraMap_injective.2 hinjQE
  haveI : IsFractionRing (integralClosure ℚ[X] E) E :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℚ[X] (RatFunc ℚ) E _
  set XB : integralClosure ℚ[X] E := algebraMap ℚ[X] (integralClosure ℚ[X] E) X with hXBdef
  have hXB0 : XB ≠ 0 := by
    rw [hXBdef, ne_eq, map_eq_zero_iff _ hinjB]; exact Polynomial.X_ne_zero
  have hXBE : algebraMap (integralClosure ℚ[X] E) E XB = algebraMap ℚ[X] E X := rfl
  -- the chart's range is `U`; `h^* f = X`
  have hrange := range_chart_eq h himg hval
  have htop : h ⁻¹ᵁ π.U = ⊤ := by
    apply top_unique
    intro x _
    show h x ∈ π.U
    have : h x ∈ Set.range h := ⟨x, rfl⟩
    rw [hrange] at this
    exact this
  set rB : Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv XB with hrBdef
  have hres : res htop.ge (h.app π.U π.f) = rB := by
    have hX := app_f_eq h hval htop
    rw [← hXBdef] at hX
    rw [hrBdef, ← hX, Iso.hom_inv_id_apply]
  set D := (Spec (CommRingCat.of (integralClosure ℚ[X] E))).basicOpen rB with hDdef
  have hD : h ⁻¹ᵁ π.V = D := by
    have e1 : h ⁻¹ᵁ π.V = h ⁻¹ᵁ (Y.left.basicOpen π.f) := by
      rw [π.basicOpen_f, Scheme.Hom.preimage_inf, htop, top_inf_eq]
    rw [e1, Scheme.preimage_basicOpen, hDdef, ← hres, res, Scheme.basicOpen_res, top_inf_eq]
  have eV : D ≤ h ⁻¹ᵁ π.V := hD.ge
  have eU : D ≤ h ⁻¹ᵁ π.U := by rw [htop]; exact le_top
  have eUV : D ≤ h ⁻¹ᵁ (π.U ⊓ π.V) := le_inf eU eV
  -- `V` nonempty, `Γ(Y, V)` a domain
  have hVne : (π.V : Set Y.left).Nonempty := by
    let x₀ : PrimeSpectrum (integralClosure ℚ[X] E) := ⟨⊥, inferInstance⟩
    have hx₀ : x₀ ∈ D := by
      have : x₀ ∈ PrimeSpectrum.basicOpen XB := by
        rw [PrimeSpectrum.mem_basicOpen]; exact hXB0
      rw [hDdef, hrBdef, basicOpen_eq_of_affine]
      exact this
    exact ⟨h x₀, eV hx₀⟩
  have hneY : Nonempty Y.left := ⟨h (Nonempty.some inferInstance)⟩
  obtain ⟨hV, hinjV, hfinV⟩ := hFI Y π hP hS hneY hfin
  haveI : IsDomain Γ(Y.left, π.V) := curveSectionsDomain Y π.V hS hirr hV hVne
  -- the map `φ`
  haveI : IsLocalization.Away rB Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), D) :=
    isLocalization_away_of_isAffine rB
  let gB : Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤) →+* E :=
    (algebraMap (integralClosure ℚ[X] E) E).comp
      (Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom.hom
  have hgB : gB rB = algebraMap ℚ[X] E X := by
    show algebraMap _ E ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv XB)) = _
    rw [Iso.inv_hom_id_apply]
    exact hXBE
  have hunit : IsUnit (gB rB) := by
    rw [hgB]; exact (map_ne_zero_iff _ hinjQE).2 Polynomial.X_ne_zero |>.isUnit
  let lam : Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), D) →+* E :=
    IsLocalization.Away.lift rB hunit
  have hlam : ∀ x, lam (algebraMap _ _ x) = gB x := fun x => IsLocalization.lift_eq _ _
  let φ : Γ(Y.left, π.V) →+* E := lam.comp (h.appLE π.V D eV).hom
  -- `φ(g) = 1/X`
  have hfD : h.appLE π.U D eU π.f =
      algebraMap Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤) _ rB := by
    show _ = res (Scheme.basicOpen_le _ rB) rB
    calc h.appLE π.U D eU π.f = res ((Scheme.basicOpen_le _ rB).trans htop.ge) (h.app π.U π.f) :=
          rfl
      _ = res (Scheme.basicOpen_le _ rB) (res htop.ge (h.app π.U π.f)) := (res_res _ _ _).symm
      _ = res (Scheme.basicOpen_le _ rB) rB := by rw [hres]
  have hgf : h.appLE π.V D eV π.g * h.appLE π.U D eU π.f = 1 := by
    have hinv := congrArg (h.appLE (π.U ⊓ π.V) D eUV) π.inv
    rw [map_mul, map_one] at hinv
    have e1 := appLE_res h (inf_le_left : π.U ⊓ π.V ≤ π.U) eUV π.f
    have e2 := appLE_res h (inf_le_right : π.U ⊓ π.V ≤ π.V) eUV π.g
    simp only [e1, e2] at hinv
    rw [mul_comm]
    exact hinv
  have hφg : φ π.g = algebraMap (RatFunc ℚ) E (RatFunc.X : RatFunc ℚ)⁻¹ := by
    have h1 : φ π.g * algebraMap ℚ[X] E X = 1 := by
      rw [← hgB, ← hlam, ← hfD]
      show lam (h.appLE π.V D eV π.g) * lam (h.appLE π.U D eU π.f) = 1
      rw [← map_mul, hgf, map_one]
    rw [map_inv₀, ← RatFunc.algebraMap_X, ← IsScalarTower.algebraMap_apply]
    exact eq_inv_of_mul_eq_one_left h1
  refine ⟨φ, hφg, ?_⟩
  -- injectivity: `ker φ` lies over `0` in `ℚ[s]`
  letI : Algebra InfCoord Γ(Y.left, π.V) := (chartHomInf Y π).toAlgebra
  haveI : Module.Finite InfCoord Γ(Y.left, π.V) := hfinV
  letI := infAlg E
  have hcomp : (φ.comp (chartHomInf Y π) : ℚ[X] →+* E) =
      (algebraMap InfCoord E : ℚ[X] →+* E) := by
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (Subsingleton.elim
        (((φ.comp (chartHomInf Y π) : ℚ[X] →+* E)).comp Polynomial.C)
        (((algebraMap InfCoord E : ℚ[X] →+* E)).comp Polynomial.C)) a
    · show φ (Polynomial.eval₂ (cQ Y π.V) π.g Polynomial.X) =
        algebraMap (RatFunc ℚ) E (Polynomial.eval₂ (algebraMap ℚ (RatFunc ℚ)) (RatFunc.X⁻¹)
          Polynomial.X)
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X, hφg]
  have hinjI : Function.Injective (algebraMap InfCoord E) := by
    show Function.Injective ((algebraMap (RatFunc ℚ) E).comp (algebraMap InfCoord (RatFunc ℚ)))
    exact (algebraMap (RatFunc ℚ) E).injective.comp infCoord_injective
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have hker : (RingHom.ker φ).under InfCoord = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [Ideal.mem_bot]
      have hc' : φ (chartHomInf Y π c) = 0 := hc
      have : (algebraMap InfCoord E) c = 0 := (RingHom.congr_fun hcomp c).symm.trans hc'
      exact (map_eq_zero_iff _ hinjI).1 this
    haveI : Nontrivial InfCoord := inferInstanceAs (Nontrivial ℚ[X])
    have := Ideal.eq_bot_of_under_eq_bot hker
    have ha' : a ∈ RingHom.ker φ := ha
    rw [this] at ha'
    exact ha'
  letI : Algebra Γ(Y.left, π.V) E := φ.toAlgebra
  haveI : FaithfulSMul Γ(Y.left, π.V) E := (faithfulSMul_iff_algebraMap_injective _ _).2 hφinj
  -- fractions
  have hW : h ''ᵁ D = Y.left.basicOpen π.g := by
    rw [← hD, Scheme.Hom.image_preimage_eq_opensRange_inf, π.basicOpen_g]
    have hor : h.opensRange = π.U := by
      ext1; exact hrange
    rw [hor]
  have hWV : h ''ᵁ D ≤ π.V := by rw [hW]; exact Y.left.basicOpen_le π.g
  have heD : D ≤ h ⁻¹ᵁ (h ''ᵁ D) := (Scheme.Hom.preimage_image_eq h D).ge
  have hθsurj : Function.Surjective (h.appLE (h ''ᵁ D) D heD) := by
    rw [← Scheme.Hom.appIso_hom']
    exact (h.appIso D).commRingCatIsoToRingEquiv.surjective
  have hfrac : ∀ b : integralClosure ℚ[X] E, ∃ (a : Γ(Y.left, π.V)) (n : ℕ),
      algebraMap _ E b * φ π.g ^ n = φ a := by
    intro b
    obtain ⟨w', hw'⟩ := hθsurj (algebraMap Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), ⊤)
      Γ(Spec (CommRingCat.of (integralClosure ℚ[X] E)), D)
      ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv b))
    obtain ⟨a, n, han⟩ := loc_helper hV π.g (h ''ᵁ D) hW hWV w'
    refine ⟨a, n, ?_⟩
    have := congrArg (h.appLE (h ''ᵁ D) D heD) han
    rw [map_mul, hw', appLE_res, appLE_res, map_pow] at this
    have h2 := congrArg lam this
    rw [map_mul, map_pow, hlam] at h2
    convert h2 using 2
    show algebraMap _ E b = algebraMap _ E
      ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (integralClosure ℚ[X] E))).inv b))
    rw [Iso.inv_hom_id_apply]
  have hφg0 : φ π.g ≠ 0 := by
    rw [hφg]; exact (map_ne_zero_iff _ (algebraMap (RatFunc ℚ) E).injective).2
      (inv_ne_zero RatFunc.X_ne_zero)
  refine IsFractionRing.of_field Γ(Y.left, π.V) E fun z => ?_
  obtain ⟨b₁, b₂, hb₂, rfl⟩ := IsFractionRing.div_surjective (A := integralClosure ℚ[X] E) z
  obtain ⟨a₁, n₁, h₁⟩ := hfrac b₁
  obtain ⟨a₂, n₂, h₂⟩ := hfrac b₂
  refine ⟨a₁ * π.g ^ n₂, a₂ * π.g ^ n₁, ?_⟩
  show _ = φ (a₁ * π.g ^ n₂) / φ (a₂ * π.g ^ n₁)
  have hb₂' : algebraMap (integralClosure ℚ[X] E) E b₂ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ E)).2 (nonZeroDivisors.ne_zero hb₂)
  rw [map_mul, map_mul, map_pow, map_pow, ← h₁, ← h₂]
  field_simp

/-- **`CurveChartInf` from the three chart Props and `ChartIrreducible`** (compiled). -/
theorem curveChartInf_of_charts' (hP : ChartProper) (hQ : ChartQuasiFinite) (hD : ChartDominant)
    (hIrr : ChartIrreducible) : CurveChartInf :=
  curveChartInf_of_charts hP hQ hD (infFnField_of (chartFiniteInf_of hP hQ hD) hIrr)

end HeckeRestCurve

end


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 3c: `ChartIrreducible` and `ChartDominant` proved

No closed point of a smooth curve is open (its local ring has dimension 1, while an open point has
no proper generization); so a nonempty open subset has infinitely many closed points (Jacobson),
hence infinitely many `ℚ̄`-points. A `π`-fibre is finite, so `π` cannot be `∞` on a nonempty open
set (`ChartIrreducible`: the chart's image is dense; `ChartDominant`: `π⁻¹(𝔸¹) ≠ ∅`), nor take
finitely many values on one (`ChartDominant`: no polynomial relation for `π.f` or `π.g`).
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestCurve

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane PropTSRed TSHecke

/-- **No closed point of a smooth curve is open** (compiled). -/
theorem not_isOpen_closed_point {K : Type} [Field K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f] (x : X)
    (hx : IsClosed ({x} : Set X)) : ¬ IsOpen ({x} : Set X) := by
  intro ho
  obtain ⟨hdim, -⟩ := InfraSmoothDim.stalk_dim_of_smoothOfRelativeDimension f 1 x hx
  haveI hsub : Subsingleton (PrimeSpectrum (X.presheaf.stalk x)) := by
    constructor
    intro p q
    apply (X.fromSpecStalk x).isEmbedding.injective
    have hmem : ∀ r : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x r = x := by
      intro r
      have hr : X.fromSpecStalk x r ∈ Set.range (X.fromSpecStalk x) := ⟨r, rfl⟩
      rw [Scheme.range_fromSpecStalk] at hr
      exact (hr.mem_open ho rfl : X.fromSpecStalk x r ∈ ({x} : Set X))
    rw [hmem p, hmem q]
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 0 := Order.krullDim_nonpos_of_subsingleton
  rw [hdim] at hle
  exact absurd hle (by decide)

/-- **A nonempty open subset of a smooth curve over `ℚ` has infinitely many closed points**
(compiled; Jacobson). -/
theorem infinite_closedPoints_of_isOpen {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℚ))
    [SmoothOfRelativeDimension 1 f] {W : Set X} (hW : IsOpen W) (hne : W.Nonempty) :
    (W ∩ closedPoints X).Infinite := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  intro hfin
  have hclosed : ∀ S ⊆ W ∩ closedPoints X, IsClosed S := by
    intro S hS
    have hSfin : S.Finite := hfin.subset hS
    rw [← Set.biUnion_of_singleton S]
    exact hSfin.isClosed_biUnion fun y hy => (hS hy).2
  have hWF : W ⊆ W ∩ closedPoints X := by
    calc W ⊆ closure W := subset_closure
      _ = closure (W ∩ closedPoints X) :=
          (JacobsonSpace.closure_inter_closedPoints_eq_closure hW.isLocallyClosed).symm
      _ = W ∩ closedPoints X := (hclosed _ le_rfl).closure_eq
  obtain ⟨x, hxW⟩ := hne
  have hxF := hWF hxW
  have hopen : IsOpen ({x} : Set X) := by
    have e : ({x} : Set X) = W ∩ ((W ∩ closedPoints X) \ {x})ᶜ := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff,
        not_and, not_not]
      constructor
      · rintro rfl; exact ⟨hxW, fun _ => rfl⟩
      · rintro ⟨hyW, hy⟩; exact hy (hWF hyW)
    rw [e]
    exact hW.inter (hclosed _ Set.diff_subset).isOpen_compl
  exact not_isOpen_closed_point f x hxF.2 hopen

/-- **A nonempty open subset of a smooth curve over `ℚ` has infinitely many `ℚ̄`-points**
(compiled). -/
theorem infinite_qbar_points {Y : Over (Spec (CommRingCat.of ℚ))}
    (hS : SmoothOfRelativeDimension 1 Y.hom) {W : Set Y.left} (hW : IsOpen W) (hne : W.Nonempty) :
    {y : fieldPt Qbar ⟶ Y | ptOf y.left ∈ W}.Infinite := by
  have hinf := infinite_closedPoints_of_isOpen Y.hom hW hne
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : Infinite ↥(W ∩ closedPoints Y.left) := hinf.to_subtype
  have hch : ∀ z : ↥(W ∩ closedPoints Y.left),
      ∃ y : fieldPt Qbar ⟶ Y, ptOf y.left = z := by
    intro z
    obtain ⟨y, hy⟩ := TSHeckeGal.exists_qbar_point Y.hom z (mem_closedPoints_iff.mp z.2.2)
    exact ⟨Over.homMk y (TSHeckeGal.specQbar_to_specQ_eq' _ _), hy _⟩
  choose F hF using hch
  refine Set.infinite_of_injective_forall_mem (f := F) ?_ ?_
  · intro z₁ z₂ h12
    apply Subtype.ext
    rw [← hF z₁, ← hF z₂, h12]
  · intro z
    show ptOf (F z).left ∈ W
    rw [hF z]
    exact z.2.1

/-- **`ChartIrreducible` holds** (compiled). -/
theorem chartIrreducible : ChartIrreducible := by
  intro Y π hP hS hfin E _ _ _ _ _ hN
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  obtain ⟨h, hO, himg, hval⟩ := hN
  haveI := hO
  have hrange := range_chart_eq h himg hval
  haveI : IrreducibleSpace (Spec (CommRingCat.of (integralClosure ℚ[X] E))) :=
    inferInstanceAs (IrreducibleSpace (PrimeSpectrum (integralClosure ℚ[X] E)))
  have hUirr : IsIrreducible (π.U : Set Y.left) := by
    rw [← hrange, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ h.continuous.continuousOn
  have hdense : closure (π.U : Set Y.left) = Set.univ := by
    by_contra hne
    have hWo : IsOpen (closure (π.U : Set Y.left))ᶜ := isClosed_closure.isOpen_compl
    have hWne : ((closure (π.U : Set Y.left))ᶜ).Nonempty := Set.nonempty_compl.2 hne
    apply infinite_qbar_points hS hWo hWne
    apply (hfin OnePoint.infty).subset
    intro y hy
    show π.val (K := Qbar) y.left = OnePoint.infty
    apply val_of_not_mem
    intro hU
    exact hy (subset_closure hU)
  have := hUirr.closure
  rw [hdense] at this
  exact (irreducibleSpace_def _).2 this

/-- The value of `p(s)` at a `ℚ̄`-point is `p` at the value of `s`. -/
theorem ev_secHom {Y : Over (Spec (CommRingCat.of ℚ))} {W : Y.left.Opens} (s : Γ(Y.left, W))
    (y : Spec (CommRingCat.of Qbar) ⟶ Y.left) (hx : ptOf y ∈ W) (p : ℚ[X]) :
    ev y hx (secHom Y W s p) = Polynomial.eval₂ (algebraMap ℚ Qbar) (ev y hx s) p := by
  rw [secHom, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]
  congr 1
  exact Subsingleton.elim _ _

/-- A value that is a root of a nonzero `p` lies in the finite root set of `p`. -/
theorem mem_roots_of_eval₂ {p : ℚ[X]} (hp : p ≠ 0) {t : Qbar}
    (ht : Polynomial.eval₂ (algebraMap ℚ Qbar) t p = 0) :
    t ∈ (p.map (algebraMap ℚ Qbar)).roots := by
  rw [Polynomial.mem_roots (Polynomial.map_ne_zero hp), Polynomial.IsRoot,
    Polynomial.eval_map]
  exact ht

/-- **`ChartDominant` holds** (compiled). -/
theorem chartDominant : ChartDominant := by
  classical
  intro Y π hP hS hne hfin
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  -- `π` takes the value `∞` on the complement of `U`
  have hUne : (π.U : Set Y.left).Nonempty := by
    by_contra hU
    rw [Set.not_nonempty_iff_eq_empty] at hU
    apply infinite_qbar_points hS isOpen_univ Set.univ_nonempty
    apply (hfin OnePoint.infty).subset
    intro y _
    show π.val (K := Qbar) y.left = OnePoint.infty
    apply val_of_not_mem
    intro hm
    have : ptOf y.left ∈ (π.U : Set Y.left) := hm
    rw [hU] at this
    exact this
  refine ⟨hUne, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    apply infinite_qbar_points hS π.U.isOpen hUne
    apply (Set.Finite.biUnion (Multiset.finite_toSet (p.map (algebraMap ℚ Qbar)).roots)
      (fun t _ => hfin (OnePoint.some t))).subset
    intro y hy
    let y₀ : Spec (CommRingCat.of Qbar) ⟶ Y.left := y.left
    have hy' : ptOf y₀ ∈ π.U := hy
    have h0 := congrArg (ev y₀ hy') hp
    rw [map_zero, ev_secHom] at h0
    refine Set.mem_biUnion (show _ ∈ {t | t ∈ (p.map (algebraMap ℚ Qbar)).roots} from mem_roots_of_eval₂ hp0 h0) ?_
    show π.val (K := Qbar) y₀ = OnePoint.some (ev y₀ hy' π.f)
    exact val_of_mem π y₀ hy'
  · -- `V` is nonempty
    have hVne : (π.V : Set Y.left).Nonempty := by
      by_contra hV
      rw [Set.not_nonempty_iff_eq_empty] at hV
      apply infinite_qbar_points hS isOpen_univ Set.univ_nonempty
      apply (hfin (OnePoint.some 0)).subset
      intro y _
      let y₀ : Spec (CommRingCat.of Qbar) ⟶ Y.left := y.left
      have hyU : ptOf y₀ ∈ π.U := by
        have : ptOf y₀ ∈ π.U ⊔ π.V := by rw [π.cover]; trivial
        rcases this with h | h
        · exact h
        · have : ptOf y₀ ∈ (π.V : Set Y.left) := h
          rw [hV] at this; exact this.elim
      show π.val (K := Qbar) y₀ = OnePoint.some 0
      rw [val_of_mem π y₀ hyU]
      congr 1
      rw [ev_eq_zero_iff, π.basicOpen_f]
      intro h
      have : ptOf y₀ ∈ (π.V : Set Y.left) := h.2
      rw [hV] at this; exact this
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    apply infinite_qbar_points hS π.V.isOpen hVne
    apply ((hfin OnePoint.infty).union (Set.Finite.biUnion
      (Multiset.finite_toSet (p.map (algebraMap ℚ Qbar)).roots)
      (fun t _ => hfin (OnePoint.some t⁻¹)))).subset
    intro y hy
    let y₀ : Spec (CommRingCat.of Qbar) ⟶ Y.left := y.left
    have hy' : ptOf y₀ ∈ π.V := hy
    have h0 := congrArg (ev y₀ hy') hp
    rw [map_zero, ev_secHom] at h0
    by_cases hU : ptOf y₀ ∈ π.U
    · right
      refine Set.mem_biUnion (show _ ∈ {t | t ∈ (p.map (algebraMap ℚ Qbar)).roots} from mem_roots_of_eval₂ hp0 h0) ?_
      show π.val (K := Qbar) y₀ = OnePoint.some (ev y₀ hy' π.g)⁻¹
      rw [val_of_mem π y₀ hU]
      congr 1
      exact eq_inv_of_mul_eq_one_left (ev_f_mul_g π y₀ hU hy')
    · left
      exact val_of_not_mem π y₀ hU

/-! ## `ChartQuasiFinite` from `ChartProper`

Given properness, Mathlib's Stacks 02UP (`exists_isFinite_morphismRestrict_of_finite_preimage_singleton`)
makes a chart finite over a neighbourhood of each closed point of `𝔸¹` with finite fibre; these
neighbourhoods cover `𝔸¹` (Jacobson). A closed fibre is finite: its closed points carry `ℚ̄`-points
with `s`-values among the roots of a generator, finitely many by the finite `π`-fibres, and a
locally closed set whose closed points are finitely many consists of closed points (Jacobson). -/

/-- **The point `secMor w` of `𝔸¹`**: `q` vanishes there iff `q(s)` vanishes at `w` (compiled). -/
theorem mem_secMor_iff {Y : Over (Spec (CommRingCat.of ℚ))} {W : Y.left.Opens} (s : Γ(Y.left, W))
    (w : W.toScheme) (q : ℚ[X]) :
    q ∈ (secMor Y W s w).asIdeal ↔ W.ι w ∉ Y.left.basicOpen (secHom Y W s q) := by
  have key := congrArg (fun O : W.toScheme.Opens => w ∈ O)
    (Scheme.Opens.toSpecΓ_preimage_basicOpen W (secHom Y W s q))
  simp only [eq_iff_iff] at key
  change secHom Y W s q ∈ (W.toSpecΓ w).asIdeal ↔ _
  rw [← not_iff_not, not_not]
  exact key

/-- A `ℚ̄`-point at a point of `W` over a point of `𝔸¹` containing `q`: `q(s(point)) = 0`. -/
theorem eval_eq_zero_of_mem {Y : Over (Spec (CommRingCat.of ℚ))} {W : Y.left.Opens}
    (s : Γ(Y.left, W)) (w : W.toScheme) (q : ℚ[X]) (hq : q ∈ (secMor Y W s w).asIdeal)
    (p : Spec (CommRingCat.of Qbar) ⟶ Y.left) (hp : ptOf p = W.ι w) (hx : ptOf p ∈ W) :
    Polynomial.eval₂ (algebraMap ℚ Qbar) (ev p hx s) q = 0 := by
  rw [← ev_secHom, ev_eq_zero_iff, hp]
  exact (mem_secMor_iff s w q).1 hq

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness is local on the target (instance search needs the transparency option, as in
Mathlib's own uses). -/
theorem isFinite_of_iSup {X Y' : Scheme.{0}} (f : X ⟶ Y') {ι : Type} (U : ι → Y'.Opens)
    (hU : iSup U = ⊤) (H : ∀ i, IsFinite (f ∣_ U i)) : IsFinite f :=
  IsZariskiLocalAtTarget.of_iSup_eq_top U hU H

/-- **A proper chart with finite `ℚ̄`-fibres of `s` is locally quasi-finite** (compiled). -/
theorem lqf_of_proper (Y : Over (Spec (CommRingCat.of ℚ))) (hS : SmoothOfRelativeDimension 1 Y.hom)
    (W : Y.left.Opens) (s : Γ(Y.left, W)) [IsProper (secMor Y W s)]
    (hfinS : ∀ t : Qbar,
      {y : fieldPt Qbar ⟶ Y | ∃ hy : ptOf y.left ∈ W, ev y.left hy s = t}.Finite) :
    LocallyQuasiFinite (secMor Y W s) := by
  haveI : Smooth Y.hom := SmoothOfRelativeDimension.smooth 1 Y.hom
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hclosedfib : ∀ y : Spec (CommRingCat.of ℚ[X]), IsClosed ({y} : Set _) →
      (secMor Y W s ⁻¹' {y}).Finite := by
    intro y hy
    have hmax : y.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).1 hy
    have hne : y.asIdeal ≠ ⊥ := by
      intro h0
      have := hmax
      rw [h0] at this
      exact Polynomial.not_isField ℚ (Ring.isField_iff_maximal_bot.2 this)
    obtain ⟨q₀, hq₀, hq₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    set C : Set Y.left := W.ι '' (secMor Y W s ⁻¹' {y}) with hCdef
    have hC : ∀ z : ↥(C ∩ closedPoints Y.left), ∃ yQ : fieldPt Qbar ⟶ Y, ptOf yQ.left = z ∧
        ∃ hy : ptOf yQ.left ∈ W, ev yQ.left hy s ∈ {t | t ∈ (q₀.map (algebraMap ℚ Qbar)).roots} := by
      intro z
      obtain ⟨⟨w, hw, hwz⟩, hzc⟩ := z.2
      obtain ⟨p, hp⟩ := TSHeckeGal.exists_qbar_point Y.hom z (mem_closedPoints_iff.mp hzc)
      have hpz : ptOf p = z := hp _
      have hx : ptOf p ∈ W := by
        rw [hpz, ← hwz]
        have : W.ι w ∈ Set.range W.ι := ⟨w, rfl⟩
        rwa [Scheme.Opens.range_ι] at this
      refine ⟨Over.homMk p (TSHeckeGal.specQbar_to_specQ_eq' _ _), hpz, hx, ?_⟩
      have hmem : q₀ ∈ (secMor Y W s w).asIdeal := by
        have hw' : secMor Y W s w = y := hw
        rw [hw']; exact hq₀
      exact mem_roots_of_eval₂ hq₀ne
        (eval_eq_zero_of_mem s w q₀ hmem p (hpz.trans hwz.symm) hx)
    choose F hF using hC
    have hCfin : (C ∩ closedPoints Y.left).Finite := by
      by_contra hinf
      haveI : Infinite ↥(C ∩ closedPoints Y.left) := Set.infinite_coe_iff.2 hinf
      apply Set.infinite_of_injective_forall_mem (f := F)
        (s := ⋃ t ∈ {t | t ∈ (q₀.map (algebraMap ℚ Qbar)).roots},
          {y : fieldPt Qbar ⟶ Y | ∃ hy : ptOf y.left ∈ W, ev y.left hy s = t})
      · intro z₁ z₂ h12
        apply Subtype.ext
        rw [← (hF z₁).1, ← (hF z₂).1, h12]
      · intro z
        obtain ⟨-, hx, hroot⟩ := hF z
        exact Set.mem_biUnion hroot ⟨hx, rfl⟩
      · exact (Multiset.finite_toSet _).biUnion fun t _ => hfinS t
    have hClc : IsLocallyClosed C :=
      (hy.preimage (secMor Y W s).continuous).isLocallyClosed.image
        W.ι.isOpenEmbedding.isInducing W.ι.isOpenEmbedding.isOpen_range.isLocallyClosed
    have hCF : C ⊆ C ∩ closedPoints Y.left := by
      have hcl : IsClosed (C ∩ closedPoints Y.left) := by
        rw [← Set.biUnion_of_singleton (C ∩ closedPoints Y.left)]
        exact hCfin.isClosed_biUnion fun z hz => hz.2
      calc C ⊆ closure C := subset_closure
        _ = closure (C ∩ closedPoints Y.left) :=
            (JacobsonSpace.closure_inter_closedPoints_eq_closure hClc).symm
        _ = C ∩ closedPoints Y.left := hcl.closure_eq
    exact Set.Finite.of_finite_image (hCfin.subset hCF) W.ι.isOpenEmbedding.injective.injOn
  haveI : JacobsonSpace (Spec (CommRingCat.of ℚ[X])) :=
    inferInstanceAs (JacobsonSpace (PrimeSpectrum ℚ[X]))
  choose Vy hyV hVfin using fun (y : {y : Spec (CommRingCat.of ℚ[X]) // IsClosed ({y} : Set _)}) =>
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton (secMor Y W s) y.1
      (hclosedfib y.1 y.2)
  have hsup : iSup Vy = ⊤ := by
    by_contra hne
    have hSne : (SetLike.coe (iSup Vy))ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      intro h
      apply hne
      apply SetLike.coe_injective
      rw [h, TopologicalSpace.Opens.coe_top]
    obtain ⟨y₀, hy₀, hy₀c⟩ := nonempty_inter_closedPoints hSne
      (iSup Vy).isOpen.isClosed_compl.isLocallyClosed
    apply hy₀
    exact (le_iSup Vy ⟨y₀, mem_closedPoints_iff.mp hy₀c⟩) (hyV ⟨y₀, mem_closedPoints_iff.mp hy₀c⟩)
  haveI : IsFinite (secMor Y W s) := isFinite_of_iSup (secMor Y W s) Vy hsup hVfin
  infer_instance

/-- **`ChartQuasiFinite` from `ChartProper`** (compiled). -/
theorem chartQuasiFinite_of_proper (hP : ChartProper) : ChartQuasiFinite := by
  intro Y π h1 h2 h4
  obtain ⟨hPU, hPV⟩ := hP Y π h1 h2 h4
  constructor
  · refine lqf_of_proper Y h2 π.U π.f fun t => (h4 (OnePoint.some t)).subset ?_
    rintro y ⟨hy, hyt⟩
    show π.val (K := Qbar) y.left = OnePoint.some t
    rw [val_of_mem π y.left hy, hyt]
  · refine lqf_of_proper Y h2 π.V π.g fun t =>
      ((h4 OnePoint.infty).union (h4 (OnePoint.some t⁻¹))).subset ?_
    rintro y ⟨hy, hyt⟩
    let y₀ : Spec (CommRingCat.of Qbar) ⟶ Y.left := y.left
    by_cases hU : ptOf y₀ ∈ π.U
    · right
      show π.val (K := Qbar) y₀ = OnePoint.some t⁻¹
      rw [val_of_mem π y₀ hU]
      congr 1
      have hfg := ev_f_mul_g π y₀ hU hy
      have hyt' : ev y₀ hy π.g = t := hyt
      rw [hyt'] at hfg
      exact eq_inv_of_mul_eq_one_left hfg
    · left
      exact val_of_not_mem π y₀ hU

/-- **`CurveNormChart` from `ChartProper` alone** (compiled). -/
theorem curveNormChart_of_proper (hP : ChartProper) : CurveNormChart :=
  curveNormChart_of_charts hP (chartQuasiFinite_of_proper hP) chartDominant

/-- **`CurveChartInf` from `ChartProper` alone** (compiled). -/
theorem curveChartInf_of_proper (hP : ChartProper) : CurveChartInf :=
  curveChartInf_of_charts' hP (chartQuasiFinite_of_proper hP) chartDominant chartIrreducible

/-- **`CurveNormChart` from `ChartProper` and `ChartQuasiFinite`** (compiled). -/
theorem curveNormChart_of_pq (hP : ChartProper) (hQ : ChartQuasiFinite) : CurveNormChart :=
  curveNormChart_of_charts hP hQ chartDominant

/-- **`CurveChartInf` from `ChartProper` and `ChartQuasiFinite`** (compiled). -/
theorem curveChartInf_of_pq (hP : ChartProper) (hQ : ChartQuasiFinite) : CurveChartInf :=
  curveChartInf_of_charts' hP hQ chartDominant chartIrreducible

end HeckeRestCurve

end


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest, Part 3d: `ChartProper` proved (valuative criterion)

`secMor Y W s : W → 𝔸¹` is locally of finite type, separated and quasi-compact by cancellation
from `W → Y → Spec ℚ` (all morphisms to `Spec ℚ` agree). For the existence part of the valuative
criterion (Mathlib's `IsProper.of_valuativeCriterion`, Stacks 0BX5): a valuation-ring point of
`𝔸¹` with a `Frac`-point of `W` lifts to `Y` (properness of `Y`); if its closed point left `W`, the
whole point would lie in `W'` (the other chart), and the pull-back `G` of `s'` would be a non-unit
of the valuation ring, while `s · s' = 1` at the generic point with `s` integral there.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestCurve

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin LeafQM.AV.Pin.ImagePlane PropTSRed TSHecke

/-- **Any two morphisms to `Spec ℚ` agree** (compiled). -/
theorem toSpecQ_eq {X : Scheme.{0}} (a b : X ⟶ Spec (CommRingCat.of ℚ)) : a = b := by
  have key : ∀ c : X ⟶ Spec (CommRingCat.of ℚ),
      c = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ c.appTop) := by
    intro c
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key a, key b]
  congr 2
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- `W → 𝔸¹ → Spec ℚ` is `W → Y → Spec ℚ`. -/
theorem secMor_comp (Y : Over (Spec (CommRingCat.of ℚ))) (W : Y.left.Opens) (s : Γ(Y.left, W)) :
    secMor Y W s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])) = W.ι ≫ Y.hom :=
  toSpecQ_eq _ _

/-- **The value of `s` at a field point of `W` over `Spec ρ`** is `ρ X` (compiled). -/
theorem ev_secMor {K : Type} [Field K] {Y : Over (Spec (CommRingCat.of ℚ))} {W : Y.left.Opens}
    (s : Γ(Y.left, W)) (q : Spec (CommRingCat.of K) ⟶ W.toScheme)
    (ρ : CommRingCat.of ℚ[X] ⟶ CommRingCat.of K) (h : q ≫ secMor Y W s = Spec.map ρ)
    (hx : ptOf (q ≫ W.ι) ∈ W) : ev (q ≫ W.ι) hx s = ρ X := by
  have e1 := ev_spec_top ρ X
  rw [← h, ev_comp] at e1
  have e2 : (secMor Y W s).app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of ℚ[X])).inv X) =
      W.topIso.inv s := by
    change (secMor Y W s).appTop _ = _
    rw [secMor, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    have e : (Spec.map (CommRingCat.ofHom (secHom Y W s))).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℚ[X])).inv X) =
        (Scheme.ΓSpecIso Γ(Y.left, W)).inv (secHom Y W s X) := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
      rfl
    rw [e, Scheme.Opens.toSpecΓ_appTop, CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    show W.topIso.inv (Polynomial.eval₂ (cQ Y W) s X) = _
    rw [Polynomial.eval₂_X]
  rw [e2] at e1
  rw [ev_comp, ← e1]
  have e3 : W.ι.app W s = W.toScheme.presheaf.map (homOfLE (le_top : W.ι ⁻¹ᵁ W ≤ ⊤)).op
      (W.topIso.inv s) := by
    have hmor : ∀ {U₁ U₂ U₃ : (Y.left.Opens)ᵒᵖ} (a : U₁ ⟶ U₂) (b : U₂ ⟶ U₃) (c : U₁ ⟶ U₃),
        Y.left.presheaf.map a ≫ Y.left.presheaf.map b = Y.left.presheaf.map c := by
      intro U₁ U₂ U₃ a b c
      rw [← Functor.map_comp]
      exact congrArg _ (Subsingleton.elim _ _)
    change Y.left.presheaf.map _ s = Y.left.presheaf.map _ (Y.left.presheaf.map _ s)
    first
    | (erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl)
    | (simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl)
    | (erw [← ConcreteCategory.comp_apply, hmor])
  rw [e3]
  exact ev_res _ _ _ _

/-- **The existence part of the valuative criterion for a chart** (compiled). -/
theorem secMor_existence (Y : Over (Spec (CommRingCat.of ℚ))) [IsProper Y.hom]
    (W W' : Y.left.Opens) (s : Γ(Y.left, W)) (s' : Γ(Y.left, W')) (hcov : W ⊔ W' = ⊤)
    (hinv : ∀ (K : Type) [Field K] (p : Spec (CommRingCat.of K) ⟶ Y.left) (hW : ptOf p ∈ W)
      (hW' : ptOf p ∈ W'), ev p hW s * ev p hW' s' = 1)
    (hbo : Y.left.basicOpen s' = W ⊓ W') :
    ValuativeCriterion.Existence (secMor Y W s) := by
  intro S
  obtain ⟨ρ, hρ⟩ : ∃ ρ : CommRingCat.of ℚ[X] ⟶ CommRingCat.of S.R, S.i₂ = Spec.map ρ :=
    ⟨Spec.preimage S.i₂, (Spec.map_preimage _).symm⟩
  let alg : CommRingCat.of S.R ⟶ CommRingCat.of S.K := CommRingCat.ofHom (algebraMap S.R S.K)
  have halg : Function.Injective (algebraMap S.R S.K) := IsFractionRing.injective S.R S.K
  let S' : ValuativeCommSq Y.hom :=
    { R := S.R, K := S.K, i₁ := S.i₁ ≫ W.ι,
      i₂ := S.i₂ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])),
      commSq := ⟨toSpecQ_eq _ _⟩ }
  have hYv : ValuativeCriterion Y.hom := by
    have h : (ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType)
        Y.hom := by
      rw [← IsProper.eq_valuativeCriterion]; infer_instance
    exact h.1.1.1
  obtain ⟨⟨l', hl1, hl2⟩⟩ := (hYv.existence S').exists_lift
  have hl1' : Spec.map alg ≫ l' = S.i₁ ≫ W.ι := hl1
  -- the value of `s` at the generic point
  have hxW : ptOf (S.i₁ ≫ W.ι) ∈ W := by
    rw [ptOf_comp]
    have : W.ι (ptOf S.i₁) ∈ Set.range W.ι := ⟨_, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  have hsq : S.i₁ ≫ secMor Y W s = Spec.map (ρ ≫ alg) := by
    rw [Spec.map_comp, ← hρ]; exact S.commSq.w
  have hsval : ev (S.i₁ ≫ W.ι) hxW s = algebraMap S.R S.K (ρ X) :=
    ev_secMor s S.i₁ (ρ ≫ alg) hsq hxW
  -- the closed point stays in `W`
  have hc : l' (IsLocalRing.closedPoint S.R) ∈ W := by
    by_contra hcW
    have hcW' : l' (IsLocalRing.closedPoint S.R) ∈ W' := by
      have : l' (IsLocalRing.closedPoint S.R) ∈ W ⊔ W' := by rw [hcov]; trivial
      rcases this with h | h
      · exact absurd h hcW
      · exact h
    have hall : ∀ x, l' x ∈ W' := fun x =>
      ((IsLocalRing.specializes_closedPoint x).map l'.continuous).mem_open W'.isOpen hcW'
    have pre : l' ⁻¹ᵁ W' = ⊤ := top_unique fun x _ => hall x
    set G : S.R := (Scheme.ΓSpecIso (CommRingCat.of S.R)).hom (res pre.ge (l'.app W' s')) with hGdef
    have hGinv : (Scheme.ΓSpecIso (CommRingCat.of S.R)).inv G = res pre.ge (l'.app W' s') := by
      rw [hGdef, Iso.hom_inv_id_apply]
    have hG : G ∈ IsLocalRing.maximalIdeal S.R := by
      have h1 : l' (IsLocalRing.closedPoint S.R) ∉ Y.left.basicOpen s' := by
        rw [hbo]; exact fun h => hcW h.1
      have h2 : IsLocalRing.closedPoint S.R ∉ (Spec (CommRingCat.of S.R)).basicOpen
          (l'.app W' s') := by
        rw [← Scheme.preimage_basicOpen]; exact h1
      have h3 : IsLocalRing.closedPoint S.R ∉ (Spec (CommRingCat.of S.R)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of S.R)).inv G) := by
        rw [hGinv, res, Scheme.basicOpen_res, top_inf_eq]; exact h2
      rw [basicOpen_eq_of_affine] at h3
      by_contra hn
      exact h3 ((PrimeSpectrum.mem_basicOpen _ _).2 hn)
    -- the value of `s'` at the generic point
    have hxW' : ptOf (S.i₁ ≫ W.ι) ∈ W' := by
      rw [← hl1', ptOf_comp]; exact hall _
    have hs'val : ev (S.i₁ ≫ W.ι) hxW' s' = algebraMap S.R S.K G := by
      have hx2 : ptOf (Spec.map alg ≫ l') ∈ W' := by rw [ptOf_comp]; exact hall _
      have e : ev (Spec.map alg ≫ l') hx2 s' = algebraMap S.R S.K G := by
        rw [ev_comp, ← ev_res _ pre.ge (show ptOf (Spec.map alg) ∈
          (⊤ : (Spec (CommRingCat.of S.R)).Opens) from trivial), ← hGinv, ev_spec_top]
        rfl
      have hgen : ∀ (p : Spec (CommRingCat.of S.K) ⟶ Y.left) (hp : p = S.i₁ ≫ W.ι)
          (h1 : ptOf p ∈ W') (h2 : ptOf (S.i₁ ≫ W.ι) ∈ W'), ev p h1 s' = ev (S.i₁ ≫ W.ι) h2 s' := by
        rintro _ rfl _ _; rfl
      rw [← hgen _ hl1' hx2 hxW', e]
    have hprod := hinv S.K (S.i₁ ≫ W.ι) hxW hxW'
    rw [hsval, hs'val, ← map_mul, ← map_one (algebraMap S.R S.K)] at hprod
    have h1 : ρ X * G = 1 := halg hprod
    have hunit : IsUnit G := ⟨⟨G, ρ X, by rw [mul_comm]; exact h1, h1⟩, rfl⟩
    exact (IsLocalRing.mem_maximalIdeal _).1 hG hunit
  have hrange : Set.range l' ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint x).map l'.continuous).mem_open W.isOpen hc
  let l := IsOpenImmersion.lift W.ι l' hrange
  have hfl : Spec.map alg ≫ l = S.i₁ := by
    rw [← cancel_mono W.ι, Category.assoc, IsOpenImmersion.lift_fac]
    exact hl1'
  have hfr : l ≫ secMor Y W s = S.i₂ := by
    have h1 : Spec.map alg ≫ (l ≫ secMor Y W s) = Spec.map alg ≫ S.i₂ := by
      rw [← Category.assoc, hfl]; exact S.commSq.w
    rw [hρ] at h1 ⊢
    rw [← Spec.map_preimage (l ≫ secMor Y W s)] at h1 ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    have h2 := Spec.map_injective h1
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    apply halg
    exact congrArg (fun φ : CommRingCat.of ℚ[X] ⟶ CommRingCat.of S.K => φ.hom a) h2
  exact ⟨⟨⟨l, hfl, hfr⟩⟩⟩

/-- **A chart is proper** (compiled). -/
theorem secMor_isProper (Y : Over (Spec (CommRingCat.of ℚ))) [IsProper Y.hom]
    (W W' : Y.left.Opens) (s : Γ(Y.left, W)) (s' : Γ(Y.left, W')) (hcov : W ⊔ W' = ⊤)
    (hinv : ∀ (K : Type) [Field K] (p : Spec (CommRingCat.of K) ⟶ Y.left) (hW : ptOf p ∈ W)
      (hW' : ptOf p ∈ W'), ev p hW s * ev p hW' s' = 1)
    (hbo : Y.left.basicOpen s' = W ⊓ W') : IsProper (secMor Y W s) := by
  haveI : LocallyOfFiniteType Y.hom := inferInstance
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have e := secMor_comp Y W s
  haveI : LocallyOfFiniteType
      (secMor Y W s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X]))) := by
    rw [e]; infer_instance
  haveI : IsSeparated (secMor Y W s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X]))) := by
    rw [e]; infer_instance
  haveI : QuasiCompact (secMor Y W s ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X]))) := by
    rw [e]; infer_instance
  haveI : LocallyOfFiniteType (secMor Y W s) :=
    locallyOfFiniteType_of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])))
  haveI : IsSeparated (secMor Y W s) :=
    IsSeparated.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])))
  haveI : QuasiCompact (secMor Y W s) :=
    QuasiCompact.of_comp _ (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])))
  exact IsProper.of_valuativeCriterion _
    (ValuativeCriterion.iff.2 ⟨secMor_existence Y W W' s s' hcov hinv hbo,
      IsSeparated.valuativeCriterion _⟩)

/-- **`ChartProper` holds** (compiled). -/
theorem chartProper : ChartProper := by
  intro Y π hP hS hfin
  haveI := hP
  refine ⟨secMor_isProper Y π.U π.V π.f π.g π.cover ?_ π.basicOpen_g,
    secMor_isProper Y π.V π.U π.g π.f (by rw [sup_comm]; exact π.cover) ?_
      (by rw [π.basicOpen_f, inf_comm])⟩
  · intro K _ p hU hV
    exact ev_f_mul_g π p hU hV
  · intro K _ p hV hU
    rw [mul_comm]
    exact ev_f_mul_g π p hU hV

/-- **`CurveNormChart` is a theorem** (compiled; with ts-hecke's `curveGaloisChart_of`,
`CurveGaloisChart` follows). -/
theorem curveNormChart : CurveNormChart := curveNormChart_of_proper chartProper

/-- **`CurveChartInf` is a theorem** (compiled). -/
theorem curveChartInf : CurveChartInf := curveChartInf_of_proper chartProper

end HeckeRestCurve

end


/-! ════════════════════════════════════════════════════════════════════════════════════════════
# hecke-rest: the composite

ts-hecke's `CoverModelOfHecke` and `PropTSAll` composites with hecke-rest's reductions of its four
glue inputs: `CurveNormChart` (hence `CurveGaloisChart`) and `CurveChartInf` from the chart Props,
`HeckeFibreSizes` from three leaves on QM pairs, `HeckeNoVertRam` from `HeckeVertWitness`.
════════════════════════════════════════════════════════════════════════════════════════════ -/

noncomputable section

namespace HeckeRestAll

open CategoryTheory AlgebraicGeometry Limits Polynomial
open LeafQM LeafQM.AV LeafQM.AV.Pin G0ModField PropTSRed PropTSGlue PkgI3 TSHecke

/-- **ts-hecke's glue Prop `CurveGaloisChart` is a theorem** (compiled; `curveGaloisChart_of` of
ts-hecke applied to hecke-rest's `curveNormChart`). -/
theorem curveGaloisChart : CurveGaloisChart := curveGaloisChart_of HeckeRestCurve.curveNormChart

/-- **`CoverModelOfHecke` from hecke-rest's inputs** (compiled). Leaves: `Y3Connected`,
`R1R2fp`, `TorsionStructure` (as in ts-hecke), `QMAutCard`, `SerreRigidity3`, `ALFixedPoints`
(new). Glue: `HeckeVertWitness` (one unramified vertical prime: Lemma NV / good reduction). -/
theorem coverModelOfHecke_of_heckeRest (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hV : HeckeRestNV.HeckeVertWitness) : CoverModelOfHecke :=
  coverModelOfHecke_of_tsHecke' hconn hRR hT HeckeRestCurve.curveNormChart
    HeckeRestCurve.curveChartInf (HeckeRest.heckeFibreSizes_of' hT hA hS hW)
    (HeckeRestNV.heckeNoVertRam_of_witness hV)

/-- **`CoverModelOfHecke` from hecke-rest's inputs, local-ring form** (compiled): as
`coverModelOfHecke_of_heckeRest` with `HeckeVertLocal` (local-ring witnesses, the shape of the
good-reduction input) in place of `HeckeVertWitness`. -/
theorem coverModelOfHecke_of_heckeRest' (hconn : Y3Connected) (hRR : R1R2fp)
    (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hV : HeckeRestNV.HeckeVertLocal) : CoverModelOfHecke :=
  coverModelOfHecke_of_tsHecke' hconn hRR hT HeckeRestCurve.curveNormChart
    HeckeRestCurve.curveChartInf (HeckeRest.heckeFibreSizes_of' hT hA hS hW)
    (HeckeRestNV.heckeNoVertRam_of_local hV)

/-- **`PropTSAll` from hecke-rest's inputs** (compiled; through ts-hecke's `propTSAll_of_tsHecke'`
and prop-ts-glue's `propTSAll_final`). -/
theorem propTSAll_of_heckeRest (t2 : PkgI2.AbhyankarDVR.{0}) (hR : R1R2fp) (hM : Pin.MobiusGlue)
    (hSN : SNSpecialize) (hC : KummerCompositum)
    (hKA : KummerAbhyankarFinGlue) (hO : KummerOtherBranchFin) (hVF : KummerVerticalFin)
    (hAI : KummerAbhyankarInfGlue) (hOI : KummerOtherBranchInf) (hVI : KummerVerticalInf)
    (hconn : Y3Connected) (hT : ObjBridge.TorsionStructure)
    (hA : HeckeRest.QMAutCard) (hS : HeckeRest.SerreRigidity3) (hW : HeckeRest.ALFixedPoints)
    (hV : HeckeRestNV.HeckeVertWitness) : PropTSAll :=
  propTSAll_of_tsHecke' t2 hR hM hSN hC hKA hO hVF hAI hOI hVI hconn hT
    HeckeRestCurve.curveNormChart
    HeckeRestCurve.curveChartInf
    (HeckeRest.heckeFibreSizes_of' hT hA hS hW) (HeckeRestNV.heckeNoVertRam_of_witness hV)

end HeckeRestAll

end


