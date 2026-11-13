import ZInQKernel.Contrib.RLeaf.X1RationalCusp
import ZInQKernel.Contrib.RLeaf.T36Torsion

/-!
# t40-igusa: Igusa transitivity from Igusa's theorem (`SL₂(ℤ/N)` in the Galois image)

`ZInQ.RLeaf.IgusaTransitive` (the `x`-coordinates of the points of exact order `N` on `E_j` form
one `Gal(\overline{ℚ(j)}/ℚ(j))`-orbit) is the corollary of Igusa's theorem that the Galois image
on `E_j[N]` contains `SL₂(ℤ/N)`, combined with the fact (proved here) that `SL₂(ℤ/N)` acts
transitively on the vectors of exact order `N` in `(ℤ/N)²`.

* `IgusaSL2X` (the named leaf, published): for some basis `e : (ℤ/N)² ≃ E_j[N]`, every
  `g ∈ SL₂(ℤ/N)` is realised on `x`-coordinates by some `σ ∈ Aut(\overline{ℚ(j)}/ℚ(j))`.
* `IgusaGL2` (Igusa's theorem as usually stated, on points, for every basis and every
  `g ∈ GL₂(ℤ/N)`): it implies `IgusaSL2X` (`igusaSL2X_of_igusaGL2`, using leaf T36 for a basis).

Proved: `exists_det_eq_one_of_addOrderOf` (a vector of order `N` is the first column of a matrix
in `SL₂(ℤ/N)`), `igusaTransitive_of_igusaSL2X : IgusaSL2X → IgusaTransitive`,
`igusaSL2X_of_igusaGL2`, `igusaTransitive_of_igusaGL2`.
-/

namespace ZInQ.RLeaf

open LeafModCurves WeierstrassCurve X1Belyi

/-! ## Linear algebra over `ℤ/N` -/

/-- **A vector of exact order `N` in `(ℤ/N)²` is the first column of a matrix of determinant `1`.**
If `u = (a, b)` has order `N`, then `gcd(a, b, N) = 1` (else `(N/g) • u = 0`), and Bézout gives
`c, d` with `a d - b c = 1`. -/
theorem exists_det_eq_one_of_addOrderOf {N : ℕ} (hN : 0 < N) (u : ZMod N × ZMod N)
    (hu : addOrderOf u = N) : ∃ c d : ZMod N, u.1 * d - u.2 * c = 1 := by
  have : NeZero N := ⟨hN.ne'⟩
  set a : ℕ := u.1.val
  set b : ℕ := u.2.val
  have ha : ((a : ℕ) : ZMod N) = u.1 := ZMod.natCast_zmod_val _
  have hb : ((b : ℕ) : ZMod N) = u.2 := ZMod.natCast_zmod_val _
  set g : ℕ := Nat.gcd (Nat.gcd a b) N with hg
  have hgN : g ∣ N := Nat.gcd_dvd_right _ _
  have hga : g ∣ a := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have hgb : g ∣ b := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right _ hN
  -- `(N / g) • u = 0`
  have hzero : (N / g) • u = 0 := by
    have key : ∀ x : ℕ, g ∣ x → (N / g) • ((x : ℕ) : ZMod N) = 0 := by
      intro x hx
      obtain ⟨k, rfl⟩ := hx
      rw [nsmul_eq_mul, ← Nat.cast_mul]
      have : N / g * (g * k) = N * k := by
        rw [← mul_assoc, Nat.div_mul_cancel hgN]
      rw [this, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    ext
    · simp only [Prod.smul_fst, Prod.fst_zero]
      rw [← ha]; exact key a hga
    · simp only [Prod.smul_snd, Prod.snd_zero]
      rw [← hb]; exact key b hgb
  have hdvd : N ∣ N / g := by
    have := addOrderOf_dvd_of_nsmul_eq_zero hzero
    rwa [hu] at this
  have hNg : 0 < N / g := Nat.div_pos (Nat.le_of_dvd hN hgN) hgpos
  have hle : N ≤ N / g := Nat.le_of_dvd hNg hdvd
  have hg1 : g = 1 := by
    by_contra hne
    have h2 : 2 ≤ g := by omega
    have : N / g < N := Nat.div_lt_self hN (by omega)
    omega
  -- Bézout
  have hb1 := Nat.gcd_eq_gcd_ab (Nat.gcd a b) N
  have hb2 := Nat.gcd_eq_gcd_ab a b
  rw [← hg, hg1] at hb1
  set s := Nat.gcdA (Nat.gcd a b) N
  set t := Nat.gcdB (Nat.gcd a b) N
  set x := Nat.gcdA a b
  set y := Nat.gcdB a b
  refine ⟨-((y * s : ℤ) : ZMod N), ((x * s : ℤ) : ZMod N), ?_⟩
  have hcast := congrArg (fun z : ℤ => (z : ZMod N)) hb1
  simp only [Nat.cast_one, Int.cast_one] at hcast
  rw [hcast, hb2]
  push_cast
  rw [ZMod.natCast_self, ha, hb]
  ring

/-! ## The leaves -/

/-- The action of a `2 × 2` matrix on column vectors `(x, y) ∈ (ℤ/N)²`. -/
def matAct {N : ℕ} (g : Matrix (Fin 2) (Fin 2) (ZMod N)) (v : ZMod N × ZMod N) :
    ZMod N × ZMod N :=
  (g 0 0 * v.1 + g 0 1 * v.2, g 1 0 * v.1 + g 1 1 * v.2)

/-- The Galois action `σ ↦ (P ↦ σ P)` on the points of `E_j` over `\overline{ℚ(j)}`. -/
noncomputable abbrev galPt (σ : Kbar ≃ₐ[Qj] Kbar) : EjBar.toAffine.Point →+ EjBar.toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := Ej) σ.toAlgHom

/-- **Igusa's theorem, geometric part, on `x`-coordinates** (published; the named leaf).
For every `N > 0` there is a `ℤ/N`-basis `e : (ℤ/N)² ≃ E_j[N]` of the `N`-torsion of the generic
elliptic curve `E_j` over `\overline{ℚ(j)}` such that every `g ∈ SL₂(ℤ/N)` is realised on
`x`-coordinates by an automorphism of `\overline{ℚ(j)}` over `ℚ(j)`:
`σ(x(e v)) = x(e (g v))` for all `v ∈ (ℤ/N)²`.

Source: Igusa, *Fibre systems of Jacobian varieties III*, Amer. J. Math. 81 (1959) 453-476
(`Gal(ℚ(j)(E_j[N])/ℚ(j)) ≅ GL₂(ℤ/N)`); Shimura, *Introduction to the arithmetic theory of
automorphic functions* (1971), Thm 6.6 (`F_N = ℚ(j, f_a)` is Galois over `ℚ(j)` with group
`GL₂(ℤ/N)/{±1}`, acting by `f_a ↦ f_{aα}` on the Fricke functions `f_a`, which are
`ℚ(j)^×`-affine images of the `x`-coordinates of the `N`-torsion points); Lang, *Elliptic
functions*, Ch. 6, §3 (theorem numbers UNVERIFIED). This statement is the `SL₂` part on
`x`-coordinates, implied by each of these (see `igusaSL2X_of_igusaGL2`). -/
def IgusaSL2X : Prop :=
  ∀ N : ℕ, 0 < N → ∃ e : (ZMod N × ZMod N) ≃+ nTors EjBar N,
    ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod N), ∃ σ : Kbar ≃ₐ[Qj] Kbar,
      ∀ v : ZMod N × ZMod N,
        σ (xCoord (e v : EjBar.toAffine.Point)) = xCoord (e (matAct g v) : EjBar.toAffine.Point)

/-- **Igusa's theorem** (published), as usually stated: the Galois representation of
`Gal(\overline{ℚ(j)}/ℚ(j))` on `E_j[N]` is surjective onto `GL₂(ℤ/N)`, in every basis.

Source: Igusa, Amer. J. Math. 81 (1959); Lang, *Elliptic functions*, Ch. 6, §3; for any model of
the generic curve over `ℚ(j)` (numbers UNVERIFIED). The geometric image is `SL₂(ℤ/N)` for every
model, because the monodromy of a family over the `j`-line maps onto `PSL₂(ℤ)` and `PSL₂(ℤ)` does
not lift to `SL₂(ℤ)`; the determinant is the cyclotomic character, onto `(ℤ/N)^×` over `ℚ(j)`. -/
def IgusaGL2 : Prop :=
  ∀ N : ℕ, 0 < N → ∀ (e : (ZMod N × ZMod N) ≃+ nTors EjBar N)
    (g : GL (Fin 2) (ZMod N)), ∃ σ : Kbar ≃ₐ[Qj] Kbar,
      ∀ v : ZMod N × ZMod N,
        galPt σ (e v : EjBar.toAffine.Point) = (e (matAct (g : Matrix (Fin 2) (Fin 2) (ZMod N)) v) :
          EjBar.toAffine.Point)

/-! ## The glue -/

/-- `matAct` of the matrix with first column `u` sends `(1, 0)` to `u`. -/
theorem matAct_first_column {N : ℕ} (a b c d : ZMod N) :
    matAct !![a, c; b, d] ((1 : ZMod N), (0 : ZMod N)) = (a, b) := by
  simp [matAct]

/-- **Transitivity of `SL₂(ℤ/N)`**: every vector of exact order `N` is `g (1, 0)` for some
`g ∈ SL₂(ℤ/N)`. -/
theorem exists_SL2_first_column {N : ℕ} (hN : 0 < N) (u : ZMod N × ZMod N)
    (hu : addOrderOf u = N) : ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod N),
      matAct g ((1 : ZMod N), (0 : ZMod N)) = u := by
  obtain ⟨c, d, hcd⟩ := exists_det_eq_one_of_addOrderOf hN u hu
  refine ⟨⟨!![u.1, c; u.2, d], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; rw [mul_comm c]; exact hcd
  · show matAct !![u.1, c; u.2, d] _ = u
    rw [matAct_first_column]

/-- The coordinate vector of a point of order `N` of `E_j[N]` has order `N`. -/
theorem addOrderOf_symm {N : ℕ} (e : (ZMod N × ZMod N) ≃+ nTors EjBar N)
    (P : EjBar.toAffine.Point) (hP : P ∈ nTors EjBar N) :
    addOrderOf (e.symm ⟨P, hP⟩) = addOrderOf P := by
  rw [AddEquiv.addOrderOf_eq, AddSubgroup.addOrderOf_mk]

/-- A point of order `N` lies in `E_j[N]`. -/
theorem mem_nTors_of_addOrderOf {N : ℕ} {P : EjBar.toAffine.Point} (hP : addOrderOf P = N) :
    P ∈ nTors EjBar N := by
  show N • P = 0
  rw [← hP]; exact addOrderOf_nsmul_eq_zero P

/-- **Igusa transitivity from Igusa's theorem (`SL₂` part, on `x`-coordinates).** -/
theorem igusaTransitive_of_igusaSL2X (h : IgusaSL2X) : IgusaTransitive := by
  intro N P P' hN hP hP'
  obtain ⟨e, he⟩ := h N hN
  have hPm := mem_nTors_of_addOrderOf hP
  have hP'm := mem_nTors_of_addOrderOf hP'
  obtain ⟨g, hg⟩ := exists_SL2_first_column hN (e.symm ⟨P, hPm⟩)
    ((addOrderOf_symm e P hPm).trans hP)
  obtain ⟨g', hg'⟩ := exists_SL2_first_column hN (e.symm ⟨P', hP'm⟩)
    ((addOrderOf_symm e P' hP'm).trans hP')
  obtain ⟨σ, hσ⟩ := he g
  obtain ⟨σ', hσ'⟩ := he g'
  refine ⟨σ.symm.trans σ', ?_⟩
  have h1 := hσ ((1 : ZMod N), (0 : ZMod N))
  have h2 := hσ' ((1 : ZMod N), (0 : ZMod N))
  rw [hg, AddEquiv.apply_symm_apply] at h1
  rw [hg', AddEquiv.apply_symm_apply] at h2
  simp only at h1 h2
  rw [AlgEquiv.trans_apply, ← h1, AlgEquiv.symm_apply_apply, h2]

/-- **Igusa's theorem (`GL₂`, points) implies its `SL₂` part on `x`-coordinates.** A basis of
`E_j[N]` comes from leaf T36 (`t36_torsionStructure`). -/
theorem igusaSL2X_of_igusaGL2 (h : IgusaGL2) : IgusaSL2X := by
  intro N hN
  obtain ⟨e⟩ := t36_torsionStructure Kbar EjBar N hN
  refine ⟨e.symm, fun g => ?_⟩
  obtain ⟨σ, hσ⟩ := h N hN e.symm (Matrix.SpecialLinearGroup.toGL g)
  refine ⟨σ, fun v => ?_⟩
  exact (xCoord_map σ _).symm.trans (congrArg xCoord (hσ v))

/-- **Igusa transitivity from Igusa's theorem.** -/
theorem igusaTransitive_of_igusaGL2 (h : IgusaGL2) : IgusaTransitive :=
  igusaTransitive_of_igusaSL2X (igusaSL2X_of_igusaGL2 h)

end ZInQ.RLeaf

#print axioms ZInQ.RLeaf.exists_det_eq_one_of_addOrderOf
#print axioms ZInQ.RLeaf.igusaTransitive_of_igusaSL2X
#print axioms ZInQ.RLeaf.igusaSL2X_of_igusaGL2
#print axioms ZInQ.RLeaf.igusaTransitive_of_igusaGL2
