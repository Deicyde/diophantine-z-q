import Mathlib

/-!
# Lane RC10 (Heegner algebra), part 8: contraction transfer, the 3-arrow identity and witnesses

Manuscript `diophantine_zq.tex` (11/5), proof of Proposition `ex:arith-finite-heegner`,
tex lines 3337–3358 (contraction transfer and the homotopy identities) and paragraph 8
"Actual finite Selmer-cone witnesses", tex 3372–3406 ((H22) and the transport of witnesses).

Setting: a preadditive category with a chosen endomorphism `d X : X ⟶ X` of every object (the
differentials; no grading or `d² = 0` is needed for these identities).  A retained contraction of
`X` onto a small model `U` is `(i, p, h)` with `i, p` chain maps and `1 - i p = d h + h d`.
Composition is written diagrammatically: the manuscript's `p_w F i_v` is `i_v ≫ F ≫ p_w`.

All statements are `PROVED`.  The choice of comparison maps between the small tame resolution and
the continuous bar resolution, and the existence of the contractions, are inputs (tex 3337–3342,
3403–3405), as the manuscript says.
-/

namespace ZInQ.Manuscript.RC.HeegnerAlgebra

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C] (d : ∀ X : C, X ⟶ X)

/-- A retained contraction `(i, p, h)` of `X` onto `U` with `1 - i p = d h + h d`
(tex 3343), in diagrammatic order `𝟙 - p ≫ i = h ≫ d + d ≫ h`; `i` and `p` are chain maps. -/
structure Contraction (U X : C) where
  /-- inclusion of the small model -/
  i : U ⟶ X
  /-- projection to the small model -/
  p : X ⟶ U
  /-- the homotopy -/
  h : X ⟶ X
  i_chain : i ≫ d X = d U ≫ i
  p_chain : p ≫ d U = d X ≫ p
  htpy : 𝟙 X - p ≫ i = h ≫ d X + d X ≫ h

variable {d}
variable {Uv Uw Uz Uu Xv Xw Xz Xu : C}

/-- The transferred arrow `F_L = p_w F i_v` (tex 3344). -/
def arrowL (cv : Contraction d Uv Xv) (cw : Contraction d Uw Xw) (F : Xv ⟶ Xw) : Uv ⟶ Uw :=
  cv.i ≫ F ≫ cw.p

/-- The transferred composition homotopy `K(G,F) = p_z G h_w F i_v` (tex 3346–3351). -/
def Khom (cv : Contraction d Uv Xv) (cw : Contraction d Uw Xw) (cz : Contraction d Uz Xz)
    (F : Xv ⟶ Xw) (G : Xw ⟶ Xz) : Uv ⟶ Uz :=
  cv.i ≫ F ≫ cw.h ≫ G ≫ cz.p

/-- The degree-minus-two map `L(H,G,F) = p_u H h_z G h_w F i_v` (tex 3351). -/
def Lhom (cv : Contraction d Uv Xv) (cw : Contraction d Uw Xw) (cz : Contraction d Uz Xz)
    (cu : Contraction d Uu Xu) (F : Xv ⟶ Xw) (G : Xw ⟶ Xz) (H : Xz ⟶ Xu) : Uv ⟶ Uu :=
  cv.i ≫ F ≫ cw.h ≫ G ≫ cz.h ≫ H ≫ cu.p

omit [Preadditive C] in
/-- Reassociated form of a chain-map identity. -/
private theorem chain_reassoc {X Y Z : C} (F : X ⟶ Y) (hF : F ≫ d Y = d X ≫ F) (k : Y ⟶ Z) :
    F ≫ d Y ≫ k = d X ≫ F ≫ k := by
  rw [← Category.assoc, hF, Category.assoc]

/-- `p ≫ i = 𝟙 - (h ≫ d + d ≫ h)` for a contraction. -/
private theorem pi_eq {U X : C} (c : Contraction d U X) : c.p ≫ c.i = 𝟙 X - (c.h ≫ d X + d X ≫ c.h) := by
  rw [← c.htpy]; abel

/-- Reassociated form of `pi_eq`. -/
private theorem pi_eq_assoc {U X Z : C} (c : Contraction d U X) (k : X ⟶ Z) :
    c.p ≫ c.i ≫ k = k - (c.h ≫ d X ≫ k + d X ≫ c.h ≫ k) := by
  rw [← Category.assoc, pi_eq]
  simp only [Preadditive.sub_comp, Preadditive.add_comp, Category.id_comp, Category.assoc]

/-- tex 3344–3345, `PROVED`: the inclusion square commutes up to the homotopy `h_w F i_v`:
`F i_v - i_w F_L = d (h_w F i_v) + (h_w F i_v) d`. -/
theorem inclusion_square (cv : Contraction d Uv Xv) (cw : Contraction d Uw Xw) (F : Xv ⟶ Xw)
    (hF : F ≫ d Xw = d Xv ≫ F) :
    cv.i ≫ F - arrowL cv cw F ≫ cw.i =
      (cv.i ≫ F ≫ cw.h) ≫ d Xw + d Uv ≫ (cv.i ≫ F ≫ cw.h) := by
  simp only [arrowL, Category.assoc, pi_eq, Preadditive.comp_sub, Preadditive.comp_add,
    Category.comp_id]
  rw [chain_reassoc F hF, chain_reassoc cv.i cv.i_chain]
  abel

/-- tex 3346–3348, `PROVED`: the composition homotopy:
`(GF)_L - G_L F_L = d K(G,F) + K(G,F) d`. -/
theorem two_arrow (cv : Contraction d Uv Xv) (cw : Contraction d Uw Xw) (cz : Contraction d Uz Xz)
    (F : Xv ⟶ Xw) (G : Xw ⟶ Xz) (hF : F ≫ d Xw = d Xv ≫ F) (hG : G ≫ d Xz = d Xw ≫ G) :
    arrowL cv cz (F ≫ G) - arrowL cv cw F ≫ arrowL cw cz G =
      Khom cv cw cz F G ≫ d Uz + d Uv ≫ Khom cv cw cz F G := by
  simp only [arrowL, Khom, Category.assoc, pi_eq_assoc, Preadditive.comp_sub,
    Preadditive.comp_add]
  rw [← chain_reassoc G hG, ← cz.p_chain, chain_reassoc F hF, chain_reassoc cv.i cv.i_chain]
  abel

/-- tex 3350–3355, `PROVED`: the 3-arrow identity
`K(H,GF) - K(HG,F) + H_L K(G,F) - K(H,G) F_L = L d - d L`, with the printed sign. -/
theorem three_arrow (cv : Contraction d Uv Xv) (cw : Contraction d Uw Xw)
    (cz : Contraction d Uz Xz) (cu : Contraction d Uu Xu) (F : Xv ⟶ Xw) (G : Xw ⟶ Xz)
    (H : Xz ⟶ Xu) (hF : F ≫ d Xw = d Xv ≫ F) (hG : G ≫ d Xz = d Xw ≫ G)
    (hH : H ≫ d Xu = d Xz ≫ H) :
    Khom cv cz cu (F ≫ G) H - Khom cv cw cu F (G ≫ H) + Khom cv cw cz F G ≫ arrowL cz cu H -
        arrowL cv cw F ≫ Khom cw cz cu G H =
      d Uv ≫ Lhom cv cw cz cu F G H - Lhom cv cw cz cu F G H ≫ d Uu := by
  simp only [arrowL, Khom, Lhom, Category.assoc, pi_eq_assoc, Preadditive.comp_sub,
    Preadditive.comp_add]
  rw [← chain_reassoc H hH, ← cu.p_chain, ← chain_reassoc G hG, chain_reassoc F hF,
    chain_reassoc cv.i cv.i_chain]
  abel

/-! ## Witnesses (H22) and their transport (tex 3372–3406) -/

/-- tex 3395–3397, `PROVED`: a retained contraction carries a relation `z - z' = d q` to
`p z - p z' = d (p q)` (generalized elements `T ⟶ X`). -/
theorem witness_project {T U X : C} (c : Contraction d U X) (z z' q : T ⟶ X)
    (hq : z - z' = q ≫ d X) : z ≫ c.p - z' ≫ c.p = (q ≫ c.p) ≫ d U := by
  rw [← Preadditive.sub_comp, hq, Category.assoc, ← c.p_chain, Category.assoc]

/-- tex 3397–3399, `PROVED`: for a comparison `F` to another model with projection `p'`, and a
cycle `z`, the correction between `p' F z` and `p' F i p z` is the boundary of `p' F h z`. -/
theorem witness_compare {T U X Y U' : C} (c : Contraction d U X) (F : X ⟶ Y) (p' : Y ⟶ U')
    (hF : F ≫ d Y = d X ≫ F) (hp' : p' ≫ d U' = d Y ≫ p') (z : T ⟶ X) (hz : z ≫ d X = 0) :
    z ≫ F ≫ p' - z ≫ c.p ≫ c.i ≫ F ≫ p' = (z ≫ c.h ≫ F ≫ p') ≫ d U' := by
  simp only [Category.assoc, pi_eq_assoc, Preadditive.comp_sub, Preadditive.comp_add]
  have h0 : z ≫ d X ≫ c.h ≫ F ≫ p' = 0 := by
    rw [← Category.assoc, hz, Limits.zero_comp]
  rw [h0, ← chain_reassoc F hF, ← hp']
  abel

/-- The degree-one piece of `Cone(C^•(G_{K,S}, M) ⊕ ⊕ U_v → ⊕ C^•(K_v, M))[-1]`: an entry
`(x, y)` with `x = (p, (u_v))` in degree one of the source and `y = (q_v)` in degree zero of the
target; the cone differential is `(x, y) ↦ (d x, f x - d y)`. -/
def coneD {X1 X2 Y0 Y1 : Type*} [AddCommGroup X1] [AddCommGroup X2] [AddCommGroup Y0]
    [AddCommGroup Y1] (dX : X1 →+ X2) (dY : Y0 →+ Y1) (f : X1 →+ Y1) (xy : X1 × Y0) : X2 × Y1 :=
  (dX xy.1, f xy.1 - dY xy.2)

/-- (H22), tex 3373–3383, `PROVED`: with `x = (p, u)`, `f(p, u) = loc p - ι u`, the entry
`((p, u), q)` is a cycle in the Selmer cone iff `p` and the `u_v` are cocycles and
`loc_v p - ι_v u_v = d q_v` for every constrained place. -/
theorem H22_cycle {P Pu P2 Pu2 Y0 Y1 : Type*} [AddCommGroup P] [AddCommGroup Pu] [AddCommGroup P2]
    [AddCommGroup Pu2] [AddCommGroup Y0] [AddCommGroup Y1] (dP : P →+ P2) (dU : Pu →+ Pu2)
    (dY : Y0 →+ Y1) (loc : P →+ Y1) (ι : Pu →+ Y1) (p : P) (u : Pu) (q : Y0) :
    coneD ((dP.comp (AddMonoidHom.fst P Pu)).prod (dU.comp (AddMonoidHom.snd P Pu))) dY
        (loc.comp (AddMonoidHom.fst P Pu) - ι.comp (AddMonoidHom.snd P Pu)) ((p, u), q) = 0 ↔
      dP p = 0 ∧ dU u = 0 ∧ loc p - ι u = dY q := by
  simp only [coneD, AddMonoidHom.prod_apply, AddMonoidHom.comp_apply, AddMonoidHom.coe_fst,
    AddMonoidHom.coe_snd, AddMonoidHom.sub_apply, Prod.mk_eq_zero, Prod.mk_eq_zero, sub_eq_zero]
  tauto

end ZInQ.Manuscript.RC.HeegnerAlgebra
