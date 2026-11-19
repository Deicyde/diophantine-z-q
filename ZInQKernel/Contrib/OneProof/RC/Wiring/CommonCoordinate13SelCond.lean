import ZInQKernel.Contrib.OneProof.RC.SelmerComplex.ChangeCondition
import ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate11Selmer

/-!
# Change of local conditions along per-place split inclusions: the Selmer split and its quotient

Manuscript `diophantine_zq.tex`, "Actual support comparisons", tex 3494–3498: "Replacing the
unramified condition by the full condition then gives the singular quotient by a cone of Selmer
cones." Nekovář, *Selmer complexes*, Astérisque 310 (2006), 6.4.2(i) (functoriality of `C_f` in
morphisms of local conditions, with `λ = id`).

For local conditions `Δ`, `Δ'` on the same genuine Selmer data (lane RC26's `selData`) and
per-place split inclusions `Es v : U_v ⊂ U'_v` (`SplitInclusion`, complements `W_v`) compatible
with the condition maps only propositionally (`i'_v ∘ i_v = i_v`, the hypothesis `compat`: the
source data need not be definitionally a restriction of the target data):

* `condMid Δ' n`: the middle inclusion `w ↦ (0, w, 0)` of `∏_v U'_v` into `C(Δ')`;
* `selSplitOfCond Δ Δ' Es compat`: the comparison `condMap : C(Δ) → C(Δ')`,
  `(a, u, x) ↦ (a, i u, x)`, is a split inclusion of Selmer complexes with complement
  `(0, ∏_v W_v, 0)` (`selSplitOfCond_i`: its map is `condMap`; `selSplitOfCond_Qc`: its
  complement, both by definition); no finiteness of the set of places is used;
* `CondInclusion.ofSplits Es compat`: the underlying termwise injective morphism of local
  conditions; `changeIncl_ofSplits`: its comparison map is the map of the split (definitional);
* `selSplitOfCond_quotEquiv`, `selSplitOfCond_quotEquiv_d`: the quotient complex of the Selmer
  split is the product of the local quotient complexes, `(0, w, 0) ↦ (w_v)_v`, compatibly with
  the differentials.

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Wiring

open ZInQ.Manuscript.RC.Limits ZInQ.Contrib.CloudB3RC53.PairedFunctional
open ZInQ.Manuscript.RC.SelmerComplex (LocalConditions selData condMap piCx piMap CondInclusion
  changeIncl)

section SelCond

variable {k : Type} [CommRing k]
  {GS : Type} [Group GS] [TopologicalSpace GS] [IsTopologicalGroup GS]
  {ι : Type} {Gv : ι → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)]
  [∀ v, IsTopologicalGroup (Gv v)] {loc : ∀ v, Gv v →ₜ* GS}
  {M : Type} [AddCommGroup M] [Module k M] [DistribMulAction GS M] [SMulCommClass GS k M]
  [TopologicalSpace M] [ContinuousAdd M] [ContinuousConstSMul k M] [ContinuousSMul GS M]
  (Δ Δ' : LocalConditions k GS Gv loc M) (Es : ∀ v, SplitInclusion (Δ.U v) (Δ'.U v))
  (compat : ∀ v (n : ℤ) (x : (Δ.U v).X n),
    (Δ'.i v).f n n rfl ((Es v).i.f n n rfl x) = (Δ.i v).f n n rfl x)

/-- The middle inclusion `w ↦ (0, w, 0)` of `∏_v U'_v` into the Selmer complex `C(Δ')`, through
which the complement of the change of condition is taken (tex 3494–3498: "Replacing the
unramified condition by the full condition then gives the singular quotient"; Nekovář 6.4.2(i)).
Kind: definition. -/
def condMid (n : ℤ) : (∀ v, (Δ'.U v).X n) →ₗ[k] (selCx (selData k GS Gv loc M Δ')).X n :=
  selMid (selData k GS Gv loc M Δ') n

/-- `condMid w = (0, w, 0)` (tex 3494–3498: "Replacing the unramified condition by the full
condition then gives the singular quotient"; Nekovář 6.4.2(i)). Kind: PROVED. -/
theorem condMid_apply (n : ℤ) (w : ∀ v, (Δ'.U v).X n) :
    condMid Δ' n w = (((0 : (selData k GS Gv loc M Δ').G.X n), w,
      (0 : (selData k GS Gv loc M Δ').L.X (n - 1))) : selT (selData k GS Gv loc M Δ') n) :=
  rfl

/-- **The comparison of Selmer complexes along per-place split inclusions is a split inclusion**
(tex 3494–3498: "Replacing the unramified condition by the full condition then gives the singular
quotient"; Nekovář 6.4.2(i)): the map `condMap Δ Δ' (fun v => (Es v).i) compat : C(Δ) → C(Δ')`,
`(a, u, x) ↦ (a, i u, x)`, with complement in degree `n` the image of
`Submodule.pi Set.univ (fun v => (Es v).Qc n)` under the middle inclusion `u ↦ (0, u, 0)`.
Injectivity and complementarity are checked componentwise (no finiteness of the places).
Kind: definition. -/
def selSplitOfCond :
    SplitInclusion (selCx (selData k GS Gv loc M Δ)) (selCx (selData k GS Gv loc M Δ')) where
  i := condMap Δ Δ' (fun v => (Es v).i) compat
  inj n := by
    intro c c' h
    have h' : ((c.1, (piMap fun v => (Es v).i).f n n rfl c.2.1, c.2.2) :
        selT (selData k GS Gv loc M Δ') n) =
          (c'.1, (piMap fun v => (Es v).i).f n n rfl c'.2.1, c'.2.2) := h
    have h1 : c.1 = c'.1 := congrArg (fun t : selT (selData k GS Gv loc M Δ') n => t.1) h'
    have h2 : (piMap fun v => (Es v).i).f n n rfl c.2.1 =
        (piMap fun v => (Es v).i).f n n rfl c'.2.1 :=
      congrArg (fun t : selT (selData k GS Gv loc M Δ') n => t.2.1) h'
    have h3 : c.2.2 = c'.2.2 :=
      congrArg (fun t : selT (selData k GS Gv loc M Δ') n => t.2.2) h'
    have hu : c.2.1 = c'.2.1 := funext fun v => (Es v).inj n (congrFun h2 v)
    exact Prod.ext h1 (Prod.ext hu h3)
  Qc n := (Submodule.pi Set.univ fun v => (Es v).Qc n).map (condMid Δ' n)
  compl n := by
    refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      rintro y ⟨c, rfl⟩ hy
      obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 hy
      have e : (((0 : (selData k GS Gv loc M Δ').G.X n), w,
          (0 : (selData k GS Gv loc M Δ').L.X (n - 1))) : selT (selData k GS Gv loc M Δ') n) =
            (c.1, (piMap fun v => (Es v).i).f n n rfl c.2.1, c.2.2) := hwy
      have e1 := congrArg Prod.fst e
      have e2 : w = (piMap fun v => (Es v).i).f n n rfl c.2.1 :=
        congrArg (fun t : selT (selData k GS Gv loc M Δ') n => t.2.1) e
      have e3 := congrArg (fun t : selT (selData k GS Gv loc M Δ') n => t.2.2) e
      have hw0 : ∀ v, w v = 0 := fun v => by
        have hd := ((Es v).compl n).disjoint
        rw [Submodule.disjoint_def] at hd
        exact hd (w v) ⟨c.2.1 v, (congrFun e2 v).symm⟩ (Submodule.mem_pi.1 hw v (Set.mem_univ v))
      have e2' : (piMap fun v => (Es v).i).f n n rfl c.2.1 = 0 := e2.symm.trans (funext hw0)
      change ((c.1, (piMap fun v => (Es v).i).f n n rfl c.2.1, c.2.2) :
        selT (selData k GS Gv loc M Δ') n) = 0
      exact Prod.ext e1.symm (Prod.ext e2' e3.symm)
    · rw [codisjoint_iff, eq_top_iff]
      intro c _
      refine Submodule.mem_sup.2 ⟨(condMap Δ Δ' (fun v => (Es v).i) compat).f n n rfl
        ((c.1, fun v => (Es v).coordP n (c.2.1 v), c.2.2) : selT (selData k GS Gv loc M Δ) n),
        ⟨_, rfl⟩, condMid Δ' n fun v => ((Es v).coordQ n (c.2.1 v) : (Δ'.U v).X n),
        Submodule.mem_map_of_mem (Submodule.mem_pi.2 fun v _ => ((Es v).coordQ n (c.2.1 v)).2),
        ?_⟩
      exact Prod.ext (add_zero c.1)
        (Prod.ext (funext fun v => (Es v).decompose n (c.2.1 v)) (add_zero c.2.2))

/-- The map of the Selmer split is the comparison `condMap` of the change of condition
(tex 3494–3498: "Replacing the unramified condition by the full condition then gives the singular
quotient"; Nekovář 6.4.2(i)). Kind: PROVED. -/
theorem selSplitOfCond_i :
    (selSplitOfCond Δ Δ' Es compat).i = condMap Δ Δ' (fun v => (Es v).i) compat :=
  rfl

/-- The complement of the Selmer split is the image of the product of the local complements
under the middle inclusion (tex 3494–3498: "Replacing the unramified condition by the full
condition then gives the singular quotient"; Nekovář 6.4.2(i)). Kind: PROVED. -/
theorem selSplitOfCond_Qc (n : ℤ) :
    (selSplitOfCond Δ Δ' Es compat).Qc n =
      (Submodule.pi Set.univ fun v => (Es v).Qc n).map (condMid Δ' n) :=
  rfl

omit [IsTopologicalGroup GS] in
variable {Δ Δ'} in
/-- **The termwise injective morphism of local conditions underlying per-place split inclusions**
(tex 3494–3498: "Replacing the unramified condition by the full condition then gives the singular
quotient"; Nekovář 6.4.2(i)): the maps `(Es v).i`, the compatibility `compat` and the
injectivity of the splits. Kind: definition. -/
def CondInclusion.ofSplits : CondInclusion Δ Δ' where
  φ v := (Es v).i
  compat := compat
  inj v := (Es v).inj

/-- The comparison map of the change of condition `CondInclusion.ofSplits Es compat` is the map
of the Selmer split (tex 3494–3498: "Replacing the unramified condition by the full condition then
gives the singular quotient"; Nekovář 6.4.2(i)). Kind: PROVED. -/
theorem changeIncl_ofSplits :
    changeIncl (CondInclusion.ofSplits Es compat) = (selSplitOfCond Δ Δ' Es compat).i :=
  rfl

/-- **The quotient of the Selmer split is the product of the local quotients**, degreewise:
`(0, w, 0) ↦ (w_v)_v` (tex 3494–3498: "Replacing the unramified condition by the full condition
then gives the singular quotient"; Nekovář 6.4.2(i)). Kind: definition. -/
def selSplitOfCond_quotEquiv (n : ℤ) :
    (selSplitOfCond Δ Δ' Es compat).quotientCx.X n ≃ₗ[k]
      (piCx fun v => (Es v).quotientCx).X n where
  toFun y v := ⟨y.1.2.1 v, by
    obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.1 y.2
    rw [← hwy]
    exact Submodule.mem_pi.1 hw v (Set.mem_univ v)⟩
  map_add' y y' := rfl
  map_smul' r y := rfl
  invFun q := ⟨condMid Δ' n fun v => (q v).1,
    Submodule.mem_map_of_mem (Submodule.mem_pi.2 fun v _ => (q v).2)⟩
  left_inv y := by
    obtain ⟨y, hy⟩ := y
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
    rfl
  right_inv q := rfl

/-- `selSplitOfCond_quotEquiv` on an element `(0, w, 0)` of the complement is `(w_v)_v`
(tex 3494–3498: "Replacing the unramified condition by the full condition then gives the singular
quotient"; Nekovář 6.4.2(i)). Kind: PROVED. -/
theorem selSplitOfCond_quotEquiv_apply (n : ℤ) (y : (selSplitOfCond Δ Δ' Es compat).quotientCx.X n)
    (v : ι) : ((selSplitOfCond_quotEquiv Δ Δ' Es compat n y v).1 : (Δ'.U v).X n) = y.1.2.1 v :=
  rfl

/-- **The quotient differentials correspond** (tex 3494–3498: "Replacing the unramified condition
by the full condition then gives the singular quotient"; Nekovář 6.4.2(i)): the quotient
differential of the Selmer split is the product of the local quotient differentials,
`d_Q (0, w, 0) = (0, (d_{Q_v} w_v)_v, 0)`. Kind: PROVED. -/
theorem selSplitOfCond_quotEquiv_d (a b : ℤ) (h : a + 1 = b)
    (x : (selSplitOfCond Δ Δ' Es compat).quotientCx.X a) :
    (piCx fun v => (Es v).quotientCx).d a b h (selSplitOfCond_quotEquiv Δ Δ' Es compat a x) =
      selSplitOfCond_quotEquiv Δ Δ' Es compat b
        ((selSplitOfCond Δ Δ' Es compat).quotientCx.d a b h x) := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hy
  have hw' : ∀ v, w v ∈ (Es v).Qc a := fun v => Submodule.mem_pi.1 hw v (Set.mem_univ v)
  let wq : ∀ v, (Es v).Qc a := fun v => ⟨w v, hw' v⟩
  let dq : ∀ v, (Δ'.U v).X b := fun v => ((Es v).dQ a b h (wq v) : (Δ'.U v).X b)
  have hmem : condMid Δ' b dq ∈ (selSplitOfCond Δ Δ' Es compat).Qc b :=
    Submodule.mem_map_of_mem (Submodule.mem_pi.2 fun v _ => ((Es v).dQ a b h (wq v)).2)
  let x : (selCx (selData k GS Gv loc M Δ)).X b :=
    ((0 : (selData k GS Gv loc M Δ).G.X b),
      (fun v => (Es v).offDiag a b h (wq v) : ∀ v, (Δ.U v).X b),
      -((selData k GS Gv loc M Δ').ι.f a (b - 1) (by omega) w))
  have hd : (selCx (selData k GS Gv loc M Δ')).d a b h (condMid Δ' a w) =
      (selSplitOfCond Δ Δ' Es compat).i.f b b rfl x +
        ((⟨condMid Δ' b dq, hmem⟩ : (selSplitOfCond Δ Δ' Es compat).Qc b) :
          (selCx (selData k GS Gv loc M Δ')).X b) := by
    have hU : ((piCx Δ'.U).d a b h w : ∀ v, (Δ'.U v).X b) =
        (fun v => (Es v).i.f b b rfl ((Es v).offDiag a b h (wq v))) + dq :=
      funext fun v => (Es v).d_Q a b h (wq v)
    change (((selData k GS Gv loc M Δ').G.d a b h 0, (piCx Δ'.U).d a b h w,
        (selData k GS Gv loc M Δ').res.f a (b - 1) (by omega) 0 -
          (selData k GS Gv loc M Δ').ι.f a (b - 1) (by omega) w -
            (selData k GS Gv loc M Δ').L.d (a - 1) (b - 1) (by omega) 0) :
              selT (selData k GS Gv loc M Δ') b) =
      (((0 : (selData k GS Gv loc M Δ').G.X b),
          (fun v => (Es v).i.f b b rfl ((Es v).offDiag a b h (wq v)) : ∀ v, (Δ'.U v).X b),
          -((selData k GS Gv loc M Δ').ι.f a (b - 1) (by omega) w)) :
            selT (selData k GS Gv loc M Δ') b) +
        (((0 : (selData k GS Gv loc M Δ').G.X b), (dq : ∀ v, (Δ'.U v).X b),
          (0 : (selData k GS Gv loc M Δ').L.X (b - 1))) : selT (selData k GS Gv loc M Δ') b)
    rw [map_zero, map_zero, map_zero, zero_sub, sub_zero]
    exact Prod.ext (add_zero 0).symm (Prod.ext hU (add_zero _).symm)
  have hQ : (selSplitOfCond Δ Δ' Es compat).dQ a b h ⟨condMid Δ' a w, hy⟩ =
      ⟨condMid Δ' b dq, hmem⟩ := by
    change (selSplitOfCond Δ Δ' Es compat).coordQ b
      ((selCx (selData k GS Gv loc M Δ')).d a b h (condMid Δ' a w)) = _
    rw [hd, map_add, SplitInclusion.coordQ_i, zero_add, SplitInclusion.coordQ_Q]
  change (fun v => (Es v).dQ a b h (wq v)) =
    selSplitOfCond_quotEquiv Δ Δ' Es compat b
      ((selSplitOfCond Δ Δ' Es compat).dQ a b h ⟨condMid Δ' a w, hy⟩)
  rw [hQ]
  rfl

end SelCond

end ZInQ.Manuscript.RC.Wiring
