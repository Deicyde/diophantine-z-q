import ZInQKernel.Contrib.CloudB3RC53.Torsion.Nakayama

/-!
# Torsion, part 11: cones over a commutative ring, and derived Nakayama for comparisons

Lemma `ex:arith-local-kummer`, tex L3452–3453: "Reduction modulo two … gives the perfect
quotient-to-dual comparison; derived Nakayama lifts it." `Nakayama.lean` proves derived Nakayama
for one based complex. The project's mapping cone `BasedCx.cone` (`Cone.lean`) is stated over a
field. This file gives the cone over any commutative ring and the comparison form:

* `ChainMapR`, `BasedCx.coneR`: chain maps of based complexes and their mapping cone over a
  commutative ring (the same formulas as `ChainMapB`, `BasedCx.cone`).
* `ChainMapR.map`, `coneR_map` (PROVED): coefficient change commutes with the cone.
* **`nakayama_comparison` (PROVED)**: for a chain map `f` of based complexes over a local ring, if
  the cone of the reduced map `f mod 𝔪` is contractible (the reduced comparison is a homotopy
  equivalence), then the cone of `f` is contractible (`f` is a homotopy equivalence).
* Non-vacuity: `nakayama_comparison_example` — over any local ring, the map `R --(1 + x)--> R`
  between one-dimensional complexes in degree zero, `x ∈ 𝔪`, reduces to the identity, and its cone
  is contractible.

**Classification.** PROVED.
-/

namespace ZInQ.Contrib.CloudB3RC53.Torsion

open Matrix

variable {R : Type*} [CommRing R]
  {κe κo κe' κo' : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  [Fintype κe'] [Fintype κo'] [DecidableEq κe'] [DecidableEq κo']

/-- **A degree-preserving chain map** of based complexes over a commutative ring. -/
structure ChainMapR (C : BasedCx R κe κo) (D : BasedCx R κe' κo') where
  fE : Matrix κe' κe R
  fO : Matrix κo' κo R
  deg_fE : HasDeg fE D.degE C.degE 0
  deg_fO : HasDeg fO D.degO C.degO 0
  commOE : D.dOE * fE = fO * C.dOE
  commEO : D.dEO * fO = fE * C.dEO

variable {C : BasedCx R κe κo} {D : BasedCx R κe' κo'}

/-- **The mapping cone** over a commutative ring, `cone^n = D^n ⊕ C^{n+1}`,
`d(d, c) = (d_D d + f c, −d_C c)`. -/
def BasedCx.coneR (f : ChainMapR C D) : BasedCx R (κe' ⊕ κo) (κo' ⊕ κe) where
  degE := Sum.elim D.degE (fun c => C.degO c + -1)
  degO := Sum.elim D.degO (fun c => C.degE c + -1)
  even_degE := by rintro (i | i); exacts [D.even_degE i, (C.odd_degO i).add_odd odd_neg_one]
  odd_degO := by rintro (i | i); exacts [D.odd_degO i, (C.even_degE i).add_odd odd_neg_one]
  dOE := fromBlocks D.dOE f.fO 0 (-C.dEO)
  dEO := fromBlocks D.dEO f.fE 0 (-C.dOE)
  dd_E := by
    rw [fromBlocks_multiply]
    simp [D.dd_E, C.dd_O, f.commEO]
  dd_O := by
    rw [fromBlocks_multiply]
    simp [D.dd_O, C.dd_E, f.commOE]
  deg_dOE := by
    rintro (i | i) (j | j) h
    · exact D.deg_dOE i j h
    · have := f.deg_fO i j h; change D.degO i = C.degO j + -1 + 1; omega
    · exact absurd rfl h
    · have := C.deg_dEO i j (by simpa using h); change C.degE i + -1 = C.degO j + -1 + 1; omega
  deg_dEO := by
    rintro (i | i) (j | j) h
    · exact D.deg_dEO i j h
    · have := f.deg_fE i j h; change D.degE i = C.degE j + -1 + 1; omega
    · exact absurd rfl h
    · have := C.deg_dOE i j (by simpa using h); change C.degO i + -1 = C.degE j + -1 + 1; omega

/-- **Coefficient change of a chain map.** -/
def ChainMapR.map {S : Type*} [CommRing S] (π : R →+* S) (f : ChainMapR C D) :
    ChainMapR (C.map π) (D.map π) where
  fE := f.fE.map π
  fO := f.fO.map π
  deg_fE i j h := f.deg_fE i j fun h0 => h (by simp [h0])
  deg_fO i j h := f.deg_fO i j fun h0 => h (by simp [h0])
  commOE := by
    change D.dOE.map π * f.fE.map π = f.fO.map π * C.dOE.map π
    rw [← Matrix.map_mul, ← Matrix.map_mul, f.commOE]
  commEO := by
    change D.dEO.map π * f.fO.map π = f.fE.map π * C.dEO.map π
    rw [← Matrix.map_mul, ← Matrix.map_mul, f.commEO]

omit [DecidableEq κe] [DecidableEq κo] [DecidableEq κe'] [DecidableEq κo'] in
/-- **Coefficient change commutes with the cone.** PROVED. -/
theorem coneR_map {S : Type*} [CommRing S] (π : R →+* S) (f : ChainMapR C D) :
    (BasedCx.coneR f).map π = BasedCx.coneR (f.map π) := by
  unfold BasedCx.map BasedCx.coneR
  congr 1
  · change (fromBlocks D.dOE f.fO 0 (-C.dEO)).map π =
      fromBlocks (D.dOE.map π) (f.fO.map π) 0 (-(C.dEO.map π))
    rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero π), Matrix.map_neg _ (map_neg π)]
  · change (fromBlocks D.dEO f.fE 0 (-C.dOE)).map π =
      fromBlocks (D.dEO.map π) (f.fE.map π) 0 (-(C.dOE.map π))
    rw [Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero π), Matrix.map_neg _ (map_neg π)]

/-- **Derived Nakayama for comparisons** (tex L3452–3453): over a local ring, if the cone of the
reduced comparison is contractible, the cone of the comparison is contractible. PROVED. -/
theorem nakayama_comparison [IsLocalRing R] (f : ChainMapR C D)
    (hbar : Contraction (BasedCx.coneR (f.map (IsLocalRing.residue R)))) :
    Nonempty (Contraction (BasedCx.coneR f)) :=
  nakayama_contraction _ ((coneR_map (IsLocalRing.residue R) f).symm ▸ hbar)

/-! ### Non-vacuity -/

/-- The complex `R` in degree zero. -/
def ptCx (R : Type*) [CommRing R] : BasedCx R Unit Empty where
  degE _ := 0
  degO e := e.elim
  even_degE _ := ⟨0, rfl⟩
  odd_degO e := e.elim
  dOE := 0
  dEO := 0
  dd_E := by simp
  dd_O := by simp
  deg_dOE e := e.elim
  deg_dEO _ e := e.elim

/-- Multiplication by `a` on `R` in degree zero. -/
def ptMap (a : R) : ChainMapR (ptCx R) (ptCx R) where
  fE := fun _ _ => a
  fO := 0
  deg_fE _ _ _ := rfl
  deg_fO e := e.elim
  commOE := Matrix.ext fun e => e.elim
  commEO := Matrix.ext fun _ e => e.elim

/-- **Non-vacuity**: over a local ring, for `x ∈ 𝔪` the reduced cone of `1 + x : R → R` is
contractible (the reduced map is the identity), so `nakayama_comparison` applies. -/
theorem nakayama_comparison_example [IsLocalRing R] (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R) :
    Nonempty (Contraction (BasedCx.coneR (ptMap (1 + x)))) := by
  have hπ : IsLocalRing.residue R (1 + x) = 1 := by
    rw [map_add, map_one, (IsLocalRing.residue_eq_zero_iff x).mpr hx, add_zero]
  refine nakayama_comparison _
    { hOE := fromBlocks 0 0 (fun _ _ => 1) 0
      hEO := 0
      deg_hOE := ?_
      deg_hEO := fun _ _ h => absurd rfl h
      htpy_E := ?_
      htpy_O := ?_ }
  · rintro (e | u) (u' | e') h
    · exact e.elim
    · exact e.elim
    · rfl
    · exact e'.elim
  · ext (u | e) (u' | e')
    · simp [BasedCx.coneR, ChainMapR.map, ptMap, ptCx, BasedCx.map, fromBlocks, mul_apply]
      exact hπ
    · exact e'.elim
    · exact e.elim
    · exact e.elim
  · ext (e | u) (e' | u')
    · exact e.elim
    · exact e.elim
    · exact e'.elim
    · simp [BasedCx.coneR, ChainMapR.map, ptMap, ptCx, BasedCx.map, fromBlocks, mul_apply]
      exact hπ

end ZInQ.Contrib.CloudB3RC53.Torsion
