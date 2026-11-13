
/-! ## Part 3: `TatePairingZl` from the leaves of scratch/weil-pairing -/

namespace G0Galois

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`TatePairingZl` from T9 (restated), the isogeny quasi-inverse and divisibility** (as in
weil-pairing's `det_galRep_sq` / `g12_detInput_of_leaves`). -/
theorem tatePairingZl_of_leaves (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints) : TatePairingZl := by
  intro K _ _ A ℓ _
  haveI : NeZero (ℓ : K) := ⟨by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero⟩
  obtain ⟨S⟩ := h9 K A
  obtain ⟨d, hd, ψ, hψ, -⟩ := hQ K _ _ S.lam S.isogeny
  obtain ⟨g, hg⟩ := WeilPairing.exists_tmu_gen K ℓ
  refine ⟨(WeilPairing.tatePairing S.D S.lam (NeZero.ne _)).compr₂ (WeilPairing.tmuCoordLin hg),
    ?_, ?_, ?_⟩
  · intro x hx
    exact WeilPairing.tatePairing_left_ker S.D S.lam hd hψ (NeZero.ne _)
      (fun k t ht => WeilPairing.tate_surj (hD K A ℓ (Fact.out : ℓ.Prime).pos) k t ht) x
      fun y => WeilPairing.tmuCoordLin_injective hg (by rw [map_zero]; exact hx y)
  · intro x
    simp only [LinearMap.compr₂_apply]
    rw [WeilPairing.tatePairing_self S.D S.lam S.symm (NeZero.ne _) x, map_zero]
  · intro σ x y
    simp only [LinearMap.compr₂_apply]
    have h := congrArg (WeilPairing.tmuCoordLin hg)
      (WeilPairing.tatePairing_cyclotomic S.D S.lam σ x y)
    rw [map_smul, smul_eq_mul] at h
    exact h

/-- **`DetTate` from leaves**: T9 restated (`T09_SymmIsogenyExists`), `IsogenyQuasiInverse`,
`DivisiblePoints` (scratch/weil-pairing §4, §8) and T26 (`PkgI3.TateModuleFree`, Objects). -/
theorem detTate_of_leaves (h9 : WeilPairing.T09_SymmIsogenyExists)
    (hQ : WeilPairing.IsogenyQuasiInverse) (hD : WeilPairing.DivisiblePoints)
    (hT : PkgI3.TateModuleFree) : DetTate :=
  detTate_of_zl (tatePairingZl_of_leaves h9 hQ hD) hT

end G0Galois

#print axioms G0Galois.tatePairingZl_of_leaves
#print axioms G0Galois.detTate_of_leaves
