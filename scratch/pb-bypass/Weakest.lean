import ZInQKernel.OneProof.H.TailA

/-! pb-bypass: the weakest form of `PanBerger` that its only consumer (`G0Galois.g12`) needs is its
instance at `p = 5`. `g12_of_panBerger5` is `g12` (TailA) verbatim with `hPB : PanBerger5`. -/

namespace HDec

noncomputable section

namespace G0Galois

open _root_.PkgI4 (GaloisRep GaloisChar)
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- `PanBerger` at `p = 5` (the only prime `g12` uses). -/
def PanBerger5 : Prop :=
  ∀ ρ : GaloisRep 5 2,
    ρ.IsIrreducible → ρ.FinitelyRamified → PkgI4.LocalIsDeRham 5 2 (ρ.restrictLocal 5) → ρ.IsOdd →
    PkgI4.GaloisRep.DistinctHTWeights (ρ := ρ) 5 →
    ∃ (N : ℕ) (k : ℤ) (χ : DirichletCharacter ℂ N) (g : PkgI4.CF N k), 0 < N ∧ 1 ≤ k ∧
      PkgI4.IsNormalizedEigenform g χ ∧
      ∃ (ψ : GaloisChar 5) (ιC : PkgI4.Qbar →ₐ[ℚ] ℂ) (ιL : PkgI4.Qbar →ₐ[ℚ] PadicAlgCl 5)
        (S : Finset ℕ), ρ.AttachedUpToTwist ψ ιC ιL g S

theorem panBerger5_of_panBerger (h : PkgI4.PanBerger) : PanBerger5 :=
  fun ρ => h 5 (le_refl 5) ρ

theorem g12_of_panBerger5 (hPB : PanBerger5) (hR14 : HSyn.EigenformRepExists) (hR13 : PkgI4.EigenformHT)
    (hR15 : HSyn.DeligneSerreConseq) (hT18 : HSyn.FrobeniusDense) (hT19 : HSyn.BrauerNesbitt)
    (hT9 : LeafPush.T09_WeilPairing.{0}) (hW : G12Weight) (hD : G12Det)
    {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (T : Finset ℕ) (r : GaloisRep 5 2)
    (e : Vb A 5 ≃ₗ[PadicAlgCl 5] (Fin 2 → PadicAlgCl 5) × (Fin 2 → PadicAlgCl 5))
    (hdim : A.dim = 2) (hint : Intertwines (tate A 5) (fun σ => r.mat (resQ K σ)) e)
    (hirr : r.IsIrreducible) (h9 : G9Out r) (h10 : G10Out r) (h11 : G11Out T r) :
    G12Out r := by
  obtain ⟨N, k, χ, g, hN, hk, hg, ψ, ιC, ιL, S, hatt⟩ :=
    hPB r hirr (finitelyRamified_of_g11 h11) h9.1 h10 ⟨0, -1, by norm_num, h9.2⟩
  obtain ⟨n, hn⟩ := hW hR14 hR13 hR15 hT18 hT19 r N k χ g ψ ιC ιL S hN hk hg hirr h9.2 hatt
  obtain ⟨-, rfl⟩ := PkgI4.weight_match n k hk hn
  obtain ⟨H, hH, dr, εg, χc, hdet, hHsq, hε⟩ :=
    hD hR14 hT9 K A r e N χ g ψ ιC ιL S hdim hint hN hg hatt
  haveI := hH
  exact ⟨N, χ, g, ψ, ιC, ιL, S, hN, hg,
    GlueAssembly.twist_finite H dr εg χc ψ.toHom hdet hHsq hε, hatt⟩

end G0Galois

end

end HDec

#print axioms HDec.G0Galois.g12_of_panBerger5
