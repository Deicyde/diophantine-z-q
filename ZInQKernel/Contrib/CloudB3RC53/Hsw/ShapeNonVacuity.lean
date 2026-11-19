import ZInQKernel.Contrib.CloudB3RC53.Hsw.Shape
import ZInQKernel.Contrib.CloudB3RC53.SwitchInputs.NonVacuityDuality

/-!
# RC53 `hsw`: non-vacuity of the local-duality shape

All hypotheses of `hsw_of_localDuality` hold together on the small Selmer model `ndR` of
`SwitchInputs/NonVacuityDuality.lean`, over `ℚ` with `ε = 1`, `J = 1`. In that model:
* the strict condition is `0`, so it vanishes in degree two;
* the local cup product is `−switchPairing 1 1 1`, which is symmetric, so the cup-one datum is
  zero with `c = −1`;
* the residue form is the switch pairing, which is nondegenerate with the finite plane isotropic.

The model has a genuine (non-degreewise) Selmer duality quasi-isomorphism (`ndHγ`). All `PROVED`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Hsw

open ZInQ.Manuscript.RC.Uniform ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Contrib.CloudB3RC53.PairedFunctional ZInQ.Contrib.CloudB3RC53.SwitchInputs
  ZInQ.Contrib.CloudB3RC53.SelmerDuality

theorem nd_cupOne_key (x y : NV4) :
    (0 : ℚ) = -(ndBeta 1 1 x y) - (-1 : ℚ) • ndBeta 1 1 y x + 0 := by
  rw [ndBeta_eq, ndBeta_eq, ndSP_symm]
  simp

/-- The zero cup-one datum of the model (its local cup product is symmetric, `c = −1`). -/
def ndCupOne : CupOneDatum ndR.D (ndConst PUnit) ndStr0 (ndQ 1 1) (-1) where
  C11 := 0
  X2 := 0
  formula a b _ := nd_cupOne_key a b

/-- The residue form of the model is the switch pairing. -/
theorem nd_resForm (t u : NV4) :
    resForm ndR (ndConst PUnit) ndStr0 (ndQ 1 1) (ndTr 1 1) t u = ndSP 1 1 t u :=
  ndSw_key 1 1 (sgn 2) t u

/-- The finite plane is isotropic for the switch pairing. -/
theorem nd_sp_fin (t u : NV4) (h1 : t.2 = 0) (h2 : u.2 = 0) : ndSP 1 1 t u = 0 := by
  simp [ndSP, switchPairing, planePairing_apply, h1, h2]

/-- The classes of the model are the cochains themselves. -/
theorem nd_gClass (t : NV4) (ht : ndR.D.U.d 1 2 rfl t = 0) : gClass ndR t ht = t :=
  constCxH1_cls1 NV4 _

/-- **Non-vacuity of `hsw_of_localDuality`** (`PROVED`): its conclusion is obtained on the model
`ndR`, with every hypothesis discharged. -/
theorem nd_hsw_of_localDuality :
    ∃ Φ : ((Fin 2 → ℚ) × (Fin 2 → ℚ)) ≃ₗ[ℚ] ((Fin 2 → ℚ) × (Fin 2 → ℚ)),
      (finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ)).map Φ.toLinearMap =
        finPlane ℚ (Fin 2 → ℚ) (Fin 2 → ℚ) ∧
      ∀ (t u : ndR.D.U.X 1) (s : (ndConst PUnit).X 2) (_ht : ndR.D.U.d 1 2 rfl t = 0)
        (_hu : ndR.D.U.d 1 2 rfl u = ndStr0.f 2 2 rfl s)
        (ct cu : LinearMap.ker (ndR.Wrel.d 1 2 rfl))
        (_hct : ct.1 = ndR.gR.f 1 1 rfl t) (_hcu : cu.1 = ndR.gR.f 1 1 rfl u),
        ndTr 1 1 (selCupFun (ndQ 1 1) 2 1 3 rfl ((0 : ndR.D.G.X 2), s,
            -(ndR.D.ι.f 1 (2 - 1) (by omega) u))
            ((0 : ndR.D.G.X 1), t, (0 : ndR.D.L.X (1 - 1)))) =
          switchPairing 1 (-(-1)) 1 ((reCoordGen ndR Φ).eR (cls1 ndR.Wrel ct))
            ((reCoordGen ndR Φ).eR (cls1 ndR.Wrel cu)) :=
  hsw_of_localDuality ndR (ndConst PUnit) ndStr0 (ndQ 1 1) (ndTr 1 1) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ y => ⟨y, rfl⟩) (fun _ _ h => ⟨PUnit.unit, h.symm⟩)
    (ndTr_htr 1 1) (fun _ => rfl) ndCupOne one_ne_zero (mul_one 1)
    (fun t u ht hu htF huF => by
      have h1 : t.2 = 0 := (congrArg Prod.snd (nd_gClass t ht)).symm.trans (mem_finPlane.1 htF)
      have h2 : u.2 = 0 := (congrArg Prod.snd (nd_gClass u hu)).symm.trans (mem_finPlane.1 huF)
      exact (nd_resForm t u).trans (nd_sp_fin t u h1 h2))
    (fun t ht h => (nd_gClass t ht).trans
      ((ndSP_nd 1 1 one_ne_zero (mul_one 1)).1 t fun u => (nd_resForm t u).symm.trans (h u rfl)))
    (Or.inl ⟨two_ne_zero, by norm_num⟩)

end ZInQ.Contrib.CloudB3RC53.Hsw
