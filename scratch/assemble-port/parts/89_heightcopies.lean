
/-! ## g0-assemble: leaf-adopt2's glue target `HeightCopiesAgree`, proved

leaf-push2's Arakelov layer (`ZInQ.LeafPush2`, over `PkgI3.AbVar`) is a textual copy of
def-faltings' (`ZInQ.DefFaltings`, over def-faltings' `AbVar`). The copies of `HodgeData`,
`GroupModel`, `MetrizedModel` and `FinExt` are converted field by field, in both directions; the
model heights agree definitionally (`rfl`), so the two infima agree. -/

section G0AssembleHeightCopiesSec

noncomputable section

namespace HSyn.G0HeightCopies

open CategoryTheory AlgebraicGeometry NumberField

/-- `HodgeData`: leaf-push2's copy to def-faltings'. -/
def hdTo {L : Type} [Field L] [NumberField L] {g : ℕ} {V : Type} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] (D : ZInQ.LeafPush2.HodgeData L g V) : ZInQ.DefFaltings.HodgeData L g V :=
  ⟨D.lattice, D.finrank_eq_one, D.isLattice, D.periods, D.periods_discrete, D.periods_isZLattice,
    D.coeff, D.coeff_ne_zero⟩

/-- `HodgeData`: def-faltings' copy to leaf-push2's. -/
def hdFrom {L : Type} [Field L] [NumberField L] {g : ℕ} {V : Type} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] (D : ZInQ.DefFaltings.HodgeData L g V) : ZInQ.LeafPush2.HodgeData L g V :=
  ⟨D.lattice, D.finrank_eq_one, D.isLattice, D.periods, D.periods_discrete, D.periods_isZLattice,
    D.coeff, D.coeff_ne_zero⟩

theorem hdTo_modelHeight {L : Type} [Field L] [NumberField L] {g : ℕ} {V : Type} [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] (D : ZInQ.LeafPush2.HodgeData L g V) :
    (hdTo D).modelHeight = D.modelHeight := rfl

theorem hdFrom_modelHeight {L : Type} [Field L] [NumberField L] {g : ℕ} {V : Type}
    [AddCommGroup V] [Module L V] [Module (𝓞 L) V] (D : ZInQ.DefFaltings.HodgeData L g V) :
    (hdFrom D).modelHeight = D.modelHeight := rfl

variable {K : Type} [Field K]

/-- `GroupModel`: leaf-push2's copy (of `A`) to def-faltings' (of `abVarEquiv.symm A`). -/
def gmTo {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : ZInQ.LeafPush2.GroupModel A L) :
    ZInQ.DefFaltings.GroupModel ((LeafAdopt.abVarEquiv K).symm A) L :=
  { G := 𝒢.G, gen := 𝒢.gen, gen_hom := 𝒢.gen_hom }

/-- `GroupModel`: def-faltings' copy to leaf-push2's. -/
def gmFrom {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]
    (𝒢 : ZInQ.DefFaltings.GroupModel ((LeafAdopt.abVarEquiv K).symm A) L) :
    ZInQ.LeafPush2.GroupModel A L :=
  { G := 𝒢.G, gen := 𝒢.gen, gen_hom := 𝒢.gen_hom }

/-- `MetrizedModel`: leaf-push2's copy to def-faltings'. -/
def mmTo {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ}
    (M : ZInQ.LeafPush2.MetrizedModel A L g) :
    ZInQ.DefFaltings.MetrizedModel ((LeafAdopt.abVarEquiv K).symm A) L g :=
  { model := gmTo M.model, hodge := hdTo M.hodge, lattice_eq := M.lattice_eq, arch := M.arch }

/-- `MetrizedModel`: def-faltings' copy to leaf-push2's. -/
def mmFrom {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L] {g : ℕ}
    (M : ZInQ.DefFaltings.MetrizedModel ((LeafAdopt.abVarEquiv K).symm A) L g) :
    ZInQ.LeafPush2.MetrizedModel A L g :=
  { model := gmFrom M.model, hodge := hdFrom M.hodge, lattice_eq := M.lattice_eq, arch := M.arch }

/-- **`HeightCopiesAgree`, proved** (g0-assemble). -/
theorem heightCopiesAgree : HSyn.HeightCopiesAgree := by
  intro K _ A
  apply le_antisymm
  · refine le_iInf fun E => le_iInf fun g => le_iInf fun M => ?_
    let E' : ZInQ.LeafPush2.FinExt K := ⟨E.L⟩
    exact iInf_le_of_le E' (iInf_le_of_le g (iInf_le_of_le (mmFrom (L := E.L) M) le_rfl))
  · refine le_iInf fun E => le_iInf fun g => le_iInf fun M => ?_
    let E' : ZInQ.DefFaltings.FinExt K := ⟨E.L⟩
    exact iInf_le_of_le E' (iInf_le_of_le g (iInf_le_of_le (mmTo (L := E.L) M) le_rfl))

end HSyn.G0HeightCopies

end

end G0AssembleHeightCopiesSec

#print axioms HSyn.G0HeightCopies.heightCopiesAgree
