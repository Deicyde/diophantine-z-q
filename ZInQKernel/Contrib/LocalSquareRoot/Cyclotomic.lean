import ZInQKernel.Contrib.LocalSquareRoot.Fields
import ZInQKernel.HDecomp.Descent.B2Glue

/-!
# The actual cyclotomic global-to-local character bridge

`finiteCyc` records the action on the chosen primitive root in the actual local
cyclotomic field. Its inflation equals the baseline global cyclotomic character
pulled back along `GlueDescent.B2Q.resp`. The proof uses the exact `IsAlgClosed.lift`
chosen inside Mathlib's `Field.absoluteGaloisGroup.map`, not a separately chosen
embedding or an assumed compatibility statement.

The finite CRT comparison identifies the actual `galToProd = (-1, 1)` element
with any unit having the required two residues. It permits `k = 0`, `m = 1`,
and `p = 2`. There is no construction of an infinite tau and no assertion about
quotient topology, descent of arbitrary characters, or the final local criterion.
This is an implementation contribution, not independent acceptance or a release.
-/

namespace ZInQ.Contrib.LocalSquareRoot

/-- Primitive-root eigenvalues are natural under an embedding intertwining the
specified two actions on the primitive root. -/
theorem autToPow_map {R S K L : Type*} [CommRing R] [CommRing S] [Field K] [Field L]
    [Algebra R K] [Algebra S L] {n : ℕ} [NeZero n] (f : K →+* L)
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (σ : Gal(K/R)) (τ : Gal(L/S))
    (hcomm : τ (f ζ) = f (σ ζ)) :
    (hζ.map_of_injective f.injective).autToPow S τ = hζ.autToPow R σ := by
  apply Units.ext
  apply ZMod.val_injective
  apply (hζ.map_of_injective f.injective).pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [(hζ.map_of_injective f.injective).autToPow_spec S τ, ← map_pow,
    hζ.autToPow_spec R σ, hcomm]

/-- The eigenvalue does not depend on which primitive root is used. -/
theorem autToPow_eq_of_primitiveRoots {R K : Type*} [CommRing R] [Field K]
    [Algebra R K] {n : ℕ} [NeZero n] {ζ η : K}
    (hζ : IsPrimitiveRoot ζ n) (hη : IsPrimitiveRoot η n) (σ : Gal(K/R)) :
    hζ.autToPow R σ = hη.autToPow R σ := by
  rw [hζ.autToPow_eq_modularCyclotomicCharacter n R,
    hη.autToPow_eq_modularCyclotomicCharacter n R]

/-- The exact algebraic-closure embedding chosen in `absoluteGaloisGroup.map`
intertwines the actual induced action. -/
theorem absoluteGalois_map_intertwines {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (g : Gal(AlgebraicClosure L/L)) (x : AlgebraicClosure K) :
    letI : Algebra K L := f.toAlgebra
    let e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
    let σ : Gal(AlgebraicClosure K/K) := Field.absoluteGaloisGroup.map f g
    g (e x) = e (σ x) := by
  let _ : Algebra K L := f.toAlgebra
  let e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L := IsAlgClosed.lift
  let _ : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := e.toAlgebra
  change g (algebraMap (AlgebraicClosure K) (AlgebraicClosure L) x) =
    algebraMap (AlgebraicClosure K) (AlgebraicClosure L)
      ((g.restrictScalars K).restrictNormal (AlgebraicClosure K) x)
  exact ((g.restrictScalars K).restrictNormal_commutes (AlgebraicClosure K) x).symm

section Finite

variable (p : ℕ) [Fact p.Prime]

/-- The cyclotomic action on the actual finite local field of `n`-th roots. -/
noncomputable def finiteCyc (n : ℕ) [NeZero n] :
    Gal(GlueSqrtDisj.muField p n/ℚ_[p]) →* (ZMod n)ˣ :=
  (IsCyclotomicExtension.zeta_spec n ℚ_[p] (GlueSqrtDisj.muField p n)).autToPow ℚ_[p]

/-- A Dirichlet character on the actual finite local cyclotomic Galois group. -/
noncomputable def finiteGalChar {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Gal(GlueSqrtDisj.muField p N/ℚ_[p]) →* ℂˣ :=
  χ.toUnitHom.comp (finiteCyc p N)

end Finite

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- The baseline global modular cyclotomic character is the eigenvalue on any
primitive root in its algebraic closure. -/
theorem cyc_eq_autToPow {N : ℕ} [NeZero N] {ζ : AlgebraicClosure ℚ}
    (hζ : IsPrimitiveRoot ζ N) (σ : GlueDescent.B2Q.GQ) :
    GlueDescent.B2Q.cyc N σ = hζ.autToPow ℚ (σ : Gal(AlgebraicClosure ℚ/ℚ)) := by
  exact (hζ.autToPow_eq_modularCyclotomicCharacter N ℚ
    (σ : Gal(AlgebraicClosure ℚ/ℚ))).symm

/-- Actual global-to-local cyclotomic naturality for the baseline `resp`, with
restriction to the actual local finite cyclotomic field. -/
theorem finiteCyc_restrict_eq_cyc (p : Nat.Primes) (N : ℕ) [NeZero N]
    (g : GlueDescent.B2Q.GQp p) :
    finiteCyc (p : ℕ) N (g.restrictNormal (GlueSqrtDisj.muField (p : ℕ) N)) =
      GlueDescent.B2Q.cyc N (GlueDescent.B2Q.resp p g) := by
  let _ : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  let e : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl (p : ℕ) := IsAlgClosed.lift
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ) N
  have hη : IsPrimitiveRoot (e ζ) N := hζ.map_of_injective e.injective
  let t : GlueSqrtDisj.muField (p : ℕ) N :=
    ⟨e ζ, IntermediateField.subset_adjoin ℚ_[p] _ hη.pow_eq_one⟩
  have ht : IsPrimitiveRoot t N :=
    IsPrimitiveRoot.of_map_of_injective
      (f := (GlueSqrtDisj.muField (p : ℕ) N).val) hη Subtype.val_injective
  have hres : hη.autToPow ℚ_[p] g =
      ht.autToPow ℚ_[p] (g.restrictNormal (GlueSqrtDisj.muField (p : ℕ) N)) := by
    exact autToPow_map (GlueSqrtDisj.muField (p : ℕ) N).val.toRingHom ht
      (g.restrictNormal (GlueSqrtDisj.muField (p : ℕ) N)) g
      (g.restrictNormal_commutes (GlueSqrtDisj.muField (p : ℕ) N) t).symm
  have hglob : hη.autToPow ℚ_[p] g = hζ.autToPow ℚ (GlueDescent.B2Q.resp p g) := by
    apply autToPow_map e.toRingHom hζ (GlueDescent.B2Q.resp p g) g
    exact absoluteGalois_map_intertwines (algebraMap ℚ ℚ_[p]) g ζ
  calc
    finiteCyc (p : ℕ) N (g.restrictNormal (GlueSqrtDisj.muField (p : ℕ) N)) =
        ht.autToPow ℚ_[p] (g.restrictNormal (GlueSqrtDisj.muField (p : ℕ) N)) :=
      autToPow_eq_of_primitiveRoots
        (IsCyclotomicExtension.zeta_spec N ℚ_[p] (GlueSqrtDisj.muField (p : ℕ) N)) ht _
    _ = hη.autToPow ℚ_[p] g := hres.symm
    _ = hζ.autToPow ℚ (GlueDescent.B2Q.resp p g) := hglob
    _ = GlueDescent.B2Q.cyc N (GlueDescent.B2Q.resp p g) := (cyc_eq_autToPow hζ _).symm

/-- The finite local Dirichlet character inflates to exactly the baseline global
character pulled back along the actual decomposition-group map. -/
theorem finiteGalChar_restrict_eq_galChar (p : Nat.Primes) {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (g : GlueDescent.B2Q.GQp p) :
    finiteGalChar (p : ℕ) χ (g.restrictNormal (GlueSqrtDisj.muField (p : ℕ) N)) =
      GlueDescent.B2Q.galChar χ (GlueDescent.B2Q.resp p g) := by
  change χ.toUnitHom (finiteCyc (p : ℕ) N
    (g.restrictNormal (GlueSqrtDisj.muField (p : ℕ) N))) =
      χ.toUnitHom (GlueDescent.B2Q.cyc N (GlueDescent.B2Q.resp p g))
  rw [finiteCyc_restrict_eq_cyc]

section CRT

variable (p : ℕ) [hp : Fact p.Prime] (k m : ℕ) [NeZero m]

/-- The two actual components of the finite cyclotomic eigenvalue are exactly
those of `galToProd`, using the same chosen zeta and its two powers. -/
theorem finiteCyc_components (σ : Gal(GlueSqrtDisj.muField p (p ^ k * m)/ℚ_[p])) :
    (((finiteCyc p (p ^ k * m) σ : (ZMod (p ^ k * m))ˣ) : ZMod (p ^ k * m)).cast :
        ZMod (p ^ k)) =
      ((GlueSqrtDisj.galToProd (p := p) (L := GlueSqrtDisj.muField p (p ^ k * m))
        k m σ).1 : ZMod (p ^ k)) ∧
    (((finiteCyc p (p ^ k * m) σ : (ZMod (p ^ k * m))ˣ) : ZMod (p ^ k * m)).cast :
        ZMod m) =
      ((GlueSqrtDisj.galToProd (p := p) (L := GlueSqrtDisj.muField p (p ^ k * m))
        k m σ).2 : ZMod m) := by
  let ζ := IsCyclotomicExtension.zeta (p ^ k * m) ℚ_[p]
    (GlueSqrtDisj.muField p (p ^ k * m))
  let a : ZMod (p ^ k * m) := finiteCyc p (p ^ k * m) σ
  have hζ : σ ζ = ζ ^ a.val :=
    (IsCyclotomicExtension.zeta_spec (p ^ k * m) ℚ_[p]
      (GlueSqrtDisj.muField p (p ^ k * m))).autToPow_spec ℚ_[p] σ |>.symm
  constructor
  · have h := GlueSqrtLocal.autToPow_eq_of_apply
      (GlueSqrtDisj.zeta_pow_m (p := p) (L := GlueSqrtDisj.muField p (p ^ k * m)) k m)
      σ a.val (by
        change σ (ζ ^ m) = (ζ ^ m) ^ a.val
        rw [map_pow, hζ, ← pow_mul, ← pow_mul]
        exact congrArg (fun j : ℕ => ζ ^ j) (Nat.mul_comm a.val m))
    change (a.cast : ZMod (p ^ k)) = _
    rw [ZMod.cast_eq_val]
    exact h.symm
  · have h := GlueSqrtLocal.autToPow_eq_of_apply
      (GlueSqrtDisj.zeta_pow_pk (p := p) (L := GlueSqrtDisj.muField p (p ^ k * m)) k m)
      σ a.val (by
        change σ (ζ ^ (p ^ k)) = (ζ ^ (p ^ k)) ^ a.val
        rw [map_pow, hζ, ← pow_mul, ← pow_mul]
        exact congrArg (fun j : ℕ => ζ ^ j) (Nat.mul_comm a.val (p ^ k)))
    change (a.cast : ZMod m) = _
    rw [ZMod.cast_eq_val]
    exact h.symm

/-- The actual finite tau has the CRT eigenvalue prescribed by the two residues.
No compatibility assumption or infinite tau is introduced. -/
theorem finiteCyc_tau_eq (hcop : p.Coprime m)
    (τ : Gal(GlueSqrtDisj.muField p (p ^ k * m)/ℚ_[p]))
    (hτ : GlueSqrtDisj.galToProd (p := p) (L := GlueSqrtDisj.muField p (p ^ k * m))
      k m τ = (-1, 1)) (u : (ZMod (p ^ k * m))ˣ)
    (hu₁ : ((u : ZMod (p ^ k * m)).cast : ZMod (p ^ k)) = -1)
    (hu₂ : ((u : ZMod (p ^ k * m)).cast : ZMod m) = 1) :
    finiteCyc p (p ^ k * m) τ = u := by
  obtain ⟨h₁, h₂⟩ := finiteCyc_components p k m τ
  rw [hτ] at h₁ h₂
  apply Units.ext
  apply (ZMod.chineseRemainder (Nat.Coprime.pow_left k hcop)).injective
  change ((↑(finiteCyc p (p ^ k * m) τ) : ZMod (p ^ k * m)).cast :
      ZMod (p ^ k) × ZMod m) = (ZMod.cast (u : ZMod (p ^ k * m)))
  apply Prod.ext
  · simpa only [Prod.fst_zmod_cast] using h₁.trans hu₁.symm
  · simpa only [Prod.snd_zmod_cast] using h₂.trans hu₂.symm

/-- Evaluation of the finite local character at the actual finite tau is exactly
its Dirichlet-character value at the prescribed CRT unit. -/
theorem finiteGalChar_tau_eq (hcop : p.Coprime m)
    (χ : DirichletCharacter ℂ (p ^ k * m))
    (τ : Gal(GlueSqrtDisj.muField p (p ^ k * m)/ℚ_[p]))
    (hτ : GlueSqrtDisj.galToProd (p := p) (L := GlueSqrtDisj.muField p (p ^ k * m))
      k m τ = (-1, 1)) (u : (ZMod (p ^ k * m))ˣ)
    (hu₁ : ((u : ZMod (p ^ k * m)).cast : ZMod (p ^ k)) = -1)
    (hu₂ : ((u : ZMod (p ^ k * m)).cast : ZMod m) = 1) :
    finiteGalChar p χ τ = χ.toUnitHom u := by
  change χ.toUnitHom (finiteCyc p (p ^ k * m) τ) = χ.toUnitHom u
  rw [finiteCyc_tau_eq p k m hcop τ hτ u hu₁ hu₂]

end CRT
end ZInQ.Contrib.LocalSquareRoot

#print axioms ZInQ.Contrib.LocalSquareRoot.autToPow_map
#print axioms ZInQ.Contrib.LocalSquareRoot.autToPow_eq_of_primitiveRoots
#print axioms ZInQ.Contrib.LocalSquareRoot.absoluteGalois_map_intertwines
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteCyc_restrict_eq_cyc
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteGalChar_restrict_eq_galChar
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteCyc_components
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteCyc_tau_eq
#print axioms ZInQ.Contrib.LocalSquareRoot.finiteGalChar_tau_eq
