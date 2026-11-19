import ZInQKernel.Contrib.CloudB3RC53.Torsion.ConeRing

/-!
# The cone of a homotopy equivalence is contractible, and its torsion is a unit

Manuscript `diophantine_zq.tex`, tex 4189–4193 (Lemma `ex:arith-common-coordinate`): "replacing
them by the retained homotopy equivalent free models contributes only determinants of unit
disks. These are `A_i`-units. Their limits and inverse limits are `Λ`-units."

The tree's mapping cone over a commutative ring is `BasedCx.coneR f`, with
`cone^n = D^n ⊕ C^{n+1}` and `d(d, c) = (d_D d + f c, −d_C c)`. Its torsion is a unit as soon as
the cone has a contraction over the ring (`isUnit_tau`). This file constructs such a contraction
from homotopy-equivalence data.

* **`contractionOfNilpotent`** (definition, PROVED identities): for a based complex, a map `s` of
  degree `−1` with `d s + s d = 1 + M` in both parities and `M³ = 0` gives the contraction
  `s (1 − M + M²)`. Here `M` commutes with `d` because `d s + s d` does.
* `HomotopyData f g` (hypothesis structure): chain maps `f : C → D`, `g : D → C`, an exact
  homotopy `g f = 1 + d k_C + k_C d`, and a homotopy `f g = 1 + d k_D + k_D d + E` with an error
  `E` of square zero. `E = 0` is a homotopy equivalence (`HomotopyData.ofEquiv`).
* **`coneContraction`** (definition, PROVED identities): a contraction of `coneR f`. The map
  `s = [[−k_D, 0], [g, k_C]]` has `d s + s d = 1 + M`, with `M = [[E, N], [0, 0]]` and
  `M³ = 0`.
* **`isUnit_tau_coneR`**, **`isUnit_torsion_coneR`** (PROVED, over a domain): the torsion of the
  cone is a unit for every orientation.
* `torsion_coneR_map` (PROVED): along a ring map to a domain, the cone's torsion is the image of
  the torsion over the source.
* Non-vacuity: `HomotopyData.id` (the identity of any based complex).

Kinds: definitions and PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E1Torsion

open Matrix
open ZInQ.Contrib.CloudB3RC53.Torsion

variable {R : Type*} [CommRing R]

/-! ### A contraction from a nilpotent defect -/

section Nilpotent

variable {κe κo : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  (C : BasedCx R κe κo)

/-- The even defect `d s + s d − 1` of a degree `−1` map `s`. Kind: definition. -/
abbrev defE (sOE : Matrix κo κe R) (sEO : Matrix κe κo R) : Matrix κe κe R :=
  C.dEO * sOE + sEO * C.dOE - 1

/-- The odd defect `d s + s d − 1`. Kind: definition. -/
abbrev defO (sOE : Matrix κo κe R) (sEO : Matrix κe κo R) : Matrix κo κo R :=
  C.dOE * sEO + sOE * C.dEO - 1

/-- The defects intertwine `d`: `M_O d = d M_E`. Kind: PROVED. -/
theorem defO_mul_dOE (sOE : Matrix κo κe R) (sEO : Matrix κe κo R) :
    defO C sOE sEO * C.dOE = C.dOE * defE C sOE sEO := by
  have h1 := C.dd_E
  have h2 := C.dd_O
  simp only [defO, defE, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc sOE C.dEO C.dOE, h1, Matrix.mul_zero, ← Matrix.mul_assoc C.dOE C.dEO sOE,
    h2, Matrix.zero_mul, Matrix.mul_assoc C.dOE sEO C.dOE]
  abel

/-- The defects intertwine `d`: `M_E d = d M_O`. Kind: PROVED. -/
theorem defE_mul_dEO (sOE : Matrix κo κe R) (sEO : Matrix κe κo R) :
    defE C sOE sEO * C.dEO = C.dEO * defO C sOE sEO := by
  have h1 := C.dd_E
  have h2 := C.dd_O
  simp only [defO, defE, Matrix.sub_mul, Matrix.mul_sub, Matrix.add_mul, Matrix.mul_add,
    Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mul_assoc sEO C.dOE C.dEO, h2, Matrix.mul_zero, ← Matrix.mul_assoc C.dEO C.dOE sEO,
    h1, Matrix.zero_mul, Matrix.mul_assoc C.dEO sOE C.dEO]
  abel

/-- `(1 + M)(1 − M + M²) = 1` when `M³ = 0`. Kind: PROVED. -/
theorem one_add_mul_inv3 {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι R}
    (hM : M * M * M = 0) : (1 + M) * (1 - M + M * M) = 1 := by
  have : (1 + M) * (1 - M + M * M) = 1 + M * M * M := by noncomm_ring
  rw [this, hM, add_zero]

/-- The inverse `1 − M + M²` commutes past `d`. Kind: PROVED. -/
theorem inv3_mul_dOE {M : Matrix κe κe R} {N : Matrix κo κo R} (h : N * C.dOE = C.dOE * M) :
    (1 - N + N * N) * C.dOE = C.dOE * (1 - M + M * M) := by
  have h2 : N * N * C.dOE = C.dOE * (M * M) := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, h, Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, h, h2, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_one]

/-- The same in the other parity. Kind: PROVED. -/
theorem inv3_mul_dEO {M : Matrix κo κo R} {N : Matrix κe κe R} (h : N * C.dEO = C.dEO * M) :
    (1 - N + N * N) * C.dEO = C.dEO * (1 - M + M * M) := by
  have h2 : N * N * C.dEO = C.dEO * (M * M) := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, h, Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, h, h2, Matrix.mul_add, Matrix.mul_sub,
    Matrix.mul_one]

/-- A degree-zero endomorphism stays of degree zero under `1 − M + M²`. Kind: PROVED. -/
theorem hasDeg_inv3 {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι R} {b : ι → ℤ}
    (hM : HasDeg M b b 0) : HasDeg (1 - M + M * M) b b 0 :=
  ((hasDeg_one b).sub hM).add ((hM.mul hM).of_eq (by ring))

omit [DecidableEq κo] in
/-- The defect of a degree `−1` map has degree `0`. Kind: PROVED. -/
theorem hasDeg_defE {sOE : Matrix κo κe R} {sEO : Matrix κe κo R}
    (h1 : HasDeg sOE C.degO C.degE (-1)) (h2 : HasDeg sEO C.degE C.degO (-1)) :
    HasDeg (defE C sOE sEO) C.degE C.degE 0 :=
  (((C.deg_dEO.mul h1).of_eq (by ring)).add ((h2.mul C.deg_dOE).of_eq (by ring))).sub
    (hasDeg_one _)

omit [DecidableEq κe] in
/-- The same in the other parity. Kind: PROVED. -/
theorem hasDeg_defO {sOE : Matrix κo κe R} {sEO : Matrix κe κo R}
    (h1 : HasDeg sOE C.degO C.degE (-1)) (h2 : HasDeg sEO C.degE C.degO (-1)) :
    HasDeg (defO C sOE sEO) C.degO C.degO 0 :=
  (((C.deg_dOE.mul h2).of_eq (by ring)).add ((h1.mul C.deg_dEO).of_eq (by ring))).sub
    (hasDeg_one _)

/-- **A contraction from a map with nilpotent defect**: if `s` has degree `−1` and
`d s + s d = 1 + M` with `M³ = 0` in both parities, then `s (1 − M + M²)` is a contraction.
Kind: definition (PROVED fields). -/
def contractionOfNilpotent (sOE : Matrix κo κe R) (sEO : Matrix κe κo R)
    (h1 : HasDeg sOE C.degO C.degE (-1)) (h2 : HasDeg sEO C.degE C.degO (-1))
    (hE : defE C sOE sEO * defE C sOE sEO * defE C sOE sEO = 0)
    (hO : defO C sOE sEO * defO C sOE sEO * defO C sOE sEO = 0) : Contraction C where
  hOE := sOE * (1 - defE C sOE sEO + defE C sOE sEO * defE C sOE sEO)
  hEO := sEO * (1 - defO C sOE sEO + defO C sOE sEO * defO C sOE sEO)
  deg_hOE := (h1.mul (hasDeg_inv3 (hasDeg_defE C h1 h2))).of_eq (by ring)
  deg_hEO := (h2.mul (hasDeg_inv3 (hasDeg_defO C h1 h2))).of_eq (by ring)
  htpy_E := by
    have hc := inv3_mul_dOE C (defO_mul_dOE C sOE sEO)
    have hs : C.dEO * sOE + sEO * C.dOE = 1 + defE C sOE sEO := by
      simp only [defE]; abel
    calc C.dEO * (sOE * (1 - defE C sOE sEO + defE C sOE sEO * defE C sOE sEO)) +
          sEO * (1 - defO C sOE sEO + defO C sOE sEO * defO C sOE sEO) * C.dOE
        = (C.dEO * sOE + sEO * C.dOE) *
            (1 - defE C sOE sEO + defE C sOE sEO * defE C sOE sEO) := by
          rw [Matrix.mul_assoc sEO, hc, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = 1 := by rw [hs, one_add_mul_inv3 hE]
  htpy_O := by
    have hc := inv3_mul_dEO C (defE_mul_dEO C sOE sEO)
    have hs : C.dOE * sEO + sOE * C.dEO = 1 + defO C sOE sEO := by
      simp only [defO]; abel
    calc C.dOE * (sEO * (1 - defO C sOE sEO + defO C sOE sEO * defO C sOE sEO)) +
          sOE * (1 - defE C sOE sEO + defE C sOE sEO * defE C sOE sEO) * C.dEO
        = (C.dOE * sEO + sOE * C.dEO) *
            (1 - defO C sOE sEO + defO C sOE sEO * defO C sOE sEO) := by
          rw [Matrix.mul_assoc sOE, hc, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = 1 := by rw [hs, one_add_mul_inv3 hO]

end Nilpotent

/-! ### Homotopy-equivalence data and the contraction of the cone -/

section Cone

variable {κe κo κe' κo' : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  [Fintype κe'] [Fintype κo'] [DecidableEq κe'] [DecidableEq κo']
  {C : BasedCx R κe κo} {D : BasedCx R κe' κo'}

/-- **Homotopy-equivalence data with a square-zero defect** for `f : C → D` (tex 4189–4193):
a chain map `g : D → C`, an exact homotopy `g f = 1 + d k_C + k_C d`, and a homotopy
`f g = 1 + d k_D + k_D d + E` whose error `E` has square zero in each parity. A homotopy
equivalence is the case `E = 0` (`HomotopyData.ofEquiv`). Kind: definition (hypothesis structure);
non-vacuity: `HomotopyData.id`. -/
structure HomotopyData (f : ChainMapR C D) where
  /-- the homotopy inverse -/
  g : ChainMapR D C
  /-- the homotopy on `C`, even to odd -/
  kCOE : Matrix κo κe R
  /-- the homotopy on `C`, odd to even -/
  kCEO : Matrix κe κo R
  deg_kCOE : HasDeg kCOE C.degO C.degE (-1)
  deg_kCEO : HasDeg kCEO C.degE C.degO (-1)
  /-- `g f = 1 + d k_C + k_C d` (even) -/
  gfE : g.fE * f.fE = 1 + C.dEO * kCOE + kCEO * C.dOE
  /-- `g f = 1 + d k_C + k_C d` (odd) -/
  gfO : g.fO * f.fO = 1 + C.dOE * kCEO + kCOE * C.dEO
  /-- the homotopy on `D`, even to odd -/
  kDOE : Matrix κo' κe' R
  /-- the homotopy on `D`, odd to even -/
  kDEO : Matrix κe' κo' R
  deg_kDOE : HasDeg kDOE D.degO D.degE (-1)
  deg_kDEO : HasDeg kDEO D.degE D.degO (-1)
  /-- the error (even) -/
  errE : Matrix κe' κe' R
  /-- the error (odd) -/
  errO : Matrix κo' κo' R
  /-- `f g = 1 + d k_D + k_D d + E` (even) -/
  fgE : f.fE * g.fE = 1 + D.dEO * kDOE + kDEO * D.dOE + errE
  /-- `f g = 1 + d k_D + k_D d + E` (odd) -/
  fgO : f.fO * g.fO = 1 + D.dOE * kDEO + kDOE * D.dEO + errO
  /-- `E² = 0` (even) -/
  errE_sq : errE * errE = 0
  /-- `E² = 0` (odd) -/
  errO_sq : errO * errO = 0

variable {f : ChainMapR C D}

/-- The contraction candidate `s = [[−k_D, 0], [g, k_C]]` on the even part of the cone.
Kind: definition. -/
def HomotopyData.sOE (H : HomotopyData f) : Matrix (κo' ⊕ κe) (κe' ⊕ κo) R :=
  fromBlocks (-H.kDOE) 0 H.g.fE H.kCEO

/-- The same on the odd part. Kind: definition. -/
def HomotopyData.sEO (H : HomotopyData f) : Matrix (κe' ⊕ κo) (κo' ⊕ κe) R :=
  fromBlocks (-H.kDEO) 0 H.g.fO H.kCOE

/-- `s` has degree `−1` (even part). Kind: PROVED. -/
theorem HomotopyData.deg_sOE (H : HomotopyData f) :
    HasDeg H.sOE (BasedCx.coneR f).degO (BasedCx.coneR f).degE (-1) := by
  rintro (i | i) (j | j) h
  · exact H.deg_kDOE i j (by simpa [HomotopyData.sOE] using h)
  · exact absurd (by simp [HomotopyData.sOE]) h
  · have := H.g.deg_fE i j (by simpa [HomotopyData.sOE] using h)
    change C.degE i + -1 = D.degE j + -1; omega
  · have := H.deg_kCEO i j (by simpa [HomotopyData.sOE] using h)
    change C.degE i + -1 = C.degO j + -1 + -1; omega

/-- `s` has degree `−1` (odd part). Kind: PROVED. -/
theorem HomotopyData.deg_sEO (H : HomotopyData f) :
    HasDeg H.sEO (BasedCx.coneR f).degE (BasedCx.coneR f).degO (-1) := by
  rintro (i | i) (j | j) h
  · exact H.deg_kDEO i j (by simpa [HomotopyData.sEO] using h)
  · exact absurd (by simp [HomotopyData.sEO]) h
  · have := H.g.deg_fO i j (by simpa [HomotopyData.sEO] using h)
    change C.degO i + -1 = D.degO j + -1; omega
  · have := H.deg_kCOE i j (by simpa [HomotopyData.sEO] using h)
    change C.degO i + -1 = C.degE j + -1 + -1; omega

/-- **The even defect of `s` on the cone** is `[[E, N], [0, 0]]` with
`N = f k_C − k_D f`. Kind: PROVED. -/
theorem HomotopyData.defE_eq (H : HomotopyData f) :
    defE (BasedCx.coneR f) H.sOE H.sEO =
      fromBlocks H.errE (f.fE * H.kCEO - H.kDEO * f.fO) 0 0 := by
  have hgE := H.g.commOE
  have hfg := H.fgE
  have hgf := H.gfO
  change fromBlocks D.dEO f.fE 0 (-C.dOE) * fromBlocks (-H.kDOE) 0 H.g.fE H.kCEO +
      fromBlocks (-H.kDEO) 0 H.g.fO H.kCOE * fromBlocks D.dOE f.fO 0 (-C.dEO) - 1 = _
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add, sub_eq_iff_eq_add,
    ← fromBlocks_one, fromBlocks_add]
  congr 1
  · simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.zero_mul, add_zero]
    rw [hfg]; abel
  · simp only [Matrix.mul_zero, Matrix.neg_mul, Matrix.zero_mul, zero_add, add_zero]
    abel
  · simp only [Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_zero, add_zero]
    simp only [neg_zero, zero_add, Matrix.neg_mul]
    rw [hgE]; abel
  · simp only [Matrix.zero_mul, Matrix.mul_neg, zero_add, Matrix.neg_mul]
    rw [hgf]; abel

/-- **The odd defect of `s` on the cone** is `[[E, N'], [0, 0]]` with
`N' = f k_C − k_D f`. Kind: PROVED. -/
theorem HomotopyData.defO_eq (H : HomotopyData f) :
    defO (BasedCx.coneR f) H.sOE H.sEO =
      fromBlocks H.errO (f.fO * H.kCOE - H.kDOE * f.fE) 0 0 := by
  have hgO := H.g.commEO
  have hfg := H.fgO
  have hgf := H.gfE
  change fromBlocks D.dOE f.fO 0 (-C.dEO) * fromBlocks (-H.kDEO) 0 H.g.fO H.kCOE +
      fromBlocks (-H.kDOE) 0 H.g.fE H.kCEO * fromBlocks D.dEO f.fE 0 (-C.dOE) - 1 = _
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_add, sub_eq_iff_eq_add,
    ← fromBlocks_one, fromBlocks_add]
  congr 1
  · simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.zero_mul, add_zero]
    rw [hfg]; abel
  · simp only [Matrix.mul_zero, Matrix.neg_mul, Matrix.zero_mul, zero_add, add_zero]
    abel
  · simp only [Matrix.zero_mul, Matrix.mul_neg, Matrix.mul_zero, add_zero]
    simp only [neg_zero, zero_add, Matrix.neg_mul]
    rw [hgO]; abel
  · simp only [Matrix.zero_mul, Matrix.mul_neg, zero_add, Matrix.neg_mul]
    rw [hgf]; abel

/-- A block matrix `[[E, N], [0, 0]]` with `E² = 0` has cube zero. Kind: PROVED. -/
theorem fromBlocks_cube {m n : Type*} [Fintype m] [Fintype n] {E : Matrix m m R}
    {N : Matrix m n R} (hE : E * E = 0) :
    (fromBlocks E N 0 0 : Matrix (m ⊕ n) (m ⊕ n) R) * fromBlocks E N 0 0 * fromBlocks E N 0 0 =
      0 := by
  have h2 : (fromBlocks E N 0 0 : Matrix (m ⊕ n) (m ⊕ n) R) * fromBlocks E N 0 0 =
      fromBlocks 0 (E * N) 0 0 := by
    rw [fromBlocks_multiply]
    simp [hE]
  rw [h2, fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, ← fromBlocks_zero]

/-- **The contraction of the cone of a homotopy equivalence** (tex 4189–4193).
Kind: definition (PROVED fields). -/
def HomotopyData.coneContraction (H : HomotopyData f) : Contraction (BasedCx.coneR f) :=
  contractionOfNilpotent (BasedCx.coneR f) H.sOE H.sEO H.deg_sOE H.deg_sEO
    (by rw [H.defE_eq]; exact fromBlocks_cube H.errE_sq)
    (by rw [H.defO_eq]; exact fromBlocks_cube H.errO_sq)

/-- **The torsion of the cone is a unit** (over a domain, any orientation; tex 4191–4193:
"These are `A_i`-units"). Kind: PROVED. -/
theorem isUnit_tau_coneR [IsDomain R] (H : HomotopyData f) (σ : κe' ⊕ κo ≃ κo' ⊕ κe) :
    IsUnit (tau (BasedCx.coneR f) H.coneContraction σ) :=
  isUnit_tau _ _ σ

/-- **The torsion of the cone is a unit** (`torsion` form). Kind: PROVED. -/
theorem isUnit_torsion_coneR [IsDomain R] (H : HomotopyData f) (σ : κe' ⊕ κo ≃ κo' ⊕ κe) :
    IsUnit (torsion (BasedCx.coneR f) σ) := by
  rw [← tau_eq_torsion _ H.coneContraction σ]
  exact isUnit_tau_coneR H σ

/-- Coefficient change of a contraction. Kind: definition. -/
def contractionMap {S : Type*} [CommRing S] (π : R →+* S) {κe κo : Type*} [Fintype κe]
    [Fintype κo] [DecidableEq κe] [DecidableEq κo] {X : BasedCx R κe κo} (h : Contraction X) :
    Contraction (X.map π) where
  hOE := h.hOE.map π
  hEO := h.hEO.map π
  deg_hOE i j hij := h.deg_hOE i j (fun h0 => hij (by simp [h0]))
  deg_hEO i j hij := h.deg_hEO i j (fun h0 => hij (by simp [h0]))
  htpy_E := by
    change X.dEO.map π * h.hOE.map π + h.hEO.map π * X.dOE.map π = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π), h.htpy_E]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  htpy_O := by
    change X.dOE.map π * h.hEO.map π + h.hOE.map π * X.dEO.map π = 1
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π), h.htpy_O]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/-- **The torsion of the cone over a coefficient extension** is the image of the torsion over
the base (for a ring map to a domain). Kind: PROVED. -/
theorem torsion_coneR_map {S : Type*} [CommRing S] [IsDomain S] (π : R →+* S)
    (H : HomotopyData f) (σ : κe' ⊕ κo ≃ κo' ⊕ κe) :
    torsion (BasedCx.coneR (f.map π)) σ = π (tau (BasedCx.coneR f) H.coneContraction σ) := by
  rw [← coneR_map π f, ← tau_eq_torsion _
    (contractionMap π H.coneContraction) σ]
  unfold tau
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [BasedCx.map, contractionMap, Matrix.submatrix]

/-- The torsion of the cone over a domain extension is the image of a unit. Kind: PROVED. -/
theorem exists_unit_torsion_coneR_map {S : Type*} [CommRing S] [IsDomain S] [IsDomain R]
    (π : R →+* S) (H : HomotopyData f) (σ : κe' ⊕ κo ≃ κo' ⊕ κe) :
    ∃ u : Rˣ, torsion (BasedCx.coneR (f.map π)) σ = π u :=
  ⟨(isUnit_tau_coneR H σ).unit, by rw [torsion_coneR_map π H σ]; rfl⟩

end Cone

/-! ### Homotopy equivalences and non-vacuity -/

section NonVacuity

variable {κe κo : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]

/-- The identity chain map. Kind: definition. -/
def ChainMapR.idR (C : BasedCx R κe κo) : ChainMapR C C where
  fE := 1
  fO := 1
  deg_fE := hasDeg_one _
  deg_fO := hasDeg_one _
  commOE := by rw [Matrix.mul_one, Matrix.one_mul]
  commEO := by rw [Matrix.mul_one, Matrix.one_mul]

/-- **Non-vacuity**: the identity is a homotopy equivalence with zero homotopies.
Kind: definition. -/
def HomotopyData.id (C : BasedCx R κe κo) : HomotopyData (ChainMapR.idR C) where
  g := ChainMapR.idR C
  kCOE := 0
  kCEO := 0
  deg_kCOE := hasDeg_zero _ _ _
  deg_kCEO := hasDeg_zero _ _ _
  gfE := by simp [ChainMapR.idR]
  gfO := by simp [ChainMapR.idR]
  kDOE := 0
  kDEO := 0
  deg_kDOE := hasDeg_zero _ _ _
  deg_kDEO := hasDeg_zero _ _ _
  errE := 0
  errO := 0
  fgE := by simp [ChainMapR.idR]
  fgO := by simp [ChainMapR.idR]
  errE_sq := by simp
  errO_sq := by simp

end NonVacuity

section Equiv

variable {κe κo κe' κo' : Type*} [Fintype κe] [Fintype κo] [DecidableEq κe] [DecidableEq κo]
  [Fintype κe'] [Fintype κo'] [DecidableEq κe'] [DecidableEq κo']
  {C : BasedCx R κe κo} {D : BasedCx R κe' κo'}

/-- **A homotopy equivalence** (both homotopies exact) as `HomotopyData` with `E = 0`.
Kind: definition. -/
def HomotopyData.ofEquiv {f : ChainMapR C D} (g : ChainMapR D C)
    (kCOE : Matrix κo κe R) (kCEO : Matrix κe κo R)
    (deg_kCOE : HasDeg kCOE C.degO C.degE (-1)) (deg_kCEO : HasDeg kCEO C.degE C.degO (-1))
    (gfE : g.fE * f.fE = 1 + C.dEO * kCOE + kCEO * C.dOE)
    (gfO : g.fO * f.fO = 1 + C.dOE * kCEO + kCOE * C.dEO)
    (kDOE : Matrix κo' κe' R) (kDEO : Matrix κe' κo' R)
    (deg_kDOE : HasDeg kDOE D.degO D.degE (-1)) (deg_kDEO : HasDeg kDEO D.degE D.degO (-1))
    (fgE : f.fE * g.fE = 1 + D.dEO * kDOE + kDEO * D.dOE)
    (fgO : f.fO * g.fO = 1 + D.dOE * kDEO + kDOE * D.dEO) : HomotopyData f where
  g := g
  kCOE := kCOE
  kCEO := kCEO
  deg_kCOE := deg_kCOE
  deg_kCEO := deg_kCEO
  gfE := gfE
  gfO := gfO
  kDOE := kDOE
  kDEO := kDEO
  deg_kDOE := deg_kDOE
  deg_kDEO := deg_kDEO
  errE := 0
  errO := 0
  fgE := by rw [fgE, add_zero]
  fgO := by rw [fgO, add_zero]
  errE_sq := by simp
  errO_sq := by simp

end Equiv

end ZInQ.Contrib.CloudB3E1Torsion
