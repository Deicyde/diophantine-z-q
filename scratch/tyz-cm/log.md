# tyz-cm results log

Task tyz-cm, 2026-11-13. Targets: `CM.CMFieldOfDefinition ringClassFieldD`, `Package.TYZSigmaFixesZn`.

## 09:30 setup
- Merged `origin/wip/ring-class` (conflicts: ThirdParty/TauCeti/NOTICE, both entries kept;
  `.fleet/x0-32.md` deleted as on fork main). Commit 96223ef3.
- `~/tyz-src/Period7.tex` is NOT on this host; TYZ line numbers below are quoted from project notes.
- `~/pyenv` does not exist; python via `~/bin/uv run --with sympy --with mpmath` (sympy was not in the uv
  cache: the first `uv run` downloaded it from PyPI — a network access by the package manager; all later
  runs use `--offline`).

## Numerics (VERIFIED, scratch/tyz-cm/twist*.py, coeffs.py; mpmath 40 digits, exact fractions)
- TYZ form `Q_n = [16(n+1), −8, 1]`, `τ = (1+w)/(4(n+1))`, `w = i√n`. `𝔟 = α𝓞_K ∩ O_{n,4}`,
  `α = 3 + 2√−n` (ring-class's `alpha`, `sigmaClass = [𝔟]`): `𝔟 = ℤ⟨6+4w, 3−4n+8w⟩` (by hand, checked).
- `𝔟̄·(⟨1,τ⟩, ⟨1/32,τ⟩)` computed by HNF; its point `τ_X`: `φ(τ_X) = φ(τ) + (0,0)` to 1e-37 for
  18 values n ∈ {5,…,205} (Γ₀(32)-reduced representatives; twist2.py).
- `Q'_n := [16(n+9), −8(2n+15), 4n+25]`, discriminant `−64n`, `32 | 16(n+9)` (n ≡ 5 mod 8), primitive.
  `τ_{Q'} = N₀ τ_Q`, `N₀ τ = (14τ−1)/(32τ−2) = S W S W τ` (`S: τ ↦ τ+1/2`, `W: τ ↦ −1/(32τ)`).
  Since `φ(τ+1/2) = −φ(τ)` (x0-32, proved) and `φ(Wτ) = T − φ(τ)` (x0-32 leaf EtaModelFricke),
  `φ(N₀τ) = φ(τ) − 2T = φ(τ) + (0,0)` (`2T = (0,0)`). Numerically `φ(τ_{Q'}) = φ(τ_Q)+(0,0)` (1e-38).
- Lattice identity (symbolic in n, sympy, coeffs.py): with `c = ((5n+9) − 2(n+3)w)/(n+9)`,
  `𝔟·⟨1, τ'⟩ = c⟨1, τ⟩` and `𝔟·⟨1/32, τ'⟩ = c⟨1/32, τ⟩`; all coefficients integer polynomials in n
  (using `(n−5)/4`, `(n+9)/2` ∈ ℤ); gcd of 2×2 minors = 1 (minors 4 and 4n+1).
  Fitted from 18 values of n, then verified symbolically.

## 10:45 TYZSigmaFixesZn reduced (VERIFIED, compiled)
- New leaf `Shimura.ShimuraReciprocityPic` (ShimuraRecip.lean): main theorem of CM for Heegner points
  of X₀(32) in Gross's form, over Tau Ceti's Pic/Artin and lattices `κ(J∩O)·(L, L_N)`.
- `Shimura.tyzSigmaFixesZn_of (hS : ShimuraReciprocityPic) (hF : X0.EtaModelFricke) :
  Package.TYZSigmaFixesZn` (ShimuraZn.lean). `lake build ZInQKernel.Contrib.TYZGenus.ShimuraZn` OK;
  `#print axioms`: propext, Classical.choice, Quot.sound.
- Proved pieces: `int_coords` (𝓞_K = ℤ[√−n], n ≡ 1 mod 4 squarefree), `idealMeetOrder_alpha`,
  `latK`/`latNK` (lattice identities in K), `phiC_add_half`, `ptTC_add_self` (2T = (0,0) in A(ℂ)),
  `phiC_N0`, `tyzForm'` (primitive: 1 = −(n+6)A − 2(n+6)B − (4n+23)C), `tau'_eq`,
  `exists_galQ_neg`, `exists_normalized_embed`, `fixes_iQ_of_sigma`.

## 10:25 scope change
- TYZSigmaFixesZn moved to cm-numeric (with Lemma318Literal, GenusPointLeafCM). ShimuraZn.lean (committed
  8ca00d4d) left as is: `tyzSigmaFixesZn_of (hS : ShimuraReciprocityPic) (hF : X0.EtaModelFricke)`.

## 10:30 CMFieldOfDefinition ringClassFieldD reduced (VERIFIED, compiled; commit e6ac1310)
- ShimuraField.lean: `cmFieldOfDefinition_of (hS : ShimuraReciprocityPic) : CM.CMFieldOfDefinition ringClassFieldD`;
  `cmFieldTYZ_of_shimura : ShimuraReciprocityPic → Package.CMFieldOfDefinitionTYZ`;
  `tyzThm35ReadingA_of_shimura` (3 L-leaves, ShimuraReciprocityPic, EtaModelFricke, Lemma318Literal, GenusPointLeafCM).
  Axioms: propext, Classical.choice, Quot.sound.
- Proof: J = 𝓞_K (trivial class) in ShimuraReciprocityPic; κ(O) ⊆ ℤ + ℤ·Aτ_Q (`kappa_order`, parity of
  half-integral coordinates of 𝓞_K, m ≡ 3 vs m ≢ 3 mod 4), so κ(O)·L = L for L = ⟨1,τ⟩, ⟨1/32,τ⟩;
  `InfiniteGalois.fixedField_fixingSubgroup`. No Heegner condition used.

## 10:40 general leaf over ℚ(X₀(N)) (VERIFIED, compiled; commit da1bc29b)
- ShimuraModFn.lean: `IsRatModFn N g` (Γ₀(N)-invariant, O(e^{2πk Im τ}) at every cusp γ∞, rational
  q-expansion at ∞ converging on ℍ); leaf `ShimuraReciprocityModFn` (Gross form, any g, any N; does not
  mention the eta model); `shimuraReciprocityPic_of (hS) (hx : IsRatModFn 32 xC) (hy : IsRatModFn 32 yC)`;
  X0-specific: `XQExpRational`, `YQExpRational`, leaf `EtaCuspGrowth`; `cmFieldOfDefinition_of_modFn`.
- Why not the j-route (x(τ) ∈ ℚ(j(τ), j(32τ))): as a statement about VALUES it fails at points where
  (j, j_32) does not separate points of X₀(32) (singular points of Φ₃₂(X,Y) = 0); the Gross form avoids it.

## 10:50 rational q-expansions proved (VERIFIED, compiled)
- ShimuraQExp.lean: `xQExpRational : XQExpRational`, `yQExpRational : YQExpRational`;
  `cmFieldOfDefinition_of_modFn' : ShimuraReciprocityModFn → X0.EtaModelInvariant → EtaCuspGrowth →
  CM.CMFieldOfDefinition ringClassFieldD`. Axioms: the standard three.

## 10:55 cusp growth proved; main result (VERIFIED, compiled)
- ShimuraCusp.lean: `etaCuspGrowth : EtaCuspGrowth` (k = 6). H(w) = |η(w)|⁴ Im w SL₂(ℤ)-invariant via
  `CuspForm.discriminant`; Hermite decomposition; compactness bounds for ∏(1−qⁿ) on |q| ≤ e^{−2π};
  identities |x−2|⁴H₄H₃₂² = 64H₂²H₁₆, |y|⁴H₄²H₃₂⁴ = 16H₈⁴H₁₆².
  `cmFieldOfDefinition_of_modFn_inv : ShimuraReciprocityModFn → X0.EtaModelInvariant → CMFieldOfDefinition ringClassFieldD`.
- ShimuraMain.lean: leaf `CMValueRingClass` (values of ℚ(X₀(N)) regular on ℍ at Heegner points lie in
  ringClassFieldD D); `cmFieldOfDefinition_of_cmValue : CMValueRingClass → X0.EtaModelInvariant →
  CM.CMFieldOfDefinition ringClassFieldD` (MAIN RESULT); `cmValueRingClass_of_modFn`;
  `shimuraReciprocityPic_of_modFn`; `tyzThm35ReadingA_of_cmValue`. All: propext, Classical.choice, Quot.sound
  (scratch/tyz-cm/ax5.lean). Commit 45ee8aaf.
- Finding (not formalized): for γ ∈ Γ₀(32), |x(γτ)−2| = |x(τ)−2| (H-invariance), so x∘γ−2 = ε_γ(x−2), ε_γ²⁴ = 1;
  EtaModelInvariant ⇔ ε ≡ 1, which needs the eta multiplier. Left as x0-32's leaf.
- diffcheck2: MOD-UNNOTED 0, NOTE-ONLY 0.

## 11:10 Γ₀(32)-invariance (VERIFIED, compiled; commits cdf88533, 02fa2baf)
- After `git merge origin/main` (b7cdba8e; only additions, clean), gz-theta's `GZTheta/Eta.lean` (η² multiplier,
  Euclidean exponent `etaSqExp`) and `TripleProduct.lean`/`JacobiGauss.lean` (Jacobi triple product) available.
- Numerics (scratch/tyz-cm/etasq.py, etasq2.py): etaSqExp ≡ (a−2d)c − bd(c²−1) + 3d − 3 (d odd), ≡ (a+d)c − bd(c²−1) − 3c
  (c odd) mod 12 on 11 962 random SL₂(ℤ) matrices, 0 failures; the four Euclidean-step congruences hold for all
  residues mod 12. Ligozat search (etaq.py): x = η(16)⁶/(η(8)²η(32)⁴), x+2 = η(4)⁵η(16)/(η(2)²η(8)²η(32)²),
  x−2 = η(2)²η(16)/(η(4)η(32)²) (the definition).
- ShimuraEtaInv.lean: `etaSqExp_closed`, `etaD_sq_smul`, `yC_gamma0` (unconditional), `xC_sub_two_sq_gamma0`
  (unconditional), `etaModelInvariant_of_equation : EtaModelEquation → EtaModelInvariant` (sign argument).
- ShimuraTheta.lean: theta products (θ₀₁(4τ), θ₀₀(16τ), θ(8τ;16τ)), Euler BCD = 1, parity split, `xC_eq_even`,
  `xC_gamma0'`, `etaModelInvariant : X0.EtaModelInvariant` (x0-32's leaf PROVED),
  `cmFieldOfDefinition_of_cmValueRingClass : CMValueRingClass → CM.CMFieldOfDefinition ringClassFieldD` (MAIN),
  `shimuraReciprocityPic_of_shimuraModFn`, `cmFieldOfDefinition_of_shimuraModFn`, `cmFieldTYZ_of_cmValueRingClass`,
  `tyzThm35ReadingA_of_cmValueRingClass`. All axioms: propext, Classical.choice, Quot.sound (ax6.lean, ax7.lean).
