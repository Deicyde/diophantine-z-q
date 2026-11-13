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
