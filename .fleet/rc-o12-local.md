# rc-o12-local

The cuspidal side of (O.12) is assembled in the new `O12Local` modules. On a conductor-one cuspidal block, the normalized inducing vector has the lower-right level character and is supported on the open Borel cell. The residue-class permutation preserves its fixed line, and evaluation at one gives the same scalar as arithmetic Frobenius on the unramified Galois line after the two Carayol dualities. The chosen inertia element acts in the same basis with signs $1,-1$. All copies at other primes carry the same Hecke scalar, and the old unary sources omitting $p$ are unramified.

`O12Local.cuspidal_upAtOne` derives the coefficient shift from the named Whittaker comparison and the existing finite sum. The away components of $a(p)$ pass the relevant level test. `O12Local.localInput` combines the cuspidal result with a separate Eisenstein sector and its Fourier shift, supplying the existing `O12.LocalInput`.

All nine modules compile with `lake env lean -j1`; the 47 theorem axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The Casselman and Carayol printed locators remain UNVERIFIED. The analytic Fourier–Whittaker normalization, the principal-series interchange, and the realization of the actual local factors remain named inputs. The Eisenstein comparison is deferred to the sibling contribution.

Report: `docs/research/rc-o12-local.md`. Results: `scratch/rc-o12-local/log.md`.

Final verified proof and report SHA (parent of this summary): `143b62a4f5a680df26c49f0c0c9c85b862097628`.
