# Four factored poles on the 389-variable proposal

This proposed stack removes one private square coordinate from each of the
parent's three detector poles and one scalar pole. It produces a conditional
construction in **385 total variables**, with the same 757-digit maximum
coefficient as the parent. The mathematical change is only these four
conics. The inherited arithmetic assumptions and proof obligations remain.

| Construction | Variables | Quadratic residuals | Quartic monomials | Maximum coefficient |
| --- | ---: | ---: | ---: | --- |
| Parent proposal | 389 | 357 | 26,295 | `28902 * 3^1576` |
| Four-conic transport | 385 | 353 | 26,235 | `28902 * 3^1576` |

The quartic is primitive, has degree four and coefficient one on `x0^4`,
and every variable occurs. Its decimal table has 1,048,785 bytes and SHA-256
`47da004230ff7a20c7a0824738422eb9c29c4a6e6de92455e3d956e979161ecf`.
The final diagonal scaling is the parent's unchanged, input-fixed map.

From the repository root, run:

```sh
python3 -B research/factored-pole-reduction/reproduce.py
```

This first runs the parent's full 23-stage reproduction, verifies the parent
import and generated manifests, transports the four conics, checks the
consumer and residual identities, and rebuilds and checks every coefficient.
Outputs go to a fresh directory under `build/`. An existing complete parent
build can be supplied with `--baseline PATH`; its manifests and source hash
are still verified. Use `--output PATH` to choose an absent or empty output
directory. Python 3 and Node are required, as in the parent package; no new
dependency or network access is needed.

[PROOF.md](PROOF.md) gives both maps and the zero branch, distinguishes
stored coordinates from semantic pole inputs, and identifies the unchanged
positivity premises. [APPLICATION_CONTRACT.json](APPLICATION_CONTRACT.json)
records the nine review obligations and exact source bindings. It is an
**unaccepted author contract**, outside the current manuscript register.
The separate replay checker was written in the same session and does not
constitute independent review. Its three negative controls reject a changed
conic coefficient, an added outside consumer, and a restored deleted square.

The construction transports the factored-pole argument already present in
Version 13; it does not claim a new discovery of that argument. Codex prepared
this application in Cameron's session. Attribution and provenance of the
parent research package remain in its `ATTRIBUTION.md` and `PROVENANCE.json`.
Neither this packet nor passing CI supplies independent acceptance of the
new application or of the parent's inherited arithmetic theorem.

The next investigation should measure the biquadratic chart at the parent's
actual consumers before estimating a saving. A custom order-45 rational
logarithm and scalar preparation-zero change are separate later proposals.
They are not part of this four-conic stack.
