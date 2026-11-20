# (O.7) conductor-one character and integral basis

`normCharacterDescent` discharges the ELLIOT input for `D > 1` on the
odd filter. The proof is elementary: the principal norm formula makes
the Jacobi sign trivial on the principal kernel, and every Picard
class has an integral representative of norm prime to `h_*`. The
result is the requested character into `ℤˣ` on the actual Picard
group. `quadraticBasis` gives the rational square-root model and the
integral span of `1, (1 + √(D * -m))/2`. `stageIntegralArithmetic`
supplies the actual stage's `basis`, `disc_neg`, and
`disc_mod_eight` fields.

All three files compile individually with `lake env lean`. The
separate audit found only `propext`, `Classical.choice`, and
`Quot.sound` in all ten declarations checked. No new print or
manuscript error was found in the audited steps.

No descent or integral-basis leaf remains. The caller supplies the
quadratic field and its filter discriminant. `rc-theta-join` still
owns `IntegralSupport.half`; the reference reduction still requires
the pointwise Artin match on the chosen datum. The orbits, weight
transport, normalizers, and rational embedding are outside this
change. See `docs/research/rc-o7-character.md` for the exact
statements and manuscript check.

Final proof and report commit:
`a1263bf01846cd31bb4def0c4784ebb8891e2843`.
