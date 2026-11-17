# Uniform odd-power detectors: 376 variables, 425 digits

Conditional research above #18. Each detector replaces three e-power coordinates by two q1-power coordinates. Its order12 weight becomes q1^23 and its order46 weight becomes q1^91. New normalized one-place inputs preserve the required valuations; the proof constructs new private pole witnesses. Scalar order31 and anchor3^2010 remain.

```sh
python3 -B research/odd-power-detectors/reproduce.py --output build/power376
python3 -B scripts/check_audit_history.py --self-test
```

Python standard library and Node suffice. Full output: 376 variables including input,345 residuals,25,964 quartic monomials,425digits/1410bits, content one and input fourth-power coefficient one. The complete decimal expansion is generated and uploaded by CI; its exact hash is in EXPECTED.json. No LP solver is needed.

Read PROOF.md, APPLICATION_CONTRACT.json, FINDINGS.json and HANDOFF.md. Finite source/gate/transport/coefficient checks do not prove the changed uniform arithmetic application. This author packet requires a separately authored source-bound review. Prior investigations remain archived in scalar-row-reduction/prior-investigation. No current manuscript/PDF or global arithmetic theorem is replaced.
