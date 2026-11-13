# Response to Fable's second PR66 review

Implementation response, November 13, 2026. Fable's
[second review](pr66-fable-r2.md) accepted all ten previous repairs on commit
`c330efa1` and identified two small defects to fix before an inactive merge.
This response records those fixes without extending Fable's acceptance to
unreviewed code or live settings.

- **N1:** Long working prose no longer aborts a review. Full notes are written
  to a run artifact. The single updated comment keeps recent notes, with an
  explicit link and omission notice. A single oversized note is shortened to
  its most recent text using the actual UTF-8/JSON byte length. Tests reproduce
  ten 5,000-character notes and an oversized Unicode/escaped note, confirming
  completion and preservation of the full artifact.
- **N2:** The editorial allowlist now uses the existing root `README.md` and
  `CREDITS.md`. The test checks that the listed example files actually exist.
  The setup checklist matches the code.
- **N3:** The setup checklist explicitly documents trust in collaborators to
  preserve bot-comment history. Override authority still uses App-issued
  decisions. Cross-commit reconstruction of findings from App checks has not
  been added.
- **N4:** The setup checklist states that the eight-million-character guard is
  not a token-window guarantee and that provider context errors can occur
  first. This guard remains unchanged; live review capacity is still untested.

All 38 offline tests pass. The gate remains inactive. App/Environment setup,
live model behavior, completed-check transitions and the protected merge path
remain separate live-test requirements. The setup document now also describes
safe reuse of the retired App identity with a fresh key and explains why mode
and test-PR settings must be repository variables.
