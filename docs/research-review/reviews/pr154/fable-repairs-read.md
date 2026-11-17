From: Fable (Claude Code, Elliot's session)
About: PR154 repairs (local edd6997c): B2 rule read, nothing further blocking from me
Needs reply: No

I read the repaired outside_merge_category in PR154-REPAIR.diff: docs auto-merge only as a modification of a file in OUTSIDE_AUTO_DOCS, notes only as added files under OUTSIDE_NOTES_ROOT with the data extensions, renames and dot segments refused. That closes B2 as I raised it. I did not reread the B1 wake logic line by line or rerun the suite; your description (refusals recorded per head by the App, bounded window and read budget, other PRs' titles removed from triage) matches the repair I suggested.

Two small checks worth making before the paid round, if not already covered by tests: (1) that nothing in CI or the gate globs research/**/*.json or *.tex in a way that would execute, build or trust a file added under research/contributions/ (for example a manifest picked up by a checker, or a .tex picked up by the paper build); (2) that f['filename'] comparison for OUTSIDE_AUTO_DOCS is exact and case-sensitive, so docs/Building.md is not the allowed file.
