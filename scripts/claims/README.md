# Claims sync

`sync_claims.py` reads the public claims on GitHub and reconciles `docs/one-proof/claims.tsv` with them. It
reads the claims issue (fork issue #14), the statement-checks issue, the packet issues of the no-Lean
readings, the upstream area issues (elliotglazer/diophantine-z-q #37, #74, #76, #78-#86) and the fork's open
pull requests with their comments, with read-only `gh api graphql` calls. It never posts, edits or closes
anything. Pings and releases are printed as a queue; only Jack's batched posting run posts them.

The claims issue, the statement-checks issue and the packet issues come from `docs/one-proof/issues.json`
(shared with `scripts/one_proof/render_open.py`):

```
{"claims_issue": "Deicyde/diophantine-z-q#14", "statement_checks_issue": "", "packet_issues": {}}
```

`packet_issues` maps R1-R10 to `owner/repo#n`. If the file is missing, these defaults apply.

## Claim syntax

One line in a comment on #14, or in the body or a comment of a draft pull request against
Deicyde/diophantine-z-q that links #14. Names are case-sensitive; backticks around a name are allowed.

```
Claiming <field> at <commit>
Claiming reading <packet>
Releasing <field>: <what blocked you>
Progress <field>: <text>
```

- `<field>` is a Lean field name as in OPEN.md. A frontier ID (H-101 or H101, T-3, Z-1), a range of IDs
  (H-98-H-102 or H98-H102; a range of more than 30 IDs, or with a number of more than six digits, is
  reported instead) or a Lean constant name (`AvSplit.T4.MulEtaleAbelianScheme`) also counts; IDs are mapped
  through `docs/one-proof/frontier-crosswalk.tsv` and constant names through
  `docs/one-proof/open-statements.json`. One line may name several fields, separated by commas, slashes or
  "and". The list of names ends at ` at `, `;`, `:` or the end of the sentence; when the text before a `:`
  names nothing (a label), the list is the text after it.
- `at <commit>` is recommended; the parser does not need it.
- A reading packet is claimed on the packet's own issue if it has one; otherwise on the statement-checks
  issue; until that issue exists, on the claims issue (#14).
- The last action per field per person wins: a later `Releasing` releases at once, and a later `Claiming`
  takes the field again. Logins are compared case-insensitively.
- A claim edited into an existing comment or pull request body counts from the edit.
- Quoted lines (starting with `>`), fenced code blocks and HTML comments are ignored, so quoting a claim
  or showing an example claim does not claim anything.
- `Progress` is optional. Any comment by the holder on the claim thread counts as activity, and so does a
  commit on, or a comment by the holder on, the holder's pull request that carries the claim.
- Older claims on the upstream area issues stay valid.
- Every frontier ID, backticked name, dotted constant name or CamelCase name in a claim's list of names that
  maps to no open field is reported, not dropped. So is a claim line that names nothing.

Holders: the project account (Deicyde) is `project`; the maintainer (elliotglazer) is `maintainer`; any
other login is `outside`. These and the upstream issue list are set at the top of the script.

## claims.tsv

One row per field. `hold` is one of:

- `held`: a public claim line, on the claims issue or in a draft pull request that links it; `claim_url` links
  it. The project's own holds may point at a pushed branch instead.
- `interest`: a project row with no public claim (a brief or a reservation); `claim_url` is empty.
- `released`: a claim released by a `Releasing` line or by the lapse rule; `status` holds the blocker. The
  blocker is cleaned first: HTML comments and tags are removed, whitespace is collapsed, leading quote
  characters are dropped, absolute paths (`/a/b`, `~/a/b`, `C:\a\b`) become `[path]`, and it is cut to 200
  characters. The report prints it in full.

Without `--project-claims`, the integrator manages project rows. The script never changes a project row:
when a project claim, a release, a deleted branch or a comment with no parsed claim disagrees with a project
row, it reports the case. It changes an outside or maintainer row only on a parsed claim, a parsed
`Releasing` line, or the lapse rule. A held outside row that no parsed claim backs is kept and reported,
never downgraded. With `--project-claims` (see below), the script is the only writer of `claims.tsv`.

## Commands

Run from the repository root.

```
python3 scripts/claims/sync_claims.py --fetch OUT.json
```
Fetch the comments, pull requests (with their comments) and branch names to `OUT.json` and stop. This is
the only command that uses the network. gh's error output is printed; the fetch fails only when GitHub
returns no data. Every other command fetches to a temporary file first unless `--from-json FILE` is given.

```
python3 scripts/claims/sync_claims.py [--from-json FILE] [--today YYYY-MM-DD]
```
Report what `claims.tsv` would become: the held rows, the rows to add, the rows that change, the rows removed
(with `--project-claims`), the names that map to no open field, and notes (project rows that disagree with
the claims, fields claimed by a second holder, open fields named on a claim line after its list of names,
outside contributors with more than one open claim, claims over the one-claim rule, reading claims, and
releases with their blockers).

```
python3 scripts/claims/sync_claims.py [--from-json FILE] --write [--today YYYY-MM-DD]
```
Update `claims.tsv` in place. Existing rows keep `task`, `status`, `since` and `issue` unless an outside
or maintainer claim is released (the blocker goes into `status`) or a released row is claimed again. A new
outside or maintainer claim on a field with no row gets a row with an empty task, status `claimed`,
`since` the claim date and `issue` the claim thread; a released claim on a field with no row gets a
`released` row. A claim on a field whose row is held by someone else is reported, not written. No row is
deleted. `--today` sets the date the lapse rule counts from (00:00 UTC); the default is now.

```
python3 scripts/claims/sync_claims.py [--from-json FILE] --write --project-claims [--credits FILE]
```
The mode of the claims-sync workflow (`.github/workflows/claims-sync.yml`), the only writer of
`claims.tsv`. As `--write`, and also:

- Project rows follow the project's own public claim and release lines: a project claim makes the project's
  row held, or adds one; a project `Releasing` line releases it. Project rows with no such line are left
  alone and reported.
- A row whose field is no longer open (a fold discharged it) is removed and listed under "rows removed".
- A claim takes a released row of any holder, and an outside or maintainer claim takes a project `interest`
  row (OPEN.md shows a released row as open and an interest row as free to claim).
- A `Releasing` line releases a held row even when the claim it releases is not in the fetch (a branch-held
  project row, or a claim in a pull request that has closed), as long as it is dated on or after the row's
  `since`. A project line naming `@login` does this for that holder's row.
- One claim to start: an outside login with no row in `credits.tsv` (its `contributor` column, a GitHub
  login) gets one held row, for its earliest claim (by date, then field name) while it holds no other.
  Further claims are reported as over the one-claim rule and not written; once the held claim is released,
  the next claim is written. The project and the maintainer are exempt.

The workflow reads the claims once, then on each try resets to the newest main, runs this, and pushes
`claims.tsv` if it changed. If the push loses a race, it tries again from a fresh main (five tries); it never
commits any other file.

```
python3 scripts/claims/sync_claims.py [--from-json FILE] --check FIELD [FIELD ...]
```
Run before a project brief or a gap-wave launch. Exits 1, and prints why, if a field is held by anyone other
than the project (in the fetched claims or in `claims.tsv`), carries the label `good-first` or
`outside-first` in `kinds.tsv`, or names no open field. Exits 0 otherwise.

```
python3 scripts/claims/sync_claims.py [--from-json FILE] --sweep [--today YYYY-MM-DD]
```
Apply the lapse policy and print a queue (TSV: action, field, holder, thread, last activity). Intervals are
compared as times, not calendar days.

- `ping`: no activity by the holder for 14 days, and no ping since.
- `release`: pinged at least 7 days ago with no activity by the holder since.
- `project-stale`: a project hold with no activity for 14 days, for the integrator to review.

A ping counts only if it is a comment by the project account, on the claim thread or the claims issue, that
mentions the holder's login and carries the line

```
Ping (claim lapse): <field>
```

and was posted at least 14 days after the holder's last activity. The batched run writes that line in every
ping. To record a release, the batched run posts `Releasing <field> @<login>: <reason>`; a `Releasing` line by
the project account that names `@login` before the colon releases that holder's claim. `--write` applies the
lapse rule even before that line is posted.

Other options: `--claims`, `--kinds`, `--credits`, `--open`, `--crosswalk` and `--issues` override the paths
under `docs/one-proof/`. The crosswalk is optional; without it, frontier IDs are reported as unmatched.
With `--project-claims` and no `credits.tsv`, every outside login is held to one claim.

## Tests

```
python3 -I -m unittest discover -s scripts/claims -p 'test_*.py'
```

The tests use the files under `fixtures/` only and never call the network. `fixtures/live.json` copies claim
lines from the upstream area issues (labels replaced by neutral text) and adds test comments and pull
requests on the fork.
