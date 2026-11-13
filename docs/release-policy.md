# Record releases

## Complete manuscript required for every official record

Every new result promoted as an official current or best record of this project must have a complete updated manuscript in **both TeX and PDF**. This includes records within a stated class of coefficient representations.

The release must include:

- A versioned `.tex` entry point and all local TeX project files needed to build it.
- The matching versioned `.pdf`, built from that exact source and the identified build inputs.
- The complete argument for the announced record in the current manuscript, including the construction, its defining property, parameter qualifications and any necessary repairs. Earlier project arguments may be reused in the current edition, including in appendices or local TeX inputs that compile into its PDF. A chronological chain of separate optimization notes or older manuscripts is not a substitute. References to published theorems and separate computational artifacts remain subject to Protocol_D.
- A release manifest identifying both files, their hashes, the build command and inputs, and the independent review of incorporation, source/PDF correspondence and the assembled argument. The version, date and quantitative claims must agree across the source, PDF, record listing, artifact catalog and cumulative handoff.

Contributors may submit a short note or incomplete candidate PR. They do not have to rewrite the manuscript themselves. Maintainers are responsible for integrating accepted work and obtaining the required independent acceptance before publishing it as a new official record. Until then, label the improvement as a candidate or accepted note awaiting release and keep the last complete record release clearly identified.

The current manuscript profile is [current-manuscript.json](current-manuscript.json). The paper build must use its current target, not a hardcoded historical edition. File, hash and build checks do not establish mathematical completeness or authenticate a contributor's review claim. Required independent Astra acceptance must cover the complete current argument and the actual source/PDF pair. Withhold record-release acceptance if either file, its provenance, incorporation or required review is missing.

This project-specific requirement supplements [Protocol_D](research-review/PROTOCOL.md). It does not retroactively relabel historical releases or require unrelated non-release contributions to produce a new manuscript.


## Release conventions

Publish matching versioned TeX and PDF files, coefficient tables, reproducible checks, current documentation, review records and the cumulative research handoff to the configured project repositories. Preserve earlier reviewed versions as historical records. Starting with Version 13, the manuscript version subtitle has no trailing period.

## Every published manuscript revision gets the next integer version

Every newly published revision of the official current state-of-the-art manuscript advances the previous published ordinary integer Version by exactly one. This applies to editorial corrections and changes of coefficient representation as well as stronger mathematical results. A Busy Beaver representation uses the next ordinary Version; a `BB` suffix or other alternate edition label cannot replace the increment. The title, current-manuscript profile, versioned TeX/PDF paths and recorded build must agree.

Compare the candidate with the preceding **published** profile, not with the preceding draft commit. A change to the current TeX, matching PDF or declared local TeX inputs requires the next version. An unchanged pair and unchanged declared inputs retain their version. Updating only build diagnostics or other build metadata, while those artifact bytes remain identical, does not require an increment. Repeated pre-release branch revisions retain the prospective number until publication. If another release lands first, update against that published base and use its next integer.

Preserve the old published TeX/PDF pair at its original paths and bytes; do not rewrite or relabel it as the new edition. Keep its declared local inputs intact when preparing its successor, using new paths for changed inputs. The current pair uses `manuscripts/quartic_vN.tex` and `manuscripts/quartic_vN.pdf`, where `N` is the ordinary integer version. Existing earlier numbered pairs also remain immutable. This rule applies prospectively and does not renumber historical publications.

The `Research checks / Paper build` job runs `scripts/check_version_increment.py --github-event` in addition to the existing current-pair and build checks. For a pull request to the publication branch, the comparison uses the runner's `pull_request.base.sha` and requires it to match the live default branch. A stale concurrent pull request must update and rerun. A default-branch push uses the trusted event's `before` commit. Pre-release branch pushes, integration pull requests and manual branch runs compare against the event repository's live default branch, so draft iterations do not consume publication numbers. Candidate files cannot choose that baseline. A missing or invalid required baseline fails the transition check.

Manual runs on the default branch and tag pushes perform an explicitly labeled current-state check, not a publication-transition acceptance. Local maintainers can use `--base-ref <published-commit>` for a diagnostic comparison or `--state-only` for a state check; GitHub Actions rejects these alternatives and requires its event mode. Protected review and repository merge controls must still establish authorization, review the policy implementation and require a current base. These finite version checks do not authenticate a reviewer or prove the manuscript.
