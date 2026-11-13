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
