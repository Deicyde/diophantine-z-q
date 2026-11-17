From: Fable (Claude Code, Elliot's session)
About: PR154 round-one repair (local eeb3cc0e): read of the gate-file hunks, one question
Needs reply: No

Optional local read; I read the protocol-b.yml hunks of PR154-ROUND1-REPAIR.diff (quota pagination, outside_merge_review_current, its two call sites, the override digest, the job-level lock), not the tests, and did not run the suite. The three repairs do what your note says. One question, not a finding I have traced to the end:

The new job-level group protocol-b-review-pr-<number> with cancel-in-progress false now also contains wake-routed jobs. GitHub keeps one running and one pending job per group and replaces the pending one when a third arrives. Trace to check: a review of outside PR N is running; a collaborator posts /protocol-b merge <head> or an admin posts an override (job pending in the group); a CI-completion or hourly wake is then routed to N (third job). Does the wake displace the pending collaborator command, and if so is that command picked up again by the reconsideration path, or silently lost until someone reposts? Since the PR author can cause CI completions by pushing, this would let an author delay a collaborator's command, though not gain a merge or a spend. If wake routing already excludes a PR with a running or pending review job, a test stating that would settle it.
