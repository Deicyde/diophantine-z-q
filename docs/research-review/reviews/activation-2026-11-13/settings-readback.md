# settings-readback

```json
{
  "observation": {
    "utc": "2026-11-14T02:57:00.050901+00:00",
    "operator": "Astra via Elliot Glazer authorized GitHub session"
  },
  "repository": "elliotglazer/diophantine-z-q",
  "main_at_observation": "f5cccda2468597b693e2f4eb0b58085e5bd89f9b",
  "mode": {
    "name": "PROTOCOL_B_MODE",
    "value": "live",
    "created_at": "2026-11-13T22:58:25Z",
    "updated_at": "2026-11-14T02:41:35Z"
  },
  "allow_auto_merge": true,
  "rules": [
    {
      "type": "deletion",
      "ruleset_source_type": "Repository",
      "ruleset_source": "elliotglazer/diophantine-z-q",
      "ruleset_id": 26781429
    },
    {
      "type": "non_fast_forward",
      "ruleset_source_type": "Repository",
      "ruleset_source": "elliotglazer/diophantine-z-q",
      "ruleset_id": 26781429
    },
    {
      "type": "pull_request",
      "parameters": {
        "required_approving_review_count": 0,
        "dismiss_stale_reviews_on_push": true,
        "required_reviewers": [],
        "require_code_owner_review": false,
        "require_last_push_approval": false,
        "required_review_thread_resolution": true,
        "require_extra_approval_for_unattributed_changes": false,
        "allowed_merge_methods": [
          "merge",
          "squash",
          "rebase"
        ]
      },
      "ruleset_source_type": "Repository",
      "ruleset_source": "elliotglazer/diophantine-z-q",
      "ruleset_id": 26781429
    },
    {
      "type": "required_status_checks",
      "parameters": {
        "strict_required_status_checks_policy": true,
        "do_not_enforce_on_create": false,
        "required_status_checks": [
          {
            "context": "Accepted Lean helpers and axiom audit",
            "integration_id": 15368
          },
          {
            "context": "Construction regeneration and finite checks",
            "integration_id": 15368
          },
          {
            "context": "Paper build",
            "integration_id": 15368
          },
          {
            "context": "Reconstructed quartic and Version 5 inventory",
            "integration_id": 15368
          },
          {
            "context": "Version 12 source and quartic replay (ubuntu-24.04)",
            "integration_id": 15368
          },
          {
            "context": "Version 12 source and quartic replay (windows-2022)",
            "integration_id": 15368
          },
          {
            "context": "Version 13 source and quartic replay (ubuntu-24.04)",
            "integration_id": 15368
          },
          {
            "context": "Version 13 source and quartic replay (windows-2022)",
            "integration_id": 15368
          },
          {
            "context": "Version 6 quartic reproduction and inventory",
            "integration_id": 15368
          },
          {
            "context": "Version 9 odd-product replay (ubuntu-24.04)",
            "integration_id": 15368
          },
          {
            "context": "Version 9 odd-product replay (windows-2022)",
            "integration_id": 15368
          },
          {
            "context": "Complete kernel build and exact-target audit",
            "integration_id": 15368
          },
          {
            "context": "Current 214-variable quartic and numerical certificate",
            "integration_id": 15368
          },
          {
            "context": "current-222",
            "integration_id": 15368
          },
          {
            "context": "Protocol B / review",
            "integration_id": 5663093
          }
        ]
      },
      "ruleset_source_type": "Repository",
      "ruleset_source": "elliotglazer/diophantine-z-q",
      "ruleset_id": 26781429
    }
  ],
  "environment": {
    "name": "protocol-b",
    "protection_rules": [
      {
        "id": 72438993,
        "node_id": "GA_kwDOVjIShs4EUVTR",
        "type": "branch_policy"
      }
    ],
    "deployment_branch_policy": {
      "protected_branches": false,
      "custom_branch_policies": true
    }
  },
  "environment_branch_policies": {
    "total_count": 1,
    "branch_policies": [
      {
        "id": 66638085,
        "node_id": "MDE2OkdhdGVCcmFuY2hQb2xpY3k2NjYzODA4NQ==",
        "name": "main",
        "type": "branch"
      }
    ]
  },
  "app_id": "5663093",
  "limitations": [
    "Authenticated operator readback, not independently obtainable by every anonymous viewer.",
    "No secret values were requested or exported. Key rotation, removal of old installations and removal of repository-level secrets are not established by this snapshot.",
    "Branch/tag secret-access denial and the live protected merge path have not been demonstrated by this settings snapshot."
  ]
}
```

## Owner readback, November 14, 2026

Owner Elliot Glazer supplied this additional readback on November 14, 2026:

- Ruleset: `26781429`, "Main branch PR and CI requirements".
- State: Active.
- Target: `main`.
- Bypass list: empty.
- Supporting observation: Elliot reported that Fable saw the screenshot.

This is the owner's reported settings observation, recorded by Astra. Astra
did not independently inspect that screenshot or perform a new API readback
for this entry. No time of day was supplied. It supplements, without changing,
the November 13 authenticated API snapshot above.

An empty bypass list is a deployment condition for the direct-merge path in
PR89. The condition must remain true; this dated readback is not continuous
monitoring and does not establish what the list contained at earlier times.
