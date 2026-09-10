# Working in this repository

Work on the Widget sync example happens as pull requests against
`gabe/sync-controller`. `main` tracks upstream.

Issue #49 is the register of what the formal work does not cover. It says which
gaps need a decision from the project owner before any code. Read it before
starting work there, and do not reverse a documented design decision on your
own.

## Where things go

- What the system does, and why: `doc/widget_sync_design.md`. Theorems and
  assumptions are there too, but the normative statement of each is
  `widget_sync_controller/trusted/liveness_theorem.rs`.
- Running and operating it: `deploy/widget_sync/README.md`. Building and
  verifying: `build.md`.
- Gaps, and decisions waiting on the owner: issue #49, and nowhere else. Other
  open work: its own issue. An issue body is current state; its comments are
  working notes.
- `discussion/` and `doc/kubernetes_model.md` come from upstream. Do not add to
  them or reorganize them.

State a fact once. Restate it freely in operator terms where a reader with a
cluster in front of them needs it — but then every number and every table in the
restatement must be asserted by a test, and the normative statement must be one
link away. `tools/check-widget-exec-hygiene.sh` and the CRD export test are the
two examples to copy.

## Attribution of GitHub posts

Anything posted to GitHub from a Claude session appears under the repository
owner's account. Every issue, issue comment, pull request description, review
and review comment that Claude writes must therefore begin with the line

    Created by Claude.

as its first line, before any other text. This applies without exception, to
every post, including edits of earlier posts.

# Request adversarial review
For any nontrivial work, before you claim to be done, spawn one or more subagents to do an "adversarial review" and address their findings.

Some possible roles (but consider others depending on the work):
- Kubernetes practitioner who is familiar with upstream conventions and KEPs, and who would need to run this on their production cluster
- Maintainer of the upstream anvil project and academic researcher, who cares about correctness, clarity, and how other academics would review it
- Expert technical writer, who values clear, concise language and abhors AI slop.  They prefer short sentences with a clear subject and object.  They know code comments and docs should not be a changelog of past decisions, but must describe current reality succinctly.
