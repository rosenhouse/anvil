# Working in this repository

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
