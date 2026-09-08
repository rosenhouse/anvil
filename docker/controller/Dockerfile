# Build outside the container with `cargo verus build`, then bake the binary.
FROM ubuntu:24.04

ARG APP

COPY target/release/${APP}_controller /usr/local/bin/controller

# The controllers only talk to the API server and write nothing to disk, so
# the image runs as an unprivileged user. Numeric, so a pod's runAsNonRoot can
# be checked without an /etc/passwd entry.
USER 65532:65532

ENTRYPOINT ["/usr/local/bin/controller", "run"]
