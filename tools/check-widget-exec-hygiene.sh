#!/usr/bin/env bash
## The widget sync reconcilers must not depend on uid or resourceVersion values
## except through equality. The exec code gets uids as opaque tokens (UidToken);
## the one place a token becomes data is the parent-uid annotation written by
## make_inner. This check keeps it that way.
set -eu
dir=src/controllers/widget_sync_controller/exec
if grep -rn "resource_version()" "$dir"; then
    echo "widget sync exec code must not read resourceVersion values" >&2
    exit 1
fi
count=$(grep -rho "as_annotation_value()" "$dir" | wc -l | tr -d ' ')
if [ "$count" != "1" ]; then
    echo "expected exactly one as_annotation_value() call in $dir, found $count" >&2
    exit 1
fi
echo "widget sync exec hygiene: ok"
