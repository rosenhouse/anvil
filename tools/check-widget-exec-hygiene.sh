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
## DynamicObject::kind() reports the API server's kind string, not the model
## kind, for custom resources (issue #19); the wrappers' has_kind is the exec
## counterpart of a model kind test.
if grep -rn '\.kind()' "$dir" | grep -v '^\s*//'; then
    echo "widget sync exec code must test kinds through the wrappers' has_kind, not DynamicObject::kind()" >&2
    exit 1
fi
count=$(grep -rh "as_annotation_value()" "$dir" | grep -v '^\s*//' | grep -o "as_annotation_value()" | wc -l | tr -d ' ')
if [ "$count" != "1" ]; then
    echo "expected exactly one as_annotation_value() call in $dir, found $count" >&2
    exit 1
fi

## The trusted exec surface of the pair is enumerated in the design doc
## (section 3). A new external_body or external item anywhere under the
## controller must be added there deliberately, so its location is pinned here.
root=src/controllers/widget_sync_controller
expected="$root/model/install.rs:3
$root/trusted/exec_types.rs:1"
actual=$(grep -rc --exclude-dir=target --exclude-dir='target-*' 'external_body' "$root" | grep -v ':0$' | sort)
if [ "$actual" != "$expected" ]; then
    echo "external_body items under $root changed; update doc/widget_sync_design.md section 3 and this script" >&2
    echo "expected:" >&2; echo "$expected" >&2
    echo "found:" >&2; echo "$actual" >&2
    exit 1
fi
if grep -rn --exclude-dir=target --exclude-dir='target-*' 'verifier(external)\]' "$root"; then
    echo "widget sync code must not declare verifier(external) items" >&2
    exit 1
fi
echo "widget sync exec hygiene: ok"
