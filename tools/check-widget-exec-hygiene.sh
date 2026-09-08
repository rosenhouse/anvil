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

## An uninterp spec function is trusted in the same way an external_body body
## is: it means whatever the exec side does with it. The pair's are the three
## reconcile states' Marshallable instances (marshal and unmarshal each) and
## default_status_rest. The disturber's edit is not among them any more: it is
## a closed definition with a proved lemma. A new one is a new assumption, so
## the count is pinned per file like the shape files' below.
uninterp_expected="$root/model/install.rs:6
$root/trusted/spec_types.rs:1"
uninterp_actual=$(grep -rc --exclude-dir=target --exclude-dir='target-*' 'uninterp spec fn' "$root" | grep -v ':0$' | sort)
if [ "$uninterp_actual" != "$uninterp_expected" ]; then
    echo "uninterp spec fn items under $root changed; update doc/widget_sync_design.md section 3 and this script" >&2
    echo "expected:" >&2; echo "$uninterp_expected" >&2
    echo "found:" >&2; echo "$uninterp_actual" >&2
    exit 1
fi

## The rest of the pair's trusted surface does not live under the controller:
## the shape's wrappers and the registry are in kubernetes_api_objects, where
## they are shared with anything else generic over kinds. They are trusted in
## the same way -- an external_body body is read, not verified, and an uninterp
## spec function means whatever the exec side does -- so their counts are
## pinned here too, per file: external_body, verifier(external), uninterp.
## spec/model_kind.rs is listed with three zeros on purpose: model_kind and its
## injectivity are proved, and a trusted item appearing there would be a change
## of what the distinctness hypotheses rest on.
## doc/widget_sync_design.md section 3 and doc/widget_sync_fanout_design.md
## section 2.3 enumerate these items; update them with this list.
shape_files="src/kubernetes_api_objects/exec/registry.rs
src/kubernetes_api_objects/exec/synced_object.rs
src/kubernetes_api_objects/spec/model_kind.rs
src/kubernetes_api_objects/spec/synced_object.rs"
shape_expected="src/kubernetes_api_objects/exec/registry.rs:4:2:0
src/kubernetes_api_objects/exec/synced_object.rs:35:11:0
src/kubernetes_api_objects/spec/model_kind.rs:0:0:0
src/kubernetes_api_objects/spec/synced_object.rs:1:0:4"
shape_actual=$(for file in $shape_files; do
    printf '%s:%s:%s:%s\n' "$file" \
        "$(grep -c '#\[verifier(external_body)\]' "$file" || true)" \
        "$(grep -c '#\[verifier(external)\]' "$file" || true)" \
        "$(grep -c '^pub uninterp spec fn' "$file" || true)"
done)
if [ "$shape_actual" != "$shape_expected" ]; then
    echo "the trusted items of the shape wrappers changed; update the design docs and this script" >&2
    echo "expected (file:external_body:external:uninterp):" >&2; echo "$shape_expected" >&2
    echo "found:" >&2; echo "$shape_actual" >&2
    exit 1
fi
echo "widget sync exec hygiene: ok"
