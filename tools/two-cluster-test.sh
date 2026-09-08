#!/usr/bin/env bash

## Build the widget sync example and run it across two local kind clusters.
##
## Creates two kind clusters:
##   widget-sync-outer  (kubectl context kind-widget-sync-outer): where users
##                      create Widgets and where the verified sync controller runs;
##   widget-sync-inner  (kubectl context kind-widget-sync-inner): where the
##                      controller keeps the mirrors and where the (unverified)
##                      widget echo controller plays the inner Widget implementation.
## The sync controller reaches the inner cluster with a kubeconfig built from a
## service account token, mounted from a Secret, exactly as it would in production.
##
## Requires kind, kubectl, docker and the prerequisites of deploy.sh.
## Usage:
##   ./tools/two-cluster-test.sh [--build] [extra cargo-verus args]
## Afterwards:
##   kubectl --context kind-widget-sync-outer apply -f deploy/widget_sync/widget.yaml
##   kubectl --context kind-widget-sync-outer get widget demo -o yaml
##   kubectl --context kind-widget-sync-inner get widget demo -o yaml

set -xeu

outer_cluster="widget-sync-outer"
inner_cluster="widget-sync-inner"
outer_ctx="kind-${outer_cluster}"
inner_ctx="kind-${inner_cluster}"
manifests="deploy/widget_sync"
build_controller="no"

if [ $# -gt 0 ]; then
    case "$1" in
        --build) build_controller="local"; shift ;;
    esac
fi

build_image() {
    local app="$1"
    case "$build_controller" in
        local)
            echo "Building ${app} controller binary"
            cargo verus build --release --bin "${app}_controller" -- --no-verify "${@:2}"
            echo "Building ${app} controller image"
            docker build -f docker/controller/Dockerfile \
                -t "local/$(echo "$app" | tr '_' '-')-controller:v0.1.0" \
                --build-arg APP="${app}" .
            ;;
        no)
            echo "Using existing ${app} controller image"
            ;;
    esac
}

build_image widget_sync "$@"
build_image widget_echo "$@"

# Fresh clusters.
for cluster in "$outer_cluster" "$inner_cluster"; do
    if kind get clusters | grep -q "^${cluster}$"; then
        kind delete cluster --name "$cluster"
    fi
    kind create cluster --config "$manifests/kind.yaml" --name "$cluster"
done
kind load docker-image local/widget-sync-controller:v0.1.0 --name "$outer_cluster"
kind load docker-image local/widget-echo-controller:v0.1.0 --name "$inner_cluster"

# The demo CRDs are installed in both clusters (same kinds on both sides).
for crd in crd.yaml crd_gadget.yaml; do
    kubectl --context "$outer_ctx" create -f "$manifests/$crd"
    kubectl --context "$inner_ctx" create -f "$manifests/$crd"
done

# Inner cluster: the echo controller, and the service account the sync controller uses.
kubectl --context "$inner_ctx" apply -f "$manifests/echo_inner.yaml"
kubectl --context "$inner_ctx" apply -f "$manifests/rbac_inner.yaml"

# Build a kubeconfig for the inner cluster from the service account token. The
# outer cluster's pods reach the inner API server through the docker network the
# kind nodes share, so the server address is the inner control-plane container's IP.
# The token is a separate Secret key next to the kubeconfig, referenced with a
# relative tokenFile: kube resolves it against the kubeconfig's directory and
# re-reads it at least once a minute, so rotating the Secret needs no restart.
# An inline token would take precedence and is never re-read.
# The token must not appear in the trace.
set +x
for _ in $(seq 1 30); do
    token="$(kubectl --context "$inner_ctx" -n widget-sync get secret widget-sync-remote-token \
        -o jsonpath='{.data.token}' 2>/dev/null | base64 -d || true)"
    if [ -n "$token" ]; then break; fi
    sleep 1
done
if [ -z "$token" ]; then
    echo "service account token for widget-sync-remote was not issued" >&2
    exit 1
fi
ca_data="$(kubectl --context "$inner_ctx" -n widget-sync get secret widget-sync-remote-token -o jsonpath='{.data.ca\.crt}')"
inner_ip="$(docker inspect -f '{{range .NetworkSettings.Networks}}{{.IPAddress}}{{end}}' "${inner_cluster}-control-plane")"
kubeconfig_dir="$(mktemp -d)"
# No trailing newline: the file content becomes the bearer header verbatim.
printf '%s' "$token" > "$kubeconfig_dir/token"
unset token
set -x
cat > "$kubeconfig_dir/kubeconfig" <<EOF
apiVersion: v1
kind: Config
clusters:
  - name: inner
    cluster:
      server: https://${inner_ip}:6443
      certificate-authority-data: ${ca_data}
users:
  - name: widget-sync-remote
    user:
      tokenFile: token
contexts:
  - name: inner
    context:
      cluster: inner
      user: widget-sync-remote
current-context: inner
EOF

# Outer cluster: RBAC, the remote kubeconfig Secret, and the sync controller.
kubectl --context "$outer_ctx" apply -f "$manifests/rbac.yaml"
kubectl --context "$outer_ctx" -n widget-sync create secret generic widget-sync-remote-kubeconfig \
    --from-file=kubeconfig="$kubeconfig_dir/kubeconfig" \
    --from-file=token="$kubeconfig_dir/token"
rm -rf "$kubeconfig_dir"
kubectl --context "$outer_ctx" apply -f "$manifests/deploy_local.yaml"

kubectl --context "$inner_ctx" -n widget-echo rollout status deployment/widget-echo-controller --timeout=180s
kubectl --context "$outer_ctx" -n widget-sync rollout status deployment/widget-sync-controller --timeout=180s

set +x
echo ""
echo "The widget sync controller runs in kind cluster ${outer_cluster} (context ${outer_ctx})"
echo "and mirrors Widgets into kind cluster ${inner_cluster} (context ${inner_ctx})."
echo "Try:"
echo "  kubectl --context ${outer_ctx} apply -f ${manifests}/widget.yaml"
echo "  kubectl --context ${outer_ctx} get widget demo -o yaml"
echo "  kubectl --context ${inner_ctx} get widget demo -o yaml"
echo "The controller is configured with two kinds; Gadgets are selected by name:"
echo "  kubectl --context ${outer_ctx} apply -f ${manifests}/gadget.yaml"
echo "  kubectl --context ${inner_ctx} get gadget inner -o yaml"
