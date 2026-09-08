#!/usr/bin/env bash

## Build the widget sync example and run it across three local kind clusters.
##
## Creates three kind clusters:
##   widget-sync-outer    (kubectl context kind-widget-sync-outer): where users
##                        create Widgets and where the verified sync controller runs;
##   widget-sync-inner-a  (context kind-widget-sync-inner-a) and
##   widget-sync-inner-b  (context kind-widget-sync-inner-b): the inner clusters
##                        of the bindings `default/a` and `default/b`, where the
##                        controller keeps the mirrors and where the (unverified)
##                        widget echo controller plays the inner Widget
##                        implementation.
## Each binding is a Secret `<clusterName>-kubeconfig` in the outer namespace
## `default`, of type `cluster.x-k8s.io/secret` and labelled
## `cluster.x-k8s.io/cluster-name: <clusterName>`, key `value`, holding a
## self-contained kubeconfig built from an inner service-account token: the
## Cluster API convention the controller reads bindings by, and the only shape
## it accepts (doc/widget_sync_fanout_design.md, section 1.2).
##
## Requires kind, kubectl, docker and the prerequisites of deploy.sh.
## Usage:
##   ./tools/two-cluster-test.sh [--build] [extra cargo-verus args]
## Afterwards:
##   kubectl --context kind-widget-sync-outer apply -f deploy/widget_sync/widget.yaml
##   kubectl --context kind-widget-sync-outer get widget demo -o yaml
##   kubectl --context kind-widget-sync-inner-a get widget demo -o yaml

set -xeu

outer_cluster="widget-sync-outer"
inner_clusters=("widget-sync-inner-a" "widget-sync-inner-b")
# The binding name of each inner cluster, in the same order: the Secret
# `<name>-kubeconfig` of the outer namespace `default`.
binding_names=("a" "b")
outer_ctx="kind-${outer_cluster}"
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
for cluster in "$outer_cluster" "${inner_clusters[@]}"; do
    if kind get clusters | grep -q "^${cluster}$"; then
        kind delete cluster --name "$cluster"
    fi
    kind create cluster --config "$manifests/kind.yaml" --name "$cluster"
done
kind load docker-image local/widget-sync-controller:v0.1.0 --name "$outer_cluster"
for cluster in "${inner_clusters[@]}"; do
    kind load docker-image local/widget-echo-controller:v0.1.0 --name "$cluster"
done

# The demo CRDs are installed in every cluster (same kinds on both sides).
for crd in crd.yaml crd_gadget.yaml; do
    kubectl --context "$outer_ctx" create -f "$manifests/$crd"
    for cluster in "${inner_clusters[@]}"; do
        kubectl --context "kind-${cluster}" create -f "$manifests/$crd"
    done
done

# Every inner cluster: the echo controller, and the service account the sync
# controller reaches this cluster with.
for cluster in "${inner_clusters[@]}"; do
    kubectl --context "kind-${cluster}" apply -f "$manifests/echo_inner.yaml"
    kubectl --context "kind-${cluster}" apply -f "$manifests/rbac_inner.yaml"
done

# Outer cluster: RBAC first, so the controller can read the binding Secrets as
# soon as it starts.
kubectl --context "$outer_ctx" apply -f "$manifests/rbac.yaml"

# One binding Secret per inner cluster. The kubeconfig is self-contained (the
# service-account token and the CA inline), which is what a Cluster API
# `<clusterName>-kubeconfig` Secret holds: a rotation is the Secret changing,
# and the controller rebuilds the binding's clients then. The outer cluster's
# pods reach an inner API server through the docker network the kind nodes
# share, so the server address is that cluster's control-plane container IP.
# Tokens must not appear in the trace.
for i in "${!inner_clusters[@]}"; do
    cluster="${inner_clusters[$i]}"
    binding="${binding_names[$i]}"
    ctx="kind-${cluster}"
    set +x
    for _ in $(seq 1 30); do
        token="$(kubectl --context "$ctx" -n widget-sync get secret widget-sync-remote-token \
            -o jsonpath='{.data.token}' 2>/dev/null | base64 -d || true)"
        if [ -n "$token" ]; then break; fi
        sleep 1
    done
    if [ -z "$token" ]; then
        echo "service account token for widget-sync-remote was not issued in ${cluster}" >&2
        exit 1
    fi
    ca_data="$(kubectl --context "$ctx" -n widget-sync get secret widget-sync-remote-token -o jsonpath='{.data.ca\.crt}')"
    inner_ip="$(docker inspect -f '{{range .NetworkSettings.Networks}}{{.IPAddress}}{{end}}' "${cluster}-control-plane")"
    kubeconfig_dir="$(mktemp -d)"
    cat > "$kubeconfig_dir/value" <<EOF
apiVersion: v1
kind: Config
clusters:
  - name: ${binding}
    cluster:
      server: https://${inner_ip}:6443
      certificate-authority-data: ${ca_data}
users:
  - name: widget-sync-remote
    user:
      token: ${token}
contexts:
  - name: ${binding}
    context:
      cluster: ${binding}
      user: widget-sync-remote
current-context: ${binding}
EOF
    unset token
    # Type and label as Cluster API writes them: the controller's Secret watch
    # selects on the label and refuses anything of another type.
    kubectl --context "$outer_ctx" -n default create secret generic "${binding}-kubeconfig" \
        --type=cluster.x-k8s.io/secret \
        --from-file=value="$kubeconfig_dir/value"
    kubectl --context "$outer_ctx" -n default label secret "${binding}-kubeconfig" \
        "cluster.x-k8s.io/cluster-name=${binding}"
    rm -rf "$kubeconfig_dir"
    set -x
done

kubectl --context "$outer_ctx" apply -f "$manifests/deploy_local.yaml"

for cluster in "${inner_clusters[@]}"; do
    kubectl --context "kind-${cluster}" -n widget-echo rollout status deployment/widget-echo-controller --timeout=180s
done
kubectl --context "$outer_ctx" -n widget-sync rollout status deployment/widget-sync-controller --timeout=180s

set +x
echo ""
echo "The widget sync controller runs in kind cluster ${outer_cluster} (context ${outer_ctx})"
echo "and mirrors each Widget into the inner cluster its spec.clusterName names:"
echo "  clusterName: a -> ${inner_clusters[0]} (context kind-${inner_clusters[0]})"
echo "  clusterName: b -> ${inner_clusters[1]} (context kind-${inner_clusters[1]})"
echo "Try:"
echo "  kubectl --context ${outer_ctx} apply -f ${manifests}/widget.yaml"
echo "  kubectl --context ${outer_ctx} get widget demo -o yaml"
echo "  kubectl --context kind-${inner_clusters[0]} get widget demo -o yaml"
echo "The controller is configured with two kinds; Gadgets are selected by name,"
echo "so the Gadget named after a binding lands in that binding's cluster:"
echo "  kubectl --context ${outer_ctx} apply -f ${manifests}/gadget.yaml"
echo "  kubectl --context kind-${inner_clusters[0]} get gadget a -o yaml"
