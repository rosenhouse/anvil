# How to build, verify and run controllers

This project uses [`cargo verus`](https://github.com/verus-lang/verus). All third-party dependencies (kube, k8s-openapi, tokio, …) live in the top-level `Cargo.toml`; the Verus standard library (`vstd`) is tracking the `main` branch of [verus-lang/verus](https://github.com/verus-lang/verus).

## Source organization

`src/`

- `reconciler/` This defines the API for implementing `reconcile()` as a state machine.
- `shim_layer/` A layer that intercepts the requests returned by each state transition of `reconcile()`, issues the requests to the Kubernetes API server (or other endpoints customized by developers), and feeds the response to the next state transition of `reconcile()`. This layer is built on top of [kube](https://github.com/kube-rs/kube).
- `kubernetes_cluster/` A model of the core components in a Kubernetes cluster that controllers often interact with, including API servers, etcd, and some built-in controllers. It is written as a TLA-style state machine.
- `kubernetes_api_objects/` A library that defines commonly used Kubernetes API objects (e.g., Pod, ConfigMap, StatefulSet, Service, etc.). Most definitions are imported from [k8s-openapi](https://github.com/Arnavion/k8s-openapi) (which is also used by [kube](https://github.com/kube-rs/kube)) with a wrapper that allows formal reasoning on these objects.
- `state_machine/` A library for defining TLA-style state machines, used by `kubernetes_cluster/`.
- `controllers/` Example controllers we built and verified using Anvil (`rabbitmq_controller/`, `vreplicaset_controller/`, `vdeployment_controller/`, `vstatefulset_controller/`, and `widget_sync_controller/`, which holds the Widget sync controller and janitor), plus their `composition/` proofs. See `doc/verified_controllers.md`.
- `crds.rs` Custom resource type definitions (`kube`-derived), shared by the controllers and the e2e tests.
- `bin/` Binary entry points, one per controller, admission webhook, and verification target (e.g., `esr_composition.rs`).
- `tla_demo.rs` Proof code for the TLA demo.

`e2e/`: end-to-end tests for controllers

`tools/`: scripts to setup environment, build controller images and deploy controllers

Anvil is packed into a single cargo package (`verifiable-controllers`); see the sections below for the `cargo verus` build/verify commands.

### Dependencies

```
kind_version: 0.23.0
go_version:   "^1.20"
```

Run `./tools/setup-verus.sh` to fetch, build, and wire up a local Verus binary.

## Build and verify

Most verification targets are library modules (under `src/controllers/`, `src/kubernetes_cluster/`, etc.). To narrow scope, use `cargo verus focus --lib -- --verify-module <mod>`; `verify` rejects partial-verification flags. `--verify-only-module` excludes a module's descendants, so naming a top-level module with it verifies nothing:

```sh
# Verify the entire Anvil framework + every controller and proof:
cargo verus verify --lib

# Verify a single controller, scoped to its module:
cargo verus focus --lib -- --verify-module vreplicaset_controller

# Verify the composition proofs:
cargo verus focus --lib -- --verify-module composition

# Verify the TLA demo (proof code lives in src/tla_demo.rs):
cargo verus focus --lib -- --verify-module tla_demo
```

Pass extra Verus flags after `--`. Replace `--lib` with `--bin <name>` to verify a specific binary's own source.

### Working on the proofs

- Several `--verify-only-module` flags can be combined in one `focus` run,
  for example a proof file plus everything that imports it. Add
  `--multiple-errors 8` to see more than the first failure.
- `cargo verus focus` decides freshness by source checksums and does not
  record the verifier flags of the previous run. After editing a proof and
  changing the module set, delete the crate's fingerprint under the target
  directory before re-running, or the previous output is replayed:
  `find target -path '*fingerprint/verifiable-controllers-*' -exec rm -rf {} +`.
  Separate `CARGO_TARGET_DIR`s for build-only, targeted and full runs avoid
  lock contention and rebuilds.
- The crate must also build with plain `cargo build --lib` (CI checks it,
  and `cargo test --lib` runs the executable-model and wrapper unit tests on
  that build). Spec and proof items are erased there, so import them with
  glob imports, never by name.
- A full `cargo verus verify --lib` takes about an hour on four cores; run
  the touched modules first and the full run last.
- Verus habits that mattered in this repository: two `choose` expressions
  over extensionally equal predicates with different free variables are not
  provably equal; to instantiate a `tla_forall`, restate its closure
  literally and assert the instance; a struct literal in `ensures` or in an
  `if` condition needs parentheses; `#[trigger]` is needed on `choose` and
  `exists` bodies and arithmetic is not allowed in a trigger; distinct string
  literals need `reveal_strlit`; a lemma that exceeds its budget is better
  split than given an `rlimit`.
- `tools/check-widget-exec-hygiene.sh` (run by CI) pins the Widget pair's
  trusted exec surface; a new `external_body` under that controller must be
  added to the design doc and to the script deliberately.

## Build and test

### Build a controller binary (fast, no verification)

```sh
cargo verus build --bin <controller_name> -- --no-verify
```

The binary lands in `target/debug/<controller_name>` (or
`target/release/<controller_name>` if you add `--release`).

### Test pipeline

1. Build the controller binary with `cargo verus build` on the host.
2. Bake the binary into a controller Docker image with
   `docker/controller/Dockerfile`.
3. Set up a kind cluster and load the image.
4. Apply the e2e tests from `e2e/src/` and the workload from `deploy/`
   via `tools/deploy.sh`.

Steps 1–3 are automated:

```
./tools/local-test.sh <controller_name> [--build]
  --build     build via `cargo verus build` on the host, then make the image
  (no flag)   reuse an existing local image named local/<app>-controller:v0.1.0
```

Step 4:

```sh
cd e2e
cargo run -- <controller_name>
```

The Widget sync controller and janitor run across two kind clusters instead:
`./tools/two-cluster-test.sh [--build]` builds the `widget_sync` and
`widget_echo` images, creates both clusters and deploys them, and
`cd e2e && cargo run -- widget-sync` runs the test. See
`deploy/widget_sync/README.md` and `doc/widget_sync_design.md`.

See `.github/workflows/ci.yml` for the exact CI invocations.
