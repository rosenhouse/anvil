// The binding manager (doc/widget_sync_fanout_design.md, sections 1.2 to 1.4 and
// 3.4). A binding is a pair (namespace, clusterName) of the outer cluster; its
// inner cluster is reached through the Secret `<clusterName>-kubeconfig` in
// `namespace`, key `value`, the Cluster API convention: type
// `cluster.x-k8s.io/secret`, labelled `cluster.x-k8s.io/cluster-name:
// <clusterName>`. The manager watches those Secrets in every namespace and, per
// binding:
//
//   - checks the kubeconfig against the shape a Cluster API kubeconfig has
//     (validate_kubeconfig) and builds the pair of clients from it,
//   - asks the inner cluster, with a SelfSubjectAccessReview per verb, whether
//     the credential may do what the reconcilers need in the binding's
//     namespace (section 1.4),
//   - creates or verifies the claim, the ConfigMap kube-system/anvil-sync-claim
//     that records which binding owns the inner cluster (section 1.3),
//   - registers the clients in the process's ClusterClients and starts the
//     binding's runners: the janitors of every configured kind, and the
//     same-name watch that feeds the sync runners of the outer cluster.
//
// A binding that is not registered has its requests answered with Timeout, so
// its outer objects read `Synced=False/InnerUnreachable`; a binding that is
// registered as refused (a claim held by someone else, or a denied verb) has
// them answered with Forbidden, so its outer objects read
// `Synced=False/Forbidden` with `Stalled=True`. Nothing here ever exits the
// process: one bad binding must not take down the others.
//
// This module is the shim's, not the controllers': what a binding's janitors
// are is the binary's business and reaches the manager as the `start_runners`
// callback.
use crate::kubernetes_api_objects::exec::api_resource::{ClusterId, ClusterRef};
use crate::kubernetes_api_objects::exec::registry::RegistryEntry;
use crate::shim_layer::controller_runtime::{
    remote_clients_from_kubeconfig_yaml, BindingStatus, ClusterClients, RemoteClients,
};
use anyhow::{anyhow, Result};
use futures::{channel::mpsc, StreamExt};
use k8s_openapi::api::authorization::v1::{ResourceAttributes, SelfSubjectAccessReview, SelfSubjectAccessReviewSpec};
use k8s_openapi::api::core::v1::{ConfigMap, Namespace, Secret};
use kube::api::{Api, ObjectMeta, PostParams, ResourceExt};
use kube::config::Kubeconfig;
use kube::core::ErrorResponse;
use kube::runtime::{reflector::ObjectRef, watcher, WatchStreamExt};
use kube::Client;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::future::Future;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::watch;
use tokio::time::Instant;
use tracing::{debug, info, warn};

type KubeDynamicObject = kube::api::DynamicObject;

// The Secret of the binding `(namespace, name)` is `<name><SECRET_SUFFIX>` in
// `namespace`, and its kubeconfig is the key `value`.
pub const SECRET_SUFFIX: &str = "-kubeconfig";
pub const SECRET_KEY: &str = "value";

// The rest of the Cluster API convention, which the watch is narrowed to: the
// Secret's type is `cluster.x-k8s.io/secret` and it carries the label
// `cluster.x-k8s.io/cluster-name`, whose value is the cluster it belongs to.
// A Secret that is merely named `<something>-kubeconfig` is not a binding: the
// watch selects on the label, and the type and the label's value are checked on
// every event, so an ordinary Secret of that name — a backup, a user's own
// kubeconfig — is never handed to a client.
pub const SECRET_TYPE: &str = "cluster.x-k8s.io/secret";
pub const CLUSTER_NAME_LABEL: &str = "cluster.x-k8s.io/cluster-name";

// The claim: a ConfigMap of the inner cluster, in kube-system so that it lives
// where a workload cluster's own bookkeeping does and is not swept away with a
// tenant namespace.
pub const CLAIM_NAMESPACE: &str = "kube-system";
pub const CLAIM_NAME: &str = "anvil-sync-claim";
pub const CLAIM_OWNER_KEY: &str = "owner";
pub const CLAIM_NAMESPACE_KEY: &str = "namespace";
pub const CLAIM_CLUSTER_NAME_KEY: &str = "clusterName";

// A bound binding is re-checked (access and claim) this often, so that releasing
// a claim by hand recovers a refused binding without a restart.
pub const RECHECK_INTERVAL: Duration = Duration::from_secs(300);

// A binding whose inner cluster did not answer is retried after BACKOFF_START,
// doubling to at most BACKOFF_MAX.
pub const BACKOFF_START: Duration = Duration::from_secs(1);
pub const BACKOFF_MAX: Duration = Duration::from_secs(60);

// How often the manager looks for work that has come due (a retry, a re-check).
const TICK: Duration = Duration::from_secs(1);

// The bound on one attempt end to end: building the clients, the access check
// and the claim. Each request is bounded on its own by the manager's request
// timeout, but a connection that is neither refused nor answered can outlast
// that, so the attempt as a whole is bounded too. It is generous, since an
// attempt is a handful of round trips to a cluster that may be far away; what
// it rules out is an attempt that never ends.
const ATTEMPT_TIMEOUT: Duration = Duration::from_secs(45);

// How many same-name triggers may be in flight per kind before the manager drops
// them. Dropping one costs at most one requeue interval of latency, which is
// what the trigger saves; the bound keeps a busy inner cluster from growing the
// queue without limit.
const TRIGGER_QUEUE: usize = 256;

/// binding_of_secret is the binding a Secret names, `None` for a Secret that is
/// not a kubeconfig of ours. `<name>-kubeconfig` in `ns` is the binding
/// `(ns, name)`; the suffix alone (`-kubeconfig`) names no cluster and is not one.
pub fn binding_of_secret(namespace: &str, name: &str) -> Option<ClusterRef> {
    let cluster = name.strip_suffix(SECRET_SUFFIX)?;
    if cluster.is_empty() || namespace.is_empty() {
        return None;
    }
    // The model kind of a mirror is `<kind name>@<namespace>/<clusterName>`,
    // and the theorems' distinctness hypotheses are discharged by that being
    // injective, which holds because the parts are free of the separators
    // (spec::model_kind::cluster_ref_ok). A DNS name is, so this is defensive
    // only -- a Kubernetes name or namespace cannot hold either character --
    // but it is the exec side of a hypothesis the proofs rest on, so it is
    // checked rather than assumed.
    if [namespace, cluster].iter().any(|part| part.contains('@') || part.contains('/')) {
        return None;
    }
    Some(ClusterRef::new(namespace.to_string(), cluster.to_string()))
}

/// binding_of_capi_secret is binding_of_secret plus the rest of the Cluster API
/// convention: the Secret's `type` must be `cluster.x-k8s.io/secret` and its
/// label `cluster.x-k8s.io/cluster-name` must be the cluster its name says it
/// is. The label is what the watch selects on and the authority on the cluster
/// name; requiring it to agree with the name keeps one Secret from being two
/// bindings depending on which of the two is read.
pub fn binding_of_capi_secret(
    namespace: &str,
    name: &str,
    secret_type: Option<&str>,
    cluster_label: Option<&str>,
) -> Option<ClusterRef> {
    if secret_type != Some(SECRET_TYPE) {
        return None;
    }
    let binding = binding_of_secret(namespace, name)?;
    if cluster_label != Some(binding.name.as_str()) {
        return None;
    }
    Some(binding)
}

/// validate_kubeconfig is the trust boundary of a binding's credential. A
/// kubeconfig is a program as much as it is a credential: kube-client honours
/// `users[].user.exec` (it runs a command in this pod), `auth-provider` with a
/// `cmd-path`, `tokenFile` (it reads any file this pod can read — the mounted
/// ServiceAccount token, say — and sends it to whatever `server` the same
/// document names), `proxy-url` and `insecure-skip-tls-verify`. Whoever can
/// create a Secret of the Cluster API convention in a namespace therefore
/// decides what this controller does for that namespace's bindings, so the
/// document is held to the shape a Cluster API workload-cluster kubeconfig has
/// and nothing else: exactly one cluster, one user and one context, an
/// `https://` server, and credentials given as data, never as a path or a
/// command.
///
/// The reasons are what the warn log of a rejected Secret says; they name the
/// offending field, so an operator can see which rule a hand-written kubeconfig
/// broke.
pub fn validate_kubeconfig(kubeconfig: &Kubeconfig) -> Result<(), String> {
    // Exactly one of each: a document with a second cluster or user is either
    // not a workload cluster's kubeconfig or an attempt to have the current
    // context select something other than what was reviewed.
    if kubeconfig.clusters.len() != 1 {
        return Err(format!("it declares {} clusters; exactly one is required", kubeconfig.clusters.len()));
    }
    if kubeconfig.auth_infos.len() != 1 {
        return Err(format!("it declares {} users; exactly one is required", kubeconfig.auth_infos.len()));
    }
    if kubeconfig.contexts.len() != 1 {
        return Err(format!("it declares {} contexts; exactly one is required", kubeconfig.contexts.len()));
    }
    let named_cluster = &kubeconfig.clusters[0];
    let cluster = named_cluster
        .cluster
        .as_ref()
        .ok_or_else(|| format!("its cluster {:?} has no cluster section", named_cluster.name))?;
    match cluster.server.as_deref() {
        // Plain http would send the credential in the clear; anything else
        // (unix://, a bare host) is not an API server address we will dial.
        Some(server) if server.starts_with("https://") => {}
        Some(server) => return Err(format!("its server {:?} is not https://", server)),
        None => return Err("its cluster has no server".to_string()),
    }
    if cluster.insecure_skip_tls_verify == Some(true) {
        return Err("it sets insecure-skip-tls-verify, which would let anything answer for the inner cluster".to_string());
    }
    if cluster.proxy_url.is_some() {
        return Err("it sets proxy-url, which would route the credential through a third party".to_string());
    }
    // Paths are the attacker's read primitive: the file is read from this pod's
    // filesystem. The data forms carry the material in the document itself.
    if cluster.certificate_authority.is_some() {
        return Err("it sets certificate-authority, a path in this pod; use certificate-authority-data".to_string());
    }
    let named_user = &kubeconfig.auth_infos[0];
    let user = named_user
        .auth_info
        .as_ref()
        .ok_or_else(|| format!("its user {:?} has no user section", named_user.name))?;
    if user.exec.is_some() {
        return Err("it sets exec, which would run a command in this pod".to_string());
    }
    if user.auth_provider.is_some() {
        return Err("it sets auth-provider, which can run a command in this pod".to_string());
    }
    if user.token_file.is_some() {
        return Err("it sets tokenFile, a path in this pod; use an inline token".to_string());
    }
    if user.client_certificate.is_some() {
        return Err("it sets client-certificate, a path in this pod; use client-certificate-data".to_string());
    }
    if user.client_key.is_some() {
        return Err("it sets client-key, a path in this pod; use client-key-data".to_string());
    }
    // The one context must be the one that is current and must name the one
    // cluster and the one user, so that what was checked here is what
    // Config::from_custom_kubeconfig builds the clients from.
    let named_context = &kubeconfig.contexts[0];
    let context = named_context
        .context
        .as_ref()
        .ok_or_else(|| format!("its context {:?} has no context section", named_context.name))?;
    if context.cluster != named_cluster.name {
        return Err(format!(
            "its context names the cluster {:?}, which it does not declare",
            context.cluster
        ));
    }
    if context.user != named_user.name {
        return Err(format!("its context names the user {:?}, which it does not declare", context.user));
    }
    match kubeconfig.current_context.as_deref() {
        Some(current) if current == named_context.name => {}
        Some(current) => {
            return Err(format!("its current-context {:?} is not its one context {:?}", current, named_context.name))
        }
        None => return Err("it has no current-context".to_string()),
    }
    Ok(())
}

/// checked_kubeconfig parses the `value` of a binding's Secret and holds it to
/// validate_kubeconfig. The clients are built from the same text
/// (remote_clients_from_kubeconfig_yaml parses it again); parsing is a pure
/// function of the string, so what was checked is what is built.
fn checked_kubeconfig(yaml: &str) -> Result<(), String> {
    let kubeconfig = Kubeconfig::from_yaml(yaml).map_err(|e| format!("it does not parse ({})", e))?;
    validate_kubeconfig(&kubeconfig)
}

/// The claim's three fields (doc/widget_sync_fanout_design.md, section 1.3).
/// Two claims are the same claim exactly when all three agree, so a copied
/// kubeconfig, which keeps the cluster but changes the namespace or the cluster
/// name, is a mismatch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Claim {
    pub owner: String,
    pub namespace: String,
    pub cluster_name: String,
}

impl Claim {
    /// The claim `binding` would write, `owner` being the outer cluster id.
    pub fn of(owner: &str, binding: &ClusterRef) -> Claim {
        Claim {
            owner: owner.to_string(),
            namespace: binding.namespace.clone(),
            cluster_name: binding.name.clone(),
        }
    }

    /// The claim a ConfigMap holds. A missing key reads as the empty string, so
    /// a hand-written ConfigMap of the right name is a mismatch, not a match.
    pub fn from_data(data: Option<&BTreeMap<String, String>>) -> Claim {
        let get = |key: &str| data.and_then(|d| d.get(key)).cloned().unwrap_or_default();
        Claim {
            owner: get(CLAIM_OWNER_KEY),
            namespace: get(CLAIM_NAMESPACE_KEY),
            cluster_name: get(CLAIM_CLUSTER_NAME_KEY),
        }
    }

    pub fn data(&self) -> BTreeMap<String, String> {
        BTreeMap::from([
            (CLAIM_OWNER_KEY.to_string(), self.owner.clone()),
            (CLAIM_NAMESPACE_KEY.to_string(), self.namespace.clone()),
            (CLAIM_CLUSTER_NAME_KEY.to_string(), self.cluster_name.clone()),
        ])
    }

    pub fn config_map(&self) -> ConfigMap {
        ConfigMap {
            metadata: ObjectMeta {
                name: Some(CLAIM_NAME.to_string()),
                namespace: Some(CLAIM_NAMESPACE.to_string()),
                ..ObjectMeta::default()
            },
            data: Some(self.data()),
            ..ConfigMap::default()
        }
    }

    /// The holder, as the warn log of a refused binding names it.
    pub fn holder(&self) -> String {
        format!("owner={:?} binding={}/{}", self.owner, self.namespace, self.cluster_name)
    }
}

/// The doubling retry delay of a binding whose inner cluster does not answer.
#[derive(Clone, Debug)]
pub struct Backoff {
    next: Duration,
}

impl Backoff {
    pub fn new() -> Backoff {
        Backoff { next: BACKOFF_START }
    }

    /// The delay to wait before the next attempt; the one after that is twice
    /// as long, up to BACKOFF_MAX.
    pub fn next_delay(&mut self) -> Duration {
        let delay = self.next;
        self.next = std::cmp::min(self.next * 2, BACKOFF_MAX);
        delay
    }

    /// Back to the start, after an attempt that got through.
    pub fn reset(&mut self) {
        self.next = BACKOFF_START;
    }
}

impl Default for Backoff {
    fn default() -> Self {
        Backoff::new()
    }
}

/// One configured kind, as the binding manager needs it: the discovered entry
/// (its ApiResource is the same in every cluster), the resource the access
/// check asks about, and where the same-name triggers of the kind's mirrors go.
#[derive(Clone)]
pub struct BindingKind {
    pub entry: RegistryEntry,
    pub group: String,
    pub plural: String,
    pub triggers: mpsc::Sender<ObjectRef<KubeDynamicObject>>,
}

impl BindingKind {
    /// `<plural>.<group>`, or the plural alone in the core group: how a
    /// SelfSubjectAccessReview's answer is logged.
    pub fn resource(&self) -> String {
        if self.group.is_empty() {
            self.plural.clone()
        } else {
            format!("{}.{}", self.plural, self.group)
        }
    }
}

/// same_name_triggers builds the channel a kind's sync runner is triggered
/// through: the receiver goes to `run_dyn_controller_with_triggers`, the sender
/// into the `BindingKind` the manager is given.
pub fn same_name_triggers() -> (mpsc::Sender<ObjectRef<KubeDynamicObject>>, mpsc::Receiver<ObjectRef<KubeDynamicObject>>) {
    mpsc::channel(TRIGGER_QUEUE)
}

/// What the manager starts for a bound binding: the janitor of every configured
/// kind, on the binding's inner cluster. The binary supplies it, since what a
/// janitor is belongs to the controllers, not to the shim. Every runner it
/// starts must stop when `shutdown` carries `true` or its sender is dropped,
/// which is how a binding whose Secret went away stops reconciling.
pub type StartRunners = Arc<dyn Fn(&ClusterRef, watch::Receiver<bool>) + Send + Sync>;

// Whether the manager considers a binding usable, and how it got there. This is
// the manager's own bookkeeping; what the shim answers requests with is the
// BindingStatus in ClusterClients.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RecordState {
    // No clients registered: the kubeconfig did not parse, or the inner cluster
    // did not answer. Requests are answered with Timeout.
    Unbound,
    // Clients registered and usable; the runners are up.
    Bound,
    // Clients registered but refused: requests are answered with Forbidden.
    Refused,
}

// What one attempt found. The attempt runs in its own task and touches no
// manager state; the loop applies the outcome to the record.
enum AttemptOutcome {
    // The binding is usable: these are its clients.
    Usable(RemoteClients),
    // The clients work but the binding may not be used: a claim held elsewhere,
    // or a denied verb. The clients stay registered so the claim can be
    // re-checked, and the shim answers the binding's requests with Forbidden.
    Refused(RemoteClients, String),
    // The inner cluster did not answer (or did not answer in time): retried with
    // backoff.
    Unreachable(String),
    // The kubeconfig itself is unusable -- it does not parse, or it is not one
    // we will build a client from. Nothing but a change of the Secret can
    // change that, so it is not retried on a timer.
    Unusable(String),
}

// An outcome as it comes back to the loop. `epoch` says which incarnation of
// the binding's record asked for it.
struct AttemptResult {
    binding: ClusterRef,
    epoch: u64,
    outcome: AttemptOutcome,
}

// What the manager remembers about one binding between events.
struct BindingRecord {
    // The kubeconfig the Secret currently holds; the clients are rebuilt from it.
    kubeconfig: String,
    state: RecordState,
    // Set when the registered clients no longer match `kubeconfig` (a rotated
    // credential) or when there are none.
    needs_clients: bool,
    // Stops the binding's runners; None while none are running.
    stop: Option<watch::Sender<bool>>,
    backoff: Backoff,
    // When the next attempt is due; None for a binding that only a change of its
    // Secret can move (an unparseable kubeconfig), and None while an attempt is
    // in flight, which is what the outcome sets again.
    due_at: Option<Instant>,
    // A refusal is logged once at warn, not at every re-check.
    refusal_logged: bool,
    // Whether an attempt for this binding is running. At most one is, so a
    // blackholed inner cluster occupies one task and nothing else.
    in_flight: bool,
    // Which incarnation of this record the attempts belong to. A Secret that
    // changes replaces the record with one of a new epoch, so the outcome of
    // the attempt that was running for the old credential is discarded rather
    // than applied to the new one.
    epoch: u64,
}

impl BindingRecord {
    fn new(kubeconfig: String, epoch: u64) -> BindingRecord {
        BindingRecord {
            kubeconfig,
            state: RecordState::Unbound,
            needs_clients: true,
            stop: None,
            backoff: Backoff::new(),
            due_at: Some(Instant::now()),
            refusal_logged: false,
            in_flight: false,
            epoch,
        }
    }

    // The overlap guard: `Some(epoch)` starts an attempt, `None` says one is
    // already running. The due time is cleared while it runs, so the ticker
    // does not queue a second one; the outcome sets the next due time.
    fn begin_attempt(&mut self) -> Option<u64> {
        if self.in_flight {
            return None;
        }
        self.in_flight = true;
        self.due_at = None;
        Some(self.epoch)
    }

    // Whether an outcome of `epoch` is this record's. An outcome of another
    // epoch is one of a credential that has since been replaced: it is dropped,
    // and the record it was for no longer exists.
    fn finish_attempt(&mut self, epoch: u64) -> bool {
        if self.epoch != epoch {
            return false;
        }
        self.in_flight = false;
        true
    }
}

/// The binding manager. `run` owns it for the life of the process.
pub struct BindingManager {
    clusters: ClusterClients,
    kinds: Vec<BindingKind>,
    verbs: Vec<String>,
    outer_cluster_id: String,
    request_timeout: Duration,
    start_runners: StartRunners,
    bindings: HashMap<ClusterRef, BindingRecord>,
    // Where the spawned attempts report back; set for the life of `run`.
    outcomes: Option<tokio::sync::mpsc::UnboundedSender<AttemptResult>>,
    // The epoch of the next record made.
    next_epoch: u64,
}

impl BindingManager {
    /// `kinds` are the configured kinds, `verbs` what the reconcilers do to them
    /// in an inner cluster, `outer_cluster_id` the owner the claim records, and
    /// `request_timeout` the bound on each of the manager's own requests, as on
    /// a reconciler's.
    pub fn new(
        clusters: ClusterClients,
        kinds: Vec<BindingKind>,
        verbs: Vec<String>,
        outer_cluster_id: String,
        request_timeout: Duration,
        start_runners: StartRunners,
    ) -> BindingManager {
        BindingManager {
            clusters,
            kinds,
            verbs,
            outer_cluster_id,
            request_timeout,
            start_runners,
            bindings: HashMap::new(),
            outcomes: None,
            next_epoch: 0,
        }
    }

    /// Watch the Secrets of every namespace until `shutdown` resolves, keeping
    /// the bindings of the process in step with them. Never returns an error for
    /// a single bad binding; the error is the watch itself ending.
    pub async fn run(mut self, shutdown: impl Future<Output = ()>) -> Result<()> {
        // Where the spawned attempts report back. The loop itself does no
        // request of an inner cluster: an attempt (the access check, the claim,
        // building the clients) is a round trip to a cluster that may be slow or
        // blackholed, and doing it inline would stall every other binding and
        // the Secret watch behind it.
        let (outcomes, mut outcomes_rx) = tokio::sync::mpsc::unbounded_channel();
        self.outcomes = Some(outcomes);
        let secrets = Api::<Secret>::all(self.clusters.primary.clone());
        // Only the Secrets of the Cluster API convention: the watch asks the
        // API server for the ones carrying the cluster-name label, so an
        // ordinary Secret of any namespace is never sent to this process, and
        // binding_of checks the type and the label's value on each event.
        let stream = watcher(secrets, watcher::Config::default().labels(CLUSTER_NAME_LABEL));
        futures::pin_mut!(stream);
        futures::pin_mut!(shutdown);
        let mut ticker = tokio::time::interval(TICK);
        ticker.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Delay);
        info!(
            "binding manager: watching Secrets of type {} labelled {} and named *{}, in every namespace",
            SECRET_TYPE, CLUSTER_NAME_LABEL, SECRET_SUFFIX
        );
        // Ok(()) only for the shutdown signal. The Secret watch ending is an
        // error, not a clean exit: the manager would go on running with the
        // bindings it happens to have, never noticing a Secret again, and
        // nothing about the process would say so.
        let result = loop {
            tokio::select! {
                _ = &mut shutdown => {
                    info!("binding manager: shutting down");
                    break Ok(());
                }
                _ = ticker.tick() => self.tick().await,
                Some(result) = outcomes_rx.recv() => self.apply(result).await,
                event = stream.next() => match event {
                    Some(Ok(event)) => self.on_event(event).await,
                    // The watcher recovers on its own; the next poll re-lists.
                    Some(Err(e)) => warn!("binding manager: watching Secrets failed: {}; retrying", e),
                    None => break Err(anyhow!(
                        "the Secret watch ended; no change of any binding would be noticed again"
                    )),
                },
            }
        };
        for binding in self.bindings.keys().cloned().collect::<Vec<_>>() {
            self.stop_runners(&binding);
        }
        result
    }

    async fn on_event(&mut self, event: watcher::Event<Secret>) {
        match event {
            watcher::Event::Applied(secret) => self.on_secret(&secret).await,
            watcher::Event::Deleted(secret) => {
                if let Some(binding) = binding_of(&secret) {
                    self.unbind(&binding, "its kubeconfig Secret was deleted").await;
                }
            }
            // A relist: bind what is there, drop what is not. Deletions missed
            // while the watch was down are exactly the bindings not listed.
            watcher::Event::Restarted(secrets) => {
                let listed: HashSet<ClusterRef> = secrets.iter().filter_map(binding_of).collect();
                let gone: Vec<ClusterRef> =
                    self.bindings.keys().filter(|b| !listed.contains(b)).cloned().collect();
                for binding in gone {
                    self.unbind(&binding, "its kubeconfig Secret is gone").await;
                }
                for secret in &secrets {
                    self.on_secret(secret).await;
                }
            }
        }
    }

    // A Secret that is one of ours: bind it, or rebind it if its kubeconfig
    // changed. A Secret without the `value` key is one we cannot use, and reads
    // like a missing one.
    async fn on_secret(&mut self, secret: &Secret) {
        let binding = match binding_of(secret) {
            Some(b) => b,
            None => return,
        };
        let kubeconfig = match kubeconfig_of(secret) {
            Some(k) => k,
            None => {
                warn!(
                    "binding {}: the Secret {}{} of namespace {} has no {:?} key; the binding is left unbound",
                    label(&binding), binding.name, SECRET_SUFFIX, binding.namespace, SECRET_KEY
                );
                self.unbind(&binding, "its kubeconfig Secret has no value key").await;
                return;
            }
        };
        // The same credential as before: a relist, or a Secret whose other keys
        // or labels were touched. A bound binding keeps running and an unbound
        // one is left to its pending retry; either way nothing is rebuilt, so a
        // relist does not restart every janitor of the process.
        if self.bindings.get(&binding).map(|record| record.kubeconfig == kubeconfig).unwrap_or(false) {
            return;
        }
        // A changed credential: the runners hold clients built from the old one,
        // so they are stopped and started again around the rebind.
        self.stop_runners(&binding);
        info!("binding {}: its kubeconfig Secret appeared or changed", label(&binding));
        let epoch = self.next_epoch;
        self.next_epoch += 1;
        self.bindings.insert(binding.clone(), BindingRecord::new(kubeconfig, epoch));
        self.start_attempt(&binding).await;
    }

    // Everything that has come due: a retry after an unreachable cluster, or the
    // periodic re-check of the access and the claim.
    async fn tick(&mut self) {
        let now = Instant::now();
        let due: Vec<ClusterRef> = self
            .bindings
            .iter()
            .filter(|(_, r)| r.due_at.map(|at| at <= now).unwrap_or(false))
            .map(|(b, _)| b.clone())
            .collect();
        for binding in due {
            self.start_attempt(&binding).await;
        }
    }

    // Start one attempt at making `binding` usable, in a task of its own. The
    // loop does not wait for it: an attempt talks to an inner cluster, which may
    // be slow or answer nothing at all, and every other binding and the Secret
    // watch would be behind it. At most one attempt per binding runs at a time
    // (BindingRecord::begin_attempt), so a cluster that never answers costs one
    // task, not one per tick.
    async fn start_attempt(&mut self, binding: &ClusterRef) {
        let (kubeconfig, needs_clients, epoch) = match self.bindings.get_mut(binding) {
            Some(record) => match record.begin_attempt() {
                Some(epoch) => (record.kubeconfig.clone(), record.needs_clients, epoch),
                None => {
                    debug!("binding {}: an attempt is already running; not starting another", label(binding));
                    return;
                }
            },
            None => return,
        };
        // The registered clients are reused unless the credential changed, so a
        // re-check does not rebuild them (and does not restart the runners).
        let registered = if needs_clients { None } else { self.clusters.remote_of(binding).await };
        let outcomes = match &self.outcomes {
            Some(outcomes) => outcomes.clone(),
            None => return,
        };
        let (kinds, verbs) = (self.kinds.clone(), self.verbs.clone());
        let owner = self.outer_cluster_id.clone();
        let request_timeout = self.request_timeout;
        let binding = binding.clone();
        tokio::spawn(async move {
            // A bound on the whole attempt, not only on each request of it: a
            // TCP connection to an address that blackholes packets is neither an
            // answer nor an error, and the record must not stay in flight
            // forever. A timeout reads as an unreachable cluster, which is
            // retried with backoff.
            let outcome = match tokio::time::timeout(
                ATTEMPT_TIMEOUT,
                attempt(&binding, &kubeconfig, registered, &kinds, &verbs, &owner, request_timeout),
            )
            .await
            {
                Ok(outcome) => outcome,
                Err(_) => AttemptOutcome::Unreachable(format!(
                    "its inner cluster did not finish answering within {:?}",
                    ATTEMPT_TIMEOUT
                )),
            };
            // The receiver lives as long as the manager loop; a send that fails
            // is a manager that is shutting down, and the outcome is moot.
            let _ = outcomes.send(AttemptResult { binding, epoch, outcome });
        });
    }

    // Apply what an attempt found. Everything that changes a binding's state
    // happens here, in the loop, so the state machine is still one thread of
    // control (the tests below are of its pieces).
    async fn apply(&mut self, result: AttemptResult) {
        let AttemptResult { binding, epoch, outcome } = result;
        let ours = match self.bindings.get_mut(&binding) {
            Some(record) => record.finish_attempt(epoch),
            None => false,
        };
        // The Secret changed, or went away, while the attempt ran: this outcome
        // is about a credential that is no longer the binding's.
        if !ours {
            debug!("binding {}: an outcome of a superseded credential is dropped", label(&binding));
            return;
        }
        match outcome {
            AttemptOutcome::Usable(clients) => self.bind(&binding, clients).await,
            AttemptOutcome::Refused(clients, why) => self.refuse(&binding, clients, why).await,
            AttemptOutcome::Unreachable(why) => self.retry(&binding, why).await,
            AttemptOutcome::Unusable(why) => {
                warn!(
                    "binding {}: {}; the binding is left unbound until the Secret changes",
                    label(&binding), why
                );
                self.deregister(&binding).await;
                if let Some(record) = self.bindings.get_mut(&binding) {
                    record.due_at = None;
                }
            }
        }
    }

    // The binding is usable: register its clients, start its runners if they are
    // not up, and come back at the re-check interval.
    async fn bind(&mut self, binding: &ClusterRef, clients: RemoteClients) {
        self.register(binding, clients.clone(), BindingStatus::Ready).await;
        let was = match self.bindings.get_mut(binding) {
            Some(record) => {
                let was = record.state;
                record.state = RecordState::Bound;
                record.needs_clients = false;
                record.refusal_logged = false;
                record.backoff.reset();
                record.due_at = Some(Instant::now() + RECHECK_INTERVAL);
                was
            }
            None => return,
        };
        if was != RecordState::Bound {
            info!("binding {}: bound; its claim is held by this controller", label(binding));
        }
        if self.bindings.get(binding).map(|r| r.stop.is_none()).unwrap_or(false) {
            self.start_runners(binding, &clients);
        }
    }

    // The binding is refused (a claim held elsewhere, or a denied verb): its
    // clients stay registered, so the claim can be re-checked, but the shim
    // answers its requests with Forbidden and no runner of ours touches the
    // cluster.
    async fn refuse(&mut self, binding: &ClusterRef, clients: RemoteClients, why: String) {
        self.stop_runners(binding);
        self.register(binding, clients, BindingStatus::Refused).await;
        let log = match self.bindings.get_mut(binding) {
            Some(record) => {
                record.state = RecordState::Refused;
                record.needs_clients = false;
                record.backoff.reset();
                record.due_at = Some(Instant::now() + RECHECK_INTERVAL);
                let log = !record.refusal_logged;
                record.refusal_logged = true;
                log
            }
            None => return,
        };
        if log {
            warn!(
                "binding {}: refused, {}. Its objects report Synced=False/Forbidden with Stalled=True and no janitor runs for it; it is re-checked every {:?}.",
                label(binding), why, RECHECK_INTERVAL
            );
        }
    }

    // The inner cluster did not answer: drop the clients, so requests read as
    // unreachable, and try again later.
    async fn retry(&mut self, binding: &ClusterRef, why: String) {
        self.deregister(binding).await;
        let delay = match self.bindings.get_mut(binding) {
            Some(record) => {
                let delay = record.backoff.next_delay();
                record.due_at = Some(Instant::now() + delay);
                delay
            }
            None => return,
        };
        warn!("binding {}: {}; retrying in {:?}", label(binding), why, delay);
    }

    // Drop everything the process holds for `binding` but keep its record, so a
    // retry can pick it up.
    async fn deregister(&mut self, binding: &ClusterRef) {
        self.stop_runners(binding);
        self.clusters.remove_remote(binding).await;
        if let Some(record) = self.bindings.get_mut(binding) {
            record.state = RecordState::Unbound;
            record.needs_clients = true;
            record.refusal_logged = false;
        }
    }

    // The binding is gone: forget it entirely.
    async fn unbind(&mut self, binding: &ClusterRef, why: &str) {
        if !self.bindings.contains_key(binding) && !self.clusters.has_remote(binding).await {
            return;
        }
        self.stop_runners(binding);
        self.clusters.remove_remote(binding).await;
        self.bindings.remove(binding);
        info!(
            "binding {}: unbound, {}. Its objects report Synced=False/InnerUnreachable.",
            label(binding), why
        );
    }

    async fn register(&self, binding: &ClusterRef, clients: RemoteClients, status: BindingStatus) {
        match self.clusters.replace_remote(binding, clients).await {
            // Already bound: the clients were swapped in place, the status is set
            // separately so that a rotated credential does not re-admit a refused
            // binding by itself.
            Ok(_previous) => {
                self.clusters.set_status(binding, status).await;
            }
            Err(clients) => {
                self.clusters.insert_remote(binding.clone(), clients, status).await;
            }
        }
    }

    // Start the binding's runners: the janitors (the binary's callback) and one
    // same-name watch per kind. They all stop together.
    fn start_runners(&mut self, binding: &ClusterRef, clients: &RemoteClients) {
        let (stop_tx, stop_rx) = watch::channel(false);
        (self.start_runners)(binding, stop_rx.clone());
        for kind in &self.kinds {
            spawn_same_name_watch(binding, kind, clients, stop_rx.clone());
        }
        if let Some(record) = self.bindings.get_mut(binding) {
            record.stop = Some(stop_tx);
        }
        info!("binding {}: its janitors and same-name watches are running", label(binding));
    }

    fn stop_runners(&mut self, binding: &ClusterRef) {
        if let Some(record) = self.bindings.get_mut(binding) {
            if let Some(stop) = record.stop.take() {
                let _ = stop.send(true);
                info!("binding {}: its janitors and same-name watches are stopping", label(binding));
            }
        }
    }
}

// The same-name trigger of one binding and kind: every change to a mirror in the
// inner cluster asks the kind's sync runner, which watches the outer cluster, to
// reconcile the object of the same namespace and name. A latency optimization
// only (doc/widget_sync_fanout_design.md, section 3.4).
fn spawn_same_name_watch(binding: &ClusterRef, kind: &BindingKind, clients: &RemoteClients, mut stop: watch::Receiver<bool>) {
    let api_resource = kind.entry.kube_api_resource().clone();
    let api = Api::<KubeDynamicObject>::all_with(clients.watch.clone(), &api_resource);
    let mut triggers = kind.triggers.clone();
    let name = label(binding);
    let kind_name = api_resource.kind.clone();
    tokio::spawn(async move {
        let stream = watcher(api, watcher::Config::default()).touched_objects();
        futures::pin_mut!(stream);
        loop {
            tokio::select! {
                _ = stop.changed() => break,
                item = stream.next() => match item {
                    None => break,
                    Some(Err(e)) => warn!("binding {}: watching {} mirrors failed: {}; retrying", name, kind_name, e),
                    Some(Ok(object)) => {
                        if let (Some(namespace), object_name) = (object.namespace(), object.name_any()) {
                            let reference = ObjectRef::<KubeDynamicObject>::new_with(&object_name, api_resource.clone())
                                .within(&namespace);
                            // The queue is bounded: a dropped trigger costs the
                            // latency the trigger saves, never correctness.
                            if triggers.try_send(reference).is_err() {
                                debug!("binding {}: dropped a same-name trigger for {}/{}", name, namespace, object_name);
                            }
                        }
                    }
                },
            }
        }
        info!("binding {}: the same-name watch of {} stopped", name, kind_name);
    });
}

// One attempt at making a binding usable, as it runs in its own task: build the
// clients if the credential changed, ask the inner cluster what this credential
// may do, and settle the claim. It has no access to the manager's state and
// changes nothing; what it found comes back as an AttemptOutcome.
async fn attempt(
    binding: &ClusterRef,
    kubeconfig: &str,
    registered: Option<RemoteClients>,
    kinds: &[BindingKind],
    verbs: &[String],
    owner: &str,
    request_timeout: Duration,
) -> AttemptOutcome {
    let clients = match registered {
        Some(clients) => clients,
        None => {
            // The kubeconfig is held to the Cluster API shape before a client is
            // built from it (validate_kubeconfig): a document that would run a
            // command in this pod, read a file of it, or send the credential
            // somewhere else is refused here, before kube ever acts on it.
            if let Err(reason) = checked_kubeconfig(kubeconfig) {
                return AttemptOutcome::Unusable(format!("its kubeconfig is refused, {}", reason));
            }
            match remote_clients_from_kubeconfig_yaml(kubeconfig, request_timeout).await {
                Ok(clients) => clients,
                Err(e) => return AttemptOutcome::Unusable(format!("its kubeconfig does not parse ({})", e)),
            }
        }
    };
    match check_binding_access(&clients.requests, binding, kinds, verbs).await {
        Err(e) => {
            return AttemptOutcome::Unreachable(format!("its inner cluster did not answer the access check: {}", e))
        }
        Ok(denied) if !denied.is_empty() => {
            return AttemptOutcome::Refused(clients, format!("its credential is denied {}", denied.join(", ")))
        }
        Ok(_) => {}
    }
    match check_claim(&clients.requests, binding, owner).await {
        Err(e) => AttemptOutcome::Unreachable(format!("its claim could not be settled: {}", e)),
        Ok(Some(holder)) => {
            AttemptOutcome::Refused(clients, format!("its inner cluster is claimed by {}", holder.holder()))
        }
        Ok(None) => AttemptOutcome::Usable(clients),
    }
}

/// check_binding_access asks the binding's inner cluster, with one
/// SelfSubjectAccessReview per verb and kind, whether the credential may do in
/// the binding's namespace what the reconcilers need, and whether it may settle
/// the claim in kube-system. It answers with the denials, which make the binding
/// refused; a request that fails is an unreachable cluster and is the Err
/// (doc/widget_sync_fanout_design.md, section 1.4).
/// The reviews are issued together, not one after another: there is one per verb
/// and kind and they are independent, so a sequence of them made the time to
/// bind a binding the sum of its round trips.
pub async fn check_binding_access(
    client: &Client,
    binding: &ClusterRef,
    kinds: &[BindingKind],
    verbs: &[String],
) -> std::result::Result<Vec<String>, kube::Error> {
    let mut checks = Vec::with_capacity(kinds.len() * verbs.len() + 2);
    for kind in kinds {
        for verb in verbs {
            checks.push(denial(
                client,
                &binding.namespace,
                &kind.group,
                &kind.plural,
                verb,
                None,
                format!("{} on {}", verb, kind.resource()),
            ));
        }
    }
    // The claim: `get` is asked for the claim by name, since rbac_inner.yaml
    // grants it through resourceNames and a nameless review would be denied;
    // `create` cannot be limited by name and is asked without one.
    checks.push(denial(
        client,
        CLAIM_NAMESPACE,
        "",
        "configmaps",
        "create",
        None,
        format!("create on configmaps in {}", CLAIM_NAMESPACE),
    ));
    checks.push(denial(
        client,
        CLAIM_NAMESPACE,
        "",
        "configmaps",
        "get",
        Some(CLAIM_NAME),
        format!("get on configmaps/{} in {}", CLAIM_NAME, CLAIM_NAMESPACE),
    ));
    // Any review that fails at all is an inner cluster that did not answer, and
    // the first such error ends the check: the binding is unreachable, not
    // denied.
    let answers = futures::future::try_join_all(checks).await?;
    Ok(answers.into_iter().flatten().collect())
}

// One review: `described` when it comes back denied, nothing when allowed.
async fn denial(
    client: &Client,
    namespace: &str,
    group: &str,
    resource: &str,
    verb: &str,
    name: Option<&str>,
    described: String,
) -> std::result::Result<Option<String>, kube::Error> {
    if allowed(client, namespace, group, resource, verb, name).await? {
        Ok(None)
    } else {
        Ok(Some(described))
    }
}

async fn allowed(client: &Client, namespace: &str, group: &str, resource: &str, verb: &str, name: Option<&str>) -> std::result::Result<bool, kube::Error> {
    let reviews: Api<SelfSubjectAccessReview> = Api::all(client.clone());
    let review = SelfSubjectAccessReview {
        spec: SelfSubjectAccessReviewSpec {
            resource_attributes: Some(ResourceAttributes {
                namespace: Some(namespace.to_string()),
                group: Some(group.to_string()),
                resource: Some(resource.to_string()),
                verb: Some(verb.to_string()),
                name: name.map(|n| n.to_string()),
                ..ResourceAttributes::default()
            }),
            ..SelfSubjectAccessReviewSpec::default()
        },
        ..SelfSubjectAccessReview::default()
    };
    let status = reviews.create(&PostParams::default(), &review).await?.status.unwrap_or_default();
    Ok(status.allowed)
}

/// check_claim creates the binding's claim in its inner cluster, or reads the
/// claim that is already there and compares it. `Ok(None)` is the binding's own
/// claim (a first contact, a restart, a re-created Secret); `Ok(Some(claim))` is
/// a cluster claimed by someone else, which the caller refuses
/// (doc/widget_sync_fanout_design.md, section 1.3).
pub async fn check_claim(
    client: &Client,
    binding: &ClusterRef,
    outer_cluster_id: &str,
) -> std::result::Result<Option<Claim>, kube::Error> {
    let claims: Api<ConfigMap> = Api::namespaced(client.clone(), CLAIM_NAMESPACE);
    let want = Claim::of(outer_cluster_id, binding);
    match claims.create(&PostParams::default(), &want.config_map()).await {
        Ok(_) => {
            info!("binding {}: claimed its inner cluster ({})", label(binding), want.holder());
            Ok(None)
        }
        Err(kube::Error::Api(ErrorResponse { reason, .. })) if reason == "AlreadyExists" => {
            let held = Claim::from_data(claims.get(CLAIM_NAME).await?.data.as_ref());
            if held == want {
                Ok(None)
            } else {
                Ok(Some(held))
            }
        }
        Err(e) => Err(e),
    }
}

/// outer_cluster_id is the uid of the outer cluster's kube-system namespace, the
/// de facto stable cluster identity, or the operator's override (a restore that
/// recreated the namespace, or a management cluster cloned with its uids).
pub async fn outer_cluster_id(client: &Client, override_id: Option<String>) -> Result<String> {
    if let Some(id) = override_id {
        info!("outer cluster id: {} (overridden)", id);
        return Ok(id);
    }
    let namespaces: Api<Namespace> = Api::all(client.clone());
    let id = namespaces
        .get(CLAIM_NAMESPACE)
        .await?
        .metadata
        .uid
        .ok_or_else(|| anyhow!("the outer namespace {} has no uid", CLAIM_NAMESPACE))?;
    info!("outer cluster id: {} (uid of the outer namespace {})", id, CLAIM_NAMESPACE);
    Ok(id)
}

// The binding a Secret names, if it names one: the Cluster API convention
// (binding_of_capi_secret), read off the object the watch delivered. The watch
// selects on the label, but a label selector cannot check the type or compare
// the label with the name, so both are checked here on every event.
fn binding_of(secret: &Secret) -> Option<ClusterRef> {
    binding_of_capi_secret(
        secret.namespace().as_deref().unwrap_or(""),
        &secret.name_any(),
        secret.type_.as_deref(),
        secret.labels().get(CLUSTER_NAME_LABEL).map(|s| s.as_str()),
    )
}

// The kubeconfig a Secret carries: the `value` key of its data (kube has already
// decoded the base64) or of its stringData.
fn kubeconfig_of(secret: &Secret) -> Option<String> {
    if let Some(bytes) = secret.data.as_ref().and_then(|d| d.get(SECRET_KEY)) {
        return String::from_utf8(bytes.0.clone()).ok();
    }
    secret.string_data.as_ref().and_then(|d| d.get(SECRET_KEY)).cloned()
}

// A binding as the logs name it.
fn label(binding: &ClusterRef) -> String {
    format!("{}/{}", binding.namespace, binding.name)
}

// The cluster a binding's requests and watches are tagged with.
pub fn cluster_id(binding: &ClusterRef) -> ClusterId {
    ClusterId::Remote(binding.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_secret_names_the_binding_of_its_namespace_and_name() {
        let binding = binding_of_secret("default", "a-kubeconfig").expect("a-kubeconfig is a binding");
        assert_eq!(binding.namespace, "default");
        assert_eq!(binding.name, "a");
        let binding = binding_of_secret("tenant", "inner-b-kubeconfig").expect("inner-b-kubeconfig is a binding");
        assert_eq!(binding.namespace, "tenant");
        assert_eq!(binding.name, "inner-b");
    }

    #[test]
    fn other_secrets_are_not_bindings() {
        // No suffix, the suffix inside the name, and the suffix alone, which
        // names no cluster.
        assert!(binding_of_secret("default", "a").is_none());
        assert!(binding_of_secret("default", "kubeconfig").is_none());
        assert!(binding_of_secret("default", "a-kubeconfig-backup").is_none());
        assert!(binding_of_secret("default", "-kubeconfig").is_none());
        assert!(binding_of_secret("", "a-kubeconfig").is_none());
        // The separators of a mirror's model kind, `<kind>@<namespace>/<name>`:
        // a binding whose parts held one would break the injectivity the
        // theorems' distinctness hypotheses are discharged with. No Kubernetes
        // name or namespace can hold them, so this can only be defensive.
        assert!(binding_of_secret("default", "a@b-kubeconfig").is_none());
        assert!(binding_of_secret("default", "a/b-kubeconfig").is_none());
        assert!(binding_of_secret("de@fault", "a-kubeconfig").is_none());
        assert!(binding_of_secret("de/fault", "a-kubeconfig").is_none());
    }

    // The whole Cluster API convention, not the name alone: an ordinary Secret
    // called `a-kubeconfig` (a backup, a user's own kubeconfig) is not a
    // binding, and neither is one whose label names another cluster than its
    // name does.
    #[test]
    fn only_a_cluster_api_secret_is_a_binding() {
        let capi = |name: &str, type_: Option<&str>, label: Option<&str>| {
            binding_of_capi_secret("default", name, type_, label)
        };
        let binding = capi("a-kubeconfig", Some(SECRET_TYPE), Some("a")).expect("the convention");
        assert_eq!((binding.namespace.as_str(), binding.name.as_str()), ("default", "a"));
        assert!(capi("a-kubeconfig", Some("Opaque"), Some("a")).is_none());
        assert!(capi("a-kubeconfig", None, Some("a")).is_none());
        assert!(capi("a-kubeconfig", Some(SECRET_TYPE), None).is_none());
        assert!(capi("a-kubeconfig", Some(SECRET_TYPE), Some("b")).is_none());
        assert!(capi("a-kubeconfig", Some(SECRET_TYPE), Some("")).is_none());
        assert!(capi("a", Some(SECRET_TYPE), Some("a")).is_none());
    }

    fn binding(namespace: &str, name: &str) -> ClusterRef {
        ClusterRef::new(namespace.to_string(), name.to_string())
    }

    #[test]
    fn a_claim_matches_only_the_binding_that_wrote_it() {
        let ours = Claim::of("outer-uid", &binding("default", "a"));
        assert_eq!(Claim::from_data(Some(&ours.data())), ours);
        // The same cluster reached from another namespace (a copied Secret),
        // under another name, or from another outer cluster.
        assert_ne!(Claim::of("outer-uid", &binding("tenant", "a")), ours);
        assert_ne!(Claim::of("outer-uid", &binding("default", "b")), ours);
        assert_ne!(Claim::of("other-uid", &binding("default", "a")), ours);
    }

    #[test]
    fn a_claim_missing_keys_matches_nothing() {
        let ours = Claim::of("outer-uid", &binding("default", "a"));
        let partial = BTreeMap::from([(CLAIM_OWNER_KEY.to_string(), "outer-uid".to_string())]);
        assert_ne!(Claim::from_data(Some(&partial)), ours);
        assert_ne!(Claim::from_data(None), ours);
        assert_eq!(Claim::from_data(None).owner, "");
    }

    #[test]
    fn the_claim_config_map_is_the_named_one_with_the_three_fields() {
        let claim = Claim::of("outer-uid", &binding("default", "a"));
        let config_map = claim.config_map();
        assert_eq!(config_map.metadata.name.as_deref(), Some(CLAIM_NAME));
        assert_eq!(config_map.metadata.namespace.as_deref(), Some(CLAIM_NAMESPACE));
        assert_eq!(Claim::from_data(config_map.data.as_ref()), claim);
    }

    // A Cluster API workload cluster's kubeconfig: a CA and a client key pair,
    // all as data. The rejections below are this document with one field added
    // or changed, so each test isolates the rule it is about.
    const CAPI_KUBECONFIG: &str = r#"
apiVersion: v1
kind: Config
clusters:
  - name: a
    cluster:
      server: https://10.0.0.2:6443
      certificate-authority-data: Q0EK
users:
  - name: a-admin
    user:
      client-certificate-data: Q1JUCg==
      client-key-data: S0VZCg==
contexts:
  - name: a-admin@a
    context:
      cluster: a
      user: a-admin
current-context: a-admin@a
"#;

    // The other accepted form: a CA and an inline bearer token, which is what
    // tools/two-cluster-test.sh writes for a service account.
    const TOKEN_KUBECONFIG: &str = r#"
apiVersion: v1
kind: Config
clusters:
  - name: a
    cluster:
      server: https://10.0.0.2:6443
      certificate-authority-data: Q0EK
users:
  - name: widget-sync-remote
    user:
      token: a-service-account-token
contexts:
  - name: a
    context:
      cluster: a
      user: widget-sync-remote
current-context: a
"#;

    fn rejection(yaml: &str) -> String {
        checked_kubeconfig(yaml).expect_err(&format!("should be refused:\n{}", yaml))
    }

    // The document as it is, with `patch` merged into it: `patch` is a YAML
    // mapping merged one level deep, so a test says only what it changes.
    fn with(yaml: &str, patch: &str) -> String {
        let mut base: serde_yaml::Value = serde_yaml::from_str(yaml).unwrap();
        let patch: serde_yaml::Value = serde_yaml::from_str(patch).unwrap();
        let (base_map, patch_map) = (base.as_mapping_mut().unwrap(), patch.as_mapping().unwrap());
        for (key, value) in patch_map {
            base_map.insert(key.clone(), value.clone());
        }
        serde_yaml::to_string(&base).unwrap()
    }

    #[test]
    fn a_cluster_api_kubeconfig_is_accepted() {
        assert_eq!(checked_kubeconfig(CAPI_KUBECONFIG), Ok(()));
        assert_eq!(checked_kubeconfig(TOKEN_KUBECONFIG), Ok(()));
        // An explicit `insecure-skip-tls-verify: false` disables nothing and is
        // the default; only `true` is a rejection.
        assert_eq!(
            checked_kubeconfig(&with(
                CAPI_KUBECONFIG,
                "clusters: [{name: a, cluster: {server: 'https://10.0.0.2:6443', certificate-authority-data: Q0EK, insecure-skip-tls-verify: false}}]"
            )),
            Ok(())
        );
    }

    // Every field kube-client acts on that turns a Secret into code or into a
    // read of this pod's filesystem.
    #[test]
    fn a_kubeconfig_that_runs_or_reads_anything_is_refused() {
        let user = |user: &str| {
            with(CAPI_KUBECONFIG, &format!("users: [{{name: a-admin, user: {}}}]", user))
        };
        assert!(rejection(&user("{exec: {apiVersion: client.authentication.k8s.io/v1, command: /bin/sh, args: [-c, 'cat /var/run/secrets/kubernetes.io/serviceaccount/token']}}"))
            .contains("exec"));
        assert!(rejection(&user("{auth-provider: {name: gcp, config: {cmd-path: /bin/sh}}}")).contains("auth-provider"));
        assert!(rejection(&user("{tokenFile: /var/run/secrets/kubernetes.io/serviceaccount/token}")).contains("tokenFile"));
        assert!(rejection(&user("{client-certificate: /etc/ssl/crt, client-key-data: S0VZCg==}")).contains("client-certificate"));
        assert!(rejection(&user("{client-certificate-data: Q1JUCg==, client-key: /etc/ssl/key}")).contains("client-key"));
    }

    #[test]
    fn a_kubeconfig_that_weakens_or_diverts_the_connection_is_refused() {
        let cluster = |cluster: &str| with(CAPI_KUBECONFIG, &format!("clusters: [{{name: a, cluster: {}}}]", cluster));
        let good = "server: 'https://10.0.0.2:6443', certificate-authority-data: Q0EK";
        assert!(rejection(&cluster(&format!("{{{}, insecure-skip-tls-verify: true}}", good))).contains("insecure-skip-tls-verify"));
        assert!(rejection(&cluster(&format!("{{{}, proxy-url: 'http://10.0.0.9:3128'}}", good))).contains("proxy-url"));
        assert!(rejection(&cluster("{server: 'https://10.0.0.2:6443', certificate-authority: /etc/ssl/ca.crt}")).contains("certificate-authority"));
        assert!(rejection(&cluster("{server: 'http://10.0.0.2:8080', certificate-authority-data: Q0EK}")).contains("not https"));
        assert!(rejection(&cluster("{certificate-authority-data: Q0EK}")).contains("no server"));
    }

    #[test]
    fn a_kubeconfig_of_more_than_one_cluster_user_or_context_is_refused() {
        let two_clusters = with(
            CAPI_KUBECONFIG,
            "clusters: [{name: a, cluster: {server: 'https://10.0.0.2:6443', certificate-authority-data: Q0EK}}, \
             {name: elsewhere, cluster: {server: 'https://10.0.0.9:6443', certificate-authority-data: Q0EK}}]",
        );
        assert!(rejection(&two_clusters).contains("2 clusters"));
        let two_users = with(
            CAPI_KUBECONFIG,
            "users: [{name: a-admin, user: {client-certificate-data: Q1JUCg==, client-key-data: S0VZCg==}}, \
             {name: other, user: {tokenFile: /var/run/secrets/kubernetes.io/serviceaccount/token}}]",
        );
        assert!(rejection(&two_users).contains("2 users"));
        let two_contexts = with(
            CAPI_KUBECONFIG,
            "contexts: [{name: a-admin@a, context: {cluster: a, user: a-admin}}, \
             {name: second, context: {cluster: a, user: a-admin}}]",
        );
        assert!(rejection(&two_contexts).contains("2 contexts"));
    }

    #[test]
    fn a_kubeconfig_whose_context_does_not_name_what_it_declares_is_refused() {
        let context = |context: &str| with(CAPI_KUBECONFIG, &format!("contexts: [{}]", context));
        assert!(rejection(&context("{name: a-admin@a, context: {cluster: elsewhere, user: a-admin}}")).contains("elsewhere"));
        assert!(rejection(&context("{name: a-admin@a, context: {cluster: a, user: someone}}")).contains("someone"));
        assert!(rejection(&with(CAPI_KUBECONFIG, "current-context: other")).contains("current-context"));
        let mut without: serde_yaml::Value = serde_yaml::from_str(CAPI_KUBECONFIG).unwrap();
        without.as_mapping_mut().unwrap().remove(serde_yaml::Value::String("current-context".to_string()));
        assert!(rejection(&serde_yaml::to_string(&without).unwrap()).contains("no current-context"));
    }

    #[test]
    fn a_value_that_is_not_a_kubeconfig_is_refused() {
        assert!(rejection("not: a kubeconfig").contains("exactly one is required"));
        assert!(rejection(": : :").contains("does not parse"));
    }

    // At most one attempt per binding is in flight, and an outcome is applied
    // only to the credential that asked for it.
    #[test]
    fn one_attempt_per_binding_at_a_time() {
        let mut record = BindingRecord::new("kubeconfig".to_string(), 7);
        assert!(record.due_at.is_some(), "a new record is due at once");
        assert_eq!(record.begin_attempt(), Some(7));
        // While it runs the record is not due again, so the ticker does not
        // queue a second attempt behind a cluster that is not answering.
        assert_eq!(record.due_at, None);
        assert_eq!(record.begin_attempt(), None);
        assert_eq!(record.begin_attempt(), None);
        // The outcome of that attempt is this record's; another epoch's is a
        // credential that has since been replaced.
        assert!(!record.finish_attempt(6));
        assert!(record.in_flight, "a stale outcome does not end the attempt in flight");
        assert!(record.finish_attempt(7));
        assert!(!record.in_flight);
        // And then the next attempt may start.
        assert_eq!(record.begin_attempt(), Some(7));
    }

    #[test]
    fn the_backoff_doubles_from_a_second_to_a_minute_and_resets() {
        let mut backoff = Backoff::new();
        assert_eq!(backoff.next_delay(), Duration::from_secs(1));
        assert_eq!(backoff.next_delay(), Duration::from_secs(2));
        assert_eq!(backoff.next_delay(), Duration::from_secs(4));
        for _ in 0..10 {
            backoff.next_delay();
        }
        assert_eq!(backoff.next_delay(), BACKOFF_MAX);
        backoff.reset();
        assert_eq!(backoff.next_delay(), BACKOFF_START);
    }
}
