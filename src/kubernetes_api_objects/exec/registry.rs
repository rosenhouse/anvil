// The registry (doc/widget_sync_fanout_design.md, section 2.4): the configured
// kinds of a process, each with its CRD name (`<plural>.<group>`) and the
// ApiResource discovered for it at boot. It is the one place that ties a
// runtime kind and a cluster to a model kind, spec::model_kind::model_kind;
// api_resource() is trusted to do that, as the typed wrappers' api_resource()
// is trusted to name their view kind.
use crate::kubernetes_api_objects::exec::{api_resource::*, resource::*};
use crate::kubernetes_api_objects::spec::model_kind::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// One configured kind. Its view is the kind name model_kind is applied to.
#[verifier(external_body)]
pub struct RegistryEntry {
    crd_name: String,
    api_resource: kube::api::ApiResource,
}

implement_view_trait!(RegistryEntry, StringView);
implement_deep_view_trait!(RegistryEntry, StringView);

impl std::clone::Clone for RegistryEntry {
    #[verifier(external_body)]
    fn clone(&self) -> (res: RegistryEntry)
        ensures res@ == self@,
    {
        RegistryEntry { crd_name: self.crd_name.clone(), api_resource: self.api_resource.clone() }
    }
}

impl RegistryEntry {
    // The CRD name of the kind, the `k` of model_kind(k, cluster).
    #[verifier(external_body)]
    pub fn crd_name(&self) -> (name: String)
        ensures name@ == self@,
    {
        self.crd_name.clone()
    }

    // The ApiResource of this kind in `cluster`: the discovered resource, tagged
    // with the cluster. Trusted: its view kind is the model kind of the entry in
    // that cluster, which is what routes the request to the cluster's client and
    // names the object's kind in the model.
    #[verifier(external_body)]
    pub fn api_resource(&self, cluster: &ClusterId) -> (res: ApiResource)
        ensures res@.kind == model_kind(self@, cluster@),
    {
        ApiResource::from_kube_in(self.api_resource.clone(), cluster.clone())
    }
}

#[verifier(external)]
impl RegistryEntry {
    // new records a discovered kind. The CRD name is `<plural>.<group>`, or the
    // plural alone for the core group.
    pub fn new(api_resource: kube::api::ApiResource) -> RegistryEntry {
        let crd_name = if api_resource.group.is_empty() {
            api_resource.plural.clone()
        } else {
            format!("{}.{}", api_resource.plural, api_resource.group)
        };
        RegistryEntry { crd_name, api_resource }
    }

    // kube_api_resource is for the shim, which builds the kube-runtime
    // controllers and the API handles from it; not for controller code.
    pub fn kube_api_resource(&self) -> &kube::api::ApiResource {
        &self.api_resource
    }
}

#[verifier(external)]
impl std::fmt::Debug for RegistryEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} ({})", self.crd_name, self.api_resource.api_version)
    }
}

// The configured kinds, in configuration order. Its view is the sequence of
// their kind names.
pub struct Registry {
    pub entries: Vec<RegistryEntry>,
}

impl View for Registry {
    type V = Seq<StringView>;

    open spec fn view(&self) -> Seq<StringView> {
        self.entries@.map_values(|e: RegistryEntry| e@)
    }
}

impl Registry {
    pub fn new() -> (r: Registry)
        ensures r@ == Seq::<StringView>::empty(),
    {
        let r = Registry { entries: Vec::new() };
        proof {
            assert(r@ =~= Seq::<StringView>::empty());
        }
        r
    }

    pub fn push(&mut self, entry: RegistryEntry)
        ensures final(self)@ == old(self)@.push(entry@),
    {
        self.entries.push(entry);
        proof {
            assert(final(self)@ =~= old(self)@.push(entry@));
        }
    }

    pub fn len(&self) -> (n: usize)
        ensures n == self@.len(),
    {
        self.entries.len()
    }

    pub fn entry(&self, kind_index: usize) -> (entry: &RegistryEntry)
        requires kind_index < self@.len(),
        ensures entry@ == self@[kind_index as int],
    {
        &self.entries[kind_index]
    }

    pub fn api_resource(&self, kind_index: usize, cluster: &ClusterId) -> (res: ApiResource)
        requires kind_index < self@.len(),
        ensures res@.kind == model_kind(self@[kind_index as int], cluster@),
    {
        self.entries[kind_index].api_resource(cluster)
    }
}

}
