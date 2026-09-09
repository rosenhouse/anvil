// The model kind of a runtime kind in a cluster (doc/widget_sync_fanout_design.md,
// section 2.4). The registry (exec::registry) ties a discovered kind and the
// cluster an object lives in to one model kind; this is the function it is
// trusted to compute, and its injectivity, which is what the distinctness
// hypotheses of the theorems are discharged with for a concrete configuration.
use crate::kubernetes_api_objects::spec::{api_resource::*, common::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub open spec fn at_sign() -> StringView { "@"@ }

pub open spec fn slash() -> StringView { "/"@ }

// The model kind of the kind named `kind_name` (the CRD name, `<plural>.<group>`)
// in `cluster`.
pub open spec fn model_kind(kind_name: StringView, cluster: ClusterIdView) -> Kind {
    match cluster {
        ClusterIdView::Primary => Kind::CustomResourceKind(kind_name),
        ClusterIdView::Remote(r) => Kind::CustomResourceKind(remote_kind_name(kind_name, r)),
    }
}

pub open spec fn remote_kind_name(kind_name: StringView, r: ClusterRefView) -> StringView {
    kind_name + at_sign() + r.namespace + slash() + r.name
}

pub open spec fn free_of(s: StringView, c: char) -> bool {
    forall |i: int| 0 <= i < s.len() ==> s[i] != c
}

// The hypothesis under which model_kind is injective: the kind name and the
// binding's names contain no '@', and the namespace no '/'. DNS names satisfy it.
pub open spec fn kind_name_ok(kind_name: StringView) -> bool {
    free_of(kind_name, '@')
}

pub open spec fn cluster_ref_ok(r: ClusterRefView) -> bool {
    &&& free_of(r.namespace, '@')
    &&& free_of(r.namespace, '/')
    &&& free_of(r.name, '@')
}

pub open spec fn cluster_id_ok(cluster: ClusterIdView) -> bool {
    match cluster {
        ClusterIdView::Primary => true,
        ClusterIdView::Remote(r) => cluster_ref_ok(r),
    }
}

// a1 + [c] + b1 == a2 + [c] + b2 with a1 and a2 free of c gives a1 == a2 and
// b1 == b2: the first c of each side is at a1.len() and a2.len().
pub proof fn lemma_split_at_separator(a1: StringView, a2: StringView, b1: StringView, b2: StringView, c: char)
    requires
        free_of(a1, c),
        free_of(a2, c),
        a1 + seq![c] + b1 == a2 + seq![c] + b2,
    ensures
        a1 == a2,
        b1 == b2,
{
    let lhs = a1 + seq![c] + b1;
    let rhs = a2 + seq![c] + b2;
    if a1.len() < a2.len() {
        assert(lhs[a1.len() as int] == c);
        assert(rhs[a1.len() as int] == a2[a1.len() as int]);
        assert(false);
    } else if a1.len() > a2.len() {
        assert(rhs[a2.len() as int] == c);
        assert(lhs[a2.len() as int] == a1[a2.len() as int]);
        assert(false);
    }
    assert(a1.len() == a2.len());
    assert forall |i: int| 0 <= i < a1.len() implies a1[i] == a2[i] by {
        assert(lhs[i] == a1[i]);
        assert(rhs[i] == a2[i]);
    }
    assert(a1 =~= a2);
    assert(lhs.len() == rhs.len());
    assert(b1.len() == b2.len());
    assert forall |i: int| 0 <= i < b1.len() implies b1[i] == b2[i] by {
        assert(lhs[a1.len() + 1 + i] == b1[i]);
        assert(rhs[a2.len() + 1 + i] == b2[i]);
    }
    assert(b1 =~= b2);
}

// A string free of c is not a1 + [c] + b1.
pub proof fn lemma_free_of_is_not_split(s: StringView, a: StringView, b: StringView, c: char)
    requires free_of(s, c),
    ensures s != a + seq![c] + b,
{
    if s == a + seq![c] + b {
        assert(s[a.len() as int] == c);
    }
}

pub proof fn lemma_at_sign_is_seq()
    ensures at_sign() == seq!['@'],
{
    reveal_strlit("@");
    assert(at_sign() =~= seq!['@']);
}

pub proof fn lemma_slash_is_seq()
    ensures slash() == seq!['/'],
{
    reveal_strlit("/");
    assert(slash() =~= seq!['/']);
}

// A remote kind name is a kind name and a ClusterRef, uniquely.
pub proof fn lemma_remote_kind_name_injective(k1: StringView, r1: ClusterRefView, k2: StringView, r2: ClusterRefView)
    requires
        kind_name_ok(k1),
        kind_name_ok(k2),
        cluster_ref_ok(r1),
        cluster_ref_ok(r2),
        remote_kind_name(k1, r1) == remote_kind_name(k2, r2),
    ensures
        k1 == k2,
        r1 == r2,
{
    lemma_at_sign_is_seq();
    lemma_slash_is_seq();
    let tail1 = r1.namespace + slash() + r1.name;
    let tail2 = r2.namespace + slash() + r2.name;
    assert(remote_kind_name(k1, r1) == k1 + seq!['@'] + tail1) by {
        assert(k1 + at_sign() + r1.namespace + slash() + r1.name =~= k1 + seq!['@'] + tail1);
    }
    assert(remote_kind_name(k2, r2) == k2 + seq!['@'] + tail2) by {
        assert(k2 + at_sign() + r2.namespace + slash() + r2.name =~= k2 + seq!['@'] + tail2);
    }
    lemma_split_at_separator(k1, k2, tail1, tail2, '@');
    lemma_split_at_separator(r1.namespace, r2.namespace, r1.name, r2.name, '/');
}

// A remote kind name is never a primary one.
pub proof fn lemma_remote_kind_name_is_not_primary(k1: StringView, k2: StringView, r: ClusterRefView)
    requires
        kind_name_ok(k1),
    ensures
        k1 != remote_kind_name(k2, r),
{
    lemma_at_sign_is_seq();
    let tail = r.namespace + slash() + r.name;
    assert(remote_kind_name(k2, r) == k2 + seq!['@'] + tail) by {
        assert(k2 + at_sign() + r.namespace + slash() + r.name =~= k2 + seq!['@'] + tail);
    }
    lemma_free_of_is_not_split(k1, k2, tail, '@');
}

// Two kinds with different names have no mirror kind in common, whatever the
// clusters. Unlike lemma_remote_kind_name_injective this asks nothing of the
// ClusterRefs: the '@' of the first name already splits both sides, so the kind
// names must agree. It is what tells the mirror kinds of two configured kinds
// apart, where the bindings are whatever an object's selector named.
pub proof fn lemma_remote_kind_names_of_distinct_kinds(k1: StringView, k2: StringView, r1: ClusterRefView, r2: ClusterRefView)
    requires
        kind_name_ok(k1),
        kind_name_ok(k2),
        k1 != k2,
    ensures
        remote_kind_name(k1, r1) != remote_kind_name(k2, r2),
{
    lemma_at_sign_is_seq();
    let tail1 = r1.namespace + slash() + r1.name;
    let tail2 = r2.namespace + slash() + r2.name;
    assert(remote_kind_name(k1, r1) == k1 + seq!['@'] + tail1) by {
        assert(k1 + at_sign() + r1.namespace + slash() + r1.name =~= k1 + seq!['@'] + tail1);
    }
    assert(remote_kind_name(k2, r2) == k2 + seq!['@'] + tail2) by {
        assert(k2 + at_sign() + r2.namespace + slash() + r2.name =~= k2 + seq!['@'] + tail2);
    }
    if remote_kind_name(k1, r1) == remote_kind_name(k2, r2) {
        lemma_split_at_separator(k1, k2, tail1, tail2, '@');
    }
}

// model_kind is injective on well-formed inputs: two equal model kinds come from
// the same kind name in the same cluster.
pub proof fn lemma_model_kind_injective(k1: StringView, c1: ClusterIdView, k2: StringView, c2: ClusterIdView)
    requires
        kind_name_ok(k1),
        kind_name_ok(k2),
        cluster_id_ok(c1),
        cluster_id_ok(c2),
        model_kind(k1, c1) == model_kind(k2, c2),
    ensures
        k1 == k2,
        c1 == c2,
{
    match (c1, c2) {
        (ClusterIdView::Primary, ClusterIdView::Primary) => {}
        (ClusterIdView::Primary, ClusterIdView::Remote(r2)) => {
            lemma_remote_kind_name_is_not_primary(k1, k2, r2);
        }
        (ClusterIdView::Remote(r1), ClusterIdView::Primary) => {
            lemma_remote_kind_name_is_not_primary(k2, k1, r1);
        }
        (ClusterIdView::Remote(r1), ClusterIdView::Remote(r2)) => {
            lemma_remote_kind_name_injective(k1, r1, k2, r2);
        }
    }
}

// The model kinds of one kind in two different clusters are distinct, and so are
// those of two kinds in one cluster; the form the distinctness hypotheses of the
// theorems take.
pub proof fn lemma_model_kind_distinct(k1: StringView, c1: ClusterIdView, k2: StringView, c2: ClusterIdView)
    requires
        kind_name_ok(k1),
        kind_name_ok(k2),
        cluster_id_ok(c1),
        cluster_id_ok(c2),
        k1 != k2 || c1 != c2,
    ensures
        model_kind(k1, c1) != model_kind(k2, c2),
{
    if model_kind(k1, c1) == model_kind(k2, c2) {
        lemma_model_kind_injective(k1, c1, k2, c2);
    }
}

// The cluster a model kind names: the inverse of model_kind on the names and
// clusters it is injective on. Every other kind, built in or not of the shape,
// is read as the primary cluster's. This is the routing of the registry
// (doc/widget_sync_fanout_design.md, section 2.4) as a function of the kind.
pub open spec fn cluster_of_kind(kind: Kind) -> ClusterIdView {
    if exists |name: StringView, r: ClusterRefView| kind_name_ok(name) && cluster_ref_ok(r) && kind == #[trigger] model_kind(name, ClusterIdView::Remote(r)) {
        let (name, r) = choose |name: StringView, r: ClusterRefView| kind_name_ok(name) && cluster_ref_ok(r) && kind == #[trigger] model_kind(name, ClusterIdView::Remote(r));
        ClusterIdView::Remote(r)
    } else {
        ClusterIdView::Primary
    }
}

pub proof fn lemma_cluster_of_model_kind(name: StringView, cluster: ClusterIdView)
    requires
        kind_name_ok(name),
        cluster_id_ok(cluster),
    ensures cluster_of_kind(model_kind(name, cluster)) == cluster,
{
    let kind = model_kind(name, cluster);
    match cluster {
        ClusterIdView::Primary => {
            if exists |n2: StringView, r2: ClusterRefView| kind_name_ok(n2) && cluster_ref_ok(r2) && kind == #[trigger] model_kind(n2, ClusterIdView::Remote(r2)) {
                let (n2, r2) = choose |n2: StringView, r2: ClusterRefView| kind_name_ok(n2) && cluster_ref_ok(r2) && kind == #[trigger] model_kind(n2, ClusterIdView::Remote(r2));
                lemma_remote_kind_name_is_not_primary(name, n2, r2);
            }
        },
        ClusterIdView::Remote(r) => {
            assert(kind == model_kind(name, ClusterIdView::Remote(r)));
            let (n2, r2) = choose |n2: StringView, r2: ClusterRefView| kind_name_ok(n2) && cluster_ref_ok(r2) && kind == #[trigger] model_kind(n2, ClusterIdView::Remote(r2));
            lemma_remote_kind_name_injective(name, r, n2, r2);
        },
    }
}

}
