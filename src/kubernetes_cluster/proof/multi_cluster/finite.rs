// Sums and ranks over a set. The refinement adds the counters of the
// stores across the sides, and numbers the sides to keep the values a counter
// never allocates apart from one another.
#![allow(unused_imports)]
use vstd::prelude::*;

verus! {

broadcast use vstd::set::group_set_lemmas;

// The sum of f over a set, taking the elements out one at a time.
#[verifier::opaque]
pub open spec fn set_sum<A>(s: Set<A>, f: spec_fn(A) -> int) -> int
    decreases s.len(),
{
    if s.len() > 0 {
        let x = s.choose();
        f(x) + set_sum(s.remove(x), f)
    } else {
        0
    }
}

pub proof fn lemma_set_sum_remove<A>(s: Set<A>, f: spec_fn(A) -> int, x: A)
    requires
        s.contains(x),
    ensures set_sum(s, f) == f(x) + set_sum(s.remove(x), f),
    decreases s.len(),
{
    reveal(set_sum);
    let y = s.choose();
    if y != x {
        let s1 = s.remove(y);
        lemma_set_sum_remove(s1, f, x);
        let s2 = s.remove(x);
        lemma_set_sum_remove(s2, f, y);
        assert(s1.remove(x) =~= s2.remove(y));
    }
}

pub proof fn lemma_set_sum_pointwise_le<A>(s: Set<A>, f: spec_fn(A) -> int, g: spec_fn(A) -> int)
    requires
        forall |x: A| #[trigger] s.contains(x) ==> f(x) <= g(x),
    ensures set_sum(s, f) <= set_sum(s, g),
    decreases s.len(),
{
    reveal(set_sum);
    if s.len() > 0 {
        let x = s.choose();
        lemma_set_sum_pointwise_le(s.remove(x), f, g);
    }
}

pub proof fn lemma_set_sum_pointwise_eq<A>(s: Set<A>, f: spec_fn(A) -> int, g: spec_fn(A) -> int)
    requires
        forall |x: A| #[trigger] s.contains(x) ==> f(x) == g(x),
    ensures set_sum(s, f) == set_sum(s, g),
{
    lemma_set_sum_pointwise_le(s, f, g);
    lemma_set_sum_pointwise_le(s, g, f);
}

// Two functions that agree everywhere but at x: the sums differ by the difference at x.
pub proof fn lemma_set_sum_diff_at<A>(s: Set<A>, f: spec_fn(A) -> int, g: spec_fn(A) -> int, x: A)
    requires
        s.contains(x),
        forall |y: A| #[trigger] s.contains(y) && y != x ==> f(y) == g(y),
    ensures set_sum(s, g) - set_sum(s, f) == g(x) - f(x),
{
    lemma_set_sum_remove(s, f, x);
    lemma_set_sum_remove(s, g, x);
    lemma_set_sum_pointwise_eq(s.remove(x), f, g);
}

pub proof fn lemma_set_sum_zero<A>(s: Set<A>)
    ensures set_sum(s, |x: A| 0) == 0,
    decreases s.len(),
{
    reveal(set_sum);
    if s.len() > 0 {
        lemma_set_sum_zero(s.remove(s.choose()));
    }
}

pub proof fn lemma_set_sum_nonneg<A>(s: Set<A>, f: spec_fn(A) -> int)
    requires
        forall |x: A| #[trigger] s.contains(x) ==> f(x) >= 0,
    ensures set_sum(s, f) >= 0,
    decreases s.len(),
{
    reveal(set_sum);
    if s.len() > 0 {
        let x = s.choose();
        lemma_set_sum_nonneg(s.remove(x), f);
    }
}

// The position of x in the order set_sum takes the elements of s out.
#[verifier::opaque]
pub open spec fn rank<A>(s: Set<A>, x: A) -> int
    decreases s.len(),
{
    if s.len() > 0 {
        let y = s.choose();
        if y == x { 0 } else { 1 + rank(s.remove(y), x) }
    } else {
        0
    }
}

pub proof fn lemma_rank_bounds<A>(s: Set<A>, x: A)
    requires
        s.contains(x),
    ensures 0 <= rank(s, x) < s.len(),
    decreases s.len(),
{
    reveal(rank);
    let y = s.choose();
    if y != x {
        lemma_rank_bounds(s.remove(y), x);
    }
}

pub proof fn lemma_rank_injective<A>(s: Set<A>, x: A, z: A)
    requires
        s.contains(x),
        s.contains(z),
        rank(s, x) == rank(s, z),
    ensures x == z,
    decreases s.len(),
{
    reveal(rank);
    let y = s.choose();
    if y == x {
        if y != z { lemma_rank_bounds(s.remove(y), z); }
    } else if y == z {
        lemma_rank_bounds(s.remove(y), x);
    } else {
        lemma_rank_injective(s.remove(y), x, z);
    }
}

}
