use crate::grammar::{
    Crate, Fallible, NegTraitImpl, Predicate, TraitImpl, TraitRef, Wc, Wcs, WhereClause,
};
use crate::prove::{Env, Program};
use anyhow::bail;
use std::fmt::Debug;

use super::{prove_goal, prove_not_goal};
use formality_core::{judgment::ProofTree, judgment_fn};

judgment_fn! {
    /// Runs coherence checking (orphan, overlap, duplicates) for the current crate.
    /// Returns ProvenSet<()> caller.
    pub(crate) fn check_coherence(program: Program, current_crate: Crate) => () {
        debug(program, current_crate)

        (
            (let current_crate_impls = program.trait_impls_in_crate(&current_crate))
            (let all_crate_impls = program.trait_impls())
            (let current_crate_neg_impls = program.neg_trait_impls_in_crate(&current_crate))
            (let all_crate_neg_impls = program.neg_trait_impls())

            (for_all(impl_a in current_crate_impls)
                (for_all(impl_b in all_crate_impls)
                    (overlap_check_impl(program, impl_a, impl_b) => ())))

            (for_all(impl_a in current_crate_impls)
                (for_all(neg_impl_b in all_crate_neg_impls)
                    (overlap_check_impl_neg(program, impl_a, neg_impl_b) => ())))

            (for_all(neg_impl_a in current_crate_neg_impls)
                (for_all(impl_b in all_crate_impls)
                    (overlap_check_impl_neg(program, impl_b, neg_impl_a) => ())))

            (for_all(neg_impl_a in current_crate_neg_impls)
                (for_all(neg_impl_b in all_crate_neg_impls)
                    (overlap_check_neg_neg(program, neg_impl_a, neg_impl_b) => ())))

            (for_all(trait_impl in current_crate_impls)
                (orphan_check(program, trait_impl) => ()))
            (for_all(neg_trait_impl in current_crate_neg_impls)
                (orphan_check_neg(program, neg_trait_impl) => ()))
            --- ("check_coherence")
            (check_coherence(program, current_crate) => ())
        )
    }
}

// Orphan rule (RFC 2451): prove the trait ref is local under the impl's where-clauses.
judgment_fn! {
    fn orphan_check(program: Program, impl_a: TraitImpl) => () {
        debug(program, impl_a)

        (
            (let (env, a) = Env::default().instantiate_universally(&impl_a.binder))
            (let trait_ref = a.trait_ref())
            (prove_goal(program, env, &a.where_clauses, Predicate::is_local(trait_ref)) => ())
            --- ("orphan_check")
            (orphan_check(program, impl_a) => ())
        )
    }
}

judgment_fn! {
    fn orphan_check_neg(program: Program, impl_a: NegTraitImpl) => () {
        debug(program, impl_a)

        // The orphan check passes if
        // ∀P. ⌐ (coherence_mode => (wf(Ts) && cannot_be_proven(is_local_trait_ref)))
        //
        // TODO: feels like we do want a general "not goal", flipping existentials
        // and universals and the coherence mode
        // self.prove_not_goal(&env, &(Wcs::wf)) // ??
        (
            (let (env, a) = Env::default().instantiate_universally(&impl_a.binder))
            (let trait_ref = a.trait_ref())
            (prove_goal(program, env, &a.where_clauses, Predicate::is_local(trait_ref)) => ())
            --- ("orphan_check_neg")
            (orphan_check_neg(program, impl_a) => ())
        )
    }
}

/// Two impls of the same trait prove they do not overlap or report impls may overlap.
/// Same impl or different trait -> trivial proof .
#[tracing::instrument(level = "Debug", skip(program, impl_a, impl_b))]
fn overlap_check_impl(
    program: &Program,
    impl_a: &TraitImpl,
    impl_b: &TraitImpl,
) -> Fallible<ProofTree> {
    // An impl cannot overlap with itself.
    if impl_a == impl_b {
        return Ok(ProofTree::new(
            "overlap_check",
            Some("skip_same_impl"),
            vec![],
        ));
    }

    // Impls of two distinct traits cannot overlap.
    if impl_a.trait_id() != impl_b.trait_id() {
        return Ok(ProofTree::new(
            "overlap_check",
            Some("skip_different_trait"),
            vec![],
        ));
    }

    // Example:
    //
    // Given two impls...
    //
    //   impl<P_a..> SomeTrait<T_a...> for T_a0 where Wc_a { }
    //   impl<P_b..> SomeTrait<T_b...> for T_b0 where Wc_b { }
    //
    // We want to prove that ∀P_a, ∀P_b ...
    let (env, a) = Env::default().instantiate_universally(&impl_a.binder);
    let (env, b) = env.instantiate_universally(&impl_b.binder);

    let trait_ref_a = a.trait_ref();
    let trait_ref_b = b.trait_ref();

    overlap_check_headers(
        program,
        &env,
        &trait_ref_a,
        &a.where_clauses,
        &trait_ref_b,
        &b.where_clauses,
        impl_a,
        impl_b,
    )
}

#[tracing::instrument(level = "Debug", skip(program, impl_a, impl_b))]
fn overlap_check_impl_neg(
    program: &Program,
    impl_a: &TraitImpl,
    impl_b: &NegTraitImpl,
) -> Fallible<ProofTree> {
    if impl_a.trait_id() != &impl_b.binder.peek().trait_id {
        return Ok(ProofTree::new(
            "overlap_check",
            Some("skip_different_trait"),
            vec![],
        ));
    }

    let (env, a) = Env::default().instantiate_universally(&impl_a.binder);
    let (env, b) = env.instantiate_universally(&impl_b.binder);

    let trait_ref_a = a.trait_ref();
    let trait_ref_b = b.trait_ref();

    overlap_check_headers(
        program,
        &env,
        &trait_ref_a,
        &a.where_clauses,
        &trait_ref_b,
        &b.where_clauses,
        impl_a,
        impl_b,
    )
}

#[tracing::instrument(level = "Debug", skip(program, impl_a, impl_b))]
fn overlap_check_neg_neg(
    program: &Program,
    impl_a: &NegTraitImpl,
    impl_b: &NegTraitImpl,
) -> Fallible<ProofTree> {
    if impl_a == impl_b {
        return Ok(ProofTree::new(
            "overlap_check",
            Some("skip_same_impl"),
            vec![],
        ));
    }

    if impl_a.binder.peek().trait_id != impl_b.binder.peek().trait_id {
        return Ok(ProofTree::new(
            "overlap_check",
            Some("skip_different_trait"),
            vec![],
        ));
    }

    let (env, a) = Env::default().instantiate_universally(&impl_a.binder);
    let (env, b) = env.instantiate_universally(&impl_b.binder);

    let trait_ref_a = a.trait_ref();
    let trait_ref_b = b.trait_ref();

    overlap_check_headers(
        program,
        &env,
        &trait_ref_a,
        &a.where_clauses,
        &trait_ref_b,
        &b.where_clauses,
        impl_a,
        impl_b,
    )
}

#[allow(clippy::too_many_arguments)]
fn overlap_check_headers(
    program: &Program,
    env: &Env,
    trait_ref_a: &TraitRef,
    where_clauses_a: &[WhereClause],
    trait_ref_b: &TraitRef,
    where_clauses_b: &[WhereClause],
    impl_a: &dyn Debug,
    impl_b: &dyn Debug,
) -> Fallible<ProofTree> {
    assert_eq!(trait_ref_a.trait_id, trait_ref_b.trait_id);

    // ... ¬(coherence_mode => (Ts_a = Ts_b ∧ Wc_a ∧ Wc_b))
    //
    // i.e., there is no overlap if, in coherence mode, if we can prove that either
    // * the parameters cannot be equated ¬(Ts_a = Ts_b)
    // * or the where-clauses don't hold (¬Wc_a || ¬Wc_b).
    //
    // TODO: feels like we do want a general "not goal", flipping existentials
    // and universals and the coherence mode.
    // self.prove_not_goal(&env, &(Wcs::wf))
    if let Ok(proof_tree) = prove_not_goal(
        program,
        env,
        (),
        (
            Wcs::all_eq(&trait_ref_a.parameters, &trait_ref_b.parameters),
            where_clauses_a,
            where_clauses_b,
        ),
    ) {
        tracing::debug!(
            "proved not {:?}",
            (
                Wcs::all_eq(&trait_ref_a.parameters, &trait_ref_b.parameters),
                where_clauses_a,
                where_clauses_b,
            )
        );

        return Ok(ProofTree::new(
            "overlap_check",
            Some("not_goal"),
            vec![proof_tree],
        ));
    }

    // try inverted where-clauses from Wc_a / Wc_b (e.g. T: Debug => T: !Debug).
    // If (equal params ∧ Wc_a ∧ Wc_b) => Wc_i is provable the two impls cannot both apply.
    let inverted: Vec<Wc> = where_clauses_a
        .iter()
        .chain(where_clauses_b)
        .flat_map(|wc| wc.invert())
        .collect();

    if let Some(inverted_wc) = inverted.iter().find(|inverted_wc| {
        prove_goal(
            program,
            env,
            (
                Wcs::all_eq(&trait_ref_a.parameters, &trait_ref_b.parameters),
                where_clauses_a,
                where_clauses_b,
            ),
            inverted_wc,
        )
        .is_ok()
    }) {
        tracing::debug!(
            "proved {:?} assuming {:?}",
            inverted_wc,
            (
                Wcs::all_eq(&trait_ref_a.parameters, &trait_ref_b.parameters),
                where_clauses_a,
                where_clauses_b,
            )
        );

        return Ok(ProofTree::new("overlap_check", Some("inverted"), vec![]));
    }

    bail!("impls may overlap:\n{impl_a:?}\n{impl_b:?}")
}
