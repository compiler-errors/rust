use rustc_hir::def_id::DefId;
use rustc_infer::infer::{DefineOpaqueTypes, InferOk, RegionVariableOrigin, TyCtxtInferExt};
use rustc_infer::traits::Obligation;
use rustc_middle::traits::ObligationCause;
use rustc_middle::ty::{self, ToPredicate, Ty, TyCtxt};
use rustc_span::DUMMY_SP;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt;
use rustc_trait_selection::traits::{elaborate, NormalizeExt, SelectionContext};

pub(crate) fn impl_may_be_shadowed_by_trait_object<'tcx>(
    tcx: TyCtxt<'tcx>,
    impl_def_id: DefId,
) -> bool {
    let trait_def_id = tcx.trait_id_of_impl(impl_def_id).expect("only called for trait impls");
    if !tcx.object_safety_violations(trait_def_id).is_empty() {
        return false;
    }

    let impl_trait_ref = tcx.impl_trait_ref(impl_def_id).expect("only called for trait impls");
    if !matches!(
        impl_trait_ref.skip_binder().self_ty().kind(),
        ty::Param(..) | ty::Alias(..) | ty::Dynamic(..)
    ) {
        return false;
    }

    let infcx = tcx.infer_ctxt().intercrate(true).build();
    let impl_args = infcx.fresh_args_for_item(DUMMY_SP, impl_def_id);

    let cause = &ObligationCause::dummy();
    let param_env = ty::ParamEnv::empty();

    let impl_trait_ref = impl_trait_ref.instantiate(tcx, impl_args);

    let impl_predicates = tcx.predicates_of(impl_def_id).instantiate(tcx, impl_args).predicates;
    let InferOk { value: (impl_trait_ref, impl_predicates), obligations: normalize_obligations } =
        infcx.at(cause, param_env).normalize((impl_trait_ref, impl_predicates));

    let mut existential_predicates = vec![ty::Binder::dummy(ty::ExistentialPredicate::Trait(
        ty::ExistentialTraitRef::erase_self_ty(tcx, impl_trait_ref),
    ))];

    let principal_clause: ty::Clause<'tcx> = impl_trait_ref.to_predicate(tcx);
    existential_predicates.extend(
        elaborate(tcx, [principal_clause]).filter_map(|clause| clause.as_projection_clause()).map(
            |proj| {
                proj.map_bound(|proj| {
                    ty::ExistentialPredicate::Projection(ty::ExistentialProjection::erase_self_ty(
                        tcx, proj,
                    ))
                })
            },
        ),
    );
    existential_predicates.sort_by(|a, b| a.skip_binder().stable_cmp(tcx, &b.skip_binder()));
    existential_predicates.dedup();
    let existential_predicates = tcx.mk_poly_existential_predicates(&existential_predicates);

    let self_ty = Ty::new_dynamic(
        tcx,
        existential_predicates,
        infcx.next_region_var(RegionVariableOrigin::MiscVariable(DUMMY_SP)),
        ty::Dyn,
    );
    let InferOk { value: self_ty, obligations: normalize_obligations2 } =
        infcx.at(cause, param_env).normalize(self_ty);

    let Ok(InferOk { value: (), obligations: eq_obligations }) =
        infcx.at(cause, param_env).eq(DefineOpaqueTypes::No, self_ty, impl_trait_ref.self_ty())
    else {
        return false;
    };

    let mut selcx = SelectionContext::new(&infcx);
    let impossible_obligation = impl_predicates
        .into_iter()
        .map(|clause| Obligation::new(tcx, cause.clone(), param_env, clause))
        .chain(normalize_obligations)
        .chain(normalize_obligations2)
        .chain(eq_obligations)
        .find(|obligation| {
            if infcx.next_trait_solver() {
                infcx.evaluate_obligation(&obligation).map_or(false, |result| !result.may_apply())
            } else {
                // We use `evaluate_root_obligation` to correctly track intercrate
                // ambiguity clauses. We cannot use this in the new solver.
                selcx.evaluate_root_obligation(&obligation).map_or(
                    false, // Overflow has occurred, and treat the obligation as possibly holding.
                    |result| !result.may_apply(),
                )
            }
        });

    impossible_obligation.is_none()
}
