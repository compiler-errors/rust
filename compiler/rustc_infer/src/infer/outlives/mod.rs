//! Various code related to computing outlives relations.
use self::env::{OutlivesEnvironment, RegionCheckingAssumptions};
use super::region_constraints::RegionConstraintData;
use super::{InferCtxt, RegionResolutionError, SubregionOrigin};
use crate::infer::free_regions::RegionRelations;
use crate::infer::lexical_region_resolve;
use rustc_data_structures::captures::Captures;
use rustc_middle::traits::query::OutlivesBound;
use rustc_middle::ty::{self, ToPredicate, Ty, TyCtxt};
use rustc_span::DUMMY_SP;

pub mod components;
pub mod env;
pub mod for_liveness;
pub mod obligations;
pub mod test_type_match;
pub mod verify;

#[instrument(level = "debug", skip(clauses), ret)]
pub fn explicit_outlives_bounds<'a, 'tcx>(
    clauses: &'a [ty::Clause<'tcx>],
) -> impl Iterator<Item = OutlivesBound<'tcx>> + Captures<'tcx> + 'a {
    clauses.iter().copied().map(ty::Clause::kind).filter_map(ty::Binder::no_bound_vars).filter_map(
        move |kind| match kind {
            ty::ClauseKind::RegionOutlives(ty::OutlivesPredicate(r_a, r_b)) => {
                Some(OutlivesBound::RegionSubRegion(r_b, r_a))
            }
            ty::ClauseKind::Trait(_)
            | ty::ClauseKind::TypeOutlives(_)
            | ty::ClauseKind::Projection(_)
            | ty::ClauseKind::ConstArgHasType(_, _)
            | ty::ClauseKind::WellFormed(_)
            | ty::ClauseKind::ConstEvaluatable(_) => None,
        },
    )
}

pub fn lower_region_checking_assumptions<'tcx, E>(
    tcx: TyCtxt<'tcx>,
    x: &RegionCheckingAssumptions<'tcx>,
    deeply_normalize_ty: impl Fn(Ty<'tcx>) -> Result<Ty<'tcx>, E>,
) -> Result<OutlivesEnvironment<'tcx>, E> {
    let mut outlives_env = OutlivesEnvironment::builder();
    let caller_bounds: Vec<_> = x
        .param_env
        .caller_bounds()
        .iter()
        .filter_map(|clause| {
            let bound_clause = clause.kind();
            let clause = match bound_clause.skip_binder() {
                region_outlives @ ty::ClauseKind::RegionOutlives(..) => region_outlives,
                ty::ClauseKind::TypeOutlives(ty::OutlivesPredicate(ty, region)) => {
                    ty::ClauseKind::TypeOutlives(ty::OutlivesPredicate(
                        match deeply_normalize_ty(ty) {
                            Ok(ty) => ty,
                            Err(e) => return Some(Err(e)),
                        },
                        region,
                    ))
                }
                _ => return None,
            };
            Some(Ok(bound_clause.rebind(clause).to_predicate(tcx)))
        })
        .try_collect()?;

    outlives_env.add_clauses(&caller_bounds);
    outlives_env.add_outlives_bounds(x.extra_bounds.iter().copied());
    Ok(outlives_env.build())
}

impl<'tcx> InferCtxt<'tcx> {
    /// Process the region constraints and return any errors that
    /// result. After this, no more unification operations should be
    /// done -- or the compiler will panic -- but it is legal to use
    /// `resolve_vars_if_possible` as well as `fully_resolve`.
    ///
    /// If you are in a crate that has access to `rustc_trai_selection`,
    /// then it's probably better to use `resolve_regions_normalizing_outlives_obligations`,
    /// which knows how to normalize registered region obligations.
    #[must_use]
    pub fn resolve_regions(
        &self,
        assumptions: &RegionCheckingAssumptions<'tcx>,
        deeply_normalize_ty: impl Fn(Ty<'tcx>) -> Result<Ty<'tcx>, Ty<'tcx>>,
    ) -> Vec<RegionResolutionError<'tcx>> {
        let outlives_env =
            match lower_region_checking_assumptions(self.tcx, assumptions, &deeply_normalize_ty) {
                Ok(outlives_env) => outlives_env,
                Err(ty) => {
                    return vec![RegionResolutionError::CannotNormalize(
                        ty,
                        SubregionOrigin::RelateRegionParamBound(DUMMY_SP),
                    )];
                }
            };

        match self.process_registered_region_obligations(
            &outlives_env,
            assumptions.param_env,
            &deeply_normalize_ty,
        ) {
            Ok(()) => {}
            Err((ty, origin)) => return vec![RegionResolutionError::CannotNormalize(ty, origin)],
        };

        let (var_infos, data) = {
            let mut inner = self.inner.borrow_mut();
            let inner = &mut *inner;
            assert!(
                self.tainted_by_errors().is_some() || inner.region_obligations.is_empty(),
                "region_obligations not empty: {:#?}",
                inner.region_obligations
            );
            inner
                .region_constraint_storage
                .take()
                .expect("regions already resolved")
                .with_log(&mut inner.undo_log)
                .into_infos_and_data()
        };

        let region_rels = &RegionRelations::new(self.tcx, outlives_env.free_region_map());

        let (lexical_region_resolutions, errors) =
            lexical_region_resolve::resolve(region_rels, var_infos, data);

        let old_value = self.lexical_region_resolutions.replace(Some(lexical_region_resolutions));
        assert!(old_value.is_none());

        errors
    }

    /// Obtains (and clears) the current set of region
    /// constraints. The inference context is still usable: further
    /// unifications will simply add new constraints.
    ///
    /// This method is not meant to be used with normal lexical region
    /// resolution. Rather, it is used in the NLL mode as a kind of
    /// interim hack: basically we run normal type-check and generate
    /// region constraints as normal, but then we take them and
    /// translate them into the form that the NLL solver
    /// understands. See the NLL module for mode details.
    pub fn take_and_reset_region_constraints(&self) -> RegionConstraintData<'tcx> {
        assert!(
            self.inner.borrow().region_obligations.is_empty(),
            "region_obligations not empty: {:#?}",
            self.inner.borrow().region_obligations
        );

        self.inner.borrow_mut().unwrap_region_constraints().take_and_reset_data()
    }

    /// Gives temporary access to the region constraint data.
    pub fn with_region_constraints<R>(
        &self,
        op: impl FnOnce(&RegionConstraintData<'tcx>) -> R,
    ) -> R {
        let mut inner = self.inner.borrow_mut();
        op(inner.unwrap_region_constraints().data())
    }
}
