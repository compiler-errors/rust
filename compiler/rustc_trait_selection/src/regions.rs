use rustc_infer::infer::outlives::env::RegionCheckingAssumptions;
use rustc_infer::infer::{InferCtxt, RegionResolutionError};
use rustc_middle::traits::ObligationCause;

pub trait InferCtxtRegionExt<'tcx> {
    fn resolve_regions_normalizing_outlives_obligations(
        &self,
        outlives_env: &RegionCheckingAssumptions<'tcx>,
    ) -> Vec<RegionResolutionError<'tcx>>;
}

impl<'tcx> InferCtxtRegionExt<'tcx> for InferCtxt<'tcx> {
    fn resolve_regions_normalizing_outlives_obligations(
        &self,
        outlives_env: &RegionCheckingAssumptions<'tcx>,
    ) -> Vec<RegionResolutionError<'tcx>> {
        self.resolve_regions(outlives_env, |ty| {
            let ty = self.resolve_vars_if_possible(ty);

            if self.next_trait_solver() {
                crate::solve::deeply_normalize_with_skipped_universes(
                    self.at(&ObligationCause::dummy(), outlives_env.param_env),
                    ty,
                    vec![None; ty.outer_exclusive_binder().as_usize()],
                )
                .map_err(|_| ty)
            } else {
                Ok(ty)
            }
        })
    }
}
