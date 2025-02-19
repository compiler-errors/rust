use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::*;
use rustc_middle::span_bug;
use rustc_middle::ty::{self, TyCtxt};

use crate::{errors, util};

pub(super) struct CheckPackedRef;

impl<'tcx> crate::MirLint<'tcx> for CheckPackedRef {
    fn run_lint(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) {
        let typing_env = body.typing_env(tcx);
        let mut checker = PackedRefChecker { body, tcx, typing_env };
        checker.visit_body(body);
    }
}

struct PackedRefChecker<'a, 'tcx> {
    body: &'a Body<'tcx>,
    tcx: TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
}

impl<'tcx> Visitor<'tcx> for PackedRefChecker<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if context.is_borrow() && util::is_disaligned(self.tcx, self.body, self.typing_env, *place)
        {
            let span = self.body.source_info(location).span;
            let def_id = self.body.source.instance.def_id();
            if let Some(impl_def_id) = self.tcx.impl_of_method(def_id)
                && self.tcx.is_builtin_derived(impl_def_id)
            {
                // If we ever reach here it means that the generated derive
                // code is somehow doing an unaligned reference, which it
                // shouldn't do.
                span_bug!(span, "builtin derive created an unaligned reference");
            } else {
                self.tcx.dcx().emit_err(errors::UnalignedPackedRef { span });
            }
        }
    }
}
