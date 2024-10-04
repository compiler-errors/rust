//! There are four type combiners: [TypeRelating], [Lub], and [Glb],
//! and `NllTypeRelating` in rustc_borrowck, which is only used for NLL.
//!
//! Each implements the trait [TypeRelation] and contains methods for
//! combining two instances of various things and yielding a new instance.
//! These combiner methods always yield a `Result<T>`. To relate two
//! types, you can use `infcx.at(cause, param_env)` which then allows
//! you to use the relevant methods of [At](crate::infer::at::At).
//!
//! Combiners mostly do their specific behavior and then hand off the
//! bulk of the work to [InferCtxt::super_combine_tys] and
//! [InferCtxt::super_combine_consts].
//!
//! Combining two types may have side-effects on the inference contexts
//! which can be undone by using snapshots. You probably want to use
//! either [InferCtxt::commit_if_ok] or [InferCtxt::probe].
//!
//! On success, the  LUB/GLB operations return the appropriate bound. The
//! return value of `Equate` or `Sub` shouldn't really be used.

use rustc_middle::traits::solve::Goal;
pub use rustc_middle::ty::relate::combine::*;
use rustc_middle::ty::{self, TyCtxt, Upcast};

use super::StructurallyRelateAliases;
use super::glb::Glb;
use super::lub::Lub;
use super::type_relating::TypeRelating;
use crate::infer::{DefineOpaqueTypes, InferCtxt, TypeTrace};
use crate::traits::{Obligation, PredicateObligation};

#[derive(Clone)]
pub struct CombineFields<'infcx, 'tcx> {
    pub infcx: &'infcx InferCtxt<'tcx>,
    pub trace: TypeTrace<'tcx>,
    pub param_env: ty::ParamEnv<'tcx>,
    pub goals: Vec<Goal<'tcx, ty::Predicate<'tcx>>>,
    pub define_opaque_types: DefineOpaqueTypes,
}

impl<'infcx, 'tcx> CombineFields<'infcx, 'tcx> {
    pub fn new(
        infcx: &'infcx InferCtxt<'tcx>,
        trace: TypeTrace<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
        define_opaque_types: DefineOpaqueTypes,
    ) -> Self {
        Self { infcx, trace, param_env, define_opaque_types, goals: vec![] }
    }

    pub(crate) fn into_obligations(self) -> Vec<PredicateObligation<'tcx>> {
        self.goals
            .into_iter()
            .map(|goal| {
                Obligation::new(
                    self.infcx.tcx,
                    self.trace.cause.clone(),
                    goal.param_env,
                    goal.predicate,
                )
            })
            .collect()
    }
}

impl<'infcx, 'tcx> CombineFields<'infcx, 'tcx> {
    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.infcx.tcx
    }

    pub fn equate<'a>(
        &'a mut self,
        structurally_relate_aliases: StructurallyRelateAliases,
    ) -> TypeRelating<'a, 'infcx, 'tcx> {
        TypeRelating::new(self, structurally_relate_aliases, ty::Invariant)
    }

    pub fn sub<'a>(&'a mut self) -> TypeRelating<'a, 'infcx, 'tcx> {
        TypeRelating::new(self, StructurallyRelateAliases::No, ty::Covariant)
    }

    pub fn sup<'a>(&'a mut self) -> TypeRelating<'a, 'infcx, 'tcx> {
        TypeRelating::new(self, StructurallyRelateAliases::No, ty::Contravariant)
    }

    pub fn lub<'a>(&'a mut self) -> Lub<'a, 'infcx, 'tcx> {
        Lub::new(self)
    }

    pub fn glb<'a>(&'a mut self) -> Glb<'a, 'infcx, 'tcx> {
        Glb::new(self)
    }

    pub fn register_obligations(
        &mut self,
        obligations: impl IntoIterator<Item = Goal<'tcx, ty::Predicate<'tcx>>>,
    ) {
        self.goals.extend(obligations);
    }

    pub fn register_predicates(
        &mut self,
        obligations: impl IntoIterator<Item: Upcast<TyCtxt<'tcx>, ty::Predicate<'tcx>>>,
    ) {
        self.goals.extend(
            obligations
                .into_iter()
                .map(|to_pred| Goal::new(self.infcx.tcx, self.param_env, to_pred)),
        )
    }
}
