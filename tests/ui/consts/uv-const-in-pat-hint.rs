//@ revisions: stock gce
//@ check-pass

#![feature(associated_const_equality)]
#![cfg_attr(gce, feature(generic_const_exprs))]
//[gce]~^ WARN the feature `generic_const_exprs` is incomplete

fn main() {
    // Make sure we don't ICE in THIR pattern analysis when writeback
    // may, depending on GCE's lazy normalization of consts, contain
    // an unevaluated const.
    let [(), ()]: [(); 1 + 1] = [(), ()];
}