
/* Safe Rust API over the extracted RSS safe-distance check. */

/// Division-free RSS longitudinal check. Returns (safe, margin) where
/// margin is the RSS inequality scaled by 2*b_min*b_max (rss_margin >= 0
/// iff safe; magnitude is a graded severity signal). Monotone the way
/// physics demands (rss_monotone_* in Rss.v); i64-safe on the rss_dom
/// parameter domain, enforced by the bindings.
pub fn rss_check(b_min: i64, b_max: i64, gap: i64, v_rear: i64, v_front: i64,
                 rho: i64, a_max: i64) -> (bool, i64) {
    let p = Program::new();
    let (safe, margin) =
        p.RocqRustExamples_Rss_rss_demo(b_min, b_max, gap, v_rear, v_front, rho, a_max);
    (safe, margin)
}
