/* rocq_ffi.h — C ABI contract for the Rocq-verified cores.
 *
 * This header IS the interop contract: any language with a C FFI (C, C++,
 * Ruby/Fiddle, Julia/ccall, Node/koffi, ...) can call the verified cores
 * through it.  Read the per-function comments carefully:
 *
 *   - Every function returns a status code (ROCQ_OK / ROCQ_ERR_*);
 *     results come back via out-pointers.
 *   - The native build uses CHECKED arithmetic: an overflow outside a
 *     proved domain panics and is CONTAINED (ROCQ_ERR_PANIC) — never
 *     silent corruption, never unwinding across the ABI.
 *   - The Python bindings implement a validation layer (proved-domain and
 *     theorem-hypothesis checks with theorem-citing errors).  THAT LAYER
 *     LIVES IN THE BINDING, NOT IN THIS ABI: a new language binding must
 *     re-implement it.  The DOMAIN comments below state, per function,
 *     what to enforce and which Rocq theorem proves it sufficient.
 */

#ifndef ROCQ_FFI_H
#define ROCQ_FFI_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

#define ROCQ_OK            0
#define ROCQ_ERR_NULL     (-1)  /* required pointer NULL with nonzero len */
#define ROCQ_ERR_PANIC    (-2)  /* extracted code panicked; contained    */
#define ROCQ_ERR_CAPACITY (-3)  /* output exceeded provided buffer       */

/* ---- sorting (InsertionSort.v) ------------------------------------ */
/* DOMAIN: none — comparisons only, total on any i64.
 * Proved: output sorted and a permutation of the input.               */
int32_t rocq_sort_i64(const int64_t *input, size_t len, int64_t *out);

/* ---- trading analytics (Trading.v) -------------------------------- */
/* DOMAIN: |price| <= 2^62 - 1 (max_profit_fits_i64).                  */
int32_t rocq_max_profit(const int64_t *px, size_t len, int64_t *out);
int32_t rocq_max_profit_checked(const int64_t *px, size_t len, int64_t *out);
int32_t rocq_max_drawdown(const int64_t *px, size_t len, int64_t *out);
int32_t rocq_max_drawdown_checked(const int64_t *px, size_t len, int64_t *out);
/* DOMAIN: limit >= 0; -limit <= initial <= limit (run_orders_within_limit
 * hypothesis); limit + max|qty| <= INT64_MAX (step_fits_i64).         */
int32_t rocq_run_orders(int64_t limit, int64_t initial, const uint8_t *sides,
                        const int64_t *qtys, size_t len, int64_t *out);
int32_t rocq_run_orders_checked(int64_t limit, int64_t initial,
                                const uint8_t *sides, const int64_t *qtys,
                                size_t len, int64_t *out);
/* out must hold 3 int64: [max_profit, max_drawdown, final_position].  */
int32_t rocq_analyze(const int64_t *px, size_t px_len, int64_t limit,
                     const uint8_t *sides, const int64_t *qtys,
                     size_t os_len, int64_t *out);
int32_t rocq_analyze_checked(const int64_t *px, size_t px_len, int64_t limit,
                             const uint8_t *sides, const int64_t *qtys,
                             size_t os_len, int64_t *out);

/* ---- RLE codec (Rle.v) -------------------------------------------- */
/* DOMAIN: none needed.  out_vals/out_counts sized len suffices
 * (encode_length_le).                                                 */
int32_t rocq_rle_encode(const int64_t *input, size_t len, int64_t *out_vals,
                        uint64_t *out_counts, size_t *out_n);
int32_t rocq_rle_decode(const int64_t *vals, const uint64_t *counts, size_t n,
                        int64_t *out, size_t out_cap, size_t *out_len);

/* ---- modular exponentiation (ModExp.v) ---------------------------- */
/* DOMAIN: 1 <= m <= 2^32 (pow_mod_correct hypothesis m != 0;
 * square_fits/mixed_fits for the upper bound).                        */
int32_t rocq_pow_mod(uint64_t m, uint64_t b, uint64_t e, uint64_t *out);

/* ---- order FSM (OrderFsm.v) --------------------------------------- */
/* DOMAIN: qty >= 0 (init_run_invariant).  Events safe for any i64.    */
int32_t rocq_order_fsm_run(int64_t qty, const uint8_t *fills,
                           const int64_t *qtys, size_t n,
                           int64_t *out_filled, uint8_t *out_canceled);

/* ---- drive-mode FSM (DriveModeFsm.v) ------------------------------ */
/* DOMAIN: none — comparisons only, any i64 speed is safe.
 * tags: 0 shift, 1 fault, 2 clear; gears: 0 P, 1 R, 2 N, 3 D.
 * out_mode: 0 P, 1 R, 2 N, 3 D, 4 Fault.                              */
int32_t rocq_drive_fsm_run(const uint8_t *tags, const uint8_t *gears,
                           const int64_t *speeds, size_t n, uint8_t *out_mode);

/* ---- hybrid energy FSM (HybridEnergyFsm.v) ------------------------ */
/* DOMAIN: none — designed out for any request stream.
 * out_mode: 0 EvOnly, 1 HybridAssist, 2 ChargeSustain.                */
int32_t rocq_energy_fsm_run(int64_t soc0, const int64_t *reqs, size_t n,
                            uint8_t *out_mode, int64_t *out_soc);

/* ---- PID (Pid.v) --------------------------------------------------- */
/* DOMAIN: |gains| <= 2^15, |errors| <= 2^31 (raw_fits_i64).           */
int32_t rocq_pid_run(int64_t kp, int64_t ki, int64_t kd,
                     const int64_t *errors, size_t n, int64_t *out_us,
                     int64_t *out_integ, int64_t *out_prev);

/* ---- hysteresis thermostat (Hysteresis.v) ------------------------- */
/* DOMAIN: |t0| <= 2^62 (step_fits_i64).                               */
int32_t rocq_thermo_run(int64_t t0, const int64_t *rhs, const int64_t *rcs,
                        size_t n, int64_t *out_t, uint8_t *out_heating);

/* ---- finite-set MPC (Mpc.v) --------------------------------------- */
/* DOMAIN: |pos|,|vel|,|reference| <= 2^20, horizon <= 8
 * (mpc_fits_i64, CB_cap).  out_action: -1 / 0 / +1.                   */
int32_t rocq_mpc_decide(int64_t reference, int64_t pos, int64_t vel,
                        uint64_t horizon, int64_t *out_cost,
                        int8_t *out_action);

/* ---- sensor fusion (SensorFusion.v) ------------------------------- */
/* DOMAIN: |reading|, tol <= 2^62 - 1 (gate_fits_i64); n >= 1.         */
int32_t rocq_fusion_fuse(int64_t tol, const int64_t *readings, size_t n,
                         int64_t *out_fused, uint8_t *out_flags);

/* ---- ADAS scene checker, ego frame (SceneModel.v) ----------------- */
/* DOMAIN: NONE — validate-then-compute; total for any i64 inputs
 * (validated_bounds, pair_arith_fits).
 * classes: 0 vehicle, 1 pedestrian, 2 bicycle, 3 sign, 4 light;
 * tl: 0 none, 1 red, 2 yellow, 3 green;
 * verdicts: 0 confirmed, 1 low-confidence, 2 implausible.             */
int32_t rocq_scene_check(int64_t lanes, int64_t lane_w, int64_t curv,
                         int64_t limit, int64_t ego_v, const uint8_t *classes,
                         const int64_t *xs, const int64_t *ys,
                         const int64_t *vxs, const int64_t *vys,
                         const int64_t *ws, const int64_t *ls,
                         const int64_t *confs, const uint8_t *targets,
                         const int64_t *tls, size_t n, uint8_t *out_scene_ok,
                         uint8_t *out_verdicts, int64_t *out_scores,
                         int64_t *out_masks);

/* ---- ADAS scene checker, world frame (SceneWorld.v) --------------- */
/* DOMAIN: |coordinates|, |velocities|, |pose| <= 2^62 - 1
 * (ingest_fits_i64); heading in 0..3 (egress_ingest_id hypothesis).
 * Bypassing the domain => ROCQ_ERR_PANIC (contained), never silence.  */
int32_t rocq_scene_world_check(int64_t lanes, int64_t lane_w, int64_t curv,
                               int64_t limit, int64_t px, int64_t py,
                               int64_t ph, int64_t pvx, int64_t pvy,
                               const uint8_t *classes, const int64_t *xs,
                               const int64_t *ys, const int64_t *vxs,
                               const int64_t *vys, const int64_t *ws,
                               const int64_t *ls, const int64_t *confs,
                               const uint8_t *targets, const int64_t *tls,
                               size_t n, uint8_t *out_scene_ok,
                               uint8_t *out_verdicts, int64_t *out_scores,
                               int64_t *out_masks);

/* ---- Fletcher-16 (Fletcher.v) ------------------------------------- */
/* DOMAIN: symbols in [0, 254] — the single_error_detected HYPOTHESIS.
 * This domain guards a PROPERTY, not a width: 0 and 255 are congruent
 * mod 255; out-of-range symbols run fine but forfeit the detection
 * guarantee.  Packed checksum = 256*s2 + s1.                          */
int32_t rocq_fletcher16(const int64_t *data, size_t n, int64_t *out_s1,
                        int64_t *out_s2);

/* ---- RSS safe distance (Rss.v) ------------------------------------ */
/* DOMAIN (rss_dom / rss_fits_i64): gap in [0, 1e6] cm, speeds in
 * [0, 7000] cm/s, rho in [1, 50] deciseconds, accelerations b_min,
 * b_max in [1, 1500] and a_max in [0, 1500] cm/s^2.
 * margin is the RSS inequality scaled by 200*b_min*b_max.             */
int32_t rocq_rss_check(int64_t b_min, int64_t b_max, int64_t gap,
                       int64_t v_rear, int64_t v_front, int64_t rho,
                       int64_t a_max, uint8_t *out_safe, int64_t *out_margin);

#ifdef __cplusplus
}
#endif

#endif /* ROCQ_FFI_H */
