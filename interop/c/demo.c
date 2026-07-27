/* C caller for the Rocq-verified cores — the C ABI is the ground truth
 * every other language binds through.
 *
 * Note what this file does NOT have: the Python bindings' validation
 * layer.  A C caller sits directly on the ABI, so it gets the status
 * codes and the checked-build containment (a bypassed domain => panic
 * => ROCQ_ERR_PANIC, demonstrated below), but the proved-domain checks
 * documented in rocq_ffi.h are ITS OWN responsibility.
 *
 * Build & run:  make interop
 */

#include <stdio.h>
#include <assert.h>
#include <string.h>
#include "rocq_ffi.h"

int main(void) {
    puts("=== C caller: Rocq-verified cores over the raw ABI ===\n");

    /* verified insertion sort */
    int64_t xs[] = {5, 3, 8, 1, 9, -4};
    int64_t sorted[6];
    assert(rocq_sort_i64(xs, 6, sorted) == ROCQ_OK);
    printf("sort      : [5 3 8 1 9 -4] -> [");
    for (int i = 0; i < 6; i++) printf("%s%lld", i ? " " : "", (long long)sorted[i]);
    puts("]");
    for (int i = 0; i + 1 < 6; i++) assert(sorted[i] <= sorted[i + 1]);

    /* Fletcher-16 (symbols kept in [0,254] — our responsibility here) */
    int64_t frame[] = {0x10, 0x22, 0x00, 0x7F, 0x22, 0x01, 0x54};
    int64_t s1, s2;
    assert(rocq_fletcher16(frame, 7, &s1, &s2) == ROCQ_OK);
    printf("fletcher16: frame checksum = 0x%04llx\n", (long long)(256 * s2 + s1));

    /* RSS safe distance: 20 m/s behind 15 m/s */
    uint8_t safe; int64_t margin;
    assert(rocq_rss_check(400, 800, 3000, 2000, 1500, 10, 300,
                          &safe, &margin) == ROCQ_OK);
    printf("rss       : gap 30 m -> %s\n", safe ? "SAFE" : "UNSAFE");
    assert(!safe);
    assert(rocq_rss_check(400, 800, 8000, 2000, 1500, 10, 300,
                          &safe, &margin) == ROCQ_OK);
    printf("rss       : gap 80 m -> %s (margin %lld)\n",
           safe ? "SAFE" : "UNSAFE", (long long)margin);
    assert(safe);

    /* MPC: track ref=1000 from rest */
    int64_t cost; int8_t action;
    assert(rocq_mpc_decide(1000, 0, 0, 5, &cost, &action) == ROCQ_OK);
    printf("mpc       : ref 1000 from rest -> action %+d, cost %lld\n",
           action, (long long)cost);
    assert(action == 1);

    /* Containment: bypass the world-frame ingest domain from C.
     * dx = (2^62-1) - (-(2^62)-...) overflows i64; the checked build
     * panics and the ABI reports it — it does NOT corrupt or crash us. */
    {
        uint8_t cls = 0, tgt = 0, ok, verdict;
        int64_t big = 4611686018427387903LL;       /* 2^62 - 1 */
        int64_t x = big, y = 0, vx = 0, vy = 0, w = 180, l = 450,
                conf = 90, tl = 0, score, mask;
        int32_t rc = rocq_scene_world_check(
            3, 350, 0, 1400, /* road */
            -big - 2, 0, 0, 0, 0, /* hostile pose: forces subtraction overflow */
            &cls, &x, &y, &vx, &vy, &w, &l, &conf, &tgt, &tl, 1,
            &ok, &verdict, &score, &mask);
        printf("containmt : hostile world pose -> status %d (ROCQ_ERR_PANIC)\n", rc);
        assert(rc == ROCQ_ERR_PANIC);
    }

    puts("\nC caller: all checks passed.");
    return 0;
}
