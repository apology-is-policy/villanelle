#include "module.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

static struct vn2_wait_hold *holds[10];
static struct vn2_wait_steady *steady;
static int tokens[10], steady_token;
static void *selected;
static unsigned scenario, ready_picks, choices, starts;
static unsigned live, withdraw_due, release_due;
static int cancelled;
static const char *ready_counts;

static void require(int valid, const char *what) {
    if (!valid) {
        fprintf(stderr, "scenario %u at choice %u: %s\n", scenario, choices, what);
        exit(1);
    }
}
static unsigned check_hold(struct vn2_wait_hold *r) {
    uintptr_t id = (uintptr_t)r->in_l;
    require(id == 1 || id == 2 || id == 9, "unknown lease");
    require(r->in_xs->len == 2 && *r->in_cell == id, "lost bound arguments");
    const uint32_t *xs = r->in_xs->data;
    require(xs[0] == id && xs[1] == 8, "wrong vector");
    return (unsigned)id;
}
uint8_t vn2_should_cancel_root(uint64_t turn) {
    const unsigned at[] = {1, 3, 4, 0, 2, 2, 3, 3, 3};
    require(!cancelled && turn == choices + 1, "wrong cancellation poll");
    if (turn != at[scenario]) return 0;
    cancelled = 1;
    for (unsigned id = 0; id < 10; ++id)
        if (holds[id]) withdraw_due |= 1u << id;
    return 1;
}
static void before_choice(void) {
    require(!withdraw_due && !release_due, "choice before withdrawal and release");
    ++choices;
}
uint64_t vn2_pick_turn(uint64_t n) {
    before_choice();
    require((*ready_counts == '1' || *ready_counts == '2') &&
            n == (unsigned)(*ready_counts - '0'), "wrong ready set size");
    ++ready_counts;
    ++ready_picks;
    if (scenario == 0) return ready_picks == 2 || ready_picks == 3;
    if (scenario == 1) return ready_picks == 1 || ready_picks == 3;
    return (scenario == 4 || scenario == 6) && ready_picks == 2;
}
uint64_t vn2_pick_waiting(void *const *states, uint64_t n) {
    before_choice();
    require(!selected, "previous host choice undelivered");
    void *expected[4];
    unsigned count = 0;
    // The root is first, followed by members in spawn order.
    if (steady && scenario != 8) expected[count++] = &steady_token;
    if (holds[9]) expected[count++] = &tokens[9];
    if (holds[1]) expected[count++] = &tokens[1];
    if (holds[2]) expected[count++] = &tokens[2];
    if (steady && scenario == 8) expected[count++] = &steady_token;
    require(n && n == count, "wrong pending set size");
    for (unsigned i = 0; i < count; ++i)
        require(states[i] == expected[i], "wrong host handle or order");
    unsigned index = scenario == 2 && n == 2;
    selected = states[index];
    return index;
}
int32_t vn2_ext_acquire(uint32_t id, void **out) {
    require(id == 1 || id == 2 || id == 9, "invalid lease id");
    require(!(live & (1u << id)), "lease already owned");
    live |= 1u << id;
    *out = (void *)(uintptr_t)id;
    printf("acquire(%u) -> ok {lease#%u}\n", (unsigned)id, (unsigned)id);
    return VN2_ACQUIRE_OK;
}
void vn2_start_hold(struct vn2_wait_hold *r) {
    unsigned id = check_hold(r);
    require(!cancelled && !holds[id] && !r->host_state, "unexpected issue");
    holds[id] = r;
    r->host_state = &tokens[id];
    ++starts;
}
void vn2_withdraw_hold(struct vn2_wait_hold *r) {
    unsigned id = check_hold(r);
    require(holds[id] == r && r->host_state == &tokens[id], "wrong withdrawal");
    require(!selected && !release_due && (withdraw_due & (1u << id)), "unexpected withdrawal");
    withdraw_due &= ~(1u << id);
    holds[id] = NULL;
    release_due = id;
}
void vn2_release_lease(void *handle) {
    uintptr_t id = (uintptr_t)handle;
    require((id == 1 || id == 2 || id == 9) && (live & (1u << id)), "unowned release");
    require(cancelled && !holds[id] && (!release_due || release_due == id), "release order");
    release_due = 0;
    live &= ~(1u << id);
    printf("lease.release(lease#%" PRIuPTR ") -> released {}\n", id);
}
int32_t vn2_complete_hold(struct vn2_wait_hold *r) {
    unsigned id = check_hold(r);
    require(holds[id] == r && selected == &tokens[id] && selected == r->host_state,
            "unexpected completion");
    require(live & (1u << id), "completion lost its lease");
    holds[id] = selected = NULL;
    live &= ~(1u << id);
    free(r->in_xs->data);
    printf("hold(lease#%u, [%u, 8], %u) -> ", id, id, id);
    *r->in_cell = 10 + id;
    if (scenario == 3 && id == 1) {
        puts("cancelled {}");
        return VN2_HOLD_CANCELLED;
    }
    *r->out_0_value_0 = 70 + id;
    printf("value {%u}\n", 70 + id);
    return VN2_HOLD_VALUE;
}
void vn2_start_steady(struct vn2_wait_steady *r) {
    require(!steady && !r->host_state, "duplicate steady request");
    steady = r;
    r->host_state = &steady_token;
}
int32_t vn2_complete_steady(struct vn2_wait_steady *r) {
    require(steady == r && selected == &steady_token && selected == r->host_state,
            "wrong steady handle");
    steady = selected = NULL;
    puts("steady() -> ok {}");
    return VN2_STEADY_OK;
}
int32_t vn2_ext_mark(uint32_t id, uint32_t cell) {
    require(!withdraw_due && !release_due, "task resumed before cleanup");
    printf("mark(%u, %u) -> ok {}\n", (unsigned)id, (unsigned)cell);
    return VN2_MARK_OK;
}
int main(void) {
    const char *offers[] = {"2222111", "2122111", "2122111", "2111111", "12111",
                            "11111", "12111", "11111", "21111111"};
    const unsigned issues[] = {0, 2, 2, 2, 2, 1, 1, 1, 1};
    for (scenario = 0; scenario < sizeof offers / sizeof *offers; ++scenario) {
        ready_counts = offers[scenario];
        choices = ready_picks = starts = cancelled = 0;
        uint32_t first, second;
        if (scenario < 4) {
            require(vn2_call_pair(&first, &second) == VN2_PAIR_OK, "pair result");
            printf("done ok {%u, %u}\n", (unsigned)first, (unsigned)second);
        } else {
            if (scenario < 7)
                require(vn2_call_together(scenario == 4, &first) == VN2_TOGETHER_OK, "root result");
            else if (scenario == 7)
                require(vn2_call_nested(&first) == VN2_NESTED_OK, "nested result");
            else
                require(vn2_call_mixed(&first) == VN2_MIXED_OK, "mixed result");
            printf("done ok {%u}\n", (unsigned)first);
        }
        require(!*ready_counts && starts == issues[scenario], "missing choice or issue");
        require(!live && !withdraw_due && !release_due && !steady && !selected, "unfinished request");
    }
    return 0;
}
