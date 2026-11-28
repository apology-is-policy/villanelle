#include "module.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static unsigned scenario, choices, ready, starts, withdrawals, releases;
static int tokens[4];
static struct vn2_wait_hold *holds[4];
static struct vn2_wait_steady *steady;
static void *selected;
static unsigned awaiting_release;
static int owner_continued;

static void require(int ok, const char *reason) {
    if (!ok) {
        fprintf(stderr, "split %u, choice %u: %s\n", scenario, choices, reason);
        exit(1);
    }
}

uint8_t vn2_should_cancel_root(uint64_t turn) {
    require(turn == choices + 1, "unexpected poll");
    return scenario == 1 && turn == 6;
}

uint64_t vn2_pick_turn(uint64_t count) {
    require(!selected && !awaiting_release, "ready choice during delivery");
    ++choices;
    ++ready;
    if (ready <= 3) {
        require(count == 4 - ready, "wrong ready members before cancel");
        if (scenario == 0) return count - 1;
    }
    return 0;
}

uint64_t vn2_pick_waiting(void *const *states, uint64_t count) {
    require(!selected && !awaiting_release && count, "unexpected host choice");
    unsigned slot = 0;
    if (steady) {
        require(slot < count && states[slot++] == &tokens[0], "missing root handle");
    }
    for (unsigned id = 1; id <= 3; ++id) {
        if (holds[id]) {
            require(slot < count && states[slot++] == &tokens[id], "wrong member handle");
        }
    }
    require(slot == count, "wrong pending count");
    unsigned index = scenario == 2 && choices == 3;
    ++choices;
    selected = states[index];
    return index;
}

int32_t vn2_ext_acquire(uint32_t id, void **lease) {
    require(id >= 1 && id <= 3, "unknown lease");
    *lease = (void *)(uintptr_t)id;
    printf("acquire(%u) -> ok {lease#%u}\n", (unsigned)id, (unsigned)id);
    return VN2_ACQUIRE_OK;
}

static unsigned bound_id(struct vn2_wait_hold *request) {
    uintptr_t id = (uintptr_t)request->in_l;
    require(id >= 1 && id <= 3 && *request->in_cell == id, "wrong bound operands");
    return (unsigned)id;
}

void vn2_start_hold(struct vn2_wait_hold *request) {
    unsigned id = bound_id(request);
    require(!holds[id] && !request->host_state, "duplicate start");
    request->host_state = &tokens[id];
    holds[id] = request;
    ++starts;
}

void vn2_withdraw_hold(struct vn2_wait_hold *request) {
    unsigned id = bound_id(request);
    require(holds[id] == request && request->host_state == &tokens[id], "wrong withdrawal");
    require(!awaiting_release && !selected, "withdrawal overlaps delivery");
    if (id == 2) {
        require(scenario == 1 && owner_continued && choices == 5, "sibling withdrawn early");
    } else {
        require(!owner_continued && choices == (scenario == 2 ? 7u : 5u), "wrong cancel turn");
        require(id != 3 || !holds[1], "withdrawal order");
    }
    holds[id] = NULL;
    awaiting_release = id;
    ++withdrawals;
}

void vn2_release_lease(void *lease) {
    uintptr_t id = (uintptr_t)lease;
    require(id && awaiting_release == id, "release before withdrawal or wrong lease");
    awaiting_release = 0;
    ++releases;
    printf("lease.release(lease#%u) -> released {}\n", (unsigned)id);
}

int32_t vn2_complete_hold(struct vn2_wait_hold *request) {
    unsigned id = bound_id(request);
    require(holds[id] == request && selected == &tokens[id], "wrong completion");
    require((id == 1 && scenario == 2 && !owner_continued) ||
            (id == 2 && scenario != 1 && owner_continued), "completed withdrawn request");
    holds[id] = selected = NULL;
    *request->in_cell = id + 10;
    *request->out_0_value_0 = id + 70;
    printf("hold(lease#%u, %u) -> value {%u}\n", id, id, id + 70);
    return VN2_HOLD_VALUE;
}

void vn2_start_steady(struct vn2_wait_steady *request) {
    require(!steady && !request->host_state, "duplicate root request");
    steady = request;
    request->host_state = &tokens[0];
}

int32_t vn2_complete_steady(struct vn2_wait_steady *request) {
    require(steady == request && selected == &tokens[0], "wrong root completion");
    steady = selected = NULL;
    puts("steady() -> ok {}");
    return VN2_STEADY_OK;
}

int32_t vn2_ext_mark(uint32_t id) {
    if (id == 9) {
        require(!owner_continued && holds[2] && !holds[1] && !holds[3], "wrong membership");
        require(releases == (scenario == 2 ? 1u : 2u), "owner continued before releases");
        require(choices == (scenario == 2 ? 7u : 5u), "cancel gave up the turn");
        owner_continued = 1;
    }
    printf("mark(%u) -> ok {}\n", (unsigned)id);
    return VN2_MARK_OK;
}

int main(void) {
    const unsigned expected_withdrawals[] = {2, 3, 1};
    for (scenario = 0; scenario < 3; ++scenario) {
        choices = ready = starts = withdrawals = releases = 0;
        owner_continued = 0;
        uint32_t first, second, sibling;
        require(vn2_call_split(&first, &second, &sibling) == VN2_SPLIT_OK, "wrong exit");
        printf("done ok {%u, %u, %u}\n", (unsigned)first, (unsigned)second, (unsigned)sibling);
        require(starts == 3 && withdrawals == expected_withdrawals[scenario], "request count");
        require(releases == withdrawals, "missing release");
        require(!holds[1] && !holds[2] && !holds[3] && !steady && !selected && !awaiting_release,
                "pending request");
    }
    return 0;
}
