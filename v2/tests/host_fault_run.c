#include "module.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned scenario, live, polls, choices, starts, withdrawals, completions;
static struct vn2_wait_send *pending;
static int token;

static void require(int ok, const char *why) {
    if (!ok) {
        fprintf(stderr, "host fault case %u: %s\n", scenario, why);
        exit(1);
    }
}

static void consume(unsigned id) {
    require(id >= 1 && id <= 2 && (live & (1u << id)), "duplicate consumption");
    live &= ~(1u << id);
}

int32_t vn2_ext_acquire(uint32_t id, void **out) {
    require(id >= 1 && id <= 2 && !(live & (1u << id)), "duplicate acquire");
    live |= 1u << id;
    *out = (void *)(uintptr_t)id;
    printf("acquire(%u) -> ok {lease#%u}\n", (unsigned)id, (unsigned)id);
    return VN2_ACQUIRE_OK;
}

int32_t vn2_ext_close(void *lease) {
    require((uintptr_t)lease == 1 && !pending, "normal continuation at wrong time");
    consume(1);
    puts("close(lease#1) -> ok {}");
    return VN2_CLOSE_OK;
}

void vn2_release_lease(void *lease) {
    unsigned id = (unsigned)(uintptr_t)lease;
    require(!pending && ((id == 2 && withdrawals == 1) || (id == 1 && completions == 1)),
            "wrong release or order");
    consume(id);
    printf("lease.release(lease#%u) -> released {}\n", id);
}

void vn2_start_send(struct vn2_wait_send *r) {
    require(!pending && !r->host_state && (uintptr_t)r->in_l == 2 && live == 6,
            "bad bound request");
    const uint32_t *xs = r->in_xs->data;
    require(r->in_xs->len == 2 && xs[0] == 3 && xs[1] == 5 && *r->in_cell == 7, "bad inputs");
    r->host_state = &token;
    pending = r;
    ++starts;
}

uint8_t vn2_should_cancel_root(uint64_t turn) {
    require(turn == 1 && pending && !polls++, "wrong cancellation turn");
    return scenario == 3;
}

uint64_t vn2_pick_waiting(void *const *states, uint64_t count) {
    require(pending && count == 1 && states[0] == &token && !choices++, "wrong host choice");
    return 0;
}

void vn2_withdraw_send(struct vn2_wait_send *r) {
    require(scenario == 3 && r == pending && r->host_state == &token && !choices, "wrong withdrawal");
    pending = NULL;
    ++withdrawals;
}

int32_t vn2_complete_send(struct vn2_wait_send *r) {
    require(r == pending && r->host_state == &token && choices == 1 && !completions, "wrong completion");
    pending = NULL;
    ++completions;
    consume(2);
    free(r->in_xs->data);
    printf("send(lease#2, [3, 5], %u) -> ", (unsigned)*r->in_cell);
    if (scenario == 0) {
        *r->in_cell = 12;
        *r->out_0_ok_0 = 37;
        puts("ok {37}");
        return VN2_SEND_OK;
    }
    if (scenario == 4) {
        *r->in_cell = 13;
        puts("cancelled {}");
        return VN2_SEND_CANCELLED;
    }
    const char *message = scenario == 1 ? "lost" : "peer \"gone\"";
    size_t n = strlen(message);
    char *owned = malloc(n);
    require(owned != NULL, "allocation");
    memcpy(owned, message, n);
    *r->out_fault = (vn2_string){ .data = owned, .len = n, .cap = n };
    if (scenario == 1) *r->in_cell = 12;
    puts(scenario == 1 ? "fault \"lost\"" : "fault \"peer \\\"gone\\\"\"");
    return VN2_FAULT;
}

int32_t vn2_ext_note(const vn2_string *m) {
    require(scenario == 1 && !live && m->len == 4 && !memcmp(m->data, "lost", 4),
            "wrong contingency message or cleanup order");
    puts("note(\"lost\") -> ok {}");
    return VN2_NOTE_OK;
}

int main(void) {
    for (scenario = 0; scenario < 5; ++scenario) {
        starts = polls = choices = completions = withdrawals = 0;
        uint32_t result = 99;
        if (scenario == 2) {
            vn2_string fault;
            require(vn2_call_escape(&result, &fault) == VN2_FAULT && result == 99, "fault selected an alternative");
            require(fault.len == 11 && !memcmp(fault.data, "peer \"gone\"", 11), "escaped fault message");
            free((void *)fault.data);
            puts("faulted \"peer \\\"gone\\\"\"");
        } else {
            require(vn2_call_catch_fault(&result) == VN2_CATCH_FAULT_DONE, "missing result");
            printf("done done {%u}\n", (unsigned)result);
        }
        require(!pending && !live && starts == 1 && polls == 1 &&
                withdrawals == (scenario == 3) && choices == completions && choices + withdrawals == 1,
                "unfinished call");
    }
    return 0;
}
