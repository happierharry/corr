from __future__ import annotations

import ast
import argparse
import json
import logging
import math
import os
import random
import sys
import time
from typing import Any, Dict, List, Tuple, Optional

MAX_GRAPH_SIZE = 700
log = logging.getLogger("cft")


# ----------------------------
# Bitset helpers
# ----------------------------

def popcount(x: int) -> int:
    return x.bit_count()

def iter_bits(mask: int):
    """Yield indices of set bits in mask."""
    while mask:
        lsb = mask & -mask
        yield (lsb.bit_length() - 1)
        mask ^= lsb


# ----------------------------
# Graph construction
# ----------------------------

def build_undirected_adj_bits(n: int, adjlist: List[List[int]]) -> List[int]:
    """Symmetrize adjacency and build bitsets."""
    bits = [0] * n
    for i, neigh in enumerate(adjlist):
        for j in neigh:
            if 0 <= j < n and j != i:
                bits[i] |= 1 << j
                bits[j] |= 1 << i
    return bits

def complement_bits(adj_bits: List[int]) -> Tuple[List[int], int]:
    n = len(adj_bits)
    all_mask = (1 << n) - 1
    comp = [0] * n
    for i in range(n):
        # all except self and original neighbors
        comp[i] = all_mask ^ (1 << i) ^ adj_bits[i]
    return comp, all_mask

def build_edges_and_incidence(comp_bits: List[int]) -> Tuple[List[int], List[int], List[List[int]]]:
    """
    Build undirected edge list (u[e], v[e]) for complement graph and incidence lists inc[v] = edges incident to v.
    """
    n = len(comp_bits)
    edge_u: List[int] = []
    edge_v: List[int] = []
    inc: List[List[int]] = [[] for _ in range(n)]

    for i in range(n):
        # consider neighbors j > i to avoid duplicates
        shifted = comp_bits[i] >> (i + 1)
        base = i + 1
        while shifted:
            lsb = shifted & -shifted
            off = lsb.bit_length() - 1
            j = base + off
            e = len(edge_u)
            edge_u.append(i)
            edge_v.append(j)
            inc[i].append(e)
            inc[j].append(e)
            shifted ^= lsb

    return edge_u, edge_v, inc


# ----------------------------
# Validity checks / reductions
# ----------------------------

def is_independent_in_complement(comp_bits: List[int], subset_mask: int) -> bool:
    """subset_mask is independent set in complement iff no complement-edge inside it."""
    for v in iter_bits(subset_mask):
        if comp_bits[v] & (subset_mask & ~(1 << v)):
            return False
    return True

def reduce_vertex_cover_minimal(comp_bits: List[int], cover_mask: int, fixed_mask: int = 0) -> int:
    """
    Remove redundant vertices from a cover while preserving 'fixed_mask' vertices.
    For vertex cover: v is redundant if all its neighbors are still in the cover.
    """
    changed = True
    while changed:
        changed = False
        removable = cover_mask & ~fixed_mask
        # iterate on a snapshot; we may remove while iterating
        for v in list(iter_bits(removable)):
            if (comp_bits[v] & ~cover_mask) == 0:
                cover_mask &= ~(1 << v)
                changed = True
    return cover_mask


# ----------------------------
# CFT building blocks (vertex-cover specializations)
# ----------------------------

def lagrangian_L_and_xmask(
    u: List[float],
    active_edges: List[int],
    free_mask: int,
    comp_bits: List[int],
    edge_u: List[int],
    edge_v: List[int],
    threshold: float = 1e-3,
    reduced_norm: bool = False,
) -> Tuple[float, List[float], int]:
    """
    Compute L(u), per-vertex lag_cost c_v(u)=1-sum_{e incident} u_e, and an x-mask used for subgradient direction.

    If reduced_norm=True, mimic CFT's "prime partial cover":
      S = {v : c_v(u) <= threshold}, then remove redundant columns from S.
    """
    n = len(comp_bits)
    sum_u = [0.0] * n
    sum_u_total = 0.0

    for e in active_edges:
        ue = u[e]
        sum_u_total += ue
        if ue:
            a = edge_u[e]
            b = edge_v[e]
            sum_u[a] += ue
            sum_u[b] += ue

    lag_cost = [0.0] * n
    L = sum_u_total
    for v in iter_bits(free_mask):
        lc = 1.0 - sum_u[v]
        lag_cost[v] = lc
        if lc < 0.0:
            L += lc  # add min(lc, 0)

    if not reduced_norm:
        x_mask = 0
        for v in iter_bits(free_mask):
            if lag_cost[v] < 0.0:
                x_mask |= 1 << v
        return L, lag_cost, x_mask

    # reduced-norm direction:
    S_mask = 0
    for v in iter_bits(free_mask):
        if lag_cost[v] <= threshold:
            S_mask |= 1 << v

    # redundant in initial S: neighbors_in_free(v) subset S
    redundant = []
    for v in iter_bits(S_mask):
        if (comp_bits[v] & free_mask & ~S_mask) == 0:
            redundant.append(v)
    redundant.sort(key=lambda vv: lag_cost[vv], reverse=True)

    for v in redundant:
        if (S_mask >> v) & 1:
            S_without = S_mask & ~(1 << v)
            if (comp_bits[v] & free_mask & ~S_without) == 0:
                S_mask = S_without

    return L, lag_cost, S_mask


def subgradient_update_in_place(
    u: List[float],
    active_edges: List[int],
    x_mask: int,
    gap: float,
    lam: float,
    edge_u: List[int],
    edge_v: List[int],
) -> Tuple[int, float]:
    """
    Subgradient is s_e = 1 - x_a - x_b.
    For vertex cover rows (edges), s_e != 0 iff endpoints are both selected or both unselected (x_a == x_b).
      s_e = +1 if both unselected, s_e = -1 if both selected.

    Returns (norm_sq, step_t) and updates u in place.
    """
    # norm_sq = sum s_e^2 = count of edges with s_e != 0
    norm_sq = 0
    for e in active_edges:
        a = edge_u[e]
        b = edge_v[e]
        xa = (x_mask >> a) & 1
        xb = (x_mask >> b) & 1
        if xa == xb:
            norm_sq += 1

    if norm_sq == 0 or gap <= 0.0:
        return norm_sq, 0.0

    t = lam * gap / norm_sq
    if t == 0.0:
        return norm_sq, 0.0

    for e in active_edges:
        a = edge_u[e]
        b = edge_v[e]
        xa = (x_mask >> a) & 1
        xb = (x_mask >> b) & 1
        if xa == xb:
            s = 1.0 if xa == 0 else -1.0
            new_val = u[e] + t * s
            if new_val < 0.0:
                new_val = 0.0
            u[e] = new_val

    return norm_sq, t


def greedy_cover_rule_a(
    u: List[float],
    active_edges: List[int],
    fixed_cover_mask: int,
    free_mask: int,
    comp_bits: List[int],
    edge_u: List[int],
    edge_v: List[int],
    inc: List[List[int]],
    rng: random.Random,
) -> Tuple[int, List[int]]:
    """
    CFT GREEDY with rule (a), specialized to vertex cover.

    Returns:
      - cover mask (includes fixed_cover_mask)
      - order of vertices added by greedy (excluding fixed ones)
    """
    n = len(comp_bits)
    selected_mask = fixed_cover_mask

    # Edge active flags for this greedy run:
    active_flag = [False] * len(edge_u)
    for e in active_edges:
        active_flag[e] = True
    remaining = len(active_edges)

    # mu[v] = uncovered incident edge count
    # gamma[v] = 1 - sum_{uncovered incident edges} u_e
    mu = [0] * n
    sum_u = [0.0] * n

    for e in active_edges:
        ue = u[e]
        a = edge_u[e]
        b = edge_v[e]
        mu[a] += 1
        mu[b] += 1
        if ue:
            sum_u[a] += ue
            sum_u[b] += ue

    gamma = [1.0] * n
    for v in iter_bits(free_mask):
        gamma[v] = 1.0 - sum_u[v]

    chosen_order: List[int] = []
    available_mask = free_mask & ~selected_mask

    while remaining > 0:
        best_v = None
        best_score = None
        best_mu = -1

        for v in iter_bits(available_mask):
            mv = mu[v]
            if mv <= 0:
                continue
            gv = gamma[v]
            if gv > 0.0:
                score = gv / mv
            elif gv < 0.0:
                score = gv * mv
            else:
                score = 0.0

            if (best_score is None or score < best_score - 1e-12
                    or (abs(score - best_score) <= 1e-12 and mv > best_mu)):
                best_score = score
                best_v = v
                best_mu = mv

        if best_v is None:
            # fallback: pick an endpoint of any remaining uncovered edge
            for e in active_edges:
                if active_flag[e]:
                    a = edge_u[e]
                    b = edge_v[e]
                    if (available_mask >> a) & 1:
                        best_v = a
                    elif (available_mask >> b) & 1:
                        best_v = b
                    break
            if best_v is None:
                break  # should not happen

        v = best_v
        selected_mask |= 1 << v
        chosen_order.append(v)
        available_mask &= ~(1 << v)

        # cover edges incident to v; update mu/gamma of the other endpoint
        for e in inc[v]:
            if active_flag[e]:
                active_flag[e] = False
                remaining -= 1
                ue = u[e]
                a = edge_u[e]
                b = edge_v[e]
                w = b if a == v else a
                mu[w] -= 1
                gamma[w] += ue  # removing edge subtracts from sum_u[w]

    # Remove redundant vertices (except fixed ones)
    selected_mask = reduce_vertex_cover_minimal(comp_bits, selected_mask, fixed_mask=fixed_cover_mask)
    return selected_mask, chosen_order


def subgradient_phase(
    active_edges: List[int],
    free_mask: int,
    UB_residual: float,
    comp_bits: List[int],
    edge_u: List[int],
    edge_v: List[int],
    rng: random.Random,
    u_start: List[float],
    max_iters: int = 2000,
    min_iters: int = 200,
    lam0: float = 0.1,
    p: int = 20,
    threshold: float = 1e-3,
    stall_window: int = 300,
) -> Tuple[List[float], float]:
    """
    CFT subgradient phase with:
      - adaptive lambda every p iters (based on variation in last p lower bounds)
      - reduced-norm direction via prime partial cover (threshold)
    """
    u = u_start[:]  # working copy
    lam = lam0

    best_lb = -1e100
    best_u = u[:]

    best_lb_hist: List[float] = []
    recent_L: List[float] = []
    iters_run = 0
    stop_reason = "max_iters"

    for it in range(1, max_iters + 1):
        iters_run = it
        L, _, x_mask = lagrangian_L_and_xmask(
            u, active_edges, free_mask, comp_bits, edge_u, edge_v,
            threshold=threshold, reduced_norm=True
        )

        if L > best_lb + 1e-12:
            best_lb = L
            best_u = u[:]

        best_lb_hist.append(best_lb)
        recent_L.append(L)
        if len(recent_L) > p:
            recent_L.pop(0)

        if it % p == 0:
            best_recent = max(recent_L)
            worst_recent = min(recent_L)
            denom = abs(best_recent) if abs(best_recent) > 1e-9 else 1.0
            diff = (best_recent - worst_recent) / denom
            if diff > 0.01:
                lam *= 0.5
            elif diff < 0.001:
                lam *= 1.5

        gap = UB_residual - L
        if gap < 0.0:
            gap = 0.0

        norm_sq, _ = subgradient_update_in_place(u, active_edges, x_mask, gap, lam, edge_u, edge_v)
        if norm_sq == 0:
            stop_reason = "zero_norm"
            break

        if it >= max(min_iters, stall_window):
            prev = best_lb_hist[-stall_window]
            if (best_lb - prev) < 1.0 and (best_lb - prev) / max(1.0, abs(prev)) < 0.001:
                stop_reason = "stall_window"
                break

    if log.isEnabledFor(logging.INFO):
        best_gap = max(0.0, UB_residual - best_lb)
        log.info(
            "subgrad phase done iters=%d best_L=%.6f gap=%.6f final_lam=%.6f stop=%s",
            iters_run, best_lb, best_gap, lam, stop_reason
        )
    return best_u, best_lb


def heuristic_phase(
    active_edges: List[int],
    free_mask: int,
    fixed_cover_mask: int,
    comp_bits: List[int],
    edge_u: List[int],
    edge_v: List[int],
    inc: List[List[int]],
    rng: random.Random,
    u_start: List[float],
    fixed_cost: int,
    heuristic_iters: int = 250,
    lam0: float = 0.1,
    p: int = 20,
) -> Tuple[int, int, List[float], float]:
    """
    CFT heuristic phase:
      - starting from u*, generate a sequence of near-optimal multiplier vectors
      - do subgradient updates WITHOUT reduced-norm trick
      - for each u^k, run GREEDY(rule a) to get a feasible cover and keep the best
    """
    u = u_start[:]
    lam = lam0

    # current-instance UB init (a feasible solution respecting fixed_cover_mask):
    cover0, _ = greedy_cover_rule_a([0.0] * len(edge_u), active_edges, fixed_cover_mask, free_mask,
                                   comp_bits, edge_u, edge_v, inc, rng)
    best_cover = cover0
    best_cost = popcount(best_cover)
    UB_residual = max(0.0, best_cost - fixed_cost)

    best_lb = -1e100
    best_u_lb = u[:]

    recent_L: List[float] = []
    iters_run = 0
    stop_reason = "max_iters"

    for it in range(1, heuristic_iters + 1):
        iters_run = it
        L, _, x_mask = lagrangian_L_and_xmask(
            u, active_edges, free_mask, comp_bits, edge_u, edge_v,
            reduced_norm=False
        )

        if L > best_lb + 1e-12:
            best_lb = L
            best_u_lb = u[:]

        recent_L.append(L)
        if len(recent_L) > p:
            recent_L.pop(0)

        if it % p == 0:
            best_recent = max(recent_L)
            worst_recent = min(recent_L)
            denom = abs(best_recent) if abs(best_recent) > 1e-9 else 1.0
            diff = (best_recent - worst_recent) / denom
            if diff > 0.01:
                lam *= 0.5
            elif diff < 0.001:
                lam *= 1.5

        cover, _ = greedy_cover_rule_a(u, active_edges, fixed_cover_mask, free_mask,
                                      comp_bits, edge_u, edge_v, inc, rng)
        cost = popcount(cover)
        if cost < best_cost:
            best_cost = cost
            best_cover = cover
            UB_residual = max(0.0, best_cost - fixed_cost)

        gap = UB_residual - L
        if gap < 0.0:
            gap = 0.0

        norm_sq, _ = subgradient_update_in_place(u, active_edges, x_mask, gap, lam, edge_u, edge_v)
        if norm_sq == 0:
            stop_reason = "zero_norm"
            break

    if log.isEnabledFor(logging.INFO):
        best_gap = max(0.0, UB_residual - best_lb)
        log.info(
            "heur phase done iters=%d best_L=%.6f best_cost=%d gap=%.6f final_lam=%.6f stop=%s",
            iters_run, best_lb, best_cost, best_gap, lam, stop_reason
        )
    return best_cover, best_cost, best_u_lb, best_lb


def column_fixing(
    active_edges: List[int],
    free_mask: int,
    fixed_cover_mask: int,
    comp_bits: List[int],
    edge_u: List[int],
    edge_v: List[int],
    inc: List[List[int]],
    rng: random.Random,
    u_best_lb: List[float],
    threshold: float = 1e-3,
    fix_frac_cap: float = 0.05,
    fix_abs_cap: Optional[int] = None
) -> Tuple[List[int], int, int, int]:
    """
    CFT column fixing specialized to vertex cover.

    Q = {v : c_v(u*) < threshold}
    1) Fix v in Q if some edge has exactly one endpoint in Q.
    2) Run GREEDY(u*) and fix first max(floor(m/200), 1) chosen vertices.

    Returns: (new_active_edges, new_free_mask, new_fixed_cover_mask, newly_fixed_mask)
    """
    _, lag_cost, _ = lagrangian_L_and_xmask(
        u_best_lb, active_edges, free_mask, comp_bits, edge_u, edge_v,
        threshold=threshold, reduced_norm=False
    )

    Q_mask = 0
    for v in iter_bits(free_mask):
        if lag_cost[v] < threshold:
            Q_mask |= 1 << v

    newly_fixed = 0

    # unique-in-Q edges
    for e in active_edges:
        a = edge_u[e]
        b = edge_v[e]
        inQa = (Q_mask >> a) & 1
        inQb = (Q_mask >> b) & 1
        if inQa ^ inQb:
            newly_fixed |= (1 << a) if inQa else (1 << b)

    # apply greedy after those immediate fixings
    temp_fixed = fixed_cover_mask | newly_fixed
    temp_free = free_mask & ~newly_fixed
    temp_active = [e for e in active_edges
                   if ((temp_free >> edge_u[e]) & 1) and ((temp_free >> edge_v[e]) & 1)]

    _, order = greedy_cover_rule_a(u_best_lb, temp_active, temp_fixed, temp_free,
                                  comp_bits, edge_u, edge_v, inc, rng)

    m = len(temp_active)
    k_raw = max(m // 200, 1)
    free_cnt = popcount(temp_free)                 # remaining vertices after initial fixings
    k_cap = max(1, int(math.ceil(fix_frac_cap * free_cnt)))                 # cap at ~5% of remaining vertices
    if fix_abs_cap is not None:
        k_cap = min(k_cap, fix_abs_cap)
    k = min(k_raw, k_cap, len(order))              # also cap by actual greedy lengthk = min(k_raw, k_cap, len(order))              # also cap by actual greedy length

    for v in order[:k]:
        newly_fixed |= 1 << v

    fixed_cover_mask |= newly_fixed
    free_mask &= ~newly_fixed

    new_active = [e for e in active_edges
                  if ((free_mask >> edge_u[e]) & 1) and ((free_mask >> edge_v[e]) & 1)]

    return new_active, free_mask, fixed_cover_mask, newly_fixed


# ----------------------------
# 3-PHASE (CFT core) for vertex cover
# ----------------------------

def three_phase_vertex_cover(
    comp_bits: List[int],
    edge_u: List[int],
    edge_v: List[int],
    inc: List[List[int]],
    rng: random.Random,
    base_fixed_mask: int = 0,
    incumbent_cover: Optional[int] = None,
    subgrad_max_iters: int = 2000,
    subgrad_min_iters: int = 200,
    heuristic_iters: int = 250,
    max_loops: int = 50,
    threshold: float = 1e-3,
) -> Tuple[int, int, Optional[List[float]], Optional[float]]:
    """
    CFT procedure 3-PHASE specialized to vertex cover.
    Returns:
      best_cover_mask, best_cost,
      (u_star_for_base_instance, L(u_star_for_base_instance)) for loop==1
    """
    n = len(comp_bits)
    all_mask = (1 << n) - 1
    m_total = len(edge_u)

    base_fixed_mask &= all_mask
    fixed_cover_mask = base_fixed_mask
    free_mask = all_mask & ~fixed_cover_mask

    active_edges = [e for e in range(m_total)
                    if ((free_mask >> edge_u[e]) & 1) and ((free_mask >> edge_v[e]) & 1)]

    if incumbent_cover is not None:
        best_cover = (incumbent_cover | base_fixed_mask)
    else:
        best_cover, _ = greedy_cover_rule_a([0.0] * m_total, active_edges, fixed_cover_mask, free_mask,
                                            comp_bits, edge_u, edge_v, inc, rng)
        best_cover |= base_fixed_mask

    best_cover = reduce_vertex_cover_minimal(comp_bits, best_cover, fixed_mask=base_fixed_mask) | base_fixed_mask
    best_cost = popcount(best_cover)

    base_best_u: Optional[List[float]] = None
    base_best_lb: Optional[float] = None

    prev_u_for_start: Optional[List[float]] = None

    for loop in range(1, max_loops + 1):
        if not active_edges:
            break

        fixed_cost = popcount(fixed_cover_mask)

        # UB for this *restricted* instance:
        ub_cover, _ = greedy_cover_rule_a([0.0] * m_total, active_edges, fixed_cover_mask, free_mask,
                                          comp_bits, edge_u, edge_v, inc, rng)
        ub_cost = popcount(ub_cover)
        UB_residual = max(0.0, ub_cost - fixed_cost)
        if log.isEnabledFor(logging.INFO):
            log.info(
                "3phase loop=%d active_edges=%d fixed=%d free=%d ub_cost=%d best_cost=%d",
                loop, len(active_edges), fixed_cost, popcount(free_mask), ub_cost, best_cost
            )

        # u0 init:
        if prev_u_for_start is None:
            deg = [0] * n
            for e in active_edges:
                deg[edge_u[e]] += 1
                deg[edge_v[e]] += 1
            u_start = [0.0] * m_total
            for e in active_edges:
                a = edge_u[e]
                b = edge_v[e]
                u_start[e] = min(1.0 / deg[a], 1.0 / deg[b])
        else:
            u_start = prev_u_for_start[:]
            for e in active_edges:
                base = prev_u_for_start[e]
                u_start[e] = base * (1.0 + rng.uniform(-0.1, 0.1)) if base != 0.0 else 0.0

        # subgradient phase
        u_sub_best, lb_sub = subgradient_phase(
            active_edges, free_mask, UB_residual, comp_bits, edge_u, edge_v, rng,
            u_start=u_start, max_iters=subgrad_max_iters, min_iters=subgrad_min_iters,
            threshold=threshold
        )

        # heuristic phase
        cover_cur, cost_cur, u_best_lb, lb_best = heuristic_phase(
            active_edges, free_mask, fixed_cover_mask, comp_bits, edge_u, edge_v, inc, rng,
            u_start=u_sub_best, fixed_cost=fixed_cost, heuristic_iters=heuristic_iters
        )
        if log.isEnabledFor(logging.INFO):
            loop_gap = max(0.0, best_cost - (fixed_cost + lb_best))
            log.info(
                "3phase loop=%d done lb_sub=%.6f lb_best=%.6f cost_cur=%d best_cost=%d gap=%.6f",
                loop, lb_sub, lb_best, cost_cur, best_cost, loop_gap
            )

        if loop == 1:
            # best lower bound for the base instance before internal column fixing
            if lb_best >= lb_sub:
                base_best_u = u_best_lb[:]
                base_best_lb = lb_best
            else:
                base_best_u = u_sub_best[:]
                base_best_lb = lb_sub

        if cost_cur < best_cost:
            best_cost = cost_cur
            best_cover = cover_cur
            if log.isEnabledFor(logging.INFO):
                log.info("3phase improve loop=%d new_best_cost=%d", loop, best_cost)

        # warm start for next cycle
        prev_u_for_start = u_best_lb[:]

        # termination: fixed_cost + LB(residual) >= best_cost
        if fixed_cost + lb_best >= best_cost - 1e-9:
            if log.isEnabledFor(logging.INFO):
                log.info(
                    "3phase stop loop=%d: bound met (fixed+lb=%.6f >= best=%d)",
                    loop, fixed_cost + lb_best, best_cost
                )
            break

        # column fixing & reduction
        active_edges, free_mask, fixed_cover_mask, newly_fixed = column_fixing(
            active_edges, free_mask, fixed_cover_mask, comp_bits, edge_u, edge_v, inc, rng,
            u_best_lb=u_best_lb, threshold=threshold
        )
        if log.isEnabledFor(logging.INFO):
            log.info(
                "3phase loop=%d column_fixing newly_fixed=%d active_now=%d fixed_now=%d",
                loop, popcount(newly_fixed), len(active_edges), popcount(fixed_cover_mask)
            )

        if popcount(fixed_cover_mask) >= best_cost:
            if log.isEnabledFor(logging.INFO):
                log.info(
                    "3phase stop loop=%d: fixed vertices reached best cost (%d)",
                    loop, best_cost
                )
            break

    return best_cover, best_cost, base_best_u, base_best_lb


# ----------------------------
# Refining (CFT outer loop) specialized to vertex cover
# ----------------------------

def compute_delta_for_cover(
    cover_mask: int,
    u_star: List[float],
    edge_u: List[int],
    edge_v: List[int],
) -> List[Tuple[int, float]]:
    """
    CFT refining delta_j specialized to vertex cover.
    For an edge e=(a,b), |S∩J_e| is 1 or 2.
    If both endpoints selected, each gets u_e/2 contribution.

    delta_v = max(c_v(u), 0) + sum_{e incident to v and both endpoints in cover} u_e/2
    """
    n = max(max(edge_u, default=-1), max(edge_v, default=-1)) + 1
    m_total = len(edge_u)

    sum_u = [0.0] * n
    for e in range(m_total):
        ue = u_star[e]
        if ue:
            a = edge_u[e]
            b = edge_v[e]
            sum_u[a] += ue
            sum_u[b] += ue

    lag_cost = [1.0 - sum_u[v] for v in range(n)]

    overlap = [0.0] * n
    for e in range(m_total):
        ue = u_star[e]
        if ue:
            a = edge_u[e]
            b = edge_v[e]
            if ((cover_mask >> a) & 1) and ((cover_mask >> b) & 1):
                half = 0.5 * ue
                overlap[a] += half
                overlap[b] += half

    out = []
    for v in iter_bits(cover_mask):
        out.append((v, (lag_cost[v] if lag_cost[v] > 0.0 else 0.0) + overlap[v]))
    out.sort(key=lambda t: t[1])
    return out


def refine_fixed_set(
    cover_mask: int,
    u_star: List[float],
    inc: List[List[int]],
    m_total: int,
    pi: float,
) -> int:
    """
    Pick smallest-delta vertices until they cover at least pi fraction of edges.
    """
    ranked = compute_delta_for_cover(cover_mask, u_star, edge_u_global, edge_v_global)  # uses globals set below
    target = int(math.ceil(pi * m_total))
    covered = [False] * m_total
    covered_count = 0
    F_mask = 0

    for v, _d in ranked:
        F_mask |= 1 << v
        for e in inc[v]:
            if not covered[e]:
                covered[e] = True
                covered_count += 1
        if covered_count >= target:
            break

    return F_mask


# We'll set these globals once inside maximum_clique_cft so refine_fixed_set can stay simple.
edge_u_global: List[int] = []
edge_v_global: List[int] = []


# ----------------------------
# Final: maximum clique via CFT vertex-cover heuristic
# ----------------------------

def maximum_clique_cft(
    n: int,
    adjlist: List[List[int]],
    *,
    seed: int = 0,
    enable_refine: bool = True,
    max_refine_iters: int = 8,
    pi_min: float = 0.3,
    alpha: float = 1.1,
    phi: float = 1.0,
    subgrad_max_iters: int = 2000,
    heuristic_iters: int = 250,
) -> List[int]:
    rng = random.Random(seed)
    if log.isEnabledFor(logging.INFO):
        log.info(
            "cft start n=%d seed=%d subgrad_max_iters=%d heuristic_iters=%d enable_refine=%s",
            n, seed, subgrad_max_iters, heuristic_iters, enable_refine
        )

    adj_bits = build_undirected_adj_bits(n, adjlist)
    comp_bits, all_mask = complement_bits(adj_bits)

    edge_u, edge_v, inc = build_edges_and_incidence(comp_bits)
    m_total = len(edge_u)

    if m_total == 0:
        return list(range(n))  # already complete graph

    # expose for refine_fixed_set
    global edge_u_global, edge_v_global
    edge_u_global = edge_u
    edge_v_global = edge_v

    # initial greedy cover
    init_cover, _ = greedy_cover_rule_a([0.0] * m_total, list(range(m_total)), 0, all_mask,
                                        comp_bits, edge_u, edge_v, inc, rng)
    init_cover = reduce_vertex_cover_minimal(comp_bits, init_cover)
    best_cover = init_cover
    best_cost = popcount(best_cover)

    # main 3-PHASE on original
    cover, cost, u_star, lb_star = three_phase_vertex_cover(
        comp_bits, edge_u, edge_v, inc, rng,
        base_fixed_mask=0,
        incumbent_cover=best_cover,
        subgrad_max_iters=subgrad_max_iters,
        heuristic_iters=heuristic_iters,
    )
    if cost < best_cost:
        best_cover, best_cost = cover, cost
    if log.isEnabledFor(logging.INFO):
        log.info(
            "cft base_3phase done cover_cost=%d best_cover_cost=%d lb_star=%s",
            cost, best_cost, "None" if lb_star is None else f"{lb_star:.6f}"
        )

    if u_star is None:
        u_star = [0.0] * m_total
        lb_star = 0.0

    # optional refining loop
    if enable_refine:
        pi = pi_min
        for refine_it in range(1, max_refine_iters + 1):
            if lb_star is not None and best_cost <= phi * lb_star + 1e-9:
                if log.isEnabledFor(logging.INFO):
                    log.info(
                        "refine stop iter=%d: best_cost=%d <= phi*lb_star=%.6f",
                        refine_it, best_cost, phi * lb_star
                    )
                break

            F_mask = refine_fixed_set(best_cover, u_star, inc, m_total, pi)
            if F_mask == 0:
                if log.isEnabledFor(logging.INFO):
                    log.info("refine stop iter=%d: empty fixed set", refine_it)
                break
            F_mask &= best_cover  # must be subset of current cover
            if log.isEnabledFor(logging.INFO):
                log.info(
                    "refine iter=%d pi=%.4f fixed_subset=%d best_cost=%d",
                    refine_it, pi, popcount(F_mask), best_cost
                )

            cover2, cost2, _, _ = three_phase_vertex_cover(
                comp_bits, edge_u, edge_v, inc, rng,
                base_fixed_mask=F_mask,
                incumbent_cover=best_cover,
                subgrad_max_iters=subgrad_max_iters,
                heuristic_iters=heuristic_iters,
            )

            if cost2 < best_cost:
                best_cover, best_cost = cover2, cost2
                pi = pi_min
                if log.isEnabledFor(logging.INFO):
                    log.info(
                        "refine improve iter=%d new_best_cost=%d reset_pi=%.4f",
                        refine_it, best_cost, pi
                    )
            else:
                pi = min(1.0, alpha * pi)
                if log.isEnabledFor(logging.INFO):
                    log.info(
                        "refine no_improve iter=%d keep_best=%d next_pi=%.4f",
                        refine_it, best_cost, pi
                    )

    # clique = complement of cover
    clique_mask = all_mask & ~best_cover

    # safety: ensure it's an independent set in complement (so a clique in original)
    if not is_independent_in_complement(comp_bits, clique_mask):
        # repair to a maximal independent subset (should almost never trigger if cover is valid)
        cand = clique_mask
        indep = 0
        while cand:
            lsb = cand & -cand
            v = lsb.bit_length() - 1
            indep |= lsb
            cand &= ~(lsb | comp_bits[v])
        clique_mask = indep

    if log.isEnabledFor(logging.INFO):
        log.info("cft done clique_size=%d", popcount(clique_mask))
    return [v for v in range(n) if (clique_mask >> v) & 1]


# ----------------------------
# Compatibility / CLI interface (matching ../cns/cns.py)
# ----------------------------

def _symmetrize_adj(n: int, adj: List[List[int]]) -> List[List[int]]:
    """Make adjacency undirected, remove self-loops, duplicates, and out-of-range entries."""
    nbrs = [set() for _ in range(n)]
    for u in range(n):
        for v in adj[u]:
            if not isinstance(v, int):
                continue
            if v < 0 or v >= n or v == u:
                continue
            nbrs[u].add(v)
            nbrs[v].add(u)
    return [sorted(list(s)) for s in nbrs]


def maximum_clique_via_cft(
    n: int,
    adj: List[List[int]],
    *,
    max_iters: int = 10000,
    stall_iter: int = 30,
    restarts: int = 1,
    seed: int = 0,
    use_eps_costs: bool = True,
) -> Tuple[List[int], Dict[str, Any]]:
    """
    Beasley-compatible CFT wrapper.

    Matches the argument surface of ../cns/cns.py's maximum_clique_via_beasley
    for easy drop-in usage.
    """
    if n > MAX_GRAPH_SIZE:
        raise ValueError(f"Graph size {n} exceeds maximum {MAX_GRAPH_SIZE}")
    if len(adj) != n:
        raise ValueError("Adjacency list length must equal n")

    # Keep behavior consistent with CNS/Beasley wrappers.
    adj = _symmetrize_adj(n, adj)

    # Kept for signature compatibility with Beasley-style callers.
    # CFT does not use epsilon costs.
    _ = use_eps_costs

    effective_restarts = max(1, int(restarts))
    effective_max_iters = max(100, int(max_iters))
    effective_stall_iter = max(10, int(stall_iter))
    subgrad_max_iters = max(100, effective_max_iters // effective_restarts)
    heuristic_iters = max(50, min(1000, effective_stall_iter * 8))

    t0 = time.perf_counter()
    best_clique: List[int] = []

    for r in range(effective_restarts):
        run_seed = seed + r
        if log.isEnabledFor(logging.INFO):
            log.info("restart %d/%d seed=%d", r + 1, effective_restarts, run_seed)
        clique = maximum_clique_cft(
            n,
            adj,
            seed=run_seed,
            subgrad_max_iters=subgrad_max_iters,
            heuristic_iters=heuristic_iters,
        )
        if len(clique) > len(best_clique):
            best_clique = clique
            if log.isEnabledFor(logging.INFO):
                log.info("restart %d improved best_clique=%d", r + 1, len(best_clique))
        elif log.isEnabledFor(logging.INFO):
            log.info("restart %d done clique=%d best=%d", r + 1, len(clique), len(best_clique))

    elapsed = time.perf_counter() - t0
    if log.isEnabledFor(logging.INFO):
        log.info("all restarts done best_clique=%d elapsed=%.3fs", len(best_clique), elapsed)

    # Complement edge count for diagnostics parity.
    adj_bits = build_undirected_adj_bits(n, adj)
    comp_bits, _ = complement_bits(adj_bits)
    edge_u, _, _ = build_edges_and_incidence(comp_bits)

    return best_clique, {
        "clique_size": len(best_clique),
        "proved_optimal": False,
        "vertex_cover_size": n - len(best_clique),
        "iterations": None,
        "best_upper": None,
        "best_lower": None,
        "restarts": effective_restarts,
        "restart_used": None,
        "complement_edges": len(edge_u),
        "elapsed_seconds": elapsed,
    }


def maximum_clique_cns(
    n: int,
    adj: List[List[int]],
    *,
    max_iters: int = 10000,
    stall_iter: int = 30,
    restarts: int = 1,
    seed: int = 0,
    use_eps_costs: bool = True,
) -> Tuple[List[int], Dict[str, Any]]:
    """Compatibility alias matching cns.py naming."""
    return maximum_clique_via_cft(
        n,
        adj,
        max_iters=max_iters,
        stall_iter=stall_iter,
        restarts=restarts,
        seed=seed,
        use_eps_costs=use_eps_costs,
    )


def maximum_clique_via_beasley(
    n: int,
    adj: List[List[int]],
    *,
    max_iters: int = 10000,
    stall_iter: int = 30,
    restarts: int = 1,
    seed: int = 0,
    use_eps_costs: bool = True,
) -> Tuple[List[int], Dict[str, Any]]:
    """Compatibility alias for callers using the Beasley function name."""
    return maximum_clique_via_cft(
        n,
        adj,
        max_iters=max_iters,
        stall_iter=stall_iter,
        restarts=restarts,
        seed=seed,
        use_eps_costs=use_eps_costs,
    )


def load_pro_file(path: str) -> Tuple[int, List[List[int]]]:
    """
    Load graph from a .pro file.
    Format: first line = n (vertex count), next n lines = comma-separated neighbor lists.
    Vertices are 0-based. Raises ValueError if n > MAX_GRAPH_SIZE.
    """
    with open(path, "r") as f:
        lines = [line.strip() for line in f if line.strip()]
    if not lines:
        raise ValueError(f"Empty file: {path}")
    n = int(lines[0])
    if n > MAX_GRAPH_SIZE:
        raise ValueError(f"Graph size {n} exceeds maximum {MAX_GRAPH_SIZE}")
    if len(lines) != n + 1:
        raise ValueError(f"Expected {n + 1} lines (n + adjacency), got {len(lines)}")
    adj: List[List[int]] = []
    for i in range(1, n + 1):
        part = lines[i].strip()
        if not part:
            adj.append([])
        else:
            adj.append([int(x) for x in part.split(",")])
    return n, adj


def format_sol(clique: List[int], elapsed: float) -> str:
    """
    Solution file format:
    Line 1: M <space-separated 0-based node indices>
    Line 2: c Elapsed Time: <elapsed_seconds>
    """
    indices = " ".join(str(v) for v in clique)
    return f"M {indices}\nc Elapsed Time: {elapsed}\n"


def configure_logging(verbose: bool) -> None:
    """Enable INFO logging to stdout when verbose=True."""
    log.setLevel(logging.INFO if verbose else logging.WARNING)
    if verbose and not log.handlers:
        h = logging.StreamHandler(sys.stdout)
        h.setFormatter(logging.Formatter("%(message)s"))
        log.addHandler(h)


def solve_file(
    path: str,
    *,
    restarts: int = 5,
    seed: int = 0,
    stall_iter: int = 30,
) -> Tuple[List[int], float]:
    """Solve one .pro file; returns (clique, elapsed_seconds)."""
    log.info(">>> %s", path)
    n, adj = load_pro_file(path)
    t0 = time.perf_counter()
    clique, _ = maximum_clique_via_cft(
        n,
        adj,
        restarts=restarts,
        seed=seed,
        stall_iter=stall_iter,
    )
    elapsed = time.perf_counter() - t0
    return clique, elapsed


def solve_stdin(
    *,
    restarts: int = 5,
    seed: int = 0,
    stall_iter: int = 30,
) -> None:
    """
    Reads from stdin:
      n <whitespace> adjacency_list

    adjacency_list: Python/JSON list-of-lists of length n, 0-based.
    Prints solution (M line + elapsed time).
    """
    data = sys.stdin.read().strip()
    if not data:
        return

    first, *rest = data.split(None, 1)
    n = int(first)
    if n > MAX_GRAPH_SIZE:
        raise ValueError(f"Graph size {n} exceeds maximum {MAX_GRAPH_SIZE}")
    if not rest:
        adj = [[] for _ in range(n)]
    else:
        tail = rest[0].strip()
        try:
            adj = json.loads(tail)
        except Exception:
            adj = ast.literal_eval(tail)

    t0 = time.perf_counter()
    clique, _ = maximum_clique_via_cft(
        n,
        adj,
        restarts=restarts,
        seed=seed,
        stall_iter=stall_iter,
    )
    elapsed = time.perf_counter() - t0
    print(format_sol(clique, elapsed), end="")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Maximum clique via CFT heuristic (vertex cover on complement)."
    )
    parser.add_argument(
        "files",
        nargs="*",
        metavar="FILE.pro",
        help=".pro graph files. If none, read from stdin (unless -i/--input-dir).",
    )
    parser.add_argument(
        "-i", "--input-dir",
        metavar="DIR",
        help="Input directory: process all .pro files.",
    )
    parser.add_argument(
        "-o", "--output",
        metavar="FILE",
        help="Output file path (single file mode). Requires exactly one input file.",
    )
    parser.add_argument(
        "-O", "--output-dir",
        metavar="DIR",
        help="Output directory (batch mode). Use with -i/--input-dir. Writes <basename>.res.",
    )
    parser.add_argument(
        "--restarts",
        type=int,
        default=5,
        metavar="N",
        help="Number of restarts (default: 5).",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=0,
        metavar="S",
        help="Random seed (default: 0).",
    )
    parser.add_argument(
        "--stall-iter",
        type=int,
        default=30,
        metavar="N",
        help="Control parameter for CFT follow-up inner iterations (default: 30).",
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Log intermediate process to stdout.",
    )
    args = parser.parse_args()

    configure_logging(args.verbose)

    # Batch mode: -i and -O
    if args.input_dir is not None and args.output_dir is not None:
        if args.files:
            print("Error: -i/--input-dir with -O/--output-dir cannot be used with file arguments.", file=sys.stderr)
            sys.exit(1)
        if args.output is not None:
            print("Error: -o/--output cannot be used with batch mode (-i -O).", file=sys.stderr)
            sys.exit(1)
        os.makedirs(args.output_dir, exist_ok=True)
        pro_files = sorted(
            f for f in os.listdir(args.input_dir)
            if f.endswith(".pro")
        )
        for fname in pro_files:
            in_path = os.path.join(args.input_dir, fname)
            base = os.path.splitext(fname)[0]
            out_path = os.path.join(args.output_dir, base + ".res")
            try:
                clique, elapsed = solve_file(
                    in_path,
                    restarts=args.restarts,
                    seed=args.seed,
                    stall_iter=args.stall_iter,
                )
                with open(out_path, "w") as f:
                    f.write(format_sol(clique, elapsed))
            except (ValueError, OSError) as e:
                print(f"Error processing {in_path}: {e}", file=sys.stderr)
                sys.exit(1)
        return

    # Single/output file mode: -o with one input file
    if args.output is not None:
        if not args.files:
            print("Error: -o/--output requires an input file.", file=sys.stderr)
            sys.exit(1)
        if len(args.files) > 1:
            print("Error: -o/--output requires exactly one input file.", file=sys.stderr)
            sys.exit(1)
        try:
            clique, elapsed = solve_file(
                args.files[0],
                restarts=args.restarts,
                seed=args.seed,
                stall_iter=args.stall_iter,
            )
            with open(args.output, "w") as f:
                f.write(format_sol(clique, elapsed))
        except (ValueError, OSError) as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)
        return

    # Default: print to stdout
    if args.files:
        for i, path in enumerate(args.files):
            try:
                clique, elapsed = solve_file(
                    path,
                    restarts=args.restarts,
                    seed=args.seed,
                    stall_iter=args.stall_iter,
                )
                if i > 0:
                    print()
                print(format_sol(clique, elapsed), end="")
            except (ValueError, OSError) as e:
                print(f"Error processing {path}: {e}", file=sys.stderr)
                sys.exit(1)
    else:
        try:
            solve_stdin(
                restarts=args.restarts,
                seed=args.seed,
                stall_iter=args.stall_iter,
            )
        except (ValueError, OSError) as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)

if __name__ == "__main__":
    main()
