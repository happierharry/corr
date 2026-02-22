#!/usr/bin/env python3
"""
Alpha-scaled CNS variant.

Modification:
  - On each greedy step, compute a robust reduced-cost scale on the current
    free-vertex subproblem:
        s = median(abs(red_cost[v]) for free v)
    and use:
        alpha_scale = 1 / max(s, eps)
        alpha_eff = base_alpha * alpha_scale, with base_alpha in {4, 8, 12}.

All other behavior is inherited from cns.py.
"""

from statistics import median
import logging
import random
import time

import cns as _base


def _maximum_clique_cns_core(
    n,
    adjacency,
    *,
    restarts=6,
    seed=0,
    batch_size=8,
    pd_first_iters=60,
    pd_next_iters=5,
):
    """
    CNS-guided maximum clique heuristic with robust per-step alpha scaling:
      alpha_eff = base_alpha * (1 / max(median(|red_cost| over free vertices), eps))
      where base_alpha cycles in {12, 4, 8, 12, ...}.
    """
    if n <= 0:
        return []
    if len(adjacency) != n:
        raise ValueError("Adjacency list length must equal n")

    adj_bits = _base._build_bit_adjacency(n, adjacency)
    comp_bits = _base._complement_bits(n, adj_bits)
    all_mask = (1 << n) - 1

    edge_u, edge_v, inc = _base._build_edges_from_bits(n, comp_bits)
    m = len(edge_u)
    if m == 0:
        return list(range(n))

    rng = random.Random(seed)

    pd_first = _base.PDParams(rho=1.2, fmin=0.002, Delta=0.01, f0=4.0, beta=15, max_iters=pd_first_iters)
    pd_next = _base.PDParams(rho=2.0, fmin=0.02, Delta=0.1, f0=2.0, beta=5, max_iters=pd_next_iters)

    best_clique_mask = 0
    best_clique_size = -1

    t0 = time.perf_counter()
    if _base.log.isEnabledFor(logging.INFO):
        _base.log.info("CNS(alpha-scale) start: n=%d complement_edges=%d restarts=%d", n, m, restarts)

    scale_eps = 1e-12

    for r in range(restarts):
        # Keep the original restart schedule, but treat it as base alpha.
        if r == 0:
            base_alpha = 12.0
            randomized = False
        else:
            base_alpha = [4.0, 8.0, 12.0][(r - 1) % 3]
            randomized = True

        in_cover = 0
        forbidden = 0
        active_edges = list(range(m))
        pos = list(range(m))
        deg_active = [len(inc[v]) for v in range(n)]
        lam = [0.0] * m
        mu = [0.0] * n
        feasible = True
        step = 0

        def remove_edge(e):
            pe = pos[e]
            if pe == -1:
                return
            u = edge_u[e]
            v = edge_v[e]
            deg_active[u] -= 1
            deg_active[v] -= 1

            last = active_edges[-1]
            active_edges[pe] = last
            pos[last] = pe
            active_edges.pop()
            pos[e] = -1

        def add_to_cover(v):
            nonlocal in_cover, forbidden
            if (in_cover >> v) & 1:
                return
            if (forbidden >> v) & 1:
                forbidden &= ~(1 << v)
            in_cover |= 1 << v
            for e in inc[v]:
                if pos[e] != -1:
                    remove_edge(e)

        def propagate_forbidden(queue):
            nonlocal feasible
            while queue and feasible:
                v = queue.pop()
                for e in inc[v]:
                    if pos[e] == -1:
                        continue
                    u = edge_u[e]
                    w = edge_v[e]
                    other = w if u == v else u
                    if (forbidden >> other) & 1:
                        feasible = False
                        return
                    add_to_cover(other)

        if _base.log.isEnabledFor(logging.INFO):
            _base.log.info(
                "restart %d/%d: base_alpha=%.1f randomized=%s",
                r + 1,
                restarts,
                base_alpha,
                randomized,
            )

        while active_edges and feasible:
            free_mask = all_mask & ~(in_cover | forbidden)
            tmp = free_mask
            while tmp:
                lsb = tmp & -tmp
                v = lsb.bit_length() - 1
                tmp ^= lsb
                if deg_active[v] == 0:
                    forbidden |= 1 << v

            if not active_edges:
                break

            free_mask = all_mask & ~(in_cover | forbidden)
            if free_mask == 0:
                feasible = False
                break

            free_vertices = [v for v in range(n) if (free_mask >> v) & 1]

            params = pd_first if step == 0 else pd_next
            zLB, red_cost = _base._primal_dual_lagrangian_vc(
                active_edges, free_vertices, edge_u, edge_v, lam, mu, params
            )

            indep_mask = _base._completion_independent_set(comp_bits, free_mask, forbidden)
            indep_size = indep_mask.bit_count()
            if indep_size > best_clique_size:
                best_clique_size = indep_size
                best_clique_mask = indep_mask
                if _base.log.isEnabledFor(logging.INFO):
                    _base.log.info(
                        "  improved incumbent: clique_size=%d elapsed=%.3fs",
                        best_clique_size,
                        time.perf_counter() - t0,
                    )

            UB_total = n - indep_size
            LB_total = in_cover.bit_count() + zLB
            gap = UB_total - LB_total
            if gap < 0.0:
                gap = 0.0

            fix_zero_mask = 0
            if gap <= 2.0:
                for v in free_vertices:
                    if red_cost[v] > gap + 1e-9:
                        fix_zero_mask |= 1 << v

            # Robust per-step scaling from reduced costs in the current subproblem.
            s = median(abs(red_cost[v]) for v in free_vertices)
            alpha_scale = 1.0 / max(s, scale_eps)
            alpha_eff = base_alpha * alpha_scale

            cand = []
            for v in free_vertices:
                if (fix_zero_mask >> v) & 1:
                    continue
                cand.append((mu[v] - alpha_eff * red_cost[v], v))

            if not cand:
                v = max(free_vertices, key=lambda x: deg_active[x])
                cand = [(0.0, v)]

            cand.sort(reverse=True)
            k = max(1, int(batch_size))
            k = min(k, len(cand))
            chosen = [cand[i][1] for i in range(k)]

            if randomized and len(chosen) >= 2 and rng.random() < 0.5:
                chosen[0], chosen[1] = chosen[1], chosen[0]

            fix_one_mask = 0
            for v in chosen:
                fix_one_mask |= 1 << v

            for v in free_vertices:
                if (fix_zero_mask >> v) & 1:
                    continue
                if mu[v] >= 0.99 and red_cost[v] <= 0.01:
                    fix_one_mask |= 1 << v

            fix_zero_mask &= ~fix_one_mask

            newly_forbidden = []
            tmp = fix_zero_mask
            while tmp:
                lsb = tmp & -tmp
                v = lsb.bit_length() - 1
                tmp ^= lsb
                if not ((forbidden >> v) & 1) and not ((in_cover >> v) & 1):
                    forbidden |= 1 << v
                    newly_forbidden.append(v)

            tmp = fix_one_mask
            while tmp:
                lsb = tmp & -tmp
                v = lsb.bit_length() - 1
                tmp ^= lsb
                add_to_cover(v)

            if newly_forbidden:
                propagate_forbidden(newly_forbidden)

            if _base.log.isEnabledFor(logging.INFO):
                _base.log.info(
                    "  iter restart=%d step=%d uncovered=%d free=%d cover=%d forbidden=%d zLB=%.4f gap=%.4f s=%.4e alpha_scale=%.4e alpha_eff=%.4e best=%d elapsed=%.3fs",
                    r + 1,
                    step + 1,
                    len(active_edges),
                    len(free_vertices),
                    in_cover.bit_count(),
                    forbidden.bit_count(),
                    zLB,
                    gap,
                    s,
                    alpha_scale,
                    alpha_eff,
                    best_clique_size,
                    time.perf_counter() - t0,
                )

            step += 1
            if step > 2 * n:
                feasible = False
                if _base.log.isEnabledFor(logging.INFO):
                    _base.log.info("  stop restart=%d: safety bound reached (step>%d)", r + 1, 2 * n)
                break

        if feasible:
            free_mask = all_mask & ~(in_cover | forbidden)
            indep_mask = _base._completion_independent_set(comp_bits, free_mask, forbidden)
            if _base._is_independent(comp_bits, indep_mask):
                cover_mask = all_mask & ~indep_mask
                cover_mask = _base._reduce_cover_by_redundancy(comp_bits, cover_mask)
                clique_mask = all_mask & ~cover_mask
                if _base._is_independent(comp_bits, clique_mask):
                    clique_size = clique_mask.bit_count()
                    if clique_size > best_clique_size:
                        best_clique_size = clique_size
                        best_clique_mask = clique_mask
                        if _base.log.isEnabledFor(logging.INFO):
                            _base.log.info(
                                "  improved after reduction: clique_size=%d elapsed=%.3fs",
                                best_clique_size,
                                time.perf_counter() - t0,
                            )

        if _base.log.isEnabledFor(logging.INFO):
            _base.log.info(
                "restart %d done: feasible=%s uncovered=%d best_so_far=%d elapsed=%.3fs",
                r + 1,
                feasible,
                len(active_edges),
                best_clique_size,
                time.perf_counter() - t0,
            )

    if _base.log.isEnabledFor(logging.INFO):
        _base.log.info("CNS(alpha-scale) done: best_clique=%d elapsed=%.3fs", best_clique_size, time.perf_counter() - t0)

    return [v for v in range(n) if (best_clique_mask >> v) & 1]


# Patch base module entry points to use this alpha-scaled core.
_base._maximum_clique_cns_core = _maximum_clique_cns_core

# Re-export the public API.
maximum_clique_cns = _base.maximum_clique_cns
maximum_clique_via_cns = _base.maximum_clique_via_cns
maximum_clique_via_beasley = _base.maximum_clique_via_beasley
solve_file = _base.solve_file
solve_stdin = _base.solve_stdin
main = _base.main


if __name__ == "__main__":
    main()
