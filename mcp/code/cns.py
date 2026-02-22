#!/usr/bin/env python3
"""
CNS-guided maximum clique heuristic via minimum vertex cover on the complement graph.

Input format (stdin):
  n
  adjacency_list

Where adjacency_list is a Python literal or JSON list-of-lists (0-based).
Example:
  5
  [[1,2],[0,2],[0,1,3],[2,4],[3]]

Output:
  A clique as a Python list of vertex indices (in increasing order).

Notes:
- This is a heuristic (not guaranteed optimal).
- Designed for n <= 700 and dense graphs (0.75..0.9), using bitsets (Python ints).
"""

from dataclasses import dataclass
from typing import Any, Dict, List, Tuple
import argparse
import random
import ast
import json
import logging
import os
import sys
import time

MAX_GRAPH_SIZE = 700
log = logging.getLogger("cns")


@dataclass
class PDParams:
    rho: float
    fmin: float
    Delta: float
    f0: float
    beta: int
    max_iters: int
    eps: float = 1e-9


def _build_bit_adjacency(n, adj_list):
    """Symmetrize adjacency and return list[int] bitsets for an undirected graph."""
    bits = [0] * n
    for u, nbrs in enumerate(adj_list):
        b = 0
        for v in nbrs:
            if 0 <= v < n and v != u:
                b |= 1 << v
        bits[u] = b

    # Symmetrize (treat input as undirected, even if one-sided)
    for u in range(n):
        b = bits[u]
        while b:
            lsb = b & -b
            v = lsb.bit_length() - 1
            b ^= lsb
            bits[v] |= 1 << u

    return bits


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


def _complement_bits(n, adj_bits):
    """Complement graph adjacency as bitsets."""
    all_mask = (1 << n) - 1
    return [all_mask & ~(adj_bits[u] | (1 << u)) for u in range(n)]


def _build_edges_from_bits(n, comp_bits):
    """Build undirected edge list (u[i], v[i]) with u < v, and incidence lists inc[v] = edges incident to v."""
    edge_u = []
    edge_v = []
    inc = [[] for _ in range(n)]

    for u in range(n):
        # neighbors with v > u
        b = comp_bits[u] & ~((1 << (u + 1)) - 1)
        while b:
            lsb = b & -b
            v = lsb.bit_length() - 1
            b ^= lsb
            e = len(edge_u)
            edge_u.append(u)
            edge_v.append(v)
            inc[u].append(e)
            inc[v].append(e)

    return edge_u, edge_v, inc


def _greedy_maximal_independent_set(comp_bits, cand_mask):
    """
    Greedy maximal independent set in the graph defined by comp_bits adjacency, restricted to cand_mask.
    Uses a 'min-degree' choice (in the induced subgraph) to grow a larger independent set.
    """
    indep = 0
    cand = cand_mask

    while cand:
        # pick min-degree vertex in induced subgraph on cand
        best_v = None
        best_deg = None
        tmp = cand
        while tmp:
            lsb = tmp & -tmp
            v = lsb.bit_length() - 1
            tmp ^= lsb
            deg = (comp_bits[v] & cand).bit_count()
            if best_deg is None or deg < best_deg:
                best_deg = deg
                best_v = v
                if deg == 0:
                    break

        v = best_v
        indep |= 1 << v
        cand &= ~((1 << v) | comp_bits[v])

    return indep


def _completion_independent_set(comp_bits, free_mask, forced_indep_mask):
    """
    Completion heuristic:
      Build an independent set in the complement graph consistent with:
        - forced_indep_mask vertices are forced OUT of the cover (i.e., in independent set)
        - free_mask vertices are available for selection into the independent set
      Then cover = V \\ independent_set is a feasible vertex cover.
    """
    indep = forced_indep_mask
    cand = free_mask

    # Remove neighbors of forced vertices from candidates
    tmp = indep
    while tmp:
        lsb = tmp & -tmp
        v = lsb.bit_length() - 1
        tmp ^= lsb
        cand &= ~comp_bits[v]

    indep |= _greedy_maximal_independent_set(comp_bits, cand)
    return indep


def _reduce_cover_by_redundancy(comp_bits, cover_mask):
    """
    Remove redundant vertices from a vertex cover in the complement graph.

    v is redundant if all its (complement-graph) neighbors are also in the cover,
    i.e., moving v out of the cover still covers every incident edge.
    """
    cover = cover_mask
    verts = [v for v in range(len(comp_bits)) if (cover >> v) & 1]
    # heuristic: low-degree first tends to remove more without blocking too many others
    verts.sort(key=lambda v: comp_bits[v].bit_count())

    for v in verts:
        if (cover >> v) & 1:
            if (comp_bits[v] & ~cover) == 0:
                cover &= ~(1 << v)

    return cover


def _primal_dual_lagrangian_vc(active_edges, free_vertices, edge_u, edge_v, lam, mu, params: PDParams):
    """
    CNS Fig-2-style primal-dual Lagrangian procedure specialized to unit-cost vertex cover.

    Updates:
      lam[e] for e in active_edges
      mu[v] for v in free_vertices

    Returns:
      zLB (current L(λ) lower bound on remaining subproblem),
      red_cost[v] for all vertices (meaningful for free_vertices).
    """
    pf = df = params.f0
    best_lower = -1e100
    best_upper = 1e100
    no_impr_lower = 0
    no_impr_upper = 0

    n = len(mu)
    sum_lambda = [0.0] * n
    red_cost = [0.0] * n
    y = [0] * n
    count_z = [0] * n
    d_slack = [0.0] * n

    if not active_edges or not free_vertices:
        return 0.0, red_cost

    zLB = 0.0
    it = 0

    while ((pf > params.fmin) or (df > params.fmin)) and ((best_upper - best_lower) > params.Delta) and (it < params.max_iters):
        it += 1

        # reset accumulators for free vertices only
        for v in free_vertices:
            sum_lambda[v] = 0.0
            count_z[v] = 0

        # edge loop: sum lambdas
        sum_lambda_total = 0.0
        for e in active_edges:
            le = lam[e]
            sum_lambda_total += le
            if le != 0.0:
                u = edge_u[e]
                v = edge_v[e]
                sum_lambda[u] += le
                sum_lambda[v] += le

        # vertex loop: primal reduced costs + y, and sum mu
        sum_y_redcost = 0.0
        sum_mu_total = 0.0
        for v in free_vertices:
            rc = 1.0 - sum_lambda[v]
            red_cost[v] = rc
            if rc < 0.0:
                y[v] = 1
                sum_y_redcost += rc
            else:
                y[v] = 0
            sum_mu_total += mu[v]

        # edge loop: sigma, zUB_second, and counts for d_slack
        sigma = 0.0
        zUB_second = 0.0
        for e in active_edges:
            u = edge_u[e]
            v = edge_v[e]
            slack = 1 - y[u] - y[v]  # ∈ {-1, 0, 1}
            if slack:
                sigma += 1.0  # slack^2
            d_red = 1.0 - mu[u] - mu[v]
            if d_red > 0.0:
                zUB_second += d_red  # since z_e = 1 and \bar c = 1
                count_z[u] += 1
                count_z[v] += 1

        zLB = sum_lambda_total + sum_y_redcost
        zUB = sum_mu_total + zUB_second

        # The paper figure shows min() for both; the lower bound should be maximized (standard correction).
        if zLB > best_lower + params.eps:
            best_lower = zLB
            no_impr_lower = 0
        else:
            no_impr_lower += 1

        if zUB < best_upper - params.eps:
            best_upper = zUB
            no_impr_upper = 0
        else:
            no_impr_upper += 1

        # vertex loop: dual slacks and d_sigma
        d_sigma = 0.0
        for v in free_vertices:
            ds = count_z[v] - 1.0
            d_slack[v] = ds
            d_sigma += ds * ds

        # step sizes
        if sigma > 0.0:
            p_step = pf * (best_upper - zLB) / sigma
            if p_step < 0.0:
                p_step = 0.0
        else:
            p_step = 0.0

        if d_sigma > 0.0:
            d_step = df * (zUB - best_lower) / d_sigma
            if d_step < 0.0:
                d_step = 0.0
        else:
            d_step = 0.0

        # update lambdas (project to >= 0)
        if p_step:
            for e in active_edges:
                u = edge_u[e]
                v = edge_v[e]
                slack = 1 - y[u] - y[v]
                if slack:
                    new_le = lam[e] + p_step * slack
                    if new_le < 0.0:
                        new_le = 0.0
                    lam[e] = new_le

        # update mus (project to >= 0)
        if d_step:
            for v in free_vertices:
                ds = d_slack[v]
                if ds:
                    new_mu = mu[v] + d_step * ds
                    if new_mu < 0.0:
                        new_mu = 0.0
                    mu[v] = new_mu

        # reduce step factors if no improvement in last beta iters
        if no_impr_lower >= params.beta:
            pf /= params.rho
            no_impr_lower = 0
        if no_impr_upper >= params.beta:
            df /= params.rho
            no_impr_upper = 0

    return zLB, red_cost

def _is_independent(graph_bits, mask: int) -> bool:
    """True iff 'mask' is an independent set in the graph whose adjacency is graph_bits."""
    tmp = mask
    while tmp:
        lsb = tmp & -tmp
        v = lsb.bit_length() - 1
        tmp ^= lsb
        if graph_bits[v] & mask:
            return False
    return True


def _maximalize_clique_mask(adj_bits: List[int], clique_mask: int) -> int:
    """Greedily extend a clique mask until it is maximal."""
    n = len(adj_bits)
    all_mask = (1 << n) - 1
    clique = clique_mask
    cand = all_mask & ~clique
    while cand:
        lsb = cand & -cand
        v = lsb.bit_length() - 1
        cand ^= lsb
        if (adj_bits[v] & clique) == clique:
            clique |= 1 << v
            cand &= adj_bits[v]
    return clique


def _greedy_clique_from_order(adj_bits: List[int], order: List[int]) -> int:
    """Build one clique greedily by following a fixed vertex order."""
    clique = 0
    n = len(adj_bits)
    cand = (1 << n) - 1
    for v in order:
        if (cand >> v) & 1:
            clique |= 1 << v
            cand &= adj_bits[v]
    return clique


def _polish_clique(adj_bits: List[int], start_mask: int, rng: random.Random, rounds: int = 24) -> int:
    """
    Lightweight multi-order polishing:
      - force maximality
      - run additional greedy constructions from deterministic and randomized orders
      - keep best clique found
    """
    n = len(adj_bits)
    verts = list(range(n))
    deg = [adj_bits[v].bit_count() for v in range(n)]

    best = _maximalize_clique_mask(adj_bits, start_mask)
    best_size = best.bit_count()

    # Deterministic orders first
    orders: List[List[int]] = []
    orders.append(sorted(verts, key=lambda v: (-deg[v], v)))
    orders.append(sorted(verts, key=lambda v: (deg[v], v)))

    # Bias one order around incumbent vertices
    in_best = [v for v in verts if (best >> v) & 1]
    out_best = [v for v in verts if not ((best >> v) & 1)]
    out_best.sort(key=lambda v: (-deg[v], v))
    orders.append(in_best + out_best)

    for order in orders:
        cand = _maximalize_clique_mask(adj_bits, _greedy_clique_from_order(adj_bits, order))
        csz = cand.bit_count()
        if csz > best_size:
            best = cand
            best_size = csz

    # Randomized orders for extra diversification
    for _ in range(max(0, rounds)):
        order = verts[:]
        rng.shuffle(order)
        cand = _maximalize_clique_mask(adj_bits, _greedy_clique_from_order(adj_bits, order))
        csz = cand.bit_count()
        if csz > best_size:
            best = cand
            best_size = csz

    return best


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
    CNS-guided maximum clique heuristic:
      max clique in G  <->  min vertex cover in complement(G)

    Returns:
      clique as a list of vertices (0-based).
    """
    if n <= 0:
        return []
    if len(adjacency) != n:
        raise ValueError("Adjacency list length must equal n")

    adj_bits = _build_bit_adjacency(n, adjacency)
    comp_bits = _complement_bits(n, adj_bits)
    all_mask = (1 << n) - 1

    edge_u, edge_v, inc = _build_edges_from_bits(n, comp_bits)
    m = len(edge_u)
    if m == 0:
        return list(range(n))  # original graph complete

    rng = random.Random(seed)

    # CNS parameter choices for the primal-dual subroutine:
    pd_first = PDParams(rho=1.2, fmin=0.002, Delta=0.01, f0=4.0, beta=15, max_iters=pd_first_iters)
    pd_next  = PDParams(rho=2.0, fmin=0.02,  Delta=0.1,  f0=2.0, beta=5,  max_iters=pd_next_iters)

    best_clique_mask = 0
    best_clique_size = -1

    t0 = time.perf_counter()
    if log.isEnabledFor(logging.INFO):
        log.info("CNS start: n=%d complement_edges=%d restarts=%d", n, m, restarts)

    for r in range(restarts):
        # CNS: alpha = 12 first run, then cycle 4,8,12 across subsequent runs
        if r == 0:
            alpha = 12.0
            randomized = False
        else:
            alpha = [4.0, 8.0, 12.0][(r - 1) % 3]
            randomized = True

        in_cover = 0
        forbidden = 0  # fixed to 0 (not in cover) => forced into independent set

        # Active edges, swap-pop removal
        active_edges = list(range(m))
        pos = list(range(m))

        # Dynamic degrees w.r.t. currently active uncovered edges
        deg_active = [len(inc[v]) for v in range(n)]

        # Lagrangian multipliers
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
            # cover overrides forbidden
            if (forbidden >> v) & 1:
                forbidden &= ~(1 << v)

            in_cover |= 1 << v
            # cover all incident active edges
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

                    # If both endpoints forbidden => infeasible
                    if (forbidden >> other) & 1:
                        feasible = False
                        return

                    add_to_cover(other)

        if log.isEnabledFor(logging.INFO):
            log.info("restart %d/%d: alpha=%.1f randomized=%s", r + 1, restarts, alpha, randomized)

        while active_edges and feasible:
            # Any free vertex with degree 0 in the remaining uncovered-edge graph
            # can safely stay out of the cover (put into independent set).
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
            zLB, red_cost = _primal_dual_lagrangian_vc(
                active_edges, free_vertices, edge_u, edge_v, lam, mu, params
            )

            # Completion heuristic -> incumbent solution + clique candidate
            indep_mask = _completion_independent_set(comp_bits, free_mask, forbidden)
            indep_size = indep_mask.bit_count()
            if indep_size > best_clique_size:
                best_clique_size = indep_size
                best_clique_mask = indep_mask
                if log.isEnabledFor(logging.INFO):
                    log.info("  improved incumbent: clique_size=%d elapsed=%.3fs", best_clique_size, time.perf_counter() - t0)

            # Gap for reduced-cost fixing (mostly inactive for unit costs unless gap is small)
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

            # Scale check on the greedy merit terms:
            #   mu[v]  versus  alpha * red_cost[v]
            mu_min = float("inf")
            mu_max = float("-inf")
            rc_min = float("inf")
            rc_max = float("-inf")
            for v in free_vertices:
                mv = mu[v]
                rv = red_cost[v]
                if mv < mu_min:
                    mu_min = mv
                if mv > mu_max:
                    mu_max = mv
                if rv < rc_min:
                    rc_min = rv
                if rv > rc_max:
                    rc_max = rv

            range_mu = max(0.0, mu_max - mu_min)
            range_rc = max(0.0, rc_max - rc_min)
            alpha_range_rc = alpha * range_rc
            scale_eps = 1e-12
            scale_factor = 10.0
            if alpha_range_rc >= scale_factor * max(range_mu, scale_eps):
                alpha_scale_relation = "alpha*range_rc >> range_mu"
            elif range_mu >= scale_factor * max(alpha_range_rc, scale_eps):
                alpha_scale_relation = "alpha*range_rc << range_mu"
            else:
                alpha_scale_relation = "alpha*range_rc ~ range_mu"

            # Merit = mu[v] - alpha * red_cost[v]
            cand = []
            for v in free_vertices:
                if (fix_zero_mask >> v) & 1:
                    continue
                cand.append((mu[v] - alpha * red_cost[v], v))

            if not cand:
                # fallback: pick max-degree vertex
                v = max(free_vertices, key=lambda x: deg_active[x])
                cand = [(0.0, v)]

            cand.sort(reverse=True)

            k = max(1, int(batch_size))
            k = min(k, len(cand))
            chosen = [cand[i][1] for i in range(k)]

            # CNS randomization: with prob 1/2 choose 2nd-best instead of best (later runs)
            if randomized and len(chosen) >= 2 and rng.random() < 0.5:
                chosen[0], chosen[1] = chosen[1], chosen[0]

            fix_one_mask = 0
            for v in chosen:
                fix_one_mask |= 1 << v

            # CNS: also fix to 1 those with mu >= 0.99 and red_cost <= 0.01
            for v in free_vertices:
                if (fix_zero_mask >> v) & 1:
                    continue
                if mu[v] >= 0.99 and red_cost[v] <= 0.01:
                    fix_one_mask |= 1 << v

            # resolve conflicts
            fix_zero_mask &= ~fix_one_mask

            # apply fix-to-0, then fix-to-1
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

            if log.isEnabledFor(logging.INFO):
                log.info(
                    "  iter restart=%d step=%d uncovered=%d free=%d cover=%d forbidden=%d zLB=%.4f gap=%.4f range_mu=%.4e range_rc=%.4e alpha_range_rc=%.4e scale=%s best=%d elapsed=%.3fs",
                    r + 1,
                    step + 1,
                    len(active_edges),
                    len(free_vertices),
                    in_cover.bit_count(),
                    forbidden.bit_count(),
                    zLB,
                    gap,
                    range_mu,
                    range_rc,
                    alpha_range_rc,
                    alpha_scale_relation,
                    best_clique_size,
                    time.perf_counter() - t0,
                )

            step += 1
            if step > 2 * n:  # hard safety bound
                feasible = False
                if log.isEnabledFor(logging.INFO):
                    log.info("  stop restart=%d: safety bound reached (step>%d)", r + 1, 2 * n)
                break

        # Always build a guaranteed-feasible clique candidate from completion
        if feasible:
            free_mask = all_mask & ~(in_cover | forbidden)
            indep_mask = _completion_independent_set(comp_bits, free_mask, forbidden)

            # Defensive: completion should yield an independent set, but verify anyway
            if _is_independent(comp_bits, indep_mask):
                cover_mask = all_mask & ~indep_mask
                cover_mask = _reduce_cover_by_redundancy(comp_bits, cover_mask)
                clique_mask = all_mask & ~cover_mask

                # Optional defensive check:
                if _is_independent(comp_bits, clique_mask):
                    clique_size = clique_mask.bit_count()
                    if clique_size > best_clique_size:
                        best_clique_size = clique_size
                        best_clique_mask = clique_mask
                        if log.isEnabledFor(logging.INFO):
                            log.info("  improved after reduction: clique_size=%d elapsed=%.3fs", best_clique_size, time.perf_counter() - t0)

        if log.isEnabledFor(logging.INFO):
            log.info(
                "restart %d done: feasible=%s uncovered=%d best_so_far=%d elapsed=%.3fs",
                r + 1,
                feasible,
                len(active_edges),
                best_clique_size,
                time.perf_counter() - t0,
            )

    if log.isEnabledFor(logging.INFO):
        log.info("CNS done: best_clique=%d elapsed=%.3fs", best_clique_size, time.perf_counter() - t0)

    return [v for v in range(n) if (best_clique_mask >> v) & 1]


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
    """
    Beasley-compatible CNS wrapper.

    Matches the argument surface of ../beasley/beasley.py's
    maximum_clique_via_beasley for easy drop-in usage.
    """
    if n > MAX_GRAPH_SIZE:
        raise ValueError(f"Graph size {n} exceeds maximum {MAX_GRAPH_SIZE}")
    if len(adj) != n:
        raise ValueError("Adjacency list length must equal n")

    adj = _symmetrize_adj(n, adj)

    # Kept for signature compatibility with Beasley-style callers.
    # CNS does not use cost perturbations.
    _ = use_eps_costs
    effective_restarts = max(1, int(restarts))

    # Map Beasley-like controls to CNS inner-loop budgets.
    # max_iters controls total effort; stall_iter controls shorter follow-up updates.
    pd_first_iters = max(10, min(200, int(max_iters) // max(1, effective_restarts)))
    pd_next_iters = max(2, min(40, int(stall_iter) // 2))

    t0 = time.perf_counter()

    clique = _maximum_clique_cns_core(
        n,
        adj,
        restarts=effective_restarts,
        seed=seed,
        batch_size=8,
        pd_first_iters=pd_first_iters,
        pd_next_iters=pd_next_iters,
    )

    # Post-polish to enforce maximality and improve weak incumbents.
    adj_bits = _build_bit_adjacency(n, adj)
    clique_mask = 0
    for v in clique:
        clique_mask |= 1 << v
    before_polish = clique_mask.bit_count()
    polish_rounds = max(8, min(40, effective_restarts * 4))
    clique_mask = _polish_clique(adj_bits, clique_mask, random.Random(seed ^ 0xC15C), rounds=polish_rounds)
    clique = [v for v in range(n) if (clique_mask >> v) & 1]

    if log.isEnabledFor(logging.INFO):
        log.info(
            "post-polish: before=%d after=%d rounds=%d elapsed=%.3fs",
            before_polish,
            len(clique),
            polish_rounds,
            time.perf_counter() - t0,
        )

    # Lightweight diagnostics with Beasley-compatible keys.
    comp_bits = _complement_bits(n, adj_bits)
    edge_u, _, _ = _build_edges_from_bits(n, comp_bits)
    elapsed = time.perf_counter() - t0

    if log.isEnabledFor(logging.INFO):
        log.info("best clique so far: size=%d elapsed=%.3fs", len(clique), elapsed)

    return clique, {
        "clique_size": len(clique),
        "proved_optimal": False,
        "vertex_cover_size": n - len(clique),
        "iterations": None,
        "best_upper": None,
        "best_lower": None,
        "restarts": effective_restarts,
        "restart_used": None,
        "complement_edges": len(edge_u),
        "elapsed_seconds": elapsed,
    }


def maximum_clique_via_cns(
    n: int,
    adj: List[List[int]],
    *,
    max_iters: int = 10000,
    stall_iter: int = 30,
    restarts: int = 1,
    seed: int = 0,
    use_eps_costs: bool = True,
) -> Tuple[List[int], Dict[str, Any]]:
    """Alias with Beasley-like naming."""
    return maximum_clique_cns(
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
    return maximum_clique_via_cns(
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


def format_basesol(clique: List[int]) -> str:
    """Format clique as .basesol: first line = size, second line = comma-separated vertices."""
    size = len(clique)
    return f"{size}\n" + ",".join(str(v) for v in clique)


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
    clique, _ = maximum_clique_via_cns(
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
    clique, _ = maximum_clique_via_cns(
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
        description="Maximum clique via CNS heuristic (vertex cover on complement)."
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
        help="Control parameter for CNS follow-up inner iterations (default: 30).",
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
