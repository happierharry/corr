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
import random
import ast
import json
import sys


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


def maximum_clique_cns(
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

            step += 1
            if step > 2 * n:  # hard safety bound
                break

        # If feasible, try redundancy removal to enlarge clique
        if feasible:
            cover_mask = _reduce_cover_by_redundancy(comp_bits, in_cover)
            clique_mask = all_mask & ~cover_mask
            clique_size = clique_mask.bit_count()
            if clique_size > best_clique_size:
                best_clique_size = clique_size
                best_clique_mask = clique_mask

    return [v for v in range(n) if (best_clique_mask >> v) & 1]


def _parse_stdin():
    data = sys.stdin.read().strip()
    if not data:
        return 0, []
    lines = data.splitlines()
    n = int(lines[0].strip())
    adj_text = "\n".join(lines[1:]).strip()
    if not adj_text:
        return n, [[] for _ in range(n)]
    try:
        adj = json.loads(adj_text)
    except Exception:
        adj = ast.literal_eval(adj_text)
    return n, adj


def solve():
    n, adj = _parse_stdin()
    clique = maximum_clique_cns(n, adj)
    print(clique)


if __name__ == "__main__":
    solve()
