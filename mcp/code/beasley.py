from __future__ import annotations

from typing import List, Tuple, Optional, Set, Dict, Any
import argparse
import ast
import json
import logging
import math
import os
import random
import sys
import time

MAX_GRAPH_SIZE = 700

log = logging.getLogger("beasley")


# ----------------------------
# Graph utilities
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


def build_complement_edges(n: int, adj: List[List[int]]) -> List[Tuple[int, int]]:
    """
    Build the edge list of the complement graph \bar{G} (simple, undirected, no self-loops).
    Returns edges as pairs (u, v) with u < v.

    Uses bitset (Python int) adjacency for speed on moderately-sized graphs.
    """
    if n <= 1:
        return []

    adj = _symmetrize_adj(n, adj)

    # bitset adjacency
    adj_bits = [0] * n
    for u in range(n):
        bits = 0
        for v in adj[u]:
            bits |= 1 << v
        adj_bits[u] = bits

    all_mask = (1 << n) - 1
    edges: List[Tuple[int, int]] = []

    for u in range(n):
        # Missing neighbors = V \ (N(u) ∪ {u})
        missing = (all_mask ^ adj_bits[u]) & ~(1 << u)
        # Keep only v > u to avoid duplicates
        missing &= ~((1 << (u + 1)) - 1)

        while missing:
            lsb = missing & -missing
            v = lsb.bit_length() - 1
            edges.append((u, v))
            missing ^= lsb

    return edges


# ----------------------------
# Beasley (1990) heuristic specialized to Vertex Cover
# (Vertex cover -> Set cover where rows are edges, columns are vertices)
# ----------------------------

def beasley_min_vertex_cover(
    n: int,
    edges: List[Tuple[int, int]],
    costs: Optional[List[float]] = None,
    *,
    max_iters: int = 10000,
    stall_iter: int = 30,
    f_init: float = 2.0,
    f_min: float = 0.005,
    step_fudge: float = 1.05,
    tol: float = 1e-9,
) -> Tuple[Set[int], Dict[str, Any]]:
    """
    Minimum Vertex Cover heuristic on an undirected graph with vertices [0..n-1],
    using Beasley's Lagrangian set-covering heuristic specialized to VC.

    edges: list of undirected edges (u, v), u < v
    costs: vertex costs (default = all 1.0). If you supply tiny perturbations
           below 1/(n+1), cardinality remains the primary objective.

    Returns:
      cover_set: a vertex cover (set of vertices)
      info: diagnostics: best_upper, best_lower, iterations, proved_optimal, cover_size
    """
    if costs is None:
        costs = [1.0] * n
    if len(costs) != n:
        raise ValueError("costs must have length n")

    m = len(edges)
    if m == 0:
        return set(), {
            "best_upper": 0.0,
            "best_lower": 0.0,
            "iterations": 0,
            "proved_optimal": True,
            "cover_size": 0,
        }

    log.info("VC: n=%d edges=%d max_iters=%d", n, m, max_iters)

    # coverage count = degree (each vertex covers its incident edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    # Beasley column ordering: increasing cost, ties by decreasing coverage count
    order = sorted(range(n), key=lambda v: (costs[v], -deg[v], v))
    old_of_new = order
    new_of_old = [0] * n
    for new, old in enumerate(old_of_new):
        new_of_old[old] = new

    # Reindex edges into the ordered column space
    edges_new = [(new_of_old[u], new_of_old[v]) for (u, v) in edges]

    # incidence list per "column" (vertex): which edge-rows it covers
    inc: List[List[int]] = [[] for _ in range(n)]
    for ei, (u, v) in enumerate(edges_new):
        inc[u].append(ei)
        inc[v].append(ei)

    INF = float("inf")
    c = [float(costs[old]) for old in old_of_new]  # mutable costs (deleted => INF)

    # ---- Beasley Step (1) init ----
    Zmax = -INF
    ZUB = INF
    best_selected: Optional[List[int]] = None
    best_cover_size: Optional[int] = None

    P = c.copy()  # forced-in lower bounds per column
    # multipliers per row (edge): t_i = min cost among covering columns (its endpoints)
    t = [min(c[u], c[v]) for (u, v) in edges_new]

    f = f_init
    stall = 0
    it = 0

    while it < max_iters:
        it += 1

        # ---- Step (2) Solve LLBP: compute reduced costs C_j and pick X_j = 1 if C_j <= 0 ----
        sum_t = [0.0] * n
        for i, (u, v) in enumerate(edges_new):
            ti = t[i]
            if ti != 0.0:
                sum_t[u] += ti
                sum_t[v] += ti

        C = [c[j] - sum_t[j] for j in range(n)]
        X = [1 if C[j] <= 0.0 else 0 for j in range(n)]
        ZLB = sum(t) + sum(C[j] for j in range(n) if X[j] == 1)

        if ZLB > Zmax + tol:
            Zmax = ZLB
            stall = 0
        else:
            stall += 1

        # ---- Step (3) Build feasible vertex cover S from X ----
        selected = X[:]  # start from LLBP solution

        # (3b) patch uncovered edges: for each uncovered row add cheapest endpoint
        for (u, v) in edges_new:
            if selected[u] or selected[v]:
                continue
            # choose endpoint with smaller cost; if tie, smaller index (due to ordering)
            chosen = u if c[u] <= c[v] else v
            if math.isinf(c[chosen]):
                other = v if chosen == u else u
                if not math.isinf(c[other]):
                    chosen = other
                else:
                    raise RuntimeError("Infeasible: an edge has both endpoints deleted.")
            selected[chosen] = 1

        # (3c) remove redundant vertices in descending index order
        for j in range(n - 1, -1, -1):
            if not selected[j]:
                continue
            # removable iff every incident edge is still covered by the other endpoint
            for ei in inc[j]:
                u, v = edges_new[ei]
                other = v if u == j else u
                if not selected[other]:
                    break
            else:
                selected[j] = 0

        cover_size = sum(selected)
        cover_cost = sum(c[j] for j in range(n) if selected[j])

        # (3d) update best feasible (upper bound)
        improved = False
        if best_cover_size is None or cover_size < best_cover_size:
            improved = True
        elif cover_size == best_cover_size and cover_cost < ZUB - tol:
            improved = True

        if improved:
            best_cover_size = cover_size
            ZUB = cover_cost
            best_selected = selected[:]
            log.info("  it=%d improved: cover_size=%d cost=%.4f ZLB=%.4f gap=%.4f", it, cover_size, cover_cost, ZLB, ZUB - ZLB)

        if it % 500 == 0 or it <= 5:
            log.info("  it=%d ZLB=%.4f ZUB=%.4f cover=%d f=%.6f stall=%d", it, ZLB, ZUB, cover_size, f, stall)

        # ---- Step (4) Optimality test ----
        if abs(Zmax - ZUB) <= tol:
            log.info("  stop: optimal (Zmax=ZUB)")
            break

        # ---- Step (5) Update P_k and delete columns with P_k > ZUB ----
        for j in range(n):
            if math.isinf(c[j]):
                P[j] = INF
                continue
            val = (ZLB + C[j]) if (X[j] == 0) else ZLB
            if val > P[j] + tol:
                P[j] = val
            if P[j] > ZUB + tol:
                c[j] = INF  # delete column

        # ---- Step (6) subgradients on rows (edges): G_i = 1 - coverage_in_X ----
        sumsq = 0.0
        G = [0.0] * m
        for i, (u, v) in enumerate(edges_new):
            gi = 1.0 - (X[u] + X[v])  # coverage is X[u] + X[v]
            # adjustment: if t_i = 0 and gi < 0 then set gi = 0
            if t[i] <= 0.0 and gi < 0.0:
                gi = 0.0
            G[i] = gi
            sumsq += gi * gi

        # ---- Step (7) stop if cannot define step size ----
        if sumsq <= 0.0:
            log.info("  stop: sumsq=0 (no subgradient direction)")
            break

        # ---- Step (8) step size control: halve f if Zmax stalls ----
        if stall >= stall_iter:
            f *= 0.5
            stall = 0
            log.info("  it=%d f halved to %.6f (stall)", it, f)

        # ---- Step (9) stop if f small ----
        if f <= f_min:
            log.info("  stop: f=%.6f <= f_min", f)
            break

        # ---- Step (8 continued) compute step size ----
        numer = step_fudge * ZUB - ZLB
        if numer < 0.0:
            numer = 0.0
        T = f * numer / sumsq
        if T <= 0.0:
            log.info("  stop: step size T<=0")
            break

        # ---- Step (10) update multipliers ----
        for i in range(m):
            ti = t[i] + T * G[i]
            if ti < 0.0:
                ti = 0.0
            t[i] = ti

    if best_selected is None:
        # should not happen, but keep safe
        best_selected = [1] * n
        ZUB = sum(c[j] for j in range(n) if not math.isinf(c[j]))
        best_cover_size = n

    cover_new = {j for j in range(n) if best_selected[j] == 1}
    cover_old = {old_of_new[j] for j in cover_new}  # map back to original vertex ids

    log.info("VC done: cover_size=%d ZUB=%.4f ZLB=%.4f iterations=%d optimal=%s",
             len(cover_old), ZUB, Zmax, it, abs(Zmax - ZUB) <= tol)

    return cover_old, {
        "best_upper": ZUB,
        "best_lower": Zmax,
        "iterations": it,
        "proved_optimal": abs(Zmax - ZUB) <= tol,
        "cover_size": len(cover_old),
    }


# ----------------------------
# Maximum clique via minimum vertex cover on complement graph
# ----------------------------

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
    """
    Returns a clique (list of vertices) in the ORIGINAL graph G.
    It is maximum only if info["proved_optimal"] is True.

    restarts: run the heuristic multiple times with tiny cost perturbations and keep the best clique.
    """
    adj = _symmetrize_adj(n, adj)
    edges_comp = build_complement_edges(n, adj)

    if not edges_comp:
        log.info("Clique: trivial (complete graph), clique_size=%d", n)
        clique = list(range(n))
        return clique, {
            "clique_size": n,
            "proved_optimal": True,
            "vertex_cover_size": 0,
            "iterations": 0,
            "restarts": 0,
            "complement_edges": 0,
        }

    # complement degrees (used to create tiny non-unicost costs while preserving cardinality objective)
    deg_comp = [0] * n
    for u, v in edges_comp:
        deg_comp[u] += 1
        deg_comp[v] += 1
    max_deg = max(deg_comp) if deg_comp else 1

    if not use_eps_costs:
        restarts = 1  # deterministic; restarts add no value
    log.info("Clique: n=%d complement_edges=%d restarts=%d use_eps_costs=%s",
             n, len(edges_comp), restarts, use_eps_costs)

    rng = random.Random(seed)
    best_clique: List[int] = []
    best_info: Dict[str, Any] = {}

    for r in range(max(1, restarts)):
        log.info("--- restart %d/%d ---", r + 1, max(1, restarts))
        if use_eps_costs:
            # Total perturbation per vertex < eps_total, so any 1-vertex difference in cover size
            # dominates the objective (eps_total*n < 1e-3).
            eps_total = 1e-3 / (n + 1)
            eps_deg = 0.7 * eps_total
            eps_rand = 0.3 * eps_total
            costs = [
                1.0
                + eps_deg * ((max_deg - deg_comp[v]) / (max_deg if max_deg > 0 else 1.0))
                + eps_rand * rng.random()
                for v in range(n)
            ]
        else:
            costs = [1.0] * n

        cover, info_vc = beasley_min_vertex_cover(
            n, edges_comp, costs=costs, max_iters=max_iters, stall_iter=stall_iter
        )

        clique = [v for v in range(n) if v not in cover]
        log.info("restart %d: VC_size=%d clique_size=%d optimal=%s", r + 1, len(cover), len(clique), info_vc.get("proved_optimal", False))
        if len(clique) > len(best_clique):
            best_clique = clique
            best_info = info_vc.copy()
            best_info["restart_used"] = r

        # if VC is proved optimal, clique is maximum
        if info_vc.get("proved_optimal", False):
            best_clique = clique
            best_info = info_vc.copy()
            best_info["restart_used"] = r
            break

    best_clique.sort()
    log.info("Clique done: best_size=%d proved_optimal=%s", len(best_clique), bool(best_info.get("proved_optimal", False)))

    return best_clique, {
        "clique_size": len(best_clique),
        "proved_optimal": bool(best_info.get("proved_optimal", False)),
        "vertex_cover_size": best_info.get("cover_size", None),
        "iterations": best_info.get("iterations", None),
        "best_upper": best_info.get("best_upper", None),
        "best_lower": best_info.get("best_lower", None),
        "restarts": restarts,
        "restart_used": best_info.get("restart_used", None),
        "complement_edges": len(edges_comp),
    }


# ----------------------------
# .pro file format (dataset/log/problems/*.pro)
# ----------------------------

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


# ----------------------------
# CLI: file args and optional stdin
# ----------------------------

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
    use_cost_perturbation: bool = False,
    restarts: int = 5,
    seed: int = 0,
    stall_iter: int = 30,
) -> Tuple[List[int], float]:
    """Solve one .pro file; returns (clique, elapsed_seconds)."""
    log.info(">>> %s", path)
    n, adj = load_pro_file(path)
    t0 = time.perf_counter()
    clique, _ = maximum_clique_via_beasley(
        n, adj, restarts=restarts, seed=seed, use_eps_costs=use_cost_perturbation,
        stall_iter=stall_iter
    )
    elapsed = time.perf_counter() - t0
    return clique, elapsed


def solve_stdin(
    *,
    use_cost_perturbation: bool = False,
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
    clique, _ = maximum_clique_via_beasley(
        n, adj, restarts=restarts, seed=seed, use_eps_costs=use_cost_perturbation,
        stall_iter=stall_iter
    )
    elapsed = time.perf_counter() - t0
    print(format_sol(clique, elapsed), end="")


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Maximum clique via Beasley heuristic (vertex cover on complement)."
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
        "--cost-perturbation",
        action="store_true",
        default=False,
        help="Use small cost perturbations per vertex (default: off).",
    )
    parser.add_argument(
        "--restarts",
        type=int,
        default=5,
        metavar="N",
        help="Number of restarts with different costs (default: 5).",
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
        help="Iterations without ZLB improvement before halving step factor f (default: 30).",
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
        for i, fname in enumerate(pro_files):
            in_path = os.path.join(args.input_dir, fname)
            base = os.path.splitext(fname)[0]
            out_path = os.path.join(args.output_dir, base + ".res")
            try:
                clique, elapsed = solve_file(
                    in_path,
                    use_cost_perturbation=args.cost_perturbation,
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
                use_cost_perturbation=args.cost_perturbation,
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
                    use_cost_perturbation=args.cost_perturbation,
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
                use_cost_perturbation=args.cost_perturbation,
                restarts=args.restarts,
                seed=args.seed,
                stall_iter=args.stall_iter,
            )
        except (ValueError, OSError) as e:
            print(f"Error: {e}", file=sys.stderr)
            sys.exit(1)


if __name__ == "__main__":
    main()
