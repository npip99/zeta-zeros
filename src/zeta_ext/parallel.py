"""Parallel driver: partition the initial boxes of a certificate across workers.

Each worker runs the same rigorous search as verify_general on its subset of
initial boxes. The certificate holds iff every worker verifies its subset
(the initial boxes cover the full domain by construction).
"""

from __future__ import annotations

import math
import multiprocessing as mp
import time
from typing import Dict, List, Sequence, Tuple

from flint import fmpq

from .kernel import KernelSpec
from .verify_general import CertificateSpec, GeneralReport, verify_general


def _spec_to_primitives(spec: CertificateSpec) -> Dict:
    return {
        "coeffs": [(int(c.p), int(c.q)) for c in spec.kernel.coeffs],
        "omega_pi_multiples": list(spec.kernel.omega_pi_multiples),
        "has_sqrt2_term": spec.kernel.has_sqrt2_term,
        "q": spec.q,
        "pressure": (int(spec.pressure.p), int(spec.pressure.q)),
        "target": (int(spec.target.p), int(spec.target.q)),
        "weights": {
            f"{i},{j}": (int(v.p), int(v.q)) for (i, j), v in spec.weights.items()
        },
        "grid": spec.grid,
        "precision": spec.precision,
        "extra_cells": spec.extra_cells,
        "use_tangent": spec.use_tangent,
    }


def _spec_from_primitives(data: Dict) -> CertificateSpec:
    kernel = KernelSpec(
        coeffs=tuple(fmpq(p, q) for p, q in data["coeffs"]),
        omega_pi_multiples=tuple(data["omega_pi_multiples"]),
        has_sqrt2_term=data["has_sqrt2_term"],
    )
    weights = {}
    for key, (p, q) in data["weights"].items():
        i, j = key.split(",")
        weights[(int(i), int(j))] = fmpq(p, q)
    return CertificateSpec(
        kernel=kernel,
        q=data["q"],
        pressure=fmpq(*data["pressure"]),
        target=fmpq(*data["target"]),
        weights=weights,
        grid=data["grid"],
        precision=data["precision"],
        extra_cells=data["extra_cells"],
        use_tangent=data.get("use_tangent", True),
    )


def _worker(args: Tuple[Dict, int, int, Sequence[float], Sequence[float]]) -> Dict:
    data, shard, shard_count, table, second_table = args
    spec = _spec_from_primitives(data)
    report = verify_general(
        spec,
        progress_every=0,
        shard=shard,
        shard_count=shard_count,
        tables=(list(table), list(second_table)),
    )
    return {
        "verified": report.verified,
        "nodes": report.nodes,
        "pruned": report.pruned,
        "splits": report.splits,
        "maximum_depth": report.maximum_depth,
        "initial_boxes": report.initial_boxes,
        "details": report.details,
    }


def _table_chunk_worker(args: Tuple[Dict, int, int]) -> Tuple[List[float], List[float]]:
    from .kernel import build_w_lower_table, build_w_second_lower_table

    data, start, stop = args
    spec = _spec_from_primitives(data)
    lower = build_w_lower_table(
        spec.grid, stop, spec.kernel, spec.precision, start=start
    )
    second = build_w_second_lower_table(
        spec.grid, stop, spec.kernel, spec.precision, start=start
    )
    return lower, second


def build_tables_parallel(
    spec: CertificateSpec, workers: int = 8
) -> Tuple[List[float], List[float]]:
    from .verify_general import cutoff_cell_count

    cell_count = cutoff_cell_count(spec) + spec.extra_cells
    data = _spec_to_primitives(spec)
    chunk = math.ceil(cell_count / workers)
    jobs = [
        (data, start, min(start + chunk, cell_count))
        for start in range(0, cell_count, chunk)
    ]
    context = mp.get_context("spawn")
    with context.Pool(len(jobs)) as pool:
        results = pool.map(_table_chunk_worker, jobs)
    table: List[float] = []
    second_table: List[float] = []
    for lower, second in results:
        table.extend(lower)
        second_table.extend(second)
    if len(table) != cell_count:
        raise RuntimeError("table assembly mismatch")
    return table, second_table


def verify_parallel(spec: CertificateSpec, workers: int = 8) -> GeneralReport:
    started = time.perf_counter()

    table, second_table = build_tables_parallel(spec, workers)
    data = _spec_to_primitives(spec)
    jobs = [
        (data, shard, workers, table, second_table) for shard in range(workers)
    ]
    context = mp.get_context("spawn")
    with context.Pool(workers) as pool:
        results = pool.map(_worker, jobs)
    if not all(r["verified"] for r in results):
        raise RuntimeError("a shard failed verification")
    details: Dict[str, object] = dict(results[0]["details"])
    for key in ("pressure_pruned", "interval_pruned", "tangent_pruned"):
        details[key] = sum(r["details"][key] for r in results)
    details["workers"] = workers
    hashes = {
        (r["details"]["w_table_sha256"], r["details"]["w_second_table_sha256"])
        for r in results
    }
    if len(hashes) != 1:
        raise RuntimeError("table hash mismatch across workers")
    return GeneralReport(
        verified=True,
        target=f"F >= {spec.target}",
        grid=spec.grid,
        nodes=sum(r["nodes"] for r in results),
        pruned=sum(r["pruned"] for r in results),
        splits=sum(r["splits"] for r in results),
        maximum_depth=max(r["maximum_depth"] for r in results),
        initial_boxes=sum(r["initial_boxes"] for r in results),
        elapsed_seconds=time.perf_counter() - started,
        details=details,
    )
