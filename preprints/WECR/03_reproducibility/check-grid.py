#!/usr/bin/env python3
"""Independently check the first even q covered by the deterministic theorem."""
from collections import Counter
from itertools import product
from math import isqrt

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def check(q: int, b: int) -> None:
    d, r = b * (2 * q - 1), isqrt(q)
    rounds = (d + 1) // 2
    vertices = set(product(range(q), range(q), range(b)))
    left_endpoints = [(0, col, 0) for col in (0, 1)]
    right_endpoints = [(q // 2, col, 0) for col in (0, 1)]
    anchors = [(q // 2 + 1, 2 * h, 0) for h in range(r)]
    holes = [(q // 2 + 1, 2 * h + 1, 0) for h in range(r)]
    intact = vertices - set(left_endpoints + right_endpoints + anchors + holes)

    def adjacent(x, y):
        return x in vertices and y in vertices and (x[0] == y[0] or x[1] == y[1])

    all_choices = [
        (j, h, w)
        for j in range(rounds)
        for h in holes
        for w in sorted(intact)
        if adjacent(h, w)
    ]
    keys = {}
    rows = []
    columns = []
    lower = []
    for col, (j, h, w) in enumerate(all_choices):
        for key, lo in ((("round-hole", j, h), 1), (("pair", h, w), 0), (("round-helper", j, w), 0)):
            if key not in keys:
                keys[key] = len(keys)
                lower.append(lo)
            rows.append(keys[key])
            columns.append(col)
    matrix = coo_matrix((np.ones(len(rows)), (rows, columns)), shape=(len(keys), len(all_choices))).tocsc()
    options = {"time_limit": 60.0}
    result = milp(
        c=np.zeros(len(all_choices)),
        integrality=np.ones(len(all_choices)),
        bounds=Bounds(0, 1),
        constraints=LinearConstraint(matrix, lower, 1),
        options=options,
    )
    assert result.success, result.message
    exchanges = [choice for x, choice in zip(result.x, all_choices, strict=True) if x > 0.5]
    assert len(exchanges) == rounds * r
    assert len({(j, h) for j, h, _ in exchanges}) == rounds * r
    assert len({(h, w) for _, h, w in exchanges}) == rounds * r
    assert len({(j, w) for j, _, w in exchanges}) == rounds * r

    exception = [("exception", h) for h in range(r)]
    complete_sides = vertices | set(exception)
    static = set(zip(right_endpoints, left_endpoints)) | {(w, w) for w in intact}
    fixed = set(static)
    for e, a, h in zip(exception, anchors, holes, strict=True):
        static.update(((a, e), (e, a), (h, e), (e, h), (e, e)))
        fixed.update(((a, e), (e, a)))

    def cap(x, y):
        return d * ((x, y) in static) + 2 * adjacent(x, y)

    spent = Counter()
    for j in range(d):
        current = [(h, w) for round_id, h, w in exchanges if round_id == j % rounds]
        selected = fixed - {(w, w) for _, w in current}
        selected.update((x, y) for h, w in current for x, y in ((h, w), (w, h)))
        assert len({x for x, _ in selected}) == len(selected)
        assert len({y for _, y in selected}) == len(selected)
        assert {x for x, _ in selected} == complete_sides - set(left_endpoints)
        assert {y for _, y in selected} == complete_sides - set(right_endpoints)
        spent.update(selected)
    assert all(used <= cap(*pair) for pair, used in spent.items())
    for side, internal in enumerate((left_endpoints, right_endpoints)):
        filler = Counter(pair[side] for pair in static)
        used = Counter()
        for pair, count in spent.items():
            used[pair[side]] += count
        for v in complete_sides:
            crossing = d * filler[v] + (2 * d if v in vertices else 0)
            assert crossing + (d if v in internal else 0) == 3 * d
            assert crossing - used[v] == 2 * d
    left = {x for x in vertices if x[0] < q // 2}
    right = vertices - left
    assert len(left) + len(right) == b * q**2
    assert {sum(cap(x, y) for y in right) for x in left} == {b * q}
    assert {sum(cap(x, y) for x in left) for y in right} == {b * q}
    print(f"q={q}, b={b}: {d} disjoint seed matchings, residue degree {2*d}, rectangle degree {b*q}")


if __name__ == "__main__":
    check(12, 1)
    check(12, 2)
