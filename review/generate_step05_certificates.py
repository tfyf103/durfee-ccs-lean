#!/usr/bin/env python3
"""Generate the finite Durfee certificates with exact integer arithmetic.

Each JSON line is [n, coefficients, [[u, e], ...]], in increasing order of n.
The coefficients are [p(n,1), ..., p(n,isqrt(n))]. The ordered points u/2**e
start with y_2.
"""

import argparse
import hashlib
from itertools import product
import json
import math
from pathlib import Path


def durfee_coefficients(limit):
    rows = [[] for _ in range(limit + 1)]
    series = [1] + [0] * limit
    for d in range(1, math.isqrt(limit) + 1):
        upto = limit - d * d
        for _ in range(2):
            for j in range(d, upto + 1):
                series[j] += series[j - d]
        for j in range(upto + 1):
            rows[d * d + j].append(series[j])
    return rows


def partition_numbers(limit):
    terms = []
    for k in range(1, limit + 1):
        lower = k * (3 * k - 1) // 2
        if lower > limit:
            break
        sign = 1 if k % 2 else -1
        terms.extend(((lower, sign), (lower + k, sign)))
    partitions = [1]
    for n in range(1, limit + 1):
        value = 0
        for offset, sign in terms:
            if offset > n:
                break
            value += sign * partitions[n - offset]
        partitions.append(value)
    return partitions


def independently_recomputed_coefficients(limit):
    """Recover B from A = (1 - q**d)**2 B in one ascending pass for each d."""
    rows = [[] for _ in range(limit + 1)]
    series = [1] + [0] * limit
    for d in range(1, math.isqrt(limit) + 1):
        upto = limit - d * d
        for j in range(d, min(2 * d, upto + 1)):
            series[j] += 2 * series[j - d]
        for j in range(2 * d, upto + 1):
            series[j] += 2 * series[j - d] - series[j - 2 * d]
        for j in range(upto + 1):
            rows[d * d + j].append(series[j])
    return rows


def signed_horner(coeffs, numerator, exponent):
    value = coeffs[-1]
    for position, coeff in enumerate(reversed(coeffs[:-1]), start=1):
        value = (coeff << (position * exponent)) - numerator * value
    return value


def signed_monomial_sum(coeffs, numerator, exponent):
    degree = len(coeffs) - 1
    power = 1
    value = 0
    for i, coeff in enumerate(coeffs):
        value += (coeff * power) << ((degree - i) * exponent)
        power *= -numerator
    return value


def grid_point(index, bits):
    power, fraction = divmod(index, 1 << bits)
    numerator = (1 << bits) + fraction
    if power >= bits:
        return numerator << (power - bits), 0
    return numerator, bits - power


def grid_index(point, bits):
    numerator, exponent = point
    length = numerator.bit_length() - 1
    fraction = (numerator << bits) >> length
    return ((length - exponent - 1) << bits) + fraction


def line_search(coeffs, previous, bits=7):
    chosen = []
    lower = -(max(coeffs).bit_length() + 2) << bits
    for j in range(1, len(coeffs) - 1):
        sign = 1 if j % 2 == 0 else -1
        centres = [grid_index(point, bits) for point in previous[j - 1 : j]]
        # Balance the monomials adjacent to the target term as a secondary guess.
        exponent = coeffs[j + 1].bit_length() // 2 + bits + 1
        numerator = math.isqrt((coeffs[j - 1] << (2 * exponent)) // coeffs[j + 1])
        centres.append(grid_index((numerator, exponent), bits))
        visited = set()
        for delta, centre, direction in product(range(33), centres, (-1, 1)):
            index = centre + direction * delta
            if index <= lower or index in visited:
                continue
            visited.add(index)
            u, e = grid_point(index, bits)
            if sign * signed_horner(coeffs, u, e) > 0:
                chosen.append((u, e))
                lower = index
                break
        else:
            return None
    return chosen


def scan_grid(coeffs, bits):
    # Apply the Cauchy bound to the polynomial and its reversal. Since all
    # coefficients are positive, these integer bounds cover every root modulus.
    largest = max(coeffs)
    lower_power = -((1 + largest // coeffs[0]).bit_length() + 1)
    upper_power = (1 + largest // coeffs[-1]).bit_length() + 1
    chosen = []
    sign = -1
    for index in range(lower_power << bits, upper_power << bits):
        u, e = grid_point(index, bits)
        if sign * signed_horner(coeffs, u, e) > 0:
            chosen.append((u, e))
            if len(chosen) == len(coeffs) - 2:
                return chosen
            sign = -sign
    return None


def find_points(coeffs, previous):
    if len(coeffs) <= 2:
        return []
    for bits in (7, 8, 9):
        points = line_search(coeffs, previous, bits)
        if points is not None:
            return points
    for bits in (7, 8, 9, 10, 11):
        points = scan_grid(coeffs, bits)
        if points is not None:
            return points
    raise ValueError("the dyadic grid failed to separate the signs")


def check_certificate(n, coeffs, points, partition, evaluate=signed_horner):
    if len(coeffs) != math.isqrt(n) or sum(coeffs) != partition:
        raise ValueError(f"polynomial coefficient check failed at n={n}")
    if len(points) != max(0, len(coeffs) - 2):
        raise ValueError(f"witness count mismatch at n={n}")
    prev_u, prev_e = 0, 0
    sign = -1
    for u, e in points:
        if type(u) is not int or type(e) is not int or u <= 0 or e < 0:
            raise ValueError(f"invalid dyadic encoding at n={n}")
        if (prev_u << e) >= (u << prev_e):
            raise ValueError(f"witness order check failed at n={n}")
        if sign * evaluate(coeffs, u, e) <= 0:
            raise ValueError(f"witness sign check failed at n={n}")
        prev_u, prev_e = u, e
        sign = -sign


def generate(path, limit):
    rows = durfee_coefficients(limit)
    partitions = partition_numbers(limit)
    path.parent.mkdir(parents=True, exist_ok=True)
    previous = []
    signs = 0
    orderings = 0
    with path.open("w", encoding="utf-8", newline="\n") as output:
        for n in range(1, limit + 1):
            try:
                points = find_points(rows[n], previous)
                check_certificate(n, rows[n], points, partitions[n])
            except ValueError as exc:
                raise ValueError(f"certificate generation failed at n={n}") from exc
            output.write(json.dumps([n, rows[n], points], separators=(",", ":")) + "\n")
            previous = points
            signs += len(points)
            orderings += max(0, len(points) - 1)
            if n % 100 == 0:
                output.flush()
                print(f"n={n} signs={signs} orderings={orderings}", flush=True)
    print(f"PASS rows={limit} signs={signs} orderings={orderings}", flush=True)


def verify(path, limit, shard_size, shards_out):
    rows = independently_recomputed_coefficients(limit)
    partitions = partition_numbers(limit)
    file_hash = hashlib.sha256()
    shard_hash = hashlib.sha256()
    shard_start = 1
    shard_signs = shard_orderings = 0
    total_signs = total_orderings = seen = 0
    report = ["n_first\tn_last\trows\tsigns\torderings\tpartition_sums\tsha256_raw_jsonl\n"]
    with path.open("rb") as source:
        for expected_n, raw in enumerate(source, start=1):
            n, coeffs, points = json.loads(raw)
            if type(n) is not int or n != expected_n or n > limit:
                raise ValueError(f"invalid or misplaced row at line {expected_n}")
            if coeffs != rows[n] or any(type(c) is not int for c in coeffs):
                raise ValueError(f"independent coefficient recurrence failed at n={n}")
            check_certificate(n, coeffs, points, partitions[n], signed_monomial_sum)
            file_hash.update(raw)
            shard_hash.update(raw)
            shard_signs += len(points)
            shard_orderings += max(0, len(points) - 1)
            seen = n
            if n % shard_size == 0 or n == limit:
                size = n - shard_start + 1
                columns = shard_start, n, size, shard_signs, shard_orderings, size, shard_hash.hexdigest()
                report.append("\t".join(map(str, columns)) + "\n")
                total_signs += shard_signs
                total_orderings += shard_orderings
                shard_start = n + 1
                shard_signs = shard_orderings = 0
                shard_hash = hashlib.sha256()
    if seen != limit:
        raise ValueError(f"missing rows {seen + 1} through {limit}")
    if shards_out is not None:
        with shards_out.open("w", encoding="utf-8", newline="\n") as output:
            output.writelines(report)
    print(f"PASS rows={seen} signs={total_signs} orderings={total_orderings} "
          f"partition_sums={seen} shards={len(report) - 1} sha256={file_hash.hexdigest()}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, help="JSONL file to write or verify")
    parser.add_argument("--limit", type=int, default=6400)
    parser.add_argument("--verify", action="store_true", help="blindly verify an existing JSONL file")
    parser.add_argument("--shard-size", type=int, default=64)
    parser.add_argument("--shards-out", type=Path, help="TSV output for the verification shards")
    args = parser.parse_args()
    if not 1 <= args.limit <= 6400:
        parser.error("--limit must be between 1 and 6400")
    if not 1 <= args.shard_size <= 6400:
        parser.error("--shard-size must be between 1 and 6400")
    if args.shards_out is not None and not args.verify:
        parser.error("--shards-out requires --verify")
    if args.shards_out is not None and args.shards_out.resolve() == args.path.resolve():
        parser.error("the verification report must have a different path from the input")
    if args.verify:
        verify(args.path, args.limit, args.shard_size, args.shards_out)
    else:
        generate(args.path, args.limit)


if __name__ == "__main__":
    main()
