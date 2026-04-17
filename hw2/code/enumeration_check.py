from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from math import comb
from pathlib import Path
import csv

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


ROOT = Path(__file__).resolve().parents[1]
FIGURES = ROOT / "figures"
FIGURES.mkdir(parents=True, exist_ok=True)


def runs_of_ones(bits: tuple[int, ...]) -> int:
    runs = 0
    prev = 0
    for bit in bits:
        if bit == 1 and prev == 0:
            runs += 1
        prev = bit
    return runs


def is_part_a_pattern(bits: tuple[int, ...]) -> bool:
    return runs_of_ones(bits) <= 2


def is_prefix_suffix_pattern(bits: tuple[int, ...]) -> bool:
    n = len(bits)
    if all(bit == 0 for bit in bits):
        return True

    ones = [i for i, bit in enumerate(bits) if bit == 1]
    if not ones:
        return True

    first = ones[0]
    last = ones[-1]
    if all(bits[i] == 1 for i in range(first, last + 1)):
        return True

    left = 0
    while left < n and bits[left] == 1:
        left += 1
    right = n - 1
    while right >= 0 and bits[right] == 1:
        right -= 1

    if left == 0 or right == n - 1:
        return False

    return all(bits[i] == 0 for i in range(left, right + 1))


def is_part_b_pattern(bits: tuple[int, ...]) -> bool:
    return is_prefix_suffix_pattern(bits)


@dataclass
class GrowthRow:
    n: int
    part_a_formula: int
    part_a_enum: int
    part_b_formula: int
    part_b_enum: int


def part_a_formula(n: int) -> int:
    return 1 + comb(n + 1, 2) + comb(n + 1, 4)


def part_b_formula(n: int) -> int:
    return n * n - n + 2


def enumerate_counts(n: int) -> GrowthRow:
    strings = list(product((0, 1), repeat=n))
    part_a_count = sum(1 for bits in strings if is_part_a_pattern(bits))
    part_b_count = sum(1 for bits in strings if is_part_b_pattern(bits))
    return GrowthRow(
        n=n,
        part_a_formula=part_a_formula(n),
        part_a_enum=part_a_count,
        part_b_formula=part_b_formula(n),
        part_b_enum=part_b_count,
    )


def write_csv(rows: list[GrowthRow]) -> Path:
    output = FIGURES / "small_n_growth.csv"
    with output.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.writer(handle)
        writer.writerow(
            [
                "n",
                "part_a_formula",
                "part_a_enum",
                "part_b_formula",
                "part_b_enum",
            ]
        )
        for row in rows:
            writer.writerow(
                [
                    row.n,
                    row.part_a_formula,
                    row.part_a_enum,
                    row.part_b_formula,
                    row.part_b_enum,
                ]
            )
    return output


def write_plot(rows: list[GrowthRow]) -> Path:
    n_values = [row.n for row in rows]
    a_values = [row.part_a_formula for row in rows]
    b_values = [row.part_b_formula for row in rows]

    fig, ax = plt.subplots(figsize=(8, 5))
    ax.plot(n_values, a_values, "o-", label=r"Part A: $1+\binom{n+1}{2}+\binom{n+1}{4}$")
    ax.plot(n_values, b_values, "s-", label=r"Part B: $n^2-n+2$")
    ax.set_xlabel("n")
    ax.set_ylabel("Growth count")
    ax.set_title("Small-n growth-function verification")
    ax.set_xticks(n_values)
    ax.grid(True, alpha=0.3)
    ax.legend()
    fig.tight_layout()

    output = FIGURES / "small_n_growth.png"
    fig.savefig(output, dpi=140, bbox_inches="tight")
    plt.close(fig)
    return output


def main() -> None:
    rows = [enumerate_counts(n) for n in range(1, 7)]
    for row in rows:
        if row.part_a_formula != row.part_a_enum:
            raise ValueError(f"Part A mismatch at n={row.n}: {row}")
        if row.part_b_formula != row.part_b_enum:
            raise ValueError(f"Part B mismatch at n={row.n}: {row}")

    csv_path = write_csv(rows)
    plot_path = write_plot(rows)

    print("Verified rows:")
    for row in rows:
        print(
            f"n={row.n}: "
            f"A={row.part_a_enum} (formula {row.part_a_formula}), "
            f"B={row.part_b_enum} (formula {row.part_b_formula})"
        )
    print(f"CSV written to: {csv_path}")
    print(f"Plot written to: {plot_path}")


if __name__ == "__main__":
    main()
