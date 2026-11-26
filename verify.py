"""Check the formulas from the local definitions, using only Python's standard library."""

from functools import cache


def tilings(side, ordinary):
    """Count perfect matchings with an exact budget for pairs sharing an edge."""
    cell_count = side * side
    choices = []
    for cell in range(cell_count):
        row, column = divmod(cell, side)
        forward = []
        for dr, dc in ((0, 1), (1, -1), (1, 0), (1, 1)):
            if row + dr < side and 0 <= column + dc < side:
                distance = dr * side + dc
                forward.append((1 << distance, int(dr == 0 or dc == 0)))
        choices.append(forward)

    @cache
    def count(cell, mask, remaining):
        if cell == cell_count:
            return int(remaining == 0 and mask == 0)
        if mask & 1:
            return count(cell + 1, mask >> 1, remaining)
        total = 0
        for bit, cost in choices[cell]:
            if cost <= remaining and not mask & bit:
                total += count(cell + 1, (mask | bit) >> 1, remaining - cost)
        return total

    result = count(0, 0, ordinary)
    count.cache_clear()
    return result


def populations(last):
    """Propagate directly on a brick-wall drawing of the degree-three honeycomb graph."""
    lit = {(0, 0)}
    result = [1]
    for _ in range(last):
        next_lit = set()
        for x, y in lit:
            vertical = 1 if (x + y) % 2 == 0 else -1
            next_lit.symmetric_difference_update(((x - 1, y), (x + 1, y), (x, y + vertical)))
        lit = next_lit
        result.append(len(lit))
    return result


def check(label, got, expected):
    if got != expected:
        raise ValueError(f"{label}: got {got}, expected {expected}")


def main():
    for n in range(1, 7):
        got = (tilings(2 * n, 0), tilings(2 * n, 2))
        check(f"board side {2*n}", got, (1, n * n * (n + 1)))
        print(f"{2*n} x {2*n}: {got}")

    last = 255
    a = populations(last)
    check("initial populations", a[:8], [1, 3, 7, 9, 7, 21, 25, 27])
    for t in range((last - 1) // 2 + 1):
        check(f"a(2t+1), t={t}", a[2*t+1], 3*a[t])
    for t in range(last // 4 + 1):
        check(f"a(4t), t={t}", a[4*t], a[2*t])
    for t in range((last - 2) // 8 + 1):
        check(f"a(8t+2), t={t}", a[8*t+2], 3*a[4*t] + 4*a[2*t])
    for t in range((last - 6) // 8 + 1):
        check(f"a(8t+6), t={t}", a[8*t+6], 3*a[4*t+2] + 4*a[2*t])
    print(f"All four recurrences pass through generation {last}.")


if __name__ == "__main__":
    main()
