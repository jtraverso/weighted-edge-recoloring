"""Cell biadjacency of the rectangular example in Figure 1, shifted by 7I."""

from itertools import product

from certo import MatrixSpec


def spec():
    cells = list(product(range(8), range(4)))
    shifted = [
        [
            int(row == other_row or col == other_col)
            - 7 * int((row, col) == (other_row, other_col))
            for other_row, other_col in cells
        ]
        for row, col in cells
    ]
    return MatrixSpec(matrix=shifted, question="inertia", title="8 by 4 grid, shifted by 7I")
