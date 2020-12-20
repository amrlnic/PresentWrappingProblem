import z3

def overlaps(
    # square 1
    l1x, r1x, l1y, r1y,
    # square 2
    l2x, r2x, l2y, r2y
):
    return z3.And(
        z3.Not(z3.Or(l1x >= r2x, l2x >= r1x)),
        z3.Not(z3.Or(r1y <= l2y, r2y <= l1y))
    )

def get_constraints(coord_x, coord_y, rotated, dimension_x, dimension_y, width, height, presents):
    constraints = []
    area = width * height
    areas = [ w * h for w, h in zip(dimension_x, dimension_y) ]

    for i in range(presents):
        constraints += [ coord_x[i] >= 1, coord_x[i] <= width, coord_y[i] >= 1, coord_y[i] <= height ]

    # The present must be in the paper sheet
    for i in range(presents):
        constraints.append(
            z3.And(
                (coord_x[i] + dimension_x[i]) <= (width + 1),
                (coord_y[i] + dimension_y[i]) <= (height + 1)
            )
        )

    # Two different presents must not overlap
    for i in range(presents):
        for j in range(i + 1, presents):
            constraints.append(
                z3.Not(
                    overlaps(
                        # present 1
                        coord_x[i], coord_x[i] + dimension_x[i],
                        coord_y[i], coord_y[i] + dimension_y[i],
                        # present 2
                        coord_x[j], coord_x[j] + dimension_x[j],
                        coord_y[j], coord_y[j] + dimension_y[j]
                    )
                )
            )

    # The presents must fit the row dimension
    for y in range(1, height + 1):
        constraints.append(
            z3.Sum([
                z3.If(
                    z3.And(y >= coord_y[i], y < coord_y[i] + dimension_y[i]),
                    dimension_x[i],
                    0
                )
                for i in range(presents)
            ]) == width
        )

    # The presents must fit the column dimension
    for x in range(1, width + 1):
        constraints.append(
            z3.Sum([
                z3.If(
                    z3.And(x >= coord_x[i], x < coord_x[i] + dimension_x[i]),
                    dimension_y[i],
                    0
                )
                for i in range(presents)
            ]) == height
        )

    # The total area of the presents must fit the area of the paper
    constraints.append(z3.Sum(areas) == area)

    return constraints