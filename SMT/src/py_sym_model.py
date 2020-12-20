import z3
# import the base model constraints (see also base_model.py)
from SMT.src.base_model import get_constraints as base_model_constraints

def get_constraints(coord_x, coord_y, rotated, dimension_x, dimension_y, width, height, presents):
    constraints = base_model_constraints(
        coord_x=coord_x,
        coord_y=coord_y,
        rotated=rotated,
        dimension_x=dimension_x,
        dimension_y=dimension_y,
        width=width,
        height=height,
        presents=presents
    )

    areas = [ w * h for w, h in zip(dimension_x, dimension_y) ]

    # === SYMMETRY BREACKING ===
    sorted_areas_indexes = sorted(range(presents), key=lambda k: -areas[k])

    # The biggest present must stay in (1, 1)
    constraints.append(coord_x[sorted_areas_indexes[0]] == 1)
    constraints.append(coord_y[sorted_areas_indexes[0]] == 1)

    # The bigger the present the lesser the X coordinate
    for i in range(presents):
        for j in range(i + 1, presents):
            constraints.append(
                z3.Implies(
                    coord_y[sorted_areas_indexes[i]] == coord_y[sorted_areas_indexes[j]],
                    coord_x[sorted_areas_indexes[i]] < coord_x[sorted_areas_indexes[j]]
                )
            )

    return constraints