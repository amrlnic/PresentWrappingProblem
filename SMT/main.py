def main(instance, all_solutions=True, python_api=True):
    import z3

    # if python_api:
    from SMT.src.py_sym_model import get_constraints

    presents = len(instance.presents)
    coord_x = [ z3.Int(f'coord_x_{p}') for p in range(1, presents + 1) ]
    coord_y = [ z3.Int(f'coord_y_{p}') for p in range(1, presents + 1) ]
    rotated = [ z3.Bool(f'rotated_{p}') for p in range(1, presents + 1) ]

    dimension_x = [ d for d, _ in instance.presents ]
    dimension_y = [ d for _, d in instance.presents ]
    width, height = instance.size
    presents = len(instance.presents)

    solver = z3.Solver()
   
    for i in range(presents): solver.add(*[ coord_x[i] >= 1, coord_x[i] <= width, coord_y[i] >= 1, coord_y[i] <= height ])

    solver.add(
        *get_constraints(
            coord_x=coord_x,
            coord_y=coord_y,
            rotated=rotated,
            dimension_x=dimension_x,
            dimension_y=dimension_y,
            width=width,
            height=height,
            presents=presents
        )
    )

    # else:
    #     solver = z3.Solver()
    #     problem_solver = z3.parse_smt2_file('SAT/src/PresentWrappingProblem.smt')
    #     solver.add(problem_solver)

    if solver.check() == z3.sat:
        model = solver.model()
        instance.add_solution(
            tuple([
                (
                    model.evaluate(coord_x[i]).as_long(),
                    model.evaluate(coord_y[i]).as_long(),
                    z3.is_true(model.evaluate(rotated[i]))
                )
                for i in range(presents)
            ])
        )