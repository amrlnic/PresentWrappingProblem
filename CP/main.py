def main(instance, all_solutions=True):
    import minizinc as mz
    model = mz.Model('CP/src/duple_rot_sym_model.mzn')
    solver = mz.Solver.lookup('chuffed')
    mzInstance = mz.Instance(solver, model)

    mzInstance['WIDTH'], mzInstance['HEIGHT'] = instance.size
    mzInstance['PRESENTS'] = len(instance)
    mzInstance['DIMENSION_X'] = [ p[0] for p in instance ]
    mzInstance['DIMENSION_Y'] = [ p[1] for p in instance ]

    results = mzInstance.solve(
        random_seed=42,
        free_search=False,
        optimisation_level=1,
        all_solutions=all_solutions
    )
    if results.status == mz.Status.SATISFIED: results = [ results.solution ]
    elif results.status == mz.Status.ALL_SOLUTIONS: results = results.solution
    else: results = []
    for result in results:
        instance.add_solution(
            tuple((x, y, r)  for x, y, r in zip(result.COORD_X, result.COORD_Y, result.ROTATED))
                if hasattr(result, 'ROTATED') else
            tuple((x, y, 0)  for x, y in zip(result.COORD_X, result.COORD_Y))
        )