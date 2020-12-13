def main(instance, all_solutions=True):
    import minizinc as mz
    model = mz.Model('CP/src/extra_model.mzn')
    solver = mz.Solver.lookup('gecode')
    mzInstance = mz.Instance(solver, model)

    mzInstance['WIDTH'], mzInstance['HEIGHT'] = instance.size
    mzInstance['PRESENTS'] = len(instance)
    mzInstance['DIMENSION_X'] = [ p[0] for p in instance ]
    mzInstance['DIMENSION_Y'] = [ p[1] for p in instance ]

    results = mzInstance.solve(
        random_seed=42,
        free_search=True,
        optimisation_level=5,
        all_solutions=all_solutions
    )
    if results.status == mz.Status.SATISFIED: results = [ results ]
    elif results.status == mz.Status.ALL_SOLUTIONS: results = [ { 'COORD_X': result.COORD_X, 'COORD_Y': result.COORD_Y } for result in results ]
    else: results = []
    for result in results: instance.add_solution(tuple((x, y)  for x, y in zip(result['COORD_X'], result['COORD_Y'])))