def configuration(parser):
    parser.add_argument('--model', default='dup_rot_sym_model', help='The model to be used in order to build the problem for the solver')
    parser.add_argument('--solver', default='chuffed', help='The solver used to carry out the problem')
    parser.add_argument('--optimization', type=int, default=1, help='The optimization level of MiniZinc compiler')
    parser.add_argument('--free-search', nargs='?', default=False, const=True, help='Allow the solver to use Free Search mode')
    parser.add_argument('--random-seed', type=int, default=42, help='The random seed used in the search')

def main(instance, all_solutions=False, model='dup_rot_sym_model', solver='chuffed', optimization=1, free_search=False, random_seed=42):
    import minizinc as mz

    model = mz.Model(f'CP/src/models/{model}.mzn')
    solver = mz.Solver.lookup(solver)
    mzInstance = mz.Instance(solver, model)

    mzInstance['WIDTH'], mzInstance['HEIGHT'] = instance.size
    mzInstance['PRESENTS'] = len(instance.presents)
    mzInstance['DIMENSION_X'] = [ d for d, _ in instance.presents ]
    mzInstance['DIMENSION_Y'] = [ d for _, d in instance.presents ]

    results = mzInstance.solve(
        random_seed=random_seed,
        free_search=free_search,
        optimisation_level=optimization,
        all_solutions=all_solutions
    )

    if results.status == mz.Status.SATISFIED: results = [ results.solution ]
    elif results.status == mz.Status.ALL_SOLUTIONS: results = results.solution
    else: results = []
    for result in results:
        instance.add_solution(
            tuple((x, y, bool(r))  for x, y, r in zip(result.COORD_X, result.COORD_Y, result.ROTATED))
                if hasattr(result, 'ROTATED') else
            tuple((x, y, False)  for x, y in zip(result.COORD_X, result.COORD_Y))
        )