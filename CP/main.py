from types import coroutine


def configuration(parser):
    parser.add_argument('--model', default='dup_rot_sym_model', help='The model to be used in order to build the problem for the solver')
    parser.add_argument('--solver', default='chuffed', help='The solver used to carry out the problem')
    parser.add_argument('--optimization', type=int, default=1, help='The optimization level of MiniZinc compiler')
    parser.add_argument('--no-free-search', nargs='?', default=False, const=True, help='Disallow the solver to use Free Search mode')
    parser.add_argument('--random-seed', type=int, default=42, help='The random seed used in the search')


def resolve(coroutine):
    import sys, asyncio
    if sys.version_info >= (3, 7):
        if sys.platform == "win32": asyncio.set_event_loop_policy(asyncio.WindowsProactorEventLoopPolicy())
        return asyncio.run(coroutine)
    else:
        if sys.platform == "win32": loop = asyncio.ProactorEventLoop()
        else: loop = asyncio.events.new_event_loop()
        try:
            asyncio.events.set_event_loop(loop)
            return loop.run_until_complete(coroutine)
        finally:
            asyncio.events.set_event_loop(None)
            loop.close()


def main(instance, all_solutions=False, model='dup_rot_sym_model', solver='chuffed', optimization=1, no_free_search=False, random_seed=42, time_limit=None):
    import minizinc as mz

    model = mz.Model(f'CP/src/models/{model}.mzn')
    solver = mz.Solver.lookup(solver)
    mzInstance = mz.Instance(solver, model)

    mzInstance['WIDTH'], mzInstance['HEIGHT'] = instance.size
    mzInstance['PRESENTS'] = len(instance.presents)
    mzInstance['DIMENSION_X'] = [ d for d, _ in instance.presents ]
    mzInstance['DIMENSION_Y'] = [ d for _, d in instance.presents ]

    async def resolve_coroutine():
        import asyncio
        try:
            return await asyncio.wait_for(mzInstance.solve_async(
                random_seed=random_seed,
                free_search=not no_free_search,
                optimisation_level=optimization,
                all_solutions=all_solutions
            ), timeout=float(time_limit) / 1000 if time_limit is not None else None)
        except asyncio.TimeoutError: pass
    
    results = resolve(resolve_coroutine())
    
    if results is not None:
        stats =  results.statistics

        if results.status == mz.Status.SATISFIED: results = [ results.solution ]
        elif results.status == mz.Status.ALL_SOLUTIONS: results = results.solution
        else: results = []
        for result in results:
            instance.add_solution(
                tuple((x, y, bool(r))  for x, y, r in zip(result.COORD_X, result.COORD_Y, result.ROTATED))
                    if hasattr(result, 'ROTATED') else
                tuple((x, y, False)  for x, y in zip(result.COORD_X, result.COORD_Y)),
                stats
            )