def configuration(parser):
    models = ('base_model', 'sym_model', 'rot_model', 'rot_sym_model', 'dup_sym_model', 'dup_sym_rot_model')
    backends = ('fast', 'smt', 'python')
    parser.add_argument('--model', default='base_model', choices=models, help='The model to be used in order to build the problem for the solver')
    parser.add_argument('--backend', default='fast', choices=backends, help='The backend used to build the problem: smt - loads a predefined smt-lib template; ' +
    'python - uses z3 python api; fast - generate smt-lib code from z3 python api and load it to the solver.')
    parser.add_argument('--verbose', default=None, type=int, help='The level of verbosity of z3 solver')
    parser.add_argument('--simple', nargs='?', default=False, const=True, help='True=Uses the z3 Simple Solver, False=Uses the standard z3 Solver')

def main(instance, all_solutions=False, backend='fast', model='base_model', time_limit=None, verbose=None, simple=False, on_prepared=None):
    use_smt_lib = backend == 'smt'
    if backend == 'fast':
        import z3_fast_backend
        backend = z3_fast_backend.create(True)
    else:
        import z3
        backend = z3
    
    if verbose is not None: backend.set_param(verbose=verbose)

    if use_smt_lib: solve_smt_lib_model(model, backend, simple, time_limit, verbose, instance, all_solutions, on_prepared)
    else:
        import importlib
        Model = importlib.import_module(f'SMT.src.python.{model}').Model
        model = Model(instance, simple=simple, backend=backend)
        if callable(on_prepared): on_prepared()
        model.solve(all_solutions=all_solutions, time_limit=time_limit)


def solve_smt_lib_model(model, backend, simple, time_limit, verbose, instance, all_solutions, on_prepared):
    solver = backend.SimpleSolver() if simple else backend.Solver()
    if time_limit is not None: solver.set(timeout=time_limit)
    if verbose is not None: solver.set(verbose=verbose)

    areas = [ w * h for w, h in instance.presents ]
    sorted_areas = sorted(range(len(instance.presents)), key=lambda k: -areas[k])
    solver.from_file(f'SMT/src/smt2/{model}.smt')

    problem_def = f'''
        (declare-const width Int)
        (declare-const height Int)
        (declare-const presents Int)
        (declare-fun dimension_x (Int) Int)
        (declare-fun dimension_y (Int) Int)
        (declare-fun sorted_areas_indexes (Int) Int)

        (assert (= width {instance.size[0]}))
        (assert (= height {instance.size[1]}))
        (assert (= presents {len(instance.presents)}))
    '''
    for i, p in enumerate(instance.presents):
        problem_def += f'''
            (assert (= (dimension_x {i + 1}) {p[0]}))
            (assert (= (dimension_y {i + 1}) {p[1]}))
            (assert (= (sorted_areas_indexes {i + 1}) {sorted_areas[i] + 1}))
        '''
    solver.from_string(problem_def)
    if callable(on_prepared): on_prepared()
    
    instance.clear()
    while True:
        if solver.check() == backend.sat:
            model = solver.model()
            solution = { str(k): k for k in model }
            coords = []
            for p in range(1, len(instance.presents) + 1):
                coords.append((
                    model.eval(solution['coord_x'](p)).as_long(),
                    model.eval(solution['coord_y'](p)).as_long(),
                    backend.is_true(model.eval(solution['rotated'](p))) if 'rotated' in solution else False
                ))
            instance.add_solution(tuple(coords), { k: v for k, v in solver.statistics() }) 
        else: break
        if not all_solutions: break
        new_problem = '''
            (declare-fun coord_x (Int) Int)
            (declare-fun coord_y (Int) Int)
            (declare-fun rotated (Int) Bool)
            (assert (not (and
        '''
        for i, (x, y, r) in enumerate(coords):
            new_problem += f'''
                (= (coord_x {i + 1}) {x})
                (= (coord_y {i + 1}) {y})
                {f'(rotated {i + 1})' if r else f'(not (rotated {i + 1}))'}
            '''
        new_problem += '\n)))'
        solver.from_string(new_problem) 