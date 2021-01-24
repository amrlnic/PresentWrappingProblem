def configuration(parser):
    models = ('base_model', 'rot_model')
    backends = ('fast', 'python')
    parser.add_argument('--model', default='base_model', choices=models, help='The model to be used in order to build the problem for the solver')
    parser.add_argument('--backend', default='fast', choices=backends, help='The backend used to build the problem: python - uses z3 python api; fast - generate smt-lib code from z3 python api and load it to the solver.')
    parser.add_argument('--verbose', default=None, type=int, help='The level of verbosity of z3 solver')
    parser.add_argument('--simple', nargs='?', default=False, const=True, help='True=Uses the z3 Simple Solver, False=Uses the standard z3 Solver')

def main(instance, all_solutions=False, model='base_model', time_limit=None, backend='fast', verbose=None, simple=False, on_prepared=None):
    import importlib
    
    if backend == 'fast':
        import z3_fast_backend
        backend = z3_fast_backend.create(False)
    else:
        import z3
        backend = z3

    if verbose is not None: backend.set_param(verbose=verbose)
    Model = importlib.import_module(f'SAT.src.{model}').Model
    model = Model(instance, simple=simple, backend=backend)
    if callable(on_prepared): on_prepared()
    model.solve(all_solutions=all_solutions, time_limit=time_limit)


    