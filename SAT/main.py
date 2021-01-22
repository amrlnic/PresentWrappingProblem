def configuration(parser):
    parser.add_argument('--model', default='base_model', help='The model to be used in order to build the problem for the solver')
    parser.add_argument('--verbose', default=None, type=int, help='The level of verbosity of z3 solver')
    parser.add_argument('--simple', nargs='?', default=False, const=True, help='True=Uses the z3 Simple Solver, False=Uses the standard z3 Solver')

def main(instance, all_solutions=False, model='base_model', time_limit=None, verbose=None, simple=False):
    import z3, importlib
    if verbose is not None: z3.set_param(verbose=verbose)
    Model = importlib.import_module(f'SAT.src.{model}').Model
    model = Model(instance, simple=simple)
    model.solve(all_solutions=all_solutions, time_limit=time_limit)


    