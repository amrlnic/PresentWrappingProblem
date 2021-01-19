def configuration(parser):
    parser.add_argument('--model', default='base_model', help='The model to be used in order to build the problem for the solver')

def main(instance, all_solutions=False, model='base_model'):
    import importlib
    Model = importlib.import_module(f'SAT.src.{model}').Model
    model = Model(instance)
    model.solve(all_solutions=all_solutions)


    