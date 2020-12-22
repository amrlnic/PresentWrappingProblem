def configuration(parser):
    parser.add_argument('--model', default='base_model', help='The model to be used in order to build the problem for the solver')
    parser.add_argument('--smt-lib', nargs='?', default=False, const=True, help='True=Uses the smt2-lib standard language, False=Uses python api of z3')

def main(instance, all_solutions=False, smt_lib=False, model='base_model'):
    import z3

    if smt_lib:
        solver = z3.Solver()
        problem_solver = z3.parse_smt2_file(f'SMT/src/smt2/{model}.smt')
        solver.add(problem_solver)

        # if solver.check() == z3.sat:
        #     model = solver.model()
        #     instance.clear()
        #     instance.add_solution(
        #         tuple([
        #             (
        #                 model.evaluate(coord_x[i]).as_long(),
        #                 model.evaluate(coord_y[i]).as_long(),
        #                 z3.is_true(model.evaluate(rotated[i]))
        #             )
        #             for i in range(presents)
        #         ])
        #     )
    else:
        import importlib
        Model = importlib.import_module(f'SMT.src.python.{model}').Model
        model = Model(instance)
        model.solve(all_solutions=all_solutions)


    