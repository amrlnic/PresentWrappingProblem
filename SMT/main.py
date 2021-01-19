from z3.z3 import is_true, solve


def configuration(parser):
    parser.add_argument('--model', default='base_model', help='The model to be used in order to build the problem for the solver')
    parser.add_argument('--smt-lib', nargs='?', default=False, const=True, help='True=Uses the smt2-lib standard language, False=Uses python api of z3')

def main(instance, all_solutions=False, smt_lib=False, model='base_model'):
    import z3

    if smt_lib:
        solver = z3.Solver()
        problem_solver = z3.parse_smt2_file(f'SMT/src/smt2/{model}.smt')

        areas = [ w * h for w, h in instance.presents ]
        sorted_areas = sorted(range(len(instance.presents)), key=lambda k: -areas[k])
        solver.add(problem_solver)

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
        solver.add(z3.parse_smt2_string(problem_def))
        
        instance.clear()
        while True:
            if solver.check() == z3.sat:
                model = solver.model()
                solution = { str(k): k for k in model }
                coords = []
                for p in range(1, len(instance.presents) + 1):
                    coords.append((
                        model.eval(solution['coord_x'](p)).as_long(),
                        model.eval(solution['coord_y'](p)).as_long(),
                        z3.is_true(model.eval(solution['rotated'](p))) if 'rotated' in solution else False
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
            solver.add(z3.parse_smt2_string(new_problem))    

    else:
        import importlib
        Model = importlib.import_module(f'SMT.src.python.{model}').Model
        model = Model(instance)
        model.solve(all_solutions=all_solutions)


    