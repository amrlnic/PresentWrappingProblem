def main(instance, all_solutions=True):
    import z3
    solver = z3.Solver()
    problem_solver = z3.parse_smt2_file('SAT/src/PresentWrappingProblem.smt')
    solver.add(problem_solver)

    if solver.check() == z3.sat:
        M = solver.model()
        values = { k: M[k] for k in M }
        print(values)