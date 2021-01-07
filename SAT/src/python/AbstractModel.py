import math

class AbstractModel:
    def __init__(self, instance):
        import z3
        self.backend = z3
        self.instance = instance

        self.presents = len(instance.presents)
        self.width, self.height = instance.size

        self.dimension_x = [ d for d, _ in instance.presents ]
        self.dimension_y = [ d for _, d in instance.presents ]

        self.area = self.width * self.height
        self.areas = [ w * h for w, h in zip(self.dimension_x, self.dimension_y) ]
        
        self.paper = [
            [
                [
                    self.backend.Bool(f'paper_{x}_{y}_{p}')
                    for p in range(1, self.presents + 1)
                ] for y in range(1, self.height + 1)
            ] for x in range(1, self.width + 1) 
        ]

        self.rotated = [ z3.Bool(f'rotated_{p}') for p in range(1, self.presents + 1) ]

        self.solver = self.backend.Solver()
        
        self.solver.add(*self.get_constraints())

    def solve(self, all_solutions=False):
        self.instance.clear()
        while True:
            if self.solver.check() == self.backend.sat:
                solution = self.solver.model()
                solution = { str(k): self.backend.is_true(solution[k]) for k in solution }
                solved = tuple([ self.find_present_coordinates(solution, p) for p in range(1, self.presents + 1) ])
                self.instance.add_solution(solved)
                self.solver.add(
                    self.backend.Not(
                        self.backend.And(
                            *([
                                self.paper[x][y][p] == solution[f'paper_{x + 1}_{y + 1}_{p + 1}']
                                for x in range(self.width)
                                for y in range(self.height)
                                for p in range(self.presents)
                            ]  +
                            ([ self.rotated[p] == solution[f'rotated_{p + 1}'] for p in range(self.presents) ] if 'rotated_1' in solution else []))
                        )
                    )
                )
            else: break
            if not all_solutions: break

    def find_present_coordinates(self, solution, present):
        for x in range(1, self.width + 1):
            for y in range(1, self.height + 1):
                if solution.get(f'paper_{x}_{y}_{present}', False):
                    return (x, y, solution.get(f'rotated_{present}', False))
        return (0, 0, False)


    def get_dimension_x(self, index):
        return self.dimension_x[index]
        
    def get_dimension_y(self, index):
        return self.dimension_y[index]


    def overlaps(self, present_1, present_2):
        constraints = []
        for x in range(self.width):
            for y in range(self.height):
                constraints.append(
                    self.backend.And(
                        self.paper[x][y][present_1],
                        self.paper[x][y][present_2]
                    )
                )

        return self.backend.Or(*constraints)

    def correct_dimension(self, present):
        constraints = []
        p_width, p_height = self.get_dimension_x(present), self.get_dimension_y(present)
        for x0 in range(self.width - p_width + 1):
            for y0 in range(self.height - p_height + 1):
                constraints += [
                    self.backend.And(*[
                        self.paper[x][y][present]
                            if x in range(x0, x0 + p_width) and y in range(y0, y0 + p_height)
                            else self.backend.Not(self.paper[x][y][present])
                            for x in range(0, self.width)
                            for y in range(0, self.height)
                    ])
                ]

        return self.backend.Or(*constraints)

    def get_constraints(self):
        return []