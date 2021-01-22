class AbstractModel:
    def __init__(self, instance, simple=False):
        import z3
        self.backend = z3
        self.instance = instance

        self.presents = len(instance.presents)
        self.width, self.height = instance.size

        self.dimension_x = [ d for d, _ in instance.presents ]
        self.dimension_y = [ d for _, d in instance.presents ]
        
        self.area = self.width * self.height
        self.areas = [ w * h for w, h in zip(self.dimension_x, self.dimension_y) ]
        
        self.coord_x = [ self.backend.Int(f'coord_x_{p}') for p in range(1, self.presents + 1) ]
        self.coord_y = [ self.backend.Int(f'coord_y_{p}') for p in range(1, self.presents + 1) ]
        self.rotated = [ self.backend.Bool(f'rotated_{p}') for p in range(1, self.presents + 1) ]

        self.solver = self.backend.SimpleSolver() if simple else self.backend.Solver()
    
        # Define domains of the coordinates
        for i in range(self.presents):
            self.solver.add(*[
                self.get_coord_x(i) >= 1,
                self.get_coord_x(i) <= self.width,
                self.get_coord_y(i) >= 1,
                self.get_coord_y(i) <= self.height
            ])
        
        self.get_constraints()

    def add_constraints(self, *constraints):
        self.solver.add(*constraints)
        return self

    def solve(self, all_solutions=False, time_limit=None):
        if time_limit is not None: self.solver.set(timeout=time_limit)
        self.instance.clear()
        while True:
            if self.solver.check() == self.backend.sat:
                solution = self.solver.model()
                solution = tuple([
                        (
                            solution.evaluate(self.coord_x[i]).as_long(),
                            solution.evaluate(self.coord_y[i]).as_long(),
                            self.backend.is_true(solution.evaluate(self.rotated[i]))
                        )
                        for i in range(self.presents)
                    ])
                stat = { k: v for k, v in self.solver.statistics() }
                self.instance.add_solution(solution, stat)
                self.solver.add(
                    self.backend.Not(
                        self.backend.And(*[
                            self.backend.And(
                                self.coord_x[i] == solution[i][0],
                                self.coord_y[i] == solution[i][1],
                                self.rotated[i] == solution[i][2]
                            ) for i in range(self.presents)
                        ])
                    )
                )
            else: break
            if not all_solutions: break

    def get_coord_x(self, index):
        return self.coord_x[index]

    def get_dimension_x(self, index):
        return self.dimension_x[index]
    
    def get_coord_y(self, index):
        return self.coord_y[index]
    
    def get_dimension_y(self, index):
        return self.dimension_y[index]

    
    def overlaps(self, index_1, index_2):
        # present 1
        l1x = self.get_coord_x(index_1)
        r1x = l1x + self.get_dimension_x(index_1)
        l1y = self.get_coord_y(index_1)
        r1y = l1y + self.get_dimension_y(index_1)
        # present 2
        l2x = self.get_coord_x(index_2)
        r2x = l2x + self.get_dimension_x(index_2)
        l2y = self.get_coord_y(index_2)
        r2y = l2y + self.get_dimension_y(index_2)

        return self.backend.And(
            self.backend.Not(self.backend.Or(l1x >= r2x, l2x >= r1x)),
            self.backend.Not(self.backend.Or(r1y <= l2y, r2y <= l1y))
        )
    
    def get_constraints(self):
        return []