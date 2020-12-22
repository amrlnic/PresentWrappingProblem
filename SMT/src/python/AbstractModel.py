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
        
        self.coord_x = [ self.backend.Int(f'coord_x_{p}') for p in range(1, self.presents + 1) ]
        self.coord_y = [ self.backend.Int(f'coord_y_{p}') for p in range(1, self.presents + 1) ]
        self.rotated = [ self.backend.Bool(f'rotated_{p}') for p in range(1, self.presents + 1) ]

        self.solver = self.backend.Solver()
    
        # Define domains of the coordinates
        for i in range(self.presents):
            self.solver.add(*[
                self.get_coord_x(i) >= 1,
                self.get_coord_x(i) <= self.width,
                self.get_coord_y(i) >= 1,
                self.get_coord_y(i)<= self.height
            ])
        
        self.solver.add(*self.get_constraints())

    def solve(self, all_solutions=False):
        if self.solver.check() == self.backend.sat:
            solution = self.solver.model()
            self.instance.clear()
            self.instance.add_solution(
                tuple([
                    (
                        solution.evaluate(self.coord_x[i]).as_long(),
                        solution.evaluate(self.coord_y[i]).as_long(),
                        self.backend.is_true(solution.evaluate(self.rotated[i]))
                    )
                    for i in range(self.presents)
                ])
            )


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