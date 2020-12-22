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
                    self.backend.Bool(f'present_{p}_{x}_{y}')
                    for p in range(1, self.presents + 1)
                ] for y in range(1, self.height + 1)
            ] for x in range(1, self.width + 1) 
        ]

        self.rotated = [ z3.Bool(f'rotated_{p}') for p in range(1, self.presents + 1) ]

        # valutare se mettere constraint almeno uno True per ogni coordinata

        self.solver = self.backend.Solver()
        
        self.solver.add(*self.get_constraints())

    def solve(self, all_solutions=False):
        if self.solver.check() == self.backend.sat:
            solution = self.solver.model()
            self.instance.clear()


            self.instance.add_solution(
                tuple([ self.find_present_coordinates(p) for p in range(self.presents) ])
            )

    def find_present_coordinates(self, present):
        for x in range(self.width):
            for y in range(self.height):
                if self.backend.is_true(self.paper[x][y][present]):
                    return (x + 1, y + 1, self.backend.is_true(self.rotated[present]))
        return (0, 0, False)


    # def get_coord_x(self, index):
    #     return self.coord_x[index]

    # def get_dimension_x(self, index):
    #     return self.dimension_x[index]
    
    # def get_coord_y(self, index):
    #     return self.coord_y[index]
    
    # def get_dimension_y(self, index):
    #     return self.dimension_y[index]


    def overlaps(self, index_1, index_2):
        constraints = []
        for x in range(self.width):
            for y in range(self.height):
                constraints.append(
                    self.backend.And(
                        self.paper[x][y][index_1],
                        self.paper[x][y][index_2]
                    )
                )

        return self.backend.Or(*constraints)
    
    def get_constraints(self):
        return []