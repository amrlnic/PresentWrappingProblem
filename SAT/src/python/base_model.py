from SAT.src.python.AbstractModel import AbstractModel

class Model(AbstractModel):
    def get_constraints(self):
        constraints = []

        # Two different presents must not overlap
        for i in range(self.presents):
            for j in range(i + 1, self.presents):
                constraints.append(self.backend.Not(self.overlaps(i, j)))

        # The present must occupy the correct dimension in the paper
        for i in range(self.presents):
            constraints.append(self.correct_dimension(i))

        # The presents must fit the row dimension
        for y in range(self.height):
            constraints.append(
                self.backend.And(*[
                    self.backend.Or(*[
                        self.paper[x][y][p] for p in range(self.presents)
                    ]) for x in range(self.width)
                ])        
            )

        # The presents must fit the column dimension
        for x in range(self.width):
            constraints.append(
                self.backend.And(*[
                    self.backend.Or(*[
                        self.paper[x][y][p] for p in range(self.presents)
                    ]) for y in range(self.height)
                ])
            )
        
        # A cell of the paper must contain at least one present
        for x in range(self.width):
            for y in range(self.height):
                constraints.append(self.backend.Or(*[
                    self.paper[x][y][p] for p in range(self.presents)
                ]))

        return constraints