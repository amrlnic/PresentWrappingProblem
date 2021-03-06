from SAT.src.AbstractModel import AbstractModel

class Model(AbstractModel):
    def get_constraints(self):
        # Two different presents must not overlap
        for i in range(self.presents):
            for j in range(i + 1, self.presents):
                self.add_constraints(self.backend.Not(self.overlaps(i, j)))

        # The present must occupy the correct dimension in the paper
        for i in range(self.presents):
            self.add_constraints(self.correct_dimension(i))

        # The presents must fit the row dimension
        for y in range(self.height):
            self.add_constraints(
                self.backend.And(*[
                    self.backend.Or(*[
                        self.paper[x][y][p] for p in range(self.presents)
                    ]) for x in range(self.width)
                ])        
            )

        # The presents must fit the column dimension
        for x in range(self.width):
            self.add_constraints(
                self.backend.And(*[
                    self.backend.Or(*[
                        self.paper[x][y][p] for p in range(self.presents)
                    ]) for y in range(self.height)
                ])
            )
        
        # A cell of the paper must contain at least one present
        for x in range(self.width):
            for y in range(self.height):
                self.add_constraints(self.backend.Or(*[
                    self.paper[x][y][p] for p in range(self.presents)
                ]))

        return self