from SMT.src.python.AbstractModel import AbstractModel

class Model(AbstractModel):
    def get_constraints(self):
        # The present must be in the paper sheet
        for i in range(self.presents):
            self.add_constraints(
                self.backend.And(
                    (self.get_coord_x(i) + self.get_dimension_x(i)) <= (self.width + 1),
                    (self.get_coord_y(i) + self.get_dimension_y(i)) <= (self.height + 1)
                )
            )

        # Two different presents must not overlap
        for i in range(self.presents):
            for j in range(i + 1, self.presents):
                self.add_constraints(self.backend.Not(self.overlaps(i, j)))

        # The presents must fit the row dimension
        for y in range(1, self.height + 1):
            self.add_constraints(
                self.backend.Sum([
                    self.backend.If(
                        self.backend.And(y >= self.get_coord_y(i), y < self.get_coord_y(i) + self.get_dimension_y(i)),
                        self.get_dimension_x(i),
                        0
                    )
                    for i in range(self.presents)
                ]) == self.width
            )

        # The presents must fit the column dimension
        for x in range(1, self.width + 1):
            self.add_constraints(
                self.backend.Sum([
                    self.backend.If(
                        self.backend.And(x >= self.get_coord_x(i), x < self.get_coord_x(i) + self.get_dimension_x(i)),
                        self.get_dimension_y(i),
                        0
                    )
                    for i in range(self.presents)
                ]) == self.height
            )

        # The total area of the presents must fit the area of the paper
        self.add_constraints(self.backend.Sum(self.areas) == self.area)

        return self