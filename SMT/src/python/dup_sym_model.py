from SMT.src.python.sym_model import Model as SymModel

class Model(SymModel):
    def get_constraints(self):
        constraints = super().get_constraints()

        # Same size presents
        for i in range(self.presents):
            for j in range(i + 1, self.presents):
                constraints.append(
                    self.backend.Or(
                        self.get_dimension_x(self.sorted_areas_indexes[i]) != self.get_dimension_x(self.sorted_areas_indexes[j]),
                        self.get_dimension_y(self.sorted_areas_indexes[i]) != self.get_dimension_y(self.sorted_areas_indexes[j]),
                        self.get_coord_y(self.sorted_areas_indexes[i]) <= self.get_coord_y(self.sorted_areas_indexes[j])
                    )
                )

        return constraints