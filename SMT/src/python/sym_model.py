# import the base model constraints (see also base_model.py)
from SMT.src.python.base_model import Model as BaseModel

class Model(BaseModel):
    def get_constraints(self):
        # === SYMMETRY BREACKING ===
        self.sorted_areas_indexes = sorted(range(self.presents), key=lambda k: -self.areas[k])

        # The biggest present must stay in (1, 1)
        self.add_constraints(self.get_coord_x(self.sorted_areas_indexes[0]) == 1)
        self.add_constraints(self.get_coord_y(self.sorted_areas_indexes[0]) == 1)

        # The bigger the present the lesser the X coordinate
        for i in range(self.presents):
            for j in range(i + 1, self.presents):
                self.add_constraints(
                    self.backend.Implies(
                        self.get_coord_y(self.sorted_areas_indexes[i]) == self.get_coord_y(self.sorted_areas_indexes[j]),
                        self.get_coord_x(self.sorted_areas_indexes[i]) < self.get_coord_x(self.sorted_areas_indexes[j])
                    )
                )

        # Adding basic constraints
        return super().get_constraints()