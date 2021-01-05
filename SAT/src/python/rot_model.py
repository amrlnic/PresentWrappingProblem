from SAT.src.python.base_model import Model as BaseModel

class Model(BaseModel):

    def correct_dimension(self, present):
        constraints_direct = []
        constraints_rotated = []
        p_width, p_height = self.get_dimension_x(present), self.get_dimension_y(present)
    
        for x0 in range(self.width - p_width + 1):
            for y0 in range(self.height - p_height + 1):
                constraints_direct += [
                    self.backend.And(*[
                        self.paper[x][y][present]
                            if x in range(x0, x0 + p_width) and y in range(y0, y0 + p_height)
                            else self.backend.Not(self.paper[x][y][present])
                            for x in range(0, self.width)
                            for y in range(0, self.height)
                    ])
                ]

        for x0 in range(self.width - p_height + 1):
            for y0 in range(self.height - p_width + 1):
                constraints_rotated += [
                    self.backend.And(*[
                        self.paper[x][y][present]
                            if x in range(x0, x0 + p_height) and y in range(y0, y0 + p_width)
                            else self.backend.Not(self.paper[x][y][present])
                            for x in range(0, self.width)
                            for y in range(0, self.height)
                    ])
                ]

        return self.backend.Or(
                self.backend.And(self.rotated[present], self.backend.Or(*constraints_rotated)),
                self.backend.And(self.backend.Not(self.rotated[present]), self.backend.Or(*constraints_direct))
            )