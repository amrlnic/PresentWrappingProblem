from SMT.src.python.base_model import Model as BaseModel

class Model(BaseModel):
    def get_dimension_x(self, index):
        return self.backend.If(self.rotated[index], self.dimension_y[index], self.dimension_x[index])

    def get_dimension_y(self, index):
        return self.backend.If(self.rotated[index], self.dimension_x[index], self.dimension_y[index])