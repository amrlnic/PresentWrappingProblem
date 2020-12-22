from SMT.src.python.duple_sym_model import Model as DupleSymModel
from SMT.src.python.rot_model import Model as RotModel

# (DupleSymModel = (SymModel = BaseModel + Sym)) + (RotModel)
class Model(DupleSymModel, RotModel): pass