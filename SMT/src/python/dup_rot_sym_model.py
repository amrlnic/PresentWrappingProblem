from SMT.src.python.dup_sym_model import Model as DupleSymModel
from SMT.src.python.rot_model import Model as RotModel

# (DupleSymModel = (SymModel = BaseModel + Sym)) + (RotModel)
class Model(DupleSymModel, RotModel): pass