import z3, tempfile

def string_bool(boolean): return ('true' if boolean else 'false') if type(boolean) is bool else str(boolean)
def string_expression(operator, operands): return f'({operator} {str.join(" ", [ string_bool(o) for o in operands ])})'

class B_Solver:
    def __init__(self, context, solver=None):
        self.__context = context
        self.__solver = solver or z3.Solver()

    def add(self, *constraints):
        for c in constraints: self.__context._Context__writeline(f'(assert {c})')

    def check(self):
        self.__calc_constraints()
        return self.__solver.check()

    def model(self): return self.__solver.model()
    def assertions(self): return self.__solver.assertions()
    def statistics(self): return self.__solver.statistics()
    def set(self, *args, **kwargs): self.__solver.set(*args, **kwargs)

    def from_file(self, filename): self.__solver.from_file(filename)
    def from_string(self, smt_string): self.__solver.from_string(smt_string)

    def __calc_constraints(self):
        smt_string = self.__context._Context__load()
        self.__solver.from_string(smt_string)
        return self

class B_Object:
    def __eq__(self, other): return B_Expression('=', [ self, other ])
    def __gt__(self, other): return B_Expression('>', [ self, other ])
    def __lt__(self, other): return B_Expression('<', [ self, other ])
    def __ge__(self, other): return B_Expression('>=', [ self, other ])
    def __le__(self, other): return B_Expression('<=', [ self, other ])
    def __add__(self, other): return B_Expression('+', [ self, other ])

class B_Variable(B_Object):
    def __init__(self, name, z3_ref):
        self.__name = name
        self.__reference = z3_ref
    
    def __str__(self): return self.__name
    def as_ast(self): return self.__reference.as_ast()

class B_Expression(B_Object):
    def __init__(self, operator, operands):
        self.__operator = operator
        self.__operands = operands

    def __str__(self): return string_expression(self.__operator, self.__operands)

class Context:
    sat = z3.sat

    def __init__(self, buffer=None):
        self.__buffer = buffer or tempfile.TemporaryFile()

    def __del__(self):
        self.__buffer.close()

    def __load(self):
        self.__buffer.seek(0)
        return self.__buffer.read()
    
    def __write(self, text):
        self.__buffer.write(str.encode(text))
        return self
    
    def __writeline(self, text): return self.__write(text + '\n')

    def __create_var(self, name, mapped_type, z3_ref):
        self.__writeline(f'(declare-const {name} {mapped_type})')
        return B_Variable(name, z3_ref)
    
    def Bool(self, name): return self.__create_var(name, 'Bool', z3.Bool(name))
    def Int(self, name): return self.__create_var(name, 'Int', z3.Int(name))

    def Solver(self): return B_Solver(self, z3.Solver())
    def SimpleSolver(self): return B_Solver(self, z3.SimpleSolver())

    def is_true(self, value): return z3.is_true(value)

    def set_param(self, *args, **kwargs): z3.set_param(*args, **kwargs)

    def Implies(self, implicator, implier): return self.__compute_expression('=>', [ implicator, implier ])
    def Not(self, neg): return self.__compute_expression('not', [ neg ])
    def And(self, *ands): return self.__compute_expression('and', ands)
    def Or(self, *ors): return self.__compute_expression('or', ors)
    def Sum(self, ops): return self.__compute_expression('+', ops)
    def If(self, if_term, then_term, else_term): return self.__compute_expression('ite', [ if_term, then_term, else_term ])

    def __compute_expression(self, operator, operands): raise NotImplementedError()

class SMTContext(Context):
    def _Context__compute_expression(self, operator, operands): return B_Expression(operator, operands)

class SATContext(Context):
    def _Context__compute_expression(self, operator, operands): return string_expression(operator, operands)


def create(smt, buffer=None): return SMTContext(buffer) if smt else SATContext(buffer)