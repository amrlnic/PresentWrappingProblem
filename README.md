# ***Present Wrapping Problem - Command Line Interface***
# Main Program

### **Command:**

`python main.py [arguments]`

### **Arguments:**
| Argument | Default | Description |
|:---------|:--------|:------------|
| `-h, --help` | --- | show help message and exit |
| `-m {CP,SAT,SMT}, --method {CP,SAT,SMT}` | REQUIRED | Method used to carry out the solution(s), possible: `CP`, `SAT`, `SMT` |
| `-i INPUT, --input INPUT` | `./instaces` | Files or directories where to locate the problem instaces |
| `-o OUTPUT, --output OUTPUT` | `{METHOD}/out` | Directory where to store the outputs |
| `-img IMAGES, --images IMAGES` | `{METHOD}/images` | Directory where to store the image representations of the outputs |
| `-ni [NO_IMAGES], --no-images [NO_IMAGES]` | `False` | Prevent the generation of the image representation |
| `-a [ALL_SOLUTIONS], --all-solutions [ALL_SOLUTIONS]` | `False` | Get all the solutions for each instance of the problem |
| `-s [PRINT_STAT], --print-stat [PRINT_STAT]` | `False` | Print statistics for the first solution |
| `-t TIME_LIMIT, --time-limit TIME_LIMIT` | `Infinite` | Max time given for solving the instances. Can be in format /\[\[hh:\]mm:\]ss\[.mil\]/. *(**Note:** the effective total time can vary for library imports or runtime side effects)*   |

### **Suggested Commands:**

| Task | Command | Description |
| ---- | ------- | ----------- |
| Help | `python main.py -h` | Get help message |
| CP   | `python main.py -m cp` | Solve all the inputs with CP, command used to generate outputs | 
| SAT  | `python main.py -m sat` | Solve all the inputs with SAT, command used to generate outputs | 
| SMT  | `python main.py -m smt` | Solve all the inputs with SMT, command used to generate outputs | 

# Structure
## Main
The main program is an abstract interface for each resolution method available. The program will invoke the single `{METHOD}/main.py` subroutine of the choosen method, passing the right parameters and instances to it. Each subroutine can also take its command line arguments too. As Python works in modules, is not possible to launch any of the subroutines singularly, you need to use this interface. 

## CP
The code is contained in a MiniZinc project, under the `CP/src` folder. The models implementations are stored in `CP/src/model` folder, while some useful testing data are stored in `CP/src/data`.

### **Arguments:**
| Argument | Default | Description |
|:---------|:--------|:------------|
| `--model` | `dup_rot_sym_model` | The model to be used in order to build the problem for the solver |
| `--solver` | `chuffed` | The MiniZinc solver used to carry out the problem |
| `--optimization` | `1` | The optimization level of MiniZinc compiler |
| `--no-free-search` | `False` | Disallow the solver to use Free Search mode |
| `--random-seed` | `42` | The random seed used in the search |

## SMT
The source code is available in two different programming language: through the z3 python API or using the STM2Lib syntax. In the first case the program is completely built on the z3 python stack, while in the latter the z3 python Solver API load the program from a source file of `.smt` extension, adding to it the parameter definitions. In the `SMT/src/smt2` folder are stored the model programs for the SMT2Lib language, while the using of z3 api allow us to use a more pythonic object oriented approach: we defined an abstract model class and we built each other model by combining the subclass chain of other models. All the python models are stored in `SMT/src/python`.

### **Arguments:**
| Argument | Default | Description |
|:---------|:--------|:------------|
| `--model` | `base_model` | The model to be used in order to build the problem for the solver |
| `--smt-lib` | `False` | True=Uses the smt2-lib standard language, False=Uses python api of z3 |
| `--verbose` | `Disabled` | The level of verbosity of z3 solver |

## SAT
As for SMT language, but since we struggled to implement a generic case of the problem through the SMT2Lib standard, we decided to implement just the python models, stored in the `SAT/src` folder. 

### **Arguments:**
| Argument | Default | Description |
|:---------|:--------|:------------|
| `--model` | `base_model` | The model to be used in order to build the problem for the solver |
| `--verbose` | `Disabled` | The level of verbosity of z3 solver |

## Statistic
This is another python program used to run in parallel the solver over the entire set of instances and store in a file the statistics of the resolution for each method.

To run it just run the command:

`python statistics.py`

**WARNING:** This program can take hours! 