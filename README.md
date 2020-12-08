# PresentWrappingProblem

It is a common practice that a private business rewards its loyal clients with presents, which are typically wrapped in a costly corporate paper covered with the logo of the business. Imagine that you work for such a business which wants to limit the overall amount of paper that can be used for this purpose, in order to reduce the associated expenses. As the combinatorial decision and optimization expert, you are assigned to solve the Present Wrapping Problem (PWP): given a wrapping paper roll of a certain dimension and a list of presents, decide how to cut oﬀ pieces of paper so that all the presents can be wrapped. Consider that each present is described by the dimensions of the piece of paper needed to wrap it. Moreover, each necessary piece of paper cannot be rotated when cutting oﬀ, to respect the direction of the patterns in the paper.


# CLI

Command:

`python main.py [arguments]`

\
Arguments:
| Argument | Default | Description |
|:---------|:--------|:------------|
| `-h`| ------------ | show help message and exit|
| `-m METHOD, --method METHOD` | REQUIRED | Method used to carry out the solution(s), possible: `CP`, `SAT`, `SMT`|
| `-i INPUT, --input INPUT` | `./inputs` | Files or directories where to locate the problem instaces|
| `-o OUTPUT, --output OUTPUT` | `{METHOD}/out` | Directory where to store the outputs |
| `-img IMAGES, --images IMAGES` | `{METHOD}/images` |  Directory where to store the image representations of the outputs |
| `-ni [NO_IMAGES], --no-images [NO_IMAGES]` | `False` | Prevent the generation of the image representation |
| `-s [ALL_SOLUTIONS], --all-solutions [ALL_SOLUTIONS]` | `False` | Get all the solutions for each instance of the problem |

\
\
Suggested Commands:

| Task | Command | Description |
| ---- | ------- | ----------- |
| Help | `python main.py -h` | Get help message |
| CP   | `python main.py -m cp` | Solve all the inputs with CP, command used to generate outputs | 
| SAT  | `python main.py -m sat` | Solve all the inputs with SAT, command used to generate outputs | 
| SMT  | `python main.py -m smt` | Solve all the inputs with SMT, command used to generate outputs | 