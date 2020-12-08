% === PARAMETERS ===
par int: WIDTH;
par int: HEIGHT;
par int: PRESENTS;

array[1..PRESENTS] of par 1..WIDTH: DIMENSION_X;
array[1..PRESENTS] of par 1..HEIGHT: DIMENSION_Y;

% === VARIABLES ===
array[1..PRESENTS] of var 1..WIDTH: COORD_X;
array[1..PRESENTS] of var 1..HEIGHT: COORD_Y;

% === PREDICATES ===
% Check if two squares overlap
predicate overlaps(
  % square 1
  var int: l1x, var int: r1x,
  var int: l1y, var int: r1y,
  % square 2
  var int: l2x, var int: r2x,
  var int: l2y, var int: r2y
) = (
  not (l1x >= r2x \/ l2x >= r1x) /\
  not (r1y <= l2y \/ r2y <= l1y)
);

% === CONSTRAINTS ===
% The present must be in the paper sheet
constraint
forall(i in 1..PRESENTS)(
   COORD_X[i] + DIMENSION_X[i] <= WIDTH + 1 /\
   COORD_Y[i] + DIMENSION_Y[i] <= HEIGHT + 1
);

% Two different presents must not overlap
constraint
forall(i, j in 1..PRESENTS where j > i)(
  not overlaps(
      % shard 1
      COORD_X[i], COORD_X[i] + DIMENSION_X[i],
      COORD_Y[i], COORD_Y[i] + DIMENSION_Y[i],
      % shard 2
      COORD_X[j], COORD_X[j] + DIMENSION_X[j],
      COORD_Y[j], COORD_Y[j] + DIMENSION_Y[j]
   )
);

solve satisfy;

output [
 "\(i): \(fix(COORD_X[i])), \(fix(COORD_Y[i])) - \(DIMENSION_X[i])x\(DIMENSION_Y[i])\n" | i in 1..PRESENTS
];