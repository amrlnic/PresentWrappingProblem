% === PARAMETERS ===
par int: WIDTH;
par int: HEIGHT;
par int: PRESENTS;
par int: AREA = WIDTH * HEIGHT;

array[1..PRESENTS] of par 1..WIDTH: DIMENSION_X;
array[1..PRESENTS] of par 1..HEIGHT: DIMENSION_Y;
array[1..PRESENTS] of par 1..AREA: AREAS = [ DIMENSION_X[i] * DIMENSION_Y[i] | i in 1..PRESENTS ];

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
      % present 1
      COORD_X[i], COORD_X[i] + DIMENSION_X[i],
      COORD_Y[i], COORD_Y[i] + DIMENSION_Y[i],
      % present 2
      COORD_X[j], COORD_X[j] + DIMENSION_X[j],
      COORD_Y[j], COORD_Y[j] + DIMENSION_Y[j]
   )
);

% The presents must fit the row dimension
constraint forall(y in 1..HEIGHT)(
  sum(i in 1..PRESENTS where y >= COORD_Y[i] /\ y < COORD_Y[i] + DIMENSION_Y[i])(DIMENSION_X[i]) = WIDTH
);

% The presents must fit the column dimension
constraint forall(x in 1..WIDTH)(
  sum(i in 1..PRESENTS where x >= COORD_X[i] /\ x < COORD_X[i] + DIMENSION_X[i])(DIMENSION_Y[i]) = HEIGHT
);

% The total area of the presents must fit the area of the paper
constraint sum(i in 1..PRESENTS)(AREAS[i]) = AREA;

% === SEARCH ===
ann: coord_x_search = int_search(COORD_X, first_fail, indomain_min);
ann: coord_y_search = int_search(COORD_Y, first_fail, indomain_min);
ann: coords_search = seq_search([ coord_x_search, coord_y_search ]);

solve :: coords_search  satisfy;