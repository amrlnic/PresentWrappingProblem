include "globals.mzn";

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

array[1..PRESENTS] of var 0..1: ROTATED;

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

function var int: rotated_dimension(1..PRESENTS: index, par 0..1: axis) =
  if ROTATED[index] = axis then DIMENSION_X[index] else DIMENSION_Y[index] endif;
     

% === CONSTRAINTS ===
% The present must be in the paper sheet
constraint
forall(i in 1..PRESENTS)(
   COORD_X[i] + rotated_dimension(i, 0) <= WIDTH + 1 /\
   COORD_Y[i] + rotated_dimension(i, 1) <= HEIGHT + 1
);

% Two different presents must not overlap
constraint
forall(i, j in 1..PRESENTS where j > i)(
  not overlaps(
      % present 1
      COORD_X[i], COORD_X[i] + rotated_dimension(i, 0),
      COORD_Y[i], COORD_Y[i] + rotated_dimension(i, 1),
      % present 2
      COORD_X[j], COORD_X[j] + rotated_dimension(j, 0),
      COORD_Y[j], COORD_Y[j] + rotated_dimension(j, 1)
   )
);

% The presents must fit the row dimension
constraint forall(y in 1..HEIGHT)(
  sum(i in 1..PRESENTS where y >= COORD_Y[i] /\ y < COORD_Y[i] + rotated_dimension(i, 1))(rotated_dimension(i, 0)) = WIDTH
);

% The presents must fit the column dimension
constraint forall(x in 1..WIDTH)(
  sum(i in 1..PRESENTS where x >= COORD_X[i] /\ x < COORD_X[i] + rotated_dimension(i, 0))(rotated_dimension(i, 1)) = HEIGHT
);

% The total area of the presents must fit the area of the paper
constraint sum(i in 1..PRESENTS)(AREAS[i]) = AREA;

% === SYMMETRY BREACKING ===
array[1..PRESENTS] of par 1..AREA: SORTED_AREAS_INDEXES = reverse(arg_sort(AREAS));

% The biggest present must stay in (1, 1)
constraint COORD_X[SORTED_AREAS_INDEXES[1]] = 1;
constraint COORD_Y[SORTED_AREAS_INDEXES[1]] = 1;

% The bigger the present the lesser the X coordinate
constraint forall(i, j in 1..PRESENTS where j > i)(
  COORD_Y[SORTED_AREAS_INDEXES[i]] = COORD_Y[SORTED_AREAS_INDEXES[j]] ->
  COORD_X[SORTED_AREAS_INDEXES[i]] < COORD_X[SORTED_AREAS_INDEXES[j]]
);

% === SEARCH ===
ann: coord_x_search = int_search(COORD_X, first_fail, indomain_min);
ann: coord_y_search = int_search(COORD_Y, first_fail, indomain_min);
ann: rotated_search = int_search(ROTATED, input_order, indomain_min);
ann: coords_search = seq_search([ rotated_search, coord_y_search, coord_x_search ]);

solve :: coords_search  satisfy;