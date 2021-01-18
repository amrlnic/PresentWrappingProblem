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
constraint diffn(COORD_X, COORD_Y, [ rotated_dimension(i, 0) | i in 1..PRESENTS ], [ rotated_dimension(i, 1) | i in 1..PRESENTS ]);

% The cumulative global constraint is very slow compared with the custom solution (see rot_model.mzn)
constraint cumulative(COORD_X, [ rotated_dimension(i, 0) | i in 1..PRESENTS ], [ rotated_dimension(i, 1) | i in 1..PRESENTS ], HEIGHT);
constraint cumulative(COORD_Y, [ rotated_dimension(i, 1) | i in 1..PRESENTS ], [ rotated_dimension(i, 0) | i in 1..PRESENTS ], WIDTH);

% The total area of the presents must fit the area of the paper
constraint sum(i in 1..PRESENTS)(AREAS[i]) = AREA;

% === SEARCH ===
ann: coord_x_search = int_search(COORD_X, first_fail, indomain_min);
ann: coord_y_search = int_search(COORD_Y, first_fail, indomain_min);
ann: rotated_search = int_search(ROTATED, input_order, indomain_min);
ann: coords_search = seq_search([ rotated_search, coord_y_search, coord_x_search ]);

solve :: coords_search  satisfy;