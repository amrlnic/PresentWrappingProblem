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

% === PREDICATES ===
% === CONSTRAINTS ===
% The present must be in the paper sheet
constraint
forall(i in 1..PRESENTS)(
   COORD_X[i] + DIMENSION_X[i] <= WIDTH + 1 /\
   COORD_Y[i] + DIMENSION_Y[i] <= HEIGHT + 1
);

constraint diffn(COORD_X, COORD_Y, DIMENSION_X, DIMENSION_Y);

% The cumulative global constraint is very slow compared with the custom solution (see base_model.mzn)
constraint cumulative(COORD_X, DIMENSION_X, DIMENSION_Y, HEIGHT);
constraint cumulative(COORD_Y, DIMENSION_Y, DIMENSION_X, WIDTH);

% The total area of the presents must fit the area of the paper
constraint sum(i in 1..PRESENTS)(AREAS[i]) = AREA;

% === SEARCH ===
ann: coord_x_search = int_search(COORD_X, first_fail, indomain_min);
ann: coord_y_search = int_search(COORD_Y, first_fail, indomain_min);
ann: coords_search = seq_search([ coord_x_search, coord_y_search ]);

solve :: coords_search  satisfy;