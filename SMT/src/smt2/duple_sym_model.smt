(declare-const width Int)
(declare-const height Int)
(declare-const presents Int)
(declare-fun dimension_x (Int) Int)
(declare-fun dimension_y (Int) Int)
(declare-fun sorted_areas_indexes (Int) Int)

(define-fun area () Int (* width height))
(define-fun areas ((p Int)) Int (* (dimension_x p) (dimension_y p)))

(define-fun-rec areaSum ((p Int)) Int
  (ite
    (= p 0)
    0
    (+ (areas p) (areaSum (- p 1)))
  )
)

(declare-fun coord_x (Int) Int)
(declare-fun coord_y (Int) Int)
(declare-fun rotated (Int) Bool)
; Prevent present rotation (not included in the model)
(assert (forall ((i Int)) (not (rotated i))))

(define-fun overlaps_squares (
  (l1x Int) (r1x Int) (l1y Int) (r1y Int)
  (l2x Int) (r2x Int) (l2y Int) (r2y Int)
) Bool
  (and
    (not (or (>= l1x r2x) (>= l2x r1x)))
    (not (or (<= r1y l2y) (<= r2y l1y)))
  )
)
(define-fun overlaps ((p1 Int) (p2 Int)) Bool
  (overlaps_squares
    (coord_x p1)
    (+ (coord_x p1) (dimension_x p1))
    (coord_y p1)
    (+ (coord_y p1) (dimension_y p1))
    
    (coord_x p2)
    (+ (coord_x p2) (dimension_x p2))
    (coord_y p2)
    (+ (coord_y p2) (dimension_y p2))
  )
)

(assert (
  forall ((i Int)) (
     => (and (>= i 1) (<= i presents)) (and 
      
    ; limit coordinates
    (>= (coord_x i) 1) (<= (coord_x i) width)
    (>= (coord_y i) 1) (<= (coord_y i) height)
    
    ; the present must be in the paper sheet
    (<= (+ (coord_x i) (dimension_x i)) (+ width 1))
    (<= (+ (coord_y i) (dimension_y i)) (+ height 1))
    
    ; Two different presents must not overlap
    (forall ((j Int)) (
      => (and (> j i) (<= j presents))
        (not (overlaps i j))
    ))
  ))
))

(define-fun-rec sumRowDim ((y Int) (i Int)) Int
  (ite
    (= i 0)
    0
    (+ 
      (ite
        (and (>= y (coord_y i)) (<  y (+ (coord_y i) (dimension_y i))))
        (dimension_x i)
        0
      )
      (sumRowDim y (- i 1))
    )
  )
)

(define-fun-rec sumColDim ((x Int) (i Int)) Int
  (ite
    (= i 0)
    0
    (+ 
      (ite
        (and (>= x (coord_x i)) (<  x (+ (coord_x i) (dimension_x i))))
        (dimension_y i)
        0
      )
      (sumColDim x (- i 1))
    )
  )
)

(define-fun-rec checkSumRowDim ((y Int)) Bool
  (ite
    (= y 0)
    true
    (and
      (= (sumRowDim y presents) width)
      (checkSumRowDim (- y 1)) 
    )
  )
)

(define-fun-rec checkSumColDim ((x Int)) Bool
  (ite
    (= x 0)
    true
    (and
      (= (sumColDim x presents) height)
      (checkSumColDim (- x 1)) 
    )
  )
)

; The presents must fit the row dimension
(assert (checkSumRowDim height))

; The presents must fit the column dimension
(assert (checkSumColDim width))

; The total area of the presents must fit the area of the paper
(assert (= (areaSum presents) area))

; The biggest present must stay in (1, 1)
(assert (= (coord_x (sorted_areas_indexes 1)) 1))
(assert (= (coord_y (sorted_areas_indexes 1)) 1))

; The bigger the present the lesser the X coordinate
(assert (forall ((i Int) (j Int))(
    => (and (>= i 1) (<= i presents) (> j i) (>= j presents))
    (=> 
        (= (coord_y (sorted_areas_indexes i)) (coord_y (sorted_areas_indexes j)))
        (< (coord_x (sorted_areas_indexes i)) (coord_x (sorted_areas_indexes j)))
    ))
))

; Same size presents
(assert (forall ((i Int) (j Int))(
        => (and (>= i 1) (<= i presents) (> j i) (>= j presents))
        (or
            (not (= (dimension_x (sorted_areas_indexes i)) (dimension_x (sorted_areas_indexes j))))
            (not (= (dimension_y (sorted_areas_indexes i)) (dimension_y (sorted_areas_indexes j))))
            (<= (coord_y (sorted_areas_indexes i)) (coord_y (sorted_areas_indexes j)))
        )
    ))
)

(check-sat)
(get-model)