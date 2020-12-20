; VARIABLES
(declare-const width Int)
(declare-const height Int)
(declare-const presents Int)
(define-const area Int (* width height))

(declare-fun dimensions (Int Int) Int)

(define-fun areas ((i Int)) Int (* (dimensions i 0) (dimensions i 1)))

(declare-fun coords (Int Int) Int)

; PREDICATES & FUNCTIONS
(define-fun overlaps (
  (l1x Int) (r1x Int)
  (l1y Int) (r1y Int)
  (l2x Int) (r2x Int)
  (l2y Int) (r2y Int)
  )
  Bool
  (and (not (or (>= l1x r2x) (>= l2x r1x))) (not (or (<= r1y l2y) (<= r2y l1y))))
)

(declare-fun areaSum (Int) Int)
(assert (= (areaSum 0) 0))
(assert (forall ((i Int)) (
    => (and (>= i 1) (<= i presents))
    (= (areaSum i) (+ (areaSum (- i 1)) (areas i)))
)))

(declare-fun rowDimSum (Int Int) Int)
(assert (forall ((y Int)) (
  => (and (>= y 1) (<= y height))
  (= (rowDimSum y 0) 0)
)))
(assert (forall ((y Int) (i Int)) (
  => (and (>= i 1) (<= i presents) (>= y 1) (<= y height))
  (= (rowDimSum y i) (+
    (rowDimSum y (- i 1))
    (ite (and (>= y (coords i 1)) (< y (+ (coords i 1) (dimensions i 1)))) (dimensions i 0) 0)
  )
))))

(declare-fun colDimSum (Int Int) Int)
(assert (forall ((x Int)) (
  => (and (>= x 1) (<= x width))
  (= (colDimSum x 0) 0)
)))
(assert (forall ((x Int) (i Int)) (
  => (and (>= i 1) (<= i presents) (>= x 1) (<= x width))
  (= (colDimSum x i) (+
    (colDimSum x (- i 1))
    (ite (and (>= x (coords i 0)) (< x (+ (coords i 0) (dimensions i 0)))) (dimensions i 1) 0)
  )
))))

; PROBLEM DEFINITION
(assert (= width 4))
(assert (= height 4))
(assert (= presents 1))
(assert (= (dimensions 1 0) 4))
(assert (= (dimensions 1 1) 4))

; CONSTRAINTS
; The total area of the presents must fit the area of the paper
(assert (= (areaSum presents) area))

; The presents must fit the row dimension
(assert (forall ((y Int)) (
  => (and (>= y 1) (<= y height))
  (= (rowDimSum y presents) width)
)))

; The presents must fit the cold dimension
(assert (forall ((x Int)) (
  => (and (>= x 1) (<= x width))
  (= (colDimSum x presents) height)
)))


; The present must be in the paper sheet
(assert (forall ((i Int))(
  => (and (>= i 1) (<= i presents))
  (and
    (<= (+ (coords i 0) (dimensions i 0)) (+ width 1))
    (<= (+ (coords i 1) (dimensions i 1)) (+ height 1))
  )
)))

; Two different presents must not overlap
(assert (forall ((i Int) (j Int))(
  => (and (>= i 1) (< i presents) (> j i) (<= j presents))
  (not (overlaps
    (coords i 0) (+ (coords i 0) (dimensions i 0))
    (coords i 1) (+ (coords i 1) (dimensions i 1))
    (coords j 0) (+ (coords j 0) (dimensions j 0))
    (coords j 1) (+ (coords j 1) (dimensions j 1))
  ))
  
)))

(check-sat)
(get-model)