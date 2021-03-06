;;; This is an exercise program in <SICP> CH3.
;;; Mainly about Stream and other stuff.
;;; Author : Brethland, Late 2019.

(require racket/stream)
(define (integers-starting-from n)
    (stream-cons n (integers-starting-from (+ n 1))))
(define integers (integers-starting-from 1))
(define (stream-map proc . argstreams)
    (if (stream-empty? (car argstreams))
        `()
        (stream-cons (apply proc (map stream-first argstreams))
            (apply stream-map (cons proc (map stream-rest argstreams))))))
(define (mul-streams s1 s2)
    (stream-map * s1 s2))
(define factorials (stream-cons 1 (mul-streams integers factorials)))
; (stream-ref factorials 5)
(define (partial-sum stream)
    (define (iter argstream result)
        (stream-cons result
            (iter (stream-rest argstream) (+ result (stream-first argstream)))))
    (iter (stream-rest stream) (stream-first stream)))
; (stream-ref (partial-sum integers) 0)
(define (scale-stream stream factor)
    (stream-map (lambda (x) (* x factor)) stream))
(define (merge s1 s2)
    (cond ((stream-empty? s1) s2)
          ((stream-empty? s2) s1)
          (else 
            (let ((s1car (stream-first s1))
                  (s2car (stream-first s2)))
                (cond ((< s1car s2car)
                        (stream-cons s1car (merge (stream-rest s1) s2)))
                      ((> s1car s2car)
                        (stream-cons s2car (merge s1 (stream-rest s2))))
                      (else
                        (stream-cons s1car (merge (stream-rest s1) (stream-rest s2)))))))))
(define S (stream-cons 1 (merge (scale-stream S 2) (merge (scale-stream S 3) (scale-stream S 5)))))
; (stream-ref S 7)
(define (integrate-series stream)
    (define (iter s n)
        (stream-cons (* (/ 1 n) (stream-first s))
            (iter (stream-rest s) (+ n 1))))
    (iter stream 1))
(define cosine-series
    (stream-cons 1 (integrate-series (stream-cons 1 (integrate-series (stream-cons 1 (integrate-series (stream-cons 1 (integrate-series cosine-series)))))))))
(define (mul-series s1 s2)
    (stream-cons (* (stream-first s1) (stream-first s2))
        (add-streams (mul-series (stream-rest s1) (scale-stream (stream-first s1) s2)) (mul-series (scale-stream (stream-first s2) s1) (stream-rest s2)))))
(define (inv-series s)
    (stream-cons 1 (mul-series (stream-map (lambda (x) (- x)) (stream-rest s)) (inv-series s))))
(define (div-series r s)
    (add-streams r (mul-series (stream-map (lambda (x) (- x)) (stream-rest s)) (div-series r s))))
(define (integers-starting-from n)
    (stream-cons n (integers-starting-from (+ n 1))))
(define integers (integers-starting-from 1))
(define (square s)
    (* s s))
(define (abs a)
    (cond ((< a 0) (- a))
          (else a)))
(define (stream-map proc . argstreams)
    (if (stream-empty? (car argstreams))
        `()
        (stream-cons (apply proc (map stream-first argstreams))
            (apply stream-map (cons proc (map stream-rest argstreams))))))
(define (eular-transform s)
    (let ((s0 (stream-ref s 0))
          (s1 (stream-ref s 1))
          (s2 (stream-ref s 2)))
        (stream-cons (- s2 (/ (square (- s2 s1))
                              (+ s0 (* -2 s1) s2)))
                    (eular-transform (stream-rest s)))))
(define (make-tableau transform s)
    (stream-cons s
        (make-tableau transform (transform s))))
(define (accelerated-sequence transform s)
    (stream-map stream-first (make-tableau transform s)))
(define (stream-limit s tolerance)
    (let ((s0 (stream-ref s 0))
          (s1 (stream-ref s 1)))
        (cond ((< (abs (- s1 s0)) tolerance) s1)
              (else (stream-limit (stream-rest s) tolerance)))))
(define (sqrt x tolerance)
    (stream-limit (sqrt-stream x) tolerance))
(define (sqrt-stream x)
    (define guesses
        (stream-cons 1.0
                    (stream-map (lambda (guess) (sqrt-improve guess x)) guesses)))
    guesses)
(define (sqrt-improve guess x)
    (average guess (/ x guess)))
(define (average a b)
    (/ (+ a b) 2))
(define (partial-sum stream)
    (define (iter argstream result)
        (stream-cons result
            (iter (stream-rest argstream) (+ result (stream-first argstream)))))
    (iter (stream-rest stream) (stream-first stream)))
; (sqrt 2 0.00001)
(define (ln2-summands n)
    (stream-cons (/ 1.0 n)
        (stream-map - (ln2-summands (+ n 1)))))
(define ln2
    (partial-sum (ln2-summands 1)))
(define (interleave s1 s2)
    (if (stream-empty? s1)
        s2
        (stream-cons (stream-first s1)
            (interleave s2 (stream-rest s1)))))
(define (pairs s t)
    (stream-cons
        (list (stream-first s) (stream-first t))
        (interleave
            (stream-map (lambda (x) (list (stream-first s) x)) (stream-rest t))
            (pairs (stream-rest s) (stream-rest t)))))
(define (display-stream s)
    (if (not (stream-empty? s))
    ((display (stream-first s))
    (newline)
    (display-stream (stream-rest s)))
    (newline)))
; (display-stream (pairs integers integers))
(define (triples s t u)
    (stream-cons
        (list (stream-first s) (stream-first t) (stream-first u))
        (interleave
            (stream-map (lambda (x) (cons (stream-first s) x)) (pairs (stream-rest t) (stream-rest u)))
            (triples (stream-rest s) (stream-rest t) (stream-rest u)))))
; (display-stream (triples integers integers integers))
(define (stream-filter pred stream)
    (cond ((stream-empty? stream) `())
          ((pred (stream-first stream))
            (stream-cons (stream-first stream)
                (stream-filter pred (stream-rest stream))))
          (else (stream-filter pred (stream-rest stream)))))
(define (merge-weighted s1 s2 weight)
    (cond ((stream-empty? s1) s2)
          ((stream-empty? s2) s1)
          (else 
            (let ((s1car (stream-first s1))
                  (s2car (stream-first s2)))
                (cond ((< (weight s1car) (weight s2car))
                        (stream-cons s1car (merge-weighted s2 (stream-rest s1) weight)))
                      (else
                        (stream-cons s2car (merge-weighted (stream-rest s2) s1 weight))))))))
(define (weighted-pairs s t weight)
    (stream-cons
        (list (stream-first s) (stream-first t))
        (merge-weighted
            (stream-map (lambda (x) (list (stream-first s) x)) (stream-rest t))
            (weighted-pairs (stream-rest s) (stream-rest t) weight)
            weight)))
(define (sum-weight pair)
    (+ (car pair) (car (cdr pair))))
(define (weight235 pair)
    (+ (* 2 (car pair)) (* 3 (car (cdr pair))) (* 5 (car pair) (car (cdr pair)))))
(define (can-divide-235? x)
    (or (= (remainder x 2) 0) (= (remainder x 3) 0) (= (remainder x 5) 0)))
; (display-stream (stream-filter 
;     (lambda (pair) (and (can-divide-235? (car pair)) (can-divide-235? (car (cdr pair))))) 
;     (weighted-pairs integers integers weight235)))
(define (cubic x)
    (* x x x))
(define (weight-cubic pair)
    (let ((x (car pair))
          (y (car (cdr pair))))
        (+ (cubic x) (cubic y))))
(define (iter s)
    (let ((s0 (stream-ref s 0))
          (s1 (stream-ref s 1))
          (s2 (stream-ref s 2)))
        (cond ((= (weight-cubic s0) (weight-cubic s1) (weight-cubic s2))
                (stream-cons (list (weight-cubic s0) s0 s1 s2)
                    (iter (stream-rest (stream-rest (stream-rest s))))))
              (else (iter (stream-rest s))))))
(define Ramanujan-number
    (iter (weighted-pairs integers integers weight-cubic)))
; (display-stream Ramanujan-number)
(define (RC R C dt)
    (lambda (i v0)
        (add-stream (scale-stream i R)
            (scale-stream (integral i v0 dt) (/ 1 C)))))
(define zero-crossings
    (stream-map sign-change-detector sense-data (stream-cons 0 sense-data)))
(define (make-zero-crossings input-stream last-value changed)
    (let ((avpt (/ (+ (stream-first input-stream) last-value) 2)))
        (stream-cons (sign-change-detector avpt changed)
            (make-zero-crossings (stream-rest input-stream) avpt (stream-first input-stream)))))
(define (smooth stream)
    (let ((s0 (stream-ref stream 0))
          (s1 (stream-ref stream 1)))
        (stream-cons (average s0 s1)
            (smooth (stream-rest stream)))))
(define zero-crossings
    (stream-map sign-change-detector (smooth sense-data) (stream-cons 0 (smooth sense-data))))
(define (integral delayed-intergrand initial-value dt)
    (stream-cons initial-value
        (let ((intergrand (force delayed-intergrand)))
            (if (stream-empty? intergrand)
                `()
                (integral (delay (stream-rest intergrand))
                          (+ (* dt (stream-first intergrand))
                            initial-value)
                        dt)))))
(define (solve-2nd a b dt y0 dy0 f)
    (define y (integral (delay dy) y0 dt))
    (define dy (integral (delay ddy) dy0 dt))
    (define ddy (stream-map f dy y))
    y)
(define (RLC R L C dt)
    (lambda (vc0 il0)
        ((define il (integral (delay dil) il0 dt))
         (define vc (integral (delay dvc) vc0 dt))
         (define dil (add-stream (scale-stream il (/ (- R) L)) (scale-stream vc (/ 1 L))))
         (define dvc (scale-stream il (/ (- 1) C)))
         (cons il vc))))
(define (reset)
        (lambda (n)
            (rand n)))
(define (rand seed)
    (define (generate stream)
        (stream-rest stream))
    (let ((stream (stream-cons seed
                    (stream-map random-update random-stream))))
    (define (dispatch m)
        (cond ((eq? m generate) (generate stream))
              ((eq? m reset) (reset))))
    dispatch))
(define (estimate-integral p x1 x2 y1 y2 trial-times)
(define (exp)
(p (random-in-range x1 x2) (random-in-range y1 y2)))
(define (monte-carlo trials experiment)
(define (iter trials-remaining trials-passed)
(cond ((= trials-remaining 0) (/ trials-passed trials))
((experiment) (iter (- trials-remaining 1) (+ trials-passed 1)))
(else (iter (- trials-remaining 1) trials-passed))))
(iter trials 0))
(let ((estimate-rate (monte-carlo trial-times exp)))
(* estimate-rate (* (- x2 x1) (- y2 y1)))))
(define unit-circle
(lambda (x y)
(<= 1.0 (+ (* x x) (* y y)))))
(define (estimate-integral p x1 x2 y1 y2)
    (define random-numbers-in-range
        (merge (stream-filter (ranged x1 x2) random-numbers) (stream-filter (ranged y1 y2) random-numbers)))
    (stream-map (lambda (x) (* x (- x2 x1) (- y2 y1)))
        (monte-carlo (map-successive-pairs p random-numbers-in-range) 0 0)))