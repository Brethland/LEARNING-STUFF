;;; This is a minimal implementation of
;;; John Conway's Game of Life.

;;; In memory of J.Conway, 1937 - 2020
;;; Arthur : Brethland, Early 2020.

(define (judge-reduce s1 s2 judge op last)
  (cond ((null? s1) last)
	      ((judge (car s1) s2) (op (car s1) (judge-reduce (cdr s1) s2 judge op last)))
	      (else (judge-reduce (cdr s1) s2 judge op last))))

(define (add-set elem set) 
  (judge-reduce set elem (lambda (x y) (not (equal? x y))) cons (cons elem `())))

(define (interaction s1 s2) 
  (judge-reduce s1 s2 member (lambda (x y) (+ 1 y)) 0))

(define (list->set elems)
  (cond ((null? elems) '())
	(else (add-set (car elems) (list->set (cdr elems))))))

(define (get-neighbours cell)
  (list
    (list (+ (car cell) 1) (+ (cadr cell) 1))
    (list (+ (car cell) 1) (- (cadr cell) 1))
    (list (- (car cell) 1) (+ (cadr cell) 1))
    (list (- (car cell) 1) (- (cadr cell) 1))
    (list (- (car cell) 0) (+ (cadr cell) 1))
    (list (+ (car cell) 0) (- (cadr cell) 1))
    (list (+ (car cell) 1) (- (cadr cell) 0))
    (list (- (car cell) 1) (+ (cadr cell) 0))))

(define (alive? cell life)
  (define living-neighbours (interaction (get-neighbours cell) life))
  (or (and (member cell life) (or (= living-neighbours 2) (= living-neighbours 3)))
      (= living-neighbours 3)))

(define (envolved life)
  (judge-reduce (list->set (judge-reduce life life (lambda (x y) #t) (lambda (x y) (cons x (append (get-neighbours x) y))) `()))
		life alive? cons `()))

(define (live-happily)
  (begin (sleep (make-time 'time-duration 400000000 0))
	 (display (string-append (list->string (list #\033 #\[ )) "2J"))))

(define (aemaeth life x y)
  (cond ((and (> x 75) (> y 25)) (newline))
	((> x 75) (begin (newline) (aemaeth life 1 (+ 1 y))))
	(else (begin (display (if (member (list x y) life) "*" ".")) (aemaeth life (+ 1 x) y)))))

(define (live-a life) (aemaeth life 1 1))

(define (game-of life)
  (begin 
    (live-a life)
	  (live-happily)
	  (game-of (envolved life))))
