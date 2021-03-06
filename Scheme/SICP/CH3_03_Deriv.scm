;;; This is an exercise program in <SICP> CH3.
;;; Mainly about Multiple Poly Deriv.
;;; Author : Brethland, Late 2019.

(define (variable? x) (symbol? x))
(define (same-variable? x y)
    (and (variable? x) (variable? y) (eq? x y)))
(define (=number? expr num)
    (and (number? expr) (= expr num)))
; (define (poland-expr expr)
;     (cond ((null? expr) `())
;           (not (pair? expr) expr)
;           ((pair? (car expr)) (list (car (cdr expr)) (car expr) (poland-expr (car (cdr (cdr expr))))))
;           (else 
;           (poland-expr (cons (list (car (cdr expr)) (car expr) (car (cdr (cdr expr))))
;               (cdr (cdr (cdr expr))))))))
(define (make-sum a1 a2)
    (cond ((=number? a1 0) a2)
          ((=number? a2 0) a1)
          ((and (number? a1) (number? a2)) (+ a1 a2))
          (else (list a1 `+ a2))))
(define (make-product a1 a2)
    (cond ((or (=number? a1 0) (=number? a2 0)) 0)
          ((=number? a1 1) a2)
          ((=number? a2 1) a1)
          ((and (number? a1) (number? a2)) (* a1 a2))
          (else (list a1 `* a2))))
(define (sum? exp)
    (and (pair? exp) (eq? (car (cdr exp)) `+)))
(define (addend x) (car x))
; (define (augend x) 
;     (if (null? (cdr (cdr (cdr x)))) 
;         (car (cdr (cdr x))) 
;         (cdr (cdr x))))
(define (augend x)
    (car (cdr (cdr x))))
(define (product? exp)
    (and (pair? exp) (eq? (car (cdr exp)) `*)))
(define (multiplier p) (car p))
; (define (multiplicand p) 
;     (if (null? (cdr (cdr (cdr p)))) 
;         (car (cdr (cdr p))) 
;         (cdr (cdr p))))
(define (multiplicand p)
    (car (cdr (cdr p))))
(define (exp? x)
    (and (pair? x) (eq? (car x) `**)))
(define (base x) (car (cdr x)))
(define (exponent x) (car (cdr (cdr x))))
(define (make-exp a1 a2)
    (cond ((=number? a2 1) a1)
          ((=number? a2 0) 1)
          ((and (number? a1) (number? a2)) (exp a1 a2))
          (else (list `** a1 a2))))
(define (deriv expr var)
    (cond ((number? expr) 0)
          ((variable? expr) (if (same-variable? expr var) 1 0))
          ((sum? expr)
            (make-sum (deriv (addend expr) var)
                      (deriv (augend expr) var)))
          ((product? expr)
            (make-sum (make-product (multiplier expr) (deriv (multiplicand expr) var))
                      (make-product (multiplicand expr) (deriv (multiplier expr) var))))
          ((exp? expr)
            (make-product (exponent expr)
                            (make-product (make-exp (base expr) (make-sum (exponent expr) (- 1)))
                                          (deriv (base expr) var))))
          (else 
            (display "unknown expression type -- DERIV" exp))))
; (deriv `(x + (3 * (x + (y + 2)))) `x)