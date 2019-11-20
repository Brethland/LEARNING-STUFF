#lang racket

; This is an exercise program in <SICP> CH3.
; Mainly about mutex in Parallel Computation.
; Author : Brethland, Late 2019.

(require compatibility/mlist)
(require rnrs/mutable-pairs-6)
(define (make-signal-volume n)
    (let ((process 0))
        (define (me m)
            (cond ((eq? m `acquire)
                    (if (test-and-set! cell)
                        (me `acquire)))
                  ((eq? m `release) (minus! cell))))
        (define (minus! a)
            (without-interrupt
            (lambda () (set! a (- a 1)))))
        (define (test-and-set! a)
            (without-interrupt
                (lambda () (
                    if (= a n)
                        #t
                        (begin (set! a (+ a 1))
                        #f)))))
    me))
(define m (list `a `b))
(define n (list `c `d))
(define (append x y)
    (if (null? x)
        y
        (cons (car x) (append (cdr x) y))))
(define x (mlist `a `b))
(define y (mlist `c `d))    
(define (append! x y)
    (set-mcdr! (last-pair x) y)
    x)
(define (last-pair x)
    (if (null? (mcdr x))
        x
        (last-pair (mcdr x))))
(append m n)
(define w (append! x y))
(mcdr w)