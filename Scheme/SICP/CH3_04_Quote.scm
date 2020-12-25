;;; This is an exercise program in <SICP> CH3.
;;; Mainly about Quote Grammer in Lisp.
;;; Author : Brethland, Late 2019.

(define (memq item x)
    (cond ((null? x) false)
          ((eq? item (car x)) x)
          (else (memq item (cdr x)))))
; (list `a `b `c) ;(a b c)
; (list (list `george)) ;((george))
; (cdr `((x1 x2) (y1 y2))) ;((y1 y2))
; (car (cdr `((x1 x2) (y1 y2)))) ;(y1 y2)
; (pair? (car `(a short list))) ;#f
; (memq `red `((red shoes) (blue socks))) ;#f
; (memq `red `(red shoes blue socks)) ;(red shoes blue socks)
(define (equal? a b)
    (cond ((and (not (pair? a)) (not (pair? b))) (eq? a b))
          ((or (not (pair? a)) (not (pair? b))) #f)
          (else (and (equal? (car a) (car b)) (equal? (cdr a) (cdr b))))))
(equal? `(this is a list) `(this is (a list)))
(equal? `(this is a list) `(this is a list))
