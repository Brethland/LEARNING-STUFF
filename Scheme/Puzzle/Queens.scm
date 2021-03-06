;;; This is a solution for eight queen problem written in Lisp.
;;; Author : Brethland, Late 2019.

(define (queen board-size)
    (define empty-board `())
    (define (safe? k sequence)
        (define check-seq (reverse sequence))
        (define (iter m seq diff)
            (if (null? seq)
                #t
            (let ((check-point (car seq)))
                (and (not (= check-point m))
                     (not (= (- diff check-point) m))
                     (not (= (+ diff check-point) m))
                     (iter m (cdr seq) (+ diff 1))))))
        (iter (car check-seq) (cdr check-seq) 1))
    (define (adjoin-position row k sequence)
        (define k-list (list row))
        (append sequence k-list))
    (define (queen-cols k)
        (if (= k 0)
            (list empty-board)
            (filter
             (lambda (positions) (safe? k positions))
             (flatmap (lambda (rest-of-queens)
                        (map (lambda (new-row)
                                (adjoin-position new-row k rest-of-queens))
                             (enumurate-interval 1 board-size)))
                      (queen-cols (- k 1))))))
    (queen-cols board-size))
(queen 8)