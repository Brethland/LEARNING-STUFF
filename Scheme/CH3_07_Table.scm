#lang racket

; This is an exercise program in <SICP> CH3.
; Mainly about Table Data Structure.
; Author : Brethland, Late 2019.

(define (assoc key table)
    (cond ((null? table) #f)
            ((same-key? key (caar table)) (car table))
        (else (assoc key (cdr table)))))
(define (lookup-inner keylist table)
    (if (null? keylist)
        table
        (let ((subtable (assoc (car keylist) (cdr table))))
            (if subtable
                (lookup-inner (cdr keylist) subtable)
                #f))))
(define (look-up keylist table)
    (if (null? keylist)
        #f
        (lookup-inner keylist table)))
(define (make-list keylist value)
    (if (null? (cdr keylist))
        (cons (car keylist value))
        (list (car keylist) (make-list (cdr keylist) value))))
(define (insert-inner! keylist value table)
    (if (null? (cdr keylist))
        (let ((record (assoc (car keylist) (cdr table))))
            (if record
                (set-cdr! record value)
                (set-cdr! table (cons (cons (car keylist) value) (cdr table)))))
        (let ((subtable assoc (car keylist) (cdr table)))
            (if subtable
                (insert-inner! (cdr keylist) value subtable)
                (set-cdr! table (cons (make-list keylist value) (cdr table)))))))
(define (insert! keylist value table)
    (if (null? keylist)
        (display "INSERT! called with an empty keylist" keylist)
        (insert-inner! keylist value table)))
