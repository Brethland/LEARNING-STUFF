#lang racket

; This is an exercise program in <SICP> CH2.
; Mainly about Church number and other WTF (SHIT STUFF).
; Author : Brethland, Early 2019

(define (cons a b)
    (* (expt 2 a)
        (expt 3 b)))
(define (car z)
    (define (iter z result)
        (if (not (= (remainder z 2) 0))
            result
            (iter (/ z 2) (+ result 1))))
    (iter z 0))
(define (cdr z)
    (define (iter z result)
        (if (not (= (remainder z 3) 0))
            result
            (iter (/ z 3) (+ result 1))))
    (iter z 0))
; (car (cons 4 5))
; (cdr (cons 7 6))
; (define one (lambda (f) (lambda (x) (f x))))
; (define two (lambda (f) (lambda (x) (f (f x)))))
(define zero (lambda (f) (lambda (x) x)))
(define (add a b)
    (lambda (f) (lambda (x) ((b f) ((a f) x)))))