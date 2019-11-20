#lang racket

; This is an exercise program in <SICP> CH2.
; Mainly about Painter Language mentioned in 2.2.4.
; Author : Brethland, Early 2019.

(define (up-split painter n)
    (if (= n 0)
        painter
        (let ((smaller upsplit painter (- n 1)))
            (below painter (beside smaller smaller)))))
(define (split combiner spliter)
    (lambda (painter n)
        (if (= n 0)
            painter
            (let ((smaller ((split combiner spliter) painter (- n 1))))
                (combiner painter (spliter smaller smaller))))))
(define (make-vect x y)
    (cons x y))
(define (xcor-vect vect)
    (car vect))
(define (ycor-vect vect)
    (cdr vect))
(define (add-vect vec1 vec2)
    (make-vect (+ (xcor-vect vec1) (xcor-vect vec2))
               (+ (ycor-vect vec1) (ycor-vect vec2))))
(define (sub-vect vec1 vec2)
    (make-vect (- (xcor-vect vec1) (xcor-vect vec2))
               (- (ycor-vect vec1) (ycor-vect vec2))))
(define (scale-vect s vect)
    (make-vect (* s (xcor-vect vect)) (* s (ycor-vect vect))))
(define (make-frame origin edge1 edge2)
    (cons origin (cons edge1 edge2)))
(define (origin-frame frame)
    (car frame))
(define (edge1-frame frame)
    (car (cdr frame)))
(define (edge2-frame frame)
    (cdr (cdr frame)))
(define (make-segment start end)
    (cons start end))
(define (start-segment segment)
    (car segment))
(define (end-segment segment)
    (cdr segment))
(define (segment->painter segment-list)
    (lambda (frame)
        (for-each
            (lambda (segment)
                (draw-line
                    ((frame-coord-map frame) (start-segment segment))
                    ((frame-coord-map frame) (end-segment segment))))
            segment-list)))
(define box-painter (segment->painter (list
    (make-segment (make-vect 0 0) (make-vect 0 1))
    (make-segment (make-vect 0 1) (make-vect 1 1))
    (make-segment (make-vect 1 1) (make-vect 1 0))
    (make-segment (make-vect 1 0) (make-vect 0 0)))))
(define xrow-painter (segment->painter (list
    (make-segment (make-vect 0 0) (make-vect 1 1))
    (make-segment (make-vect 1 0) (make-vect 0 1)))))
(define rhombus-painter (segment->painter (list
    (make-segment (make-vect 0 0.5) (make-vect 0.5 1))
    (make-segment (make-vect 0.5 1) (make-vect 1 0.5))
    (make-segment (make-vect 1 0.5) (make-vect 0.5 0))
    (make-segment (make-vect 0.5 0) (make-vect 0 0.5)))))