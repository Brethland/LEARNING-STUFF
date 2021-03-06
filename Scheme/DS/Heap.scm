;;; This is an implementation of heap.
;;; Written for teaching purpose
;;; Arthur : Brethland, Late 2019.

(define (heap-node value left right) (list value left right))
(define (insert x hp)
  (if (null? hp)
      (heap-node x `() `())
      (if (< (car hp) x)
	  (heap-node (car hp) (caddr hp) (insert x (cadr hp)))
	  (heap-node x (caddr hp) (insert (car hp) (cadr hp))))))
(define (pop hp)
  (if (null? (cadr hp))
      `()
      (heap-node (car (cadr hp))
		 (cons (cadr (cadr hp)) (caddr (cadr hp)))
		 (caddr hp))))
(define (top hp)
  (if (null? hp)
      (display "ERROR : Heap is empty!")
      (car hp)))
(define (empty? hp)
  (null? hp))
(define (size hp)
  (if (null? hp) 0
      (+ 1 (size (cadr hp)) (size (caddr hp)))))
 
