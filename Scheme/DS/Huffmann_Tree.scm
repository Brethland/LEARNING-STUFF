;;; This is an program implementing Huffmann Tree Data structures.
;;; Some code comes from <SICP>
;;; Author : Brethland, Early 2019.

(define (equal? a b)
    (cond ((and (not (pair? a)) (not (pair? b))) (eq? a b))
          ((or (not (pair? a)) (not (pair? b))) #f)
          (else (and (equal? (car a) (car b)) (equal? (cdr a) (cdr b))))))
(define (element-of-set? x set)
    (cond ((null? set) #f)
          ((equal? x (car set)) #t)
          (else (element-of-set? x (cdr set)))))
(define (make-leaf symbol weight)
    (list `leaf symbol weight))
(define (leaf? ob)
    (eq? (car ob) `leaf))
(define (symbol-leaf x) (car (cdr x)))
(define (weight-leaf x) (car (cdr (cdr x))))
(define (make-code-tree left right)
    (list left
          right
          (append (symbols left) (symbols right))
          (+ (weight left) (weight right))))
(define (left-branch tree) (car tree))
(define (right-branch tree) (car (cdr tree)))
(define (symbols tree)
    (if (leaf? tree)
        (list (symbol-leaf tree))
        (car (cdr (cdr tree)))))
(define (weight tree)
    (if (leaf? tree)
        (weight-leaf tree)
        (car (cdr (cdr (cdr tree))))))
(define (decode bits tree)
    (define (decode-1 bits current-branch)
        (if (null? bits)
            `()
            (let ((next-branch
                    (choose-branch (car bits) current-branch)))
                (if (leaf? next-branch)
                    (cons (symbol-leaf next-branch)
                          (decode-1 (cdr bits) tree))
                    (decode-1 (cdr bits) next-branch)))))
    (decode-1 bits tree))
(define (choose-branch bit branch)
    (cond ((= bit 0) (left-branch branch))
          ((= bit 1) (right-branch branch))
          (else (display "bad bit -- CHOOSE-BRANCH" bit))))
(define (adjoin-set x set)
    (cond ((null? set) (list x))
          ((< (weight x) (weight (car set))) (cons x set))
          (else (cons (car set) (adjoin-set x (cdr set))))))
(define (make-leaf-set pairs)
    (if (null? pairs)
        `()
        (let ((pair (car pairs)))
            (adjoin-set (make-leaf (car pair)
                                    (car (cdr pair)))
                        (make-leaf-set (cdr pairs))))))
(define sample-tree
    (make-code-tree (make-leaf `A 4)
                    (make-code-tree
                        (make-leaf `B 2)
                        (make-code-tree (make-leaf `D 1)
                                        (make-leaf `C 1)))))
(define sample-message `(0 1 1 0 0 1 0 1 0 1 1 1 0))
; (decode sample-message sample-tree)
(define (encode message tree)
    (if (null? message)
        `()
        (append (encode-symbol (car message) tree)
            (encode (cdr message) tree))))
(define (encode-symbol sym tree)
    (if (leaf? tree) `()
          (let ((left-symbol (symbols (left-branch tree)))
                      (right-symbol (symbols (right-branch tree))))
                    (cond ((element-of-set? sym left-symbol) (cons 0 (encode-symbol sym (left-branch tree))))
                          ((element-of-set? sym right-symbol) (cons 1 (encode-symbol sym (right-branch tree))))
                          (else (display "Not in this tree" sym))))))
; (encode `(A D A B B C A) sample-tree)
(define (generate-huffman-tree pairs)
    (successive-merge (make-leaf-set pairs)))
(define (successive-merge set)
    (if (= (length set) 1)
        (car set)
        (let ((min-pair (car set))
              (min2-pair (car (cdr set))))
            (successive-merge (adjoin-set (make-code-tree min-pair min2-pair) (cdr (cdr set)))))))
(define rock-words-tree (generate-huffman-tree `((A 2) (NA 16) (BOOM 1) (SHA 3) (GET 2) (YIP 9) (JOB 2) (WAH 1))))
(length (encode `(GET A JOB 
          SHA NA NA NA NA NA NA NA NA 
          GET A JOB 
          SHA NA NA NA NA NA NA NA NA 
          WAH YIP YIP YIP YIP YIP YIP YIP YIP YIP 
          SHA BOOM) rock-words-tree))