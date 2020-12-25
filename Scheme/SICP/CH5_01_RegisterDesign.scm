;;; This is an exercise program in <SICP> CH5.
;;; Mainly about using a language to describe registers.
;;; Author : Brethland, Late 2019.

(data-paths
    (registers
        ((name res)
            (buttons ((name res<-mult) (source (operation mult)))))
         (name n)
            (buttons ((name n<-plus1) (source (operation plus1)))))
    (operations
        ((name mult)
            (inputs (register n) (register res)))
        ((name plus1)
            (inputs (register n) (constant 1)))
        ((name =)
            (inputs (register n) (constant cnt)))))
(controller
    test-n
        (test =)
        (branch (label fac-done))
        (res<-mult)
        (n<-plus1)
        (goto (label test-n))
    fac-done)

(data-paths
    (registers
        ((name guess)
            (buttons ((name guess<-ave) (source (operation ave)))))
        ((name x)))
    (operations
        ((name squ)
            (inputs (register guess)))
        ((name -)
            (inputs (operation squ) (register x)))
        ((name <)
            (inputs (operation -) (constant eps)))
        ((name /)
            (inputs (register x) (register guess)))
        ((name ave)
            (inputs (register guess) (operation /)))))
(controller
    test-guess
    (test (op <) (op -) (constant eps))
    (branch (label sqrt-done))
    (assign guess (op ave) (reg guess) (op /))
    (goto (label test-guess))
    sqrt-done)

(controller
    (assign continue (label exp-done))
    exp-loop
    (test (op =) (reg n) (const 0))
    (branch (label assign-case))
    (save continue)
    (assign n (op -) (reg n) (const 1))
    (assign continue (label after-exp))
    (goto (label exp-loop))
    after-exp
    (assign val (op *) (reg b) (reg val))
    (goto (label continue))
    assign-case
    (assign val (const 1))
    (goto (label continue))
    exp-done)

(controller
    (assign val (const 1))
    test-cnt
    (test (op =) (reg cnt) (const 0))
    (branch (label exp-done))
    (assign val (op *) (reg val) (reg b))
    (assign cnt (op -) (reg cnt) (const 1))
    (goto (label test-cnt))
    exp-done)

(define exp-machine
    (make-machine
        `(cnt b val)
        (list (list `* *) (list `= =) (list `- -))
        `((assign val (const 1))
            test-cnt
            (test (op =) (reg cnt) (const 0))
            (branch (label exp-done))
            (assign val (op *) (reg val) (reg b))
            (assign cnt (op -) (reg cnt) (const 1))
            (goto (label test-cnt))
            exp-done)))

(define (make-operation-exp expr machine labels operations) 
  (let ((op (lookup-prim (operation-exp-op expr) operations)) 
            (aprocs 
                 (map (lambda (e) 
                           (if (label-exp? e) 
                               (error "can't operate on label -- MAKE-OPERATION-EXP" e) 
                               (make-primitive-exp e machine labels))) 
                      (operation-exp-operands expr)))) 
   (lambda () 
           (apply op (map (lambda (p) (p)) aprocs))))) 

 (define (allocate-stack name) 
         (if (assoc name stack-table) 
             (error "Multiply defined stacks: " name) 
             (set! stack-table 
                   (cons 
                     (list name 
                           (make-stack)) 
                     stack-table))) 
         'stack-allocated) 
  
 (for-each (lambda (reg-name)
                 ((machine 'allocate-stack) 
                  reg-name)) 
               register-names) 
  
 (the-ops 
    (list (list 'initialize-stack 
                (lambda () 
                       (for-each (lambda (stack) 
                                   (stack 'initialize)) 
                                 (map cadr stack-table)))))) 

(define (lookup-register name) 
      (let ((val (assoc name register-table))) 
       (if val 
           (cadr val) 
           (begin 
            (allocate-register name) 
            (lookup-register name))))) 
(define (excute)
    (let ((lists (get-contents pc)))
        (if (null? lists)
            `done
            (begin  
                (if trace-on
                    (display current-label)
                    (display (caar insts)))
                ((instruction-execution-proc (car insts)))
                (set! counter (+ counter 1))
                (if (or (tagged-list? (instruction-text inst) 'goto) 
                          (and (tagged-list? (instruction-text inst) 'branch) 
                               (get-contents flag))) 
                      (set! current-label 
                            (label-exp-label (cadr (instruction-text))))) 
                (excute)))))
(define (print-cnt)
    (display "Execution Times : " counter)
    ((set! counter 0)))