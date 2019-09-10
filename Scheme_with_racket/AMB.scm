(define (an-interger-between low high)
    (require (<= low high))
    (amb low (an-interger-between (+ low 1) high)))
(define (logical-solving)
    (let ((fletcher (amb 2 3 4))
          (cooper (amb 2 3 4 5))
          (baker (amb 1 2 3 4))
          (miller (amb 1 2 3 4 5)))
        (require (> miller cooper))
        (require (not (= (abs (- fletcher cooper)) 1)))
        (let ((smith (amb 1 2 3 4 5)))
            (require (not (= (abs (- fletcher smith)) 1)))
            (list (list `baker baker)
                  (list `cooper cooper)
                  (list `fletcher fletcher)
                  (list `miller miller)
                  (list `smith smith)))))