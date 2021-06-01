;; Stream a
(define zeroes
  (lambda (d)
    (cond [(equal? d 'head) 0]
          [(equal? d 'tail) zeroes])))

;; takes: (Nat, Stream a) -> List a
(define (takes n s)
         (cond [(= n 0) '()]
                [(= n 1) (list (s 'head))]
                [else (cons (s 'head) (takes (- n 1) (s 'tail)))]))

(define-syntax cocase
  (syntax-rules ()
    ((cocase [destructor result] ...)
     (lambda (question)
       (cond [(equal? question destructor) result]
             ...)))))

;; always : a -> Stream a
(define (always x)
  (cocase ['head x]
          ['tail (always x)]))

;; drop : (Nat, Stream a) -> Stream a
(define (drop n xs)
  (cond [(= n 0) xs]
        [(> n 0) (drop (- n 1) (xs 'tail))]))

;; index : (Nat , Stream a) -> a
(define (index n xs)
  ((drop n xs) 'head))

(define (count-up n)
  (cocase ['head n]
          ['tail (count-up (+ n 1))]))

;; coiter : (b -> a , b -> b , b) -> Stream a
(define (coiter make update state)
  (cocase ['head (make state)]
          ['tail (coiter make update (update state))]))

;; maps* : (a -> b , Stream a) -> Stream b
(define (maps* f xs)
  (coiter
    (lambda (xs) (f (xs 'head)))
    (lambda (xs) (xs 'tail))
    xs))

;; corec : (b -> a , (Cont (Stream a) , b) -> b , b) -> Stream a
(define (corec make update state)
  (cocase ['head (make state)]
          ['tail
           (call/cc
             (lambda (finish)
               (corec make update (update finish state))))]))

;; append : (List a , Stream a) -> Stream a
(define (append xs ys)
  (corec
    (lambda (xs) (cond [(null? xs) (ys 'head)]
                       [else (car xs)]))
    (lambda (ret xs) (cond [(null? xs) (ret (ys 'tail))]
                           [else (cdr xs)]))
    xs))

;; infinite-bits : Stream a -> Stream Nat
(define (infinite-bits s)
  (call/cc
    (lambda (restart)
      (infinite-bit0 (s 'head) (s 'tail) 0 restart))))

;; infinite-bit0 : (a , Stream a , Nat , Cont (Stream Nat)) -> Stream Nat
(define (infinite-bit0 bit0 s depth switch)
  (cocase ['head depth]
          ['tail 
           (cond [(equal? (s 'head) bit0)
                  (infinite-bit0 bit0 (s 'tail) (+ depth 1) switch)]
                 [else
                   (call/cc
                     (lambda (return)
                       (switch (infinite-bit1 bit0 (s 'tail) (+ depth 1) return))))])]))

;; infinite-bit1 : (a , Stream a , Nat , Cont (Stream Nat)) -> Stream Nat
(define (infinite-bit1 bit0 s depth switch)
  (cocase ['head depth]
          ['tail 
           (cond [(not (equal? (s 'head) bit0))
                  (infinite-bit1 bit0 (s 'tail) (+ depth 1) switch)]
                 [else
                   (call/cc
                     (lambda (return)
                       (switch (infinite-bit0 bit0 (s 'tail) (+ depth 1) return))))])]))

