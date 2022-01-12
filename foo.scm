(define foo (lambda (x) (lambda (y) x)))
((foo 1) 2)