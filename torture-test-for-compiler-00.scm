;;; torture-test-for-compiler-00.scm
;;; Testing pvar, bvar, lambda-simple, applic, #f, #t
;;; This test should return #t
;;;
;;; Programmer: Mayer Goldberg, 2010


(((((lambda (a) (lambda (b) (((lambda (a) (lambda (b) ((a b) (lambda
(x) (lambda (y) y))))) ((lambda (n) ((n (lambda (x) (lambda (x)
(lambda (y) y)))) (lambda (x) (lambda (y) x)))) (((lambda (a) (lambda
(b) ((b (lambda (n) ((lambda (p) (p (lambda (a) (lambda (b) b)))) ((n
(lambda (p) (((lambda (a) (lambda (b) (lambda (c) ((c a) b))))
((lambda (n) (lambda (s) (lambda (z) (s ((n s) z))))) ((lambda (p) (p
(lambda (a) (lambda (b) a)))) p))) ((lambda (p) (p (lambda (a) (lambda
(b) a)))) p)))) (((lambda (a) (lambda (b) (lambda (c) ((c a) b))))
(lambda (x) (lambda (y) y))) (lambda (x) (lambda (y) y))))))) a))) a)
b))) ((lambda (n) ((n (lambda (x) (lambda (x) (lambda (y) y))))
(lambda (x) (lambda (y) x)))) (((lambda (a) (lambda (b) ((b (lambda
(n) ((lambda (p) (p (lambda (a) (lambda (b) b)))) ((n (lambda (p)
(((lambda (a) (lambda (b) (lambda (c) ((c a) b)))) ((lambda (n)
(lambda (s) (lambda (z) (s ((n s) z))))) ((lambda (p) (p (lambda (a)
(lambda (b) a)))) p))) ((lambda (p) (p (lambda (a) (lambda (b) a))))
p)))) (((lambda (a) (lambda (b) (lambda (c) ((c a) b)))) (lambda (x)
(lambda (y) y))) (lambda (x) (lambda (y) y))))))) a))) b) a)))))
((lambda (n) ((lambda (p) (p (lambda (a) (lambda (b) b)))) ((n (lambda
(p) (((lambda (a) (lambda (b) (lambda (c) ((c a) b)))) ((lambda (n)
(lambda (s) (lambda (z) (s ((n s) z))))) ((lambda (p) (p (lambda (a)
(lambda (b) a)))) p))) (((lambda (a) (lambda (b) ((b (a (lambda (a)
(lambda (b) ((a (lambda (n) (lambda (s) (lambda (z) (s ((n s) z))))))
b))))) (lambda (x) (lambda (y) y))))) ((lambda (p) (p (lambda (a)
(lambda (b) a)))) p)) ((lambda (p) (p (lambda (a) (lambda (b) b))))
p))))) (((lambda (a) (lambda (b) (lambda (c) ((c a) b)))) (lambda (x)
x)) (lambda (x) x))))) (lambda (x) (lambda (y) (x (x (x (x (x
y))))))))) (((lambda (a) (lambda (b) ((b (a (lambda (a) (lambda (b)
((a (lambda (n) (lambda (s) (lambda (z) (s ((n s) z)))))) b)))))
(lambda (x) (lambda (y) y))))) (((lambda (a) (lambda (b) ((b (a
(lambda (a) (lambda (b) ((a (lambda (n) (lambda (s) (lambda (z) (s ((n
s) z)))))) b))))) (lambda (x) (lambda (y) y))))) ((lambda (x) (lambda
(y) (x (x (x y))))) (lambda (x) (lambda (y) (x (x y)))))) (lambda (x)
(lambda (y) (x (x (x y))))))) (lambda (x) (lambda (y) (x (x (x (x (x
y))))))))) #t) #f)
