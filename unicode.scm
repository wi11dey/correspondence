(define-syntax ¬
  (syntax-rules ()
    ((¬ . rest) (not . rest))))

(define-syntax ∈
  (syntax-rules ()
    ((∈ . rest) (in . rest))))

(define-syntax ≠
  (syntax-rules ()
    ((≠ . rest) (=/= . rest))))

(define-syntax =/=
  (syntax-rules ()
    ((=/= . rest) (not (= . rest)))))
