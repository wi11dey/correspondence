(define (unify a b))

(define (quantifier? x)
  (match x
    ((or 'forall '∀ 'exists '∃)
     )))

(define (type-matcher type)
  (case type
    ;; Promotion:
    ((sentence) => sentence?)
    ;; Literals:
    ((natural ℕ) => (λ (candidate)
		      (and (integer? candidate)
			   (>= 0     candidate))))
    ((integer ℤ)  => integer?)
    ((rational ℚ) => rational?)
    ((real ℝ) => real?)
    ((complex ℂ) => complex?)
    ;; Dependent:
    (else => (const (matches type ('quote _))))))

(define (declare in-theory)
  (put in-theory))

(define-syntax theorem
  (syntax-rules ()
    ))

(define-syntax lemma
  (syntax-rules ()
    ((lemma . rest) (theorem . rest))))

