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
