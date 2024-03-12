(define-library (correspondence core)
  (export sentence?)

  (define-record-type sentence
    (make-sentence content)
    sentence?
    (content sentence-content))
  )
