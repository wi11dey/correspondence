(import
 (srfi 128)
 (rename
  (srfi 146 hash)
  (hashmap mapping)
  (hashmap-set mapping-set)
  (hashmap-ref mapping-ref)))

(define-record-type <variable>
  (variable symbol de-bruijn-index)
  variable?
  (symbol variable-symbol)
  (de-bruijn-index variable-de-bruijn-index))

(define (de-bruijn form)
  (let recurse
      ((depth 0)
       (variable-map (mapping (make-default-comparator))))
    (match form
      ((= binder
	  (and
	   (not #f)
	   bound-variable))
       (recurse
	(+ depth 1)
	(mapping-set bound-variable depth)))
      ((? symbol? symbol)
       (mapping-ref variable-map symbol
		    (λ () symbol)
		    (λ (binder-depth)
		      (variable
		       symbol
		       (- depth binder-depth)))))
      (else
       form))))

(define (α=? form1 form2)
  (cond
   ((and
     (variable? form1)
     (variable? form2))
    (=
     (variable-de-bruijn-index form1)
     (variable-de-bruijn-index form2)))
   ((and
     (pair? form1)
     (pair? form2))
    (and
     (α=?
      (car form1)
      (car form2))
     (α=?
      (cdr form1)
      (cdr form2))))
   ((and
     (vector? form1)
     (vector? form2))
    (α=?
     (vector->list form1)
     (vector->list form2)))   
   (else
    (equal? form1 form2))))
