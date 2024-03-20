(define error #f)
(define (catch)
  (call-with-current-continuation
   (lambda (continuation)
     (set! error (lambda args (continuation args)))
     #f)))
(let ((message (catch)))
  (if message
      (begin
        (display "error: ")
	(let print ((separate? #f)
		    (rest message))
	  (cond
	   ((null? rest)
	    (newline))
	   ((string? (car rest))
	    (display (car rest))
	    (print #f (cdr rest)))
	   (else
	    (if separate?
		(display " "))
	    (write (car rest))
	    (print #t (cdr rest))))))))
