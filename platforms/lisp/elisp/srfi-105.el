(defun srfi-105-uncurl (expr)
  (cond
   ((consp expr)
    (cons (srfi-105-uncurl (car expr))
	  (srfi-105-uncurl (cdr expr))))
   ((symbolp expr)
    )))
