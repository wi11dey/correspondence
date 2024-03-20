(defmacro define-syntax (name definition)
  `(defmacro ,name (&rest body)
     (apply definition body)))

(defmacro syntax-rules (&rest body)
  (let* ((ellipsis (if (listp (car body))
		       '...
		       (pop body)))
	 (literals (car body))
	 (rules body))
    `(lambda (&rest body)
       )))
