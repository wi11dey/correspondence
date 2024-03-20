;; Copyright (C) 2012 David A. Wheeler and Alan Manuel K. Gloria. All Rights Reserved.

;; Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

;; The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

  ; ------------------------------
  ; Curly-infix support procedures
  ; ------------------------------

  ; Return true if lyst has an even # of parameters, and the (alternating)
  ; first parameters are "op".  Used to determine if a longer lyst is infix.
  ; If passed empty list, returns true (so recursion works correctly).
  (define (even-and-op-prefix? op lyst)
    (cond
      ((null? lyst) #t)
      ((not (pair? lyst)) #f)
      ((not (equal? op (car lyst))) #f) ; fail - operators not the same
      ((not (pair? (cdr lyst)))  #f) ; Wrong # of parameters or improper
      (#t   (even-and-op-prefix? op (cddr lyst))))) ; recurse.

  ; Return true if the lyst is in simple infix format
  ; (and thus should be reordered at read time).
  (define (simple-infix-list? lyst)
    (and
      (pair? lyst)           ; Must have list;  '() doesn't count.
      (pair? (cdr lyst))     ; Must have a second argument.
      (pair? (cddr lyst))    ; Must have a third argument (we check it
                             ; this way for performance)
      (even-and-op-prefix? (cadr lyst) (cdr lyst)))) ; true if rest is simple

  ; Return alternating parameters in a lyst (1st, 3rd, 5th, etc.)
  (define (alternating-parameters lyst)
    (if (or (null? lyst) (null? (cdr lyst)))
      lyst
      (cons (car lyst) (alternating-parameters (cddr lyst)))))

  ; Not a simple infix list - transform it.  Written as a separate procedure
  ; so that future experiments or SRFIs can easily replace just this piece.
  (define (transform-mixed-infix lyst)
     (cons '$nfx$ lyst))

  ; Given curly-infix lyst, map it to its final internal format.
  (define (process-curly lyst)
    (cond
     ((not (pair? lyst)) lyst) ; E.G., map {} to ().
     ((null? (cdr lyst)) ; Map {a} to a.
       (car lyst))
     ((and (pair? (cdr lyst)) (null? (cddr lyst))) ; Map {a b} to (a b).
       lyst)
     ((simple-infix-list? lyst) ; Map {a OP b [OP c...]} to (OP a b [c...])
       (cons (cadr lyst) (alternating-parameters lyst)))
     (#t  (transform-mixed-infix lyst))))


  ; ------------------------------------------------
  ; Key procedures to implement neoteric-expressions
  ; ------------------------------------------------

  ; Read the "inside" of a list until its matching stop-char, returning list.
  ; stop-char needs to be closing paren, closing bracket, or closing brace.
  ; This is like read-delimited-list of Common Lisp.
  ; This implements a useful extension: (. b) returns b.
  (define (my-read-delimited-list my-read stop-char port)
    (let*
      ((c   (peek-char port)))
      (cond
        ((eof-object? c) (read-error "EOF in middle of list") '())
        ((eqv? c #\;)
          (consume-to-eol port)
          (my-read-delimited-list my-read stop-char port))
        ((my-char-whitespace? c)
          (read-char port)
          (my-read-delimited-list my-read stop-char port))
        ((char=? c stop-char)
          (read-char port)
          '())
        ((or (eq? c #\)) (eq? c #\]) (eq? c #\}))
          (read-char port)
          (read-error "Bad closing character"))
        (#t
          (let ((datum (my-read port)))
            (cond
               ((eq? datum '.)
                 (let ((datum2 (my-read port)))
                   (consume-whitespace port)
                   (cond
                     ((eof-object? datum2)
                      (read-error "Early eof in (... .)\n")
                      '())
                     ((not (eqv? (peek-char port) stop-char))
                      (read-error "Bad closing character after . datum"))
                     (#t
                       (read-char port)
                       datum2))))
               (#t
                   (cons datum
                     (my-read-delimited-list my-read stop-char port)))))))))


  ; Implement neoteric-expression's prefixed (), [], and {}.
  ; At this point, we have just finished reading some expression, which
  ; MIGHT be a prefix of some longer expression.  Examine the next
  ; character to be consumed; if it's an opening paren, bracket, or brace,
  ; then the expression "prefix" is actually a prefix.
  ; Otherwise, just return the prefix and do not consume that next char.
  ; This recurses, to handle formats like f(x)(y).
  (define (neoteric-process-tail port prefix)
      (let* ((c (peek-char port)))
        (cond
          ((eof-object? c) prefix)
          ((char=? c #\( ) ; Implement f(x)
            (read-char port)
            (neoteric-process-tail port
                (cons prefix (my-read-delimited-list neoteric-read-real #\) port))))
          ((char=? c #\[ )  ; Implement f[x]
            (read-char port)
            (neoteric-process-tail port
                  (cons '$bracket-apply$
                    (cons prefix
                      (my-read-delimited-list neoteric-read-real #\] port)))))
          ((char=? c #\{ )  ; Implement f{x}
            (read-char port)
            (neoteric-process-tail port
              (let ((tail (process-curly
                      (my-read-delimited-list neoteric-read-real #\} port))))
                (if (eqv? tail '())
                  (list prefix) ; Map f{} to (f), not (f ()).
                  (list prefix tail)))))
          (#t prefix))))


  ; To implement neoteric-expressions, modify the reader so
  ; that [] and {} are also delimiters, and make the reader do this:
  ; (let* ((prefix
  ;           read-expression-as-usual
  ;       ))
  ;   (if (eof-object? prefix)
  ;     prefix
  ;     (neoteric-process-tail port prefix)))

  ; Modify the main reader so that [] and {} are also delimiters, and so
  ; that when #\{ is detected, read using my-read-delimited-list
  ; any list from that port until its matching #\}, then process
  ; that list with "process-curly", like this:
  ;   (process-curly (my-read-delimited-list #\} port))
