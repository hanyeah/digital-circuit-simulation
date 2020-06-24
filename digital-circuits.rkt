#lang racket

;=====================================================================================================
 
(require (for-syntax racket racket/syntax))

(provide
 make-circuit-maker
 trit?
 bit?
 ?
 F
 T
 trits
 trit-seq
 bits
 bit-seq
 Not
 And
 Or
 Xor
 Eq
 Nand
 Nor
 Implies
 If
 T?
 F?
 ??
 make-inputs
 truth-table
 run-circuit
 circuit?
 circuit-maker?)

;=====================================================================================================
; Structs for circuit-makers and circuits themselfes.

(define (circuit-maker-printer circuit-maker port mode)
 (fprintf port "#<circuit-maker:~a>" (circuit-maker-name circuit-maker)))

(struct circuit-maker (name proc)
 #:property prop:procedure 1
 #:property prop:custom-write circuit-maker-printer
 #:property prop:object-name (λ (x) (string->symbol (format "make:~a" (circuit-maker-name x)))))

(define (circuit-printer circuit port mode)
 (fprintf port "#<circuit:~a>" (circuit-name circuit)))

(struct circuit (name proc)
 #:property prop:procedure 1
 #:property prop:custom-write circuit-printer
 #:property prop:object-name 0)

;=====================================================================================================
; Trinary logic.

(define ? '?)
(define F 0)
(define T 1)
(define (T? x) (eq? x 1))
(define (F? x) (eq? x 0))
(define (?? x) (eq? x ?))
(define (trit? p) (or (eq? p 0) (eq? p 1) (eq? p ?)))
(define trits '(0 1 ?))
(define trit-seq (in-list trits))

; Binary logic.
(define (bit? p) (or (eq? p 0) (eq? p 1))) 
(define bits '(0 1))
(define bit-seq (in-list bits))

;=====================================================================================================
; Central part of the code

(define-syntax (make-circuit-maker stx)
 (define (wrap stx)
  (syntax-case stx ()
   (id (identifier? #'id) #'(id))
   (_ stx)))
 (syntax-case stx ()
  ((_ name-expr (input ...) (output ...) (xgate-output gate-expr) ...)
   (with-syntax*
    ((((gate-output ...) ...) (map wrap (syntax->list #'(xgate-output ...))))
     (((saved-gate-output ...) ...)
      (map generate-temporaries (syntax->list #'((gate-output ...) ...))))
     (((new-gate-output ...) ...)
      (map generate-temporaries (syntax->list #'((gate-output ...) ...))))
     ((gate-arity ...) (map length (syntax->datum #'((gate-output ...) ...)))))
    (check-make-circuit-maker-form
   #'((input ...) (output ...) ((gate-output ...) gate-expr) ...))
  #'(let ((name (check-name name-expr)))
     (circuit-maker name
      (lambda ()
       (circuit name
        (let ((saved-gate-output ?) ... ... (active (make-parameter #f)))
         (λ (input ... #:report (report #f) #:unstable-error (unstable-error #t))
          (when (active) (error name "direct or indirect recursive call"))
          (parameterize ((active #t))
           (unless (trit? input)
            (error name "input ~s must be a trit, given: ~s" 'input input))...
           (when report
            (printf "~nReport of circuit ~s:~n~n" name)
            (printf "Inputs:~n")
            (printf "~s = ~s~n" 'input input) ...
            (printf "~nInitial state:~n")
            (printf "~s = ~s~n" 'gate-output saved-gate-output) ... ...)
           (let loop ((step 1) (history '()) (gate-output saved-gate-output) ... ...)
            (cond
             ((member (list gate-output ... ...) history)
              (cond
               (unstable-error
                (error name
                 (string-append
                  "repeated unstable state~n"
                  (format "  ~s = ~s~n" 'input input) ...
                  (format "  ~s = ~s~n" 'gate-output gate-output) ... ...)))
               (else
                (eprintf "Warning: circuit halted in unstable state~n")
                (set! history '())
                (values output ...))))
             (else
              (let-values
               (((new-gate-output ...)
                 (let-syntax
                  ([gate-output
                    (make-set!-transformer
                     (lambda (stx)
                      (syntax-case stx (set!)
                       [(set! id v) #'(error name "assignment to gate-output '~s' not allowed" 'id)]
                       [id (identifier? #'id) #'gate-output])))] ... ...
                   [input
                    (make-set!-transformer
                     (lambda (stx)
                      (syntax-case stx (set!)
                       [(set! id v) #'(error name "assignment to input '~s' not allowed" 'id)]
                       [id (identifier? #'id) #'input])))] ...)
                  (let
                   ((vals (call-with-values (λ () gate-expr) list)))
                   (unless (= (length vals) gate-arity)
                    (error name "incorrect nr of values for wires ~s" '(gate-output ...)))
                   (unless (andmap trit? vals)
                    (error name "non trit values found for gate-outputs: ~s~nvalues: ~s"
                     '(gate-output ...) vals))
                   (apply values vals)))) ...)
               (when report
                (printf "~nStep ~s of ~s:~n" step name)
                (printf "~s : ~s -> ~s~n" 'gate-output gate-output new-gate-output) ... ...)
               (cond
                ((and (eq? new-gate-output gate-output) ... ...)
                 (set!-values (saved-gate-output ...) (values new-gate-output ...)) ...
                 (when report
                  (printf "~nFinal state:~n")
                  (printf "~s = ~s~n" 'gate-output gate-output) ... ...
                  (when (and report (member ? (list output ...)))
                   (printf "~nWARNING: some outputs are not well defined.~n"))
                  (printf "~nEnd of report of circuit ~s.~n~n" name))
                 (set! history '())
                 (values output ...))
                (else
                 (loop
                  (add1 step)
                  (cons (list gate-output ... ...) history)
                  new-gate-output ... ...))))))))))))))))))

(define (check-name name)
 (unless (or (symbol? name) (not name))
  (raise-argument-error 'make-circuit-maker "(or/c symbol? #f)" name))
 name)

(define-for-syntax (check-make-circuit-maker-form stx)
 (syntax-case stx ()
  (((input ...) (output ...) ((gate-output ...) gate-expr) ...)
   (check-circuit-form-helper stx
    (syntax->list #'(input ...))
    (syntax->list #'(output ...))
    (syntax->list #'(gate-output ... ...))))))

(define-for-syntax (check-circuit-form-helper stx inputs outputs gate-outputs)
 (define (check-ids type ids)
  (define (check-id id)
   (unless (identifier? id)
    (raise-syntax-error 'make-circuit (format "identifier expected for ~a" type) stx id)))
  (for-each check-id ids)
  (let ((dup (check-duplicates ids free-identifier=?)))
   (when dup (raise-syntax-error 'make-circuit (format "duplicate ~a" type) stx dup))))
 (check-ids 'input inputs)
 (check-ids 'output outputs)
 (check-ids "gate output" gate-outputs)
 (define inputs+wires (remove-duplicates (append inputs gate-outputs) bound-identifier=?))
 (for-each
  (λ (output)
   (unless (member output inputs+wires bound-identifier=?)
    (raise-syntax-error 'make-circuit "unconnected output" stx output)))
  outputs)
 (for-each
  (λ (output)
   (when (member output gate-outputs bound-identifier=?)
    (raise-syntax-error 'make-circuit "a gate-output must not be an input" stx output)))
  inputs)
 #t)

;=====================================================================================================
; Elementary gates.

(define (Not p) (case p ((0) 1) ((1) 0) (else ?)))

(define (And . p)
 (cond
  ((member 0 p) 0)
  ((member ? p) ?)
  (else 1)))

(define (Or . p)
 (cond
  ((member 1 p) 1)
  ((member ? p) ?)
  (else 0)))

(define (Nand . p)
 (cond
  ((member 0 p) 1)
  ((member ? p) ?)
  (else 0)))

(define (Nor . p)
 (cond
  ((member 1 p) 0)
  ((member ? p) ?)
  (else 1)))

(define (Xor . p)
 (cond
  ((member ? p) ?)
  ((odd? (count positive? p)) 1)
  (else 0)))

(define (Eq . x)
 (let loop ((x x) (?? 1) (0? #f) (1? #f))
  (cond
   ((null? x) ??)
   (else
    (case (car x)
     ((0) (if 1? 0 (loop (cdr x) ?? #t 1?)))
     ((1) (if 0? 0 (loop (cdr x) ?? 0? #t)))
     ((?) (loop (cdr x) ? 0? 1?)))))))

(define (Implies a b) (Or (Not a) b))

(define (If condition then else)
 (if (eq? then else) then
  (Or
   (And condition then)
   (And (Not condition) else))))

;=====================================================================================================
; Tables

(define-syntax (truth-table stx)
 (syntax-case stx ()
  ((_ (in ...) expr)
 #'(for*/list ((in trit-seq) ...)
    (list in ... (call-with-values (λ () expr) list))))
  ((_ (in ...) expr #:omit-?)
 #'(for*/list ((in (in-list '(0 1))) ...)
    (list in ... (call-with-values (λ () expr) list))))
  ((_ (in ...) #:omit-? expr)
 #'(for*/list ((in (in-list '(0 1))) ...)
    (list in ... (call-with-values (λ () expr) list))))
  ((_  #:omit-? (in ...) expr)
 #'(for*/list ((in (in-list '(0 1))) ...)
    (list in ... (call-with-values (λ () expr) list))))))

(define (run-circuit circuit list-of-list-of-inputs)
 (for/list ((args (in-list list-of-list-of-inputs)))
  (call-with-values (λ () (apply circuit args)) list)))

(define (make-inputs n include?)
 (define (cons0 x) (cons 0 x))
 (define (cons1 x) (cons 1 x))
 (define (cons? x) (cons ? x))
 (cond
  ((zero? n) '(()))
  (else
   (define inputs (make-inputs (sub1 n) include?))
   (if include?
    (append (map cons0 inputs)
            (map cons1 inputs)
            (map cons? inputs))
    (append (map cons0 inputs)
            (map cons1 inputs))))))

;=====================================================================================================
; The end
