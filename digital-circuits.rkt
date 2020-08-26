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
 in-trits
 bits
 in-bits
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
 apply-repeatedly
 values->list
 circuit?
 circuit-maker?
 power-up-signal
 circuit-rename!
 gate?)

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

(struct circuit ((name #:mutable) proc)
 #:property prop:procedure 1
 #:property prop:custom-write circuit-printer
 #:property prop:object-name (λ (circuit) (string->symbol (format "~a" (circuit-name circuit)))))

(define (circuit-rename! circuit name)
 (unless (symbol? name) (raise-argument-error 'circuit-rename "symbol?" 1 name circuit))
 (unless (circuit? circuit) (raise-argument-error "circuit?" 0 name circuit))
 (set-circuit-name! circuit name)
 circuit)

(define (gate-printer gate port mode)
 (fprintf port "#<gate:~a>" (gate-name gate)))

(struct gate (name proc)
 #:property prop:procedure 1
 #:property prop:custom-write gate-printer
 #:property prop:object-name (λ (x) (string->symbol (format "gate:~a" (gate-name x)))))

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
(define in-trits (in-list trits))

; Binary logic.
(define (bit? p) (or (eq? p 0) (eq? p 1))) 
(define bits '(0 1))
(define in-bits (in-list bits))

(define (power-up-guard signal)
 (unless (trit? signal)
  (raise-argument-error 'power-up-signal "trit?" signal))
 signal)

(define power-up-signal (make-parameter ?  power-up-guard 'power-up-signal))

;=====================================================================================================
; Central part of the code

(define-syntax (make-circuit-maker stx)
 (define (wrap stx)
  (syntax-case stx ()
   (id (identifier? #'id) #'(id))
   (_ stx)))
 (syntax-case stx ()
  ((_ name (input ...) (output ...) (xgate-output gate-expr) ...)
   (with-syntax*
    ((((gate-output ...) ...) (map wrap (syntax->list #'(xgate-output ...))))
     (((saved-gate-output ...) ...)
      (map generate-temporaries (syntax->list #'((gate-output ...) ...))))
     (((new-gate-output ...) ...)
      (map generate-temporaries (syntax->list #'((gate-output ...) ...))))
     ((gate-arity ...) (map length (syntax->datum #'((gate-output ...) ...)))))
    (check-make-circuit-maker-form #'(name (input ...) (output ...) ((gate-output ...)) ...))
  #'(circuit-maker 'name
     (lambda ()
      (letrec
       ((the-circuit
         (circuit 'name
          (let ((saved-gate-output (power-up-signal)) ... ... (active (make-parameter #f)))
           (λ (input ... #:report (report #f)
                         #:unstable-error (unstable-error #t)
                         #:indeterminate-error (indeterminate-error #f))
            (define neem (circuit-name the-circuit))
            (when (active) (error neem "direct or indirect recursive call prohibited"))
            (parameterize ((active #t))
             (unless (trit? input) (error neem "input ~s must be a trit, given: ~s" 'input input))
             ... 
             (when report
              (printf "~nReport of circuit ~s:~n" neem)
              (printf "Inputs of circuit ~s:~n" neem)
              (printf "  ~s = ~s~n" 'input input) ...
              (printf "~nInitial state of circuit ~s:~n" neem)
              (printf "  ~s = ~s~n" 'gate-output saved-gate-output) ... ...)
             (let loop ((step 1) (history (set)) (gate-output saved-gate-output) ... ...)
              (cond
               ((set-member? history (list gate-output ... ...))
                (cond
                 (unstable-error
                  (error neem
                   (string-append
                    "repeated unstable state~n"
                    (format "  ~s = ~s~n" 'input input) ...
                    (format "  ~s = ~s~n" 'gate-output gate-output) ... ...)))
                 (else
                  (eprintf "Warning: ~a halted in unstable state~n" neem)
                  (set! history (set))
                  (values output ...))))
               (else
                (let-values
                 (((new-gate-output ...)
                   (let-syntax
                    ([gate-output
                      (make-set!-transformer
                       (lambda (stx)
                        (syntax-case stx (set!)
                         [(set! id v)
                          (raise-syntax-error (syntax->datum #'name)
                           "assignment to gate-output prohibited" stx #'id)]
                         [id (identifier? #'id) #'gate-output])))] ... ...
                     [input
                      (make-set!-transformer
                       (lambda (stx)
                        (syntax-case stx (set!)
                         [(set! id v)
                          (raise-syntax-error (syntax->datum #'name)
                           "assignment to input prohibited" stx #'id)]
                         [id (identifier? #'id) #'input])))] ...)
                    (let
                     ((vals (values->list gate-expr)))
                     (unless (= (length vals) gate-arity)
                      (error neem "incorrect nr of values for wires ~s" '(gate-output ...)))
                     (unless (andmap trit? vals)
                      (error neem "non trit values found for gate-outputs: ~s~nvalues: ~s"
                       '(gate-output ...) vals))
                     (apply values vals)))) ...)
                 (cond
                  ((and (eq? new-gate-output gate-output) ... ...)
                   (set!-values (saved-gate-output ...) (values new-gate-output ...)) ...
                   (when report
                    (printf "~nFinal state of circuit ~s:~n" neem)
                    (printf "  ~s = ~s~n" 'gate-output gate-output) ... ...
                    (when (member ? (list output ...))
                     (eprintf "~nWARNING: one or more indeterminate outputs.~n"))
                    (printf "~nEnd of report of circuit ~s.~n~n" neem))
                   (set! history '())
                   (define outputs (list output ...))
                   (when (and (member ? outputs) indeterminate-error)
                    (error neem "indeterminate outputs: ~n~a"
                     (string-append
                      (if (?? output) (format "  ~a~n" 'output) "") ...)))
                   (values output ...))
                  (else
                   (when report
                    (printf "~nStep ~s of circuit ~s:~n" step neem)
                     (unless (eq? gate-output new-gate-output)
                      (printf "  ~s : ~s -> ~s~n" 'gate-output gate-output new-gate-output)) ... ...)
                   (loop
                    (add1 step)
                    (set-add history (list gate-output ... ...))
                    new-gate-output ... ...)))))))))))))
       the-circuit)))))))

(define-for-syntax (check-make-circuit-maker-form stx)
 (syntax-case stx ()
  ((name (input ...) (output ...) ((gate-output ...)) ...)
   (unless (identifier? #'name)
    (raise-syntax-error 'make-circuit-maker "identifier expected" stx #'name))
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

(define-syntax-rule (define-gate (name . args) . body)
 (define name (gate 'name (λ args . body))))

(define-gate (Not p) (case p ((0) 1) ((1) 0) (else ?)))

(define-gate (And . p)
 (cond
  ((member 0 p) 0)
  ((member ? p) ?)
  (else 1)))

(define-gate (Or . p)
 (cond
  ((member 1 p) 1)
  ((member ? p) ?)
  (else 0)))

(define-gate (Nand . p)
 (cond
  ((member 0 p) 1)
  ((member ? p) ?)
  (else 0)))

(define-gate (Nor . p)
 (cond
  ((member 1 p) 0)
  ((member ? p) ?)
  (else 1)))

(define-gate (Xor . p)
 (cond
  ((member ? p) ?)
  ((odd? (count positive? p)) 1)
  (else 0)))

(define-gate (Eq . x)
 (let loop ((x x) (?? 1) (0? #f) (1? #f))
  (cond
   ((null? x) ??)
   (else
    (case (car x)
     ((0) (if 1? 0 (loop (cdr x) ?? #t 1?)))
     ((1) (if 0? 0 (loop (cdr x) ?? 0? #t)))
     ((?) (loop (cdr x) ? 0? 1?)))))))

(define-gate (Implies a b) (Or (Not a) b))

(define-gate (If condition then else)
 (if (eq? then else) then
  (Or
   (And condition then)
   (And (Not condition) else))))

;=====================================================================================================
; Tables

(define-syntax (truth-table stx)
 (define (check ids)
  (let ((ids (syntax->list ids)))
   (for ((id (in-list ids)))
    (unless (identifier? id)
     (raise-syntax-error 'truth-table "identifier expected" stx id)))
   (define dup-id (check-duplicate-identifier ids))
   (when dup-id (raise-syntax-error 'truth-table "duplicate identifier" stx dup-id))))
 (syntax-case stx ()
  ((_ (id ...) expr)
   (check #'(id ...))
 #'(for*/list ((id in-trits) ...)
    (list id ... (call-with-values (λ () expr) list))))
  ((_ (id ...) expr #:omit-?)
   (check #'(id ...))
 #'(for*/list ((id (in-list '(0 1))) ...)
    (list id ... (call-with-values (λ () expr) list))))
  ((_ (id ...) #:omit-? expr)
   (check #'(id ...))
 #'(for*/list ((id (in-list '(0 1))) ...)
    (list id ... (call-with-values (λ () expr) list))))
  ((_  #:omit-? (id ...) expr)
   (check #'(id ...))
 #'(for*/list ((id (in-list '(0 1))) ...)
    (list id ... (call-with-values (λ () expr) list))))))

(define (apply-repeatedly proc list-of-list-of-inputs)
 (for/list ((args (in-list list-of-list-of-inputs)))
  (values->list (apply proc args))))

(define-syntax (values->list stx)
 (syntax-case stx ()
  ((_ expr)
 #'(call-with-values (λ () expr) list))))

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
