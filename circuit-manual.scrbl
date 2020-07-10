#lang scribble/manual

@;====================================================================================================
@(require
  scribble/core
  "digital-circuits.rkt"
  "scribble-utensils.rkt"
  (for-label "digital-circuits.rkt" racket racket/block)
  (for-template "digital-circuits.rkt" racket)
  (for-syntax racket)) 
@title[#:version ""]{Digital circuits}
@author{Jacob J. A. Koot}
@(defmodule "digital-circuits.rkt" #:packages ())
@section{Introduction}
Module @hyperlink["digital-circuits.rkt"]{digital-circuits.rkt}
provides a simple tool for the preparation of procedures for digital simulation of digital
electronic circuits. Given the digital inputs such a procedure calculates the digital outputs.
It can have an internal state that is preserved between successive calls.
These calls can be regarded as successive points of
time at which the signals on the inputs can be changed.
The outputs and new internal state can depend on both the inputs and the former internal state.
@seclink["Ternary logic"]{Ternary logic} is used such as to include indeterminate signals:
@inset{@Tabular[
(("variable" "value" "predicate" "description" (list "is a " @nbr[trit?]) (list "also a " @nbr[bit?]))
 (@nbr[F] @nbr['0] @nbr[F?] "false, off, low" "yes" "yes")
 (@nbr[T] @nbr['1] @nbr[T?] "true, on, high"  "yes" "yes")
 (@nbr[?] @nbr['?] @nbr[??] "indeterminate"   "yes" "no"))
 #:sep (hspace 2)
 #:row-properties '((top-border bottom-border) () () bottom-border)
 #:column-properties '(center center center center center center)]}
Let n be the number of all wires in a circuit.
The circuit cannot assume more than 3@↑{n} distinct ternary digital states, usually much less.
@nbr[F] and @nbr[T] are no
@seclink["booleans" #:doc '(lib "scribblings/reference/reference.scrbl")]{booleans}
in the sense of predicate @nbr[boolean?], id est
@nbr[(boolean? F)] → @nbr[#f] and @nbr[(boolean? T)] → @nbr[#f].
Use predicates @nbr[bit?] and @nbr[trit?] in stead.

@elemtag{D-latch}
As introductory example a D-latch:@(lb)
It has two inputs, which will be called ‘@tt{in}’ and ‘@tt{clock}’.@(lb)
It has two outputs, which will be called ‘@tt{state}’ and ‘@nb{@tt{state-inverse}}’.@(lb)
The outputs are preserved as internal state as well.@(lb)
They always are inverses of each other.@(lb)
After switching the inputs the new @tt{state}
can depend on the previous @tt{state} too.@(lb)
The following transition table applies:
@inset{@Tabular[
(((tt "in")
  (tt "clock")
  (list "old" (hspace 1) (tt "state"))
  (list "new" (hspace 1) (tt "state"))
  "action")
 ("any"     (tt "0") (tt "state") (tt "state") "state preserved")
 ((tt "0" ) (tt "1") "any"        (tt "0")     "reset")
 ((tt "1" ) (tt "1") "any"        (tt "1")     "set"))
 #:row-properties '((top-border bottom-border) () () bottom-border)
 #:column-properties '(center center center center left)
 #:sep (hspace 2)]}
Hence, in order to set or reset the @nb{D-latch},
set @tt{in} to @nbr[1] cq @nbr[0] and apply a @nbr[1]-pulse to the @tt{clock}.
Leave the @tt{clock} low at @nbr[0] in order to preserve the state.
There are several ways to construct a D-latch.
The following diagram shows a D-latch consisting of four @nbr[Nand]-gates.@(lb)
@ignore{@inset{@image["D-Type_Transparent_Latch.svg"]}}
@inset{@image["D-latch.gif" #:scale 0.5]}
With syntax @nbr[make-circuit-maker] a procedure for simulation of the circuit
can be made by straightforwardly listing the elements of the diagram:
@Interaction*[
(define make-D-latch
 (make-circuit-maker
  D-latch               (code:comment "name")
  (in clock)            (code:comment "inputs")
  (state state-inverse) (code:comment "outputs")
  (code:comment "Gates:")
  (reset         (Nand in    clock))
  (SET           (Nand reset clock))
  (state         (Nand reset state-inverse))
  (state-inverse (Nand SET   state))))]
In fact syntax @nbr[make-circuit-maker] produces a thunk, called a ‘circuit maker’,
that returns a procedure for the simulation, called a ‘circuit procedure’.
We must call the circuit maker in order to make an instance of the circuit procedure proper.
In section @secref["mcm"] we shall see why the circuit procedure is not returned immediately.
@Interaction*[(define D-latch (make-D-latch))]
Procedure @tt{D-latch} accepts the two arguments @tt{in} and @tt{clock}
and returns the two values @tt{state} and @tt{state-inverse}.
Via the wires @tt{state} and @tt{state-inverse} the @tt{state} is fed back to itself
via the two @nbr[Nand]-gates at the right in the diagram.
When the @tt{clock} is @nbr[0], both @tt{set} and @tt{reset} raise to @nbr[1]
(as far as not already @nbr[1])
and the two @nbr[Nand]-gates act as a loop of two inverters for
the signals @tt{state} and @tt{state-inverse}.
@note{When power is switched on, the D-latch must be reset or set with a @nbr[1]-pulse on the
@tt{clock} and @tt{in} hold at @nbr[0] or @nbr[1].
This is necessary in order to stabilize the @tt{state} and @tt{state-inverse}.
Otherwise they may vibrate for a while,
both simultaneously receiving the same signal and simultaneously sending the same inverted signal,
which means that they simultaneously remain switching.
Once stable, the @tt{state} and @tt{state-inverse} are inverses of each other
and remain as they are after the @tt{clock} falls down from @nb{@nbr[1] to @nbr[0]}.}
Let's test the @nb{D-latch} for all combinations of @seclink["binary"]{binary} values for
@tt{in}, @tt{clock} and @nb{old @tt{state}:}
@(define D-latch-comment
  (list "Send signals " @black{@tt{in}} " and " @black{@tt{clock}} " to the D-latch and check."))
@Interaction*[
(define (test/make-table) (code:comment "Does tests and gathers info in a table.")
 (for*/list ((state in-bits) (clock in-bits) (in in-bits))
  (code:comment #,(list "First put the D-latch in old state " @black{@tt{state}} " and check"))
  (code:comment "that the D-latch indeed assumes this state.")
  (define-values (old-state old-state-inverse) (D-latch state 1))
  (unless
   (and
    (eq? old-state state)
    (eq? old-state-inverse (Not state)))
   (error "test fails"))
  (code:comment #,D-latch-comment)
  (define-values (new-state new-state-inverse) (D-latch in clock))
  (code:comment "Check the results.")
  (unless 
   (and
    (eq? new-state (If clock in state))
    (eq? new-state-inverse (Not new-state)))
   (error "test fails"))
  (code:comment "Add a line with all details to the table.")
  (list in clock old-state new-state
   (cond (code:comment "Description of the action.")
    ((= clock 0) "preserve state")
    ((= in 0)
     (if (= in old-state)
      "reset (was already reset)"
      "reset"))
    ((= in 1)
     (if (= in old-state)
      "set (was already set)"
      "set"))))))
(code:comment " ")
(define (do-test-and-print-table)
 (code:comment "We print the details in a table.")
 (code:comment "First the header of the table.")
 (printf " ~n")
 (define line (string-append (make-string 58 #\─) "\n"))
 (printf line)
 (printf "in  clock  old-state  new-state  action~n")
 (printf line)
 (code:comment "The test proper.")
 (define table (test/make-table))
 (code:comment "Print the results.")
 (for ((line (in-list table)))
  (apply printf " ~s    ~s        ~s          ~s      ~a~n" line))
 (code:comment "Close the table.")
 (printf line)
 (code:comment "Arriving here means that all went well.")
 (printf "Hurray, test passed.~n"))
(code:comment " ")
(do-test-and-print-table)]
@(reset-Interaction*)
More examples in section @secref["Elaborated examples"].
@section[#:tag "mcm"]{Make-circuit-maker}
@(define cmnt (list "An assignment, but "
                    @(black @tt{n})
                    " is not an "
                    @black{@tt{@italic{input}}}
                    " nor a "
                    @@black{@tt{@italic{gate-output}}}
                    "."))
@(defform-remove-empty-lines
@defform[(make-circuit-maker name (input ...) (output ...) gate ...)
#:grammar ((name id)
           (input id)
           (output id)
           (gate (gate-output gate-expr) ((gate-output ...) gate-expr))
           (gate-output id))
#:contracts ((gate-expr (values trit? ...)))]{
Returns a thunk.
Each time the thunk is called it returns a distinct instance of a
@elemref["circuit procedure"]{circuit procedure},
id est, an instance with its own internal state.
This is important when the @nbr[output]s of the circuit may depend on a preserved internal state and
several instances are needed in one or more @nb{other circuits.}
Each such instance must have its own internal state in order that
they @nb{do not} perturb each other's internal states.

The following restrictions apply:

• The @nbr[input]s must be distinct identifiers without duplicates.@(lb)
• The @nbr[output]s must be distinct identifiers without duplicates.@(lb)
• All @nbr[gate-output]s must be distinct identifiers without duplicates.@(lb)
• The set of the @nbr[input]s and that of the @nbr[gate-output]s must be disjunct.@(lb)
• The @nbr[output]s must be a subset of the conjunction of @nbr[input]s and @nbr[gate-output]s.@(lb)
• Within each @nbr[gate-expr] all identifiers of the @nbr[input]s
and @nbr[gate-output]s are bound,@(lb)
@(hspace 2)those of other @nbr[gate]s included.
They can be used as inputs of the @nbr[gate].@(lb)
• Assignments to @nbr[input]s, @nbr[output]s and @nbr[gate-output]s are inhibited.@(lb)
• Each @nbr[gate-expr] must return as many values as its @nbr[gate] has @nbr[gate-output]s.@(lb)
@(hspace 2)These values must be @nbrl[trit?]{trits} and are transmitted to the
@nbr[gate-output]s.@(lb)
• A @nbr[gate-expr] must not involve direct nor indirect calls to the circuit it is part of.

The last two requirements are checked while a
@elemref["circuit procedure"]{circuit procecure} is running.
The other requirements are checked immediately during expansion.
The @nbr[gate-expr]s are not yet evaluated.
They will be incorporated in the circuit procedure made by the circuit maker
and will be evaluated one or more times when the circuit procedure is called.

The @nbr[name] is used for the @nbr[object-name] and the
@seclink["print-unreadable"
#:doc '(lib "scribblings/reference/reference.scrbl")]{printed form}
of the circuit maker and the circuit procedures it makes.
Here is an empty circuit showing how the @nbr[object-name]s and
@seclink["print-unreadable"
#:doc '(lib "scribblings/reference/reference.scrbl")]{printed forms} look like:
@Interaction[
(define make-empty-circuit (make-circuit-maker nothing () ()))
(define empty-circuit (make-empty-circuit))
(values
 (object-name make-empty-circuit)
 (object-name empty-circuit)
 make-empty-circuit
 empty-circuit)]
A @nbr[gate-expr] can include calls to gates and other circuits,
but it must not directly nor indirectly call the circuit procedure it belongs to,
for this would represent an infinitely deep nesting of the circuit,
which in real life is impossible, of course.
A circuit can have circular dependencies between its internal signals, though.
For example the signals @tt{state} and @nb{@tt{state-inverse}}
in the above @nb{@elemref["D-latch"]{D-latch}} have such dependency.
When a @nbr[gate-expr] directly or indirectly calls the circuit procedure it is part of,
an exception is raised:
@Interaction[
(define make-nested-circuit
 (make-circuit-maker nested-circuit
  () () (() (nested-circuit))))
(define nested-circuit (make-nested-circuit))
(nested-circuit)]
A @nbr[gate-expr] cannot make assignments to @nbr[input]s or @nbr[gate-output]s.
@Interaction[
(make-circuit-maker wrong-circuit (var) () (() (set! var ?)))]
@Interaction[
(make-circuit-maker wrong-circuit
 () () (var (set!-values (var) "will not be accepted")))]
@note{In DrRacket the @nbr[var] is highlighted with red background and the message ends with:
“@tt{in: @red{var}}”.}
A @nbr[gate] is not required to have outputs.
Such a @nbr[gate] can be used for inclusion of checks and for printed output
as a probe on some or all wires:
@Interaction[
(define make-probed-circuit
 (let ((n 0))
  (make-circuit-maker probed-circuit () ()
   (a 1)
   (b (Not a))
   (c (Not b))
   (() (code:comment "probe:")
    (begin
     (printf "Step ~s: a=~s, b=~s, c=~s.~n" n a b c)
     (set! n (add1 n))
     (code:comment #,cmnt)
     (code:comment #,(list @nbr[set!] " returns " @(Void) ", but we must not return any value."))
     (code:comment "Therefore we finish with:")
     (values))))))
(define probed-circuit (make-probed-circuit))
(probed-circuit)]
The probe shows how the signal travels through the circuit from @tt{a} via @tt{b} to @tt{c}.
Notice that the @nbr[gate-expr] of the probe is evaluated four times,
as many times as needed to obtain a stable state.
After step 3 the circuit procedure detects a stable state and terminates by returning its
@nbr[output]s (none in this example).
@defproc[#:kind "predicate" (circuit-maker? (obj any/c)) boolean?]{
Predicate for thunks made by syntax @nbr[make-circuit-maker].}
@defproc[#:kind "predicate" (circuit? (obj any/c)) boolean?]{
Predicate for circuit procedures made by a @nbrl[circuit-maker?]{circuit maker}.}
@elemtag{circuit procedure}
@section{Circuit procedures}
@defproc[(circuit (#:report report any/c #f)
                  (#:unstable-error unstable-error any/c #t)
                  (input trit?) ...) (values trit? ...)]{
@element["RktSymDef RktSym"]{circuit}
is supposed to be a @racketlink[circuit?]{circuit procedure}
as returned by a @racketlink[circuit-maker?]{circuit maker} made by syntax 
@racket[make-circuit-maker].
The @racket[input]s correspond to those given to syntax @racket[make-circuit-maker].
As many @nbr[input]s must be supplied as were given to @racket[make-circuit-maker].
The circuit procedure returns a multiple value corresponding to the @racket[output]s
given to @racket[make-circuit-maker].
The combination of all @racket[gate-output]s is preserved as the internal state of the circuit.
Initially, id est before the circuit procedure is called for the first time,
all @racket[gate-output]s are @racket[?], id est indeterminate.
The circuit procedure makes steps as follows:
all @racket[gate-expr]s are evaluated.
@nb{Each @racket[gate-expr]} must yield as many values
as its @racket[gate] has @racket[gate-output]s.
@nb{The values} must be @racketlink[trit?]{trits} of course.
After all @racket[gate-expr]s have been evaluated,
the values are transmitted to the @racket[gate-output]s.
More steps are made until all @racket[gate-output]s are stable.
@nb{A @racket[gate-output]} is stable if it no longer changes value.
After stability is obtained, the @racket[output]s are returned as a multiple value.
The internal state is preserved for the next call to the circuit procedure.

When repetition of a previous unstable internal state is detected,
the simulation is terminated, for otherwise the circuit procedure would loop forever.
Because a circuit procedure has a finite number of
feasible internal states and memorizes and inspects the history after each step,
loops always are detected.
A circuit procedure always starts with empty history and clears its history before returning.
This prevents a circuit procedure form halting prematurely when called repeatedly.

The @nbr[output]s of a circuit can depend on the internal state.
This is the case in the above @nb{@elemref["D-latch"]{D-latch}.}
For such a circuit distinct instances of the circuit procedure are required
wherever part of another circuit.
This is the reason why syntax @nbr[make-circuit-maker] returns a thunk for the
preparation of the circuit procedure proper.
Each call to the @nb{thunk returns} a distinct instance.

An elementary gate or circuit is one whose @nbr[output]s are fully determined by its
@nbr[input]s only,
id est without dependency on a preserved internal state within the gate or circuit.
The same elementary gate or circuit can be used multiple times in the same circuit or in two or more
distinct circuits as though each occurrence refers to a distinct gate or circuit.
Some caution is required, because @nbr[make-circuit-maker] cannot distinguish
elementary gates or circuits from those with internal state.
No errors or warnings are issued.

If the circuit procedure is called with a true value for optional keyword argument @nbr[report]
a report is printed on the @nbr[current-output-port],
showing mutations of the internal state after each step.
It is allowed to ask for a report of a circuit procedure called by a @nbr[gate-expr] within
a circuit procedure for which a report is asked for as well.
@nb{This is discouraged,} though, because it may result in a confusing nest of reports.

When instability is detected and @nbr[unstable-error] is not @nbr[#f] an exception is raised.
@nb{If @nbr[unstable-error]} is @nbr[#f] and instability is detected, the simulation is terminated,
@nb{the possibly} partially or fully undetermined @nbr[output]s are returned
and the possibly partially or fully undetermined internal state is preserved.
In the following example instability is detected and an exception is raised:
@Interaction*[
(define unstable-circuit
 ((make-circuit-maker unstable-circuit
   (a) (b) (b (And a (Not b))))))
(code:comment #,(tt "First initialize " @tt{b} ":"))
(unstable-circuit 0)
(code:comment #,(tt"The following report shows the loop when input "@tt{a}" is raised to "@tt{1}":"))
(unstable-circuit 1 #:report #t #:unstable-error 'yes)]}})
@(reset-Interaction*)
@(void @Interaction*[
(define make-D-latch
 (make-circuit-maker
  D-latch               (code:comment "name")
  (in clock)            (code:comment "inputs")
  (state state-inverse) (code:comment "outputs")
  (code:comment "Gates:")
  (reset         (Nand      in  clock))
  (SET           (Nand (Not in) clock))
  (state         (Nand reset state-inverse))
  (state-inverse (Nand   SET state))))])
Let's check that two distinct instances of a circuit have their own internal state.@(lb)
For this pupose we use two @nb{@elemref["D-latch"]{D-latches}}:
@Interaction*[
(define D-latch-0 (make-D-latch))
(define D-latch-1 (make-D-latch))
(define-syntax-rule (show-state D-latch)
 (call-with-values
  (λ () (D-latch ? 0))
  (λ (state state-inverse)
   (printf "(state state-inverse) of ~a is ~s.~n"
   'D-latch (list state state-inverse)))))
(begin
 (D-latch-0 0 1) (code:comment "reset D-latch-0")
 (D-latch-1 1 1) (code:comment "  set D-latch-1")
 (show-state D-latch-0)
 (show-state D-latch-1))]
@(reset-Interaction*)
@section[#:tag "Ternary logic"]{Ternary logic}
@deftogether[
(@defthing[F trit? #:value '0]
 @defthing[T trit? #:value '1]
 @defthing[? trit? #:value '?]
 @defthing[trits (list/c trit? trit? trit?) #:value '(0 1 ?)]
 @defthing[in-trits sequence? #:value (in-list trits)])]{
@inset{@Tabular[(("variable" "value"  "description"     "predicate")
                 ((nbr F)    (nbr '0) "false, off, low" @nbr[F?])
                 ((nbr T)    (nbr '1) "true, on, high"  @nbr[T?])
                 ((nbr ?)    (nbr '?) "indeterminate"   @nbr[??]))
                #:sep (hspace 2)
                #:column-properties '(center center left left)
                #:row-properties '((top-border bottom-border) () () 'bottom-border)]}}
@defproc[#:kind "predicate" (trit? (obj any/c)) boolean?]{
@nbr[#t] if @nbr[obj] is a trit, id est @nbr[0], @nbr[1] or @nbr['?]. Else @nbr[#f].}
@deftogether[
(@defproc[#:kind "predicate" (F? (obj any/c)) boolean?]
 @defproc[#:kind "predicate" (T? (obj any/c)) boolean?]
 @defproc[#:kind "predicate" (?? (obj any/c)) boolean?])]{
@Tabular[
((@nbr[(F? obj)] "is the same as" @nbr[(eq? obj '0)])
 (@nbr[(T? obj)] "is the same as" @nbr[(eq? obj '1)])
 (@nbr[(?? obj)] "is the same as" @nbr[(eq? obj '?)]))
 #:sep (hspace 1)]}
@section[#:tag "binary"]{Binary logic}
The binary digits are @nbr[F]=@nbr[0] and @nbr[T]=@nbr[1].@(lb)
@nbr[?]=@nbr['?] is not a binary digit.
@deftogether[
 (@defthing[bits (list/c bit? bit?) #:value '(0 1)]
  @defthing[in-bits sequence? #:value (in-list bits)])]
@defproc[#:kind "predicate" (bit? (obj any/c)) boolean?]{
@nbr[#t] if the @nbr[obj] is a bit, id est @nbr[0] or @nbr[1]. Else @nbr[#f].@(lb)
Always: @nbr[(implies (bit? obj) (trit? obj))] → @nbr[#t]:
@Interaction[
(for/and ((t (in-list (list F T ? "not a trit nor a bit"))))
 (implies (bit? t) (trit? t)))]}
@section[#:tag "Elementary gates"]{Elementary gates}
All gates described in this section are elementary, id est they have no preserved internal state and
their outputs are fully determined by their inputs.
The same instance of an elementary gate-procedure can be used everywhere in all circuit procedures
as though a distinct instance everywhere where it appears.
This simplifies the code of a circuit and saves memory,
but has the disadvantage that we always must be aware where the distinction matters.
@defproc[(Not (input trit?)) trit?]{
@ignore{
@nbr[(Not 0)] yields @nbr[1].@(lb)
@nbr[(Not 1)] yields @nbr[0].@(lb)
@nbr[(Not ?)] yields @nbr[?].}
@(inset (make-truth-table (input) (Not input) #t))}
@defproc[(And (input trit?) ...) trit?]{
Yields @nbr[1] when called without @nbr[input]s.@(lb)
Yields @nbr[0] when at least one @nbr[input] is @nbr[0].@(lb)
Yields @nbr[1] when at all @nbr[input]s are @nbr[1].@(lb)
Else yields @nbr[?].
@(inset (make-truth-table (a b) (And a b) #t))
@nbr[And] is commutative: it is invariant under permutation of its arguments.@(lb)
@nbr[And] is associative as well: a nest of @nbr[And]-forms can be replaced by one single
@nbr[And]-form.
@Interaction[
(for*/and ((a in-trits) (b in-trits))
 (eq? (And a b) (And b a)))
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define And-a-b-c (And a b c))
 (and (eq? (And (And a b) c) And-a-b-c)
      (eq? (And a (And b c)) And-a-b-c)))]}
@defproc[(Nand (input trit?) ...) trit?]{
Yields @nbr[0] when called without @nbr[input]s.@(lb)
Yields @nbr[1] when at least one @nbr[input] is @nbr[0].@(lb)
Yields @nbr[0] when at all @nbr[input]s are @nbr[1].@(lb)
Else yields @nbr[?].@(lb)
In other words: same as @nbr[(Not (And input ...))]
@(inset (make-truth-table (a b) (Nand a b) #t))
Given one argument, @nbr[Nand] does the same as @nbr[Not]:
@Interaction[
(for/and ((input in-trits)) (eq? (Nand input) (Not input)))]
@nbr[Nand] is commutative: it is invariant under permutation of its arguments.@(lb)
@Interaction[
(for*/and ((a in-trits) (b in-trits))
 (eq? (Nand a b) (Nand b a)))
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (for/and ((abc (in-permutations (list a b c))))
  (eq? (Nand a b c) (apply Nand abc))))]
@nbr[Nand] is not associative, for example:
@Interaction[
(values (Nand (Nand 0 0) 1) (Nand 0 (Nand 0 1)))]}
@defproc[(Or (input trit?) ...) trit?]{
Yields @nbr[0] when called without @nbr[input]s.@(lb)
Yields @nbr[1] when at least one @nbr[input] is @nbr[1].@(lb)
Yields @nbr[0] when all @nbr[input]s are @nbr[0].@(lb)
Else yields @nbr[?].
@(inset (make-truth-table (a b) (Or a b) #t))
@nbr[Or] is commutative: it is invariant under permutation of its arguments.@(lb)
@nbr[Or] is associative as well: a nest of @nbr[Or]-forms can be replaced by one single
@nbr[Or]-form.
@Interaction[
(for*/and ((a in-trits) (b in-trits))
 (eq? (Or a b) (Or b a)))
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define Or-a-b-c (Or a b c))
 (and (eq? (Or (Or a b) c) Or-a-b-c)
      (eq? (Or a (Or b c)) Or-a-b-c)))]
@nbr[And] and @nbr[Or] are distributative for each other.@(lb)
Because both @nbr[And] and @nbr[Or] are commutative,@(lb)
the distribution holds both at the right and at the left:
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (and (eq? (And a (Or b c)) (Or (And a b) (And a c)))
      (eq? (And (Or b c) a) (Or (And b a) (And c a)))
      (eq? (Or a (And b c)) (And (Or a b) (Or a c)))
      (eq? (Or (And b c) a) (And (Or b a) (Or c a)))))]}
@defproc[(Nor (input trit?) ...) trit?]{
Yields @nbr[1] when called without @nbr[input]s.@(lb)
Yields @nbr[0] when at least one @nbr[input] is @nbr[1].@(lb)
Yields @nbr[1] when all @nbr[input]s are @nbr[0].@(lb)
Else yields @nbr[?].@(lb)
In other words: same as @nbr[(Not (Or input ...))]
@(inset (make-truth-table (a b) (Nor a b) #t))
@nbr[Nor] is commutative: it is invariant under permutation of its arguments.@(lb)
@Interaction[
(for*/and ((a in-trits) (b in-trits))
 (eq? (Nor a b) (Nor b a)))]
@nbr[Nor] is not associative, for example:
@Interaction[
(values (Nor (Nor 0 0) 1) (Nor 0 (Nor 0 1)))]}
@defproc[(Xor (input trit?) ...) trit?]{
Yields @nbr[0] when called without @nbr[input]s.@(lb)
Yields @nbr[?] when at least one @nbr[input] is @nbr[?].@(lb)
Yields @nbr[1] when an odd number of @nbr[input]s is @nbr[1]
and all other @nbr[input]s, if any, are @nbr[0].@(lb)
Yields @nbr[0] when an even number of @nbr[input]s is @nbr[1]
and all other @nbr[input]s, if any, are @nbr[0].
@(inset (make-truth-table (a b) (Xor a b) #t))
@nbr[Xor] is commutative: it is invariant under permutation of its arguments.@(lb)
@nbr[Xor] is associative as well: a nest of @nbr[Xor]-forms can be replaced by one single
@nbr[Xor]-form.
@Interaction[
(for*/and ((a in-trits) (b in-trits))
 (eq? (Xor a b) (Xor b a)))
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define Xor-a-b-c (Xor a b c))
 (and (eq? (Xor (Xor a b) c) Xor-a-b-c)
      (eq? (Xor a (Xor b c)) Xor-a-b-c)))]}
@defproc[(Eq (p trit?) ...) trit?]{
Yields @nbr[1] when called without arguments.@(lb)
Yields @nbr[1] if all arguments are @nbr[0] or all are @nbr[1].@(lb)
Yields @nbr[0] if at least one argument is @nbr[0] and at least one is @nbr[1].@(lb)
Else yields @nbr[?]. Same as:
@inset{@nbr[(Or (And p ...) (Nor p ...))]}
@(inset (make-truth-table (x y) (Eq x y) #t))
@(inset (make-truth-table (x y z) (Eq x y z) #f))
@nbr[Eq] is commutative: it is invariant under permutation of its arguments.
@Interaction[
(for*/and ((a in-trits) (b in-trits))
 (eq? (Eq a b) (Eq b a)))
(for*/and ((a in-trits) (b in-trits) (c in-trits) (d in-trits))
 (define Eq-abcd (Eq a b c d))
 (for/and ((abcd (in-permutations (list a b c d))))
  (eq? (apply Eq abcd) Eq-abcd)))]
@nbr[Eq] is not associative, for example:
@Interaction[(eq? (Eq 0 0 0) (Eq (Eq 0 0) 0))]
When restricted to two arguments, @nbr[Eq] is associative, though:
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (eq? (Eq a (Eq b c)) (Eq (Eq a b) c)))]
However,when applied to more than two arguments @nbr[Eq] looses its associativity.}
@defproc[(Implies (premise trit?)(implication trit?)) trit?]{
Same as: @nbr[(Or (Not premise) implication)].
@(inset (make-truth-table (premise implication) (Implies premise implication) #t))}
@defproc[(If (test trit?) (then trit?) (else trit?)) trit?]{
If @nbr[then] and @nbr[else] are the same, their value is returned.@(lb)
Else if @nbr[test] is @nbr[T], @nbr[then] is returned.@(lb)
Else if @nbr[test] is @nbr[F], @nbr[else] is returned.@(lb)
Else if @nbr[test] is @nbr[?] and @nbr[test] and @nbr[else] are not the same, @nbr[?] is returned. 

Same as:
@inset{@nbr[(Or (And then else) (And test then) (And (Not test) else))]}
Also the same as:
@inset{@nbr[(Nand (Nand then else) (Nand test then) (Nand (Not test) else))]}
Let's check this:
@Interaction[
(for*/and ((test in-trits) (then in-trits) (else in-trits))
 (define result (If test then else))
 (and
  (eq? result
   (Or (And then else) (And test then) (And (Not test) else)))
  (eq? result
   (Nand (Nand then else) (Nand test then) (Nand (Not test) else)))))]
@(inset (make-truth-table (test then else) (If test then else) #f))}
@section{Tables}
@defform[(truth-table (id ...) expr maybe-omit-?)
         #:grammar ((maybe-omit-? (code:line) #:omit-?))]{
The @nbr[id]s are bound within the @nbr[expr].
The list of @nbr[id]s must not contain duplicates.
Keyword @nbr[#:omit-?] may appear before, among or after the other fields of the form,
but must not appear more than once.
Let n be the number @nb{of @nbr[id]s.}
If keyword @nbr[#:omit-?] is absent the @nbr[expr] is evaluated 3@↑{n} times,
@nb{one time} for each combination of @nb{n @nbrl[trit?]{trits}}.
@nb{If keyword @nbr[#:omit-?]} is present the @nbr[expr] is evaluated 2@↑{n} times,
@nb{one time} for each combination of @nb{n @nbrl[bit?]{bits}}.
The result is a list of 3@↑{n} cq 2@↑{n} elements.
@nb{Each element} of this list reads:
@inset{@tt{(@nbr[id] ... (@italic{value} ...))}}
where @tt{(@italic{value} ...)} are the values produced by the @nbr[expr].
For example:
@Interaction[
(truth-table (a b) (values (And a b) (And (Not a) b)))]
@Interaction[
(truth-table (a b c) (If a b c) #:omit-?)]
@Interaction[
(truth-table () (values))]
Syntax @nbr[truth-table] can be used for the preparation of truth-tables, of course.
The truth-tables of the gates in section @secref{Elementary gates}
have been prepared with help of procedure @nbr[truth-table].
However, the syntax can be used for other purposes too.
The following example checks that @nbr[(Nand a b)] always equals @nbr[(Or (Not a) (Not b))]:
@Interaction[
(define (ok? x) (eq? (caaddr x) 'ok))
(andmap ok? 
 (truth-table (a b)
  (if (eq? (Nand a b) (Or (Not a) (Not b)))
   'ok
   'not-ok)))]}
@defproc[
(make-inputs (n exact-nonnegative-integer?) (include-? any/c)) (listof (listof trit?))]{
If @nbr[include-?] is @nbr[#f] a list of all possible combinations of @nbr[n] @nbrl[bit?]{bits}
is returned.@(lb)
In this case there are 2@↑{n} combinations and
each element of the list is a list of @nbr[n] @nbrl[bit?]{bits}.@(lb)
If @nbr[include-?] is not @nbr[#f] a list of all possible combinations of @nbr[n] @nbrl[bit?]{trits}
is returned.@(lb)
In this case there are 3@↑{n} combinations and
each element of the list is a list of @nbr[n] @nbrl[bit?]{trits}.@(lb)
@Interaction[(make-inputs 0 #t)
             (make-inputs 1 #t)
             (make-inputs 2 #t)
             (make-inputs 3 #f)]}
@defproc[(run-circuit (circuit procedure?) (args (listof (listof any/c))))
         (listof (listof any/c))]{
Same as:
@inset{@tt{(@nbr[for/list] ((inputs (@nbr[in-list] @nbr[args]))))@(lb)
@(hspace 1)(@nbr[call-with-values] (@nbr[λ] () (@nbr[apply] @nbr[circuit] inputs)) @nbr[list]))}}
The following example shows subsequent responses of the @nb{@elemref["D-latch"]{D-latch}}
defined in the @secref{Introduction}.
@(reset-Interaction*)
@(void @Interaction*[
(define make-D-latch
 (make-circuit-maker
  D-latch               (code:comment "name")
  (in clock)            (code:comment "inputs")
  (state state-inverse) (code:comment "outputs")
  (code:comment "Gates:")
  (reset         (Nand      in  clock))
  (SET           (Nand (Not in) clock))
  (state         (Nand reset state-inverse))
  (state-inverse (Nand   SET state))))])
@Interaction*[
(define D-latch (make-D-latch))
(run-circuit D-latch
 '((0 1) (? 0) (1 1) (1 0) (0 0) (? 1) (0 1) (? 0) (1 ?)))]
Procedure @nbr[run-circuit] is especially provided for circuits,@(lb)
but can be used for arbitrary procedures, for example:
@Interaction*[
(define D-latch (make-D-latch))
(define-values (old-state old-state-inverse) (D-latch ? 0))
(run-circuit
 (λ (in clock)
  (define-values (new-state new-state-inverse) (D-latch in clock))
  (define line
   (format "in=~s clock=~s state=~s -> state=~s"
    in clock old-state new-state))
  (set! old-state new-state)
  line)
'((0 1) (? 0) (1 1) (? 0) (? 1) (0 1) (? 0) (1 ?)))]}
@(reset-Interaction*)
@section[#:tag "Elaborated examples"]{Elaborated examples}
@subsection{Adder}
We present a two's complement 6-bit adder with overflow detection.
There are 13 inputs: one carry-in, followed by the 6 bits of the first operand
and finally the 6 bits of the second operand.
The bits of the operands must be given in order of decreasing significance.
There are 8 outputs: an overflow indicator, a carry-out bit and the 6 bits of the sum
in decreasing order of significance.
The overflow bit is @nbr[1] in case of overflow, @nb{else it is @nbr[0].}
If the carry-in is @nbr[0] the sum is calculated.
If the carry-in is @nbr[1] the sum plus @nbr[1] is calculated.

The 6-bit adder:
@inset{@Tabular[
(("inputs" "")
 (@tt{c0} "carry-in")
 ((list @tt{a5} " .. " @tt{a0}) "first operand")
 ((list @tt{b5} " .. " @tt{b0}) "second operand")
 ("outputs" "")
 (@tt{ov} "overflow indicator")
 (@tt{c6} "carry-out")
 ((list @tt{s5} " .. " @tt{s0}) "sum")) #:sep (hspace 2)
 #:row-properties
 '((top-border bottom-border) () () ()
   (top-border bottom-border) () () 'bottom-border)]}
@Interaction*[
(define 6-bit-adder
 ((make-circuit-maker 6-bit-adder
   (code:comment "Inputs:")
   (    c0 a5 a4 a3 a2 a1 a0
           b5 b4 b3 b2 b1 b0)
   (code:comment "Outputs:")
   (ov c6 s5 s4 s3 s2 s1 s0)
   (code:comment "Gates:")
   ((s0 c1) (full-adder a0 b0 c0))
   ((s1 c2) (full-adder a1 b1 c1))
   ((s2 c3) (full-adder a2 b2 c2))
   ((s3 c4) (full-adder a3 b3 c3))
   ((s4 c5) (full-adder a4 b4 c4))
   ((s5 c6) (full-adder a5 b5 c5))
   (ov (Xor c5 c6)))))
(code:comment " ")
(code:comment "The full-adder and half-adder compute")
(code:comment "the sum and carry of 1 bit numbers.")
(code:comment " ")
(define full-adder
 (code:comment "bit bit carry -> bit carry")
 ((make-circuit-maker full-adder
   (code:comment "Inputs:")
   (a b carry-in)
   (code:comment "Outputs:")
   (sum carry-out)
   (code:comment "Gates:")
   ((half-sum half-carry-1) (half-adder a b))
   ((     sum half-carry-2) (half-adder carry-in half-sum))
   ((carry-out) (Or half-carry-1 half-carry-2)))))
(code:comment " ")
(define half-adder
 (code:comment "bit bit -> bit carry")
 ((make-circuit-maker half-adder
   (a b)       (code:comment "inputs")
   (sum carry) (code:comment "outputs")
   (code:comment "gates")
   (sum   (Xor a b))
   (carry (And a b)))))]
Because the outputs of procedure @tt{full-adder} do not depend on internal state,
@nb{we can} use the same instance six times in procedure @tt{6-bit-adder}.
In a real life circuit, @nb{six distinct} instances are required, of course.
The same holds for the two uses of @nb{@tt{half-adder}} in @nb{@tt{full-adder}}.
In the following two tables the right column shows @nb{@tt{(sum carry)}} cq @nb{@tt{(sum carry-out)}}:
@(define half-adder ((make-circuit-maker half-adder
                      (a b) (sum carry)
                      (sum   (Xor a b))
                      (carry (And a b)))))
@(define full-adder
 ((make-circuit-maker full-adder
   (a b carry-in)
   (sum carry-out)
   ((half-sum half-carry-1) (half-adder a b))
   ((     sum half-carry-2) (half-adder carry-in half-sum))
   ((carry-out) (Or half-carry-1 half-carry-2)))))
@(inset{make-truth-table (a b) (half-adder a b) #f})
@(inset{make-truth-table (a b carry-in) (full-adder a b carry-in) #f})
For testing we need procedures for the conversion of
@nbrl[exact-nonnegative-integer?]{exact natural numbers} to lists of bits.
@Interaction*[
(define bitmasks (reverse '(1 2 4 8 16 32)))
(code:comment " ")
(code:comment "Number to list of bits.")
(code:comment " ")
(define (n->6b n)
 (for/list ((m (in-list bitmasks)))
  (if (zero? (bitwise-and m n)) 0 1)))
(code:comment " ")
(code:comment "List of bits to number. ")
(code:comment " ")
(define (6b->n b)
 (define n
  (for/fold ((n 0)) ((b (in-list b)) (m (in-list bitmasks)))
   (if (zero? b) n (+ n m))))
 (if (>= n 32) (- n 64) n))
(code:comment " ")
(code:comment "Test n->6b and 6b->n.")
(code:comment " ")
(for/and ((n (in-range -32 +32)))
 (let* ((b (n->6b n)) (x (6b->n b)))
  (= x n)))]
Procedure @tt{do-example} takes two exact integer numbers @tt{x} and @tt{y} in the range
@nbr[-32] included to @nbr[+32] excluded and computes the sum with the @tt{6-bit-adder}.
In case of overflow it prints a message.
It returns six values:
@inset{@Tabular[
 (("•" @tt{x} " ")
  ("•" @tt{y} " ")
  ("•" @tt{x+y} (list "as computed by the " @tt{6-bit-adder}))
  ("•" @tt{x} "as a list of bits")
  ("•" @tt{y} "as a list of bits")
  ("•" @tt{x+y} (list "as a list of bits computed by the " @tt{6-bit-adder})))
 #:sep (hspace 1)]}
@Interaction*[
(define (do-example x y)
 (let ((xb (n->6b x)) (yb (n->6b y)))
  (let
   ((ov/carry-out/sum
     (call-with-values
      (λ () (apply 6-bit-adder 0 (append xb yb)))
      list)))
   (define ov (car ov/carry-out/sum))
   (define sum (cddr ov/carry-out/sum))
   (when (T? ov) (printf "Overflow detected.~n"))
   (values x y (6b->n sum) xb yb sum))))]
Let's test the @tt{6-bit-adder}.
@Interaction*[
(for*/and
 ((a (in-range -32 32))
  (b (in-range -32 32)))
 (define port (open-output-string))
 (define-values (x y x+y xb yb x+yb)
  (parameterize ((current-output-port port)) (do-example a b)))
 (define ov (get-output-string port))
 (cond
  ((< -33 (+ a b) 32) (and (= (6b->n x+yb) (+ a b)) (equal? ov "")))
  (else (equal? ov "Overflow detected.\n"))))]
We show some examples.
Each example shows the two operands and the sum, both in decimal and in binary notation
as a list of bits.
@Interaction*[
(do-example +15 +5)
(do-example +15 -5)
(do-example -15 +5)
(do-example -15 -5)
(code:comment " ")
(code:comment "Two examples of overflow.")
(code:comment " ")
(do-example -20 -25)
(do-example +20 +25)]
6-bit-adders can be put into a chain such as to make a 12-bit-adder, an 18-bit-adder or
any 6n-bit-adder.
Because the outputs of the 6-bit-adder do not depend on internal state,
a chain can contain the same instance of procedure @tt{6-bit-adder} multiple times.
In a real life circuit, distinct instances are required, of course.
Let's try a 12 bit adder.
The carry-out bit of the lower significance 6-bit-adder is the carry-in bit for the higher
significance 6-bit-adder.
The overflow bit of the lower 6-bit-adder can be ignored.
@Interaction*[
(define 12-bit-adder
 ((make-circuit-maker 12-bit-adder
   (code:comment "Inputs.")
   (             c0  a11 a10 a9 a8 a7 a6
                     a5  a4  a3 a2 a1 a0
                     b11 b10 b9 b8 b7 b6
                     b5  b4  b3 b2 b1 b0)
   (code:comment "Outputs.")
   (overflow     c12 s11 s10 s9 s8 s7 s6
                     s5  s4  s3 s2 s1 s0)
   (code:comment "Chain of two 6-bit-adders.")
   ((ov-ignore   c6  s5  s4  s3 s2 s1 s0)
    (6-bit-adder c0  a5  a4  a3 a2 a1 a0
                     b5  b4  b3 b2 b1 b0))
   ((overflow    c12 s11 s10 s9 s8 s7 s6)
    (6-bit-adder c6  a11 a10 a9 a8 a7 a6
                     b11 b10 b9 b8 b7 b6)))))
(code:comment " ")
(define (n->12b n)
 (for/fold
  ((n (if (negative? n) (+ n 4096) n))
   (12b '())
   #:result 12b)
  ((k (in-range 12)))
  (values (quotient n 2) (cons (if (odd? n) 1 0) 12b))))
(code:comment " ")
(define (12b->n bits)
 (for/fold
  ((bits bits) (n 0)
   #:result (if (< n 2048) n (- n 4096)))
  ((k (in-range 12)))
  (values (cdr bits)
   (if (T? (car bits)) (+ (* 2 n) 1) (* 2 n)))))
(code:comment " ")
(code:comment "Test n->12b and 12b->n")
(code:comment " ")
(for/and ((n (in-range -2048 2048)))
 (= (12b->n (n->12b n)) n))
(code:comment " ")
(code:comment "Test the 12-bit-adder for some random inputs.")
(code:comment "Some of the inputs may cause overflow.")
(code:comment "This is tested as well.")
(code:comment " ")
(random-seed 1)
(define nr-of-overflows 0)
(define n 100)
(for*/and ((k (in-range n)))
 (define x (random -2048 2048))
 (define y (random -2048 2048))
 (define x+y (+ x y))
 (define ov/c/x+y
  (call-with-values
   (λ ()
    (apply 12-bit-adder 0
     (append (n->12b x) (n->12b y))))
    list))
 (define computed (12b->n (cddr ov/c/x+y)))
 (cond
  ((< -2049 x+y 2048)
   (and
    (= computed x+y)
    (F? (car ov/c/x+y))))
  (else
   (set! nr-of-overflows (add1 nr-of-overflows))
   (T? (car ov/c/x+y)))))
(printf "with overflow: ~s, without overflow: ~s~n"
 nr-of-overflows (- n nr-of-overflows))
(code:comment " ")
(code:comment "1023 + 85 = 1108")
(code:comment " ")
(let ((a 1023) (b 85))
 (define a-bits (n->12b a))
 (define b-bits (n->12b b))
 (define outputs
  (call-with-values
   (λ () (apply 12-bit-adder 0 (append a-bits b-bits)))
   list))
 (define a+b (12b->n (cddr outputs)))
 (printf "~s + ~s = ~s : this is ~a.~n" a b a+b
         (if (= a+b (+ a b)) 'correct 'INCORRECT))
 (values a-bits b-bits (cddr outputs)))]
Detection of overflow: 2000 + 100 ≥ 2@↑{11}.
An n-bit entity interpreted as a two's complement number is confined to the range from
@larger{@tt{-}}2@↑{n-1} inclusive to 2@↑{n-1} exclusive.
@Interaction*[
(define a 2000)
(define b 100)
(define a-bits (n->12b a))
(define b-bits (n->12b b))
(define ov/c/sum-bits
 (call-with-values
  (λ () (apply 12-bit-adder 0 (append a-bits b-bits)))
  list))
(define ov (car ov/c/sum-bits))
(define sum-bits (cddr ov/c/sum-bits))
(define sum (12b->n sum-bits))
(begin
 (printf "a : ~s~n" a)
 (printf "b : ~s~n" b)
 (printf "s : ~s: wrong, of course.~n" sum)
 (printf "a : ~s~n" a-bits)
 (printf "b : ~s~n" b-bits)
 (printf "s : ~s~n" sum-bits)
 (unless (T? ov) (error "Overflow not detected"))
 (printf "Overflow detected.~n"))]
@(reset-Interaction*)
@subsection{Unsigned numbers}
The @tt{6-bit-adder} and @tt{12-bit-adder} can be used for unsigned numbers too.
In that case the carry-out bit being @nbr[1] indicates overflow and the overflow bit can be ignored.
@subsection{Predecessor-successor flip-flop}
@note{Uually called a ‘master-slave flip-flop’ but this is not a happy name.@(lb)
Therefore I use another name, but when googling, use the original name.}
There are several ways to construct a predecessor-successor flip-flop.@(lb)
Below two @nb{JK-latches} are used. Hence we first define a JK-latch maker.@(lb)
Its diagram looks pretty much like that of a @elemref["D-latch"]{D-latch}.@(lb)
You may want to draw the diagram according to the following definition:@(lb)
@;@image["JK-latch.gif" #:scale 0.5]
@Interaction*[
(define make-JK-latch
 (make-circuit-maker JK-latch
  (J K clock) (code:comment "inputs")
  (P Q)       (code:comment "outputs")
  (code:comment "gates")
  (reset (Nand J clock))
  (SET   (Nand K clock))
  (P     (Nand reset Q))
  (Q     (Nand SET   P))))]
@tt{P} and @tt{Q} always are inverses of each other, provided never @tt{J=K=1}.
They are the state and inverted state of the JK-latch.
The state transition table for a JK-latch after a @nbr[1]-pulse on the @tt{clock} is as follows:
@inset{@Tabular[
(((tt "J") (tt "K") (tt "P") (tt "Q") (list "new "(tt "P")) (list "new "(tt "Q")) "Action/warning")
 ((tt "0") (tt "0") (tt "P") (tt "Q") (tt "P") (tt "Q") "State preserved")
 ((tt "0") (tt "1") (tt " ") (tt " ") (tt "0") (tt "1") "Reset")
 ((tt "1") (tt "0") (tt " ") (tt " ") (tt "1") (tt "0") "Set")
 ((tt "1") (tt "1") 'cont 'cont 'cont 'cont @red{Don't do this}))
 #:row-properties '((top-border bottom-border) () () () bottom-border)
 #:column-properties '(()()()() center center left)
 #:sep (hspace 2)]}
Because a JK-latch has preserved internal state, we need two distinct instances
in the predecessor-successor flip-flop, one for the predecessor and one for the successor:
@Interaction*[
(define make-predecessor-successor-flip-flop
 (let ((predecessor (make-JK-latch))
       (successor   (make-JK-latch)))
  (make-circuit-maker predecessor-successor-flip-flop
   (J K clock) (code:comment "inputs")
   (P Q)       (code:comment "outputs")
   (code:comment "The two JK-latchs:")
   ((SET reset) (predecessor (And J (Nand K P))
                             (And K (Nand J Q)) clock))
   ((P Q) (successor SET reset (Not clock))))))
(code:comment " ")
(define predecessor-successor-flip-flop
 (make-predecessor-successor-flip-flop))]
@tt{P} and @tt{Q} always are inverses of each other.
They are the state and inverted state of the predecessor-successor flip-flop.
The state transition table for the predecessor-successor flip-flop after a @nbr[1]-pulse on the
@tt{clock} is as follows:
@inset{@Tabular[
(((tt "J") (tt "K") (tt "P") (tt "Q") (list "new "(tt "P")) (list "new "(tt "Q")) "Action")
 ((tt "0") (tt "0") (tt "P") (tt "Q") (tt "P") (tt "Q") "No change")
 ((tt "0") (tt "1") (tt " ") (tt " ") (tt "0") (tt "1") "Reset")
 ((tt "1") (tt "0") (tt " ") (tt " ") (tt "1") (tt "0") "Set")
 ((tt "1") (tt "1") (tt "P") (tt "Q") (tt "Q") (tt "P") "Flip"))
 #:row-properties '((top-border bottom-border) () () () bottom-border)
 #:column-properties '(()()()() 'center 'center 'left)
 #:sep (hspace 2)]}
In order to clock the predecessor-successor flip-flop we need two calls,
one with @tt{clock=1} to set or reset or flip the predecessor or to leave it as it is and
one call with @tt{clock=0} in order to copy the state of the predecessor into the successor.
@tt{clock=1} may change the predecessor but leaves the successor unaffected.
@tt{clock=0} leaves the predecessor unaffected and
copies the state of the predecessor into the successor.
When @tt{clock=0}, @tt{J} and @tt{K} are irrelevant and we take @tt{J=K=?}.
@Interaction*[
(define (clock-the-predecessor-successor-flip-flop J K)
 (predecessor-successor-flip-flop J K 1)
 (predecessor-successor-flip-flop ? ? 0))]
Let's test clocking the predecessor-successor flip-flop for all combinations of
old state @nb{@tt{(P Q)}} and the inputs @tt{J} and @tt{K}:
@Interaction*[
(define table
 (for*/list ((P in-bits) (K in-bits) (J in-bits))
  (define Q (Not P))
  (code:comment "Put the flip-flop in state (P Q) and check it's done right.")
  (define-values (old-P old-Q)
   (clock-the-predecessor-successor-flip-flop P Q))
  (unless (and (= old-P P) (= old-Q Q)) (error "test fails"))
  (code:comment "Clock the flip-flop with J and K.")
  (define-values (new-P new-Q)
   (clock-the-predecessor-successor-flip-flop J K))
  (code:comment "Check:")
  (case (list J K)
   (((0 0)) (equal? (list new-P new-Q) (list old-P old-Q)))
   (((0 1)) (equal? (list new-P new-Q) (list 0 1)))
   (((1 0)) (equal? (list new-P new-Q) (list 1 0)))
   (((1 1)) (equal? (list new-P new-Q) (list old-Q old-P)))
   (else (error "test fails")))
  (code:comment "Gather results.")
  (list J K (list old-P old-Q) (list new-P new-Q)
   (case (list J K old-P)
    (((0 0 0)) "no action")
    (((0 1 0)) "reset (was already reset)")
    (((1 0 0)) "set")
    (((1 1 0)) "flip")
    (((0 0 1)) "no action")
    (((0 1 1)) "reset")
    (((1 0 1)) "set (was already set)")
    (((1 1 1)) "flip")))))
(code:comment " ")
(code:comment "Print results:")
(code:comment " ")
(begin
 (define line (make-string 52 #\─))
 (printf "~a~n" line)
 (printf "     old state  new state~n")
 (printf "J K    (P Q)      (P Q)    action~n")
 (printf "~a~n" line)
 (for ((line (in-list table)))
  (apply printf "~s ~s    ~s      ~s    ~a~n" line))
 (printf "~a~n" line))]

@(bold (larger (larger "The end")))
