#lang scribble/manual

@;====================================================================================================
@(require
  scribble/core
  "digital-circuits.rkt"
  "scribble-utensils.rkt"
  (for-label "digital-circuits.rkt" (except-in racket set) racket/block)
  (for-template "digital-circuits.rkt" (except-in racket set))
  (for-syntax (except-in racket set)))
@title[#:version ""]{Digital circuits}
@author{Jacob J. A. Koot}
@(defmodule "digital-circuits.rkt" #:packages ())
@section{Introduction}
Module @hyperlink["digital-circuits.rkt"]{digital-circuits.rkt}
provides a simple tool for the preparation of procedures
for the digital simulation of digital electronic circuits.
Given the digital inputs such a procedure calculates the digital outputs.
It can have an internal state that is preserved between successive calls.
These calls can be regarded as successive points of
time at which the signals on the inputs can be changed.
The outputs and new internal state can depend on both the inputs and the former internal state.
@seclink["Ternary logic"]{Ternary logic} is used in order to include indeterminate signals.
@(define ternary-table
@inset{@Tabular[
(("constant" "value" "predicate" "description" (list "is a " @nbr[trit?]) (list "also a " @nbr[bit?]))
 (@nbr[F] @nbr['0] @nbr[F?] "false, off, low" "yes" "yes")
 (@nbr[T] @nbr['1] @nbr[T?] "true, on, high"  "yes" "yes")
 (@nbr[?] @nbr['?] @nbr[??] "indeterminate"   "yes" "no"))
 #:sep (hspace 2)
 #:row-properties '((top-border bottom-border) () () bottom-border)
 #:column-properties '(center center center center center center)]})
@ternary-table
@elemtag{D-latch}
As introductory example a D-latch.@(lb)
It has two inputs, say @tt{in} and @tt{clock}.@(lb)
It has two outputs, say @tt{state} and @nb{@tt{state-inverse}}.@(lb)
After the @nb{D-latch} has been initialized properly,@(lb)
the outputs always remain inverses of each other.@(lb)
The outputs are preserved as internal state.@(lb)
The new @tt{state} and @nb{@tt{state-inverse}} can depend on the previous @tt{state}.@(lb)
The following transition table applies:
@inset{@Tabular[
(((tt "clock")
  (tt "in")
  (list "old" (hspace 1) (tt "state"))
  (list "new" (hspace 1) (tt "state"))
  "action")
 ((tt "1") (tt "0" ) "any"        (tt "0")     "reset")
 ((tt "1") (tt "1" ) "any"        (tt "1")     "set")
 ((tt "0") "any"     (tt "state") (tt "state") "state preserved"))
 #:row-properties '((top-border bottom-border) () () bottom-border)
 #:column-properties '(center center center center left)
 #:sep (hspace 2)]}
Hence, in order to set or reset the @nb{D-latch},
set @tt{in} to @nbr[1] cq @nbr[0] and apply a @nbr[1]-pulse to the @tt{clock}.
Leave the @tt{clock} low at @nbr[0] in order to preserve the state.
There are several ways to construct a D-latch.
The following diagram shows a D-latch consisting of four @nbr[Nand]-gates.
@elemtag["D-latch-diagram"]@inset{@image["D-latch.gif" #:scale 1]}
With syntax @nbr[make-circuit-maker] a procedure for simulation of the circuit
can be made by straightforwardly listing the elements of the @elemref["D-latch-diagram"]{diagram}:
@elemtag["make-D-latch"]@(define-make-D-latch #t)
The order in which the gates are listed is irrelevant.
Syntax @nbr[make-circuit-maker] yields a procedure, called a ‘circuit maker’.
The latter returns a procedure for the simulation, called a ‘circuit procedure’.
We have to call the @nb{circuit maker} in order to make an instance of the circuit procedure proper.
In section @secref["mcm"] we shall see why the circuit procedure is not made immediately.
@Interaction*[(define D-latch (make-D-latch))]
Procedure @tt{D-latch} accepts the two signals @tt{in} and @tt{clock}
and returns the two signals @tt{state} and @tt{state-inverse}.
The @tt{state} and @tt{state-inverse} are fed back to each other
via the two @nbr[Nand]-gates at the right in the @elemref["D-latch-diagram"]{diagram},
cq the last two lines in the above definition of @elemref["make-D-latch"]{@tt{make-D-latch}}.
When @tt{clock}=@nbr[0], @tt{set} and @tt{reset} raise to @nbr[1]
(as far as not already @nbr[1])
and the two @nbr[Nand]-gates act as a loop of two inverters for
the signals @tt{state} and @tt{state-inverse}.
If they are inverses of each other, they remain stable as they are.

The first call to a circuit procedure corresponds to switching power on.
During power on, the @nb{@tt{D-latch}} must be reset or set with a @nbr[1]-pulse on the
@tt{clock} and @tt{in} hold at @nbr[0] or @nbr[1].
This is necessary in order to stabilize the @tt{state} and @tt{state-inverse}.
Otherwise they may vibrate for a while, possibly forever,
both simultaneously receiving the same signal and simultaneously sending the same
inverted signal, which means that they remain switching.
Once stable, the @tt{state} and @tt{state-inverse} are inverses of each other
and remain as they are after the @tt{clock} falls down from @nb{@nbr[1] to @nbr[0]}.
A circuit procedure is protected such as never to vibrate more than one cycle;
outputs may be indeterminate or a warning may be issued or an exception may be raised
depending on the @elemref["circuit procedure"]{circuit procedure} itself and how it is called.
Let's see what happens when we start up with @tt{clock}=@nbr[0].
In this example a D-latch is used whose internal signals are initialized with @nbr[power-up]=@nbr[0],
for this provides a better demonstration of what goes wrong.
(The default @nbr[power-up] is determined by parameter @nbr[power-up-signal]
whose initial value is @nbrl[?]{indeterminate}.)
@elemtag{unstable}
@Interaction*[
(define wrongly-powered-up-D-latch
 (make-D-latch
  #:name 'D-latch-with-wrong-power-up
  #:power-up 0))
(wrongly-powered-up-D-latch 0 0 #:report #t)]
In step 2 @tt{state} and @tt{state-inverse} simultaneously switch from @nbr[1] to @nbr[0],
but in step 3 they simultaneously switch back to @nbr[1], resulting in exactly the same
unstable internal state as at the start of step 2, thus causing a vibration.
This vibration would go on forever if not detected and halted by the circuit procedure.
We'd better stabilize the D-latch by resetting or setting it
with @tt{clock}=@nbr[1] and @tt{in}=@nbr[0] or @tt{in}=@nbr[1].
The initial internal signals are @nbr[?], id est @nbrl[?]{indeterminate}.
Initial internal signals @nbr[0] and @nbr[1] would work as well.
@Interaction*[
(D-latch 0 1 #:report #t)]
The returned values are @tt{state} and @tt{state-inverse}.
Now we can safely drop the @tt{clock}.
When the @tt{clock} is @nbr[0], input @tt{in} is irrelevant and we can leave it indeterminate.
@Interaction*[(D-latch ? 0 #:report #t)]
After the clock is put down to @nbr[0],
internal signal @tt{set} raises to @nbr[1] as shown in step 1 of the report,
@nb{but none} of the other signals change.
Let's test the @nb{D-latch} for all combinations of @seclink["binary"]{binary} values for
@tt{in}, @tt{clock} and @nb{old @tt{state}:}
@(define D-latch-comment
  (list "Send signals " @black{@tt{in}} " and " @black{@tt{clock}} " to the D-latch."))
@Interaction*[
(define (test/make-table latch) (code:comment "Does tests and gathers info in a table.")
 (for*/list ((clock in-bits) (in in-bits) (old-state in-bits))
  (code:comment #,(list "First put the D-latch in state " @black{@tt{old-state}} " and check"))
  (code:comment "that the D-latch indeed assumes this state.")
  (define-values (state state-inverse) (latch old-state 1))
  (unless
   (and
    (eq? state old-state)
    (eq? state-inverse (Not state)))
   (error "test fails"))
  (code:comment #,D-latch-comment)
  (define-values (new-state new-state-inverse) (latch in clock))
  (code:comment "Check the results.")
  (unless 
   (and
    (eq? new-state (If clock in state))
    (eq? new-state-inverse (Not new-state)))
   (error "test fails"))
  (code:comment "Add a row with all details to the table.")
  (list in clock old-state new-state (action in clock old-state))))]
@Interaction*[
(define (action in clock state)
 (cond (code:comment "Description of the action.")
  ((= clock 0) "preserve state")
  ((= in 0) "reset")
  ((= in 1) "set")
  (else (error 'action "unexpected arguments"))))]
@Interaction*[
(define (do-test-and-print-table latch)
 (code:comment "The test proper.")
 (define table (test/make-table latch))
 (code:comment "We print the details in a table.")
 (code:comment "First the header of the table.")
 (printf " ~n")
 (define border (string-append (make-string 47 #\─) "~n"))
 (printf border)
 (printf "in  clock  old-state  new-state  action~n")
 (printf border)
 (code:comment "Print the table proper.")
 (for ((row (in-list table)))
  (apply printf " ~s    ~s        ~s          ~s      ~a~n" row))
 (code:comment "Close the table.")
 (printf border)
 (code:comment "Arriving here means that all went well.")
 (printf "Hurray, test passed.~n")
 (printf border))]
@Interaction*[
(do-test-and-print-table D-latch)]
The above table shows that:
@inset{@nbr[new-state = (Or (And in clock) (And (Not clock) old-state))]}
which is the same as:
@inset{@nbr[new-state = (Nand (Nand in clock) (Nand (Not clock) old-state))]}
Let's try a diagram according to this formula:
@inset{@image["another-D-latch.gif" #:scale 1]}
Let's call it @tt{another-D-latch}.
For the moment ignore the bold bar in wire @tt{a}.
@Interaction*[
(define another-D-latch
 ((make-circuit-maker another-D-latch
   (in clock) (state state-inverse)
   (state (Nand (Nand in clock) (Nand (Not clock) state)))
   (state-inverse (Not state)))))]
@Interaction*[
(define (test-latch latch) (and (test/make-table latch)) #t)
(test-latch another-D-latch)]
Well, this seems to work,
but when listing all gates separately, things go wrong:
@Interaction*[
(define wrong-D-latch
 ((make-circuit-maker wrong-D-latch
   (in clock) (state state-inverse)
   (not-clock (Not clock))
   (a (Nand in clock))
   (b (Nand not-clock state))
   (state (Nand a b))
   (state-inverse (Not state)))))]
In some situations the @tt{wrong-D-latch} is unstable, even after correct power-up and the @tt{clock}
dropped to @nbr[0].
The problem is located in signal @tt{b}.
There is a circular dependency between signals @tt{b} and @tt{state}.
However, signal @tt{b} has an inappropiate delay.
Let's see what happens after stabilizing the latch with @tt{state}=@nbr[1]
and subsequently dropping the @tt{clock}:
@Interaction*[
(wrong-D-latch 1 1)]
The @tt{wrong-D-latch} has been stabilized properly,
but dropping the clock fails:
@Interaction*[
(wrong-D-latch 1 0 #:report #t #:unstable-error #f)]
The report shows that signal @tt{a} switches in step 1,
but @tt{b} switches in step 2,
in the same step as signal @tt{state} switches too but based on the old signal of @tt{b}.
It is important that signal @tt{a} does not switch earlier than signal @tt{b}.
We can hack this problem by delaying signal @tt{a} by one step,
in the diagram shown as a bold bar:
@Interaction*[
(test-latch
 ((make-circuit-maker hacked-D-latch
   (in clock) (state state-inverse)
   (not-clock (Not clock))
   (a1 (Nand in clock))
   (a a1) (code:comment "One step delay (The bold bar in signal a)")
   (b (Nand not-clock state))
   (state (Nand a b))
   (state-inverse (Not state)))))] @(reset-Interaction*)
Section @secref{Circuit procedures} describes the timing of changes of signals.@(lb)
Timing is not important in circuits without circular dependencies.

More examples in section @seclink{Elaborated examples}.
@(reset-Interaction*)
@section[#:tag "mcm"]{Make-circuit-maker}
@defform-remove-empty-lines[@defform[(make-circuit-maker name (input ...) (output ...) gate ...)
#:grammar ((name id)
           (input id)
           (output id)
           (gate (gate-output gate-expr) ((gate-output ...) gate-expr))
           (gate-output id))
#:contracts ((gate-expr (values trit? ...)))]{
Yields a circuit maker:
@elemtag{circuit-maker}
@inset[@defproc[#:link-target? #t
(circuit-maker (#:name name symbol?
                #,(tt @italic{name} @roman{ as given to } (nbr make-circuit-maker)))
               (#:power-up power-up trit? (power-up-signal))) circuit?]{
Each time the circuit maker is called it returns a distinct instance of a
@elemref["circuit procedure"]{circuit procedure},
@nb{id est}, an instance with its own internal state.
This is important when the @nbr[output]s of the circuit may depend on a preserved internal state and
several instances are needed in one or more circuits.
Each such instance must have its own internal state
such as to prevent that they disturb each other's internal states.
Argument @nbr[power-up] is for the initial value of all internal signals of the circuit made by the
@elemref["circuit-maker"]{circuit-maker}.
The initial value of parameter @nbr[(power-up-signal)] is @nbr[?],
id est @nbrl[?]{indeterminate}.}]

The following restrictions apply to @nbr[make-circuit-maker]:
@inset{
• The @nbr[input]s must be distinct identifiers without duplicates.@(lb)
• The @nbr[output]s must be distinct identifiers without duplicates.@(lb)
• All @nbr[gate-output]s must be distinct identifiers without duplicates.@(lb)
• The set of the @nbr[input]s and that of the @nbr[gate-output]s must be disjunct.@(lb)
• The @nbr[output]s must be a subset of the conjunction of @nbr[input]s and @nbr[gate-output]s.@(lb)
• Assignments to @nbr[input]s and @nbr[gate-output]s are inhibited.@(lb)
• This implies that assignments to @nbr[output]s are inhibited as well.@(lb)
• Each @nbr[gate-expr] must return as many values as its @nbr[gate] has @nbr[gate-output]s.@(lb)
• These values must be @nbrl[trit?]{trits}
  (they are transmitted to the @nbr[gate-output]s).@(lb)
• A @nbr[gate-expr] must not involve direct nor indirect calls to the circuit it is part of.}
The last three restrictions are checked while a
@elemref["circuit procedure"]{circuit procecure} is running.
The other restrictions are checked immediately during expansion
of the @nbr[make-circuit-maker]-form.
Within each @nbr[gate-expr] all identifiers of the @nbr[input]s
and @nbr[gate-output]s are bound, those of other @nbr[gate]s included.
They can be used as inputs of the @nbr[gate].
The @nbr[gate-expr]s are not yet evaluated.
They will be incorporated in the circuit procedures to be made by the circuit maker
and will be evaluated one or more times each time such circuit procedure is called.

The @nbr[name] is used for the @nbr[object-name] and the
@seclink["print-unreadable"
#:doc '(lib "scribblings/reference/reference.scrbl")]{printed form}
of the circuit maker and the circuit procedures it makes.
The following example shows how the @nbr[object-name]s and
@seclink["print-unreadable"
#:doc '(lib "scribblings/reference/reference.scrbl")]{printed forms}
look like:
@Interaction[
(define make-empty-circuit (make-circuit-maker nothing () ()))
(define empty-circuit (make-empty-circuit))
(values
 (object-name make-empty-circuit)
 (object-name empty-circuit)
 make-empty-circuit
 empty-circuit)]

A circuit procedure can be renamed with procedure @nbr[circuit-rename!] without loosing its identity
in the sense of @nbr[eq?].

A @nbr[gate-expr] can represent a subcircuit with more complexity than an
@seclink["Elementary gates"]{elementary gate}.
@nb{It can} include calls to gates and other circuits,
but it must not directly nor indirectly call the circuit procedure it belongs to,
for this would represent an infinitely deep nesting of the same circuit,
which in real life is impossible, of course.
@nb{A circuit} can have circular dependencies between its internal signals, though.
For example, the signals @tt{state} and @nb{@tt{state-inverse}}
in the above @nb{@elemref["D-latch"]{D-latch}} have such dependency.
When a @nbr[gate-expr] directly or indirectly calls the circuit procedure it is part of,
an exception is raised:
@Interaction[
(define make-nested-circuit
 (make-circuit-maker nested-circuit
  () () (() (nested-circuit))))
(define nested-circuit (make-nested-circuit))
(nested-circuit)]
A @nbr[gate-expr] cannot make assignments to @nbr[input]s, @nbr[output]s, or @nbr[gate-output]s.@(lb)
Offences are detected immediately during expansion.
@Interaction[
(make-circuit-maker wrong-circuit (var) () (() (set! var ?)))]
@Interaction[
(make-circuit-maker wrong-circuit
 () () (var (set!-values (var) "will not be accepted")))]
A @nbr[gate] is not required to have outputs.
Such a @nbr[gate] can be used for inclusion of checks and for printed output
as a probe on some or all wires:
@inset{@image["probed-circuit.gif" #:scale 0.75]}
@Interaction[
(define make-probed-circuit
 (make-circuit-maker probed-circuit (a) (c)
  (b (Not a))
  (c (Not b))
  (() (code:comment "probe:")
   (begin
    (printf "a=~s, b=~s, c=~s.~n" a b c)
    (code:comment #,(list @nbr[printf] " returns " @(Void) ", but we must not return any value."))
    (code:comment "Therefore we finish with:")
    (values)))))
(define probed-circuit (make-probed-circuit))
(probed-circuit 0)]
Every @nbr[gate-expr] of this circuit, the probe included, is evaluated three times,@(lb)
as many times as needed to obtain and confirm a stable state.
@defproc[#:kind "predicate" (circuit-maker? (obj any/c)) boolean?]{
Predicate for circuit makers made by syntax @nbr[make-circuit-maker].}
@defproc[#:kind "predicate" (circuit? (obj any/c)) boolean?]{
Predicate for circuit procedures made by a @elemref["circuit-maker"]{circuit maker}.}
@defproc[(circuit-rename! (circuit circuit?) (name symbol?)) circuit?]{
Changes the name of a circuit and returns the circuit.@(lb)
The returned one is @nbr[eq?] to the original.
@note{A circuit is represented by a struct with @nbrl[prop:procedure]{procedure-property}.
Such a struct has two fields, its name and the circuit procedure proper.
Procedure @nbr[circuit-rename!] simply returns this struct
after adjusting the mutable @nbr[name] field.
No new circuit is made.}}
@defparam[power-up-signal signal trit? #:value ?]{
Parameter containing the default value for optional keyword argument @tt{@italic{power-up}}
for the initial signals in the internal state
when a circuit procedure is made by a @elemref["circuit-maker"]{circuit maker}.}
@elemtag{circuit procedure}
@section[#:tag "Circuit procedures"]{Circuit procedures}
@defproc[#:kind "circuit procedure"
(circuit (#:report report any/c #f)
         (#:unstable-error unstable-error any/c #t)
         (#:indeterminate-error indeterminate-error any/c #f)
         (input trit?) ...) (values trit? ...)]{
@element["RktSymDef RktSym"]{circuit}
is supposed to be a @racketlink[circuit?]{circuit procedure}
as returned by a @elemref["circuit-maker"]{circuit maker} made by syntax 
@racket[make-circuit-maker].
The @racket[input]s correspond to those given to syntax @racket[make-circuit-maker].
As many @nbr[input]s must be supplied as were given to @racket[make-circuit-maker].
The circuit procedure returns a multiple value corresponding to the @racket[output]s
given to @racket[make-circuit-maker].
The combination of all @racket[gate-output]s is preserved as the internal state of the circuit.
When a circuit procedure is made by a circuit maker,
all @racket[gate-output]s are initialized with the trit given for it's optional @italic{@tt{power-up}}
argument, whose default value is determined by parameter @nbr[power-up-signal].
The predefined value of this parameter @nb{is @racket[?],} id est indeterminate.
The circuit procedure makes steps as follows:
all @racket[gate-expr]s are evaluated.
@nb{Each @racket[gate-expr]} must yield as many values
as its @racket[gate] has @racket[gate-output]s.
The values must be @racketlink[trit?]{trits}, of course.
After all @racket[gate-expr]s have been evaluated,
the signals are transmitted simultaneously to the @racket[gate-output]s.
This means that every @nbr[gate] of a @nbr[make-circuit-maker]-form has the same delay.
Where needed signals are transmitted to the @nbr[gate-output]s
as though clocked simultaneously via @nb{@elemref["D-latch"]{D-latches}}.
More steps are made until all @nbr[gate-output]s are stable.
@nb{After stability} is obtained, the @racket[output]s are returned as a multiple value.
The internal state is preserved for the next call to the circuit procedure.

Notice that a @nbr[gate] of the form @nbr[(id_1 id_0)]
transmits the signal of @nbr[id_0] to @nbr[id_1] with one step of delay.
Sometimes such additional delay may be necessary.

@ignore{Evaluation of every @nbr[gate-expr] even when its inputs have not been changed,
may seem inefficient, but @seclink["Elementary gates"]{elementary gates} are fast
and memorizing their inputs and corresponding outputs could be slower.
For circuits whose outputs may depend on internal state,
the latter must be 
memorizing is not possible, for such a circuit may return different values even when
called with the same inputs as in an earlier call.
@nb{A @seclink["twin flip-flop"]{twin flip-flop}} is an example of such a circuit.
Where desired, a @nbr[gate-expr] can be made such as to memorize its inputs,
internal state and related outputs,
but module @nb{@hyperlink["digital-circuits.rkt"]{digital-circuits.rkt}}
does not provide predefined tools for this purpose.}

When repetition of a previous unstable internal state is detected,
the simulation is terminated, for otherwise the circuit procedure would loop forever.
Because a circuit procedure has a finite number of
feasible internal states and memorizes and inspects the history after each step,
loops always are detected.
A circuit procedure always starts with empty history and clears its history before returning.
This prevents a circuit procedure from halting prematurely when called repeatedly.

The @nbr[output]s of a circuit can depend on the internal state.
This is the case in the above @nb{@elemref["D-latch"]{D-latch}.}
For such a circuit distinct instances of the circuit procedure are required
wherever part of another circuit.
This is the reason why syntax @nbr[make-circuit-maker] returns a circuit maker for the
preparation of the circuit procedure proper.
Each time the circuit maker is called, @nb{it returns} a distinct instance of the circuit procedure
with its own independent internal state.

An elementary gate or circuit is one whose @nbr[output]s are fully determined by its
@nbr[input]s only,
id est without dependency on a preserved internal state within the gate or circuit.
The same elementary gate or circuit can be used multiple times in the same circuit or in two or more
distinct circuits as though each occurrence refers to a distinct gate or circuit.
Syntax @nbr[make-circuit-maker] cannot distinguish
elementary gates or circuits from those with internal state;
@red{no errors or warnings are issued}.

If @nbr[indeterminate-error] has a true value and one or more @nbr[output]s are
indeterminate,@(lb) an exception is raised:
@Interaction[
(define make-indeterminate-circuit
 (make-circuit-maker indeterminate-circuit () (a b c)
  (a 1)
  (b c)
  (c b)))
(define indeterminate-circuit
 (make-indeterminate-circuit #:power-up ?))
(indeterminate-circuit #:indeterminate-error #t)]
If the circuit procedure is called with a true value for argument @nbr[report]
a report is printed on the @nbr[current-output-port],
showing mutations of the internal state after each step.
Examples can be found in the @secref{Introduction}.
It is allowed to ask for a report of a circuit procedure called by a @nbr[gate-expr] within
a circuit procedure for which a report is asked for as well.
@nb{This is discouraged,} though, because it may result in a confusing nest of reports.

When instability is detected and @nbr[unstable-error] is not @nbr[#f] an exception is raised.
For an example see the @elemref["unstable"]{wrong starting up of a D-latch}.
@nb{If @nbr[unstable-error]} is @nbr[#f] and instability is detected,
the simulation is terminated, no exception is raised,
@nb{a warning} is written on the @nbr[current-error-port],
@nb{the possibly} partially or fully undetermined @nbr[output]s are returned
and @nb{the possibly} partially or fully undetermined internal state is preserved.}}]
@(reset-Interaction*)
@section[#:tag "Ternary logic"]{Ternary logic}
@deftogether[
(@defthing[#:kind "false/off/low constant" F trit? #:value '0]
 @defthing[#:kind "true/on/high constant" T trit? #:value '1]
 @defthing[#:kind "indeterminate constant" ? trit? #:value '?]
 @defthing[#:kind "constant" trits (list/c trit? trit? trit?) #:value (list F T ?)]
 @defthing[#:kind "constant" in-trits sequence? #:value (in-list trits)]
 @defproc[#:kind "predicate" (trit? (obj any/c)) boolean?]
 @defproc[#:kind "predicate" (F? (obj any/c)) boolean?]
 @defproc[#:kind "predicate" (T? (obj any/c)) boolean?]
 @defproc[#:kind "predicate" (?? (obj any/c)) boolean?])]{
@;@ternary-table
@nbr[F] and @nbr[T] are no
@seclink["booleans" #:doc '(lib "scribblings/reference/reference.scrbl")]{booleans}
in the sense of predicate @nbr[boolean?].@(lb)
Use predicates @nbr[bit?] and @nbr[trit?] in stead.@(lb)
@nbr[(trit? obj)] yields @nbr[#t] if @nbr[obj] is a trit, id est @nbr[0], @nbr[1] or @nbr['?].@(lb)
Else @nbr[(trit? obj)] yields @nbr[#f].@(lb)
@nbr[(F? obj)] is the same as @nbr[(eq? obj F)] id est @nbr[(eq? obj '0)].@(lb)
@nbr[(T? obj)] is the same as @nbr[(eq? obj T)] id est @nbr[(eq? obj '1)].@(lb)
@nbr[(?? obj)] is the same as @nbr[(eq? obj ?)] id est @nbr[(eq? obj '?)].}
@section[#:tag "binary"]{Binary logic}
The binary digits are @nbr[F]=@nbr[0] and @nbr[T]=@nbr[1].@(lb)
@nbr[?]=@nbr['?] is not a binary digit.
@deftogether[
 (@defthing[#:kind "constant" bits (list/c bit? bit?) #:value (list F T)]
  @defthing[#:kind "constant" in-bits sequence? #:value (in-list bits)]
@defproc[#:kind "predicate" (bit? (obj any/c)) boolean?])]{
@nbr[(bit? obj)] yields @nbr[#t] if the @nbr[obj] is a bit, id est @nbr[0] or @nbr[1].
Else @nbr[(bit? obj)] yields @nbr[#f].@(lb)
Always: @nbr[(implies (bit? obj) (trit? obj))] → @nbr[#t].}
@section[#:tag "Elementary gates"]{Elementary gates}
All gates described in this section are elementary, id est
their outputs are fully determined by their inputs without dependency on internal state.
The same instance of an elementary gate-procedure can be used
multiple times in the same and in distinct circuit procedures
as though a distinct instance everywhere.

@elemtag{generalized-associativity}
Where applicable a note is added about commutativity and associativity.
In this document these two concepts are generalized to functions that can accept more than two
arguments.
Such a function will be said to be commutative if it is invariant
under permutation of its arguments.
It will be said to be associative if a nested application
can be replaced by one single application.
For example, @nbr[And] is associative in generalized sense. For example:
@inset{@nbr[(And (And a b) (And c d))] can be written as: @nbr[(And a b c d)]}
This excludes the distinction between left and right associativity,
but in the present document this distinction is not needed.
A function that is associative when called with two arguments only,
not necessarily is associative in generalized sense too.
For an example see procedure @nbr[Eq].
@defproc[#:kind "predicate" (gate? (obj any/c)) boolean?]{
This predicate holds for all elementary gates described in this section.
It returns @nbr[#t] if the @nbr[obj] is
@nbr[Not],
@nbr[And],
@nbr[Nand],
@nbr[Or],
@nbr[Nor],
@nbr[Xor],
@nbr[Eq],
@nbr[Implies] or
@nbr[If].
For every other @nbr[obj] the predicate returns @nbr[#f].}
@defproc[#:kind "elementary gate" (Not (input trit?)) trit?]{
@(inset (make-truth-table (input) (Not input) #t))}
@defproc[#:kind "elementary gate" (And (input trit?) ...) trit?]{
Yields @nbr[1] when called without @nbr[input]s.@(lb)
Yields @nbr[0] when at least one @nbr[input] is @nbr[0].@(lb)
Yields @nbr[1] when all @nbr[input]s are @nbr[1].@(lb)
Else yields @nbr[?].
@(inset (make-truth-table (a b) (And a b) #t))
@nbr[And] is commutative: it is invariant under permutation of its arguments.
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define And-abc (And a b c))
 (for/and ((abc (in-permutations (list a b c))))
  (eq? And-abc (apply And abc))))]
@nbr[And] is associative as well: a nest of @nbr[And]-forms can be replaced by one single
@nbr[And]-form.
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define And-abc (And a b c))
 (and (eq? (And (And a b) c) And-abc)
      (eq? (And a (And b c)) And-abc)))]}
@defproc[#:kind "elementary gate" (Nand (input trit?) ...) trit?]{
Yields @nbr[0] when called without @nbr[input]s.@(lb)
Yields @nbr[1] when at least one @nbr[input] is @nbr[0].@(lb)
Yields @nbr[0] when all @nbr[input]s are @nbr[1].@(lb)
Else yields @nbr[?].@(lb)
In other words: same as @nbr[(Not (And input ...))]
@(inset (make-truth-table (a b) (Nand a b) #t))
@nbr[Nand] is commutative: it is invariant under permutation of its arguments.
@Interaction[
(for*/and ((a in-trits) (b in-trits))
 (eq? (Nand a b) (Nand b a)))
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define Nand-abc (Nand a b c))
 (for/and ((abc (in-permutations (list a b c))))
  (eq? Nand-abc (apply Nand abc))))]
@nbr[Nand] is not associative, for example:
@Interaction[
(values (Nand (Nand 0 0) 1) (Nand 0 (Nand 0 1)))]}
@defproc[#:kind "elementary gate" (Or (input trit?) ...) trit?]{
Yields @nbr[0] when called without @nbr[input]s.@(lb)
Yields @nbr[1] when at least one @nbr[input] is @nbr[1].@(lb)
Yields @nbr[0] when all @nbr[input]s are @nbr[0].@(lb)
Else yields @nbr[?].
@(inset (make-truth-table (a b) (Or a b) #t))
@nbr[Or] is commutative: it is invariant under permutation of its arguments.
@Interaction[
(for*/and ((a in-trits) (b in-trits))
 (eq? (Or a b) (Or b a)))]
@nbr[Or] is associative as well: a nest of @nbr[Or]-forms can be replaced by one single
@nbr[Or]-form.
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define Or-abc (Or a b c))
 (and (eq? (Or (Or a b) c) Or-abc)
      (eq? (Or a (Or b c)) Or-abc)))]
@nbr[And] and @nbr[Or] are distributative for each other.@(lb)
Because both @nbr[And] and @nbr[Or] are commutative,@(lb)
the distributivity holds both at the right and at the left:
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (and
  (eq? (And a (Or b c)) (Or (And a b) (And a c)))
  (eq? (And (Or b c) a) (Or (And b a) (And c a)))
  (eq? (Or a (And b c)) (And (Or a b) (Or a c)))
  (eq? (Or (And b c) a) (And (Or b a) (Or c a)))))]}
@defproc[#:kind "elementary gate" (Nor (input trit?) ...) trit?]{
Yields @nbr[1] when called without @nbr[input]s.@(lb)
Yields @nbr[0] when at least one @nbr[input] is @nbr[1].@(lb)
Yields @nbr[1] when all @nbr[input]s are @nbr[0].@(lb)
Else yields @nbr[?].@(lb)
In other words: same as @nbr[(Not (Or input ...))]
@(inset (make-truth-table (a b) (Nor a b) #t))
@nbr[Nor] is commutative: it is invariant under permutation of its arguments.
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define Nor-abc (Nor a b c))
 (for/and ((abc (in-permutations (list a b c))))
  (eq? Nor-abc (apply Nor abc))))]
@nbr[Nor] is not associative, for example:
@Interaction[
(values (Nor (Nor 0 0) 1) (Nor 0 (Nor 0 1)))]}
@defproc[#:kind "elementary gate" (Xor (input trit?) ...) trit?]{
Yields @nbr[0] when called without @nbr[input]s.@(lb)
Yields @nbr[?] when at least one @nbr[input] is @nbr[?].@(lb)
Yields @nbr[1] when an odd number of @nbr[input]s is @nbr[1]
and all other @nbr[input]s, if any, are @nbr[0].@(lb)
Yields @nbr[0] when an even number of @nbr[input]s is @nbr[1]
and all other @nbr[input]s, if any, are @nbr[0].
@(inset (make-truth-table (a b) (Xor a b) #t))
@(inset (make-truth-table (a b c) (Xor a b c) #f))
@nbr[Xor] is commutative: it is invariant under permutation of its arguments.
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define Xor-abc (Xor a b c))
 (for/and ((abc (in-permutations (list a b c))))
  (eq? Xor-abc (apply Xor abc))))]
@nbr[Xor] is associative as well: a nest of @nbr[Xor]-forms can be replaced by one single
@nbr[Xor]-form.
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (define Xor-abc (Xor a b c))
 (and (eq? (Xor (Xor a b) c) Xor-abc)
      (eq? (Xor a (Xor b c)) Xor-abc)))]}
@defproc[#:kind "elementary gate" (Eq (p trit?) ...) trit?]{
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
@nbr[Eq] is not associative in @elemref["generalized-associativity"]{generalized sense}, for example:
@Interaction[(eq? (Eq 0 0 0) (Eq (Eq 0 0) 0))]
When restricted to two arguments, @nbr[Eq] is associative, though:
@Interaction[
(for*/and ((a in-trits) (b in-trits) (c in-trits))
 (eq? (Eq (Eq a b) c) (Eq a (Eq b c))))]
However, when applied to more than two arguments @nbr[Eq] looses its associativity.
@nb{In particular} @nbr[(Eq (Eq a b) c)] → @nbr[1]
does not imply that @tt{a}, @tt{b} and @tt{c} have the same value,
for example @nbr[(Eq (Eq 0 0) 1)] → @nbr[1].
Compare this with @nbr[(eq? (eq? #f #f) #t)] → @nbr[#t].}
@defproc[#:kind "elementary gate" (Implies (premise trit?)(implication trit?)) trit?]{
Same as: @nbr[(Or (Not premise) implication)].
@(inset (make-truth-table (premise implication) (Implies premise implication) #t))
@nbr[Implies] is not commutative nor associative:
@Interaction[
(values (Implies 0 1) (Implies 1 0))]
@Interaction[
(values (Implies (Implies 0 1) 0) (Implies 0 (Implies 1 0)))]
At first sight it may be confusing that @nbr[Implies] always returns true when the @nbr[premise]
is false, but it is logical, for assuming a false @nbr[premise] to be true destroys all logic.
When we assume a false @nbr[premise] to be true, every @nbr[implication] becomes true,
as well as the negation of every @nbr[implication].
In a proof ad absurdum, this rule often is used to prove that a given premise cannot be true.}
@defproc[#:kind "elementary gate" (If (test trit?) (then trit?) (else trit?)) trit?]{
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
Keyword @nbr[#:omit-?] may appear before, between or after the other two fields of the form,
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
   'not-ok)))]
The @nbr[expr] is not required to yield the same number of values for each
combination of @nbr[id]s:
@Interaction[
(truth-table (a b)
 (if (or (eq? a ?) (eq? b ?))
  (values ?)
  (values a b)))]}
@defproc[
(make-inputs (n exact-nonnegative-integer?) (include-? any/c)) (listof (listof trit?))]{
If @nbr[include-?] is @nbr[#f] a list of all possible combinations of @nbr[n] @nbrl[bit?]{bits}
is returned.@(lb)
In this case there are 2@↑{n} combinations and
each element of the list is a list of @nbr[n] @nbrl[bit?]{bits}.@(lb)
If @nbr[include-?] is not @nbr[#f] a list of all possible combinations of @nbr[n] @nbrl[bit?]{trits}
is returned.@(lb)
In this case there are 3@↑{n} combinations and
each element of the list is a list of @nbr[n] @nbrl[bit?]{trits}.
@Interaction[(make-inputs 0 #t)
             (make-inputs 1 #t)
             (make-inputs 2 #t)
             (make-inputs 3 #f)]}

@defproc[(apply-repeatedly (proc procedure?) (args (listof (listof any/c))))
         (values (listof any/c) ...)]{
Same as:
@inset{@tt{(@nbr[for/list] ((inputs (@nbr[in-list] @nbr[args])))@(lb)
@(hspace 1)(@nbr[values->list] (@nbr[apply] @nbr[proc] inputs)))}}
The following example shows subsequent responses of the @nb{@elemref["D-latch"]{D-latch}}
defined in the @secref{Introduction}.
@(reset-Interaction*)
@(define-make-D-latch #f)
@Interaction*[
(apply-repeatedly D-latch
 '((0 1) (? 0) (1 1) (1 0) (0 0) (? 1) (0 1) (? 0) (1 ?)))]}
@(reset-Interaction*)
@defform[(values->list expr)]{
Same as @nbr[(call-with-values (λ () expr) list)].}
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
(define make-6-bit-adder
 (make-circuit-maker 6-bit-adder
  (code:comment "Inputs:")
  (   c0 a5 a4 a3 a2 a1 a0
         b5 b4 b3 b2 b1 b0)
  (code:comment "Outputs:")
  (ov c6 s5 s4 s3 s2 s1 s0)
  (code:comment "Gates:")
  ((s0 c1) (1-bit-adder a0 b0 c0))
  ((s1 c2) (1-bit-adder a1 b1 c1))
  ((s2 c3) (1-bit-adder a2 b2 c2))
  ((s3 c4) (1-bit-adder a3 b3 c3))
  ((s4 c5) (1-bit-adder a4 b4 c4))
  ((s5 c6) (1-bit-adder a5 b5 c5))
  (ov (Xor c5 c6))))]
@Interaction*[
(define 6-bit-adder (make-6-bit-adder))]
The 1-bit-adder:
@Interaction*[
(define make-1-bit-adder
 (make-circuit-maker 1-bit-adder
  (code:comment "Inputs:")
  (a b carry-in)
  (code:comment "Outputs:")
  (sum carry-out)
  (code:comment "Gates:")
  (sum (Xor a b carry-in))
  (carry-out (Nand (Nand a b) (Nand a carry-in) (Nand b carry-in)))))]
@Interaction*[
(define 1-bit-adder (make-1-bit-adder))]
Notice that @nbr[(Nand (Nand a b) (Nand a c) (Nand b c))]@(lb)
yields the same as @nbr[(Or (And a b) (And a c) (And b c))]@(lb)
meaning that at least two of the signals @tt{a}, @tt{b} and @tt{c} must be @nbr[1]
in order to produce @nbr[1].

Because the outputs of procedure @nb{@tt{1-bit-adder}} do not depend on internal state,
@nb{we can} use the same instance six times in procedure @nb{@tt{6-bit-adder}}.
In a real life circuit, @nb{six distinct} instances are required, @nb{of course.}
In the following table the right column shows @nb{@tt{(sum carry-out)}}:
@(define 1-bit-adder
 ((make-circuit-maker 1-bit-adder
   (a b carry-in)
   (sum carry-out)
   (sum (Xor a b carry-in))
   (carry-out (Nand (Nand a b) (Nand a carry-in) (Nand b carry-in))))))
@(inset{make-truth-table (a b carry-in) (1-bit-adder a b carry-in) #f})
@ignore{Let's see an example of how the signals flow through the adder:
@Interaction*[
(begin
 (6-bit-adder
  0           (code:comment "carry-in")
  0 0 1 0 1 1 (code:comment "operand a")
  0 0 1 0 0 1 (code:comment "operand b")
  #:report #t)
 (void))]
In this case three steps are made. They are necessary to ripple the carry through the adder.
This slows down the adder, the worst case being adding @tt{1} to @tt{-1}:
@Interaction*[
(begin
 ((make-6-bit-adder)
   0           (code:comment "carry-in")
   1 1 1 1 1 1 (code:comment "operand a")
   0 0 0 0 0 1 (code:comment "operand b")
   #:report #t)
 ((make-6-bit-adder)
   0           (code:comment "carry-in")
   1 1 1 1 1 1 (code:comment "operand a")
   0 0 0 0 0 1 (code:comment "operand b")
   #:report #t)
 (void))]}
For testing the 6-bit-adder we need procedures for the conversion of
@nbrl[exact-nonnegative-integer?]{exact natural numbers} to lists of bits.
@Interaction*[
(define bitmasks (reverse '(1 2 4 8 16 32)))]
Number to list of bits.
@Interaction*[
(define (n->6b n)
 (for/list ((m (in-list bitmasks)))
  (if (zero? (bitwise-and m n)) 0 1)))]
List of bits to number.
@Interaction*[
(define (6b->n b)
 (define n
  (for/fold ((n 0)) ((b (in-list b)) (m (in-list bitmasks)))
   (if (zero? b) n (+ n m))))
 (if (>= n 32) (- n 64) n))]
Test @tt{n->6b} and @tt{6b->n}.
@Interaction*[
(for/and ((n (in-range -32 32)))
 (= (6b->n (n->6b n)) n))
(andmap (λ (x) (equal? x '(#t)))
 (apply-repeatedly
  (λ b (equal? (n->6b (6b->n b)) b))
  (make-inputs 6 #f)))]
Procedure @tt{run-example} takes two exact integer numbers @tt{x} and @tt{y} in the range
@nbr[-32] included to @nbr[+32] excluded and computes the sum with the @tt{6-bit-adder}.
It returns seven values:
@inset{@Tabular[
 ((@tt{x} " ")
  (@tt{y} " ")
  (@tt{x+y} (list "as computed by the " @tt{6-bit-adder}))
  (@tt{x} "as a list of bits")
  (@tt{y} "as a list of bits")
  (@tt{x+y} (list "as a list of bits computed by the " @tt{6-bit-adder}))
  (@tt{ov} "overflow bit"))
 #:sep (hspace 2)]}
@Interaction*[
(define (run-example x y)
 (let ((xb (n->6b x)) (yb (n->6b y)))
  (let
   ((ov/carry-out/sum
     (values->list (apply 6-bit-adder 0 (append xb yb)))))
   (define ov (car ov/carry-out/sum))
   (define sum (cddr ov/carry-out/sum))
   (values x y (6b->n sum) xb yb sum ov))))]
Let's test the @tt{6-bit-adder}.
@Interaction*[
(for*/and
 ((a (in-range -32 32))
  (b (in-range -32 32)))
 (define-values (x y x+y xb yb x+yb ov) (run-example a b))
 (cond
  ((< -33 (+ a b) 32) (and (= (6b->n x+yb) (+ a b)) (= ov 0)))
  (else (= ov 1))))]
We show some examples.
Each example shows the two operands and the sum, both in decimal and in binary notation
as a list of bits. In case of overflow, a message is shown.
@Interaction*[
(define (do-example a b)
 (define-values (x y x+y xb yb x+yb ov) (run-example a b))
 (when (= ov 1) (printf "Oveflow detected.~n"))
 (values x y x+y xb yb x+yb))
(do-example +15 +5)
(do-example +15 -5)
(do-example -15 +5)
(do-example -15 -5)]
Two examples of overflow.
@Interaction*[
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
                     b11 b10 b9 b8 b7 b6)))))]
@Interaction*[
(define (n->12b n)
 (for/fold
  ((n (if (negative? n) (+ n 4096) n))
   (12b '())
   #:result 12b)
  ((k (in-range 12)))
  (values (quotient n 2) (cons (if (odd? n) 1 0) 12b))))]
@Interaction*[
(define (12b->n bits)
 (for/fold
  ((bits bits) (n 0)
   #:result (if (< n 2048) n (- n 4096)))
  ((k (in-range 12)))
  (values (cdr bits)
   (if (T? (car bits)) (+ (* 2 n) 1) (* 2 n)))))]
Test @tt{n->12b} and @tt{12b->n}.
@Interaction*[
(for/and ((n (in-range -2048 2048)))
 (= (12b->n (n->12b n)) n))
(andmap (λ (x) (equal? x '(#t)))
 (apply-repeatedly
  (λ b (equal? (n->12b (12b->n b)) b))
  (make-inputs 12 #f)))]
Test the 12-bit-adder for some random inputs.
Some of the inputs may cause overflow.
This is tested as well.
@Interaction*[
(random-seed 1)
(define nr-of-overflows 0)
(define n 100)
(for*/and ((k (in-range n)))
 (define x (random -2048 2048))
 (define y (random -2048 2048))
 (define x+y (+ x y))
 (define ov/c/x+y
  (values->list
   (apply 12-bit-adder 0
    (append (n->12b x) (n->12b y)))))
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
 nr-of-overflows (- n nr-of-overflows))]
1023 + 85 = 1108
@Interaction*[
(let ((a 1023) (b 85))
 (define a-bits (n->12b a))
 (define b-bits (n->12b b))
 (define outputs
  (values->list
   (apply 12-bit-adder 0 (append a-bits b-bits))))
 (define a+b (12b->n (cddr outputs)))
 (printf "~s + ~s = ~s : this is ~a.~n" a b a+b
         (if (= a+b (+ a b)) 'correct 'INCORRECT))
 (values a-bits b-bits (cddr outputs)))]
Detection of overflow: 2000 + 100 ≥ 2@↑{11}.
An n-bit entity interpreted as a two's complement number is confined to the range from
@larger{@tt{-}}2@↑{n-1} inclusive to 2@↑{n-1} exclusive.
@nb{For 12 bit} two's complement numbers
this means from @larger{@tt{-}}@tt{2048} inclusive to @tt{2048} exclusive.
Hence 2000+100 must yield overflow:
@Interaction*[
(define a 2000)
(define b 100)
(define a-bits (n->12b a))
(define b-bits (n->12b b))
(define ov/c/sum-bits
 (values->list
  (apply 12-bit-adder 0 (append a-bits b-bits))))
(define ov (car ov/c/sum-bits))
(define sum-bits (cddr ov/c/sum-bits))
(define sum (12b->n sum-bits))
(begin
 (printf "a : ~s~n" a)
 (printf "b : ~s~n" b)
 (printf "s : ~s: wrong, of course. (-1996=2100-4096)~n" sum)
 (printf "a : ~s~n" a-bits)
 (printf "b : ~s~n" b-bits)
 (printf "s : ~s~n" sum-bits)
 (unless (T? ov) (error "Overflow not detected"))
 (printf "Overflow detected.~n"))]
@(reset-Interaction*)
@subsection{Unsigned numbers}
The @tt{6-bit-adder} and @tt{12-bit-adder} can be used for unsigned numbers too.
In that case the carry-out bit being @nbr[1] indicates overflow and the overflow bit can be ignored.
@subsection[#:tag "twin flip-flop"]{Twin flip-flop}
@note{Usually a twin flip-flop is called “master-slave flip-flop”,
but this is not a happy name.
If you want to search for more literature about twin flip-flops, you have to use the unhappy name,
I'm afraid.
@nb{A twin} consists of two elements, a first one and a second one.}
@ignore{There are several ways to construct a twin flip-flop.
Below two @nb{@elemref["D-latch"]{D-latches}} are used.
Because a D-latch has preserved internal state, we need two distinct instances
in the twin flip-flop, one for the first and one for the second D-latch.
@(define-make-D-latch #f)
@Interaction*[
(define make-twin-flip-flop
 (let ((first  (make-D-latch))
       (second (make-D-latch)))
  (make-circuit-maker twin-flip-flop
   (J K clock)
   (P Q)
   (first-in
    (Or
     (code:comment "Preserve state of first.")
     (And (Not J) (Not K) first-state=second-in)
     (code:comment "Set first.")
     (And J (Not K))
     (code:comment "Flip.")
     (And J K Q)))
    (code:comment "Else the first is reset or is preserved at 0.")
   ((first-state=second-in ignore) (first first-in clock))
   ((P Q) (second first-state=second-in (Not clock))))))]
@Interaction*[
(define twin-flip-flop (make-twin-flip-flop))]}
@do-not-ignore{There are several ways to construct a twin flip-flop.@(lb)
Below two @nb{SR-latches} are used. Hence we first define an SR-latch maker.
@inset{@image["SR-latch.gif" #:scale 1]}
@Interaction*[
(define make-SR-latch
 (make-circuit-maker SR-latch
  (S R clock) 
  (P Q)       
  (reset (Nand S clock))
  (set   (Nand R clock))
  (P     (Nand reset Q))
  (Q     (Nand set   P))))]
@tt{P} and @tt{Q} always are inverses of each other, provided never @tt{S=R=clock=1}
and the latch has been stabilized by setting or resetting it.
@tt{P} and @tt{Q} are the state and inverted state of the SR-latch.
The state transition table for an SR-latch after a @nbr[1]-pulse on the @tt{clock} is as follows:
@inset{@Tabular[
(((tt "S") (tt "R") (tt "P") (tt "Q") (list "new "(tt "P")) (list "new "(tt "Q")) "Action/warning")
 ((tt "0") (tt "0") (tt "P") (tt "Q") (tt "P") (tt "Q") "State preserved")
 ((tt "0") (tt "1") (tt " ") (tt " ") (tt "0") (tt "1") "Reset")
 ((tt "1") (tt "0") (tt " ") (tt " ") (tt "1") (tt "0") "Set")
 ((red (tt "1")) (red (tt "1")) " " 'cont 'cont 'cont @red{Do not clock this}))
 #:row-properties '((top-border bottom-border) () () () bottom-border)
 #:column-properties '(()()()() center center left)
 #:sep (hspace 2)]}
Because an SR-latch has preserved internal state, we need two distinct instances
in the twin flip-flop, one for the first and one for the second SR-latch.
@Interaction*[
(define make-twin-flip-flop
 (let ((SR-latch-1 (make-SR-latch))
       (SR-latch-2 (make-SR-latch)))
  (make-circuit-maker twin-flip-flop
   (J K clock) 
   (P Q)
   (code:comment "When both J and K are 1,")
   (code:comment "the second SR-latch must flip the first one.")
   (code:comment "In this case P and Q must be fed back")
   (code:comment "to inputs S1 and R1 of the first SR-latch.")
   (S1 (And J (Nand K P)))
   (R1 (And K (Nand J Q)))
   (code:comment "The two SR-latches.")
   ((P1 Q1) (SR-latch-1 S1 R1      clock))
   ((P  Q ) (SR-latch-2 P1 Q1 (Not clock))))))]
@Interaction*[
(define twin-flip-flop (make-twin-flip-flop))]}
After correct power up, @tt{P} and @tt{Q} always are inverses of each other.
They are the state and inverted state of the twin flip-flop.
The state transition table for the twin flip-flop after a @nb{@nbr[1]-pulse} on the
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
In contrast to an SR-latch, the twin flip-flop allows clocking with @nb{@tt{J}=@tt{K}=@nbr[1]}
in which case it flips its outputs.
In order to clock the twin flip-flop we need two calls,
one with @tt{clock=1} to set or reset or flip the first SR-latch or to leave it as it is and
one call with @tt{clock=0} in order to copy the state of the first SR-latch into the second one.
@tt{clock=1} may change the first SR-latch but leaves the second one unaffected.
@tt{clock=0} leaves the first SR-latch unaffected and
copies the state of the first one into the second one.
@Interaction*[
(define (clock-the-twin-flip-flop J K)
 (twin-flip-flop J K 1)
 (twin-flip-flop J K 0))]
During power up the twin flip-flop must be initialized with a @nbr[1] pulse on the clock
and @nb{@tt{J}=@nbr[0]} and @nb{@tt{K}=@nbr[1]} or reversely.
During the start up @nb{@tt{clock}=@nbr[1]} stabilizes the first SR-latch
while the second one remains unstable.
After the @tt{clock} falls down to @nbr[0] the second SR-latch is stabilized as well.
Let's test clocking the twin flip-flop for all combinations of
old state @nb{@tt{(P Q)}} and the inputs @tt{J} and @tt{K}.
@Interaction*[
(define (test/make-table) (code:comment "Does tests and gathers details in a table.") 
 (define (check computed expected)
  (unless (equal? computed expected) (error "test fails")))
 (for*/list ((J in-bits) (K in-bits) (P in-bits))
  (define Q (Not P))
  (code:comment "Put the flip-flop in state (P Q) and check it's done right.")
  (define-values (old-P old-Q) (clock-the-twin-flip-flop P Q))
  (check (list old-P old-Q) (list P Q))
  (code:comment "Clock the flip-flop with J and K.")
  (define-values (new-P new-Q) (clock-the-twin-flip-flop J K))
  (code:comment "Check:")
  (case (list J K)
   (((0 0)) (check (list new-P new-Q) (list old-P old-Q)))
   (((0 1)) (check (list new-P new-Q) (list 0 1)))
   (((1 0)) (check (list new-P new-Q) (list 1 0)))
   (((1 1)) (check (list new-P new-Q) (list old-Q old-P)))
   (else (error "test fails")))
  (code:comment "Gather results.")
  (list J K (list old-P old-Q) (list new-P new-Q) (action J K))))]
@Interaction*[
(define (action J K)
 (case (list J K)
  (((0 0)) "no action")
  (((0 1)) "reset")
  (((1 0)) "set")
  (((1 1)) "flip")))]
@Interaction*[
(define (do-test-and-print-table)
 (code:comment "We print the details in a table.")
 (code:comment "First the header of the table.")
 (define border (make-string 36 #\─))
 (printf " ~n~a~n" border)
 (printf "Transition table of twin flip-flop~n")
 (printf "     old state  new state~n")
 (printf "J K    (P Q)      (P Q)    action~n")
 (printf "~a~n" border)
 (code:comment "The test proper.")
 (define table (test/make-table))
 (code:comment "Print the results.")
 (for ((row (in-list table)))
  (apply printf "~s ~s    ~s      ~s    ~a~n" row))
 (printf "~a~n" border))]
@Interaction*[
(do-test-and-print-table)]

@(bold (larger (larger "The end")))
@(reset-Interaction*)
