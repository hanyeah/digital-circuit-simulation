# digital-circuit-simulation

Written for use in DrRacket.\
For example: a very straight forward coding of a D-latch simulator:

```
#lang racket
(require "make-circuit.rkt")
(define make-D-latch
 (make-circuit-maker
  D-latch     ; name
  (in clock)  ; inputs
  (state)     ; outputs
  ; Gates:
  (reset         (Nand in    clock))
  (set           (Nand reset clock))
  (state         (Nand reset state-inverse))
  (state-inverse (Nand set   state))))
(define D-latch (make-D-latch))
```

Syntax make-circuit-maker produces a thunk, in the example make-D-latch.\
make-D-latch returns a distinct D-gate every time it is called.\
Every instance is a procedure with its own internal state.\
D-latch is a procedure of two arguments *in* and *clock* and one output *state*.\
For example:

```
(D-latch 0 1) -> 0 ; reset
(D-latch ? 0) -> 0 ; preserve state
(D-latch 1 1) -> 1 ; set
(D-latch ? 0) -> 1 ; preserve state
```

A ternary logic is used:
- 0 = false
- 1 = true
- ? = indeterminate

A number of gates is predefined, such as And, Or, Nand, Not, Xor and more.\
Some tools are included such as:
- for the preparation of truth-tables
- for running a circuit with a sequence of inputs

Use DrRacket to make documentation from file manual.scrbl.\
The source-code is in file make-circuit.rkt.\
The simulator has some drawbacks.\
For example, it does not account for delays in gates and subcircuits\
and has no tools for edge triggered circuits.\
More information in the documentation.

Have fun!
