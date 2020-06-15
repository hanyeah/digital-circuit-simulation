# digital-circuit-simulation

Written for use in DrRacket.\
For example: a very straight forward coding of a D-latch simulator:

```
#lang racket
(require make-circuit.rkt)
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

make-D-latch is a thunk that returns a distinct D-gate every time it is called.\
Every instance has its own internal state.\
D-latch is a procedure of two arguments *in* and *clock* and one output *state*.\
For example:

```
(D-latch 0 1) -> 0 ; reset
(D-latch ? 0) -> 0 ; get state
(D-latch 1 1) -> 1 ; set
(D-latch ? 0) -> 1 ; get state
```

Use DrRacket to make documentation from file manual.scrbl.\
The source-code is in file make-circuit.rkt.\
The simulator has some drawbacks.\
For example, it does not account for delays in gates and subcircuits.\
More information in the documentation.

Have fun!
