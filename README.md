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

D-latch is a procedure of two arguments *in* and *clock* and one output *state*.\
For example:

```
(D-latch 1 0) -> 0 ; reset the D-latch
(D-latch 0 ?) -> 0 ; get the current state
(D-latch 1 1) -> 1 ; set the D-latch
(D-latch 0 ?) -> 1 ; get the current state
```

Use DrRacket to make documentation from file manual.scrbl.\
The source-code is in file make-circuit.rkt.\
The simulator has some drawbacks.\
For example, it does not account for delays in gates and subcircuits.\
More information in the documentation.

Have fun!
