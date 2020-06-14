# digital-circuit-simulation
Simple tool for digital circuit simulation
```
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
