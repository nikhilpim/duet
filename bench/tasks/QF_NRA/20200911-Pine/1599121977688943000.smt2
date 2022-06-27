(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Anastasiia Izycheva, Eva Darulova
Generated on: 2020-09-11
Generator: Pine (using Z3 Python API)
Application: Check inductiveness of a loop invariant
Target solver: Z3

These benchmarks were generated while developing the tool Pine [1], which uses
CVC4/Z3 to check inductiveness of invariants. The work is described in [2].

[1] https://github.com/izycheva/pine
[2] A.Izycheva, E.Darulova, H.Seidl, SAS'20, "Counterexample- and Simulation-Guided Floating-Point Loop Invariant Synthesis"

 Loop:
   u' := u + 0.01 * v
   v' := v + 0.01 * (-0.5 * v - 9.81 * u)

 Input ranges:
   u in [0.0,0.0]
   v in [2.0,3.0]

 Invariant:
   -0.01*u + 0.01*v + 1.0*u^2 + 0.02*u*v + 0.09*v^2 <= 0.95
 and
   u in [-1.0,1.0]
   v in [-3.3,3.0]

 Query: Loop and Invariant and not Invariant'
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun u! () Real)
(declare-fun v! () Real)
(declare-fun u () Real)
(declare-fun v () Real)
(assert
 (let ((?x118 (+ (* (* (/ 1.0 50.0) u!) v!) (+ (* (* (/ 9.0 100.0) v!) v!) (* (- (/ 1.0 100.0)) u!)))))
 (let ((?x112 (* (/ 1.0 100.0) v!)))
 (let (($x98 (and (<= (- 1.0) u!) (>= 1.0 u!) (<= (- (/ 33.0 10.0)) v!) (>= 3.0 v!))))
 (let (($x25 (and $x98 (>= (/ 19.0 20.0) (+ ?x112 (+ (* (* 1.0 u!) u!) ?x118))) )))
 (let (($x156 (and (= u! (+ u (* (/ 1.0 100.0) v))) (= v! (+ v (* (/ 1.0 100.0) (- (* (- (/ 1.0 2.0)) v) (* (/ 981.0 100.0) u))))))))
 (let ((?x260 (+ (* (* (/ 1.0 50.0) u) v) (+ (* (* (/ 9.0 100.0) v) v) (* (- (/ 1.0 100.0)) u)))))
 (let ((?x122 (* (/ 1.0 100.0) v)))
 (let (($x249 (>= 3.0 v)))
 (let (($x99 (and (and (<= (- 1.0) u) (>= 1.0 u) (<= (- (/ 33.0 10.0)) v) $x249) (>= (/ 19.0 20.0) (+ ?x122 (+ (* (* 1.0 u) u) ?x260))) )))
 (and $x99 $x156 (not $x25))))))))))))
(check-sat)
(exit)
