(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by a component of the Ultimate program analysis framework [1] 
that implements a constraint-based synthesis of invariants [2].

This SMT script belongs to a set of SMT scripts that was generated by 
applying Ultimate to benchmarks [3] from the SV-COMP 2017 [4,5].

This script might _not_ contain all SMT commands that are used by 
Ultimate . In order to satisfy the restrictions of
the SMT-COMP we have to drop e.g., the commands for getting
values (resp. models), unsatisfiable cores and interpolants.

2017-05-01, Matthias Heizmann (heizmann@informatik.uni-freiburg.de)


[1] https://ultimate.informatik.uni-freiburg.de/
[2] Michael Colon, Sriram Sankaranarayanan, Henny Sipma: Linear Invariant 
Generation Using Non-linear Constraint Solving. CAV 2003: 420-432
[3] https://github.com/sosy-lab/sv-benchmarks
[4] Dirk Beyer: Software Verification with Validation of Results - 
(Report on SV-COMP 2017). TACAS (2) 2017: 331-349
[5] https://sv-comp.sosy-lab.org/2017/
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun lp_0_0c () Real)
(declare-fun lp_0_0_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_0_1c () Real)
(declare-fun lp_0_1_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_1_2c () Real)
(declare-fun lp_1_2_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_1_3c () Real)
(declare-fun lp_1_3_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_2_4c () Real)
(declare-fun lp_2_4_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_2_5c () Real)
(declare-fun lp_2_5_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_3_6c () Real)
(declare-fun lp_3_6_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_3_7c () Real)
(declare-fun lp_3_7_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_4_8c () Real)
(declare-fun lp_4_8_ULTIMATE.start_main_~i~4 () Real)
(declare-fun lp_4_9c () Real)
(declare-fun lp_4_9_ULTIMATE.start_main_~i~4 () Real)
(declare-fun motzkin_1752_0 () Real)
(declare-fun motzkin_1752_1 () Real)
(declare-fun motzkin_1752_2 () Real)
(declare-fun motzkin_1753_0 () Real)
(declare-fun motzkin_1753_1 () Real)
(declare-fun motzkin_1753_2 () Real)
(assert (and (>= motzkin_1752_0 0.0) (>= motzkin_1752_1 0.0) (>= motzkin_1752_2 0.0) (= (+ motzkin_1752_0 (* motzkin_1752_1 (- 1.0)) (* motzkin_1752_2 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (* motzkin_1752_2 (+ (* (- 1.0) lp_0_0c) 0.0)) 0.0) (or (< 0.0 0.0) (> motzkin_1752_2 0.0)) (>= motzkin_1753_0 0.0) (>= motzkin_1753_1 0.0) (>= motzkin_1753_2 0.0) (= (+ motzkin_1753_0 (* motzkin_1753_1 (- 1.0)) (* motzkin_1753_2 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (* motzkin_1753_2 (+ (* (- 1.0) lp_0_1c) 0.0)) 0.0) (or (< 0.0 0.0) (> motzkin_1753_2 0.0))))
(declare-fun motzkin_1754_0 () Real)
(declare-fun motzkin_1754_1 () Real)
(declare-fun motzkin_1754_2 () Real)
(declare-fun motzkin_1754_3 () Real)
(declare-fun motzkin_1754_4 () Real)
(declare-fun motzkin_1754_5 () Real)
(declare-fun motzkin_1755_0 () Real)
(declare-fun motzkin_1755_1 () Real)
(declare-fun motzkin_1755_2 () Real)
(declare-fun motzkin_1755_3 () Real)
(declare-fun motzkin_1755_4 () Real)
(declare-fun motzkin_1755_5 () Real)
(assert (and (>= motzkin_1754_0 0.0) (>= motzkin_1754_1 0.0) (>= motzkin_1754_2 0.0) (>= motzkin_1754_3 0.0) (>= motzkin_1754_4 0.0) (>= motzkin_1754_5 0.0) (= (+ (* motzkin_1754_0 (- 1.0)) motzkin_1754_2 (* motzkin_1754_3 (+ (* (- 1.0) lp_0_0_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1754_0 (* motzkin_1754_1 (- 1.0)) (* motzkin_1754_2 (- 1.0)) (* motzkin_1754_4 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1754_5 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ motzkin_1754_0 (* motzkin_1754_1 99999.0) (* motzkin_1754_2 (- 1.0)) (* motzkin_1754_3 (+ (* (- 1.0) lp_0_0c) 0.0)) (* motzkin_1754_4 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_1754_5 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ motzkin_1754_0 (* motzkin_1754_1 99999.0) (* motzkin_1754_2 (- 1.0)) (* motzkin_1754_4 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_1754_5 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> motzkin_1754_3 0.0)) (>= motzkin_1755_0 0.0) (>= motzkin_1755_1 0.0) (>= motzkin_1755_2 0.0) (>= motzkin_1755_3 0.0) (>= motzkin_1755_4 0.0) (>= motzkin_1755_5 0.0) (= (+ (* motzkin_1755_0 (- 1.0)) motzkin_1755_2 (* motzkin_1755_3 (+ (* (- 1.0) lp_0_1_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1755_0 (* motzkin_1755_1 (- 1.0)) (* motzkin_1755_2 (- 1.0)) (* motzkin_1755_4 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1755_5 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ motzkin_1755_0 (* motzkin_1755_1 99999.0) (* motzkin_1755_2 (- 1.0)) (* motzkin_1755_3 (+ (* (- 1.0) lp_0_1c) 0.0)) (* motzkin_1755_4 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_1755_5 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ motzkin_1755_0 (* motzkin_1755_1 99999.0) (* motzkin_1755_2 (- 1.0)) (* motzkin_1755_4 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_1755_5 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> motzkin_1755_3 0.0))))
(declare-fun motzkin_1756_0 () Real)
(declare-fun motzkin_1756_1 () Real)
(declare-fun motzkin_1756_2 () Real)
(declare-fun motzkin_1756_3 () Real)
(declare-fun motzkin_1756_4 () Real)
(declare-fun motzkin_1756_5 () Real)
(declare-fun motzkin_1757_0 () Real)
(declare-fun motzkin_1757_1 () Real)
(declare-fun motzkin_1757_2 () Real)
(declare-fun motzkin_1757_3 () Real)
(declare-fun motzkin_1757_4 () Real)
(declare-fun motzkin_1757_5 () Real)
(assert (and (>= motzkin_1756_0 0.0) (>= motzkin_1756_1 0.0) (>= motzkin_1756_2 0.0) (>= motzkin_1756_3 0.0) (>= motzkin_1756_4 0.0) (>= motzkin_1756_5 0.0) (= (+ motzkin_1756_0 (* motzkin_1756_2 (- 1.0)) (* motzkin_1756_3 (+ (* (- 1.0) lp_1_2_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1756_1 (* motzkin_1756_4 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1756_5 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1756_1 (- 100000.0)) (* motzkin_1756_3 (+ (* (- 1.0) lp_1_2c) 0.0)) (* motzkin_1756_4 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_1756_5 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_1756_1 (- 100000.0)) (* motzkin_1756_4 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_1756_5 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> motzkin_1756_3 0.0)) (>= motzkin_1757_0 0.0) (>= motzkin_1757_1 0.0) (>= motzkin_1757_2 0.0) (>= motzkin_1757_3 0.0) (>= motzkin_1757_4 0.0) (>= motzkin_1757_5 0.0) (= (+ motzkin_1757_0 (* motzkin_1757_2 (- 1.0)) (* motzkin_1757_3 (+ (* (- 1.0) lp_1_3_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1757_1 (* motzkin_1757_4 (+ (* 1.0 lp_0_0_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1757_5 (+ (* 1.0 lp_0_1_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1757_1 (- 100000.0)) (* motzkin_1757_3 (+ (* (- 1.0) lp_1_3c) 0.0)) (* motzkin_1757_4 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_1757_5 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (or (< (+ (* motzkin_1757_1 (- 100000.0)) (* motzkin_1757_4 (+ (* 1.0 lp_0_0c) 0.0)) (* motzkin_1757_5 (+ (* 1.0 lp_0_1c) 0.0))) 0.0) (> motzkin_1757_3 0.0))))
(declare-fun motzkin_1758_0 () Real)
(declare-fun motzkin_1758_1 () Real)
(declare-fun motzkin_1758_2 () Real)
(declare-fun motzkin_1758_3 () Real)
(declare-fun motzkin_1758_4 () Real)
(declare-fun motzkin_1758_5 () Real)
(declare-fun motzkin_1759_0 () Real)
(declare-fun motzkin_1759_1 () Real)
(declare-fun motzkin_1759_2 () Real)
(declare-fun motzkin_1759_3 () Real)
(declare-fun motzkin_1759_4 () Real)
(declare-fun motzkin_1759_5 () Real)
(assert (and (>= motzkin_1758_0 0.0) (>= motzkin_1758_1 0.0) (>= motzkin_1758_2 0.0) (>= motzkin_1758_3 0.0) (>= motzkin_1758_4 0.0) (>= motzkin_1758_5 0.0) (= (+ (* motzkin_1758_0 (- 1.0)) motzkin_1758_1 (* motzkin_1758_2 (- 1.0)) (* motzkin_1758_4 (+ (* 1.0 lp_1_2_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1758_5 (+ (* 1.0 lp_1_3_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ (* motzkin_1758_1 (- 1.0)) motzkin_1758_2 (* motzkin_1758_3 (+ (* (- 1.0) lp_1_2_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1758_0 99999.0) motzkin_1758_1 (* motzkin_1758_2 (- 1.0)) (* motzkin_1758_3 (+ (* (- 1.0) lp_1_2c) 0.0)) (* motzkin_1758_4 (+ (* 1.0 lp_1_2c) 0.0)) (* motzkin_1758_5 (+ (* 1.0 lp_1_3c) 0.0))) 0.0) (or (< (+ (* motzkin_1758_0 99999.0) motzkin_1758_1 (* motzkin_1758_2 (- 1.0)) (* motzkin_1758_4 (+ (* 1.0 lp_1_2c) 0.0)) (* motzkin_1758_5 (+ (* 1.0 lp_1_3c) 0.0))) 0.0) (> motzkin_1758_3 0.0)) (>= motzkin_1759_0 0.0) (>= motzkin_1759_1 0.0) (>= motzkin_1759_2 0.0) (>= motzkin_1759_3 0.0) (>= motzkin_1759_4 0.0) (>= motzkin_1759_5 0.0) (= (+ (* motzkin_1759_0 (- 1.0)) motzkin_1759_1 (* motzkin_1759_2 (- 1.0)) (* motzkin_1759_4 (+ (* 1.0 lp_1_2_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1759_5 (+ (* 1.0 lp_1_3_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ (* motzkin_1759_1 (- 1.0)) motzkin_1759_2 (* motzkin_1759_3 (+ (* (- 1.0) lp_1_3_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1759_0 99999.0) motzkin_1759_1 (* motzkin_1759_2 (- 1.0)) (* motzkin_1759_3 (+ (* (- 1.0) lp_1_3c) 0.0)) (* motzkin_1759_4 (+ (* 1.0 lp_1_2c) 0.0)) (* motzkin_1759_5 (+ (* 1.0 lp_1_3c) 0.0))) 0.0) (or (< (+ (* motzkin_1759_0 99999.0) motzkin_1759_1 (* motzkin_1759_2 (- 1.0)) (* motzkin_1759_4 (+ (* 1.0 lp_1_2c) 0.0)) (* motzkin_1759_5 (+ (* 1.0 lp_1_3c) 0.0))) 0.0) (> motzkin_1759_3 0.0))))
(declare-fun motzkin_1760_0 () Real)
(declare-fun motzkin_1760_1 () Real)
(declare-fun motzkin_1760_2 () Real)
(declare-fun motzkin_1760_3 () Real)
(declare-fun motzkin_1760_4 () Real)
(declare-fun motzkin_1760_5 () Real)
(declare-fun motzkin_1761_0 () Real)
(declare-fun motzkin_1761_1 () Real)
(declare-fun motzkin_1761_2 () Real)
(declare-fun motzkin_1761_3 () Real)
(declare-fun motzkin_1761_4 () Real)
(declare-fun motzkin_1761_5 () Real)
(assert (and (>= motzkin_1760_0 0.0) (>= motzkin_1760_1 0.0) (>= motzkin_1760_2 0.0) (>= motzkin_1760_3 0.0) (>= motzkin_1760_4 0.0) (>= motzkin_1760_5 0.0) (= (+ motzkin_1760_0 (* motzkin_1760_2 (- 1.0)) (* motzkin_1760_3 (+ (* (- 1.0) lp_2_4_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1760_1 (* motzkin_1760_4 (+ (* 1.0 lp_1_2_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1760_5 (+ (* 1.0 lp_1_3_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1760_1 (- 100000.0)) (* motzkin_1760_3 (+ (* (- 1.0) lp_2_4c) 0.0)) (* motzkin_1760_4 (+ (* 1.0 lp_1_2c) 0.0)) (* motzkin_1760_5 (+ (* 1.0 lp_1_3c) 0.0))) 0.0) (or (< (+ (* motzkin_1760_1 (- 100000.0)) (* motzkin_1760_4 (+ (* 1.0 lp_1_2c) 0.0)) (* motzkin_1760_5 (+ (* 1.0 lp_1_3c) 0.0))) 0.0) (> motzkin_1760_3 0.0)) (>= motzkin_1761_0 0.0) (>= motzkin_1761_1 0.0) (>= motzkin_1761_2 0.0) (>= motzkin_1761_3 0.0) (>= motzkin_1761_4 0.0) (>= motzkin_1761_5 0.0) (= (+ motzkin_1761_0 (* motzkin_1761_2 (- 1.0)) (* motzkin_1761_3 (+ (* (- 1.0) lp_2_5_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1761_1 (* motzkin_1761_4 (+ (* 1.0 lp_1_2_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1761_5 (+ (* 1.0 lp_1_3_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1761_1 (- 100000.0)) (* motzkin_1761_3 (+ (* (- 1.0) lp_2_5c) 0.0)) (* motzkin_1761_4 (+ (* 1.0 lp_1_2c) 0.0)) (* motzkin_1761_5 (+ (* 1.0 lp_1_3c) 0.0))) 0.0) (or (< (+ (* motzkin_1761_1 (- 100000.0)) (* motzkin_1761_4 (+ (* 1.0 lp_1_2c) 0.0)) (* motzkin_1761_5 (+ (* 1.0 lp_1_3c) 0.0))) 0.0) (> motzkin_1761_3 0.0))))
(declare-fun motzkin_1762_0 () Real)
(declare-fun motzkin_1762_1 () Real)
(declare-fun motzkin_1762_2 () Real)
(declare-fun motzkin_1762_3 () Real)
(declare-fun motzkin_1762_4 () Real)
(declare-fun motzkin_1762_5 () Real)
(declare-fun motzkin_1763_0 () Real)
(declare-fun motzkin_1763_1 () Real)
(declare-fun motzkin_1763_2 () Real)
(declare-fun motzkin_1763_3 () Real)
(declare-fun motzkin_1763_4 () Real)
(declare-fun motzkin_1763_5 () Real)
(assert (and (>= motzkin_1762_0 0.0) (>= motzkin_1762_1 0.0) (>= motzkin_1762_2 0.0) (>= motzkin_1762_3 0.0) (>= motzkin_1762_4 0.0) (>= motzkin_1762_5 0.0) (= (+ motzkin_1762_0 (* motzkin_1762_2 (- 1.0)) (* motzkin_1762_3 (+ (* (- 1.0) lp_3_6_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1762_1 (* motzkin_1762_4 (+ (* 1.0 lp_2_4_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1762_5 (+ (* 1.0 lp_2_5_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1762_1 (- 100000.0)) (* motzkin_1762_3 (+ (* (- 1.0) lp_3_6c) 0.0)) (* motzkin_1762_4 (+ (* 1.0 lp_2_4c) 0.0)) (* motzkin_1762_5 (+ (* 1.0 lp_2_5c) 0.0))) 0.0) (or (< (+ (* motzkin_1762_1 (- 100000.0)) (* motzkin_1762_4 (+ (* 1.0 lp_2_4c) 0.0)) (* motzkin_1762_5 (+ (* 1.0 lp_2_5c) 0.0))) 0.0) (> motzkin_1762_3 0.0)) (>= motzkin_1763_0 0.0) (>= motzkin_1763_1 0.0) (>= motzkin_1763_2 0.0) (>= motzkin_1763_3 0.0) (>= motzkin_1763_4 0.0) (>= motzkin_1763_5 0.0) (= (+ motzkin_1763_0 (* motzkin_1763_2 (- 1.0)) (* motzkin_1763_3 (+ (* (- 1.0) lp_3_7_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1763_1 (* motzkin_1763_4 (+ (* 1.0 lp_2_4_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1763_5 (+ (* 1.0 lp_2_5_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1763_1 (- 100000.0)) (* motzkin_1763_3 (+ (* (- 1.0) lp_3_7c) 0.0)) (* motzkin_1763_4 (+ (* 1.0 lp_2_4c) 0.0)) (* motzkin_1763_5 (+ (* 1.0 lp_2_5c) 0.0))) 0.0) (or (< (+ (* motzkin_1763_1 (- 100000.0)) (* motzkin_1763_4 (+ (* 1.0 lp_2_4c) 0.0)) (* motzkin_1763_5 (+ (* 1.0 lp_2_5c) 0.0))) 0.0) (> motzkin_1763_3 0.0))))
(declare-fun motzkin_1764_0 () Real)
(declare-fun motzkin_1764_1 () Real)
(declare-fun motzkin_1764_2 () Real)
(declare-fun motzkin_1764_3 () Real)
(declare-fun motzkin_1764_4 () Real)
(declare-fun motzkin_1764_5 () Real)
(declare-fun motzkin_1765_0 () Real)
(declare-fun motzkin_1765_1 () Real)
(declare-fun motzkin_1765_2 () Real)
(declare-fun motzkin_1765_3 () Real)
(declare-fun motzkin_1765_4 () Real)
(declare-fun motzkin_1765_5 () Real)
(assert (and (>= motzkin_1764_0 0.0) (>= motzkin_1764_1 0.0) (>= motzkin_1764_2 0.0) (>= motzkin_1764_3 0.0) (>= motzkin_1764_4 0.0) (>= motzkin_1764_5 0.0) (= (+ (* motzkin_1764_0 (- 1.0)) motzkin_1764_2 (* motzkin_1764_3 (+ (* (- 1.0) lp_2_4_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1764_0 (* motzkin_1764_1 (- 1.0)) (* motzkin_1764_2 (- 1.0)) (* motzkin_1764_4 (+ (* 1.0 lp_2_4_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1764_5 (+ (* 1.0 lp_2_5_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ motzkin_1764_0 (* motzkin_1764_1 99999.0) (* motzkin_1764_2 (- 1.0)) (* motzkin_1764_3 (+ (* (- 1.0) lp_2_4c) 0.0)) (* motzkin_1764_4 (+ (* 1.0 lp_2_4c) 0.0)) (* motzkin_1764_5 (+ (* 1.0 lp_2_5c) 0.0))) 0.0) (or (< (+ motzkin_1764_0 (* motzkin_1764_1 99999.0) (* motzkin_1764_2 (- 1.0)) (* motzkin_1764_4 (+ (* 1.0 lp_2_4c) 0.0)) (* motzkin_1764_5 (+ (* 1.0 lp_2_5c) 0.0))) 0.0) (> motzkin_1764_3 0.0)) (>= motzkin_1765_0 0.0) (>= motzkin_1765_1 0.0) (>= motzkin_1765_2 0.0) (>= motzkin_1765_3 0.0) (>= motzkin_1765_4 0.0) (>= motzkin_1765_5 0.0) (= (+ (* motzkin_1765_0 (- 1.0)) motzkin_1765_2 (* motzkin_1765_3 (+ (* (- 1.0) lp_2_5_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1765_0 (* motzkin_1765_1 (- 1.0)) (* motzkin_1765_2 (- 1.0)) (* motzkin_1765_4 (+ (* 1.0 lp_2_4_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1765_5 (+ (* 1.0 lp_2_5_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ motzkin_1765_0 (* motzkin_1765_1 99999.0) (* motzkin_1765_2 (- 1.0)) (* motzkin_1765_3 (+ (* (- 1.0) lp_2_5c) 0.0)) (* motzkin_1765_4 (+ (* 1.0 lp_2_4c) 0.0)) (* motzkin_1765_5 (+ (* 1.0 lp_2_5c) 0.0))) 0.0) (or (< (+ motzkin_1765_0 (* motzkin_1765_1 99999.0) (* motzkin_1765_2 (- 1.0)) (* motzkin_1765_4 (+ (* 1.0 lp_2_4c) 0.0)) (* motzkin_1765_5 (+ (* 1.0 lp_2_5c) 0.0))) 0.0) (> motzkin_1765_3 0.0))))
(declare-fun motzkin_1766_0 () Real)
(declare-fun motzkin_1766_1 () Real)
(declare-fun motzkin_1766_2 () Real)
(declare-fun motzkin_1766_3 () Real)
(declare-fun motzkin_1766_4 () Real)
(declare-fun motzkin_1766_5 () Real)
(declare-fun motzkin_1767_0 () Real)
(declare-fun motzkin_1767_1 () Real)
(declare-fun motzkin_1767_2 () Real)
(declare-fun motzkin_1767_3 () Real)
(declare-fun motzkin_1767_4 () Real)
(declare-fun motzkin_1767_5 () Real)
(assert (and (>= motzkin_1766_0 0.0) (>= motzkin_1766_1 0.0) (>= motzkin_1766_2 0.0) (>= motzkin_1766_3 0.0) (>= motzkin_1766_4 0.0) (>= motzkin_1766_5 0.0) (= (+ (* motzkin_1766_0 (- 1.0)) motzkin_1766_1 (* motzkin_1766_2 (- 1.0)) (* motzkin_1766_4 (+ (* 1.0 lp_3_6_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1766_5 (+ (* 1.0 lp_3_7_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ (* motzkin_1766_1 (- 1.0)) motzkin_1766_2 (* motzkin_1766_3 (+ (* (- 1.0) lp_3_6_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1766_0 99999.0) motzkin_1766_1 (* motzkin_1766_2 (- 1.0)) (* motzkin_1766_3 (+ (* (- 1.0) lp_3_6c) 0.0)) (* motzkin_1766_4 (+ (* 1.0 lp_3_6c) 0.0)) (* motzkin_1766_5 (+ (* 1.0 lp_3_7c) 0.0))) 0.0) (or (< (+ (* motzkin_1766_0 99999.0) motzkin_1766_1 (* motzkin_1766_2 (- 1.0)) (* motzkin_1766_4 (+ (* 1.0 lp_3_6c) 0.0)) (* motzkin_1766_5 (+ (* 1.0 lp_3_7c) 0.0))) 0.0) (> motzkin_1766_3 0.0)) (>= motzkin_1767_0 0.0) (>= motzkin_1767_1 0.0) (>= motzkin_1767_2 0.0) (>= motzkin_1767_3 0.0) (>= motzkin_1767_4 0.0) (>= motzkin_1767_5 0.0) (= (+ (* motzkin_1767_0 (- 1.0)) motzkin_1767_1 (* motzkin_1767_2 (- 1.0)) (* motzkin_1767_4 (+ (* 1.0 lp_3_6_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1767_5 (+ (* 1.0 lp_3_7_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ (* motzkin_1767_1 (- 1.0)) motzkin_1767_2 (* motzkin_1767_3 (+ (* (- 1.0) lp_3_7_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1767_0 99999.0) motzkin_1767_1 (* motzkin_1767_2 (- 1.0)) (* motzkin_1767_3 (+ (* (- 1.0) lp_3_7c) 0.0)) (* motzkin_1767_4 (+ (* 1.0 lp_3_6c) 0.0)) (* motzkin_1767_5 (+ (* 1.0 lp_3_7c) 0.0))) 0.0) (or (< (+ (* motzkin_1767_0 99999.0) motzkin_1767_1 (* motzkin_1767_2 (- 1.0)) (* motzkin_1767_4 (+ (* 1.0 lp_3_6c) 0.0)) (* motzkin_1767_5 (+ (* 1.0 lp_3_7c) 0.0))) 0.0) (> motzkin_1767_3 0.0))))
(declare-fun motzkin_1768_0 () Real)
(declare-fun motzkin_1768_1 () Real)
(declare-fun motzkin_1768_2 () Real)
(declare-fun motzkin_1768_3 () Real)
(declare-fun motzkin_1768_4 () Real)
(declare-fun motzkin_1768_5 () Real)
(declare-fun motzkin_1769_0 () Real)
(declare-fun motzkin_1769_1 () Real)
(declare-fun motzkin_1769_2 () Real)
(declare-fun motzkin_1769_3 () Real)
(declare-fun motzkin_1769_4 () Real)
(declare-fun motzkin_1769_5 () Real)
(assert (and (>= motzkin_1768_0 0.0) (>= motzkin_1768_1 0.0) (>= motzkin_1768_2 0.0) (>= motzkin_1768_3 0.0) (>= motzkin_1768_4 0.0) (>= motzkin_1768_5 0.0) (= (+ (* motzkin_1768_0 (- 1.0)) motzkin_1768_2 (* motzkin_1768_3 (+ (* (- 1.0) lp_4_8_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1768_1 (* motzkin_1768_4 (+ (* 1.0 lp_3_6_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1768_5 (+ (* 1.0 lp_3_7_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1768_1 (- 100000.0)) (* motzkin_1768_3 (+ (* (- 1.0) lp_4_8c) 0.0)) (* motzkin_1768_4 (+ (* 1.0 lp_3_6c) 0.0)) (* motzkin_1768_5 (+ (* 1.0 lp_3_7c) 0.0))) 0.0) (or (< (+ (* motzkin_1768_1 (- 100000.0)) (* motzkin_1768_4 (+ (* 1.0 lp_3_6c) 0.0)) (* motzkin_1768_5 (+ (* 1.0 lp_3_7c) 0.0))) 0.0) (> motzkin_1768_3 0.0)) (>= motzkin_1769_0 0.0) (>= motzkin_1769_1 0.0) (>= motzkin_1769_2 0.0) (>= motzkin_1769_3 0.0) (>= motzkin_1769_4 0.0) (>= motzkin_1769_5 0.0) (= (+ (* motzkin_1769_0 (- 1.0)) motzkin_1769_2 (* motzkin_1769_3 (+ (* (- 1.0) lp_4_9_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1769_1 (* motzkin_1769_4 (+ (* 1.0 lp_3_6_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1769_5 (+ (* 1.0 lp_3_7_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ (* motzkin_1769_1 (- 100000.0)) (* motzkin_1769_3 (+ (* (- 1.0) lp_4_9c) 0.0)) (* motzkin_1769_4 (+ (* 1.0 lp_3_6c) 0.0)) (* motzkin_1769_5 (+ (* 1.0 lp_3_7c) 0.0))) 0.0) (or (< (+ (* motzkin_1769_1 (- 100000.0)) (* motzkin_1769_4 (+ (* 1.0 lp_3_6c) 0.0)) (* motzkin_1769_5 (+ (* 1.0 lp_3_7c) 0.0))) 0.0) (> motzkin_1769_3 0.0))))
(declare-fun motzkin_1770_0 () Real)
(declare-fun motzkin_1770_1 () Real)
(declare-fun motzkin_1770_2 () Real)
(declare-fun motzkin_1770_3 () Real)
(declare-fun motzkin_1770_4 () Real)
(declare-fun motzkin_1770_5 () Real)
(declare-fun motzkin_1771_0 () Real)
(declare-fun motzkin_1771_1 () Real)
(declare-fun motzkin_1771_2 () Real)
(declare-fun motzkin_1771_3 () Real)
(declare-fun motzkin_1771_4 () Real)
(declare-fun motzkin_1771_5 () Real)
(assert (and (>= motzkin_1770_0 0.0) (>= motzkin_1770_1 0.0) (>= motzkin_1770_2 0.0) (>= motzkin_1770_3 0.0) (>= motzkin_1770_4 0.0) (>= motzkin_1770_5 0.0) (= (+ (* motzkin_1770_0 (- 1.0)) motzkin_1770_2 (* motzkin_1770_3 (+ (* (- 1.0) lp_4_8_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1770_0 (* motzkin_1770_1 (- 1.0)) (* motzkin_1770_2 (- 1.0)) (* motzkin_1770_4 (+ (* 1.0 lp_4_8_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1770_5 (+ (* 1.0 lp_4_9_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ motzkin_1770_0 (* motzkin_1770_1 99999.0) (* motzkin_1770_2 (- 1.0)) (* motzkin_1770_3 (+ (* (- 1.0) lp_4_8c) 0.0)) (* motzkin_1770_4 (+ (* 1.0 lp_4_8c) 0.0)) (* motzkin_1770_5 (+ (* 1.0 lp_4_9c) 0.0))) 0.0) (or (< (+ motzkin_1770_0 (* motzkin_1770_1 99999.0) (* motzkin_1770_2 (- 1.0)) (* motzkin_1770_4 (+ (* 1.0 lp_4_8c) 0.0)) (* motzkin_1770_5 (+ (* 1.0 lp_4_9c) 0.0))) 0.0) (> motzkin_1770_3 0.0)) (>= motzkin_1771_0 0.0) (>= motzkin_1771_1 0.0) (>= motzkin_1771_2 0.0) (>= motzkin_1771_3 0.0) (>= motzkin_1771_4 0.0) (>= motzkin_1771_5 0.0) (= (+ (* motzkin_1771_0 (- 1.0)) motzkin_1771_2 (* motzkin_1771_3 (+ (* (- 1.0) lp_4_9_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1771_0 (* motzkin_1771_1 (- 1.0)) (* motzkin_1771_2 (- 1.0)) (* motzkin_1771_4 (+ (* 1.0 lp_4_8_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1771_5 (+ (* 1.0 lp_4_9_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (<= (+ motzkin_1771_0 (* motzkin_1771_1 99999.0) (* motzkin_1771_2 (- 1.0)) (* motzkin_1771_3 (+ (* (- 1.0) lp_4_9c) 0.0)) (* motzkin_1771_4 (+ (* 1.0 lp_4_8c) 0.0)) (* motzkin_1771_5 (+ (* 1.0 lp_4_9c) 0.0))) 0.0) (or (< (+ motzkin_1771_0 (* motzkin_1771_1 99999.0) (* motzkin_1771_2 (- 1.0)) (* motzkin_1771_4 (+ (* 1.0 lp_4_8c) 0.0)) (* motzkin_1771_5 (+ (* 1.0 lp_4_9c) 0.0))) 0.0) (> motzkin_1771_3 0.0))))
(declare-fun motzkin_1772_0 () Real)
(declare-fun motzkin_1772_1 () Real)
(declare-fun motzkin_1772_2 () Real)
(declare-fun motzkin_1772_3 () Real)
(declare-fun motzkin_1772_4 () Real)
(declare-fun motzkin_1772_5 () Real)
(declare-fun motzkin_1772_6 () Real)
(declare-fun motzkin_1772_7 () Real)
(declare-fun motzkin_1772_8 () Real)
(declare-fun motzkin_1772_9 () Real)
(declare-fun motzkin_1773_0 () Real)
(declare-fun motzkin_1773_1 () Real)
(declare-fun motzkin_1773_2 () Real)
(declare-fun motzkin_1773_3 () Real)
(declare-fun motzkin_1773_4 () Real)
(declare-fun motzkin_1773_5 () Real)
(declare-fun motzkin_1773_6 () Real)
(declare-fun motzkin_1773_7 () Real)
(declare-fun motzkin_1773_8 () Real)
(declare-fun motzkin_1773_9 () Real)
(assert (and (>= motzkin_1772_0 0.0) (>= motzkin_1772_1 0.0) (>= motzkin_1772_2 0.0) (>= motzkin_1772_3 0.0) (>= motzkin_1772_4 0.0) (>= motzkin_1772_5 0.0) (>= motzkin_1772_6 0.0) (>= motzkin_1772_7 0.0) (>= motzkin_1772_8 0.0) (>= motzkin_1772_9 0.0) (= (+ motzkin_1772_0 (* motzkin_1772_1 (- 1.0)) motzkin_1772_2 (* motzkin_1772_4 (- 1.0))) 0.0) (= (+ (* motzkin_1772_0 (- 1.0)) motzkin_1772_4) 0.0) (= (+ motzkin_1772_3 (* motzkin_1772_8 (+ (* 1.0 lp_4_8_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1772_9 (+ (* 1.0 lp_4_9_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= motzkin_1772_5 0.0) (= (+ motzkin_1772_6 (* motzkin_1772_7 (- 1.0))) 0.0) (<= (+ (* motzkin_1772_3 (- 100000.0)) (* motzkin_1772_5 (- 46.0)) (* motzkin_1772_8 (+ (* 1.0 lp_4_8c) 0.0)) (* motzkin_1772_9 (+ (* 1.0 lp_4_9c) 0.0))) 0.0) (or (< (+ (* motzkin_1772_3 (- 100000.0)) (* motzkin_1772_5 (- 46.0)) (* motzkin_1772_8 (+ (* 1.0 lp_4_8c) 0.0)) (* motzkin_1772_9 (+ (* 1.0 lp_4_9c) 0.0))) 0.0) (> 0.0 0.0)) (>= motzkin_1773_0 0.0) (>= motzkin_1773_1 0.0) (>= motzkin_1773_2 0.0) (>= motzkin_1773_3 0.0) (>= motzkin_1773_4 0.0) (>= motzkin_1773_5 0.0) (>= motzkin_1773_6 0.0) (>= motzkin_1773_7 0.0) (>= motzkin_1773_8 0.0) (>= motzkin_1773_9 0.0) (= (* motzkin_1773_0 (- 1.0)) 0.0) (= (+ motzkin_1773_1 (* motzkin_1773_2 (- 1.0)) motzkin_1773_3 (* motzkin_1773_5 (- 1.0))) 0.0) (= (+ (* motzkin_1773_1 (- 1.0)) motzkin_1773_5) 0.0) (= (+ motzkin_1773_4 (* motzkin_1773_8 (+ (* 1.0 lp_4_8_ULTIMATE.start_main_~i~4) 0.0)) (* motzkin_1773_9 (+ (* 1.0 lp_4_9_ULTIMATE.start_main_~i~4) 0.0))) 0.0) (= (+ motzkin_1773_6 (* motzkin_1773_7 (- 1.0))) 0.0) (<= (+ (* motzkin_1773_0 44.0) (* motzkin_1773_4 (- 100000.0)) (* motzkin_1773_8 (+ (* 1.0 lp_4_8c) 0.0)) (* motzkin_1773_9 (+ (* 1.0 lp_4_9c) 0.0))) 0.0) (or (< (+ (* motzkin_1773_0 44.0) (* motzkin_1773_4 (- 100000.0)) (* motzkin_1773_8 (+ (* 1.0 lp_4_8c) 0.0)) (* motzkin_1773_9 (+ (* 1.0 lp_4_9c) 0.0))) 0.0) (> 0.0 0.0))))
(check-sat)
(exit)
