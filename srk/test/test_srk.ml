open OUnit2

let suite = "Main" >::: [
    Test_arraylift.suite;
]

let _ =
  Printexc.record_backtrace true;
  Printf.printf "Running srk test suite";
  ignore (run_test_tt_main suite)
