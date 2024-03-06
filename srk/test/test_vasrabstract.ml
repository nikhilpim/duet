open Srk.Vasrabstract
open OUnit
open Test_pervasives

let check_coh_lin_maps real expected = 
  List.iter2 (fun ((real_dims, real_mat), real_wit) ((exp_dims, exp_mat), exp_wit) -> 
    assert_bool "witness does not match" (real_wit = exp_wit);
    assert_bool "matrix dims not correct" (real_dims = exp_dims);
    assert_equal_qqmatrix (exp_mat) (real_mat)
  ) real expected

let check_vasr_tfs expected real = 
  List.iter2 (fun ((real_vecdim, real_vec), real_res) ((exp_vecdim, exp_vec), exp_res) -> 
      assert_bool "vector dimension does not match" (real_vecdim = exp_vecdim);
      assert_bool "reset does not match" (real_res = exp_res);
      assert_equal_qqvector exp_vec real_vec
    ) real expected

let single_tf1 () = 
  let phi =
    let open Infix in
    x' = x + (int 1) && y' = (int 2) in
  let map, vasr = abstract_single_tf srk [(xsym, xsym'); (ysym, ysym')] phi in 
  let expected_map = [
    ((2, 1), mk_matrix [[1; 0]]), 0; 
    ((2, 1), mk_matrix [[0; 1]]), 0; 
  ] in 
  let expected_vasr = [((1, mk_vector [1]), false); ((1, mk_vector [2]), true)] in 
  check_coh_lin_maps expected_map map;
  check_vasr_tfs expected_vasr vasr


let sep_comp1 () = 
  let function1 : coherent_linear_map = [
    ((2, 2), mk_matrix [[1; 0]; [0; 2]]), 0 ;
    ((2, 2), mk_matrix [[3; 0]; [0; 4]]), 1
    ] in 
  let function2 : coherent_linear_map = [
    ((2, 2), mk_matrix [[5; 0]; [0; 6]]), 1 ;
    ((2, 2), mk_matrix [[7; 0]; [0; 8]]), 0
    ] in  
  let comp = sep_comp function1 function2 in 
  let expected = [
    ((2, 2), mk_matrix [[5; 0]; [0; 12]]), 1;
    ((2, 2), mk_matrix [[21; 0]; [0 ; 32]]), 0;
  ] in 
  check_coh_lin_maps expected comp

let sep_image1 () =
  let function1 : coherent_linear_map = [
    ((2, 2), mk_matrix [[1; 0]; [0; 2]]), 1 ;
    ((2, 2), mk_matrix [[3; 0]; [0; 4]]), 0
    ] in 
  let vasr1 = [((2, mk_vector [5 ; 6]), false); ((2, mk_vector [7 ; 8]), true)] in 
  let real_vasr = sep_image_vasr function1 vasr1 in 
  let expected_vasr = [((2, mk_vector [7 ; 16]), true) ; ((2, mk_vector [15 ; 24]), false)] in 
  check_vasr_tfs expected_vasr real_vasr

let sep_pushout1 () =
  let function1 = [
    (((2, 1), mk_matrix [[1; 0]]), 0);
    (((2, 1), mk_matrix [[0 ; 2]]), 0);
    (((2, 2), mk_matrix [[1; 1]; [0 ; 1]]), 1);
  ] in 
  let function2 = [
    (((2, 1), mk_matrix [[1; 1]]), 0);
    (((2, 2), mk_matrix [[1; 0]; [0 ; 1]]), 1);
  ] in 
  let a, b = sep_pushout function1 function2 in 
  check_coh_lin_maps (sep_comp a function1) (sep_comp b function2)
  
let suite = "Vasrabstract" >::: [
  "single_tf1" >:: single_tf1;
  "sep_comp1" >:: sep_comp1;
  "sep_image1" >:: sep_image1;
  "sep_pushout1" >:: sep_pushout1;
]