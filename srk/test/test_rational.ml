open OUnit
open Srk
open Rational
open Polynomial


type block = TransitionIdeal.block


let mat_mul_v m v = 
  Array.map (
    fun row ->
      let dot_prod = Array.map2 (
        fun q p ->  QQXs.scalar_mul q p
      ) row v in
      Array.fold_left QQXs.add QQXs.zero dot_prod
  ) m

let enumerate mat init add n = 
  let rec aux acc curr_v curr_n = 
    if curr_n >= n then
      Array.map List.rev acc
    else
      let next_v = Array.map2 QQXs.add (mat_mul_v mat curr_v) add in
      aux (Array.map2 (fun v l -> v :: l) next_v acc) next_v (curr_n + 1)
  in
  aux (Array.init (Array.length mat) (fun i -> [init.(i)])) init 0

let enumerate_sp ?(initial = None) sp n = 
  let size = List.fold_left (+) 0 (List.map (fun (blk : block) -> Array.length blk.blk_transform) sp) in
  let init = 
    match initial with
    | None -> Array.init size (fun i -> QQXs.of_dim i) 
    | Some x ->
      Array.init size (fun i -> match x.(i) with | None -> QQXs.of_dim i | Some v -> QQXs.scalar v)
    in
  let rec aux acc curr_v curr_n = 
    if curr_n >= n then
      Array.map List.rev acc
    else
      let next_v = Array.make size QQXs.zero in
      let  _ = List.fold_left (
        fun offset (blk : block) ->
          let translate_blk_add p =
            QQXs.fold (
              fun m coef rs ->
                let mon_rs = BatEnum.fold (
                  fun acc (dim, pow) ->
                    QQXs.mul acc (QQXs.exp (curr_v.(dim)) pow)  (* <-- Which is it supposed to be curr_v or next_v*)
                ) QQXs.one (Monomial.enum m) in
                QQXs.add (QQXs.scalar_mul coef mon_rs) rs
            ) p QQXs.zero
          in
          let mat_mult = mat_mul_v blk.blk_transform (Array.sub curr_v offset (Array.length blk.blk_transform)) in
          let result = Array.map2 QQXs.add mat_mult (Array.map translate_blk_add blk.blk_add) in
          for i = 0 to (Array.length mat_mult) - 1 do
            next_v.(i + offset) <- result.(i)
          done;
          offset + (Array.length mat_mult)
      ) 0 sp in
      aux (Array.map2 (fun v l -> v :: l) next_v acc) next_v (curr_n + 1)
  in
  aux (Array.init size (fun i -> [init.(i)])) init 0

let qqify_v = Array.map (QQ.of_int)

let qqify = Array.map qqify_v



let assert_equal_seq =
  let eq = List.equal (QQXs.equal) in
  let qq_pp = QQXs.pp (fun fo d -> Format.fprintf fo "x_%d" d) in
  let printer f l = Format.fprintf f "[%a]" (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f ";"; Format.pp_print_space f ()) qq_pp) l in
  assert_equal ~cmp:eq ~printer:(SrkUtil.mk_show printer)

let assert_equal_ep = 
  assert_equal ~cmp:(RatEP.equal) ~printer:(SrkUtil.mk_show RatEP.pp)


let mat_rec_test1 () =
  let transform = qqify [|[|2; 0|];
                        [|0; 3|]|] in
  let add = [|QQXs.zero; QQXs.zero|] in
  let init = [|QQXs.of_dim 0; QQXs.of_dim 1|] in
  let first_10 = enumerate transform init add 9 in
  let eps = RatEP.solve_rec [({blk_transform = transform; blk_add = add} : block)] in
  (*Array.iteri (fun dim ep ->
    Log.logf ~level:`always "Dim %d : %a" dim RatEP.pp ep) eps;*)
  let dim0_10 = List.init 10 (fun i -> RatEP.eval eps.(0) i) in
  let dim1_10 = List.init 10 (fun i -> RatEP.eval eps.(1) i) in
  assert_equal_seq first_10.(0) dim0_10;
  assert_equal_seq first_10.(1) dim1_10

let mat_rec_test2 () =
  let transform = qqify [|[|0; 1|];
                          [|0; 0|];|] in
  let add = [|QQXs.zero; QQXs.zero|] in
  let init = [|QQXs.of_dim 0; QQXs.of_dim 1|] in
  let first_10 = enumerate transform init add 9 in
  let eps = RatEP.solve_rec [({blk_transform = transform; blk_add = add} : block)] in
  (*Array.iteri (fun dim ep ->
    Log.logf ~level:`always "Dim %d : %a" dim RatEP.pp ep) eps;*)
  let dim0_10 = List.init 10 (fun i -> RatEP.eval eps.(0) i) in
  let dim1_10 = List.init 10 (fun i -> RatEP.eval eps.(1) i) in
  assert_equal_seq first_10.(0) dim0_10;
  assert_equal_seq first_10.(1) dim1_10

let sp_test1 () =
  let transform1 = qqify [|[|2; 0|];
                          [|0; 3|]|] in
  let add1 = [|QQXs.zero; QQXs.zero|] in
  let blk1 : block = {blk_transform = transform1; blk_add = add1} in
  let transform2 = qqify [|[|4|]|] in
  let add2 = [|Polynomial.QQXs.mul (Polynomial.QQXs.of_dim 0) (Polynomial.QQXs.of_dim 1)|] in
  let blk2 : block = {blk_transform = transform2; blk_add = add2} in
  let eps = RatEP.solve_rec [blk1; blk2] in
  (*Array.iteri (fun dim ep ->
    Log.logf ~level:`always "Dim %d : %a" dim RatEP.pp ep) eps;*)
  let first_10 = enumerate_sp [blk1; blk2] 9 in
  let dim0_10 = List.init 10 (fun i -> RatEP.eval eps.(0) i) in
  let dim1_10 = List.init 10 (fun i -> RatEP.eval eps.(1) i) in
  let dim2_10 = List.init 10 (fun i -> RatEP.eval eps.(2) i) in
  assert_equal_seq first_10.(0) dim0_10;
  assert_equal_seq first_10.(1) dim1_10;
  assert_equal_seq first_10.(2) dim2_10

let iif_test1 () =
  let transform1 = qqify [|[|1; 1|];
                          [|1; 0|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let blk : block = {blk_transform = transform1; blk_add = add1} in
  let eps = RatEP.solve_rec [blk] in
  Array.iteri (fun dim ep ->
    Log.logf ~level:`always "Dim %d : %a" dim RatEP.pp ep) eps

let zero_eigen_test () = 
  let transform1 = qqify [|[|0; 1|];
                          [|0; 0|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let blk : block = {blk_transform = transform1; blk_add = add1} in
  let eps = RatEP.solve_rec [blk] in
  (*Array.iteri (fun dim ep ->
    Log.logf ~level:`always "Dim %d : %a" dim RatEP.pp ep) eps;*)
  let first_10 = enumerate_sp [blk] 9 in
  let dim0_10 = List.init 10 (fun i -> RatEP.eval eps.(0) i) in
  let dim1_10 = List.init 10 (fun i -> RatEP.eval eps.(1) i) in
  assert_equal_seq first_10.(0) dim0_10;
  assert_equal_seq first_10.(1) dim1_10
  (*let module EP = (val RatEP.to_nf eps) in
  let nf_rat_to_rat nf = 
    if QQX.order (EP.NF.get_poly nf) > 0 then failwith "NF value wasn't rational";
    QQX.coeff 0 (EP.NF.get_poly nf)
  in
  let const_ring_nf_to_qqxs p = 
    let monomial_to_rat (nf, m) = (nf_rat_to_rat nf, m) in
    QQXs.of_enum (BatEnum.map monomial_to_rat (EP.ConstRing.enum p))
  in
  let (transient, shift, relations) = EP.long_run_algebraic_relations () in
  let transient_rat = List.map (Array.map const_ring_nf_to_qqxs) transient in
  let v_printer fo d =
    if d < Array.length eps then Format.fprintf fo "x_%d" d
    else if d < 2 * (Array.length eps) then Format.fprintf fo "x'_%d" (d - Array.length eps)
    else Format.pp_print_string fo "K"
  in
  List.iteri (
    fun i pos ->
      let pp_l = Format.pp_print_list ~pp_sep:(fun fo () -> Format.fprintf fo "; ") (QQXs.pp v_printer) in
      Log.logf ~level:`always "Pos %d : [%a]" i pp_l (Array.to_list pos)
  ) transient_rat;
  Log.logf ~level:`always "Relations when x>=%d" shift;
  List.iter (fun p ->
    Log.logf ~level:`always "%a" (Polynomial.QQXs.pp v_printer) p
    ) relations*)



let nf_test1 () =
  let transform1 = qqify [|[|1; 1|];
                          [|1; 0|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let blk : block = {blk_transform = transform1; blk_add = add1} in
  let eps = RatEP.solve_rec [blk] in
  let module EP = (val RatEP.to_nf eps) in
  let nf_eps = EP.get_rec_sols () in
  (*Array.iteri (fun dim ep ->
    Log.logf ~level:`always "Dim %d : %a" dim EP.pp ep) nf_eps;*)
  let first_10 = enumerate_sp [blk] 9 in
  let nf_rat_to_rat nf = 
    if QQX.order (EP.NF.get_poly nf) > 0 then failwith "NF value wasn't rational";
    QQX.coeff 0 (EP.NF.get_poly nf)
  in
  let const_ring_nf_to_qqxs p = 
    let monomial_to_rat (nf, m) = (nf_rat_to_rat nf, m) in
    QQXs.of_enum (BatEnum.map monomial_to_rat (EP.ConstRing.enum p))
  in
  let dim0_10 = List.init 10 (fun i -> const_ring_nf_to_qqxs (EP.eval nf_eps.(0) i)) in
  let dim1_10 = List.init 10 (fun i -> const_ring_nf_to_qqxs (EP.eval nf_eps.(1) i)) in
  assert_equal_seq first_10.(0) dim0_10;
  assert_equal_seq first_10.(1) dim1_10

let show = SrkUtil.mk_show (QQXs.pp (fun fo d -> Format.fprintf fo "x_%d" d))
  

let rel_test1 () =
  let transform1 = qqify [|[|1; 1; 0|];
                          [|1; 0; 0|];
                          [|0; 0; -1|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.zero; Polynomial.QQXs.zero|] in
  let init = [|Some (QQ.of_int 1); Some (QQ.of_int 0); Some (QQ.of_int 1)|] in
  let blk : block = {blk_transform = transform1; blk_add = add1} in
  let eps = RatEP.solve_rec ~initial:(Some init) [blk] in
  let module EP = (val RatEP.to_nf eps) in
  let relations = EP.algebraic_relations () in
  (*let nf_eps = EP.get_rec_sols () in
  Array.iteri (fun dim ep ->
    Log.logf ~level:`always "Dim %d : %a" dim EP.pp ep) nf_eps;
  Log.logf  ~level:`always "z is a root of %a" Polynomial.QQX.pp EP.NF.int_poly;
  Log.log ~level:`always "Relations";
  let v_printer fo d =
    if d < Array.length eps then Format.fprintf fo "x_%d" d
    else if d < 2 * (Array.length eps) then Format.fprintf fo "x'_%d" (d - Array.length eps)
    else Format.pp_print_string fo "K"
  in
  List.iter (fun p ->
    Log.logf ~level:`always "%a" (Polynomial.QQXs.pp v_printer) p
    ) relations;*)
  let first_10 = enumerate_sp ~initial:(Some init) [blk] 9 in
  let check_relation r = 
    let rel = List.init 10 (
      fun i ->
        QQXs.substitute (
          fun j -> 
            if j < (Array.length eps) then QQXs.of_dim j
            else 
              List.nth first_10.(j-(Array.length eps)) i
        ) r
    ) in
    assert_equal_seq (List.init 10 (fun _ -> QQXs.zero)) rel
  in
  List.iter (fun p ->
    check_relation p
    ) relations


let rel_test2 () =
  let transform1 = qqify [|[|3; 0|];
                          [|2; 0|]|] in
  let add1 = [|Polynomial.QQXs.zero; Polynomial.QQXs.one|] in
  let blk : block = {blk_transform = transform1; blk_add = add1} in
  let eps = RatEP.solve_rec [blk] in
  let module EP = (val RatEP.to_nf eps) in
  let _, _, relations = EP.long_run_algebraic_relations () in
  (*let nf_eps = EP.get_rec_sols () in
  Array.iteri (fun dim ep ->
    Log.logf ~level:`always "Dim %d : %a" dim EP.pp ep) nf_eps;
  Log.logf  ~level:`always "z is a root of %a" Polynomial.QQX.pp EP.NF.int_poly;
  Log.log ~level:`always "Relations";
  let v_printer fo d =
    if d < Array.length eps then Format.fprintf fo "x_%d" d
    else if d < 2 * (Array.length eps) then Format.fprintf fo "x'_%d" (d - Array.length eps)
    else Format.pp_print_string fo "K"
  in
  List.iter (fun p ->
    Log.logf ~level:`always "%a" (Polynomial.QQXs.pp v_printer) p
    ) relations;*)
  let first_10 = enumerate_sp [blk] 9 in
  let check_relation r = 
    let rel = List.init 9 (
      fun i ->
        QQXs.substitute (
          fun j -> 
            if j < (Array.length eps) then QQXs.of_dim j
            else 
              List.nth first_10.(j-(Array.length eps)) (i + 1)
        ) r
    ) in
    assert_equal_seq (List.init 9 (fun _ -> QQXs.zero)) rel
  in
  List.iter (fun p ->
    check_relation p
    ) relations


let suite = "Rational" >:::
  [
    "mat_rec_test1" >:: mat_rec_test1;
    "mat_rec_test2" >:: mat_rec_test2;
    "sp_test1" >:: sp_test1;
    (*"iif_test1" >:: iif_test1;*)
    "zero_eigen_test" >:: zero_eigen_test;
    "nf_test1" >:: nf_test1;
    "rel_test1" >:: rel_test1;
    "rel_test2" >:: rel_test2
  ]