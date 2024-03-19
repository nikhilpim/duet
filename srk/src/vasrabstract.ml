open Syntax 
module L = Linear
module Q = L.QQMatrix
module V = L.QQVector
module A = Abstract 
module IntPair = SrkUtil.IntPair
module IntTriple = SrkUtil.IntTriple
module M = BatMap.Make(IntPair)
module M4 = BatMap.Make(SrkUtil.IntQuad)

type vector = int * V.t
type matrix = (int * int) * Q.t
type vasr_transform = (vector * bool) list 
type lvasr_transform = (vector * bool) list
type vasr_var_id = int * int
type coherent_linear_map = (matrix * int) list
type vasr = (vasr_transform list) M.t
type lvasr = (lvasr_transform list) M.t

let pp_vasr (fmt : Format.formatter) (vasr: vasr) = 
  SrkUtil.pp_print_enum (fun fmt (edge, vasr_transform_ls) -> 
    Format.fprintf fmt "%s : " (IntPair.show edge);
    SrkUtil.pp_print_list (fun fmt vasr_transform -> 
      SrkUtil.pp_print_list (fun fmt ((vec_size, vec), b) ->
        Format.fprintf fmt " %d " vec_size;
        V.pp fmt vec; Format.fprintf fmt "  %s" (if b then "RES" else "INC")
      ) fmt vasr_transform 
      ) fmt vasr_transform_ls
    ) fmt (M.enum vasr)

  let pp_clm (fmt : Format.formatter) (f : coherent_linear_map) = 
    SrkUtil.pp_print_list (fun fmt (((i, o), matrix), witness) ->
      Format.fprintf fmt "(%d, %d) " i o;
      Q.pp fmt matrix;
      Format.fprintf fmt " : %d" witness
      ) fmt f

let abstract_single_vasr context symbol_pairs f : coherent_linear_map * vasr_transform = 
  let addition_basis = (mk_one context) :: 
    List.map 
      (fun (pre, post) -> mk_sub context (mk_const context pre) (mk_const context post)) 
      symbol_pairs 
    |> Array.of_list in 
  let add_f = A.vanishing_space context f addition_basis in 
  let mat_to_adds = (List.length symbol_pairs, List.length add_f), 
      Q.col_slice 1 ((List.length symbol_pairs) + 1) (Q.of_rows add_f) in 
  let add_tf = ((List.length add_f, 
    V.of_list (List.mapi (fun i vec -> (V.coeff 0 vec, i)) add_f)), false) in 

  let reset_basis = (mk_one context) :: 
    List.map (fun (_, post) -> mk_neg context (mk_const context post)) symbol_pairs 
    |> Array.of_list in 
  let res_f = A.vanishing_space context f reset_basis in 
  let mat_to_ress = (List.length symbol_pairs, List.length res_f),
     Q.col_slice 1 ((List.length symbol_pairs) + 1) (Q.of_rows res_f) in 
  let res_tf = ((List.length res_f, V.of_list (List.mapi (fun i vec -> (V.coeff 0 vec, i)) res_f)), true) in 
  [(mat_to_adds, 0); (mat_to_ress, 0)], [add_tf; res_tf]

let abstract_single_lvasr context symbol_pairs f : coherent_linear_map * lvasr_transform = 
  let addition_basis = (mk_one context) :: 
    List.map 
      (fun (pre, post) -> mk_sub context (mk_const context pre) (mk_const context post)) 
      symbol_pairs in 
  let reset_basis = (mk_one context) :: 
    List.map (fun (_, post) -> mk_neg context (mk_const context post)) symbol_pairs in
  let dummy_symbols = List.mapi (fun i _ -> mk_symbol context ~name:((string_of_int i)^"D") `TyReal) addition_basis in 

  let adds_formula = List.fold_left2 (fun acc dummy term -> mk_eq context (mk_const context dummy) term :: acc) [f] dummy_symbols addition_basis |> mk_and context 
  |> Nonlinear.linearize context |> rewrite context ~down:(pos_rewriter context) in 
  let resets_formula = List.fold_left2 (fun acc dummy term -> mk_eq context (mk_const context dummy) term :: acc) [f] dummy_symbols reset_basis |> mk_and context |> Nonlinear.linearize context |> rewrite context ~down:(pos_rewriter context) in  
  print_string (SrkUtil.mk_show (Syntax.pp_expr_unnumbered context) adds_formula); print_string "\n\n";
  let adds = Abstract.conv_hull context adds_formula (Array.of_list (List.map (mk_const context) dummy_symbols)) |> Polyhedron.of_dd 
    |> Polyhedron.dual_cone (List.length dummy_symbols) |> Polyhedron.dd_of (List.length dummy_symbols) |> DD.enum_generators 
    |> BatEnum.fold (fun acc elem -> match fst elem with 
      | `Line -> (V.negate (snd elem)) :: snd elem :: acc
      | `Ray -> if (V.is_zero (V.slice 1 (List.length addition_basis) (snd elem))) then acc else snd elem :: acc
      | `Vertex -> (assert (V.is_zero (snd elem))); acc (*This space should be a convex cone.*)
    ) [] in 
  let resets = Abstract.conv_hull context resets_formula (Array.of_list (List.map (mk_const context) dummy_symbols)) |> Polyhedron.of_dd
    |> Polyhedron.dual_cone (List.length dummy_symbols) |> Polyhedron.dd_of (List.length dummy_symbols) |> DD.enum_generators
    |> BatEnum.fold (fun acc elem -> match fst elem with 
      | `Line -> (V.negate (snd elem)) :: snd elem :: acc
      | `Ray -> if (V.is_zero (V.slice 1 (List.length reset_basis) (snd elem))) then acc else snd elem :: acc
      | `Vertex -> (assert (V.is_zero (snd elem))); acc (*This space should be a convex cone.*)
    ) [] in 

  let mat_to_adds = (List.length symbol_pairs, List.length adds), 
    Q.col_slice 1 ((List.length symbol_pairs) + 1) (Q.of_rows adds) in 
  let mat_to_ress = (List.length symbol_pairs, List.length resets),
     Q.col_slice 1 ((List.length symbol_pairs) + 1) (Q.of_rows resets) in 

  let add_class = ((List.length adds, 
     V.of_list (List.mapi (fun i vec -> (V.coeff 0 vec, i)) adds)), false) in 
  let reset_class = ((List.length resets,
     V.of_list (List.mapi (fun i vec -> (V.coeff 0 vec, i)) resets)), true) in 
  [mat_to_adds, 0; mat_to_ress, 0], [add_class; reset_class]

(* Given coherent linear maps f,g computes function compostion f g *)
let sep_comp (f : coherent_linear_map) (g: coherent_linear_map) : coherent_linear_map = 
        print_string "\n\n"; print_string (SrkUtil.mk_show pp_clm f); print_string "\n"; print_string (SrkUtil.mk_show pp_clm g); 
  List.map (fun (((f_proj_in, f_proj_out), f_proj), f_wit) ->
    let (((g_proj_in, g_proj_out), g_proj), g_wit) = List.nth g f_wit in 
    assert (g_proj_out = f_proj_in);
    (((g_proj_in, f_proj_out), Q.mul f_proj g_proj), g_wit)
    ) f

(* Given a coherent linear map f and a vasr transformation V, computes the image of v under f *)
let sep_image_vasr (f : coherent_linear_map) (v : vasr_transform) : vasr_transform = 
  List.map (fun (((f_proj_in, f_proj_out), f_proj), f_wit) ->
    let ((v_dim, offset), reset) = List.nth v f_wit in 
    assert (v_dim = f_proj_in);
    ((f_proj_out, Q.vector_right_mul f_proj offset), reset)
    ) f
let mat_out mat in_dim = 
  List.fold_left (fun max_out i -> 
    let basis_vec = V.of_term (QQ.of_int 1) i in 
    let output = Q.vector_right_mul mat basis_vec in 
    let local_max_out = V.fold (fun i _ local_max_out -> 
      if (i + 1) > local_max_out 
        then i + 1 
        else local_max_out)
    output 0 in 
    if local_max_out > max_out then local_max_out else max_out
    ) 0 (List.init in_dim (fun v -> v))
  
  let pushout_ord (a: Q.t) (b: Q.t) : Q.t * Q.t =
    let acollen = (BatEnum.fold (fun acc (_, v) -> V.fold (fun i _ acc -> i :: acc) v acc) [] (Q.rowsi (Q.transpose a)) 
      |> List.fold_left (fun acc e -> if e > acc then e else acc) 0 ) + 1 in 
    let bcollen = (BatEnum.fold (fun acc (_, v) -> V.fold (fun i _ acc -> i :: acc) v acc) [] (Q.rowsi (Q.transpose b)) 
      |> List.fold_left (fun acc e -> if e > acc then e else acc) 0) + 1 in 
    let combine va vb = V.add va (V.of_enum (BatEnum.map (fun (v, i) -> (QQ.negate v, i + acollen)) (V.enum vb))) in 
    let rec helper acols bcols = match (acols, bcols) with
      | [], [] -> []
      | (_, av) :: atl , [] -> combine av V.zero :: helper atl bcols
      | [], (_, bv) :: btl -> combine V.zero bv :: helper acols btl
      | (i, av) :: atl, (j, bv) :: btl -> 
          if (i = j) then ( combine av bv :: helper atl btl)
          else if (i < j) then combine av V.zero :: helper atl bcols 
          else combine V.zero bv :: helper acols btl in
    let constr = helper (List.rev (BatEnum.fold (fun acc e -> e :: acc) [] (Q.rowsi (Q.transpose a)))) (List.rev (BatEnum.fold (fun acc e -> e :: acc) [] (Q.rowsi (Q.transpose b)))) in 
    let constr = List.map (fun i -> `Nonneg, (V.add_term (QQ.of_int 1) i V.zero)) (List.init (acollen + bcollen) (fun v -> v))
      @  List.map (fun v -> `Zero, v) constr in  
    let constr_enum = BatEnum.map (fun i -> List.nth constr i) (BatEnum.range 0 ~until:(List.length constr-1)) in 
    let poly = Polyhedron.of_constraints constr_enum in 

    let split vab = V.fold (fun i v (c, d) -> if i < acollen then (V.add_term v i c, d) else (c, V.add_term v (i - acollen) d)) vab (V.zero, V.zero) in 

    let rows = BatEnum.fold (fun acc elem -> match fst elem with 
          | `Ray -> let (c, _) = split (snd elem) in if (V.is_zero (Q.vector_left_mul c a)) then acc else snd elem :: acc
          | `Line -> (assert false) (* it should not be possible to have a line *)
          | `Vertex -> assert (V.is_zero (snd elem)); acc
      ) [] (DD.enum_generators (Polyhedron.dd_of (acollen + bcollen) poly)) in
    let c, d = List.map split rows |> List.split in 

    let rec prune (before_c, before_d) (after_c, after_d) = 
      match after_c, after_d with 
      | [], [] -> before_c, before_d 
      | curr_c :: rest_c, curr_d :: rest_d -> (
        let c_enum = BatEnum.singleton (`Vertex, V.zero) in 
        List.iter (fun c_v -> BatEnum.push c_enum (`Ray, c_v)) (before_c @ rest_c);
        let c_cone = DD.of_generators acollen c_enum |> Polyhedron.of_dd in 

        let d_enum = BatEnum.singleton (`Vertex, V.zero) in 
        List.iter (fun d_v -> BatEnum.push d_enum (`Ray, d_v)) (before_d @ rest_d);
        let d_cone = DD.of_generators bcollen d_enum |> Polyhedron.of_dd in 
        
        if Polyhedron.mem (fun i -> V.coeff i curr_c) c_cone && Polyhedron.mem (fun i -> V.coeff i curr_d) d_cone 
        then prune (before_c, before_d) (rest_c, rest_d)
        else prune (curr_c :: before_c, curr_d :: before_d) (rest_c, rest_d)
      )
      | _, _ -> (assert false)
    in
    
    let c, d = prune ([], []) (c, d) in
    let c, d = L.QQVectorSpace.matrix_of c, L.QQVectorSpace.matrix_of d in 
    (assert (Q.equal (Q.mul c a) (Q.mul d b) ));
    c, d


(* Given coherent linear maps f,g returns a, b  such that af = gb meeting the universality property of pushouts*)
  let sep_pushout ~is_lossy (f: coherent_linear_map) (g : coherent_linear_map) : (coherent_linear_map * coherent_linear_map) = 
    let pushout = if is_lossy then pushout_ord else L.pushout in 
    let a, b = [], [] in 
    let f = List.mapi (fun i e -> (i, e)) f in 
    let g = List.mapi (fun i e -> (i, e)) g in 
    List.fold_left (fun (a, b) (fi, (((f_proj_in, f_proj_out), f_proj), f_wit)) ->
      List.fold_left (fun (a, b) (gi, (((g_proj_in, g_proj_out), g_proj), g_wit)) ->
        assert (f_proj_in = g_proj_in);
        if (f_wit != g_wit) then (a, b) else (
          let c, d = pushout f_proj g_proj in 
          assert ((mat_out c f_proj_out) = (mat_out d g_proj_out)); 
          (* print_string "\n\n new pushout. f: "; print_int f_proj_in; print_string " "; print_int f_proj_out; print_string " g: ";
          print_int g_proj_in; print_string " "; print_int g_proj_out; print_string " "; print_int (mat_out c f_proj_out); print_string "\n"; *)
          (* print_string (SrkUtil.mk_show Q.pp f_proj); print_string (SrkUtil.mk_show Q.pp g_proj);
          print_string (SrkUtil.mk_show Q.pp c); print_string (SrkUtil.mk_show Q.pp d); *)
          let out = max (mat_out c f_proj_out) (mat_out d g_proj_out) in 
          (((f_proj_out, out), c), fi) :: a, 
          (((g_proj_out, out), d), gi) :: b
          )
        ) (a, b) g
        ) (a, b) f

  let prune_pushout (lvasr : lvasr_transform) simulation pushout = 
    let module VM = BatMap.Make(V) in 
    let comp_sim = sep_comp pushout simulation in 
    let rows_to_use = List.fold_left2 (fun acc (mat, _) (vec, _) -> 
      let tightest = BatEnum.fold (fun map (ind, v) -> 
          if not (VM.mem v map) || V.coeff (VM.find v map) (snd vec) > V.coeff ind (snd vec) 
            then VM.add v ind map
            else map
        ) VM.empty (Q.rowsi (snd mat)) in
      let rows_to_use = VM.to_seq tightest |> BatSeq.enum 
        |> BatEnum.fold (fun ls (_row, index) -> index :: ls) [] in 
      rows_to_use :: acc
      ) [] comp_sim (sep_image_vasr pushout lvasr) |> List.rev in 
    List.map2 (fun (mat, wit) row_indices -> 
       let rows' = List.map (fun index -> Q.row index (snd mat)) row_indices in
       (((List.length rows'), snd (fst mat)), Q.of_rows rows'), wit 
    ) pushout rows_to_use


let genVASRLossy context symbol_pairs tf : coherent_linear_map * lvasr = 
    let tf_list = M.fold (fun e tf_e acc -> (e, tf_e) :: acc) tf [] in 
    let individual_reflections = List.map (fun (e, tf_e) -> (e, abstract_single_lvasr context symbol_pairs tf_e)) tf_list in
    let curr_sim = List.hd individual_reflections |> snd |> fst in 
    if (List.length individual_reflections == 1) then (curr_sim, M.singleton (List.hd individual_reflections |> fst) [List.hd individual_reflections |> snd |> snd]) else (
    let tracking = [(List.hd individual_reflections |> fst), (List.hd individual_reflections |> snd |> snd)] in 
    let simulation, reflection = List.fold_left (fun (curr_sim, tracking) (edge, (indiv_sim, lvasr_tf)) ->
       let a_i, b_i = (sep_pushout ~is_lossy:true) curr_sim indiv_sim in 
       let pruned_b_i = prune_pushout lvasr_tf indiv_sim b_i in 
       let curr_sim' = sep_comp pruned_b_i indiv_sim in 
       let lvasr_tf' = sep_image_vasr pruned_b_i lvasr_tf in 
       let tracking' = List.map (fun (edge, tracking_tf) -> 
         let pruned_a_i = prune_pushout tracking_tf curr_sim a_i in 
         (edge, sep_image_vasr pruned_a_i tracking_tf)) tracking in 
       (curr_sim', (edge, lvasr_tf') :: tracking')
    ) (curr_sim, tracking) (List.tl individual_reflections) in 
    
    let vasr_refl = List.fold_left (fun vasr_refl (edge, v_tr) -> M.add edge [v_tr] vasr_refl) M.empty reflection in 

    let keep = List.map (fun (((_, output_dimension), mat), _) -> output_dimension != 0 && not (Q.equal Q.zero mat)) simulation in 
  let keep = M.fold (fun _ v_tf_ls keep -> 
    List.fold_left (fun keep v_tf -> 
        List.map2 (fun keep_var ((state_size, _), _) -> keep_var && state_size != 0) keep v_tf 
      ) keep v_tf_ls
    ) vasr_refl keep in 
  
  let (simulation) = List.filteri (fun i _ -> List.nth keep i) simulation in 
  let vasr_refl = M.map (fun v_tf_ls -> 
    List.map (fun v_tf -> 
      List.filteri (fun i _ -> List.nth keep i) v_tf) v_tf_ls
    ) vasr_refl in 
    simulation, vasr_refl

    )
 
let genVASR ~is_lossy context symbol_pairs tf : coherent_linear_map * vasr = 
  let abstract = if is_lossy then abstract_single_lvasr else abstract_single_vasr in 
  let tf_list = M.fold (fun e tf_e acc -> (e, tf_e) :: acc) tf [] in 
  let individual_reflections = List.map (fun (e, tf_e) -> (e, abstract context symbol_pairs tf_e)) tf_list in 
  (* print_string "\n\n\n BEGINNING \n\n";
  List.iter (fun (edge, (cm, vasr_ls)) -> print_string "\n\nEdge: "; print_string (IntPair.show edge); print_string "\n simulation: "; print_string (SrkUtil.mk_show pp_clm cm); print_string "\n LVASR"; print_string (SrkUtil.mk_show pp_vasr (M.add edge [vasr_ls] M.empty))) individual_reflections; *)
  
  let curr : coherent_linear_map = List.hd individual_reflections |> snd |> fst in
  if (List.length individual_reflections == 1) then (curr, M.singleton (List.hd individual_reflections |> fst) [List.hd individual_reflections |> snd |> snd]) else (

  let (ab, _) = List.fold_left (fun (ab, curr) (_, (f, _)) -> 
    let a_i, b_i = (sep_pushout ~is_lossy) curr f in 
    ((a_i, b_i)::ab, sep_comp a_i curr)) 
    ([], curr) (List.tl individual_reflections) in  
    
  let backwards_indiv_refl = (List.rev (List.tl individual_reflections)) in 
  let r = List.mapi (fun i (((_, a_out), _), _) -> 
      ((a_out, a_out), Q.identity (List.init a_out (fun v -> v))), i
    ) (fst (List.hd ab)) in 
  let (vasr_refl_list, r) = List.fold_left2 
      (fun (vasr_refl_list, r) (a, b) (edge, (_, vasr)) ->
        let vasr_reflection = sep_image_vasr (sep_comp r b) vasr in 
        let r = sep_comp r a in
        (edge, vasr_reflection) :: vasr_refl_list, r
    ) ([], r) ab backwards_indiv_refl in 
  let vasr_refl_list = (fst (List.hd individual_reflections), 
    sep_image_vasr r (List.hd individual_reflections |> snd |> snd)) 
  :: vasr_refl_list in 
  
  let simulation = sep_comp (snd (List.hd ab)) (fst (snd (List.hd backwards_indiv_refl))) in 
  let vasr_refl = List.fold_left (fun vasr_refl (edge, v_tr) -> M.add edge [v_tr] vasr_refl)
        M.empty vasr_refl_list in 
  
   (* Pruning 0 dimensional classes *)
  let keep = List.map (fun (((_, output_dimension), mat), _) -> output_dimension != 0 && not (Q.equal Q.zero mat)) simulation in 
  let keep = M.fold (fun _ v_tf_ls keep -> 
    List.fold_left (fun keep v_tf -> 
        List.map2 (fun keep_var ((state_size, _), _) -> keep_var && state_size != 0) keep v_tf 
      ) keep v_tf_ls
    ) vasr_refl keep in 
  
  let simulation = List.filteri (fun i _ -> List.nth keep i) simulation in 
  let vasr_refl = M.map (fun v_tf_ls -> 
    List.map (fun v_tf -> 
      List.filteri (fun i _ -> List.nth keep i) v_tf) v_tf_ls
    ) vasr_refl in 
  (* let simulation = List.filter (fun (((_, output_dimension), _), _) -> output_dimension != 0) simulation in 
  let vasr_refl = M.map (fun v_tf_ls ->
    List.map (fun v_tf -> 
        List.filter (fun ((state_size ,_), _) -> state_size != 0) v_tf
      ) v_tf_ls
    ) vasr_refl in  *)
        
  simulation, vasr_refl )



let dim (vasr : vasr) = M.find_first (fun _ -> true) vasr  
      |> snd |> List.hd |> List.fold_left (fun sum ((v_dim,_), _) -> sum + v_dim) 0

let classes (vasr : vasr) = M.find_first (fun _ -> true) vasr 
    |> snd |> List.hd |> List.length
let resetable_classes (vasr : vasr) = 
  let resetable = M.fold (fun _ v_tf_ls acc -> 
    List.fold_left (fun acc vasr_tf -> 
        List.map2 (fun b (_, is_reset) -> b || is_reset) acc vasr_tf
      ) acc v_tf_ls
    ) vasr (List.init (classes vasr) (fun _ -> false)) in 
  List.filter (fun b -> b) resetable |> List.length

let resets_and_offsets (vasr : vasr) edge (class_index, var_index: vasr_var_id) = 
  let vasr_transforms = M.find edge vasr in 
  List.mapi (fun supp_index vasr_transform -> 
    let class_tf = List.nth vasr_transform class_index in
    supp_index, (fst class_tf |> snd |> V.coeff var_index), snd class_tf)
  vasr_transforms

let adds_after context interval_param supp_var_map (vasr : vasr) (vasr_var_id : vasr_var_id) j = 
  M.fold (fun edge _ ls -> 
      let resets_and_offsets = resets_and_offsets vasr edge vasr_var_id in 
      List.filter_map (fun (supp_index, offset, reset) -> 
        if not reset
         then let at_vars = List.init ((2 * interval_param + 1) - (j - 1))
            (fun i -> supp_var_map (supp_index, (i + j), (fst edge), (snd edge))) 
            |> mk_add context in 
            Some (mk_mul context [mk_real context offset; at_vars])
          else None
        ) resets_and_offsets :: ls
    ) vasr [] |> List.flatten |> mk_add context

let get_reset context supp_var_map vasr vasr_var_id j = 
  M.fold (fun edge _ ls ->
    let resets_and_offsets = resets_and_offsets vasr edge vasr_var_id in 
    List.filter_map (fun (supp_index, offset, reset) ->
      if reset 
        then Some (mk_mul context [mk_real context offset; 
          supp_var_map (supp_index, (j), (fst edge), (snd edge))])
        else None
      ) resets_and_offsets :: ls
    ) vasr [] |> List.flatten |> mk_add context

let final_reset context interval_param supp_var_map (vasr : vasr) (vasr_var_id : vasr_var_id) j  = 
  let reset_at_j = M.fold (fun edge _ ls -> 
    List.filter_map (fun (supp_index, _, reset) ->
      if reset 
        then Some (mk_lt context (mk_zero context) (supp_var_map (supp_index, j, (fst edge), (snd edge)))) 
        else None
      ) (resets_and_offsets vasr edge vasr_var_id) :: ls
    ) vasr [] |> List.flatten |> mk_or context in 
  let never_reset_after = M.fold (fun edge _ ls -> 
    (List.filter_map (fun (supp_index, _, reset) ->
      if reset 
        then Some (List.init ((2 * interval_param + 1) - (j)) 
          (fun i -> mk_eq context (mk_zero context) (supp_var_map (supp_index, (i + j + 1), (fst edge), (snd edge))))) 
        else None) 
      (resets_and_offsets vasr edge vasr_var_id) 
      |> List.flatten) :: ls
    ) vasr [] |> List.flatten |> mk_and context in 
  mk_and context [reset_at_j; never_reset_after]

let never_reset context interval_param supp_var_map (vasr : vasr) (vasr_var_id : vasr_var_id) = 
  M.fold (fun edge _ ls -> 
    (List.filter_map (fun (supp_index, _, reset) -> 
      if reset
        then Some (List.init (2 * interval_param + 1) 
          (fun i -> mk_eq context (mk_zero context) (supp_var_map (supp_index, (i + 1), (fst edge), (snd edge)))))
        else None
      ) (resets_and_offsets vasr edge vasr_var_id) |> List.flatten)
    :: ls
    ) vasr [] |> List.flatten |> mk_and context 

let vasr_var_to_term context symbol_pairs (simulation : coherent_linear_map) (class_id, var_id : vasr_var_id) = 
  let ((_, simulation_proj), _) = List.nth simulation class_id in
  let row = Q.row var_id simulation_proj in
  let pre_term = V.fold (fun index value ls -> mk_mul context [mk_real context value; List.nth symbol_pairs index |> fst |> mk_const context] :: ls) row [] in
  let post_term = V.fold (fun index value ls -> mk_mul context [mk_real context value; List.nth symbol_pairs index |> snd |> mk_const context] :: ls) row [] in
  mk_add context pre_term, mk_add context post_term

let transition ~is_lossy context interval_param symbol_pairs supp_var_map (vasr : vasr) (simulation : coherent_linear_map) = 
  let op = if is_lossy then mk_leq context else mk_eq context in 
  let example_tf = M.find_first (fun _ -> true) vasr |> snd |> List.hd in 
  List.mapi (fun class_id ((c_dim, _), _) -> 
    List.map (fun var_id ->
        let vasr_var_id = (class_id, var_id) in 
        let y, y' = vasr_var_to_term context symbol_pairs simulation vasr_var_id in 
        let unreset_case = mk_and context 
            [never_reset context interval_param supp_var_map vasr vasr_var_id; 
              op y' (mk_add context [y; adds_after context interval_param supp_var_map vasr vasr_var_id 1])]
        in
        let reset_case = List.init interval_param (fun j -> 
          let even_index = (j + 1) * 2 in 
          mk_and context [  
          final_reset context interval_param supp_var_map vasr vasr_var_id even_index;
          op y' (mk_add context [get_reset context supp_var_map vasr vasr_var_id even_index;
            adds_after context interval_param supp_var_map vasr vasr_var_id (even_index + 1)])]
          ) in  
        mk_or context (unreset_case :: reset_case)
      ) (List.init c_dim (fun v -> v))
  ) example_tf
  |> List.flatten 
  |> mk_and context 

let well_formed context interval_param supp_var_map (vasr : vasr) = 
  let example_tf = M.find_first (fun _ -> true) vasr |> snd |> List.hd in
  List.mapi (fun class_id ((v_dim, _), _) ->
    List.init v_dim (fun var_id ->
      let vasr_var_id = (class_id, var_id) in 
      mk_or context ((never_reset context interval_param supp_var_map vasr vasr_var_id) :: 
        List.init interval_param (fun j -> final_reset context interval_param supp_var_map vasr vasr_var_id (2 * (j + 1))) 
        )
      )
    ) example_tf
  |> List.flatten
  |> mk_and context


(* Generates extra variables to handle multiple VASR transformations per edge. *)
let get_supp_var_map context interval_param vasr varmap edge_list = 
  let supp_var_map, constraints = List.fold_left (fun (supp_var_map, constraints) edge -> 
    List.fold_left (fun (supp_var_map, constraints) index -> 
        let general_variable = varmap (index, fst edge, snd edge) in
        let new_variables = List.mapi (fun supp_index _ -> 
          supp_index, mk_symbol context ~name:((IntPair.show edge)^(string_of_int index)^(string_of_int supp_index))
            `TyInt
            |> mk_const context 
          ) (M.find edge vasr) in
        let supp_var_map = List.fold_left (fun supp_var_map (supp_index, supp_var) ->
          M4.add (supp_index, index, fst edge, snd edge) supp_var supp_var_map 
          ) supp_var_map new_variables in 
        let constraints = mk_eq context (mk_add context (List.map snd new_variables)) (general_variable) :: 
            (List.map (fun (_, new_var) -> mk_leq context (mk_zero context) new_var) new_variables) @ constraints in 
        supp_var_map, constraints
      ) (supp_var_map, constraints) (List.init (2 * interval_param + 1) (fun v -> v + 1))) 
      (M4.empty, []) edge_list in 
  (fun quad -> M4.find quad supp_var_map), 
  mk_and context constraints
  
  
