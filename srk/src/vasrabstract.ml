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
type vasr_var_id = int * int
type coherent_linear_map = (matrix * int) list
type vasr = (vasr_transform list) M.t

let abstract_single_tf context symbol_pairs f : coherent_linear_map * vasr_transform = 
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

(* Given coherent linear maps f,g computes function compostion f g *)
let sep_comp (f : coherent_linear_map) (g: coherent_linear_map) : coherent_linear_map = 
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
    let basis_vec = V.of_term (Mpqf.of_int 1) i in 
    let output = Q.vector_right_mul mat basis_vec in 
    let local_max_out = V.fold (fun i _ local_max_out -> 
      if (i + 1) > local_max_out 
        then i + 1 
        else local_max_out)
    output 0 in 
    if local_max_out > max_out then local_max_out else max_out
    ) 0 (List.init in_dim (fun v -> v))
  
(* Given coherent linear maps f,g returns a, b  such that af = gb meeting the universality property of pushouts*)
let sep_pushout (f: coherent_linear_map) (g : coherent_linear_map) : (coherent_linear_map * coherent_linear_map) = 
  let a, b = [], [] in 
  let f = List.mapi (fun i e -> (i, e)) f in 
  let g = List.mapi (fun i e -> (i, e)) g in 
  List.fold_left (fun (a, b) (fi, (((f_proj_in, f_proj_out), f_proj), f_wit)) ->
    List.fold_left (fun (a, b) (gi, (((g_proj_in, g_proj_out), g_proj), g_wit)) ->
      assert (f_proj_in = g_proj_in);
      if (f_wit != g_wit) then (a, b) else (
        let c, d = L.pushout f_proj g_proj in 
        (((f_proj_out, (mat_out c f_proj_out)), c), fi) :: a, 
        (((g_proj_out, (mat_out d g_proj_out)), d), gi) :: b
        )
      ) (a, b) g
    ) (a, b) f

let genVASR context symbol_pairs tf : coherent_linear_map * vasr = 
  let tf_list = M.fold (fun e tf_e acc -> (e, tf_e) :: acc) tf [] in 
  let individual_reflections = List.map (fun (e, tf_e) -> (e, abstract_single_tf context symbol_pairs tf_e)) tf_list in 
  let possible_initial_dim = List.length symbol_pairs + 1 in 
  let id_triv = [((possible_initial_dim, possible_initial_dim), 
    Q.identity (List.init (possible_initial_dim) (fun v -> v))), 0] in 
  let (ab, _) = List.fold_left (fun (ab, curr) (_, (f, _)) -> 
    let a_i, b_i = sep_pushout curr f in 
    ((a_i, b_i)::ab, sep_comp a_i curr)) 
    ([], id_triv) individual_reflections in   

  let individual_reflections = (List.rev individual_reflections) in 
  let id_out = List.mapi (fun i _ -> (
    (possible_initial_dim, possible_initial_dim), 
    Q.identity (List.init (possible_initial_dim) (fun v -> v))), i)
    (snd (List.hd ab)) in 
  let (vasr_refl_list, _) = List.fold_left2 (fun (vasr_refl, r) (edge, (_, v)) (a_i, b_i) -> 
      let v = sep_image_vasr (sep_comp r b_i) v in 
      ((edge, v) :: vasr_refl, sep_comp a_i r)
    ) ([], id_out) individual_reflections ab in
  let simulation = sep_comp (snd (List.hd ab)) (fst (snd (List.hd individual_reflections))) in 
  let vasr_refl = List.fold_left (fun vasr_refl (edge, v_tr) -> M.add edge [v_tr] vasr_refl) 
    M.empty vasr_refl_list in 
  simulation, vasr_refl


let dim (vasr : vasr) = M.find_first (fun _ -> true) vasr  
      |> snd |> List.hd |> List.fold_left (fun sum ((v_dim,_), _) -> sum + v_dim) 0

let resets_and_offsets (vasr : vasr) edge (class_index, var_index: vasr_var_id) = 
  let vasr_transforms = M.find edge vasr in 
  List.mapi (fun supp_index vasr_transform -> 
    let class_tf = List.nth vasr_transform class_index in
    supp_index, fst class_tf |> snd |> V.coeff var_index, snd class_tf)
  vasr_transforms

let adds_after context supp_var_map (vasr : vasr) (vasr_var_id : vasr_var_id) j = 
  M.fold (fun edge _ ls -> 
      let resets_and_offsets = resets_and_offsets vasr edge vasr_var_id in 
      List.filter_map (fun (supp_index, offset, reset) -> 
        if not reset
         then let at_vars = List.init ((2 * (dim vasr) + 1) - (j))
            (fun i -> supp_var_map (supp_index, (i + j + 1), (fst edge), (snd edge))) 
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

let final_reset context supp_var_map (vasr : vasr) (vasr_var_id : vasr_var_id) j  = 
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
        then Some (List.init ((2 * (dim vasr) + 1) - (j)) 
          (fun i -> mk_eq context (mk_zero context) (supp_var_map (supp_index, (i + j + 1), (fst edge), (snd edge))))) 
        else None) 
      (resets_and_offsets vasr edge vasr_var_id) 
      |> List.flatten) :: ls
    ) vasr [] |> List.flatten |> mk_and context in 
  mk_and context [reset_at_j; never_reset_after]

let never_reset context supp_var_map (vasr : vasr) (vasr_var_id : vasr_var_id) = 
  M.fold (fun edge _ ls -> 
    (List.filter_map (fun (supp_index, _, reset) -> 
      if reset
        then Some (List.init (2 * (dim vasr) + 1) 
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

let transition context symbol_pairs supp_var_map (vasr : vasr) (simulation : coherent_linear_map) = 
  let example_tf = M.find_first (fun _ -> true) vasr |> snd |> List.hd in 
  List.mapi (fun class_id ((c_dim, _), _) -> 
    List.map (fun var_id ->
        let vasr_var_id = (class_id, var_id) in 
        let y', y = vasr_var_to_term context symbol_pairs simulation vasr_var_id in 
        let unreset_case = mk_and context 
            [never_reset context supp_var_map vasr vasr_var_id; 
              mk_eq context y' (mk_add context [y; adds_after context supp_var_map vasr vasr_var_id 0])]
        in
        let reset_case = List.map (fun j -> 
          mk_and context [  
          final_reset context supp_var_map vasr vasr_var_id (2 * j);
          mk_eq context y' (mk_add context [get_reset context supp_var_map vasr vasr_var_id (2*j);
            adds_after context supp_var_map vasr vasr_var_id (2 * j)])]
          ) (List.init (dim vasr) (fun v -> v + 1)) in  
        mk_or context (unreset_case :: reset_case)
      ) (List.init c_dim (fun v -> v))
  ) example_tf
  |> List.flatten 
  |> mk_and context 

let well_formed context supp_var_map (vasr : vasr) = 
  let example_tf = M.find_first (fun _ -> true) vasr |> snd |> List.hd in
  List.mapi (fun class_id ((v_dim, _), _) ->
    List.map (fun var_id ->
      let vasr_var_id = (class_id, var_id) in 
      mk_or context ((never_reset context supp_var_map vasr vasr_var_id) :: 
        List.map (fun j -> final_reset context supp_var_map vasr vasr_var_id (2 * j)) (List.init (dim vasr) (fun v -> v + 1))
        )
      ) (List.init v_dim (fun v -> v))
    ) example_tf
  |> List.flatten
  |> mk_and context

let get_supp_var_map context vasr varmap edge_list = 
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
      ) (supp_var_map, constraints) (List.init (2 * dim vasr + 1) (fun v -> v + 1))) 
      (M4.empty, []) edge_list in 
  (fun quad -> M4.find quad supp_var_map), 
  mk_and context constraints
  