(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;


let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        List.for_all2 expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (List.for_all2 expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false;;


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env = 
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe = 
    let rec run pe params env =
      match pe with
      | ScmConst x -> ScmConst' x
      | ScmVar x ->  
        (match (lookup_in_rib x params) with
        | Some index -> ScmVar'(VarParam(x, index))
        | None -> match (lookup_in_env x env) with
                  | Some(major, minor) -> ScmVar'(VarBound(x, major, minor))
                  | None -> ScmVar'(VarFree(x)))
      | ScmLambdaSimple(vars, body) -> ScmLambdaSimple'(vars, run body vars (params :: env))
      | ScmLambdaOpt(vars, var, body) -> ScmLambdaOpt'(vars, var, run body (vars @ [var]) (params :: env))
      | ScmIf(test, dit, dif) -> ScmIf'(run test params env, run dit params env, run dif params env)
      | ScmSeq(exprs) -> ScmSeq'(List.map (fun x -> run x params env) exprs)
      | ScmSet(variable, value) -> 
        (match (lookup_in_rib (string_of_expr variable) params) with
        | Some index -> ScmSet'(VarParam((string_of_expr variable), index), run value params env)
        | None -> match (lookup_in_env (string_of_expr variable) env) with
                  | Some(major, minor) -> ScmSet'(VarBound((string_of_expr variable), major, minor), run value params env)
                  | None -> ScmSet'(VarFree(string_of_expr variable), run value params env))
      | ScmOr(exprs) -> ScmOr'(List.map (fun x -> run x params env) exprs)
      | ScmApplic(func, exprs) -> ScmApplic'(run func params env, List.map (fun x -> run x params env) exprs)
      | ScmDef(variable, value) -> 
        (match (lookup_in_rib (string_of_expr variable) params) with
        | Some index -> ScmDef'(VarParam((string_of_expr variable), index), run value params env)
        | None -> match (lookup_in_env (string_of_expr variable) env) with
                  | Some(major, minor) -> ScmDef'(VarBound((string_of_expr variable), major, minor), run value params env)
                  | None -> ScmDef'(VarFree(string_of_expr variable), run value params env))
    in 
    run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
      let (rdc, rac) = rdc_rac s in 
      (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;
  
  let rec remove_last_elem = function
  | [] -> []
  | hd::[] -> []
  | hd::tl -> hd::(remove_last_elem tl)

  (* run this second! *)
  let annotate_tail_calls pe =
    let rec run pe in_tail =
      match pe with
      | ScmConst' x -> ScmConst' x
      | ScmVar' x -> ScmVar' x
      | ScmBox' x -> ScmBox' x
      | ScmBoxGet' x -> ScmBoxGet' x 
      | ScmBoxSet'(var, expr) -> ScmBoxSet'(var, expr)
      | ScmIf'(test, dit , dif) -> ScmIf'(run test false, run dit in_tail, run dif in_tail)
      | ScmSeq'(exprs) -> let no_last_elem = remove_last_elem exprs in
                          ScmSeq'((List.map (fun x -> run x false) no_last_elem) @ [run (List.nth exprs ((List.length exprs) - 1)) in_tail])
      | ScmSet'(var, expr) -> ScmSet'(var, run expr false)
      | ScmDef'(var, expr) -> ScmDef'(var, run expr false)
      | ScmOr'(exprs) -> let no_last_elem = remove_last_elem exprs in
                         ScmOr'((List.map (fun x -> run x false) no_last_elem) @ [run (List.nth exprs ((List.length exprs) - 1)) in_tail])
      | ScmLambdaSimple'(vars, expr) -> ScmLambdaSimple'(vars, run expr true)
      | ScmLambdaOpt'(vars, var, expr) -> ScmLambdaOpt'(vars, var, run expr true)
      | ScmApplic'(func, exprs) -> 
        if in_tail
          then
            ScmApplicTP'(run func false, List.map (fun x -> run x false) exprs)
          else
            ScmApplic'(run func false, List.map (fun x -> run x false) exprs)
      | ScmApplicTP'(func, exprs) -> ScmApplicTP'(func, exprs)
    in 
    run pe false;;

  (* boxing *)

  let rec find_reads_writes name body current_lambda_tree lambda_index all_reads_ref all_writes_ref =
    match body with
    | ScmConst' x -> ()
    | ScmVar'(VarFree(x)) -> ()
    | ScmVar'(VarParam(x, _)) when x = name -> (all_reads_ref := !all_reads_ref @ [current_lambda_tree])
    | ScmVar'(VarParam(x, _)) -> ()
    | ScmVar'(VarBound(x, _, _)) when x = name -> (all_reads_ref := !all_reads_ref @ [current_lambda_tree])
    | ScmVar'(VarBound(x, _, _)) -> ()
    | ScmBox' x -> ()
    | ScmBoxGet' x -> ()
    | ScmBoxSet'(var, expr) -> (find_reads_writes name expr current_lambda_tree lambda_index all_reads_ref all_writes_ref); ()
    | ScmIf'(test, dit , dif) -> (find_reads_writes name test current_lambda_tree lambda_index all_reads_ref all_writes_ref);
                                 (find_reads_writes name dit current_lambda_tree lambda_index all_reads_ref all_writes_ref);
                                 (find_reads_writes name dif current_lambda_tree lambda_index all_reads_ref all_writes_ref); ()
    | ScmSeq'(exprs) -> let _ = (List.map (fun x -> find_reads_writes name x current_lambda_tree lambda_index all_reads_ref all_writes_ref) exprs) in ()
    | ScmSet'(VarParam(x, _), expr) when x = name -> (all_writes_ref := !all_writes_ref @ [current_lambda_tree]);
                                                     (find_reads_writes name expr current_lambda_tree lambda_index all_reads_ref all_writes_ref); ()
    | ScmSet'(VarBound(x, _, _), expr) when x = name -> (all_writes_ref := !all_writes_ref @ [current_lambda_tree]);
                                                        (find_reads_writes name expr current_lambda_tree lambda_index all_reads_ref all_writes_ref); ()
    | ScmSet'(var, expr) -> (find_reads_writes name expr current_lambda_tree lambda_index all_reads_ref all_writes_ref); ()
    | ScmDef'(var, expr) -> (find_reads_writes name expr current_lambda_tree lambda_index all_reads_ref all_writes_ref); ()
    | ScmOr'(exprs) -> let _ = (List.map (fun x -> find_reads_writes name x current_lambda_tree lambda_index all_reads_ref all_writes_ref) exprs) in ()
    | ScmLambdaSimple'(vars, body_lambda) -> if (List.mem name vars)
                                        then ()
                                        else 
                                          let new_lambda_index : int ref = ref 0 in 
                                          (lambda_index := !lambda_index + 1);
                                          (find_reads_writes name body_lambda (current_lambda_tree @ [!lambda_index]) new_lambda_index all_reads_ref all_writes_ref); ()
    | ScmLambdaOpt'(vars, var, body_lambda) -> if (List.mem name (vars @ [var]))
                                          then ()
                                          else
                                            let new_lambda_index : int ref = ref 0 in
                                            (lambda_index := !lambda_index + 1);
                                            (find_reads_writes name body_lambda (current_lambda_tree @ [!lambda_index]) new_lambda_index all_reads_ref all_writes_ref); ()
    | ScmApplic'(func, exprs) -> (find_reads_writes name func current_lambda_tree lambda_index all_reads_ref all_writes_ref);
                                 let _ = (List.map (fun x -> find_reads_writes name x current_lambda_tree lambda_index all_reads_ref all_writes_ref) exprs) in ()
    | ScmApplicTP'(func, exprs) -> (find_reads_writes name func current_lambda_tree lambda_index all_reads_ref all_writes_ref);
                                   let _ = (List.map (fun x -> find_reads_writes name x current_lambda_tree lambda_index all_reads_ref all_writes_ref) exprs) in ()

  let rec check_prefix read_val write_val =
    match read_val, write_val with
    | [], _ -> false
    | _, [] -> false
    | [hd1], [hd2] when hd1 = hd2 -> false
    | [hd1], [hd2] when not (hd1 = hd2)  -> true
    | [hd1], hd2 :: tl2 when hd1 = hd2 && hd1 = 0 -> true
    | [hd1], hd2 :: tl2 when not (hd1 = hd2) -> true
    | [hd1], hd2 :: tl2 -> false
    | hd1 :: tl1, [hd2] when hd1 = hd2 && hd1 = 0 -> true
    | hd1 :: tl1, [hd2] when not (hd1 = hd2) -> true
    | hd1 :: tl1, [hd2] -> false
    | hd1 :: tl1, hd2 :: tl2 when hd1 = hd2 && hd1 = 0 -> check_prefix tl1 tl2
    | hd1 :: tl1, hd2 :: tl2 when not (hd1 = hd2) -> true
    | hd1 :: tl1, hd2 :: tl2 -> false

  let rec should_i_box reads writes =
    let mapped = List.map (fun read_val -> List.exists (fun write_val -> check_prefix read_val write_val) !writes) !reads in
    (List.fold_left (fun var init -> var || init) false mapped)

  let rec box_body name body =
    match body with
    | ScmConst' x -> ScmConst' x
    | ScmVar'(VarFree(x)) -> ScmVar'(VarFree(x))
    | ScmVar'(VarParam(x, index)) when x = name -> ScmBoxGet'(VarParam(x, index))
    | ScmVar'(VarParam(x, index)) -> ScmVar'(VarParam(x, index))
    | ScmVar'(VarBound(x, major, minor)) when x = name -> ScmBoxGet'(VarBound(x, major, minor))
    | ScmVar'(VarBound(x, major, minor)) -> ScmVar'(VarBound(x, major, minor))
    | ScmBox' x -> ScmBox' x
    | ScmBoxGet' x -> ScmBoxGet' x
    | ScmBoxSet'(var, expr) -> ScmBoxSet'(var, box_body name expr)
    | ScmIf'(test, dit , dif) -> ScmIf'(box_body name test, box_body name dit , box_body name dif)
    | ScmSeq'(exprs) -> ScmSeq'(List.map (fun x -> box_body name x) exprs)
    | ScmSet'(VarParam(x, index), expr) when x = name -> ScmBoxSet'(VarParam(x, index), box_body name expr)
    | ScmSet'(VarBound(x, major, minor), expr) when x = name -> ScmBoxSet'(VarBound(x, major, minor), box_body name expr)
    | ScmSet'(var, expr) -> ScmSet'(var, box_body name expr)
    | ScmDef'(var, expr) -> ScmDef'(var, box_body name expr)
    | ScmOr'(exprs) -> ScmOr'(List.map (fun x -> box_body name x) exprs)
    | ScmLambdaSimple'(vars, body_lambda) -> if (List.mem name vars)
                                        then ScmLambdaSimple'(vars, body_lambda)
                                        else 
                                          ScmLambdaSimple'(vars, box_body name body_lambda)
    | ScmLambdaOpt'(vars, var, body_lambda) -> if (List.mem name (vars @ [var]))
                                          then ScmLambdaOpt'(vars, var, body_lambda)
                                        else 
                                          ScmLambdaOpt'(vars, var, box_body name body_lambda)
    | ScmApplic'(func, exprs) -> ScmApplic'(box_body name func, List.map (fun x -> box_body name x) exprs)
    | ScmApplicTP'(func, exprs) -> ScmApplicTP'(box_body name func, List.map (fun x -> box_body name x) exprs)

  let reset reads writes lambda_index =
    reads := [];
    writes := [];
    lambda_index := 0

  let add_to_beginning_of_lambda param body =
    match body with
    | ScmSeq'(exprs) -> ScmSeq'((ScmSet'(param, ScmBox'(param))) :: exprs)
    | other -> ScmSeq'([(ScmSet'(param, ScmBox'(param))); other])
  
  let rec return_boxed_body params body = 
    let reads : int list list ref = ref [] in
    let writes : int list list ref = ref [] in
    let lambda_index : int ref = ref 0 in
    let new_body : expr' ref = ref body in
    let index_in_params : int ref = ref ((List.length params) - 1) in
    let reversed_params = List.rev params in

    let _ = (List.map (fun param -> (reset reads writes lambda_index);
                                    (find_reads_writes param !new_body [0] lambda_index reads writes);
                                    if (should_i_box reads writes)
                                      then
                                        (new_body := box_body param !new_body;
                                        new_body := add_to_beginning_of_lambda (VarParam(param, !index_in_params)) !new_body;
                                        index_in_params := !index_in_params - 1;
                                        ())
                                      else 
                                        (index_in_params := !index_in_params - 1; 
                                        ()))
                      reversed_params) in

    !new_body

  let rec box_set expr = 
    match expr with
    | ScmConst' x -> ScmConst' x
    | ScmVar' x -> ScmVar' x
    | ScmBox' x -> ScmBox' x
    | ScmBoxGet' x -> ScmBoxGet' x 
    | ScmBoxSet'(var, expr) -> ScmBoxSet'(var, expr)
    | ScmIf'(test, dit , dif) -> ScmIf'(box_set test, box_set dit, box_set dif)
    | ScmSeq'(exprs) -> ScmSeq'(List.map (fun x -> box_set x) exprs)
    | ScmSet'(var, expr) -> ScmSet'(var, box_set expr)
    | ScmDef'(var, expr) -> ScmDef'(var, box_set expr)
    | ScmOr'(exprs) -> ScmOr'(List.map (fun x -> box_set x) exprs)
    | ScmLambdaSimple'(vars, body) -> ScmLambdaSimple'(vars, return_boxed_body vars (box_set body))
    | ScmLambdaOpt'(vars, var, body) -> ScmLambdaOpt'(vars, var, return_boxed_body (vars @ [var]) (box_set body))
    | ScmApplic'(func, exprs) -> ScmApplic'(box_set func, List.map (fun x -> box_set x) exprs)
    | ScmApplicTP'(func, exprs) -> ScmApplicTP'(box_set func, List.map (fun x -> box_set x) exprs)

  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
