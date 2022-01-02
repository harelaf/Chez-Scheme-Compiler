#use "semantic-analyser.ml";;

exception X_this_shouldnt_happen;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with 
  | (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
  | ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
  | ScmChar(char1), ScmChar(char2) -> char1 = char2
  | ScmString(string1), ScmString(string2) -> String.equal string1 string2
  | ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
  | ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
  | ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
  | ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _, _ -> false

let unannotate_lexical_address = function
| (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name

let rec unanalyze expr' =
match expr' with
  | ScmConst' s -> ScmConst(s)
  | ScmVar' var -> unannotate_lexical_address var
  | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
  | ScmBoxGet' var -> unannotate_lexical_address var
  | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
  | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
  | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
  | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
  | ScmLambdaSimple' (params, expr') ->
        ScmLambdaSimple (params, unanalyze expr')
  | ScmLambdaOpt'(params, param, expr') ->
        ScmLambdaOpt (params, param, unanalyze expr')
  | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
        ScmApplic (unanalyze expr', List.map unanalyze expr's);;

let string_of_expr' expr' =
    string_of_expr (unanalyze expr');;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

  (* CONSTANTS *)

  let rec find_all_consts expr lst =
    match expr with
    | ScmConst' x -> lst @ [x]
    | ScmVar' x -> lst
    | ScmBox' x -> lst
    | ScmBoxGet' x -> lst
    | ScmBoxSet'(var, exp) -> 
      let exp_lst = find_all_consts exp [] in
      lst @ exp_lst
    | ScmIf'(test, dit, dif) ->
      let test_lst = find_all_consts test [] in
      let dit_lst = find_all_consts dit [] in
      let dif_lst = find_all_consts dif [] in
      ((lst @ test_lst) @ dit_lst) @ dif_lst 
    | ScmSeq'(exprs) ->
      let mapped = List.map (fun x -> find_all_consts x []) exprs in
      List.fold_left (fun init next -> init @ next) lst mapped
    | ScmSet'(var, exp) ->
      let exp_lst = find_all_consts exp [] in
      lst @ exp_lst
    | ScmDef'(var, exp) ->
      let exp_lst = find_all_consts exp [] in
      lst @ exp_lst
    | ScmOr'(exprs) ->
      let mapped = List.map (fun x -> find_all_consts x []) exprs in
      List.fold_left (fun init next -> init @ next) lst mapped
    | ScmLambdaSimple'(params, exp) ->
      let exp_lst = find_all_consts exp [] in
      lst @ exp_lst
    | ScmLambdaOpt'(params, param, exp) ->
      let exp_lst = find_all_consts exp [] in
      lst @ exp_lst
    | ScmApplic'(exp, exprs) ->
      let exp_lst = find_all_consts exp [] in
      let mapped = List.map (fun x -> find_all_consts x []) exprs in
      List.fold_left (fun init next -> init @ next) (lst @ exp_lst) mapped
    | ScmApplicTP'(exp, exprs) ->
      let exp_lst = find_all_consts exp [] in
      let mapped = List.map (fun x -> find_all_consts x []) exprs in
      List.fold_left (fun init next -> init @ next) (lst @ exp_lst) mapped

  let rec extend_consts const = 
    match const with
    | ScmVoid -> [ScmVoid]
    | ScmNil -> [ScmNil]
    | ScmBoolean x -> [ScmBoolean x]
    | ScmChar x -> [ScmChar x]
    | ScmString x -> [ScmString x]
    | ScmNumber x -> [ScmNumber x]
    | ScmSymbol(x) -> [ScmString(x); ScmSymbol(x)]
    | ScmPair(car, cdr) -> 
      let extended_car = extend_consts car in
      let extended_cdr = extend_consts cdr in
      (extended_car @ extended_cdr) @ [ScmPair(car, cdr)]
    | ScmVector(sexprs) -> 
      let mapped = List.map (fun x -> extend_consts x) sexprs in
      let without_vector = List.fold_left (fun init next -> init @ next) [] mapped in
      without_vector @ [ScmVector(sexprs)]

  let rec extend_consts_from_list const_lst tbl =
    match const_lst with
    | [] -> tbl
    | hd :: tl -> 
      let hd_consts_extended = extend_consts hd in
      (tbl @ hd_consts_extended) @ extend_consts_from_list tl tbl

  let rec create_consts_tbl_with_dups asts tbl = 
    match asts with
    | [] -> tbl
    | hd :: tl -> 
      let hd_consts = find_all_consts hd [] in
      let extended = extend_consts_from_list hd_consts [] in
      (tbl @ extended) @ create_consts_tbl_with_dups tl tbl

  let rec remove_dups lst new_lst =
    match lst with
    | [] -> new_lst
    | hd :: tl -> 
      if (List.mem hd new_lst)
        then
          remove_dups tl new_lst
        else
          remove_dups tl (new_lst @ [hd])

  let find_byte_size const =
    match const with
    | ScmVoid -> 1
    | ScmNil -> 1
    | ScmBoolean x -> 2
    | ScmChar x -> 2
    | ScmString x -> 1 + 8 + String.length x
    | ScmSymbol x -> 1 + 8
    | ScmNumber x -> 1 + 8
    | ScmVector x -> 1 + 8 + (List.length x) * 8
    | ScmPair(car, cdr) -> 1 + 8 + 8

  let rec find_offset const consts_tbl =
    match consts_tbl with
    | [] -> raise X_this_shouldnt_happen
    | (x, (offset, _)) :: tl ->
      if (sexpr_eq x const) 
        then
          offset
        else
          find_offset const tl
  
  let create_const_offset_assembly_tbl const offset populated_already =
    match const with
    | ScmChar x -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_CHAR(\"%c\")" x))]
    | ScmString str -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_STRING \"%s\"" str))]
    | ScmSymbol str -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" (find_offset (ScmString(str)) populated_already)))]
    | ScmNumber(ScmRational(numerator, denominator)) -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_RATIONAL(%d,%d)" numerator denominator))]
    | ScmNumber(ScmReal(x)) -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" x))]
    | ScmVector(sexprs) -> 
      let offsets = List.map (fun x -> Printf.sprintf "const_tbl+%d" (find_offset x populated_already)) sexprs in
      let offsets_together = List.fold_right (fun next cur -> next ^ "," ^ cur) offsets "" in
      [(const, (offset, Printf.sprintf "MAKE_LITERAL_VECTOR %s" (String.sub offsets_together 0 (String.length offsets_together - 1))))]
    | ScmPair(car, cdr) -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d,const_tbl+%d)" (find_offset car populated_already) (find_offset cdr populated_already)))]
    | _ -> raise X_this_shouldnt_happen

  let rec populate_consts_tbl consts_tbl populated offset =
    match consts_tbl with
    | [] -> populated
    | ScmVoid :: tl -> populate_consts_tbl tl populated offset
    | ScmNil :: tl-> populate_consts_tbl tl populated offset
    | ScmBoolean x :: tl-> populate_consts_tbl tl populated offset
    | hd :: tl -> populate_consts_tbl tl (populated @ (create_const_offset_assembly_tbl hd offset populated)) (offset + find_byte_size hd)

  let make_consts_tbl asts = 
    let default_tbl = [(ScmVoid, (0, "db T_VOID"));
                       (ScmNil, (1, "db T_NIL"));
                       (ScmBoolean(false), (2, "db T_BOOL 0"));
                       (ScmBoolean(true), (4, "db T_BOOL 1"))] in
    let default_consts = [ScmVoid; 
                          ScmNil; 
                          ScmBoolean(false); 
                          ScmBoolean(true)] in
    let consts_with_dups = create_consts_tbl_with_dups asts [] in
    let all_consts = default_consts @ consts_with_dups in
    let consts_no_dups = remove_dups all_consts [] in
    populate_consts_tbl consts_no_dups default_tbl 6
  
  (* FREE VARS *)
  
  let rec find_all_free_vars expr lst =
    match expr with
    | ScmConst' x -> lst
    | ScmVar'(VarFree(x))-> lst @ [x]
    | ScmVar' x -> lst
    | ScmBox' x -> lst
    | ScmBoxGet' x -> lst
    | ScmBoxSet'(var, exp) -> 
      let exp_lst = find_all_free_vars exp [] in
      lst @ exp_lst
    | ScmIf'(test, dit, dif) ->
      let test_lst = find_all_free_vars test [] in
      let dit_lst = find_all_free_vars dit [] in
      let dif_lst = find_all_free_vars dif [] in
      ((lst @ test_lst) @ dit_lst) @ dif_lst 
    | ScmSeq'(exprs) ->
      let mapped = List.map (fun x -> find_all_free_vars x []) exprs in
      List.fold_left (fun init next -> init @ next) lst mapped
    | ScmSet'(var, exp) ->
      let exp_lst = find_all_free_vars exp [] in
      lst @ exp_lst
    | ScmDef'(var, exp) ->
      let exp_lst = find_all_free_vars exp [] in
      lst @ exp_lst
    | ScmOr'(exprs) ->
      let mapped = List.map (fun x -> find_all_free_vars x []) exprs in
      List.fold_left (fun init next -> init @ next) lst mapped
    | ScmLambdaSimple'(params, exp) ->
      let exp_lst = find_all_free_vars exp [] in
      lst @ exp_lst
    | ScmLambdaOpt'(params, param, exp) ->
      let exp_lst = find_all_free_vars exp [] in
      lst @ exp_lst
    | ScmApplic'(exp, exprs) ->
      let exp_lst = find_all_free_vars exp [] in
      let mapped = List.map (fun x -> find_all_free_vars x []) exprs in
      List.fold_left (fun init next -> init @ next) (lst @ exp_lst) mapped
    | ScmApplicTP'(exp, exprs) ->
      let exp_lst = find_all_free_vars exp [] in
      let mapped = List.map (fun x -> find_all_free_vars x []) exprs in
      List.fold_left (fun init next -> init @ next) (lst @ exp_lst) mapped

  let rec create_fvars_tbl_with_dups asts tbl = 
    match asts with
    | [] -> tbl
    | hd :: tl -> 
      let hd_fvars = find_all_free_vars hd [] in
      (tbl @ hd_fvars) @ create_fvars_tbl_with_dups tl tbl

  let rec index_fvars_tbl fvars_tbl index indexed_fvars = 
    match fvars_tbl with
    | [] -> indexed_fvars
    | hd :: tl -> index_fvars_tbl tl (index + 1) ([(hd, index)] @ indexed_fvars)

  let rec find_index fvars_tbl fvar =
    match fvars_tbl with
    | [] -> raise X_this_shouldnt_happen
    | (name, index) :: tl when name = fvar -> index
    | hd :: tl -> find_index tl fvar

  let make_fvars_tbl asts = 
    let free_vars_with_dups = create_fvars_tbl_with_dups asts [] in
    let free_vars_no_dups = remove_dups free_vars_with_dups [] in
    index_fvars_tbl free_vars_no_dups 0 []

  (* GENERATE ASSEMBLY*)

  let generate_lambda_simple_code consts fvars unique_index nested_lambda_index params body =
    let lcode = Printf.sprintf "Lcode%d" unique_index in
    let lcont = Printf.sprintf "Lcont%d" unique_index in
    let add_zero_rib_params_label = Printf.sprintf "add_zero_rib_params%d" unique_index in
    let copy_env_loop_label = Printf.sprintf "copy_env_loop%d" unique_index in
    let end_copy_env_loop_label = Printf.sprintf "end_copy_env_loop%d" unique_index in
    let copy_params_loop_label = Printf.sprintf "copy_params_loop%d" unique_index in
    let end_copy_params_loop_label = Printf.sprintf "end_copy_params_loop%d" unique_index in
    unique_index := !unique_index + 1;
    let simple_lambda_comment = "; ScmLambdaSimple': \n; Params: " ^ String.concat ", " params ^ "\n" in
    let generate_lambda_exec_code = lcode ^ ":\n" ^
                                    "push rbp\n" ^
                                    "mov rbp , rsp\n" ^
                                    recursive_generate consts fvars body unique_index (nested_lambda_index + 1) ^
                                    "leave\n" ^
                                    "ret\n" ^
                                    lcont ":\n" in
    let generate_extended_environment_code = 
      "mov rdx, " ^ string_of_int !unique_index ^ "\n" ^
      "shl rdx, 3 ; number_of_environments * 8 bytes\n" ^
      "MALLOC rdx, rdx\n" ^
      "mov rbx, [rbp + 8 * 2]\n" ^
      "cmp rbx, SOB_NIL_ADDRESS\n" ^
      "je " ^ add_zero_rib_params_label ^ "\n" ^
      "\n" ^
      "mov rsi, 0 ; i=0\n" ^
      "mov rdi, 1 ; j=1\n" ^
      copy_env_loop_label ^ ":\n" ^
      "cmp rsi, " ^ string_of_int (!unique_index - 1) ^ "\n" ^
      "je " ^ end_copy_env_loop_label ^ "\n" ^
      "mov rcx, [rbx + 8 * rdi]\n" ^ (**THIS MIGHT FAIL *)
      "mov qword [rdx + 8 * rsi], rcx\n" ^ (**THIS MIGHT FAIL *)
      "inc rsi\n" ^
      "inc rdi\n" ^
      "jmp " ^ copy_env_loop_label ^ "\n" ^
      end_copy_env_loop_label ^ ":\n" ^
      "\n" ^
      add_zero_rib_params_label ^ ":\n" ^
      "mov rcx, [rbp + 8 * 3]\n" ^
      "shl rcx, 3 ; number of params * 8 bytes\n" ^
      "MALLOC rcx, rcx\n" ^
      "mov qword [rdx + 8 * 0], rcx\n" ^
      "mov rdi, 0 ; i=0\n" ^
      copy_params_loop_label ^ ":\n" ^
      "cmp rdi, [rbp + 8 * 3]\n" ^
      "je " ^ end_copy_params_loop_label ^ "\n" ^
      "mov rbx, [rbp + 8 * (4 + rdi)]\n" ^
      "mov qword [rcx + 8 * rdi], rbx\n" ^
      "inc rdi\n" ^
      "jmp " ^ copy_params_loop_label ^ "\n" ^
      end_copy_params_loop_label ^ ":\n" ^ in
    let generate_closure_code = 
      "MALLOC_CLOSURE(rax, rdx, " ^ lcode ^ ")\n" ^ (** SOMETHING MIGHT BE WRONG HERE WITH rdx *)
      "jmp " ^ lcont "\n" in
    simple_lambda_comment ^ generate_extended_environment_code ^ generate_lambda_exec_code

  let generate_applic_code consts fvars unique_index nested_lambda_index proc args =
    let applic_comment = "; ScmApplic': \n" in
    let reversed_args = List.rev args in
    let generated_proc = recursive_generate consts fvars proc unique_index nested_lambda_index in
    let generated_reversed_args = List.map (fun x -> recursive_generate consts fvars x unique_index nested_lambda_index) reversed_args in
    let args_code = String.concat "push rax\n" generated_reversed_args in
    let code =
      args_code ^ "\n" ^
      "push rax\n" ^
      "push " ^ string_of_int (List.length args) ^ "\n" ^
      generated_proc ^
      "CLOSURE_ENV(rbx, rax)\n" ^
      "push rbx\n"
      "CLOSURE_CODE(rbx, rax)\n" ^
      "call rbx\n" ^
      "add rsp , 8*1 ; pop env\n" ^
      "pop rbx ; pop arg count\n" ^
      "lea rsp , [rsp + 8*rbx]\n" in
    code

  let rec recursive_generate consts fvars e unique_index nested_lambda_index = 
    match e with
    | ScmConst' x -> Printf.sprintf "; ScmConst':\nmov rax, const_tbl + %d\n" (find_offset e consts)
    | ScmVar'(VarParam(name, minor)) -> Printf.sprintf ";ScmVar'(VarParam): %s\nmov rax, qword [rbp + 8 ∗ (4 + %d)]\n" name minor
    | ScmVar'(VarBound(name, major, minor)) ->
      "; ScmVar'(VarBound): " ^ name ^ "\n" ^
      "mov rax, qword [rbp + 8 ∗ 2]\n" ^ 
      "mov rax, qword [rax + 8 ∗ " ^ string_of_int major ^ "]\n" ^ 
      "mov rax, qword [rax + 8 ∗ " ^ string_of_int minor ^ "]\n"
    | ScmVar'(VarFree(name)) -> Printf.sprintf "; ScmVar'(VarFree): %s\nmov rax, qword [fvar_tbl + %d]\n" name (find_index fvars name)
    | ScmSet'(ScmVar'(VarParam(name, minor)), expr) -> 
      "; ScmSet':\n; VarParam: " ^ name ^ "\n" ^
      recursive_generate consts fvars expr unique_index nested_lambda_index ^ 
      "mov qword [rbp + 8 ∗ (4 + " ^ string_of_int minor ^ ")], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"
    | ScmSet'(ScmVar'(VarBound(_, major, minor)), expr) -> 
      "; ScmSet':\n; VarBound: " ^ name ^ "\n" ^
      recursive_generate consts fvars expr unique_index nested_lambda_index ^ 
      "mov rbx, qword [rbp + 8 ∗ 2]\n" ^
      "mov rbx, qword [rbx + 8 ∗ " ^ string_of_int major ^ "]\n" ^
      "mov qword [rbx + 8 ∗ " ^ string_of_int minor ^ "], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"
    | ScmSet'(ScmVar'(VarFree(name)), expr) -> 
      "; ScmSet':\n; VarFree: " ^ name ^ "\n" ^
      recursive_generate consts fvars expr unique_index nested_lambda_index ^ 
      "mov qword [fvar_tbl + " ^ string_of_int (find_index fvars name) ^ "], rax\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"
    | ScmSeq'(exprs) ->
      let generated_code = List.map (fun x -> recursive_generate consts fvars x unique_index nested_lambda_index) exprs in
      let combined_code = List.fold_right (fun next cur -> next ^ cur) generated_code "" in
      "; ScmSeq': \n" ^ combined_code
    | ScmOr'(exprs) -> 
      let lexit = Printf.sprintf "Lexit%d" !unique_index in
      unique_index := !unique_index + 1;
      let code_between_exprs = "cmp rax, SOB_FALSE_ADDRESS\n" ^
                               "jne " ^ lexit ^ "\n" in
      let generated_code = List.map (fun x -> recursive_generate consts fvars x unique_index nested_lambda_index) exprs in
      let code_without_lexit = String.concat code_between_exprs generated_code in
      let code = code_without_lexit ^ lexit ^ ":\n"
      "; ScmOr': \n" ^ code
    | ScmIf'(test, dit, dif) -> 
      let lelse = Printf.sprintf "Lelse%d" !unique_index in
      let lexit = Printf.sprintf "Lexit%d" !unique_index in
      unique_index := !unique_index + 1;
      let generated_code_test = recursive_generate consts fvars test unique_index nested_lambda_index in
      let generated_code_dit = recursive_generate consts fvars dit unique_index nested_lambda_index in
      let generated_code_dif = recursive_generate consts fvars dif unique_index nested_lambda_index in
      let code = generated_code_test ^
                 "cmp rax, SOB_FALSE_ADDRESS\n" ^
                 "je " ^ lelse ^ "\n" ^
                 generated_code_dit ^
                 "jmp " ^ lexit ^ "\n" ^
                 lelse ^ ":\n" ^
                 generated_code_dif ^
                 lexit ^ ":\n"
      "; ScmIf': \n" ^ code
    | ScmBoxGet'(x) -> 
      "; ScmBoxGet': \n" ^
      recursive_generate consts fvars x unique_index nested_lambda_index ^
      "mov rax, qword [rax]\n"
    | ScmBoxSet'(x, expr) -> 
      "; ScmBoxSet': \n" ^
      recursive_generate consts fvars expr unique_index nested_lambda_index ^
      "push rax\n" ^
      recursive_generate consts fvars x unique_index nested_lambda_index ^
      "pop qword [rax]\n" ^
      "mov rax, SOB_VOID_ADDRESS\n"
    | ScmLambdaSimple'(params, body) ->
      generate_lambda_simple_code consts fvars unique_index nested_lambda_index params body
    | ScmLambdaOpt'(params, param, body) ->
      (* FINISH THIS PART *)
    | ScmApplic'(proc, args) ->
      generate_applic_code consts fvars unique_index nested_lambda_index proc args

  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

