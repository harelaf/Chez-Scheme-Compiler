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
    | ScmString str -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_STRING(\"%s\")" str))]
    | ScmSymbol str -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_SYMBOL(const_tbl+%d)" (find_offset (ScmString(str)) populated_already)))]
    | ScmNumber(ScmRational(numerator, denominator)) -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_RATIONAL(%d,%d)" numerator denominator))]
    | ScmNumber(ScmReal(x)) -> [(const, (offset, Printf.sprintf "MAKE_LITERAL_FLOAT(%f)" x))]
    | ScmVector(sexprs) -> 
      let offsets = List.map (fun x -> Printf.sprintf "const_tbl+%d" (find_offset x populated_already)) sexprs in
      let offsets_together = List.fold_right (fun next cur -> next ^ "," ^ cur) offsets "" in
      [(const, (offset, Printf.sprintf "MAKE_LITERAL_VECTOR(%s)" (String.sub offsets_together 0 (String.length offsets_together - 1))))]
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

  let rec recursive_generate consts fvars e unique_index = 
    match e with
    | ScmConst' x -> Printf.sprintf "\nmov rax, const_tbl + %d\n" (find_offset e consts)
    | ScmVar'(VarParam(_, minor)) -> Printf.sprintf "\nmov rax, qword [rbp + 8 ∗ (4 + %d)]\n" minor
    | ScmVar'(VarBound(_, major, minor)) ->
      "\nmov rax, qword [rbp + 8 ∗ 2]\n" ^ 
      "mov rax, qword [rax + 8 ∗ " ^ string_of_int major ^ "]\n" ^ 
      "mov rax, qword [rax + 8 ∗ " ^ string_of_int minor ^ "]\n"
    | ScmVar'(VarFree(name)) -> Printf.sprintf "\nmov rax, qword [fvar_tbl + %d]\n" (find_index fvars name)
    | ScmSet'(ScmVar'(VarParam(_, minor)), expr) -> 
      recursive_generate consts fvars expr unique_index ^ 
      "mov qword [rbp + 8 ∗ (4 + " ^ string_of_int minor ^ ")], rax\n" ^
      "mov rax, sob_void\n"
    | ScmSet'(ScmVar'(VarBound(_, major, minor)), expr) -> 
      recursive_generate consts fvars expr unique_index ^ 
      "mov rbx, qword [rbp + 8 ∗ 2]\n" ^
      "mov rbx, qword [rbx + 8 ∗ " ^ string_of_int major ^ "]\n" ^
      "mov qword [rbx + 8 ∗ " ^ string_of_int minor ^ "], rax\n" ^
      "mov rax, sob_void\n"
    | ScmSet'(ScmVar'(VarFree(name)), expr) -> 
      recursive_generate consts fvars expr unique_index ^ 
      "mov qword [fvar_tbl + " ^ string_of_int (find_index fvars name) ^ "], rax\n" ^
      "mov rax, sob_void\n"
    | ScmSeq'(exprs) ->
      let generated_code = List.map (fun x -> recursive_generate consts fvars x unique_index) exprs in
      let combined_code = List.fold_right (fun next cur -> next ^ cur) generated_code "" in
      combined_code
    | ScmOr'(exprs) -> 
      let lexit = Printf.sprintf "Lexit%d" !unique_index in
      unique_index := !unique_index + 1;
      let code_between_exprs = "cmp rax, sob_false\n" ^
                               "jne " ^ lexit ^ "\n" in
      let generated_code = List.map (fun x -> recursive_generate consts fvars x unique_index) exprs in
      let code_without_lexit = String.concat code_between_exprs generated_code in
      let code = code_without_lexit ^ lexit ^ ":\n"
      code
    | ScmIf'(test, dit, dif) -> 
      let lelse = Printf.sprintf "Lelse%d" !unique_index in
      let lexit = Printf.sprintf "Lexit%d" !unique_index in
      unique_index := !unique_index + 1;
      let generated_code_test = recursive_generate consts fvars test unique_index in
      let generated_code_dit = recursive_generate consts fvars dit unique_index in
      let generated_code_dif = recursive_generate consts fvars dif unique_index in
      let code = generated_code_test ^
                 "cmp rax, sob_false\n" ^
                 "je " ^ lelse ^ "\n" ^
                 generated_code_dit ^
                 "jmp " ^ lexit ^ "\n" ^
                 lelse ^ ":\n" ^
                 generated_code_dif ^
                 lexit ^ ":\n"
      code
    | ScmBoxGet'(x) -> 
      recursive_generate consts fvars x unique_index ^
      "mov rax, qword [rax]\n"
    | ScmBoxSet'(x, expr) -> 
      recursive_generate consts fvars expr unique_index ^
      "push rax\n" ^
      recursive_generate consts fvars x unique_index ^
      "pop qword [rax]\n" ^
      "mov rax, sob_void\n"
    | ScmLambdaSimple'(params, body) ->
      

  let generate consts fvars e = raise X_not_yet_implemented;;
end;;

