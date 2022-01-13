#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec scm_improper_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_improper_list_to_list tl)
| ScmNil -> []
| sexpr -> [sexpr];;

let rec check_dup_lambda_vars = function
| [] -> false
| hd::tl -> (List.mem hd tl) || (check_dup_lambda_vars tl)

let rec remove_last_elem = function
| [] -> []
| hd::[] -> []
| hd::tl -> hd::(remove_last_elem tl)

let rec scm_is_list = function
| ScmPair (hd, tl) -> scm_is_list tl
| ScmNil -> true
| _ -> false

let rec scm_is_improper_list = function
| ScmPair (hd, tl) -> scm_is_improper_list tl
| ScmNil -> false
| _ -> true

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

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

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;; 

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with
(* CONSTANTS *)
| ScmNil -> ScmConst(ScmNil)
| ScmBoolean(x) -> ScmConst(ScmBoolean(x))
| ScmChar(x) -> ScmConst(ScmChar(x))
| ScmNumber(x) -> ScmConst(ScmNumber(x))
| ScmString(x) -> ScmConst(ScmString(x))
| ScmPair(ScmSymbol("quote"), (ScmPair (x, ScmNil))) -> ScmConst(x)
| ScmSymbol(x) -> if (List.mem x reserved_word_list) 
                    then raise (X_reserved_word (x))
                    else ScmVar(x)
(* IF STATEMENTS *)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmPair(dif, ScmNil)))) ->
  ScmIf(tag_parse_expression test, tag_parse_expression dit, tag_parse_expression dif)
| ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(dit, ScmNil))) ->
  ScmIf(tag_parse_expression test, tag_parse_expression dit, ScmConst ScmVoid)
(* OR EXPRESSIONS *)
| ScmPair(ScmSymbol("or"), ScmNil) -> ScmConst (ScmBoolean false)
| ScmPair(ScmSymbol("or"), ScmPair(x, ScmNil)) -> tag_parse_expression x
| ScmPair(ScmSymbol("or"), exprs) -> 
  let or_exprs = scm_list_to_list exprs in 
  ScmOr(List.map tag_parse_expression or_exprs)
(* LAMBDA EXPRESSIONS *)
| ScmPair(ScmSymbol("lambda"), ScmPair(ScmSymbol(args), exprs)) ->
  if (scm_list_length exprs = 1)
    then 
      let expr = List.nth (scm_list_to_list exprs) 0 in
      ScmLambdaOpt([], args, tag_parse_expression expr)
    else
      let lambda_exprs = scm_list_to_list exprs in
      ScmLambdaOpt([], args, ScmSeq(List.map tag_parse_expression lambda_exprs))
| ScmPair(ScmSymbol("lambda"), ScmPair(variables, exprs)) ->
  if (scm_is_improper_list variables)
    then 
      let full_improper_varaibles = scm_improper_list_to_list variables in
      let lambda_variables = remove_last_elem full_improper_varaibles in
      if (check_dup_lambda_vars full_improper_varaibles)
        then
          raise (X_syntax_error(variables, "lambda variables contain duplicates"))
        else
          if (scm_list_length exprs = 1)
            then 
              let expr = List.nth (scm_list_to_list exprs) 0 in
              ScmLambdaOpt(List.map string_of_sexpr lambda_variables, string_of_sexpr (List.nth full_improper_varaibles ((List.length full_improper_varaibles) - 1)), tag_parse_expression expr)
            else
              let lambda_exprs = scm_list_to_list exprs in
              ScmLambdaOpt(List.map string_of_sexpr lambda_variables, string_of_sexpr (List.nth full_improper_varaibles ((List.length full_improper_varaibles) - 1)), ScmSeq(List.map tag_parse_expression lambda_exprs))
    else
      if (check_dup_lambda_vars (scm_list_to_list variables))
        then
          raise (X_syntax_error(variables, "lambda variables contain duplicates"))
        else 
          let lambda_variables = scm_list_to_list variables in
          if (scm_list_length exprs = 1)
            then 
              let expr = List.nth (scm_list_to_list exprs) 0 in
              ScmLambdaSimple(List.map string_of_sexpr lambda_variables, tag_parse_expression expr)
            else
              let lambda_exprs = scm_list_to_list exprs in
              ScmLambdaSimple(List.map string_of_sexpr lambda_variables, ScmSeq(List.map tag_parse_expression lambda_exprs))
(* DEFINE *)
| ScmPair(ScmSymbol("define"), ScmPair(ScmPair(name, args), exprs)) ->
  tag_parse_expression (ScmPair(ScmSymbol("define"), ScmPair(name, ScmPair(ScmPair(ScmSymbol("lambda"), ScmPair(args, exprs)), ScmNil))))
| ScmPair(ScmSymbol("define"), ScmPair(var, ScmPair(value, ScmNil))) ->
  if (List.mem (string_of_sexpr var) reserved_word_list)
    then
      raise (X_syntax_error (ScmPair(ScmSymbol("define"), ScmPair(var, ScmPair(value, ScmNil))), "Expected variable on LHS of define"))
    else
      if (sexpr_eq var (ScmSymbol(string_of_sexpr var)))
        then
          ScmDef(tag_parse_expression var, tag_parse_expression value)
        else
          raise (X_syntax_error (ScmPair(ScmSymbol("define"), ScmPair(var, ScmPair(value, ScmNil))), "Expected variable on LHS of define"))
(* ASSIGNMENTS *)
| ScmPair(ScmSymbol("set!"), ScmPair(var, ScmPair(value, ScmNil))) ->
  if (List.mem (string_of_sexpr var) reserved_word_list)
    then
      raise (X_syntax_error (ScmPair(ScmSymbol("set"), ScmPair(var, ScmPair(value, ScmNil))), "Expected variable on LHS of set!"))
    else
      if (sexpr_eq var (ScmSymbol(string_of_sexpr var)))
        then
          ScmSet(tag_parse_expression var, tag_parse_expression value)
        else
          raise (X_syntax_error (ScmPair(ScmSymbol("set!"), ScmPair(var, ScmPair(value, ScmNil))), "Expected variable on LHS of set!"))
(* SEQUENCES *)
| ScmPair(ScmSymbol "begin", ScmPair(expr, ScmNil)) ->
  tag_parse_expression expr
| ScmPair(ScmSymbol "begin", exprs) ->
  let exprs_list = scm_list_to_list exprs in
  ScmSeq(List.map tag_parse_expression exprs_list)
(* APPLICATIONS *)
| ScmPair(ScmPair(ScmSymbol("lambda"), body), args) ->
  let args_list = scm_list_to_list args in
  ScmApplic(tag_parse_expression (ScmPair(ScmSymbol("lambda"), body)), List.map tag_parse_expression args_list)
| ScmPair(func, ScmNil) -> 
  if not (List.mem (string_of_sexpr func) reserved_word_list)
    then
      ScmApplic(tag_parse_expression func, [])
  else
    raise (X_syntax_error ((ScmPair(func, ScmNil)), "This is a reserved word"))
| ScmPair(func, args) ->
  if not (List.mem (string_of_sexpr func) reserved_word_list)
    then
      let args_list = scm_list_to_list args in
      ScmApplic(tag_parse_expression func, List.map tag_parse_expression args_list)
  else
    raise (X_syntax_error ((ScmPair(func, args)), "This is a reserved word"))
(* STRUCTURE NOT RECOGNIZED *)
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))

and macro_expand sexpr =
match sexpr with
(* AND EXPRESSIONS *)
| ScmPair(ScmSymbol("and"), ScmNil) -> ScmBoolean(true)
| ScmPair(ScmSymbol("and"), ScmPair(expr, ScmNil)) -> expr
| ScmPair(ScmSymbol("and"), ScmPair(expr, exprs)) -> 
  ScmPair(ScmSymbol("if"), ScmPair(expr, ScmPair(macro_expand (ScmPair(ScmSymbol("and"), exprs)), ScmPair(ScmBoolean(false), ScmNil))))
(* COND EXPRESSIONS *)
| ScmPair(ScmSymbol("cond"), ScmNil) ->
  raise (X_syntax_error(ScmPair(ScmSymbol("cond"), ScmNil), "Sexpr structure not recognized"))
| ScmPair(ScmSymbol("cond"), ScmPair(ScmPair(ScmSymbol("else"), body), rest)) ->
  ScmPair(ScmSymbol("begin"), body)
| ScmPair(ScmSymbol("cond"), ScmPair(ScmPair(test, ScmPair(ScmSymbol("=>"), body)), rest)) ->
  if not (rest = ScmNil)
    then
    macro_expand
            (ScmPair
              (ScmSymbol "let",
                ScmPair
                (ScmPair
                  (ScmPair (ScmSymbol "value", ScmPair (test, ScmNil)),
                    ScmPair
                    (ScmPair
                      (ScmSymbol "f",
                        ScmPair
                        (ScmPair
                          (ScmSymbol "lambda",
                            ScmPair (ScmNil, body)),
                          ScmNil)),
                      ScmPair
                      (ScmPair
                        (ScmSymbol "rest",
                          ScmPair
                          (ScmPair
                            (ScmSymbol "lambda",
                              ScmPair (ScmNil, ScmPair (ScmPair(ScmSymbol("cond"), rest), ScmNil))),
                            ScmNil)),
                        ScmNil))),
                  ScmPair
                  (ScmPair
                    (ScmSymbol "if",
                      ScmPair
                      (ScmSymbol "value",
                        ScmPair
                        (ScmPair
                          (ScmPair (ScmSymbol "f", ScmNil),
                            ScmPair (ScmSymbol "value", ScmNil)),
                          ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
                    ScmNil))))
    else 
      macro_expand
            (ScmPair
              (ScmSymbol "let",
                ScmPair
                (ScmPair
                  (ScmPair (ScmSymbol "value", ScmPair (test, ScmNil)),
                    ScmPair
                    (ScmPair
                      (ScmSymbol "f",
                        ScmPair
                        (ScmPair
                          (ScmSymbol "lambda",
                            ScmPair (ScmNil, body)),  
                          ScmNil)),
                      ScmPair
                      (ScmPair
                        (ScmSymbol "rest",
                          ScmPair
                          (ScmPair
                            (ScmSymbol "lambda",
                              ScmPair (ScmNil, ScmPair (ScmVoid, ScmNil))),
                            ScmNil)),
                        ScmNil))),
                  ScmPair
                  (ScmPair
                    (ScmSymbol "if",
                      ScmPair
                      (ScmSymbol "value",
                        ScmPair
                        (ScmPair
                          (ScmPair (ScmSymbol "f", ScmNil),
                            ScmPair (ScmSymbol "value", ScmNil)),
                          ScmPair (ScmPair (ScmSymbol "rest", ScmNil), ScmNil)))),
                    ScmNil))))
| ScmPair(ScmSymbol("cond"), ScmPair(ScmPair(test, body), rest)) ->
  if not (rest = ScmNil)
    then
      ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol("begin"), body), ScmPair (ScmPair(ScmSymbol("cond"), rest), ScmNil))))
    else
      ScmPair(ScmSymbol("if"), ScmPair(test, ScmPair(ScmPair(ScmSymbol("begin"), body), ScmNil)))
(* LET EXPRESSIONS *)
| ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)) ->
  ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(ScmNil, body)), ScmNil)
| ScmPair(ScmSymbol "let", ScmPair(ScmPair(ScmPair(arg, ScmPair(value, ScmNil)), ribs), body)) ->
  let ribs_list = scm_list_to_list ribs in
  let ribs_list = List.map scm_list_to_list ribs_list in
  ScmPair(ScmPair(ScmSymbol "lambda", ScmPair(macro_expand (ScmPair(arg, list_to_proper_list (List.map (fun x -> List.nth x 0) ribs_list))), body)), ScmPair(value, list_to_proper_list (List.map (fun x -> List.nth x 1) ribs_list)))
(* LET* EXPRESSIONS *)
| ScmPair(ScmSymbol("let*"), ScmPair(ScmNil, body)) ->
  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmNil, body)))
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(ScmPair(arg, ScmPair(value, ScmNil)), ScmNil), body)) ->
  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmPair(ScmPair(arg, ScmPair(value, ScmNil)), ScmNil), body)))
| ScmPair(ScmSymbol("let*"), ScmPair(ScmPair(ScmPair(arg, ScmPair(value, ScmNil)), ribs), body)) ->
  macro_expand (ScmPair(ScmSymbol("let"), ScmPair(ScmPair(ScmPair(arg, ScmPair(value, ScmNil)), ScmNil), ScmPair(ScmPair(ScmSymbol("let*"), ScmPair(ribs, body)), ScmNil))))
(* LETREC EXPRESSIONS *)
| ScmPair(ScmSymbol("letrec"), ScmPair(ScmNil, body)) ->
  macro_expand (ScmPair(ScmSymbol "let", ScmPair (ScmNil, body)))
| ScmPair(ScmSymbol("letrec"), ScmPair(ribs, body)) ->
  let ribs_list = scm_list_to_list ribs in
  let ribs_list = List.map scm_list_to_list ribs_list in
  let whatever_list = List.map (fun x -> ScmPair(List.nth x 0, ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmSymbol("whatever"), ScmNil)), ScmNil))) ribs_list in
  let set_list = List.map (fun x -> ScmPair(ScmSymbol("set!"), ScmPair(List.nth x 0, ScmPair(List.nth x 1, ScmNil)))) ribs_list in
  let body_list = scm_list_to_list body in
  macro_expand (ScmPair(ScmSymbol "let", ScmPair(list_to_proper_list whatever_list, list_to_proper_list (set_list @ body_list))))
(* QUASIQUOTE EXPRESSIONS *)
(* `Number *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmNumber(x), ScmNil)) ->
  ScmNumber(x)
(* `Char *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmChar(x), ScmNil)) ->
  ScmChar(x)
(* `Boolean *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmBoolean(x), ScmNil)) ->
  ScmBoolean(x)
(* (*`String*)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmString(x), ScmNil)) ->
  ScmString(x) *)
(* `Symbol *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmSymbol(x), ScmNil)) ->
  ScmPair(ScmSymbol("quote"), (ScmPair (ScmSymbol(x), ScmNil)))
(* `Nil *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmNil, ScmNil)) ->
  ScmNil
(* `,expr *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair (ScmSymbol("unquote"), ScmPair (expr, ScmNil)), ScmNil)) ->
  expr
(* `,@expr *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(expr, ScmNil)), ScmNil)) ->
  ScmPair(ScmSymbol("quote"), ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(expr, ScmNil)), ScmNil))
(* `(,@expr_A) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(expr_A, ScmNil)), ScmNil),ScmNil)) ->
  ScmPair(ScmSymbol("append"), ScmPair(expr_A, ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmNil, ScmNil)), ScmNil)))
(* `(,expr_A) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(ScmPair(ScmSymbol("unquote"), ScmPair(expr_A, ScmNil)), ScmNil),ScmNil)) ->
  ScmPair(ScmSymbol("cons"), ScmPair(expr_A, ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmNil, ScmNil)), ScmNil)))
(* `((expr_A rest)) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(ScmPair(expr_A, rest), ScmNil), ScmNil)) ->
  ScmPair(ScmSymbol("cons"), ScmPair(macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(expr_A, rest), ScmNil))), ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmNil, ScmNil)), ScmNil)))
(* `(,@expr_A rest) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(ScmPair(ScmSymbol("unquote-splicing"), ScmPair(expr_A, ScmNil)), rest),ScmNil)) ->
  ScmPair(ScmSymbol("append"), ScmPair(expr_A, ScmPair(macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(rest, ScmNil))), ScmNil)))
(* `(,expr_A rest) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(ScmPair(ScmSymbol("unquote"), ScmPair(expr_A, ScmNil)), rest),ScmNil)) ->
  ScmPair(ScmSymbol("cons"), ScmPair(expr_A, ScmPair(macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(rest, ScmNil))), ScmNil)))
(* `('expr_A rest) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(expr_A, ScmNil)), rest),ScmNil)) ->
  ScmPair(ScmSymbol("cons"), ScmPair(macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(expr_A, ScmNil)), ScmNil))), ScmPair(macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(rest, ScmNil))), ScmNil)))
(* `#(exprs) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmVector exprs, ScmNil)) ->
  let exprs_list = list_to_proper_list exprs in 
  let expanded_exprs = macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(exprs_list, ScmNil))) in
  ScmPair(ScmSymbol("list->vector"), ScmPair(expanded_exprs, ScmNil))
(* `(expr_A) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(expr_A, ScmNil),ScmNil)) ->
  ScmPair(ScmSymbol("cons"), ScmPair(macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(expr_A, ScmNil))), ScmPair(ScmPair(ScmSymbol("quote"), ScmPair(ScmNil, ScmNil)), ScmNil)))
(* `(expr_A rest) *)
| ScmPair(ScmSymbol("quasiquote"), ScmPair(ScmPair(expr_A, rest),ScmNil)) ->
  ScmPair(ScmSymbol("cons"), ScmPair(macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(expr_A, ScmNil))), ScmPair(macro_expand (ScmPair(ScmSymbol("quasiquote"), ScmPair(rest, ScmNil))), ScmNil)))
| _ -> sexpr
end;;

