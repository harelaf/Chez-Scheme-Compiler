(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

let rec pow num = 
  function
    | 0 -> 1
    | 1 -> num
    | n -> 
      let ans = pow num (n / 2) in
      ans * ans * (if n mod 2 = 0 then 1 else num);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

let rec make_pairs =
  function
    | [] -> ScmNil
    | [e1] -> ScmPair(e1, ScmNil)
    | head :: tail -> ScmPair(head, make_pairs tail);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser;;
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str
and nt_line_comment str =
  let nt_end = disj (unitify (char '\n')) (unitify nt_end_of_input) in
  let nt1 = char ';' in
  let nt2 = diff nt_any nt_end in
  let nt2 = star nt2 in
  let nt1 = caten nt1 (caten nt2 nt_end) in
  let nt1 = unitify nt1 in
  nt1 str
and nt_paired_comment str = 
  let problematic_sexprs = disj (unitify (disj (word "#\\{") (word "#\\}"))) (unitify nt_string) in
  let problematic_sexprs = disj problematic_sexprs (unitify nt_comment) in
  let nt1 = disj problematic_sexprs (unitify (one_of "{}")) in
  let nt2 = diff nt_any nt1 in
  let nt2 = disj (unitify nt2) problematic_sexprs in
  let nt2 = star nt2 in
  let nt = unitify (caten (char '{') (caten nt2 (char '}'))) in
  nt str
and nt_sexpr_comment str = 
  let nt1 = word "#;" in
  let nt1 = caten nt1 nt_sexpr in
  let nt1 = unitify nt1 in
  nt1 str
and nt_comment str =
  disj_list
    [nt_line_comment;
     nt_paired_comment;
     nt_sexpr_comment] str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1
and nt_int str = 
  let plus_op = char '+' in
  let minus_op = char '-' in
  let digits = range '0' '9' in
  let num = plus digits in
  let num = pack num (fun (ds) -> int_of_string (list_to_string ds)) in

  let positives = caten plus_op num in
  let positives = pack positives (fun (_, n) -> n) in

  let negatives = caten minus_op num in
  let negatives = pack negatives (fun (_, n) -> -n) in

  let all_ints = disj num positives in
  let all_ints = disj all_ints negatives in

  all_ints str
and nt_frac str =
  let nt1 = char '/' in
  let digits = range '0' '9' in
  let num = plus digits in
  let num = pack num (fun (ds) -> int_of_string (list_to_string ds)) in

  let fracs = caten nt_int (caten nt1 num) in
  let fracs = pack fracs (fun (numerator, (_, denominator)) -> if denominator = 0 then raise X_no_match 
                                                                                  else ScmRational(numerator / (gcd numerator denominator), denominator / (gcd numerator denominator))) in
  fracs str
and nt_integer_part str =
  let plus_op = char '+' in
  let minus_op = char '-' in
  let digits = range '0' '9' in
  let num = plus digits in
  let num_no_op = pack num (fun (ds) -> ('+' ,int_of_string (list_to_string ds))) in
  let num = pack num (fun (ds) -> int_of_string (list_to_string ds)) in

  let positives = caten plus_op num in

  let negatives = caten minus_op num in

  let all_ints = disj num_no_op positives in
  let all_ints = disj all_ints negatives in

  all_ints str
and nt_mantissa str =
  let digits = range '0' '9' in
  let num = plus digits in
  let num = pack num (fun digits -> float_of_string ("." ^ (list_to_string digits))) in
  num str
and nt_exponent str =
  let nt1 = char_ci 'e' in
  let nt1 = unitify nt1 in
  let nt2 = word "*10^" in
  let nt2 = unitify nt2 in
  let nt3 = word "*10**" in
  let nt3 = unitify nt3 in
  let nt4 = disj nt1 nt2 in
  let nt4 = disj nt4 nt3 in

  let exp = caten nt4 nt_int in
  let exp = pack exp (fun (_, n) -> 
                                    if (n >= 0) then (float_of_int (pow 10 n))
                                                else (1. /. (float_of_int (pow 10 n)))) in
  exp str
and nt_float str =
  let dot = char '.' in
  let plus_op = char '+' in
  let minus_op = char '-' in

  let floatA_1 = caten nt_integer_part dot in
  let floatA_1 = pack floatA_1 (fun ((op, n), _) -> ScmReal (float_of_string ((String.make 1 op) ^ (string_of_int n)))) in
  let floatA_2 = caten nt_integer_part (caten dot nt_exponent) in
  let floatA_2 = pack floatA_2 (fun ((op, n), (_, exp)) -> ScmReal ((float_of_string ((String.make 1 op) ^ (string_of_int n))) *. exp)) in
  let floatA_3 = caten nt_integer_part (caten dot nt_mantissa) in
  let floatA_3 = pack floatA_3 (fun ((op, n), (_, man)) -> ScmReal ((float_of_string ((String.make 1 op) ^ (string_of_float ((float_of_int n) +. man)))))) in
  let floatA_4 = caten nt_integer_part (caten dot (caten nt_mantissa nt_exponent)) in
  let floatA_4 = pack floatA_4 (fun ((op, n), (_, (man, exp))) -> ScmReal ((float_of_string ((String.make 1 op) ^ (string_of_float ((float_of_int n) +. man)))) *.  exp)) in
  let floatA = disj floatA_4 (disj floatA_3 (disj floatA_2 floatA_1)) in

  let floatB_1 = caten dot nt_mantissa in
  let floatB_1_pos = caten plus_op floatB_1 in
  let floatB_1_neg = caten minus_op floatB_1 in
  let floatB_1 = pack floatB_1 (fun (_, man) -> ScmReal man) in
  let floatB_1_pos = pack floatB_1_pos (fun (_, (_, man)) -> ScmReal man) in
  let floatB_1_neg = pack floatB_1_neg (fun (_, (_, man)) -> ScmReal (-.(man))) in
  let floatB_2 = caten dot (caten nt_mantissa nt_exponent) in
  let floatB_2_pos = caten plus_op floatB_2 in
  let floatB_2_neg = caten minus_op floatB_2 in
  let floatB_2 = pack floatB_2 (fun (_, (man, exp)) -> ScmReal (man *. exp)) in
  let floatB_2_pos = pack floatB_2_pos (fun (_, (_, (man, exp))) -> ScmReal (man *. exp)) in
  let floatB_2_neg = pack floatB_2_neg (fun (_, (_, (man, exp))) -> ScmReal (-.(man *. exp))) in
  let floatB = disj floatB_2_neg floatB_2_pos in
  let floatB = disj floatB floatB_1_pos in
  let floatB = disj floatB floatB_1_neg in
  let floatB = disj floatB floatB_2 in
  let floatB = disj floatB floatB_1 in

  let floatC = caten nt_integer_part nt_exponent in
  let floatC = pack floatC (fun ((op, n), exp) -> ScmReal ((float_of_string ((String.make 1 op) ^ (string_of_int n))) *. exp)) in

  let float = disj floatA (disj floatB floatC) in

  float str
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
and nt_boolean str = 
  let nt1 = word_ci "#f" in
  let nt1 = pack nt1 (fun _ -> false) in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _ -> true) in
  let nt1 = disj nt1 nt2 in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  nt1 str
and nt_char_simple str = 
  let nt = followed_by (range ' ' '\127') (disj (unitify (char ' ')) (disj (unitify (char ')')) (disj (unitify (char '(')) (unitify nt_end_of_line_or_file)))) in
  nt str 
and make_named_char char_name ch = 
  let nt = pack (word_ci char_name) (fun _ -> ch) in
  nt
and nt_char_named str =
  disj_list [(make_named_char "newline" '\n');
              (make_named_char "nul" '\000');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] str
and nt_char_hex str = 
  let nt1 = range '0' '9' in
  let nt2 = range_ci 'a' 'f' in
  let nt2 = disj nt1 nt2 in
  let nt2 = plus nt2 in
  let nt2 = pack nt2 (fun (lst) -> List.fold_left 
                                    (fun b a -> if (int_of_char a) <= (int_of_char '9')
                                                then (int_of_char a) - (int_of_char '0') + 16*b
                                                else
                                                  if (int_of_char a) >= (int_of_char 'a')
                                                  then (int_of_char a) - (int_of_char 'a') + 10 + 16*b
                                                  else
                                                    (int_of_char a) - (int_of_char 'A') + 10 + 16*b)
                                    0 
                                    lst) in

  let nt_prefix = char_ci 'x' in
  let nt = caten nt_prefix nt2 in
  let nt = pack nt (fun (_, n) -> char_of_int n) in
  nt str
and nt_char str = 
  let prefix = word "#\\" in
  let nt1 = disj nt_char_hex nt_char_named in
  let nt1 = disj nt1 nt_char_simple in
  let nt = caten prefix nt1 in
  let nt = pack nt (fun (_, ch) -> ScmChar ch) in
  nt str
and nt_symbol_char str = 
  let nt1 = range '0' '9' in
  let nt2 = range_ci 'a' 'z' in
  let nt3 = char '!' in
  let nt4 = char '$' in
  let nt5 = char '^' in
  let nt6 = char '*' in
  let nt7 = char '-' in
  let nt8 = char '_' in
  let nt9 = char '=' in
  let nt10 = char '+' in
  let nt11 = char '<' in
  let nt12 = char '>' in
  let nt13 = char '?' in
  let nt14 = char '/' in
  let nt15 = char ':' in

  let nt = disj_list [nt1; nt2; nt3; nt4; nt5; nt6; nt7; nt8; nt9; nt10; nt11; nt12; nt13; nt14; nt15] in
  nt str
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str
and nt_string str = 
  let nt1 = disj (char '\"') (char '\\') in
  let nt1 = disj nt1 (char '~') in
  let nt_literal_char = diff nt_any nt1 in

  let nt2 = disj (pack (word "\\\"") (fun _ -> '\"')) (pack (word "\\\\") (fun _ -> '\\')) in
  let nt2 = disj nt2 (pack (word "\\t") (fun _ -> '\t')) in
  let nt2 = disj nt2 (pack (word "\\f") (fun _ -> '\012')) in
  let nt2 = disj nt2 (pack (word "\\n") (fun _ -> '\n')) in
  let nt2 = disj nt2 (pack (word "\\r") (fun _ -> '\r')) in
  let nt_meta_char = disj nt2 (pack (word "~~") (fun _ -> '~')) in

  let nt3 = caten (char '\\') nt_char_hex in
  let nt_hex_char = caten nt3 (char ';') in
  let nt_hex_char = pack nt_hex_char (fun ((_, ch), _) -> ch) in
  
  let nt_tilde = char '~' in
  let nt_left = char '{' in
  let nt_right = char '}' in
  let nt_interpolated = caten nt_tilde (caten nt_left (caten (make_skipped_star nt_sexpr) nt_right)) in
  let nt_interpolated = pack nt_interpolated (fun (_, (_, (expr, _))) -> ScmPair(ScmSymbol "format", ScmPair(ScmString("~a"), ScmPair(expr, ScmNil)))) in

  let nt_chars = disj nt_meta_char nt_hex_char in
  let nt_chars = disj nt_chars nt_literal_char in
  let nt_chars = plus nt_chars in
  let nt_chars = pack nt_chars (fun lst -> ScmString(list_to_string lst)) in

  let nt_combined = disj nt_interpolated nt_chars in

  let nt_combined_star = star nt_combined in
  let nt_combined_star = pack nt_combined_star (fun lst -> if List.length lst == 0 
                                                            then ScmString("")
                                                            else if List.length lst = 1
                                                              then List.hd lst
                                                              else ScmPair(ScmSymbol("string-append"), make_pairs lst)) in

  let nt = caten (char '\"') (caten nt_combined_star (char '\"')) in
  let nt = pack nt (fun (_, (expr, _)) -> expr) in
  nt str
and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str
and nt_list str = 
  let left_bracket = char '(' in
  let right_bracket = char ')' in
  let whitespace_right = caten nt_skip_star right_bracket in
  let whitespace_right = pack whitespace_right (fun _ -> ScmNil) in
  let dot = char '.' in

  let star_sxepr = star nt_sexpr in
  let plus_sexpr = plus nt_sexpr in

  let nt1 = caten star_sxepr right_bracket in
  let nt1 = pack nt1 (fun (exprs, _) -> List.fold_right 
                                              (fun b a -> ScmPair (b, a))
                                              exprs
                                              ScmNil) in
  let nt1 = caten left_bracket (disj whitespace_right nt1) in
  let nt1 = pack nt1 (fun (_, expr) -> expr) in

  let nt2 = caten left_bracket (caten plus_sexpr (caten dot (caten nt_sexpr right_bracket))) in
  let nt2 = pack nt2 (fun (_, (exprs, (_, (expr, _)))) -> List.fold_right 
                                                            (fun b a -> ScmPair (b, a))
                                                            exprs
                                                            expr) in

  let nt = disj nt1 nt2 in
  nt str
and nt_quoted_forms str = 
  let nt1 = char '\'' in
  let nt1 = caten nt1 nt_sexpr in
  let nt_quote = pack nt1 (fun (_, expr) -> ScmPair(ScmSymbol "quote", ScmPair(expr, ScmNil))) in

  let nt2 = char '`' in
  let nt2 = caten nt2 nt_sexpr in
  let nt_quasiquote = pack nt2 (fun (_, expr) -> ScmPair(ScmSymbol "quasiquote", ScmPair(expr, ScmNil))) in

  let nt3 = char ',' in
  let nt3 = caten nt3 nt_sexpr in
  let nt_unquote = pack nt3 (fun (_, expr) -> ScmPair(ScmSymbol "unquote", ScmPair(expr, ScmNil))) in

  let nt4 = word ",@" in
  let nt4 = caten nt4 nt_sexpr in
  let nt_unquote_splicing = pack nt4 (fun (_, expr) -> ScmPair(ScmSymbol "unquote-splicing", ScmPair(expr, ScmNil))) in

  let nt = disj nt_quote nt_quasiquote in
  let nt = disj nt nt_unquote_splicing in
  let nt = disj nt nt_unquote in
  nt str
and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
              nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;