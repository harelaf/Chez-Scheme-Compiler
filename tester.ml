#use "pc.ml"
#use "reader.ml"

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
and nt_paired_comment str = raise X_not_yet_implemented
and nt_sexpr_comment str = raise X_not_yet_implemented
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
  let fracs = pack fracs (fun (numerator, (_, denominator)) -> ScmRational(numerator, denominator)) in
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
  (* let nt1 = not_followed_by nt1 nt_symbol in *)
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  nt1 str
and nt_char_simple str = 
  let nt = range ' ' '\127'in
  nt str
and make_named_char char_name ch = 
  let nt = pack (word_ci char_name) (fun _ -> ch) in
  nt
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str = raise X_not_yet_implemented
and nt_char str = 
  let prefix = word "#\\" in
  let nt1 = disj nt_char_named nt_char_simple in
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
and nt_string str = raise X_not_yet_implemented
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
  let right_bracket = char '(' in
  let left_bracket = char ')' in
  let dot = char '.' in

  let star_sxepr = star nt_sexpr in
  let plus_sexpr = plus nt_sexpr in

  let nt1 = caten right_bracket (caten star_sxepr left_bracket) in
  let nt1 = pack nt1 (fun (_, (exprs, _)) -> List.fold_left 
                                              (fun a b -> ScmPair (b, a))
                                              ScmNil
                                              exprs) in
  let nt2 = caten right_bracket (caten plus_sexpr (caten dot (caten nt_sexpr left_bracket))) in
  let nt2 = pack nt2 (fun (_, (exprs, (_, (expr, _)))) -> List.fold_left 
                                                            (fun a b -> ScmPair (b, a))
                                                            expr
                                                            exprs) in

  let nt = disj nt1 nt2 in
  nt str
and nt_quoted_forms str = raise X_not_yet_implemented
and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;