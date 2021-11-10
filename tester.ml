#use "pc.ml"
#use "reader.ml"

open PC;;

  (* let plus_op = char '+';;
  let minus_op = char '-';;
  let digits = range '0' '9';;
  let num = plus digits;;
  let num = pack num (fun (ds) -> int_of_string (list_to_string ds));;

  let positives = caten plus_op num;;
  let positives = pack positives (fun (_, n) -> n);;

  let negatives = caten minus_op num;;
  let negatives = pack negatives (fun (_, n) -> -n);;

  let all_ints = disj num positives;;
  let all_ints = disj all_ints negatives;;

  let nt1 = char '/';;
  let digits = range '0' '9';;
  let num1 = plus digits;;
  let num1 = pack num1 (fun (ds) -> int_of_string (list_to_string ds));;

  let fracs = caten all_ints (caten nt1 num1);;
  let fracs = pack fracs (fun (numerator, (_, denominator)) -> ScmRational(numerator, denominator));; *)
let nt_int str = 
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

  all_ints str;;

let unitify nt =
    let nt1 = pack nt (fun _ -> ()) in
    nt1;;

let nt_integer_part str =
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

  all_ints str;;
let nt_mantissa str =
  let digits = range '0' '9' in
  let num = plus digits in
  let num = pack num (fun digits -> float_of_string ("." ^ (list_to_string digits))) in
  num str;;
let nt_exponent str =
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
  exp str;;
let nt_float str =
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
  let floatB = disj floatB_1_neg floatB_1_pos in
  let floatB = disj floatB floatB_2_pos in
  let floatB = disj floatB floatB_2_neg in
  let floatB = disj floatB floatB_1 in
  let floatB = disj floatB floatB_2 in

  let floatC = caten nt_integer_part nt_exponent in
  let floatC = pack floatC (fun ((op, n), exp) -> ScmReal ((float_of_string ((String.make 1 op) ^ (string_of_int n))) *. exp)) in

  let float = disj floatA (disj floatB floatC) in

  float str;;