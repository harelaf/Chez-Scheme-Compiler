#use "pc.ml";;
#use "reader.ml";;

let nt_boolean str = 
  let nt1 = word_ci "#f" in
  let nt1 = pack nt1 (fun _ -> false) in
  let nt2 = word_ci "#t" in
  let nt2 = pack nt2 (fun _ -> true) in
  let nt1 = disj nt1 nt2 in
  let nt1 = not_followed_by nt1 nt_symbol in
  let nt1 = pack nt1 (fun b -> ScmBoolean b) in
  nt1 str;;