#use "semantic-analyser.ml";;
open Semantic_Analysis;;
open Tag_Parser;;
open Reader;;

let tester str = Semantic_Analysis.run_semantics (Tag_Parser.tag_parse_expression (Reader.nt_sexpr str 0).found);;

let inputs = ["(lambda (x) (set! x (+ 1 x)))";
                "(lambda (x) (list (lambda () x) (lambda () (set! x (+ x 1)))))";
                "(lambda (x) (lambda (u) (u (lambda () x) (lambda () (set! x (+ x 1))))))";
                "(lambda (x) (list x (set! x 5)))";
                "(lambda (f k) ((lambda (x k) (f (lambda (arg k) (x x (lambda (xx) (xx arg k)) k)) k)) (lambda (x k) (f (lambda (arg k) (x x (lambda (xx) (xx arg k)) k)) k)) k))";
                "(lambda (x) (lambda (y z) (lambda (t) ((x y) ((x t) z)))))";
                "(define ycurry (lambda (f) ((lambda (x) (f (lambda args (apply (x x) args)))) (lambda (x) (f (lambda args (apply (x x) args)))))))";
                "((lambda (x) (lambda (f) (f (lambda args (apply ((x x) f) args))))) (lambda (x) (lambda (f) (f (lambda args (apply ((x x) f) args)))))) ";
                "(lambda (a b c)
  (list
    (lambda ()
      (set! a 0)
      (set! c 0)
      (+ a b c))
    (lambda (new-a)
      (set! a new-a)
      (* a b c))
    (lambda () a)
    (lambda () b)
    (lambda () c)))
";
                "

(lambda (a b c)
  (list 
    (lambda (a c)
      (display (format \"a = ~~a~~%\" a))
      (display (format \"b = ~~a~~%\" b))
      (display (format \"c = ~~a~~%\" c))
      (+ a b c))
    (lambda ()
      (display (format \"a = ~~a~~%\" a))
      (display (format \"b = ~~a~~%\" b))
      (display (format \"c = ~~a~~%\" c))
      (set! a 0)
      (set! b 0)
      (set! c 0)
      )
    (lambda (aa bb cc)
      (set! a aa)
      (set! bb b)
      (set! c cc)
      (list a b c))))

";
"(lambda (x) (lambda (y) (set! x 1) (lambda () x)))";
"(lambda ()
  ((lambda () x)) 
  ((lambda (x)
     (set! x 104)
     (lambda () x))
   104)
  ((lambda x x) 104))";
  "

(lambda (x)
  (lambda (y)
    (set! x 1)
    (lambda () x)))

"];;

let outputs=[ScmLambdaSimple' (["x"],
 ScmSet' (VarParam ("x", 0),
  ScmApplic' (ScmVar' (VarFree "+"),
   [ScmConst' (ScmNumber (ScmRational (1, 1))); ScmVar' (VarParam ("x", 0))])));
   ScmLambdaSimple' (["x"],
 ScmSeq'
  [ScmSet' (VarParam ("x", 0), ScmBox' (VarParam ("x", 0)));
   ScmApplicTP' (ScmVar' (VarFree "list"),
    [ScmLambdaSimple' ([], ScmBoxGet' (VarBound ("x", 0, 0)));
     ScmLambdaSimple' ([],
      ScmBoxSet' (VarBound ("x", 0, 0),
       ScmApplic' (ScmVar' (VarFree "+"),
        [ScmBoxGet' (VarBound ("x", 0, 0));
         ScmConst' (ScmNumber (ScmRational (1, 1)))])))])]);
         ScmLambdaSimple' (["x"],
 ScmLambdaSimple' (["u"],
  ScmApplicTP' (ScmVar' (VarParam ("u", 0)),
   [ScmLambdaSimple' ([], ScmVar' (VarBound ("x", 1, 0)));
    ScmLambdaSimple' ([],
     ScmSet' (VarBound ("x", 1, 0),
      ScmApplic' (ScmVar' (VarFree "+"),
       [ScmVar' (VarBound ("x", 1, 0));
        ScmConst' (ScmNumber (ScmRational (1, 1)))])))])));
        ScmLambdaSimple' (["x"],
 ScmApplicTP' (ScmVar' (VarFree "list"),
  [ScmVar' (VarParam ("x", 0));
   ScmSet' (VarParam ("x", 0), ScmConst' (ScmNumber (ScmRational (5, 1))))]));
   ScmLambdaSimple' (["f"; "k"],
 ScmApplicTP'
  (ScmLambdaSimple' (["x"; "k"],
    ScmApplicTP' (ScmVar' (VarBound ("f", 0, 0)),
     [ScmLambdaSimple' (["arg"; "k"],
       ScmApplicTP' (ScmVar' (VarBound ("x", 0, 0)),
        [ScmVar' (VarBound ("x", 0, 0));
         ScmLambdaSimple' (["xx"],
          ScmApplicTP' (ScmVar' (VarParam ("xx", 0)),
           [ScmVar' (VarBound ("arg", 0, 0)); ScmVar' (VarBound ("k", 0, 1))]));
         ScmVar' (VarParam ("k", 1))]));
      ScmVar' (VarParam ("k", 1))])),
  [ScmLambdaSimple' (["x"; "k"],
    ScmApplicTP' (ScmVar' (VarBound ("f", 0, 0)),
     [ScmLambdaSimple' (["arg"; "k"],
       ScmApplicTP' (ScmVar' (VarBound ("x", 0, 0)),
        [ScmVar' (VarBound ("x", 0, 0));
         ScmLambdaSimple' (["xx"],
          ScmApplicTP' (ScmVar' (VarParam ("xx", 0)),
           [ScmVar' (VarBound ("arg", 0, 0)); ScmVar' (VarBound ("k", 0, 1))]));
         ScmVar' (VarParam ("k", 1))]));
      ScmVar' (VarParam ("k", 1))]));
   ScmVar' (VarParam ("k", 1))]));
   ScmLambdaSimple' (["x"],
 ScmLambdaSimple' (["y"; "z"],
  ScmLambdaSimple' (["t"],
   ScmApplicTP'
    (ScmApplic' (ScmVar' (VarBound ("x", 1, 0)),
      [ScmVar' (VarBound ("y", 0, 0))]),
    [ScmApplic'
      (ScmApplic' (ScmVar' (VarBound ("x", 1, 0)),
        [ScmVar' (VarParam ("t", 0))]),
      [ScmVar' (VarBound ("z", 0, 1))])]))));
      ScmDef' (VarFree "ycurry",
 ScmLambdaSimple' (["f"],
  ScmApplicTP'
   (ScmLambdaSimple' (["x"],
     ScmApplicTP' (ScmVar' (VarBound ("f", 0, 0)),
      [ScmLambdaOpt' ([], "args",
        ScmApplicTP' (ScmVar' (VarFree "apply"),
         [ScmApplic' (ScmVar' (VarBound ("x", 0, 0)),
           [ScmVar' (VarBound ("x", 0, 0))]);
          ScmVar' (VarParam ("args", 0))]))])),
   [ScmLambdaSimple' (["x"],
     ScmApplicTP' (ScmVar' (VarBound ("f", 0, 0)),
      [ScmLambdaOpt' ([], "args",
        ScmApplicTP' (ScmVar' (VarFree "apply"),
         [ScmApplic' (ScmVar' (VarBound ("x", 0, 0)),
           [ScmVar' (VarBound ("x", 0, 0))]);
          ScmVar' (VarParam ("args", 0))]))]))])));
          ScmApplic'
 (ScmLambdaSimple' (["x"],
   ScmLambdaSimple' (["f"],
    ScmApplicTP' (ScmVar' (VarParam ("f", 0)),
     [ScmLambdaOpt' ([], "args",
       ScmApplicTP' (ScmVar' (VarFree "apply"),
        [ScmApplic'
          (ScmApplic' (ScmVar' (VarBound ("x", 1, 0)),
            [ScmVar' (VarBound ("x", 1, 0))]),
          [ScmVar' (VarBound ("f", 0, 0))]);
         ScmVar' (VarParam ("args", 0))]))]))),
 [ScmLambdaSimple' (["x"],
   ScmLambdaSimple' (["f"],
    ScmApplicTP' (ScmVar' (VarParam ("f", 0)),
     [ScmLambdaOpt' ([], "args",
       ScmApplicTP' (ScmVar' (VarFree "apply"),
        [ScmApplic'
          (ScmApplic' (ScmVar' (VarBound ("x", 1, 0)),
            [ScmVar' (VarBound ("x", 1, 0))]),
          [ScmVar' (VarBound ("f", 0, 0))]);
         ScmVar' (VarParam ("args", 0))]))])))]);
         ScmLambdaSimple' (["a"; "b"; "c"],
 ScmSeq'
  [ScmSet' (VarParam ("a", 0), ScmBox' (VarParam ("a", 0)));
   ScmSet' (VarParam ("c", 2), ScmBox' (VarParam ("c", 2)));
   ScmApplicTP' (ScmVar' (VarFree "list"),
    [ScmLambdaSimple' ([],
      ScmSeq'
       [ScmBoxSet' (VarBound ("a", 0, 0),
         ScmConst' (ScmNumber (ScmRational (0, 1))));
        ScmBoxSet' (VarBound ("c", 0, 2),
         ScmConst' (ScmNumber (ScmRational (0, 1))));
        ScmApplicTP' (ScmVar' (VarFree "+"),
         [ScmBoxGet' (VarBound ("a", 0, 0)); ScmVar' (VarBound ("b", 0, 1));
          ScmBoxGet' (VarBound ("c", 0, 2))])]);
     ScmLambdaSimple' (["new-a"],
      ScmSeq'
       [ScmBoxSet' (VarBound ("a", 0, 0), ScmVar' (VarParam ("new-a", 0)));
        ScmApplicTP' (ScmVar' (VarFree "*"),
         [ScmBoxGet' (VarBound ("a", 0, 0)); ScmVar' (VarBound ("b", 0, 1));
          ScmBoxGet' (VarBound ("c", 0, 2))])]);
     ScmLambdaSimple' ([], ScmBoxGet' (VarBound ("a", 0, 0)));
     ScmLambdaSimple' ([], ScmVar' (VarBound ("b", 0, 1)));
     ScmLambdaSimple' ([], ScmBoxGet' (VarBound ("c", 0, 2)))])]);
     ScmLambdaSimple' (["a"; "b"; "c"],
 ScmSeq'
  [ScmSet' (VarParam ("a", 0), ScmBox' (VarParam ("a", 0)));
   ScmSet' (VarParam ("b", 1), ScmBox' (VarParam ("b", 1)));
   ScmSet' (VarParam ("c", 2), ScmBox' (VarParam ("c", 2)));
   ScmApplicTP' (ScmVar' (VarFree "list"),
    [ScmLambdaSimple' (["a"; "c"],
      ScmSeq'
       [ScmApplic' (ScmVar' (VarFree "display"),
         [ScmApplic' (ScmVar' (VarFree "format"),
           [ScmConst' (ScmString "a = ~a~%"); ScmVar' (VarParam ("a", 0))])]);
        ScmApplic' (ScmVar' (VarFree "display"),
         [ScmApplic' (ScmVar' (VarFree "format"),
           [ScmConst' (ScmString "b = ~a~%");
            ScmBoxGet' (VarBound ("b", 0, 1))])]);
        ScmApplic' (ScmVar' (VarFree "display"),
         [ScmApplic' (ScmVar' (VarFree "format"),
           [ScmConst' (ScmString "c = ~a~%"); ScmVar' (VarParam ("c", 1))])]);
        ScmApplicTP' (ScmVar' (VarFree "+"),
         [ScmVar' (VarParam ("a", 0)); ScmBoxGet' (VarBound ("b", 0, 1));
          ScmVar' (VarParam ("c", 1))])]);
     ScmLambdaSimple' ([],
      ScmSeq'
       [ScmApplic' (ScmVar' (VarFree "display"),
         [ScmApplic' (ScmVar' (VarFree "format"),
           [ScmConst' (ScmString "a = ~a~%");
            ScmBoxGet' (VarBound ("a", 0, 0))])]);
        ScmApplic' (ScmVar' (VarFree "display"),
         [ScmApplic' (ScmVar' (VarFree "format"),
           [ScmConst' (ScmString "b = ~a~%");
            ScmBoxGet' (VarBound ("b", 0, 1))])]);
        ScmApplic' (ScmVar' (VarFree "display"),
         [ScmApplic' (ScmVar' (VarFree "format"),
           [ScmConst' (ScmString "c = ~a~%");
            ScmBoxGet' (VarBound ("c", 0, 2))])]);
        ScmBoxSet' (VarBound ("a", 0, 0),
         ScmConst' (ScmNumber (ScmRational (0, 1))));
        ScmBoxSet' (VarBound ("b", 0, 1),
         ScmConst' (ScmNumber (ScmRational (0, 1))));
        ScmBoxSet' (VarBound ("c", 0, 2),
         ScmConst' (ScmNumber (ScmRational (0, 1))))]);
     ScmLambdaSimple' (["aa"; "bb"; "cc"],
      ScmSeq'
       [ScmBoxSet' (VarBound ("a", 0, 0), ScmVar' (VarParam ("aa", 0)));
        ScmSet' (VarParam ("bb", 1), ScmBoxGet' (VarBound ("b", 0, 1)));
        ScmBoxSet' (VarBound ("c", 0, 2), ScmVar' (VarParam ("cc", 2)));
        ScmApplicTP' (ScmVar' (VarFree "list"),
         [ScmBoxGet' (VarBound ("a", 0, 0));
          ScmBoxGet' (VarBound ("b", 0, 1));
          ScmBoxGet' (VarBound ("c", 0, 2))])])])]);
          ScmLambdaSimple' (["x"],
 ScmLambdaSimple' (["y"],
  ScmSeq'
   [ScmSet' (VarBound ("x", 0, 0),
     ScmConst' (ScmNumber (ScmRational (1, 1))));
    ScmLambdaSimple' ([], ScmVar' (VarBound ("x", 1, 0)))]));
    ScmLambdaSimple' ([],
 ScmSeq'
  [ScmApplic' (ScmLambdaSimple' ([], ScmVar' (VarFree "x")), []);
   ScmApplic'
    (ScmLambdaSimple' (["x"],
      ScmSeq'
       [ScmSet' (VarParam ("x", 0), ScmBox' (VarParam ("x", 0)));
        ScmBoxSet' (VarParam ("x", 0),
         ScmConst' (ScmNumber (ScmRational (104, 1))));
        ScmLambdaSimple' ([], ScmBoxGet' (VarBound ("x", 0, 0)))]),
    [ScmConst' (ScmNumber (ScmRational (104, 1)))]);
   ScmApplicTP' (ScmLambdaOpt' ([], "x", ScmVar' (VarParam ("x", 0))),
    [ScmConst' (ScmNumber (ScmRational (104, 1)))])]);
    ScmLambdaSimple' (["x"],
 ScmLambdaSimple' (["y"],
  ScmSeq'
   [ScmSet' (VarBound ("x", 0, 0),
     ScmConst' (ScmNumber (ScmRational (1, 1))));
    ScmLambdaSimple' ([], ScmVar' (VarBound ("x", 1, 0)))]))];;

let input_expected_lst = List.combine inputs outputs;;

let outputs = List.map (fun (input,output) -> expr'_eq (tester input) output) input_expected_lst;;

let rec index_tests has_passed_lst idx acc_lst = match has_passed_lst with
    | [] -> List.rev acc_lst
    | x::xs -> index_tests xs (idx+1) ((x,idx)::acc_lst);;

let outputs = index_tests outputs 1 [];;


List.map (fun (has_passed,index) -> 
                                        if has_passed then Printf.printf "%s%d\n" "PASS: Test#" index
                                        else Printf.printf "%s%d\n" "FAIL: Test#" index
                                            ) outputs














