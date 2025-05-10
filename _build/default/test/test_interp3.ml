open OUnit2
open Interp3

(* Eval tests: assumes eval_expr : dyn_env -> expr -> value *)

let eval_expr_tests =
  "eval_expr test suite" >:::

  [
    (* Arithmetic operators *)
    "add ints" >:: (fun _ ->
      assert_equal (VInt 5) (eval_expr Env.empty (Bop (Add, Int 2, Int 3)))
    );

    "sub ints" >:: (fun _ ->
      assert_equal (VInt (-1)) (eval_expr Env.empty (Bop (Sub, Int 2, Int 3)))
    );

    "mul ints" >:: (fun _ ->
      assert_equal (VInt 6) (eval_expr Env.empty (Bop (Mul, Int 2, Int 3)))
    );

    "div ints" >:: (fun _ ->
      assert_equal (VInt 2) (eval_expr Env.empty (Bop (Div, Int 6, Int 3)))
    );

    "mod ints" >:: (fun _ ->
      assert_equal (VInt 1) (eval_expr Env.empty (Bop (Mod, Int 7, Int 3)))
    );

    (* Float operators *)
    "add floats" >:: (fun _ ->
      match eval_expr Env.empty (Bop (AddF, Float 2.0, Float 3.5)) with
      | VFloat f -> assert_equal ~cmp:(cmp_float ~epsilon:1e-6) 5.5 f
      | _ -> assert_failure "Expected VFloat"
    );

    "pow floats" >:: (fun _ ->
      match eval_expr Env.empty (Bop (PowF, Float 2.0, Float 3.0)) with
      | VFloat f -> assert_equal ~cmp:(cmp_float ~epsilon:1e-6) 8.0 f
      | _ -> assert_failure "Expected VFloat"
    );

    (* Booleans and comparisons *)
    "and true" >:: (fun _ ->
      assert_equal (VBool true) (eval_expr Env.empty (Bop (And, Bool true, Bool true)))
    );

    "or false" >:: (fun _ ->
      assert_equal (VBool true) (eval_expr Env.empty (Bop (Or, Bool true, Bool false)))
    );

    "eq ints" >:: (fun _ ->
      assert_equal (VBool true) (eval_expr Env.empty (Bop (Eq, Int 5, Int 5)))
    );

    "neq ints" >:: (fun _ ->
      assert_equal (VBool true) (eval_expr Env.empty (Bop (Neq, Int 5, Int 6)))
    );

    (* Lists and Options *)
    "list cons" >:: (fun _ ->
      assert_equal (VList [VInt 1; VInt 2]) 
        (eval_expr Env.empty (Bop (Cons, Int 1, Bop (Cons, Int 2, Nil))))
    );

    "option some" >:: (fun _ ->
      assert_equal (VSome (VInt 5)) (eval_expr Env.empty (ESome (Int 5)))
    );

    "option match none" >:: (fun _ ->
      assert_equal (VInt 0)
        (eval_expr Env.empty 
          (OptMatch { matched = ENone; some_name = "x"; some_case = Int 1; none_case = Int 0 }))
    );

    "option match some" >:: (fun _ ->
      assert_equal (VInt 1)
        (eval_expr Env.empty 
          (OptMatch { matched = ESome (Int 5); some_name = "x"; some_case = Int 1; none_case = Int 0 }))
    );

    (* Function comparison must fail *)
    "compare function fails" >:: (fun _ ->
      assert_raises CompareFunVals (fun () -> 
        ignore (eval_expr Env.empty (Bop (Eq, Fun ("x", None, Var "x"), Fun ("y", None, Var "y"))))
      )
    );

"simple recursion" >:: (fun _ ->
  let fact = 
    Let {
      is_rec = true;
      name = "fact";
      binding = Fun ("n", None,
        If (
          Bop (Eq, Var "n", Int 0),
          Int 1,
          Bop (Mul, Var "n", App (Var "fact", Bop (Sub, Var "n", Int 1)))
        )
      ); (* close Fun normally, no extra closing for binding *)
      body = App (Var "fact", Int 5)
    }
  in
  assert_equal (VInt 120) (eval_expr Env.empty fact)
);


    
  ]


  let tests =
    "all test suites" >::: [
      eval_expr_tests;
    ]
  ;;
  
  let _ = run_test_tt_main tests
  