include Utils

let parse (s : string) : prog option =
  match Parser.prog Lexer.read (Lexing.from_string s) with
  | prog -> Some prog
  | exception _ -> None

type subst = (ident * ty) list

(* get the free variables a type t*)
let get_free_var (ty : ty) : VarSet.t =
  let rec go ty = 
    match ty with
    | TUnit | TInt | TFloat | TBool -> VarSet.empty
    | TVar id -> VarSet.singleton id
    | TList ty -> go ty
    | TOption ty -> go ty
    | TPair (ty1, ty2) -> VarSet.union (go ty1) (go ty2)
    | TFun (ty1, ty2) -> VarSet.union (go ty1) (go ty2)
  in go ty 


(* subsutite the variables with the types *)
let substitute (s: subst) (ty: ty) : ty = 
  let rec go ty = 
    match ty with
    | TUnit | TInt | TFloat | TBool -> ty
    | TVar id -> 
      let n_id = List.assoc_opt id s in 
            (match n_id with
            | Some ty' -> go ty'
            | None -> TVar id)
    | TList cur_ty -> 
            let n_type = go cur_ty 
            in TList (n_type)
    | TOption cur_ty -> 
            let n_type = go cur_ty 
            in TOption (n_type)
    | TPair (ty1, ty2) -> 
            let n_ty1 = go ty1 in
            let n_ty2 = go ty2 in
            TPair (n_ty1, n_ty2)
    | TFun (ty1, ty2) ->  
            let n_ty1 = go ty1 in
            let n_ty2 = go ty2 in
            TFun (n_ty1, n_ty2)
  
  in go ty

  (* to fix *)
let combine_subst (s1: subst) (s2: subst) : subst = 
  let n_s1 = List.map (fun (id, ty) -> (id, substitute s2 ty)) s1 in 
  let n_s2 = List.filter (fun (id, _) -> not ((List.mem_assoc id s1))) s2 in
  n_s1 @ n_s2
(* a substitution is a list of pairs of variable and type *)


(* unify the constraints *)
let unify (cs: constr list) : subst option = 
  let rec go cs acc = 
    match cs with 
    (* base case return empty list *)
    | [] -> Some acc
    
    (* recurse to the rest of the list*)
    | (ty1, ty2) :: rest -> 
      (* if they are equal we skip*)
        if ty1 = ty2 then 
          go rest acc
      else 
        match (ty1, ty2) with 
        | (TVar id, ty) |  (ty, TVar id) -> 
          
          if VarSet.mem id (get_free_var ty) then None
          else 
            let subst1 = [(id, ty)] in
            let rest = List.map (fun (ty1, ty2) -> (substitute [(id, ty)] ty1, substitute [(id, ty)] ty2)) rest in
            go rest (combine_subst subst1 acc)

        | (TList n_ty1, TList n_ty2) -> 
            go ((n_ty1, n_ty2)::rest) acc

        | (TOption n_ty1, TOption n_ty2) ->
             go ((n_ty1, n_ty2)::rest) acc

        | (TPair (n_ty1, n_ty2), TPair (n_ty3, n_ty4)) -> 
            go ((n_ty1, n_ty3)::(n_ty2, n_ty4)::rest) acc

        | (TFun (n_ty1, n_ty2), TFun (n_ty3, n_ty4)) ->
            go ((n_ty1, n_ty3)::(n_ty2, n_ty4)::rest) acc

        | _ -> None 

    
  in go cs [] 

let principle_type (_ty : ty) (_cs : constr list) : ty_scheme option = 
  let unified_cs = unify _cs in 
  match unified_cs with 
  | None -> None 
  | Some s -> 
      let n_ty = substitute s _ty in 
      let free_vars = get_free_var n_ty in 
      Some (Forall (free_vars, n_ty))

let instantiate (Forall (vars, ty)) : ty =
        let subst =
          VarSet.fold (fun v acc -> (v, TVar (gensym ())) :: acc) vars []
        in
        substitute subst ty      
let infer_type (_ctxt: stc_env) (_e : expr) : (ty * constr list) option = 
  let rec go ctxt e  = 
    match e with 
    | Unit -> Some (TUnit, [])
    | Bool _ -> Some (TBool, [])
    | Nil -> 
      let fresh = gensym () in 
      Some (TList (TVar fresh), [])

    | ENone -> 
      let fresh = gensym () in
      Some (TOption (TVar fresh), [])
      
    | Int _ -> Some (TInt, [])
    | Float _  -> Some (TFloat, [])

    | Var ident ->
        (match Env.find_opt ident ctxt with
         | Some scheme -> Some (instantiate scheme, [])
         | None -> None)

    | Assert (Bool false) -> 
      Some (TVar (gensym ()), [])

    | Assert expr -> 
      (match go ctxt expr with
      | None -> None 
      | Some (ty, cs) -> Some (TUnit, (ty, TBool) :: cs)
      )

    | ESome expr -> 
      (match go ctxt expr with
      | None -> None 
      | Some (ty, cs) -> 
          let n_ty = TOption ty in
          Some (n_ty, cs)
      )

    | Bop (bop, expr1, expr2) -> 

      let ty1 = go ctxt expr1 in
      let ty2 = go ctxt expr2 in

      (match (ty1, ty2) with 
      | Some (ty1, cs1), Some (ty2, cs2) -> 
        (match bop with 
         (* Integer arithmetic *)
         | Add | Sub | Mul | Div | Mod -> 
             Some (TInt, (ty1, TInt) :: (ty2, TInt) :: cs1 @ cs2)
         (* Float arithmetic *)
         | AddF | SubF | MulF | DivF | PowF -> 
             Some (TFloat, (ty1, TFloat) :: (ty2, TFloat) :: cs1 @ cs2)
         (* Comparisons: inputs must have same type *)
         | Lt | Lte | Gt | Gte | Eq | Neq -> 
             Some (TBool, (ty1, ty2) :: cs1 @ cs2)
         (* Boolean operations *)
         | And | Or -> 
             Some (TBool, (ty1, TBool) :: (ty2, TBool) :: cs1 @ cs2)
         (* Pair creation *)
         | Comma -> 
             Some (TPair (ty1, ty2), cs1 @ cs2)
         (* List cons: e1 : τ, e2 : TList τ *)
         | Cons ->
             let result_ty = TList ty1 in
             Some (result_ty, (ty2, result_ty) :: cs1 @ cs2))
    | _ -> None)


    | If (cond, expr1, expr2) -> 
      let cond_ty = go ctxt cond in
      let expr1_ty = go ctxt expr1 in
      let expr2_ty = go ctxt expr2 in

      (match (cond_ty, expr1_ty, expr2_ty) with 
      | (Some (ty_cond, cs_cond), Some (ty_e1, cs_e1), Some (ty_e2, cs_e2)) -> 
        Some (ty_e1, (ty_cond, TBool) :: (ty_e1, ty_e2) :: (cs_cond @ cs_e1 @ cs_e2))

      | _ -> None)


    | ListMatch { matched; hd_name; tl_name; cons_case; nil_case } -> 
      (match go ctxt matched with 
      | None -> None
      | Some (ty_matched, cs_matched) -> 

        let alpha = TVar (gensym ()) in 
        let ctxt_hd = 
          Env.add hd_name (Forall (VarSet.empty, alpha)) ctxt in
        let new_ctxt = 
            (Env.add tl_name (Forall (VarSet.empty, TList alpha)) ctxt_hd) in
        let cons_case_ty = go new_ctxt cons_case in
        let nil_case_ty = go ctxt nil_case in

        (match (cons_case_ty, nil_case_ty) with
        | (Some (ty_cons, cs_cons), Some (ty_nil, cs_nil)) -> 
          Some (ty_cons, (ty_matched, TList alpha) :: (ty_cons, ty_nil) :: (cs_matched @ cs_cons @ cs_nil))
        | _ -> None
        )
        
      )

        
    | OptMatch
      { matched : expr
      ; some_name : ident
      ; some_case : expr
      ; none_case : expr
      } ->       
        (match go ctxt matched with 
      | None -> None
      | Some (ty_matched, cs_matched) -> 
        let alpha = TVar (gensym ()) in 
        let new_ctxt = 
          (Env.add some_name (Forall (VarSet.empty, alpha)) ctxt) in 

        let some_case_ty = go new_ctxt some_case in
        let none_case_ty = go ctxt none_case in

        (match (some_case_ty, none_case_ty) with
        | (Some (ty_some, cs_some), Some (ty_none, cs_none)) -> 
          Some (ty_some, (ty_matched, TOption alpha) :: (ty_some, ty_none) :: (cs_matched @ cs_some @ cs_none))
        | _ -> None
        )
        
      )

    | PairMatch
      { matched : expr
      ; fst_name : ident
      ; snd_name : ident
      ; case : expr
      } -> 
        (match go ctxt matched with 
      | None -> None
      | Some (ty_matched, cs_matched) -> 
        let alpha1 = TVar (gensym ()) in 
        let alpha2 = TVar (gensym ()) in 

        let ctxt = 
          Env.add fst_name (Forall (VarSet.empty, alpha1)) ctxt in 
        let new_ctxt =
          (Env.add snd_name (Forall (VarSet.empty, alpha2)) ctxt) in 

        let case_ty = go new_ctxt case in

        (match case_ty with
        | Some (ty_case, cs_case) -> 
          Some (ty_case, (ty_matched, TPair (alpha1, alpha2)) :: (cs_matched @ cs_case))
        | _ -> None
        )
        
      )


    | Fun  (ident, ty_option, expr) ->
      (match ty_option with
      | None -> 
        let alpha = TVar (gensym ()) in 
        let new_ctxt = Env.add ident (Forall (VarSet.empty, alpha)) ctxt in
        let expr_ty = go new_ctxt expr in
        (match expr_ty with
        | None -> None
        | Some (ty, cs) -> 
          let n_ty = TFun (alpha, ty) in
          Some (n_ty, cs)
        )
      | Some t ->
        let new_ctxt = Env.add ident (Forall (VarSet.empty, t)) ctxt in
        let expr_ty = go new_ctxt expr in
        (match expr_ty with
        | None -> None
        | Some (ty, cs) -> 
          let n_ty = TFun (t, ty) in
          Some (n_ty, cs)
        )
      )

      
      


    | App (func, expr) -> 
      let func_ty = go ctxt func in
      let arg_ty = go ctxt expr in

      (match (func_ty, arg_ty) with 
      | (Some (ty_func, cs_func), Some (ty_arg, cs_arg)) -> 
        let alpha = TVar (gensym ()) in 
        let n_ty = TFun (ty_arg, alpha) in
        Some (alpha, (ty_func, n_ty) :: (cs_func @ cs_arg))
      | _ -> None
      )

    | Annot (expr, ty) -> 
      (match go ctxt expr with
      | None -> None 
      | Some (n_ty, cs) -> 
          Some (ty, (n_ty, ty) :: cs)
      )

    | Let { is_rec; name; binding; body } -> 
      if is_rec then 
        let alpha = TVar (gensym ()) in
        let new_ctxt = Env.add name (Forall (VarSet.empty, alpha)) ctxt in
        match go new_ctxt binding with
        | None -> None
        | Some (t1, c1) ->
            (match go new_ctxt body with
            | None -> None
            | Some (t2, c2) -> Some (t2, (t1, alpha) :: c1 @ c2))
      else 
        let binding_ty = go ctxt binding in
        (match binding_ty with
        | None -> None
        | Some (t1, c1) ->
            let new_ctxt = Env.add name (Forall (VarSet.empty, t1)) ctxt in
            match go new_ctxt body with
            | None -> None
            | Some (t2, c2) -> Some (t2, c1 @ c2))


  in go _ctxt _e 

let type_of (_ctxt: stc_env) (_e : expr) : ty_scheme option = 
  match infer_type _ctxt _e with
  | None -> None
  | Some (ty, cs) -> 
    let n_ty = principle_type ty cs in n_ty 



let is_well_typed (_p : prog) : bool =
  let rec go p ctxt = 
    (match p with 
    | [] -> true 
    | { name; binding; is_rec } :: rest -> 
      if is_rec then 
          let alpha = TVar (gensym ()) in
          let new_ctxt = Env.add name (Forall (VarSet.empty, alpha)) ctxt in
          let check_type = type_of new_ctxt binding in
          match check_type with
          | None -> false
          | Some (Forall (_, ty)) -> 
            let unified = unify [(alpha, ty)] in
            (match unified with
            | None -> false
            | Some _ -> 
              let new_ctxt = Env.add name (Forall (get_free_var ty, ty)) ctxt in
              go rest new_ctxt)

      else 
        match type_of ctxt binding with
        | None -> false
        | Some (Forall (_, ty))->
          let new_ctxt = Env.add name (Forall (get_free_var ty, ty)) ctxt in
          go rest new_ctxt)

  in go _p Env.empty 

exception AssertFail
exception DivByZero
exception CompareFunVals

let calculate bop x y = 
  (match bop with 
    | Add -> 
      (match (x, y) with 
      | (VInt x, VInt y ) -> VInt (x + y)
      | exception e -> raise e
      | _ -> assert false )

    | Sub ->    
      (match (x, y) with 
      | (VInt x, VInt y ) -> VInt (x - y)
      | exception e -> raise e
      | _ -> assert false )  

    | Mul -> 
      (match (x, y) with 
      | (VInt x, VInt y ) -> VInt (x * y)
      | exception e -> raise e
      | _ -> assert false )

    | Div -> 
      (match (x, y) with 
      | (VInt x, VInt y ) -> 
        if y <> 0 then VInt (x / y)
        else raise DivByZero
      | exception e -> raise e
      | _ -> assert false )
      
    | Mod -> 
        (match (x, y) with 
        | (VInt x, VInt y ) -> 
          if y <> 0 then VInt (x mod y)
          else raise DivByZero
        | exception e -> raise e
        | _ -> assert false )

    | AddF -> 
        (match (x, y) with 
        | (VFloat x, VFloat y ) -> VFloat (x +. y)
        | exception e -> raise e
        | _ -> assert false )
    | SubF -> 
      (match (x, y) with 
      | (VFloat x, VFloat y ) -> VFloat (x -. y)
      | exception e -> raise e
      | _ -> assert false )
    | MulF -> 
      (match (x, y) with 
      | (VFloat x, VFloat y ) -> VFloat (x *. y)
      | exception e -> raise e
      | _ -> assert false )

    | DivF -> 
        (match (x, y) with 
        | (VFloat x, VFloat y ) -> VFloat (x /. y)
        | exception e -> raise e
        | _ -> assert false )

    | PowF -> 
      (match (x, y) with 
      | (VFloat x, VFloat y ) -> VFloat (x ** y)
      | exception e -> raise e
      | _ -> assert false )

    | Lt ->
      (match (x, y) with 
      | (VClos _, _) | (_, VClos _) -> raise CompareFunVals
      | (x, y) -> VBool (x < y) )

    | Lte -> 
      (match (x, y) with 
      | (VClos _, _) | (_, VClos _) -> raise CompareFunVals
      | (x, y) -> VBool (x <= y) )

    | Gt -> 
      (match (x, y) with 
      | (VClos _, _) | (_, VClos _) -> raise CompareFunVals
      | (x, y) -> VBool (x > y) )

    | Gte -> 
      (match (x, y) with 
      | (VClos _, _) | (_, VClos _) -> raise CompareFunVals
      | (x, y) -> VBool (x >= y) )


    | Eq -> 
      (match (x, y) with 
    
      | (VClos _, _) | (_, VClos _) -> raise CompareFunVals
      | (x, y) -> VBool (x = y) )
      
    | Neq -> 
      (match (x, y) with 
      | (VClos _, _) | (_, VClos _) -> raise CompareFunVals
      | (x, y) -> VBool (x <> y) )


    | And -> 
      (match x with 
      | VClos _ -> raise CompareFunVals
      | VBool false -> VBool false 
      | VBool true -> 
        (match y with 
        | VClos _ -> raise CompareFunVals
        | value -> value)
      | _ -> assert false ) 
    | Or -> 
      (match x with 
          
      | VClos _ -> raise CompareFunVals
      | VBool true -> VBool true 
      | VBool false -> 
        (match y with 
        | VClos _ -> raise CompareFunVals
        | value -> value)

      | _ -> assert false ) 

    | Comma -> VPair (x, y) 

    | Cons ->
      (match y with
      | VList rest -> VList (x :: rest)
      | _ -> assert false)
    )

let eval_expr (_env : dyn_env) (_e : expr) : value = 
  let rec go env expr = 
    (match expr with 
  (* unit variables *)
  | Unit -> VUnit
  | Bool bool -> VBool bool 
  | Nil -> VList []
  | ENone -> VNone
  | Int i -> VInt i
  | Float f -> VFloat f

  (* variable evaluations*)
  | Var x -> 
    (match Env.find_opt x env with 
    | Some v -> v
    | exception e -> raise e
    | _ -> failwith ("Unbound variable: " ^ x)
    )
  | Assert expr -> 
    (match go env expr with 
    | VBool true-> VUnit
    | exception e -> raise e
    | _ -> raise AssertFail )
  | Annot (expr, _ ) -> go env expr 
  | ESome expr -> VSome (go env expr) 

  (* arithmetic *)
  (* | Bop (bop, expr1, expr2) -> 
    let e1_val = go env expr1 in 
    let e2_val = go env expr2 in 
    (match (e1_val, e2_val) with 
    | (VInt _, VInt _) -> calculate bop e1_val e2_val 
    | (VFloat _, VFloat _) -> calculate bop e1_val e2_val 
    
    | exception e -> raise e
    | _ -> assert false 
    ) *)
    (* arithmetic *)
  | Bop (And, expr1, expr2) -> 
    let x = go env expr1 in 
    (match x with 
      | VBool false -> VBool false 
      | VBool true -> 
        let y = go env expr2 in 
        (match y with 
        | VBool b -> VBool b
        | _ -> assert false )

      | VClos _ -> raise CompareFunVals
      | _ -> assert false ) 

    | Bop (Or, expr1, expr2) -> 
        let x = go env expr1 in 
        (match x with 
          | VBool true -> VBool true 
          | VBool false -> 
            let y = go env expr2 in 
            (match y with 
            | VBool b -> VBool b
            | _ -> assert false)
    
          | VClos _ -> raise CompareFunVals
          | _ -> assert false ) 


  | Bop (bop, expr1, expr2) -> 
      let e1_val = go env expr1 in 
      let e2_val = go env expr2 in 
      calculate bop e1_val e2_val 

    

  (* Conditional *)
  | If (cond, expr1, expr2) -> 
    let cond_value = go env cond in 
    (match cond_value with 
    | VBool true -> go env expr1
    | VBool false -> go env expr2
    | exception e -> raise e
    | _ -> assert false)


  | ListMatch
    { matched : expr = expr 
    ; hd_name : ident = hd
    ; tl_name : ident = tl
    ; cons_case : expr = expr1
    ; nil_case : expr = expr2
    }  -> 
      (match go env expr with 
      | VList [] -> go env expr2 
      | VList (h :: t ) -> 
        let new_env = Env.add tl (VList t) (Env.add hd h env) in 
        go new_env expr1
      | exception e -> raise e
      | _ -> assert false 
      
      
      )
  | OptMatch
    { matched : expr = expr
    ; some_name : ident = name
    ; some_case : expr = sn
    ; none_case : expr = nn 
    } -> 
      (match go env expr with 
      | VNone -> go env nn 
      | VSome v -> 
        let new_env = Env.add name v env in 
        go new_env sn
      | exception e -> raise e
      | _ -> assert false )

  | PairMatch
    { matched : expr = expr
    ; fst_name : ident = fst
    ; snd_name : ident = snd
    ; case : expr = c 
    } -> 
      (match go env expr with 
      | VPair (v1, v2) -> 
        let new_env = Env.add snd v2 (Env.add fst v1 env) in 
        go new_env c
      | exception e -> raise e
      | _ -> assert false )

  | Fun (ident, _, expr) -> 
    VClos { name = None; arg = ident; body = expr; env = env }
  
  | App (expr1, expr2)-> 
    let func = go env expr1 in 
    let arg = go env expr2 in 
    (match func with 
    | VClos { name = Some name; arg = x; body = body; env = f_env } -> 
      let new_env = Env.add x arg f_env in 
      let new_env = Env.add name func new_env in 
      go new_env body

    | VClos { name = None; arg = x; body = body; env = f_env } -> 
      let new_env = Env.add x arg f_env in 
      go new_env body
    | exception e -> raise e
    | _ -> assert false )

  | Let
    { is_rec : bool
    ; name : ident
    ; binding : expr
    ; body : expr
    } -> 
      let binding_value = go env binding in
      let new_env =
        if is_rec then
          match binding_value with
          | VClos clos ->
              (* make recursive by giving it its own name *)
              let new_env = Env.add name (VClos { clos with name = Some name }) env in
              new_env
          | _ ->
              (* not a function — just bind normally *)
              Env.add name binding_value env
        else
          Env.add name binding_value env
      in
      go new_env body
    )
    
in go _env _e 


let eval p =
  let rec nest = function
    | [] -> Unit
    | [{is_rec;name;binding}] -> Let {is_rec;name;binding;body = Var name}
    | {is_rec;name;binding} :: ls -> Let {is_rec;name;binding;body = nest ls}
  in eval_expr Env.empty (nest p)

let interp input =
  match parse input with
  | Some prog ->
    if is_well_typed prog
    then Ok (eval prog)
    else Error TypeError
  | None -> Error ParseError
