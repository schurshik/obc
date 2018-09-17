(* obc *)
(* obc.ml *)
(* Developer: Branitskiy Alexander <schurshik@yahoo.com> *)

open Core.Std
open Core_extended.Std
open Core_extended.Readline (* readline *)
open Obclexer
open Libevent

type qfloat_num = QFloatNum of Obctypes.qfloat (* Zarith *)

exception BreakLoop
exception ContinueLoop
exception QuitProgram
exception ExitProgram of int
exception IncorrectCall of string
exception ReturnFromFunction of qfloat_num

let create_hash () =
  Hashtbl.create ~hashable:String.hashable ()

let interprete_program ?(warn=false) prog g_vars_ref g_funs_ref =
  let add_to_hash ?(if_exists_add=true) h_ref p =
    if not if_exists_add then
      match Hashtbl.find !h_ref (fst p) with
      | Some _ -> ()
      | None -> Hashtbl.replace !h_ref ~key:(fst p) ~data:(snd p)
    else
      Hashtbl.replace !h_ref ~key:(fst p) ~data:(snd p)
  in
  let add_to_g_vars ?(if_exists_add=true) p =
    if if_exists_add && (fst p) = "ibase" then
      ibase_ref := Q.to_int (fst (snd p));
    add_to_hash ~if_exists_add:if_exists_add g_vars_ref p
  in
  let add_to_g_funs ?(if_exists_add=true) p =
    add_to_hash ~if_exists_add:if_exists_add g_funs_ref p
  in
  let rcv_from_hash h k =
    Hashtbl.find h k
  in
  let rcv_from_g_vars k =
    match rcv_from_hash !g_vars_ref k with
    | Some f -> f
    | None ->
       begin
         if warn then
           Printf.printf "The variable '%s' is not initialized\n" k;
         make_qval "0" 0
       end
  in
  let create_arr_regexp arr_name arr_dim =
    Str.regexp (Printf.sprintf "^%s%s:[0-9]+$" arr_name (String.concat ~sep:"" (List.init arr_dim ~f:(fun _ -> "\\[\\([0-9]+\\)\\]")))) in
  let add_to_vars_by_ref vars_ref p =
    if not (phys_equal vars_ref g_vars_ref) then
      let (k, _) = p in
      match rcv_from_hash !vars_ref k with
      | Some f -> add_to_hash vars_ref p
      | None ->
         begin
           if warn then
             Printf.printf "The variable '%s' is not initialized\n" k;
           match String.split k ~on:':' with
           | [v; d] -> let arr_name = Str.replace_first (Str.regexp "^\\([^[]+\\)\\[.*$") "\\1" v in
                       let arr_dim = Int.of_string d in
                       let reg_exp = create_arr_regexp arr_name arr_dim in
                       if List.exists ~f:(fun x -> Str.string_match reg_exp x 0) (Hashtbl.keys !vars_ref) then
                           add_to_hash vars_ref p
                       else
                         add_to_g_vars p
           | _ -> add_to_g_vars p
         end
    else
      add_to_g_vars p
  in
  let rcv_from_vars vars k =
    match rcv_from_hash vars k with
    | Some f -> f
    | None ->
       begin
         match String.split k ~on:':' with
         | [v; d] -> let arr_name = Str.replace_first (Str.regexp "^\\([^[]+\\)\\[.*$") "\\1" v in
                     let arr_dim = Int.of_string d in
                     let reg_exp = create_arr_regexp arr_name arr_dim in
                     if List.exists ~f:(fun x -> Str.string_match reg_exp x 0) (Hashtbl.keys vars) then
                       begin
                         if warn then
                           Printf.printf "The variable '%s' is not initialized\n" k;
                         make_qval "0" 0
                       end
                     else
                       rcv_from_g_vars k
         | _ -> rcv_from_g_vars k
       end
  in
  let rcv_from_g_funs k =
    match rcv_from_hash !g_funs_ref k with
    | Some f -> f
    | None -> raise (IncorrectCall (Printf.sprintf "Function %s is not defined" k))
  in
  let rcv_expr_name ?(str_inds=[]) named_expr =
    match named_expr with
    | Obctypes.Value l -> l
    | Obctypes.ValueAtIndex (l, _) -> let inds_str = List.map ~f:(fun s -> Printf.sprintf "[%s]" s) str_inds |> String.concat ~sep:"" in
                                      Printf.sprintf "%s%s:%d" l inds_str (List.length str_inds)
    | Obctypes.Scale -> "scale" (* Obclexer.scale_token *)
    | Obctypes.Ibase -> "ibase" (* Obclexer.ibase_token *)
    | Obctypes.Obase -> "obase" (* Obclexer.obase_token *)
  in
  let qval_of_qfloat_num f =
    match f with
    | QFloatNum n -> n
  in
  let qfloat_num_of_qval n =
    QFloatNum n
  in
  let qfloat_num_to_string f =
    let (q, s) = match f with
      | QFloatNum n -> n in
    if Q.equal q Q.zero then
      "0"
    else
      let precision = Int.max s (Q.to_int (fst (rcv_from_g_vars "scale"))) in
      let ins_symbol smb pos str = Printf.sprintf "%s%c%s" (String.sub str 0 pos) smb (String.sub str pos ((String.length str) - pos)) in
      let aux_string = Z.to_string (Z.div (Z.mul (Q.num q) (Z.of_string ("1" ^ (String.make precision '0')))) (Q.den q)) in
      let res_string = if precision <> 0 then ins_symbol '.' ((String.length aux_string) - precision) aux_string else aux_string in
      (* let rec decode_num_between_bases n from_base to_base = *)
      (*   if n = 0 then 0 else from_base * (decode_num_between_bases (n / to_base) from_base to_base) + (n mod to_base) *)
      let rec decode_z10_to_str ?(first_call=true) n to_base =
        if Z.equal n Z.zero
        then
          (if first_call then "0" else "")
        else
          let (div_val, rem_val) = Z.div_rem n (Z.of_int to_base) in
          let d = (Z.to_int rem_val) - 10 in
          let suff = if d >= 0 then Char.to_string (match Char.of_int ((Char.to_int 'A') + d) with | Some a -> a | None -> '0')
                     else Z.to_string rem_val in
          (decode_z10_to_str ~first_call:false div_val to_base) ^ suff in
      let trim_zero ?(apply_fun=ident) str =
        let r = Str.regexp "^\\([0-9]+\\)\\.\\([0-9]*[1-9]\\)0+$" in
        if Str.string_match r str 0
        then
          Printf.sprintf "%s.%s" (apply_fun (Str.replace_first r "\\1" str)) (apply_fun (Str.replace_first r "\\2" str))
        else
          let r = Str.regexp "^\\([0-9]+\\)\\.0+$" in
          if Str.string_match r str 0 then
            apply_fun (Str.replace_first r "\\1" str)
          else
            apply_fun str in
      let obase = Q.to_int (fst (rcv_from_g_vars "obase")) in
      trim_zero ~apply_fun:(if obase = 10 then ident else fun s -> decode_z10_to_str (Z.of_string s) obase) res_string
  in
  let print_qfloat_num f =
    Printf.printf "%s\n" (qfloat_num_to_string f)
  in
  let trunc_q_to_z q= Z.div (Q.num q) (Q.den q) in
  List.iter ~f:(add_to_g_vars ~if_exists_add:false) [((rcv_expr_name Obctypes.Scale), (make_qval "0" 0));
                                                     ((rcv_expr_name Obctypes.Ibase), (make_qval "10" 0));
                                                     ((rcv_expr_name Obctypes.Obase), (make_qval "10" 0))];
  match prog with
  | Obctypes.Program p ->
     begin
       let interprete_input_item in_item =
         match in_item with
         | Obctypes.InputItem i ->
            begin
              let rec interprete_statement ?(l_vars_ref=g_vars_ref) st =
                let rec interprete_expression ?(to_print=false) l_vars_ref expr =
                  let rec interprete_named_expression ?(extract_val=true) l_vars_ref named_expr =
                    let expr_name =
                      match named_expr with
                      | Obctypes.ValueAtIndex (l, exprs) ->
                         let str_inds = List.map ~f:(fun e ->
                                                     let val_to_int_string q =
                                                       Printf.sprintf "%s" (Z.to_string (trunc_q_to_z q))
                                                     in
                                                     val_to_int_string (fst (qval_of_qfloat_num (interprete_expression l_vars_ref e)))) exprs in
                         rcv_expr_name ~str_inds:str_inds named_expr
                      | _ -> rcv_expr_name named_expr
                    in
                    (expr_name, if extract_val then rcv_from_vars !l_vars_ref expr_name else make_qval "0" 0)
                  in
                  match expr with
                  | Obctypes.NamedExpr v ->
                     let f = qfloat_num_of_qval (snd (interprete_named_expression l_vars_ref v)) in
                     if to_print then
                       print_qfloat_num f;
                     f
                  | Obctypes.Number num ->
                     let f = qfloat_num_of_qval num in
                     if to_print then
                       print_qfloat_num f;
                     f
                  | Obctypes.Call (f, a) ->
                     let f =
                       begin
                         let (fun_params, fun_vars, fun_body) = rcv_from_g_funs f in
                         let l_vars = create_hash () in (* modeling the function stack *)
                         begin
                           match (fun_params, a) with (* simple unification :) *)
                           | (Obctypes.OptParameters param_names, Obctypes.OptArguments arg_values) ->
                              let param_arg_pairs = List.zip param_names arg_values in
                              match param_arg_pairs with
                              | Some l ->
                                 let add_to_l_vars p =
                                   match p with
                                   | (Obctypes.Var s, Obctypes.ArgExpr e) ->
                                      let n = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                                      add_to_hash (ref l_vars) (s, n)
                                   | (Obctypes.Arr (dst_r, dst_d), Obctypes.ArgArr (src_r, src_d)) ->
                                      if dst_d <> src_d
                                      then
                                        raise (IncorrectCall (Printf.sprintf "Array dimension mismatch in function %s" f))
                                      else
                                        let reg_exp = create_arr_regexp src_r src_d in
                                        if List.exists ~f:(fun k -> Str.string_match reg_exp k 0) (Hashtbl.keys !l_vars_ref) then
                                          Hashtbl.iter ~f:(fun ~key:k ~data:d ->
                                                           if Str.string_match reg_exp k 0 then
                                                             let inds = List.map ~f:(fun y -> Int.of_string (Str.replace_first reg_exp ("\\" ^ y) k))
                                                                                 (List.init src_d ~f:(fun x -> Int.to_string (x + 1))) in
                                                             let inds_str = String.concat ~sep:"" (List.map ~f:(fun x -> Printf.sprintf "[%d]" x) inds) in
                                                             add_to_hash (ref l_vars) ((Printf.sprintf "%s%s:%d" dst_r inds_str dst_d), d)) !l_vars_ref
                                        else
                                            if warn then
                                              Printf.printf "The array '%s%s' is not initialized\n" src_r (String.concat ~sep:"" (List.init src_d ~f:(fun _ -> "[]")));
                                            let inds_str = String.concat ~sep:"" (List.init dst_d ~f:(fun _ -> "[0]")) in
                                            add_to_hash (ref l_vars) (Printf.sprintf "%s%s:%d" dst_r inds_str dst_d, make_qval "0" 0)
                                   | (_, _) -> raise (IncorrectCall (Printf.sprintf "Parameter type mismatch in function %s" f))
                                 in
                                 List.iter ~f:add_to_l_vars l
                              | None -> raise (IncorrectCall (Printf.sprintf "Parameter number mismatch in function %s" f))
                         end;
                         begin
                           match fun_vars with
                           | Obctypes.AutoDefine l ->
                              let add_to_l_vars p =
                                match p with
                                | (Obctypes.Var s, n) -> add_to_hash (ref l_vars) (s, n)
                                | (Obctypes.Arr (s, dim), n) -> let inds_str = String.concat ~sep:"" (List.init dim ~f:(fun _ -> "[0]")) in
                                                                add_to_hash (ref l_vars) (Printf.sprintf "%s%s:%d" s inds_str dim, n)
                              in
                              List.iter ~f:(fun s -> add_to_l_vars (s, (make_qval "0" 0))) l;
                         end;
                         begin
                           try
                             begin
                               match fun_body with
                               | Obctypes.Statements l -> List.iter ~f:(interprete_statement ~l_vars_ref:(ref l_vars)) l
                             end;
                             qfloat_num_of_qval (make_qval "0" 0)
                           with
                           | ReturnFromFunction r -> r
                         end;
                       end
                     in
                     if to_print then
                       print_qfloat_num f;
                     f
                  | Obctypes.LogApply (o, e1, e2) ->
                     begin
                       let n1 = qval_of_qfloat_num (interprete_expression l_vars_ref e1) in
                       let n2 = qval_of_qfloat_num (interprete_expression l_vars_ref e2) in
                       let z = Q.zero in
                       let lambda_op =
                         match o with
                         | Obctypes.Or -> fun x y -> Q.of_int (if not (Q.equal x z) || not (Q.equal y z) then 1 else 0)
                         | Obctypes.And -> fun x y -> Q.of_int (if not (Q.equal x z) && not (Q.equal y z) then 1 else 0)
                       in
                       let f = qfloat_num_of_qval (lambda_op (fst n1) (fst n2), 0) in
                       if to_print then
                         print_qfloat_num f;
                       f
                     end
                  | Obctypes.InvertBool e ->
                     begin
                       let n = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                       let z = Q.zero in
                       let f = qfloat_num_of_qval (make_qval (if Q.equal (fst n) z then "1" else "0") 0) in
                       if to_print then
                         print_qfloat_num f;
                       f
                     end
                  | Obctypes.Apply (o, e1, e2) ->
                     begin
                       let n1 = qval_of_qfloat_num (interprete_expression l_vars_ref e1) in
                       let n2 = qval_of_qfloat_num (interprete_expression l_vars_ref e2) in
                       let lambda_op =
                         match o with
                         | Obctypes.Plus -> Q.add
                         | Obctypes.Minus -> Q.sub
                         | Obctypes.Mul -> Q.mul
                         | Obctypes.Div -> Q.div
                         | Obctypes.Mod ->
                            fun x y -> let num = Z.rem (trunc_q_to_z x) (trunc_q_to_z y) in
                                       let den = Z.of_string "1" in
                                       Q.make num den
                         | Obctypes.Pow ->
                            fun x y -> let num = Z.pow (trunc_q_to_z x) (Z.to_int (trunc_q_to_z y)) in
                                       let den = Z.of_string "1" in
                                       Q.make num den
                       in
                       let f = qfloat_num_of_qval (lambda_op (fst n1) (fst n2), Int.max (snd n1) (snd n2)) in
                       if to_print then
                         print_qfloat_num f;
                       f
                     end
                  | Obctypes.Compare (o, e1, e2) ->
                     begin
                       let n1 = qval_of_qfloat_num (interprete_expression l_vars_ref e1) in
                       let n2 = qval_of_qfloat_num (interprete_expression l_vars_ref e2) in
                       let lambda_op =
                         match o with
                         | Obctypes.Eq -> Q.equal
                         | Obctypes.Ne -> fun x y -> not (Q.equal x y)
                         | Obctypes.Le -> Q.leq
                         | Obctypes.Ge -> Q.geq
                         | Obctypes.Lt -> Q.lt
                         | Obctypes.Gt -> Q.gt
                       in
                       let f = qfloat_num_of_qval (make_qval (if lambda_op (fst n1) (fst n2) then "1" else "0") 0) in
                       if to_print then
                         print_qfloat_num f;
                       f
                     end
                  | Obctypes.InvertSign e ->
                     begin
                       let n = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                       let f = qfloat_num_of_qval (Q.sub Q.zero (fst n), (snd n)) in
                       if to_print then
                         print_qfloat_num f;
                       f
                     end
                  | Obctypes.PreAssign (o, v) ->
                     begin
                       let (var_name, var_val) = interprete_named_expression l_vars_ref v in
                       let lambda_op =
                         match o with
                         | Obctypes.Incr -> fun x -> Q.add x (Q.of_string "1")
                         | Obctypes.Decr -> fun x -> Q.sub x (Q.of_string "1")
                       in
                       add_to_vars_by_ref l_vars_ref (var_name, (lambda_op (fst var_val), snd var_val));
                       let f = qfloat_num_of_qval (rcv_from_vars !l_vars_ref var_name) in
                       if to_print then
                         print_qfloat_num f;
                       f
                     end
                  | Obctypes.PostAssign (o, v) ->
                     begin
                       let (var_name, var_val) = interprete_named_expression l_vars_ref v in
                       let lambda_op =
                         match o with
                         | Obctypes.Incr -> fun x -> Q.add x (Q.of_string "1")
                         | Obctypes.Decr -> fun x -> Q.sub x (Q.of_string "1")
                       in
                       add_to_vars_by_ref l_vars_ref (var_name, (lambda_op (fst var_val), snd var_val));
                       let f = qfloat_num_of_qval var_val in
                       if to_print then
                         print_qfloat_num f;
                       f
                     end
                  | Obctypes.Assign (o, v, e) ->
                     begin
                       let expr_val = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                       let (var_name, var_val) = interprete_named_expression ~extract_val:(match o with | Obctypes.OpAssign -> false | _ -> true) l_vars_ref v
                       in
                       let lambda_op =
                         match o with
                         | Obctypes.OpAssign -> fun _ y -> y
                         | Obctypes.PlusAssign -> Q.add
                         | Obctypes.MinusAssign -> Q.sub
                         | Obctypes.MulAssign -> Q.mul
                         | Obctypes.DivAssign -> Q.div
                         | Obctypes.ModAssign ->
                            fun x y -> let num = Z.rem (trunc_q_to_z x) (trunc_q_to_z y) in
                                       let den = Z.of_string "1" in
                                       Q.make num den
                         | Obctypes.PowAssign ->
                            fun x y -> let num = Z.pow (trunc_q_to_z x) (Z.to_int (trunc_q_to_z y)) in
                                       let den = Z.of_string "1" in
                                       Q.make num den
                       in
                       add_to_vars_by_ref l_vars_ref (var_name, (lambda_op (fst var_val) (fst expr_val), Int.max (snd var_val) (snd expr_val)));
                       qfloat_num_of_qval (rcv_from_vars !l_vars_ref var_name)
                     end
                  | Obctypes.Ternary (e1, e2, e3) ->
                     let expr1_val = qval_of_qfloat_num (interprete_expression l_vars_ref e1) in
                     let f  = interprete_expression l_vars_ref (if not (Q.equal (fst expr1_val) Q.zero) then e2 else e3) in
                     if to_print then
                       print_qfloat_num f;
                     f
                  | Obctypes.Length e ->
                     let expr_val = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                     let l = make_qval (Int.to_string (String.length (qfloat_num_to_string (qfloat_num_of_qval expr_val)))) 0 in
                     let f = qfloat_num_of_qval l in
                     if to_print then
                       print_qfloat_num f;
                     f
                  | Obctypes.Sqrt e ->
                     let expr_val = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                     let precision = Int.max (Q.to_int (fst (rcv_from_g_vars "scale"))) (snd expr_val) in
                     let aux_mul = Q.mul (fst expr_val) (Q.of_string ("1" ^ (String.make (2 * precision) '0'))) in
                     let aux_sqrt = Z.sqrt (trunc_q_to_z aux_mul) in
                     let s = (Q.make aux_sqrt (Z.of_string ("1" ^ (String.make precision '0'))), precision) in
                     let f = qfloat_num_of_qval s in
                     if to_print then
                       print_qfloat_num f;
                     f
                  | Obctypes.ScaleWithArg e ->
                     let expr_val = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                     let s = make_qval (Int.to_string (snd expr_val)) 0 in
                     let f = qfloat_num_of_qval s in
                     if to_print then
                       print_qfloat_num f;
                     f
                  | Obctypes.Truncate e ->
                     let expr_val = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                     let t = (Q.make (trunc_q_to_z (fst expr_val)) (Z.of_string "1"), 0) in
                     let f = qfloat_num_of_qval t in
                     if to_print then
                       print_qfloat_num f;
                     f
                in
                match st with
                | Obctypes.Expr e -> let _ = interprete_expression l_vars_ref ~to_print:true e in ()
                | Obctypes.String s -> Printf.printf "%s\n" s
                | Obctypes.Break -> raise BreakLoop
                | Obctypes.Continue -> raise ContinueLoop
                | Obctypes.Quit -> raise QuitProgram
                | Obctypes.Exit r ->
                   let n = match r with
                     | Obctypes.Empty -> qfloat_num_of_qval (make_qval "0" 0)
                     | Obctypes.RetExpr e -> interprete_expression l_vars_ref e
                   in
                   raise (ExitProgram (Z.to_int (trunc_q_to_z (fst (qval_of_qfloat_num n)))))
                | Obctypes.Return r ->
                   let n = match r with
                     | Obctypes.Empty -> qfloat_num_of_qval (make_qval "0" 0)
                     | Obctypes.RetExpr e -> interprete_expression l_vars_ref e
                   in
                   raise (ReturnFromFunction n)
                | Obctypes.For (e1, e2, e3, s) ->
                   begin
                     let interprete_for expr1 expr2 expr3 st =
                       let _ = interprete_expression l_vars_ref expr1 in
                       let n = qval_of_qfloat_num (interprete_expression l_vars_ref expr2) in
                       if not (Q.equal (fst n) Q.zero) then
                         try
                           while true do
                             begin
                               try
                                 interprete_statement ~l_vars_ref:l_vars_ref st;
                               with
                               | ContinueLoop -> ()
                             end;
                             let _ = interprete_expression l_vars_ref expr3 in
                             let n = qval_of_qfloat_num (interprete_expression l_vars_ref expr2) in
                             if Q.equal (fst n) Q.zero then
                               raise BreakLoop
                           done
                         with
                         | BreakLoop -> ()
                     in
                     interprete_for e1 e2 e3 s
                   end
                | Obctypes.If (e, s) ->
                   let n = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                   if not (Q.equal (fst n) Q.zero) then interprete_statement ~l_vars_ref:l_vars_ref s
                | Obctypes.IfElse (e, s1, s2) ->
                   let n = qval_of_qfloat_num (interprete_expression l_vars_ref e) in
                   interprete_statement ~l_vars_ref:l_vars_ref (if not (Q.equal (fst n) Q.zero) then s1 else s2)
                | Obctypes.While (e, s) ->
                   begin
                     let interprete_while expr st =
                       let n = qval_of_qfloat_num (interprete_expression l_vars_ref expr) in
                       if not (Q.equal (fst n) Q.zero) then
                         try
                           while true do
                             begin
                               try
                                 interprete_statement ~l_vars_ref:l_vars_ref st;
                               with
                               | ContinueLoop -> ()
                             end;
                             let n = qval_of_qfloat_num (interprete_expression l_vars_ref expr) in
                             if Q.equal (fst n) Q.zero then
                               raise BreakLoop
                           done
                         with
                         | BreakLoop -> ()
                     in
                     interprete_while e s
                   end
                | Obctypes.StatementList sl -> List.iter ~f:(interprete_statement ~l_vars_ref:l_vars_ref) sl
              in
              List.iter ~f:interprete_statement i
            end
         | Obctypes.DefFunc (l, p, d, s) -> add_to_g_funs (l, (p, d, s))
       in
       List.iter ~f:interprete_input_item p (* List.iter is overloaded by Core.Std *)
     end

let main () =
  let force_interactive_mode = ref false in
  let enable_warnings = ref false in
  let print_version = ref false in
  let in_file_list = ref [] in
  let usage = ref "" (* initialized later *) in
  let version = "0.1" in
  let parse_args args =
    let specs = [("-h|-help|--help", Arg.Unit (fun () -> raise (Arg.Help !usage)), "show help info and exit");
                 ("-i|-interactive|--interactive", Arg.Unit (fun () -> force_interactive_mode := true), "force interactive mode");
                 ("-w|-warnings|--warnings", Arg.Unit (fun () -> enable_warnings := true), "enable warnings");
                 ("-v|-version|--version", Arg.Unit (fun () -> print_version := true), "print version and exit")] in
    let real_specs = (List.fold_left ~init:[] ~f:(fun a b -> let (l, s, d) = b in a @ (List.map ~f:(fun x -> (x, s, d)) l))
                                     (List.map ~f:(fun s -> let (k, s, d) = s in (Str.split (Str.regexp "|") k), s, d) specs)) in
    usage :=
      begin
      let max_opt_k_len = List.max_elt (List.map specs ~f:(fun a -> let (k, _, _) = a in String.length(k)))
                                       ~cmp:(fun a b -> if a > b then 1 else if a < b then -1 else 0) in
      let max_k_len =
        match max_opt_k_len with
        | Some n -> n
        | None -> 0 in
      (List.fold_left specs ~init:("usage: obc " ^ version ^ " [options] [file ...]\n")
                      ~f:(fun a e -> let (k, _, d) = e in
                                    a ^ (Printf.sprintf "  %s%s%s\n" k (String.make (max_k_len + 1 - String.length k) ' ') d))) ^
        "Branitskiy Alexander\n"
      end;
    Arg.parse_argv ?current:(Some (ref 0)) args real_specs (fun x -> if Str.string_match (Str.regexp "^-.+$") x 0 then
                                                                         () (* raise (Arg.Bad ("unknown input argument: " ^ x)) *)
                                                                     else
                                                                         in_file_list := !in_file_list @ [x]) !usage
  in
  begin
    try
      parse_args Sys.argv
    with
    | Arg.Bad s -> let reg_exp = Str.regexp "^.+unknown option `\\(.+\\)'\\(\\(.\\|\n\\)+\\)$" in
                   Printf.printf "obc %s: unknown input argument: %s\n%s" version (Str.replace_first reg_exp "\\1" s) !usage;
                   exit 1
    (* let reg_exp = Str.regexp "^\\(\\(.\\|\n\\)+\\)\n\n\\(.\\|\n\\)+$" in *)
                   (* if Str.string_match reg_exp s 0 then *)
                   (*   Printf.printf "%s\n" (Str.replace_first reg_exp "\\1" s); *)
                   (* exit 1 *)
    | Arg.Help s -> Printf.printf "%s" s;
                    exit 0
  end;
  if !print_version then
    begin
      print_endline ("obc " ^ version);
      exit 0
    end;
  let g_vars_ref = ref (create_hash ()) in
  let g_funs_ref = ref (create_hash ()) in
  let in_file_list_len = List.length !in_file_list in
  if in_file_list_len > 0 then
    begin
      let interprete_file in_file =
        try
          let read_from_fh in_fh =
            let in_fbuf = Lexing.from_channel in_fh in
            try
              Printf.printf "in_file: %s\n" in_file;
              let prog = Obcparser.program Obclexer.read_tokens in_fbuf in
              interprete_program ~warn:!enable_warnings prog g_vars_ref g_funs_ref
            with
            | Obclexer.SyntaxError err -> Printf.eprintf "%s" err
            | Obcparser.Error -> Printf.eprintf "At offset %d: syntax error.\n" (Lexing.lexeme_start in_fbuf)
          in
          In_channel.with_file in_file ~f:read_from_fh
        with
        | Sys_error s -> Printf.printf "%s\n" s
      in
      try
        List.iter ~f:interprete_file !in_file_list
      with
      | QuitProgram -> ()
      | ExitProgram n -> exit n
    end;
  if in_file_list_len = 0 || !force_interactive_mode then
    let keywords = ["for"; "if"; "else"; "while"; "break"; "continue"; "quit"; "exit"] in
    let tab_completion ~left ~right:_ =
      let last_elem = List.last_exn (String.split left ~on:' ') in
      List.filter keywords ~f:(String.is_prefix ~prefix:last_elem) in
    let read_input_line ~p = Readline.input_line ~prompt:p ~tab_completion in
    let default_prompt_line = "obc> " in
    let rec process_input ?(p=default_prompt_line) s =
      match (read_input_line ~p:p) () with
      | None -> ()
      | Some l ->
         let line = s ^ l ^ "\n" in
         begin
           let in_buf = Lexing.from_string line in
           try
             let prog = Obcparser.program Obclexer.read_tokens in_buf in
             interprete_program ~warn:!enable_warnings prog g_vars_ref g_funs_ref;
             process_input ""
           with
           | Obclexer.SyntaxError err -> Printf.eprintf "%s" err
           | Obcparser.Error ->
              if (Lexing.lexeme_start in_buf) = (String.length line) then
                process_input ~p:(String.make (String.length default_prompt_line) ' ') line
              else
                begin
                  Printf.eprintf "At offset %d: syntax error.\n%!" (Lexing.lexeme_start in_buf);
                  process_input ""
                end
         end in
    try
      let evt_base = Libevent.init() in
      let evt = Libevent.create() in
      let evt_callback fd fl =
        if fl = TIMEOUT then
          Libevent.del evt
        else
          (* let in_buf = Lexing.from_string ((input_line (Unix.in_channel_of_descr fd)) ^ "\n") in *)
          let in_buf = Lexing.from_string ((read_line ()) ^ "\n") in
          try
            let prog = Obcparser.program Obclexer.read_tokens in_buf in
            interprete_program ~warn:!enable_warnings prog g_vars_ref g_funs_ref;
            Libevent.del evt;
            exit 0
          with
          | Obclexer.SyntaxError err -> Printf.eprintf "%s" err
          | Obcparser.Error -> Printf.eprintf "At offset %d: syntax error.\n" (Lexing.lexeme_start in_buf)
      in
      Libevent.set evt_base evt Unix.stdin [TIMEOUT; READ] false evt_callback;
      Libevent.add evt (Some 0.1); (* timeout (for calling via pipeline) *)
      Libevent.dispatch(evt_base);
      process_input ""
    with
    | QuitProgram -> ()
    | ExitProgram n -> exit n

let _ = main ()
