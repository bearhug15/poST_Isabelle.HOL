theory poSTVM
  imports poST_model
begin

type_synonym current_time = "time"
(*process vars, current state, start state, process status, time*)
type_synonym process_state = "(proc_var list) * state_name * state_name * proc_status *current_time"
type_synonym program_state = "((process_name,process_state) fmap) * process_name"
datatype model_state = ST "(global_var_decl list)"  "((program_name,program_state) fmap * program_name)"  "(function_block_decl list)"  "(function_decl list)"

definition find_var_by_name :: "symbolic_var  \<Rightarrow>(symbolic_var, var_init_decl) fmap \<Rightarrow> (symbolic_var * var_init_decl) option " where
"find_var_by_name var val = (case (fmlookup val var) of None \<Rightarrow> None | Some v \<Rightarrow> Some (var, v))"

fun get_var_by_name :: "(proc_var list) \<Rightarrow>  symbolic_var \<Rightarrow> (symbolic_var * var_init_decl) option" where
  "get_var_by_name [] _ = None" |
  "get_var_by_name (x#yz) var_name  =(let res = (case x of proc_var.ProcessVar var \<Rightarrow> None |
                                          proc_var.Var (is_const,  var) \<Rightarrow> find_var_by_name var_name var |
                                          proc_var.InVar var \<Rightarrow> find_var_by_name var_name var | 
                                          proc_var.OutVar var \<Rightarrow> find_var_by_name var_name var | 
                                          proc_var.InOutVar var \<Rightarrow> find_var_by_name var_name var) 
    in (if res = None 
          then get_var_by_name yz var_name 
          else res))"

fun get_cur_proc_state :: "program_state \<Rightarrow> process_state" where
"get_cur_proc_state (ps_map, ps_name) = (case (fmlookup ps_map ps_name) of Some (st) \<Rightarrow> st)"

definition get_cur_proc_var_list :: "program_state \<Rightarrow>proc_var list" where 
  "get_cur_proc_var_list ps_state = 
    (let (proc_var_list,st_name,proc_stat,cur_time) = get_cur_proc_state ps_state in
      proc_var_list)"
 
fun get_cur_prog_state :: "model_state \<Rightarrow> program_state" where
"get_cur_prog_state (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) = 
  (case (fmlookup ps_map p_name) of 
    Some(p_state) \<Rightarrow> p_state)"

definition get_cur_var_list :: "model_state \<Rightarrow> proc_var list" where
"get_cur_var_list st = get_cur_proc_var_list (get_cur_prog_state st)"



fun set_symbvar_in_var_list :: "(proc_var list) \<Rightarrow>  symbolic_var \<Rightarrow> var_init_decl \<Rightarrow> (proc_var list)" where
"set_symbvar_in_var_list [] var_name value = []" |
"set_symbvar_in_var_list (x # xs :: proc_var list) var_name value =
  (let res = (case x of 
    proc_var.ProcessVar var \<Rightarrow> None |
    proc_var.Var (is_const,  var) \<Rightarrow> find_var_by_name var_name var |
    proc_var.InVar var \<Rightarrow> find_var_by_name var_name var | 
    proc_var.OutVar var \<Rightarrow> find_var_by_name var_name var | 
    proc_var.InOutVar var \<Rightarrow> find_var_by_name var_name var) in
   (if res = None
      then ([x] @ (set_symbvar_in_var_list xs var_name value))
      else ([(case x of 
    proc_var.ProcessVar var \<Rightarrow>(proc_var.ProcessVar var) |
    proc_var.Var (is_const,  var) \<Rightarrow>(proc_var.Var (is_const, (fmupd var_name value var))) |
    proc_var.InVar var \<Rightarrow>(proc_var.InVar (fmupd var_name value var)) | 
    proc_var.OutVar var \<Rightarrow>(proc_var.OutVar (fmupd var_name value var)) | 
    proc_var.InOutVar var \<Rightarrow>(proc_var.InOutVar (fmupd var_name value var)))] @ xs)
)) "

fun set_symbvar :: "process_state \<Rightarrow> symbolic_var \<Rightarrow> var_init_decl \<Rightarrow> process_state" where
"set_symbvar (proc_var_list, state_name, proc_stat, cur_time) var_name value = 
  (set_symbvar_in_var_list proc_var_list var_name value,state_name,proc_stat,cur_time)"

fun set_symbvar_in_cur_proc :: "program_state \<Rightarrow> symbolic_var \<Rightarrow> var_init_decl \<Rightarrow> program_state" where
"set_symbvar_in_cur_proc (proc_map, proc_name) var_name value = 
  (case (fmlookup proc_map proc_name) of 
    Some(proc_state) \<Rightarrow> (fmupd proc_name (set_symbvar proc_state var_name value) proc_map,proc_name))"

fun set_symbvar_in_cur_prog :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> var_init_decl \<Rightarrow> model_state" where 
"set_symbvar_in_cur_prog (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) var_name value = 
  (case (fmlookup ps_map p_name) of
    Some(p_state) \<Rightarrow> (ST global_var_decl_list ((fmupd p_name p_state ps_map), p_name) function_block_decl_list function_decl_list))"


fun expr_processing :: "model_state \<Rightarrow> expr \<Rightarrow>(model_state * basic_post_type) " and
  prim_expr_processing :: "model_state \<Rightarrow> prim_expr \<Rightarrow>(model_state * basic_post_type)" and
  initialize_array :: "model_state \<Rightarrow> array_spec_init \<Rightarrow> (model_state * array_spec_init)"
  where
  "expr_processing st (Unary (UnaryExpr unary_option prim_exp)) =  (case unary_option of 
          Some op \<Rightarrow> (st, (basic_post_type.Nat 0)) | 
          None \<Rightarrow> prim_expr_processing st prim_exp)" |
  "expr_processing st (Binary bin_op exp1 exp2) = (case bin_op of 
    binary_op.And \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_and var1 var2))) |
    binary_op.Or \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_or var1 var2))) |
    binary_op.Less \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_less var1 var2))) |
    binary_op.More \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_more var1 var2))) |
    binary_op.LessEq \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_lesseq var1 var2))) |
    binary_op.MoreEq \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1  exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_moreeq var1 var2))) |
    binary_op.Eq \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_eq var1 var2))) |
    binary_op.NotEq \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_noteq var1 var2))) |
    binary_op.Xor \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type.Bool (basic_post_type_xor var1 var2))) |
    binary_op.Sum \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type_sum var1 var2)) |
    binary_op.Sub \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type_sub var1 var2)) |
    binary_op.Mul \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type_mul var1 var2)) |
    binary_op.Div \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type_div var1 var2)) |
    binary_op.Mod \<Rightarrow> 
      (let (new_st1, var1) = (expr_processing st exp1);
           (new_st2, var2) = (expr_processing new_st1 exp2) in
           (new_st2,basic_post_type_mod var1 var2)))" |
  "prim_expr_processing st (prim_expr.Const c) = (st , const_to_basic c)" |
  (*Add other case branches? *)
  "prim_expr_processing st (prim_expr.SymbolicVar var_name) = 
    (let var_list = get_cur_var_list st;
        buff = (get_var_by_name var_list var_name) in 
      (case buff of 
        None \<Rightarrow> (st, (basic_post_type.Nat 0)) | 
        Some (var_name,init) \<Rightarrow> 
          (case init of 
            (var_init_decl.Simple (value, exp_option))\<Rightarrow> 
              (let (st,new_value) = (case exp_option of 
                                      None =>(st, value) | 
                                      Some(exp) \<Rightarrow> (let (st,res) = expr_processing st exp;
                                                        new_st = (set_symbvar_in_cur_prog st var_name (var_init_decl.Simple (res,None)))  
                                                    in (new_st, res) ))
                in (st,new_value))) ))" |
  "prim_expr_processing st (prim_expr.ArrayVar (array_var.ArrayVar var_name exp)) = 
    (let var_list = get_cur_var_list st 
      in (case (get_var_by_name var_list var_name) of 
        None \<Rightarrow> (st, (basic_post_type.Nat 0)) |
        Some (var, init)\<Rightarrow> (case init of 
          var_init_decl.Array(array_init)\<Rightarrow> 
            (let (new_st1,((ar_interval,values),expr_list_option)) = initialize_array st array_init;
                 new_st2 = set_symbvar_in_cur_prog  new_st1 var_name (var_init_decl.Array ((ar_interval,values), expr_list_option));
                 new_var_list = set_symbvar_in_var_list var_list;
                 (new_st3, pos) = expr_processing new_st2 exp
              in (case pos of
                    basic_post_type.Nat val \<Rightarrow> (st, (nth values val)) |
                    basic_post_type.Int val \<Rightarrow> (st, (nth values (nat val))))))))" |
  "prim_expr_processing st (prim_expr.ProcStatEpxr (proc_name, proc_stat)) = 
    (let (proc_var_list,st_name,start_st_name,cur_proc_stat,cur_time) = get_cur_proc_state (get_cur_prog_state st);
      comp = proc_status_is cur_proc_stat proc_stat in
       (st, (basic_post_type.Bool comp)) )" |
  "prim_expr_processing st (prim_expr.Expression exp) = (expr_processing st exp)" |
  (*To Do*)
  "prim_expr_processing st (prim_expr.FunctionCall (function_call.FuncCall f_name param_list)) = (st, (basic_post_type.Nat 0))" |
  (*something wrong with map*)
  "initialize_array st ((ar_interval,values), array_init_option) =
    (let new_ar_interval = (case ar_interval of 
                              (array_interval.Expr exp1 exp2) \<Rightarrow>(let (new_st1,val1) = (expr_processing st exp1);
                                                                     (new_st2,val2) = (expr_processing st exp2) in
                                                                      (basics_to_array_interval val1 val2)) | 
                              (array_interval.Int int1 int2) \<Rightarrow> (array_interval.Int int1 int2)) 
      in (case array_init_option of
            None \<Rightarrow> (st, ((new_ar_interval,values), None)) |
            Some(expr_list) \<Rightarrow>(st, ((new_ar_interval,
                                    (map
                                      (\<lambda>exp. (let (st,res) = (expr_processing st exp) in res)) 
                                      expr_list):: (basic_post_type list)) , 
                                    None)))) "

datatype statement_result = Break | Continue | Exit | Reset | NextState

fun stop_process :: "model_state \<Rightarrow> process_name \<Rightarrow> model_state" where
"stop_process (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) target_proc_name =
   (let (proc_map, proc_name) = (case (fmlookup ps_map p_name) of 
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map target_proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
    in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            ((fmupd 
                 target_proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Stop, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list))"
fun stop_same_process :: "model_state  \<Rightarrow> model_state" where
"stop_same_process (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) =
   (let (proc_map, proc_name) = (case (fmlookup ps_map p_name) of 
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
    in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            ((fmupd 
                 proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Stop, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)) "
fun error_process :: "model_state \<Rightarrow> process_name \<Rightarrow> model_state" where
"error_process (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) target_proc_name =
   (let (proc_map, proc_name) = (case (fmlookup ps_map p_name) of 
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map target_proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
    in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            ((fmupd 
                 target_proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Error, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list))"
fun error_same_process :: "model_state \<Rightarrow> model_state" where
"error_same_process (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) =
   (let (proc_map, proc_name) = (case (fmlookup ps_map p_name) of 
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
    in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            ((fmupd 
                 proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Error, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list))"
fun reset_process :: "model_state \<Rightarrow> process_name \<Rightarrow> model_state" where
"reset_process (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) target_proc_name =
  (let (proc_map, proc_name) = (case (fmlookup ps_map p_name) of 
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), _ ,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map target_proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            ((fmupd 
                 target_proc_name
                 ((proc_var_list), start_st_name,start_st_name, proc_stat, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list))"
fun reset_same_process :: "model_state \<Rightarrow> model_state" where
"reset_same_process (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list)  =
  (let (proc_map, proc_name) = (case (fmlookup ps_map p_name) of 
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), _,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            ((fmupd 
                 proc_name
                 ((proc_var_list), start_st_name,start_st_name, proc_stat, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list))"
fun set_state :: "model_state \<Rightarrow> state_name \<Rightarrow> model_state" where
"set_state (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) st_name = 
  (let (proc_map, proc_name) = (case (fmlookup ps_map p_name) of 
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), _ ,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            ((fmupd 
                 proc_name
                 ((proc_var_list), st_name,start_st_name, proc_stat, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list))"

fun statement_processing :: "model_state \<Rightarrow> statement \<Rightarrow> model_state * statement_result" and
  statement_list_processing :: "model_state \<Rightarrow> statement_list \<Rightarrow> model_state * statement_result" and
  if_processing :: "model_state \<Rightarrow> (expr * statement_list) list \<Rightarrow> statement_list option \<Rightarrow> model_state * statement_result" and
  case_processing :: "model_state \<Rightarrow> basic_post_type \<Rightarrow> case_element list \<Rightarrow> statement_list option \<Rightarrow> model_state * statement_result"
  where
"statement_processing st (statement.AssignSt (var,exp)) =
  (let (new_st,new_value) = expr_processing st exp 
    in (case var of
        (common_var.SymbolicVar var_name) \<Rightarrow> 
          (set_symbvar_in_cur_prog new_st var_name (var_init_decl.Simple (new_value,None)),statement_result.Continue) |
        (common_var.Array (array_var.ArrayVar var_name exp)) \<Rightarrow> 
          (let (new_st,pos) = expr_processing new_st exp;
               (var_option) = get_var_by_name (get_cur_var_list new_st) var_name
           in (case var_option of 
                Some(var_name, init_decl) \<Rightarrow>
                  (case init_decl of 
                    var_init_decl.Array(array_init) \<Rightarrow>
                       (let (new_st,((ar_interval,values),expr_list_option)) = initialize_array new_st array_init;
                             actual_pos = (case (pos,ar_interval) of 
                                            (basic_post_type.Nat val,array_interval.Int start end) \<Rightarrow> 
                                              (nat ((int val) - start)) |
                                            (basic_post_type.Int val,array_interval.Int start end) \<Rightarrow> 
                                              (nat (val - start)));
                             new_values = (list_update values actual_pos new_value ) in
                          (set_symbvar_in_cur_prog new_st var_name (var_init_decl.Array ((ar_interval,new_values),expr_list_option)),statement_result.Continue))) )))) " |
(*"statement_processing st (statement.FBInvocation (fb_name,param_assign_list)) = st" |*)
"statement_processing st (statement.Return) = (st, statement_result.Break)" |
"statement_processing st (statement.Exit) = (st, statement_result.Exit)" |
"statement_processing st (statement.ProcessSt proc_statement) =
  (case proc_statement of 
    process_statement.Start(process_name_option) \<Rightarrow> 
      (case process_name_option of 
        None \<Rightarrow> (reset_same_process st,statement_result.Continue) |
        Some(proc_name) \<Rightarrow> (reset_process st proc_name,statement_result.Reset)) |
    process_statement.Stop(process_name_option) \<Rightarrow>
      (case process_name_option of 
        None \<Rightarrow> (stop_same_process st,statement_result.Continue) |
        Some(proc_name) \<Rightarrow> (stop_process st proc_name,statement_result.Reset)) |
    process_statement.Error(process_name_option) \<Rightarrow> 
      (case process_name_option of 
        None \<Rightarrow> (error_same_process st,statement_result.Continue) |
        Some(proc_name) \<Rightarrow> (error_process st proc_name,statement_result.Reset)))" |
"statement_processing st (statement.SetStateSt state_name_option) =
  (case state_name_option of 
    None \<Rightarrow> (st, statement_result.NextState) |
    Some(st_name) \<Rightarrow> (set_state st st_name, statement_result.Continue))" |
"statement_processing st (statement.ResetSt) = (st, statement_result.Reset)" |

"statement_processing st (statement.SelectSt (select_statement.IfSt (if_statement.IfSt if_then_list else_option ))) = 
  if_processing st if_then_list else_option" |

"statement_processing st (statement.SelectSt (select_statement.CaseSt (case_statement.CaseSt exp case_then_list else_option))) =
  (let (new_st, val) = expr_processing st exp
    in case_processing st val case_then_list else_option) " |

"statement_list_processing st (StList []) = (st,statement_result.Continue)" |

"statement_list_processing st (StList (elem#other)) = 
  (let (new_st,st_result) = statement_processing st elem 
    in (case st_result of
        statement_result.Continue \<Rightarrow> (statement_list_processing new_st (StList other))|
        statement_result.Break \<Rightarrow> (statement_list_processing new_st (StList other))|
        _ \<Rightarrow> (new_st,st_result)))" | 
"if_processing st [] else_option = 
 (case else_option of
    None \<Rightarrow> (st,statement_result.Continue) |
    Some(st_list) \<Rightarrow> statement_list_processing st st_list)"|
(*To Do*)
"if_processing st ((exp,st_list)#other) else_option = 
(st,statement_result.Continue)"|
(*To Do*)
"statement_processing st (statement.IterSt iter_st) = (st,statement_result.Continue) "

(*
fun state_processing :: "(proc_var list) state_decl \<Rightarrow> (proc_var list) process_vars"
  where
*)
(*
definition get_val :: "(string, nat) fmap" where
  "get_val = fmempty"

value "(fmlookup (fmupd ''val'' 0 get_val) ''val'')"
*)
end