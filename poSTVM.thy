theory poSTVM
  imports poST_model "HOL-Data_Structures.Queue_2Lists"

begin

type_synonym current_time = "time"
(*process vars, current state, start state, process status, time*)
type_synonym process_state = "(proc_var list) * state_name * state_name * proc_status *current_time"
type_synonym program_state = "((process_name,process_state) fmap) * process_name"
datatype model_state = ST "(global_var_decl list)"  "((program_name,program_state) fmap * program_name)"  "(function_block_decl list)"  "(function_decl list)"

definition find_var_by_name :: "symbolic_var  \<Rightarrow>(symbolic_var, var_init_decl) fmap \<Rightarrow> var_init_decl option" where
"find_var_by_name var val =(fmlookup val var) "
(*"find_var_by_name var val = (case (fmlookup val var) of None \<Rightarrow> None | Some v \<Rightarrow> Some (var, v))"*)

fun get_var_by_name :: "(proc_var list) \<Rightarrow>  symbolic_var \<Rightarrow>  var_init_decl option" where
  "get_var_by_name (x#yz) var_name  = (let res = (case x of proc_var.ProcessVar var \<Rightarrow> None |
                                          proc_var.Var (is_const,  var) \<Rightarrow> find_var_by_name var_name var |
                                          proc_var.InVar var \<Rightarrow> find_var_by_name var_name var | 
                                          proc_var.OutVar var \<Rightarrow> find_var_by_name var_name var | 
                                          proc_var.InOutVar var \<Rightarrow> find_var_by_name var_name var) 
    in (if res = None 
          then get_var_by_name yz var_name 
          else res))"

fun get_cur_proc_state_by_prog :: "program_state \<Rightarrow> process_state" where
"get_cur_proc_state_by_prog (ps_map, ps_name) = (case (fmlookup ps_map ps_name) of Some (st) \<Rightarrow> st)"



definition get_cur_proc_var_list :: "program_state \<Rightarrow>proc_var list" where 
  "get_cur_proc_var_list ps_state = 
    (let (proc_var_list,st_name,proc_stat,cur_time) = get_cur_proc_state_by_prog ps_state in
      proc_var_list)"
 
fun get_cur_prog_state :: "model_state \<Rightarrow> program_state" where
"get_cur_prog_state (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) = 
  (case (fmlookup ps_map p_name) of 
    Some(p_state) \<Rightarrow> p_state)"

fun get_proc_state_by_prog :: "program_state \<Rightarrow> process_name \<Rightarrow> process_state" where
"get_proc_state_by_prog (ps_map,ps_name) var_name = (case (fmlookup ps_map var_name) of Some (st) \<Rightarrow> st)"

definition get_proc_state :: "model_state \<Rightarrow> process_name \<Rightarrow> process_state" where 
"get_proc_state st var_name =
  get_proc_state_by_prog (get_cur_prog_state st) var_name"

definition get_cur_var_list :: "model_state \<Rightarrow> proc_var list" where
"get_cur_var_list st = get_cur_proc_var_list (get_cur_prog_state st)"

definition get_cur_var_by_name :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> var_init_decl" where
"get_cur_var_by_name st var_name = the (get_var_by_name (get_cur_var_list st) var_name)"

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

fun set_simpvar :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type => model_state" where
"set_simpvar st var_name value =
  (case (get_cur_var_by_name st var_name) of
    (var_init_decl.Simple (old_val,opt)) \<Rightarrow> (set_symbvar_in_cur_prog st var_name (var_init_decl.Simple (value, opt))) )"

definition set_bval_to_list :: "basic_post_type list \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type list" where
"set_bval_to_list l pos new_val = 
  (case pos of 
    basic_post_type.Nat pos \<Rightarrow> (list_update l pos new_val) |
    basic_post_type.Int pos \<Rightarrow> (list_update l (nat pos) new_val))"

fun set_arvar :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type \<Rightarrow>  model_state" where
"set_arvar st var_name pos value =
  (case (get_cur_var_by_name st var_name) of
    (var_init_decl.Array ((array_interval.Int val1 val2,values),opt)) \<Rightarrow> 
      (set_symbvar_in_cur_prog 
        st 
        var_name 
        (var_init_decl.Array ((array_interval.Int val1 val2,
                               (set_bval_to_list values (basic_post_type_sum (basic_post_type.Int val1) pos) value)),
                              opt))) )"

definition get_bval_from_list :: "basic_post_type list \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
"get_bval_from_list l pos = 
  (case pos of 
    basic_post_type.Nat val \<Rightarrow> (nth l val) |
    basic_post_type.Int val \<Rightarrow> (nth l (nat val)))"

fun get_val_from_array :: "array_spec_init \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
"get_val_from_array ((array_interval.Int val1 val2, values),_) pos =
  get_bval_from_list values (basic_post_type_sub pos (basic_post_type.Int val1))"

(*Reset timer in current process*)
fun reset_timer :: "model_state \<Rightarrow> model_state" where
"reset_timer (ST g_list (pr_map,pr_name) fb_list f_list) = 
  (let (p_map,p_name) = (get_cur_prog_state (ST g_list (pr_map,pr_name) fb_list f_list));
       (process_vars, current_state, start_state, process_status, t) = (get_cur_proc_state_by_prog (p_map,p_name))
    in (ST 
          g_list 
          ((fmupd 
              pr_name 
              ((fmupd 
                 p_name 
                 (process_vars, current_state, start_state, process_status, t)
                 p_map),p_name)
              pr_map),
            pr_name) 
          fb_list 
          f_list))"

datatype statement_result = Break | Continue | Exit | Return | Reset | NextState
datatype point_type = Break | Return | Exit
datatype process_mod = Restart | Stop | Error


datatype stack_op = 
  Unary "unary_op option" | 
  Binary binary_op | 
  Value basic_post_type | 
  Get symbolic_var |
  GetArray symbolic_var |
  CheckProcStat process_name proc_status |
  FunctionCall func_name "param_assign list" |
  Assign symbolic_var  |
  AssignArray symbolic_var |
  FunctionBlockCall func_block_name "param_assign list" |
  SetPoint point_type |
  GoPoint point_type |
  SetState "state_name option" |
  ProcessStatement "process_name option" process_mod |
  StatementList "stack_op list" |
  IfStatement "stack_op list" |
  CaseStatement "stack_op list" |
  WhileStatement "stack_op list" |
  ResetTimer 

type_synonym stack = "stack_op list"

fun stack_expr :: "expr \<Rightarrow> stack" and
  stack_prim_expr :: "prim_expr \<Rightarrow> stack" where
"stack_expr exp = 
  (case exp of 
    (expr.Unary (UnaryExpr unary_option prim_exp)) \<Rightarrow> (stack_op.Unary unary_option)# (stack_prim_expr prim_exp) |
    (expr.Binary bin_op exp1 exp2) \<Rightarrow> ((stack_op.Binary bin_op) # (stack_expr exp1)) @ (stack_expr exp2))" |
"stack_prim_expr (prim_expr.Const c) = [stack_op.Value (const_to_basic c)]" |
"stack_prim_expr (prim_expr.SymbolicVar var_name) = [stack_op.Get var_name ]" |
"stack_prim_expr (prim_expr.ArrayVar (array_var.ArrayVar var_name exp)) = (stack_op.GetArray var_name) #(stack_expr exp)" |
"stack_prim_expr (prim_expr.ProcStatEpxr (proc_name, proc_stat)) = [stack_op.CheckProcStat proc_name proc_stat]" |
"stack_prim_expr (prim_expr.Expression exp) = stack_expr exp" |
"stack_prim_expr (prim_expr.FunctionCall (function_call.FuncCall f_name param_assign_list)) = [stack_op.FunctionCall f_name param_assign_list]"

 
(**)
definition initialize_array :: "[model_state, symbolic_var] \<Rightarrow> model_state" where
"initialize_array st var_name= st"


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

primrec nat_to_values_stack :: "nat list \<Rightarrow> stack" where
"nat_to_values_stack [] = [] " |
"nat_to_values_stack (v#other) = (stack_op.Value (basic_post_type.Nat v)) # (nat_to_values_stack other)"
(*
primrec for_to_while_statement :: "for_statement \<Rightarrow>statement *  while_statement * statement" where
"for_to_while_statement (for_statement.ForSt var_name (exp1,exp2,exp_option) st_list) = 
  (let st1 = (stat))"
*)
fun stack_statement :: "statement \<Rightarrow> stack" and
  stack_statement_list:: "statement list \<Rightarrow>stack" and
  stack_if_statements :: "(expr * statement_list) list \<Rightarrow> stack" and
  stack_case_statements :: "case_element list \<Rightarrow> stack"  where
"stack_statement (statement.AssignSt (var, exp)) = 
  (let value_queue = (stack_expr exp)
  in (case var of 
      (common_var.SymbolicVar var_name) \<Rightarrow> ((stack_op.Assign var_name)# value_queue) |
      (common_var.Array (array_var.ArrayVar var_name exp)) \<Rightarrow>((stack_op.AssignArray var_name)# (stack_expr exp)@ value_queue )))" |
"stack_statement (statement.Return) = [stack_op.GoPoint point_type.Return]" |
"stack_statement (statement.Exit) = [stack_op.GoPoint point_type.Exit]" |
"stack_statement (statement.ProcessSt proc_statement) = 
  (case proc_statement of
    process_statement.Start(process_name_option) \<Rightarrow> 
      [stack_op.ProcessStatement process_name_option process_mod.Restart] |
    process_statement.Stop(process_name_option) \<Rightarrow>
      [stack_op.ProcessStatement process_name_option process_mod.Stop] |
    process_statement.Error(process_name_option) \<Rightarrow> 
      [stack_op.ProcessStatement process_name_option process_mod.Error])" |
"stack_statement (statement.SetStateSt state_name_option) = [stack_op.SetState state_name_option]" |
"stack_statement (statement.SelectSt (select_statement.IfSt  if_then_list else_option )) = 
  (let if_stack = (stack_if_statements if_then_list) in  
        (case else_option of None \<Rightarrow> if_stack |
          Some(statement_list.StList st_list) \<Rightarrow> if_stack @ (stack_statement_list st_list))
          @[stack_op.SetPoint point_type.Break])" |
"stack_statement_list [] = []" |
"stack_statement_list (st#other) = (stack_statement st) @ (stack_statement_list other)" |
"stack_if_statements [] = []" |
"stack_if_statements (ifs#other) = 
    (let (exp,st_list) = ifs 
      in (case st_list of (statement_list.StList st_list) \<Rightarrow>  
            ([stack_op.IfStatement (stack_expr exp)]) 
            @ [stack_op.StatementList ((stack_statement_list st_list)@ [(stack_op.GoPoint point_type.Break)])]))  
      @ (stack_if_statements other) 
      @ [stack_op.SetPoint point_type.Break]" |
"stack_statement (statement.SelectSt (select_statement.CaseSt  exp case_then_list else_option)) =
  (stack_op.CaseStatement (stack_expr exp))
    #(case else_option of 
        None \<Rightarrow> (stack_case_statements case_then_list) |
        Some(statement_list.StList st_list) \<Rightarrow> (stack_case_statements case_then_list) @ (stack_statement_list st_list))
      @ [stack_op.SetPoint point_type.Break]" |
"stack_case_statements [] =[]" |
"stack_case_statements (cas#other) = 
  (case cas of 
    (case_element.CaseElem nat_list (statement_list.StList st_list)) \<Rightarrow>
        (nat_to_values_stack nat_list) 
      @ [stack_op.StatementList ((stack_statement_list st_list) @ [(stack_op.GoPoint point_type.Break)])]
      @ (stack_case_statements other))" |
"stack_statement (statement.IterSt (iter_statement.ForSt  var_name (exp1,exp2,exp_option) (statement_list.StList st_list))) = 
  [stack_op.Assign var_name] 
  @ (stack_expr exp1)
  @ [stack_op.WhileStatement
      (stack_expr (expr.Binary 
                    binary_op.LessEq 
                    (expr.Unary (UnaryExpr None (prim_expr.SymbolicVar var_name)) )
                    exp2))]
  @ [stack_op.StatementList 
    ((stack_statement_list (st_list ))
      @ [stack_op.Assign var_name]
      @ (case exp_option of
          None \<Rightarrow> [stack_op.Binary binary_op.Sum ,stack_op.Get var_name, stack_op.Value (basic_post_type.Nat 0)] |
          Some(exp) \<Rightarrow>[stack_op.Binary binary_op.Sum ,stack_op.Get var_name] @ (stack_expr exp)))] " |
"stack_statement (statement.IterSt (iter_statement.WhileSt  exp (statement_list.StList st_list))) = 
   [stack_op.WhileStatement (stack_expr exp)]
   @ [stack_op.StatementList (stack_statement_list st_list)]
   @ [stack_op.SetPoint point_type.Break]" |
"stack_statement (statement.IterSt (iter_statement.RepeatSt  (statement_list.StList st_list) exp)) =  
    (let st_list = [stack_op.StatementList (stack_statement_list st_list)] 
    in (st_list
    @[stack_op.WhileStatement (stack_expr exp)]
    @ st_list
    @[stack_op.SetPoint point_type.Break])) " |
"stack_statement (statement.ResetSt) = [stack_op.ResetTimer]" |
"stack_statement (FBInvocation (fb_name, param_assign_list)) =[stack_op.FunctionBlockCall fb_name param_assign_list]"




definition unary_op_exec :: "unary_op => basic_post_type \<Rightarrow> basic_post_type" where
"unary_op_exec op var = (case op of unary_op.Not \<Rightarrow> (basic_post_type_not var) | unary_op.Minus \<Rightarrow> (basic_post_type_minus var))"

definition binary_op_exec :: "binary_op \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
"binary_op_exec op var1 var2 = 
  (case op of 
    binary_op.And \<Rightarrow> basic_post_type.Bool(basic_post_type_and var1 var2)|
 binary_op.Or \<Rightarrow> basic_post_type.Bool(basic_post_type_or var1 var2)|
    binary_op.Xor \<Rightarrow> basic_post_type.Bool(basic_post_type_xor var1 var2) | 
    binary_op.Eq \<Rightarrow> basic_post_type.Bool(basic_post_type_or var1 var2)| 
    binary_op.NotEq \<Rightarrow>basic_post_type.Bool(basic_post_type_noteq var1 var2)| 
    binary_op.Less \<Rightarrow>basic_post_type.Bool(basic_post_type_less var1 var2)| 
    binary_op.More \<Rightarrow>basic_post_type.Bool(basic_post_type_more var1 var2)| 
    binary_op.LessEq \<Rightarrow>basic_post_type.Bool(basic_post_type_lesseq var1 var2)| 
    binary_op.MoreEq \<Rightarrow>basic_post_type.Bool(basic_post_type_moreeq var1 var2)| 
    binary_op.Sum \<Rightarrow> basic_post_type_sum var1 var2| 
    binary_op.Sub \<Rightarrow> basic_post_type_sub var1 var2| 
    binary_op.Mul \<Rightarrow> basic_post_type_mul var1 var2| 
    binary_op.Div \<Rightarrow> basic_post_type_div var1 var2| 
    binary_op.Mod \<Rightarrow> basic_post_type_mod var1 var2)"

fun get_expr :: "stack  \<Rightarrow> stack * stack" where
"get_expr []  = ([], [])" |
"get_expr ((stack_op.Unary unary_op_option)#other)  = 
  (let (expr_list,st) = (get_expr other) in ((stack_op.Unary unary_op_option) # expr_list,st))" |
"get_expr ((stack_op.Binary binary_op)#other)  = 
  (let (expr_list1,st1) = (get_expr other);
       (expr_list2,st2) = (get_expr st1) in ((Binary binary_op) # expr_list1 @ expr_list2,st2))" |
"get_expr ((stack_op.Value basic_post_type)#other)  = 
  ([Value basic_post_type],other)" |
"get_expr ((stack_op.Get var)#other)  = 
  ([stack_op.Get var],other)" |
"get_expr ((stack_op.GetArray var)#other)  = 
  (let (expr_list1,st1) = (get_expr other) in ((stack_op.GetArray var) # expr_list1, st1))"|
"get_expr ((stack_op.CheckProcStat v1 v2)#other)  = 
  ([stack_op.CheckProcStat v1 v2],other)" |
"get_expr ((stack_op.FunctionCall v1 v2)#other)  = 
  ([stack_op.FunctionCall v1 v2],other)" |
"get_expr lt  = ([],lt)"

fun skip_after_break :: "stack \<Rightarrow> stack" where
"skip_after_break [] = []" |
"skip_after_break ((stack_op.SetPoint point_type.Break)#other) = other" |
"skip_after_break (_#other) = other"

fun skip_after_exit :: "stack \<Rightarrow> stack" where
"skip_after_exit [] = []" |
"skip_after_exit ((stack_op.SetPoint point_type.Exit)#other) = other" |
"skip_after_exit (_#other) = other"

fun skip_after_return :: "stack \<Rightarrow> stack" where
"skip_after_return [] = []" |
"skip_after_return ((stack_op.SetPoint point_type.Return)#other) = other" |
"skip_after_return (_#other) = other"

fun skip_statement_list :: "stack \<Rightarrow> stack" where
"skip_statement_list [] = []" |
"skip_statement_list ((stack_op.StatementList loc_stack)#other) = other" |
"skip_statement_list other = other"

fun skip_if :: "stack \<Rightarrow> stack" where
"skip_if [] = []" |
"skip_if ((stack_op.IfStatement loc_stack1)#(stack_op.StatementList loc_stack2)#other) = (other)" |
"skip_if other = other"

fun get_values :: "stack \<Rightarrow> stack * stack" where
"get_values [] = ([],[])" |
"get_values ((stack_op.Value val)#other) = (let (res,stack_res) = (get_values other) in ((stack_op.Value val)#res,stack_res) )" |
"get_values other =([], other)"

(*assumes stack have only stack_op.Value*)
fun values_to_basics :: "stack \<Rightarrow> basic_post_type list" where
"values_to_basics [] = []" |
"values_to_basics ((stack_op.Value val)#other) = val # (values_to_basics other)"
 

fun get_cases :: "stack \<Rightarrow> stack * (((basic_post_type list) * stack_op) list)" where
"get_cases [] = ([],[])" |
"get_cases ((stack_op.Value val)#other) = 
  (let (values,new_st) = get_values ((stack_op.Value val)#other);
        values = values_to_basics (values) in
    (case new_st of
      ((stack_op.StatementList loc_stack)#new_stack) \<Rightarrow> 
        (let (res_stack,res_list) = get_cases new_stack in (res_stack,(values,(stack_op.StatementList loc_stack))#res_list))))" |
"get_cases st = (st,[])"


fun skip_case :: "stack \<Rightarrow> stack" where
"skip_case [] = []" |
"skip_case ((stack_op.CaseStatement loc_stack)#other) = skip_after_break other" |
"skip_case other = other"

primrec check_case :: "basic_post_type list \<Rightarrow> basic_post_type \<Rightarrow> bool" where
"check_case [] _ = False" |
"check_case (val1#other) val2 = 
  (if (basic_post_type_eq val1 val2) 
    then True
    else (check_case other val2))"

(*TO DO Vars init on start*)

(*function assumes that variables initialized*)
fun exec_expr :: "stack \<Rightarrow> model_state \<Rightarrow> basic_post_type option" where
"exec_expr [] st = None" |

"exec_expr ((stack_op.Unary unary_op_option)#other) st = 
  (let res = (exec_expr other st) 
    in (case unary_op_option of 
      None \<Rightarrow> res | 
      (Some un_op) \<Rightarrow> (Some (unary_op_exec un_op (the res)))))" |

"exec_expr ((stack_op.Binary bin_op)#other) st = 
  (let (left,new_stack) = (get_expr other 1)
  in (Some (binary_op_exec 
            bin_op 
            (the (exec_expr left st)) 
            (the (exec_expr new_stack st)))))" |

"exec_expr ((stack_op.Value val)#[]) st = 
  (Some val)" |

"exec_expr ((stack_op.Get var_name)#[]) st = 
 (let init_decl = (get_cur_var_by_name st var_name)
  in (case init_decl of
      (var_init_decl.Simple (val, _)) \<Rightarrow> (Some val))) " |

"exec_expr ((stack_op.GetArray var_name) #other) st =
  (let init_decl = (get_cur_var_by_name st var_name);
       pos = (the (exec_expr other st)) 
    in (case init_decl of
      (var_init_decl.Array array_spec) \<Rightarrow> (Some (get_val_from_array array_spec pos))))" |

"exec_expr ((stack_op.CheckProcStat proc_name proc_stat)#[]) st = 
  (let (_,_,_, cur_proc_stat,_) = (get_proc_state st proc_name) in 
  Some (basic_post_type.Bool (proc_status_is cur_proc_stat proc_stat)))" |
(*TO DO Function Call*)
"exec_expr ((stack_op.FunctionCall v1 v2)#[])st  =
  None" |
"exec_expr lt _ = None"

fun exec_statement :: "stack \<Rightarrow> model_state \<Rightarrow> stack * model_state * statement_result" and
  exec_case_statement :: "model_state \<Rightarrow> ((basic_post_type list) * stack_op) list \<Rightarrow> basic_post_type \<Rightarrow>model_state * statement_result" where
"exec_statement [] st = ([],st,statement_result.Return)" |

"exec_statement ((stack_op.Assign var_name )#other) st = 
  (let (val_stack, new_stack) = (get_expr other)
      in (new_stack,(set_simpvar st var_name (the (exec_expr val_stack))),statement_result.Continue))" |
"exec_statement ((stack_op.AssignArray var_name)#other) st = 
    (let (pos_stack,new_stack1) = (get_expr other);
         (val_stack,new_stack2) = (get_expr new_stack1) in
        (new_stack2,(set_arvar st var_name (the (exec_expr pos_stack)) (the (exec_expr val_stack))),statement_result.Continue))" |
(*TO DO FunctionBlockCall
"exec_statement ((stack_op.FunctionBlockCall fb_name param_assign_list )#other) st "*)
"exec_statement ((stack_op.SetPoint p)#other) st = (other,st, statement_result.Continue)" |
"exec_statement ((stack_op.GoPoint p)#other) st = 
  (case p of 
    point_type.Break \<Rightarrow> (other, st, statement_result.Break)|
    point_type.Exit \<Rightarrow>  (other, st, statement_result.Exit)|
    point_type.Return \<Rightarrow>  (other, st, statement_result.Return))" |
"exec_statement ((stack_op.SetState state_name_option)#other) st =
  (case state_name_option of
    None \<Rightarrow> (other, st, statement_result.NextState) |
    (Some st_name) \<Rightarrow> (other, set_state st st_name, statement_result.Return))" |
"exec_statement ((stack_op.ProcessStatement proc_name_option proc_mod)#other) st =
  (case proc_mod of
    (process_mod.Restart) \<Rightarrow> 
      (case proc_name_option of
        None \<Rightarrow> (other, reset_same_process st, statement_result.Return) |
        (Some proc_name) \<Rightarrow> (other, reset_process st proc_name, statement_result.Continue)) |
    (process_mod.Stop) \<Rightarrow> 
      (case proc_name_option of
        None \<Rightarrow> (other, stop_same_process st, statement_result.Return) |
        (Some proc_name) \<Rightarrow> (other, stop_process st proc_name, statement_result.Continue)) |
    (process_mod.Error) \<Rightarrow> 
      (case proc_name_option of
        None \<Rightarrow> (other, error_same_process st, statement_result.Return) |
        (Some proc_name) \<Rightarrow> (other, error_process st proc_name, statement_result.Continue)))" |
"exec_statement ((stack_op.IfStatement loc_stack )#other) st =
  (case (exec_expr loc_stack) of 
    (Some (basic_post_type.Bool val)) \<Rightarrow> 
      (if val 
        then (case other of 
          ((stack_op.StatementList loc_stack)#new_other) \<Rightarrow> 
            (let (_,new_st,st_result) = (exec_statement loc_stack st) in (new_other,new_st,st_result)))
        else (let (new_stack) = (skip_statement_list other) in (exec_statement new_stack st))))" |
"exec_statement ((stack_op.CaseStatement loc_stack)#other) st =
  (let (new_stack,cases_list) = get_cases other;
       value = the (exec_expr loc_stack);
       (new_st,st_res) = exec_case_statement st cases_list value in
    (new_stack,new_st,st_res))" |
"exec_case_statement st [] _ = (st, statement_result.Continue)" |
"exec_case_statement st ((values,st_list)#other) value =
  (if (check_case values value)
    then 
      (let (_,new_st,st_res) = (exec_statement [st_list] st)
        in (new_st,st_res))
    else
      (exec_case_statement st other value))" |
"exec_statement ((stack_op.ResetTimer)#other) st = (other,(reset_timer st),statement_result.Continue)" |
"exec_statement ((stack_op.StatementList loc_stack)#other) st =
 (let (new_stack,new_st,st_res) = (exec_statement loc_stack st) in 
  (case st_res of
    statement_result.Break \<Rightarrow> (exec_statement (skip_to_exec new_stack) new_st) |
    statement_result.Continue \<Rightarrow> (exec_statement new_stack new_st) |
    statement_result.Return \<Rightarrow> (new_stack, new_st, statement_result.Continue) |
    _ \<Rightarrow> (new_stack,new_st,st_res)))"

(*TO DO while branch*)

definition expr_ex1 :: "expr" where
"expr_ex1 = expr.Binary binary_op.Sum 
                        (expr.Binary binary_op.Mul 
                                     (expr.Unary (UnaryExpr None (prim_expr.Const (const.Nat 1)))) 
                                     (expr.Unary (UnaryExpr None (prim_expr.SymbolicVar ''var1'')))) 
                        (expr.Unary (UnaryExpr (Some unary_op.Minus) 
                                               (prim_expr.ArrayVar (array_var.ArrayVar 
                                                                    ''arvar1''
                                                                    (expr.Unary (UnaryExpr None (prim_expr.Const (const.Int 1)))))))) "

value "stack_expr (expr_ex1)"

definition st_ex1 :: "statement" where
"st_ex1 = statement.IterSt (iter_statement.ForSt
                            ''counter''
                            ((expr.Unary (UnaryExpr None (prim_expr.Const (const.Nat 0)))),
                             (expr.Unary (UnaryExpr None (prim_expr.Const (const.Nat 5)))),
                             Some (expr.Unary (UnaryExpr None (prim_expr.Const (const.Nat 2)))))
                            (statement_list.StList 
                              [statement.AssignSt (common_var.SymbolicVar ''collector'',
                                                   (expr.Unary (UnaryExpr None (prim_expr.SymbolicVar ''counter''))))]))"

value" stack_statement (st_ex1)"
(*
definition get_val :: "(string, nat) fmap" where
  "get_val = fmempty"

value "(fmlookup (fmupd ''val'' 0 get_val) ''val'')"
*)
end