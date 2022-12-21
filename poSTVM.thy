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

datatype buff = Buff nat nat
fun buff_fun :: "buff \<Rightarrow> nat"
  where
"buff_fun value = (let (val1, val2) = (case value of (Buff val1 val2) \<Rightarrow> (val1,val2)) in val1)"

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

datatype statement_result = Break | Continue | Exit | Reset | NextState
datatype point_type = Break | Result | Exit
datatype process_mod = Restart | Stop | Error


datatype stack_op = 
  Unary "unary_op option" | 
  Binary binary_op | 
  Value basic_post_type | 
  Assign symbolic_var | 
  ArrayAssign symbolic_var |
  Get symbolic_var |
  CheckProcStat process_name proc_status |
  FunctionCall func_name "param_assign list" |
  FunctionBlockCall func_block_name "param_assign list" |
  StatementResult statement_result |
  SetPoint point_type |
  GoPoint point_type |
  SetState "state_name option" |
  ProcessStatement "process_name option" process_mod |
  StatementList "stack_op queue" |
  IfStatement "stack_op queue" |
  CaseStatement "stack_op queue" |
  WhileStatement "stack_op queue" |
  ResetTimer |
  Blanck

type_synonym stack = "stack_op queue"

definition enqueue :: "'a \<Rightarrow> 'a queue" where
"enqueue val = ([val],[])"

definition queue_concat :: "'a queue \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
"queue_concat q1 q2 = ((list q1) @ (list q2),[])"

definition list_to_queue :: "'a list \<Rightarrow> 'a queue" where
"list_to_queue l = (l,[])"

definition self :: "'a queue \<Rightarrow> 'a queue" where
"self q = q"

primrec queue_list_to_queue :: "('a queue) list \<Rightarrow>'a queue" where
"queue_list_to_queue [] = ([],[])  " |
"queue_list_to_queue (x#other) = queue_concat x (queue_list_to_queue other)"

fun stack_expr :: "expr \<Rightarrow> stack" and
  stack_prim_expr :: "prim_expr \<Rightarrow> stack" where
(*To do Unary branch*)
"stack_expr exp = 
  (case exp of 
    (expr.Unary (UnaryExpr unary_option prim_exp)) \<Rightarrow> (queue_concat (enqueue (stack_op.Unary unary_option)) (stack_prim_expr prim_exp)) |
    (expr.Binary bin_op exp1 exp2) \<Rightarrow>(queue_concat (queue_concat (enqueue (stack_op.Binary bin_op)) (stack_expr exp1)) (stack_expr exp2)))" |
"stack_prim_expr (prim_expr.Const c) = enqueue (stack_op.Value (const_to_basic c))" |
"stack_prim_expr (prim_expr.SymbolicVar var_name) = enqueue (stack_op.Get var_name)" |
"stack_prim_expr (prim_expr.ArrayVar (array_var.ArrayVar var_name exp)) = queue_concat (enqueue (stack_op.Get var_name)) (stack_expr exp)" |
"stack_prim_expr (prim_expr.ProcStatEpxr (proc_name, proc_stat)) = enqueue (stack_op.CheckProcStat proc_name proc_stat)" |
"stack_prim_expr (prim_expr.Expression exp) = stack_expr exp" |
"stack_prim_expr (prim_expr.FunctionCall (function_call.FuncCall f_name param_assign_list)) = enqueue (stack_op.FunctionCall f_name param_assign_list)"

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
"nat_to_values_stack [] = enqueue (stack_op.Blanck) " |
"nat_to_values_stack (v#other) = queue_concat (enqueue (stack_op.Value (basic_post_type.Nat v))) (nat_to_values_stack other)"
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
      (common_var.SymbolicVar var_name) \<Rightarrow> queue_concat (enqueue (stack_op.Assign var_name)) value_queue|
      (common_var.Array (array_var.ArrayVar var_name exp)) \<Rightarrow>queue_concat (queue_concat (enqueue (stack_op.Assign var_name)) (stack_expr exp)) value_queue ))" |
"stack_statement (statement.Return) = enqueue (stack_op.GoPoint point_type.Result)" |
"stack_statement (statement.Exit) = enqueue (stack_op.GoPoint point_type.Exit)" |
"stack_statement (statement.ProcessSt proc_statement) = 
  (case proc_statement of
     process_statement.Start(process_name_option) \<Rightarrow> 
      enqueue (stack_op.ProcessStatement process_name_option process_mod.Restart) |
    process_statement.Stop(process_name_option) \<Rightarrow>
      enqueue (stack_op.ProcessStatement process_name_option process_mod.Stop) |
    process_statement.Error(process_name_option) \<Rightarrow> 
      enqueue (stack_op.ProcessStatement process_name_option process_mod.Error))" |
"stack_statement (statement.SetStateSt state_name_option) = enqueue (stack_op.SetState state_name_option)" |
"stack_statement (statement.SelectSt (select_statement.IfSt (if_statement.IfSt if_then_list else_option ))) = 
  (let if_queue = (stack_if_statements if_then_list) in 
    (queue_concat 
      (enqueue (stack_op.SetPoint point_type.Break)) 
        (case else_option of None \<Rightarrow> if_queue |
          Some(statement_list.StList st_list) \<Rightarrow> queue_concat if_queue (stack_statement_list st_list))))" |
"stack_statement_list [] = enqueue (stack_op.Blanck)" |
"stack_statement_list (st#other) = queue_concat (stack_statement st) (stack_statement_list other)" |
"stack_if_statements [] = enqueue (stack_op.Blanck)" |
"stack_if_statements (ifs#other) = 
  queue_concat 
    (let (exp,st_list) = ifs 
      in (case st_list of (statement_list.StList st_list) \<Rightarrow>  
          (queue_concat 
            (enqueue (stack_op.IfStatement (stack_expr exp))) 
            (enqueue (stack_op.StatementList 
                      (queue_concat 
                        (stack_statement_list st_list)
                        (enqueue (stack_op.GoPoint point_type.Break))))))) )
    (queue_concat 
      (stack_if_statements other)
      (enqueue (stack_op.SetPoint point_type.Break)))" |
"stack_statement (statement.SelectSt (select_statement.CaseSt (case_statement.CaseSt exp case_then_list else_option))) =
  queue_concat
    (enqueue (stack_op.CaseStatement (stack_expr exp)))
    (queue_concat
      (case else_option of None \<Rightarrow> (stack_case_statements case_then_list) |
        Some(statement_list.StList st_list) \<Rightarrow> queue_concat (stack_case_statements case_then_list) (stack_statement_list st_list))
      (enqueue (stack_op.SetPoint point_type.Break)))" |
"stack_case_statements [] = enqueue (stack_op.Blanck)" |
"stack_case_statements (cas#other) = 
  (case cas of (case_element.CaseElem nat_list (statement_list.StList st_list)) \<Rightarrow> 
    queue_concat
      (queue_concat
        (nat_to_values_stack nat_list)
        (enqueue (stack_op.StatementList 
                    (queue_concat
                      (stack_statement_list st_list)
                        (enqueue (stack_op.GoPoint point_type.Break))))))
      (stack_case_statements other))" |
(*"stack_statement (statement.IterSt (iter_statement.ForSt (for_statement.ForSt var_name (exp1,exp2,exp_option) st_list))) = " |*)
"stack_statement (statement.IterSt (iter_statement.WhileSt (while_statement.WhileSt exp (statement_list.StList st_list)))) = 
 queue_list_to_queue
   [(enqueue (stack_op.WhileStatement (stack_expr exp))),
    (enqueue (stack_op.StatementList (stack_statement_list st_list))),
    (enqueue (stack_op.SetPoint point_type.Break))]" |
"stack_statement (statement.IterSt (iter_statement.RepeatSt (repeat_statement.RepeatSt (statement_list.StList st_list) exp))) = 
  (let st_queue = (enqueue (stack_op.StatementList (stack_statement_list st_list))) 
    in queue_list_to_queue
   [st_queue,
    (enqueue (stack_op.WhileStatement (stack_expr exp))),
    st_queue,
    (enqueue (stack_op.SetPoint point_type.Break))])" |
"stack_statement (statement.ResetSt) = enqueue (stack_op.ResetTimer)" |
"stack_statement (FBInvocation (fb_name, param_assign_list)) = enqueue (stack_op.FunctionBlockCall fb_name param_assign_list)"




(*
definition get_val :: "(string, nat) fmap" where
  "get_val = fmempty"

value "(fmlookup (fmupd ''val'' 0 get_val) ''val'')"
*)
end