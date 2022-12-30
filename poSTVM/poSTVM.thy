theory poSTVM
  imports 
    "~~/poST/poSTVM/poSTVM_state"
begin

text "Type describing result of processing statement"
datatype statement_result = Break | Continue | Exit | Return | Reset | NextState

text "Executing unary operation"
definition unary_op_exec :: "unary_op => basic_post_type \<Rightarrow> basic_post_type" where
"unary_op_exec op var = (case op of unary_op.Not \<Rightarrow> (basic_post_type_not var) | unary_op.Minus \<Rightarrow> (basic_post_type_minus var))"

text "Executing binary operation"
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

text "Splitting stack to first part describing expression and other stack. Assuming stack starting with some expression operation"
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

text "Unwind stack until end or break point returning stack starting with the following instruction"
fun skip_after_break :: "stack \<Rightarrow> stack" where
"skip_after_break [] = []" |
"skip_after_break ((stack_op.SetPoint point_type.Break)#other) = other" |
"skip_after_break (_#other) = other"

text "Unwind stack until end or exit point returning stack starting with the following instruction"
fun skip_after_exit :: "stack \<Rightarrow> stack" where
"skip_after_exit [] = []" |
"skip_after_exit ((stack_op.SetPoint point_type.Exit)#other) = other" |
"skip_after_exit (_#other) = other"

text "Unwind stack until end or return point returning stack starting with the following instruction"
fun skip_after_return :: "stack \<Rightarrow> stack" where
"skip_after_return [] = []" |
"skip_after_return ((stack_op.SetPoint point_type.Return)#other) = other" |
"skip_after_return (_#other) = other"

text "Skipping statement list instruction if it next"
fun skip_statement_list :: "stack \<Rightarrow> stack" where
"skip_statement_list [] = []" |
"skip_statement_list ((stack_op.StatementList loc_stack)#other) = other" |
"skip_statement_list other = other"

(*
fun skip_if :: "stack \<Rightarrow> stack" where
"skip_if [] = []" |
"skip_if ((stack_op.IfStatement loc_stack1)#(stack_op.StatementList loc_stack2)#other) = (other)" |
"skip_if other = other"
*)

text "Splitting stack to seq of Values and other stack. Assuming stack starting with Value"
fun get_values :: "stack \<Rightarrow> stack * stack" where
"get_values [] = ([],[])" |
"get_values ((stack_op.Value val)#other) = (let (res,stack_res) = (get_values other) in ((stack_op.Value val)#res,stack_res) )" |
"get_values other =([], other)"

text "Converting stack Values to list of basic values. Assuming stack has only Value operationss"
fun values_to_basics :: "stack \<Rightarrow> basic_post_type list" where
"values_to_basics [] = []" |
"values_to_basics ((stack_op.Value val)#other) = val # (values_to_basics other)" |
"values_to_basics other = [] "

text "Splitting stack to all following case branches from stack and other stack"
fun get_cases :: "stack \<Rightarrow> stack * (((basic_post_type list) * stack_op) list)" where
"get_cases [] = ([],[])" |
"get_cases ((stack_op.Value val)#other) = 
  (let (values,new_st) = get_values ((stack_op.Value val)#other);
        values = values_to_basics (values) in
    (case new_st of
      ((stack_op.StatementList loc_stack)#new_stack) \<Rightarrow> 
        (let (res_stack,res_list) = get_cases new_stack in (res_stack,(values,(stack_op.StatementList loc_stack))#res_list))))" |
"get_cases st = (st,[])"

(*
fun skip_case :: "stack \<Rightarrow> stack" where
"skip_case [] = []" |
"skip_case ((stack_op.CaseStatement loc_stack)#other) = skip_after_break other" |
"skip_case other = other"
*)

text "Checking if value contains in list of values "
primrec check_case :: "basic_post_type list \<Rightarrow> basic_post_type \<Rightarrow> bool" where
"check_case [] _ = False" |
"check_case (val1#other) val2 = 
  (if (basic_post_type_eq val1 val2) 
    then True
    else (check_case other val2))"

text "Executing first full expressions from stack. Assumes stack starting from some expression operation. Assuming all variables initialized"
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
 Some (get_symbvar_by_name st var_name) " |

"exec_expr ((stack_op.GetArray var_name) #other) st =
  (let pos = (the (exec_expr other st)) 
    in (Some (get_arvar_by_name st var_name pos)))" |

"exec_expr ((stack_op.CheckProcStat proc_name proc_stat)#[]) st = 
  (let (_,_,_, cur_proc_stat,_) = (get_proc_state st proc_name) in 
  Some (basic_post_type.Bool (proc_status_is cur_proc_stat proc_stat)))" |
(*TO DO Function Call*)
"exec_expr ((stack_op.FunctionCall v1 v2)#[])st  =
  None" |
"exec_expr lt _ = None"

(*TO DO*)
text "Initialization of array"
fun initialize_array :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> model_state" where
"initialize_array st var_name= st"

(*TO DO*)
text "Initialization of symbolic variable"
fun initialize_symbolic :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> model_state" where
"initialize_symbolic st var_name= st"

(*TO DO*)
text "Initialization of process variables"
fun initialize_process_vars :: "model_state \<Rightarrow> model_state" where
"initialize_process_vars st =st"

(*TO DO*)
text "Initialization of program variables"
fun initialize_program_vars :: "model_state \<Rightarrow> model_state" where
"initialize_program_vars st =st"

text "Executing first full statement from stack returning other stack part modified model state and result of statement. Assuming stack starting from some statement operation. Assuming all variables initialized."
fun exec_statement :: "stack \<Rightarrow> model_state \<Rightarrow> stack * model_state * statement_result" and
  exec_case_statement :: "model_state \<Rightarrow> ((basic_post_type list) * stack_op) list \<Rightarrow> basic_post_type \<Rightarrow>model_state * statement_result" where
"exec_statement [] st = ([],st,statement_result.Return)" |

"exec_statement ((stack_op.Assign var_name )#other) st = 
  (let (val_stack, new_stack) = (get_expr other)
      in (new_stack,(set_symbvar st var_name (the (exec_expr val_stack))),statement_result.Continue))" |
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
    statement_result.Break \<Rightarrow> (exec_statement (skip_after_break new_stack) new_st) |
    statement_result.Continue \<Rightarrow> (exec_statement new_stack new_st) |
    statement_result.Return \<Rightarrow> (new_stack, new_st, statement_result.Continue) |
    _ \<Rightarrow> (new_stack,new_st,st_res)))"

(*TO DO while branch. Решил отложить эту ветвь и сначала разобраться с доказательством конечности остальных ветвей, т.к. циклы потенциально могут быть бесконечными и я пока не уверен что с таким делать*)

(*
definition get_val :: "(string, nat) fmap" where
  "get_val = fmempty"

value "(fmlookup (fmupd ''val'' 0 get_val) ''val'')"
*)
end