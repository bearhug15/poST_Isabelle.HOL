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
(*
text "Splitting stack to first part describing expression and other stack. Assuming stack starting with some expression operation"
function (sequential) get_expr :: "stack  \<Rightarrow> stack * stack" where
  "get_expr []  = ([], [])" |
  "get_expr ((stack_op.Unary unary_op_option)#other)  = 
    (let (expr_list,st) = (get_expr other) in ((stack_op.Unary unary_op_option) # expr_list,st))" |
  "get_expr ((stack_op.Binary binary_op)#other)  = 
    (let (expr_list1,st1) = (get_expr other);
         (expr_list2,st2) = (get_expr st1);
          new_st = ((Binary binary_op) # expr_list1) @ expr_list2 
      in (new_st,st2))" |
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
  "get_expr other  = ([],other)"
  by pat_completeness auto
termination get_expr
  apply (relation "measure (\<lambda>s. (size s))") 
      apply auto
  apply simp
  done*)
(*termination by size_change*)

function inc :: "nat list \<Rightarrow> nat list" where
"inc [] = []" |
"inc (val#other) = (val + 1) # (inc other)"
  by pat_completeness auto
termination by lexicographic_order

lemma "inc [] = []"
  apply auto
  done



function (sequential) skip_expr :: "stack \<Rightarrow> stack" where 
  "skip_expr [] = []"
| "skip_expr ((stack_op.Unary _)#other)= skip_expr other"
| "skip_expr ((stack_op.Binary _)#other)= skip_expr (skip_expr other)"
| "skip_expr ((stack_op.Value _)#other) = other"
| "skip_expr ((stack_op.Get _)#other) = other"
| "skip_expr ((stack_op.GetArray _)#other) = skip_expr other"
| "skip_expr ((stack_op.CheckProcStat _ _)#other) = other"
| "skip_expr ((stack_op.FunctionCall _ _)#other) = other"
| "skip_expr other = other"
  by pat_completeness auto

lemma length_skip_expr [termination_simp]:
    "skip_expr_dom xs \<Longrightarrow> length (skip_expr xs) \<le> length xs"
  by (induction xs rule: skip_expr.pinduct) (auto simp: skip_expr.psimps)

termination skip_expr by lexicographic_order

print_theorems

lemma skip_expr_lessening:
  "length (skip_expr xs) \<le> length xs"
  by (induction xs rule: skip_expr.induct) auto

lemma shift_skip_expr_lessening:
  "length (skip_expr (skip_expr xs)) \<le> length (skip_expr xs)"
  by (induction xs rule: skip_expr.induct) (auto simp add: skip_expr_lessening)

lemma double_skip_expr_lessening : 
    "length (skip_expr (skip_expr xs)) \<le> length xs"
  by (induction xs rule: skip_expr.induct) (auto simp add: skip_expr_lessening  Nat.le_SucI)

find_theorems " _ \<le> _ \<Longrightarrow> _ \<le> Suc _"


(*TO DO*)
function (sequential) get_one_expr :: "stack \<Rightarrow> stack" where
  "get_one_expr [] = []"
| "get_one_expr ((stack_op.Unary unary_op_option)#other) = (stack_op.Unary unary_op_option) # (get_one_expr other)"
| "get_one_expr ((stack_op.Binary binary_op)#other) =
  (let left = (get_one_expr other);
       right = (get_one_expr (skip_expr other))
    in (stack_op.Binary binary_op)#left@right)"
| "get_one_expr ((stack_op.Value val)#other) = [stack_op.Value val]"
| "get_one_expr ((stack_op.Get val)#other) = [stack_op.Get val]"
| "get_one_expr ((stack_op.GetArray val)#other) = (stack_op.GetArray val)#(get_one_expr other)"
| "get_one_expr ((stack_op.CheckProcStat val1 val2)#other) = [stack_op.CheckProcStat val1 val2]"
| "get_one_expr ((stack_op.FunctionCall val1 val2)#other) = [stack_op.FunctionCall val1 val2]"
| "get_one_expr other = []"
  by pat_completeness auto

print_theorems

lemma const_get_one_expr [termination_simp]:
      "get_one_expr_dom xs \<Longrightarrow> length ((get_one_expr xs) @ (skip_expr xs)) = length xs"
  by (induction xs rule :get_one_expr.pinduct) (auto simp: get_one_expr.psimps)

lemma const_l_get_one_expr [termination_simp]:
      "get_one_expr_dom xs \<Longrightarrow> (length (get_one_expr xs)) + (length (skip_expr xs)) = length xs"
  by (induction xs rule :get_one_expr.pinduct) (auto simp: get_one_expr.psimps)

lemma const_l_buff_get_one_expr [termination_simp]:
    "get_one_expr_dom xs \<Longrightarrow> (length (get_one_expr xs)) + (length (skip_expr xs)) = length xs"
  apply (induct xs rule:get_one_expr.pinduct)
                     apply (auto simp: get_one_expr.psimps)
  done


lemma skip_get_one_expr [termination_simp]:
      "get_one_expr_dom xs \<Longrightarrow> length (get_one_expr xs) = (length xs) - length (skip_expr xs)"
  apply (induct xs rule:get_one_expr.pinduct)
                     apply (auto simp add: get_one_expr.psimps skip_expr_lessening Nat.Suc_diff_le)
  done

lemma length_get_one_expr [termination_simp]:
    "get_one_expr_dom xs \<Longrightarrow> length (get_one_expr xs) \<le> (length xs)"
  by (induction xs rule: get_one_expr.pinduct) (auto simp add: get_one_expr.psimps const_get_one_expr const_l_get_one_expr)

termination get_one_expr by lexicographic_order

(*TO DO get_expr as combination of get_simple_expr and skip_expr*)
function (sequential) get_expr :: "stack \<Rightarrow> stack * stack" where
"get_expr [] = ([],[])"
| "get_expr ((stack_op.Unary unary_op_option)#other) = (let (res,rest) = get_expr other in ((stack_op.Unary unary_op_option)#res,rest))"
| "get_expr ((stack_op.Binary binary_op)#other) =
  (let (left,rest1)= (get_expr other);
       (right,rest2) = (get_expr rest1)
    in (((stack_op.Binary binary_op)#left@right),rest2))"
| "get_expr ((stack_op.Value val)#other) = ([stack_op.Value val],other)"
| "get_expr ((stack_op.Get val)#other) = ([stack_op.Get val],other)"
| "get_expr ((stack_op.GetArray val)#other) = (let (res,rest) = get_expr other in ((stack_op.GetArray val)#res,rest))"
| "get_expr ((stack_op.CheckProcStat val1 val2)#other) = ([stack_op.CheckProcStat val1 val2],other)"
| "get_expr ((stack_op.FunctionCall val1 val2)#other) = ([stack_op.FunctionCall val1 val2],other)"
| "get_expr other = ([],other)"
  by pat_completeness auto

lemma length_get_expr [termination_simp]:
  "get_expr_dom xs \<Longrightarrow> (let (f,s) = get_expr xs in ((length s) \<le> length xs))"
  by (induction xs rule: get_expr.pinduct) (auto simp add: get_expr.psimps)

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

definition get_ex :: "(string,nat) fmap" where
"get_ex = fmap_of_list [(''a'',1::nat), (''b'',2::nat)]"

definition self :: "(string,nat) fmap \<Rightarrow> (string,nat) fmap" where
"self v = v"

value "self (fmmap (\<lambda>x. x) get_ex)"

text "Initialization of array"
fun initialize_array :: "model_state \<Rightarrow> stacked_var_init \<Rightarrow> stacked_var_init" where
"initialize_array st var= 
  (case var of 
    (stacked_var_init.Array interval values (Some expr_list)) \<Rightarrow> 
      (stacked_var_init.Array
        (case interval of
          (stacked_array_interval.Expr exp1 exp2) \<Rightarrow> 
            (stacked_array_interval.Int (basic_post_type_to_int (the (exec_expr exp1))) (basic_post_type_to_int (the (exec_expr exp2)))) |
          (stacked_array_interval.Int int1 int2) =>
            (stacked_array_interval.Int int1 int2))
        (map 
          (\<lambda>exp. (the (exec_expr exp)))
          expr_list)
        None) |
    (stacked_var_init.Array interval values None) \<Rightarrow> 
      (stacked_var_init.Array 
        (case interval of
          (stacked_array_interval.Expr exp1 exp2) \<Rightarrow> 
            (stacked_array_interval.Int (basic_post_type_to_int (the (exec_expr exp1))) (basic_post_type_to_int (the (exec_expr exp2)))) |
          (stacked_array_interval.Int int1 int2) =>
            (stacked_array_interval.Int int1 int2)) 
        values 
        None))"

text "Initialization of symbolic variable"
fun initialize_symbolic :: "model_state \<Rightarrow> stacked_var_init  \<Rightarrow> stacked_var_init" where
"initialize_symbolic st var= 
  (case var of
    (stacked_var_init.Symbolic value (Some init_stack)) \<Rightarrow> 
      (stacked_var_init.Symbolic (the (exec_expr init_stack st)) None) |
    (stacked_var_init.Symbolic value None) \<Rightarrow> 
      (stacked_var_init.Symbolic value None))"

(*TO DO FunctionBlock init*)
text "Initialization of stacked var"
fun initialize_stacked_vars :: "model_state \<Rightarrow> stacked_vars \<Rightarrow> stacked_vars" where
"initialize_stacked_vars st vars =
  (fmmap
    (\<lambda>init.
      (case init of
        (stacked_var_init.Symbolic value init_option) \<Rightarrow> (initialize_symbolic st init) |
        (stacked_var_init.Array interval values init_option) \<Rightarrow> (initialize_array st init) |
        (stacked_var_init.FunctionBlock name) \<Rightarrow> (stacked_var_init.FunctionBlock name)) )
    vars) "

text "Initialization of proc_vars"
fun initialize_stacked_proc_vars :: "model_state \<Rightarrow> stacked_proc_var list \<Rightarrow> stacked_proc_var list" where
"initialize_stacked_proc_vars _ [] = []" |
"initialize_stacked_proc_vars st (proc_var#other) = 
  ((case proc_var of
    (stacked_proc_var.Var stacked_vars) \<Rightarrow> (stacked_proc_var.Var (initialize_stacked_vars stacked_vars))|
    (stacked_proc_var.ProcessVar var) \<Rightarrow> (stacked_proc_var.ProcessVar var)|
    (stacked_proc_var.InOutVar stacked_vars) \<Rightarrow> (stacked_proc_var.InOutVar (initialize_stacked_vars stacked_vars)) |
    (stacked_proc_var.InVar stacked_vars) \<Rightarrow> (stacked_proc_var.InVar (initialize_stacked_vars stacked_vars))|
    (stacked_proc_var.OutVar stacked_vars) \<Rightarrow> (stacked_proc_var.OutVar (initialize_stacked_vars stacked_vars)))
  #(initialize_stacked_proc_vars st other))"

(*TO DO*)
text "Initialization of process variables"
fun initialize_process_vars :: "model_state \<Rightarrow> model_state" where
"initialize_process_vars (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list) =
  (let st = (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list) 
  in  (model_state.ST 
    global_vars_list 
    (fmmap 
       (\<lambda>(var_list,proc_map,proc_name). 
          (var_list,
            (fmmap 
              (\<lambda>(var_list,v1,v2,v3,v4).
                (initialize_stacked_proc_vars st var_list,v1,v2,v3,v4))
              proc_map),
          proc_name)) 
       program_map,
      cur_prog_name) 
    fb_decl_list 
    f_decl_list))"

text "Initialization of prog_vars"
fun initialize_stacked_prog_vars :: "model_state \<Rightarrow> stacked_prog_var list \<Rightarrow> stacked_prog_var list" where
"initialize_stacked_prog_vars _ [] = []" |
"initialize_stacked_prog_vars st (prog_var#other) = 
  ((case prog_var of
    (stacked_prog_var.ExtVar stacked_vars) \<Rightarrow> (stacked_prog_var.ExtVar (initialize_stacked_vars st stacked_vars))|
    (stacked_prog_var.Var stacked_vars) \<Rightarrow> (stacked_prog_var.Var (initialize_stacked_vars st stacked_vars))|
    (stacked_prog_var.InOutVar stacked_vars) \<Rightarrow> (stacked_prog_var.InOutVar (initialize_stacked_vars st stacked_vars))|
    (stacked_prog_var.InVar stacked_vars) \<Rightarrow> (stacked_prog_var.InVar (initialize_stacked_vars st stacked_vars))|
    (stacked_prog_var.OutVar stacked_vars) \<Rightarrow> (stacked_prog_var.OutVar (initialize_stacked_vars st stacked_vars)))
   #(initialize_stacked_prog_vars st other))"

(*TO DO*)
text "Initialization of program variables"
fun initialize_program_vars :: "model_state \<Rightarrow> model_state" where
"initialize_program_vars (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list) =
  (let st = (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list)
  in (model_state.ST 
    global_vars_list 
    (fmmap 
       (\<lambda>(var_list,proc_map,proc_name). 
          (initialize_stacked_prog_vars st var_list,proc_map,proc_name)) 
       program_map,
      cur_prog_name) 
    fb_decl_list 
    f_decl_list))"

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