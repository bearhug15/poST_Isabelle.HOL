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

lemma skip_expr_lessening_suc:
  "length (skip_expr xs) \<le> Suc (length xs)"
  by (induction xs rule: skip_expr.induct) (auto simp add: skip_expr_lessening)

find_theorems funpow_Suc_right

find_theorems " _ \<le> _ \<Longrightarrow> _ \<le> _ \<Longrightarrow> _ \<le> _"

lemma double_skip_expr_lessening : 
    "length (skip_expr (skip_expr xs)) \<le> length xs"
  by (induction xs rule: skip_expr.induct) (auto simp add: skip_expr_lessening  Nat.le_SucI Orderings.preorder_class.order.trans)

fun skip_exprs :: "nat \<Rightarrow> stack \<Rightarrow> stack" where
  "skip_exprs (Suc n) [] = []"
| "skip_exprs (Suc n) ((stack_op.Unary _)#other)= skip_exprs (Suc n) other"
| "skip_exprs (Suc n) ((stack_op.Binary _)#other)= skip_exprs (Suc (Suc n)) other"
| "skip_exprs (Suc n) ((stack_op.Value _)#other) = skip_exprs n other"
| "skip_exprs (Suc n) ((stack_op.Get _)#other) = skip_exprs n other"
| "skip_exprs (Suc n) ((stack_op.GetArray _)#other) = skip_exprs (Suc n) other"
| "skip_exprs (Suc n) ((stack_op.CheckProcStat _ _)#other) = skip_exprs n other"
| "skip_exprs (Suc n) ((stack_op.FunctionCall _ _)#other) = skip_exprs n other"
| "skip_exprs (Suc n) other = other"



fun get_sev_expr :: "nat \<Rightarrow> stack \<Rightarrow> stack list" where
  "get_sev_expr 0 _ = []"
| "get_sev_expr (Suc n) [] = []"
| "get_sev_expr (Suc n) ((stack_op.Unary unary_op_option)#other) = 
    (case (get_sev_expr (Suc n) other) of
    (first#rest) \<Rightarrow> ((stack_op.Unary unary_op_option) # first) # rest)"
| "get_sev_expr (Suc n) ((stack_op.Binary binary_op)#other) =
    (case (get_sev_expr (Suc (Suc n)) other) of
    (first#second#rest) \<Rightarrow> ((stack_op.Binary binary_op) # first @ second) # rest)"
| "get_sev_expr (Suc n) ((stack_op.Value val)#other) =
    [stack_op.Value val] # (get_sev_expr n other)"
| "get_sev_expr (Suc n) ((stack_op.Get val)#other) =
    [stack_op.Get val] # (get_sev_expr n other)"
| "get_sev_expr (Suc n) ((stack_op.GetArray val)#other) =
    (case (get_sev_expr (Suc n) other) of
    (first#rest) \<Rightarrow> ((stack_op.GetArray val) # first) # rest)"
| "get_sev_expr (Suc n) ((stack_op.CheckProcStat val1 val2)#other) =
    [stack_op.CheckProcStat val1 val2] # (get_sev_expr n other)"
| "get_sev_expr (Suc n) ((stack_op.FunctionCall val1 val2)#other) =
    [stack_op.FunctionCall val1 val2] # (get_sev_expr n other)"
| "get_sev_expr (Suc n) other = []"

definition get_one_expr :: "stack \<Rightarrow> stack" where 
  "get_one_expr st = (nth (get_sev_expr 1 st) 0)"

value "get_one_expr [(stack_op.Value (basic_post_type.Nat 0)), (stack_op.Value (basic_post_type.Nat 1))]" 
(*
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

lemma skip_get_one_expr [termination_simp]:
      "get_one_expr_dom xs \<Longrightarrow> length (get_one_expr xs) = (length xs) - length (skip_expr xs)"
  apply (induct xs rule:get_one_expr.pinduct)
  apply (auto simp add: get_one_expr.psimps skip_expr_lessening Nat.Suc_diff_le double_skip_expr_lessening)
  done

lemma buff [termination_simp]:
    "get_one_expr_dom xs \<Longrightarrow> "


lemma length_get_one_expr [termination_simp]:
    "get_one_expr_dom xs \<Longrightarrow> length (get_one_expr xs) \<le> (length xs)"
  apply (induction xs rule: get_one_expr.pinduct) 
  apply (auto simp add: get_one_expr.psimps) 
  done

termination get_one_expr by lexicographic_order
*)
(*
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
*)
definition get_expr :: "stack \<Rightarrow> stack * stack" where
"get_expr st = ((get_one_expr st), (skip_expr st))"

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
  "values_to_basics [] = []" 
| "values_to_basics ((stack_op.Value val)#other) = val # (values_to_basics other)" 
| "values_to_basics other = [] "

fun skip_case :: "stack \<Rightarrow> stack" where
  "skip_case [] = []"
| "skip_case ((stack_op.Value val)#other) = skip_case other"
| "skip_case ((stack_op.StatementList loc_stack)#other) = other"
| "skip_case other = other"

lemma skip_case_lessening:
  "length xs \<ge> length (skip_case xs)"
  by (induct xs rule: skip_case.induct) auto

fun get_case :: "stack \<Rightarrow> ((basic_post_type list) * stack_op) list" where
  "get_case [] = []"
| "get_case ((stack_op.Value val)#other) =
  (case (get_case other) of
     ((b_list,st_list)#oth) \<Rightarrow> [(val#b_list,st_list)])"
| "get_case ((stack_op.StatementList loc_stack)#oth) =
  [([],(stack_op.StatementList loc_stack))]"
| "get_case other = []"

fun get_one_case :: "stack \<Rightarrow> stack * (((basic_post_type list) * stack_op) list)" where
  "get_one_case st = (skip_case st, get_case st)"

definition add_value_to_case :: "basic_post_type \<Rightarrow> (((basic_post_type list) * stack_op) list) \<Rightarrow> (((basic_post_type list) * stack_op) list)" where
  "add_value_to_case val one_case = 
  (let (val_list,st_list) = (nth one_case 0)
    in [(val#val_list,st_list)])"

fun get_sev_cases :: "nat \<Rightarrow> stack \<Rightarrow> stack * (((basic_post_type list) * stack_op) list)" where
  "get_sev_cases (Suc n) [] = ([],[])"
| "get_sev_cases (Suc n) ((stack_op.SetPoint point_type.Break)#other) = (other,[])"
| "get_sev_cases (Suc n) ((stack_op.Value val)#other) = 
    (let (new_stack1,one_case) = get_one_case other;
         new_one_case = (add_value_to_case val one_case);
         (new_stack2,cases) = get_sev_cases n new_stack1
      in (new_stack2,new_one_case@cases))"
| "get_sev_cases (Suc n) other = (other,[])"

text "Splitting stack to all following case branches from stack and other stack. Collects 256 branches"
definition get_cases :: "stack \<Rightarrow> stack * (((basic_post_type list) * stack_op) list)" where
"get_cases st = get_sev_cases (length st) st"


text "Checking if value contains in list of values "
primrec check_case :: "basic_post_type list \<Rightarrow> basic_post_type \<Rightarrow> bool" where
"check_case [] _ = False" |
"check_case (val1#other) val2 = 
  (if (basic_post_type_eq val1 val2) 
    then True
    else (check_case other val2))"

primrec rest_list :: "'a list \<Rightarrow> 'a list" where
  "rest_list [] = []"
| "rest_list (el#other) = other"

fun exec_sev_expr :: "nat \<Rightarrow> stack \<Rightarrow> model_state \<Rightarrow> (basic_post_type option) list" where
  "exec_sev_expr 0 _ st = [None]"
| "exec_sev_expr (Suc n) [] st = [None]"
| "exec_sev_expr (Suc n) ((stack_op.Unary unary_op_option)#other) st = 
  (case (unary_op_option,(exec_sev_expr (Suc n) other st)) of
    (None,(first#rest)) \<Rightarrow> (first#rest) 
  | (Some un_op,(first#rest)) \<Rightarrow> ((Some (unary_op_exec un_op (the first)))# rest))"
| "exec_sev_expr (Suc n) ((stack_op.Binary bin_op)#other) st =
  (case (exec_sev_expr (Suc (Suc n)) other st) 
    of (first#second#rest) \<Rightarrow> (Some (binary_op_exec bin_op (the first) (the second)))#rest)"
| "exec_sev_expr (Suc n) ((stack_op.Value val)#other) st = 
    (Some val)#(exec_sev_expr n other st)"
| "exec_sev_expr (Suc n) ((stack_op.Get var_name)#other) st = 
 (Some (get_symbvar_by_name st var_name))#(exec_sev_expr n other st) " 

| "exec_sev_expr (Suc n) ((stack_op.GetArray var_name) #other) st =
  (case (exec_sev_expr (Suc n) other st)
    of (first#rest) \<Rightarrow> (Some (get_arvar_by_name st var_name (the first)))#rest )" 

| "exec_sev_expr (Suc n) ((stack_op.CheckProcStat proc_name proc_stat)#other) st = 
  (Some (check_proc_status st proc_name proc_stat))#(exec_sev_expr n other st)" 
(*TO DO Function Call*)
| "exec_sev_expr (Suc n) ((stack_op.FunctionCall v1 v2)#other) st  =
  None#(exec_sev_expr n other st)" 
| "exec_sev_expr _ other _ = [None]"

fun exec_expr :: "stack \<Rightarrow> model_state \<Rightarrow> basic_post_type option" where
 "exec_expr st model_st = nth (exec_sev_expr 1 st model_st) 0"

(*
text "Executing first full expressions from stack. Assumes stack starting from some expression operation. Assuming all variables initialized"
fun exec_expr :: "stack \<Rightarrow> model_state \<Rightarrow> basic_post_type option" where
"exec_expr [] st = None" |

"exec_expr ((stack_op.Unary unary_op_option)#other) st = 
  (let res = (exec_expr other st) 
    in (case unary_op_option of 
      None \<Rightarrow> res | 
      (Some un_op) \<Rightarrow> (Some (unary_op_exec un_op (the res)))))" |

"exec_expr ((stack_op.Binary bin_op)#other) st = 
  (let (left,new_stack) = (get_expr other )
  in (Some (binary_op_exec 
            bin_op 
            (the (exec_expr left st)) 
            (the (exec_expr new_stack st)))))" |

"exec_expr ((stack_op.Value val)#other) st = 
  (Some val)" |

"exec_expr ((stack_op.Get var_name)#other) st = 
 Some (get_symbvar_by_name st var_name) " |

"exec_expr ((stack_op.GetArray var_name) #other) st =
  (let pos = (the (exec_expr other st)) 
    in (Some (get_arvar_by_name st var_name pos)))" |

"exec_expr ((stack_op.CheckProcStat proc_name proc_stat)#[]) st = 
  (let (_,_,_, cur_proc_stat,_) = (get_proc_state st proc_name) in 
  Some (basic_post_type.Bool (proc_status_is cur_proc_stat proc_stat)))" |
(*TO DO Function Call*)
"exec_expr ((stack_op.FunctionCall v1 v2)#other)st  =
  None" |
"exec_expr lt _ = None"
*)

text "Initialization of array"
fun initialize_array :: "model_state \<Rightarrow> stacked_var_init \<Rightarrow> stacked_var_init" where
"initialize_array st var= 
  (case var of 
    (stacked_var_init.Array interval values (Some expr_list)) \<Rightarrow> 
      (stacked_var_init.Array
        (case interval of
          (stacked_array_interval.Expr exp1 exp2) \<Rightarrow> 
            (stacked_array_interval.Int (basic_post_type_to_int (the (exec_expr exp1 st))) (basic_post_type_to_int (the (exec_expr exp2 st)))) |
          (stacked_array_interval.Int int1 int2) =>
            (stacked_array_interval.Int int1 int2))
        (map 
          (\<lambda>exp. (the (exec_expr exp st)))
          expr_list)
        None) |
    (stacked_var_init.Array interval values None) \<Rightarrow> 
      (stacked_var_init.Array 
        (case interval of
          (stacked_array_interval.Expr exp1 exp2) \<Rightarrow> 
            (stacked_array_interval.Int (basic_post_type_to_int (the (exec_expr exp1 st))) (basic_post_type_to_int (the (exec_expr exp2 st)))) |
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
    (stacked_proc_var.Var stacked_vars) \<Rightarrow> (stacked_proc_var.Var (initialize_stacked_vars st stacked_vars))|
    (stacked_proc_var.ProcessVar var) \<Rightarrow> (stacked_proc_var.ProcessVar var)|
    (stacked_proc_var.InOutVar stacked_vars) \<Rightarrow> (stacked_proc_var.InOutVar (initialize_stacked_vars st stacked_vars)) |
    (stacked_proc_var.InVar stacked_vars) \<Rightarrow> (stacked_proc_var.InVar (initialize_stacked_vars st stacked_vars))|
    (stacked_proc_var.OutVar stacked_vars) \<Rightarrow> (stacked_proc_var.OutVar (initialize_stacked_vars st stacked_vars)))
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

(*statement_result = Break | Continue | Exit | Return | Reset | NextState*)

primrec get_first_imp_res :: "statement_result list \<Rightarrow> statement_result" where
  "get_first_imp_res [] = statement_result.Continue"
| "get_first_imp_res (st_res#other) = 
  (case st_res of
    (statement_result.Continue) \<Rightarrow> (get_first_imp_res other)
  | (statement_result.Return) \<Rightarrow> (statement_result.Return)
  | (statement_result.Exit) \<Rightarrow> (statement_result.Exit)
  | (statement_result.Break) \<Rightarrow> (statement_result.Break)
  | (statement_result.Reset) \<Rightarrow> (statement_result.Reset)
  | (statement_result.NextState) \<Rightarrow> (statement_result.NextState))"

fun exec_sev_statement :: "nat \<Rightarrow> stack \<Rightarrow> model_state \<Rightarrow> model_state * statement_result" (* and
  exec_case_statement :: "model_state \<Rightarrow> ((basic_post_type list) * stack_op) list \<Rightarrow> basic_post_type \<Rightarrow> model_state * statement_result"*) where
  "exec_sev_statement 0 stack st = (st,statement_result.Continue)"
| "exec_sev_statement (Suc n) [] st = (st,statement_result.Return)"
| "exec_sev_statement (Suc n) ((stack_op.Assign var_name )#other) st =
    (let (val_stack, new_stack) = (get_expr other);
          new_st = (set_symbvar st var_name (the (exec_expr val_stack st))) 
    in (exec_sev_statement n new_stack new_st))"
| "exec_sev_statement (Suc n) ((stack_op.AssignArray var_name)#other) st =
    (let (pos_stack,new_stack1) = (get_expr other);
         (val_stack,new_stack2) = (get_expr new_stack1);
          new_st = (set_arvar st var_name (the (exec_expr pos_stack st)) (the (exec_expr val_stack st)))
    in (exec_sev_statement n new_stack2 new_st))"
(*TO DO FunctionBlockCall 
| "exec_sev_statement (Suc n) ((stack_op.FunctionBlockCall fb_name param_assign_list )#other) st = (st,statement_result.Continue)"
*)
| "exec_sev_statement (Suc n) ((stack_op.SetPoint p)#other) st = (exec_sev_statement n other st)"
| "exec_sev_statement (Suc n) ((stack_op.GoPoint p)#other) st = 
    (case p of 
      point_type.Break \<Rightarrow> (st, statement_result.Break)|
      point_type.Exit \<Rightarrow>  (st, statement_result.Exit)|
      point_type.Return \<Rightarrow>  (st, statement_result.Return))"
| "exec_sev_statement (Suc n) ((stack_op.SetState state_name_option)#other) st =
    (case state_name_option of
    None \<Rightarrow> (st, statement_result.NextState) |
    (Some st_name) \<Rightarrow> (set_state st st_name, statement_result.Return))"
| "exec_sev_statement (Suc n) ((stack_op.ProcessStatement proc_name_option proc_mod)#other) st =
  (case proc_mod of
    (process_mod.Restart) \<Rightarrow> 
      (case proc_name_option of
        None \<Rightarrow> (reset_same_process st, statement_result.Return) 
      | (Some proc_name) \<Rightarrow> (exec_sev_statement n other (reset_process st proc_name))) |
    (process_mod.Stop) \<Rightarrow> 
      (case proc_name_option of
        None \<Rightarrow> (stop_same_process st, statement_result.Return) 
      | (Some proc_name) \<Rightarrow> (exec_sev_statement n other (stop_process st proc_name))) |
    (process_mod.Error) \<Rightarrow> 
      (case proc_name_option of
        None \<Rightarrow> (error_same_process st, statement_result.Return) 
      | (Some proc_name) \<Rightarrow> (exec_sev_statement n other (error_process st proc_name))))"
| "exec_sev_statement (Suc n) ((stack_op.IfStatement loc_stack )#(stack_op.StatementList st_stack)#other) st =
  (case (exec_expr loc_stack st) of 
    (Some (basic_post_type.Bool val)) \<Rightarrow> 
      (if val 
        then 
          (let (new_st,st_result) = (exec_sev_statement (length st_stack) st_stack st)
              in (case st_result of
                    (statement_result.Break) => (exec_sev_statement n (skip_after_break other) new_st)
                  | (_) \<Rightarrow> (new_st,st_result)))
        else 
          (exec_sev_statement (Suc n) other st)))"
(*| "exec_sev_statement (Suc n) ((stack_op.CaseStatement loc_stack)#other) st =
    (let (new_stack,cases_list) = get_cases other;
          value = the (exec_expr loc_stack st);
          (new_st,st_res) = exec_case_statement st cases_list value 
      in (case st_res of
            (statement_result.Break) \<Rightarrow> (exec_sev_statement n (skip_after_break new_stack) new_st)
          | (statement_result.Continue) \<Rightarrow> (exec_sev_statement (Suc n) new_stack new_st)
          | (_) \<Rightarrow> (new_st,st_res)))"
| "exec_case_statement st [] _ = (st, statement_result.Continue)" 
| "exec_case_statement st ((values,st_list)#other) value =
  (if (check_case values value)
    then (exec_sev_statement 1 [st_list] st)
    else (exec_case_statement st other value))" 
(*TO DO correct statement list*)
| "exec_statement_list stack st = (exec_sev_statement 1 stack st)"*)


(*
lemma length_exec_sev_statement [termination_simp]:
  "exec_sev_statement_dom n stack st \<Longrightarrow> (length stack) \<le> (length (fst (exec_sev_statement n stack st)))"
  by (induct xs rule: exec_sev_statement_exec_statement_list.pinduct)
*)

(*
text "Executing first full statement from stack returning other stack part modified model state and result of statement. Assuming stack starting from some statement operation. Assuming all variables initialized."
function (sequential) exec_statement :: "stack \<Rightarrow> model_state \<Rightarrow> stack * model_state * statement_result" and
  exec_case_statement :: "model_state \<Rightarrow> ((basic_post_type list) * stack_op) list \<Rightarrow> basic_post_type \<Rightarrow>model_state * statement_result" where
"exec_statement [] st = ([],st,statement_result.Return)" |

"exec_statement ((stack_op.Assign var_name )#other) st = 
  (let (val_stack, new_stack) = (get_expr other)
      in (new_stack,(set_symbvar st var_name (the (exec_expr val_stack st))),statement_result.Continue))" |
"exec_statement ((stack_op.AssignArray var_name)#other) st = 
    (let (pos_stack,new_stack1) = (get_expr other);
         (val_stack,new_stack2) = (get_expr new_stack1) in
        (new_stack2,(set_arvar st var_name (the (exec_expr pos_stack st)) (the (exec_expr val_stack st))),statement_result.Continue))" |
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
  (case (exec_expr loc_stack st) of 
    (Some (basic_post_type.Bool val)) \<Rightarrow> 
      (if val 
        then (case other of 
          ((stack_op.StatementList loc_stack)#new_other) \<Rightarrow> 
            (let (_,new_st,st_result) = (exec_statement loc_stack st) in (new_other,new_st,st_result)))
        else (let (new_stack) = (skip_statement_list other) in (exec_statement new_stack st))))" |
"exec_statement ((stack_op.CaseStatement loc_stack)#other) st =
  (let (new_stack,cases_list) = get_cases other;
       value = the (exec_expr loc_stack st);
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
  by pat_completeness auto
print_theorems

lemma length_exec_statement [termination_simp]:
  "exec_statement_dom xs st \<Longrightarrow> length (fst (exec_statement xs st)) \<le> length xs "
  by (induct xs rule: exec_statement_exec_case_statement.pinduct) (auto simp: exec_statement.psimps)
*)


(*TO DO while branch. Решил отложить эту ветвь и сначала разобраться с доказательством конечности остальных ветвей, т.к. циклы потенциально могут быть бесконечными и я пока не уверен что с таким делать*)
 
(*
definition get_val :: "(string, nat) fmap" where
  "get_val = fmempty"

value "(fmlookup (fmupd ''val'' 0 get_val) ''val'')"
*)
end