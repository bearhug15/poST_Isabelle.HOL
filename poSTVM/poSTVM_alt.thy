theory poSTVM_alt
  imports 
    "~~/poST/poSTVM/poSTVM_state_alt" 
begin
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

function (sequential) skip_expr :: "expr_stack \<Rightarrow> expr_stack" where 
  "skip_expr [] = []"
| "skip_expr ((expr_op.Unary _)#other)= skip_expr other"
| "skip_expr ((expr_op.Binary _)#other)= skip_expr (skip_expr other)"
| "skip_expr ((expr_op.Value _)#other) = other"
| "skip_expr ((expr_op.Get _)#other) = other"
| "skip_expr ((expr_op.GetArray _)#other) = skip_expr other"
| "skip_expr ((expr_op.CheckProcStat _ _)#other) = other"
| "skip_expr ((expr_op.FunctionCall _ _)#other) = other"
  by pat_completeness auto

lemma length_skip_expr [termination_simp]:
    "skip_expr_dom xs \<Longrightarrow> length (skip_expr xs) \<le> length xs"
  by (induction xs rule: skip_expr.pinduct) (auto simp: skip_expr.psimps)

termination skip_expr by lexicographic_order

lemma skip_expr_lessening:
  "length (skip_expr xs) \<le> length xs"
  by (induction xs rule: skip_expr.induct) auto

lemma shift_skip_expr_lessening:
  "length (skip_expr (skip_expr xs)) \<le> length (skip_expr xs)"
  by (induction xs rule: skip_expr.induct) (auto simp add: skip_expr_lessening)

lemma skip_expr_lessening_suc:
  "length (skip_expr xs) \<le> Suc (length xs)"
  by (induction xs rule: skip_expr.induct) (auto simp add: skip_expr_lessening)

lemma double_skip_expr_lessening : 
    "length (skip_expr (skip_expr xs)) \<le> length xs"
  by (induction xs rule: skip_expr.induct) (auto simp add: skip_expr_lessening  Nat.le_SucI Orderings.preorder_class.order.trans)

fun skip_exprs :: "nat \<Rightarrow> expr_stack \<Rightarrow> expr_stack" where
  "skip_exprs (Suc n) [] = []"
| "skip_exprs (Suc n) ((expr_op.Unary _)#other)= skip_exprs (Suc n) other"
| "skip_exprs (Suc n) ((expr_op.Binary _)#other)= skip_exprs (Suc (Suc n)) other"
| "skip_exprs (Suc n) ((expr_op.Value _)#other) = skip_exprs n other"
| "skip_exprs (Suc n) ((expr_op.Get _)#other) = skip_exprs n other"
| "skip_exprs (Suc n) ((expr_op.GetArray _)#other) = skip_exprs (Suc n) other"
| "skip_exprs (Suc n) ((expr_op.CheckProcStat _ _)#other) = skip_exprs n other"
| "skip_exprs (Suc n) ((expr_op.FunctionCall _ _)#other) = skip_exprs n other"

fun get_sev_expr :: "nat \<Rightarrow> expr_stack \<Rightarrow> expr_stack list" where
  "get_sev_expr 0 _ = []"
| "get_sev_expr (Suc n) [] = []"
| "get_sev_expr (Suc n) ((expr_op.Unary unary_op_option)#other) = 
    (case (get_sev_expr (Suc n) other) of
    (first#rest) \<Rightarrow> ((expr_op.Unary unary_op_option) # first) # rest)"
| "get_sev_expr (Suc n) ((expr_op.Binary binary_op)#other) =
    (case (get_sev_expr (Suc (Suc n)) other) of
    (first#second#rest) \<Rightarrow> ((expr_op.Binary binary_op) # first @ second) # rest)"
| "get_sev_expr (Suc n) ((expr_op.Value val)#other) =
    [expr_op.Value val] # (get_sev_expr n other)"
| "get_sev_expr (Suc n) ((expr_op.Get val)#other) =
    [expr_op.Get val] # (get_sev_expr n other)"
| "get_sev_expr (Suc n) ((expr_op.GetArray val)#other) =
    (case (get_sev_expr (Suc n) other) of
    (first#rest) \<Rightarrow> ((expr_op.GetArray val) # first) # rest)"
| "get_sev_expr (Suc n) ((expr_op.CheckProcStat val1 val2)#other) =
    [expr_op.CheckProcStat val1 val2] # (get_sev_expr n other)"
| "get_sev_expr (Suc n) ((expr_op.FunctionCall val1 val2)#other) =
    [expr_op.FunctionCall val1 val2] # (get_sev_expr n other)"


definition get_one_expr :: "expr_stack \<Rightarrow> expr_stack" where 
  "get_one_expr st = (nth (get_sev_expr 1 st) 0)"

definition get_expr :: "expr_stack \<Rightarrow> expr_stack * expr_stack" where
"get_expr st = ((get_one_expr st), (skip_expr st))"

text "Unwind stack until end or break point returning stack starting with the following instruction"
fun skip_after_break :: "statement_stack \<Rightarrow> statement_stack" where
"skip_after_break [] = []" |
"skip_after_break ((statement_op.SetPoint point_type.Break)#other) = other" |
"skip_after_break (_#other) = other"

text "Unwind stack until end or exit point returning stack starting with the following instruction"
fun skip_after_exit :: "statement_stack \<Rightarrow> statement_stack" where
"skip_after_exit [] = []" |
"skip_after_exit ((statement_op.SetPoint point_type.Exit)#other) = other" |
"skip_after_exit (_#other) = other"

text "Unwind stack until end or return point returning stack starting with the following instruction"
fun skip_after_return :: "statement_stack \<Rightarrow> statement_stack" where
"skip_after_return [] = []" |
"skip_after_return ((statement_op.SetPoint point_type.Return)#other) = other" |
"skip_after_return (_#other) = other"

text "Skipping statement list instruction if it next"
fun skip_statement_list :: "statement_stack \<Rightarrow> statement_stack" where
"skip_statement_list [] = []" |
"skip_statement_list ((statement_op.StatementList loc_stack)#other) = other" |
"skip_statement_list other = other"

text "Converting stack Values to list of basic values. Assuming stack has only Value operationss"
fun values_to_basics :: "expr_stack \<Rightarrow> basic_post_type list" where
  "values_to_basics [] = []" 
| "values_to_basics ((expr_op.Value val)#other) = val # (values_to_basics other)" 
| "values_to_basics other = [] "

fun get_cases :: "statement_stack \<Rightarrow> statement_stack * statement_stack" where
  "get_cases [] = ([],[])"
| "get_cases ((statement_op.CaseStatement nat_list)#(statement_op.StatementList st_list)#other) =
    (let (cases,rest) = get_cases other
      in ((statement_op.CaseStatement nat_list)#(statement_op.StatementList st_list)#cases,rest))"
| "get_cases other = ([],other)"

text "Checking if value contains in list of values "
primrec contains_basic :: "nat list \<Rightarrow> basic_post_type \<Rightarrow> bool" where
"contains_basic [] _ = False" |
"contains_basic (val1#other) val2 = 
  (if (basic_post_type_eq (basic_post_type.Nat val1) val2) 
    then True
    else (contains_basic other val2))"

fun exec_sev_expr :: "nat \<Rightarrow> expr_stack \<Rightarrow> model_state \<Rightarrow> (basic_post_type option) list" where
  "exec_sev_expr 0 _ st = [None]"
| "exec_sev_expr (Suc n) [] st = [None]"
| "exec_sev_expr (Suc n) ((expr_op.Unary unary_op_option)#other) st = 
  (case (unary_op_option,(exec_sev_expr (Suc n) other st)) of
    (None,(first#rest)) \<Rightarrow> (first#rest) 
  | (Some un_op,(first#rest)) \<Rightarrow> ((Some (unary_op_exec un_op (the first)))# rest))"
| "exec_sev_expr (Suc n) ((expr_op.Binary bin_op)#other) st =
  (case (exec_sev_expr (Suc (Suc n)) other st) 
    of (first#second#rest) \<Rightarrow> (Some (binary_op_exec bin_op (the first) (the second)))#rest)"
| "exec_sev_expr (Suc n) ((expr_op.Value val)#other) st = 
    (Some val)#(exec_sev_expr n other st)"
| "exec_sev_expr (Suc n) ((expr_op.Get var_name)#other) st = 
 (Some (get_symbvar_by_name st var_name))#(exec_sev_expr n other st) " 

| "exec_sev_expr (Suc n) ((expr_op.GetArray var_name) #other) st =
  (case (exec_sev_expr (Suc n) other st)
    of (first#rest) \<Rightarrow> (Some (get_arvar_by_name st var_name (the first)))#rest )" 

| "exec_sev_expr (Suc n) ((expr_op.CheckProcStat proc_name proc_stat)#other) st = 
  (Some (check_proc_status st proc_name proc_stat))#(exec_sev_expr n other st)" 
(*TO DO Function Call*)
| "exec_sev_expr (Suc n) ((expr_op.FunctionCall v1 v2)#other) st  =
  None#(exec_sev_expr n other st)" 

fun exec_expr :: "expr_stack \<Rightarrow> model_state \<Rightarrow> basic_post_type option" where
 "exec_expr st model_st = nth (exec_sev_expr 1 st model_st) 0"

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

definition unpack_bool :: "basic_post_type \<Rightarrow> bool" where
  "unpack_bool val = (case val of (basic_post_type.Bool val) \<Rightarrow> val)"

fun exec_sev_statements :: "nat \<Rightarrow> statement_stack \<Rightarrow> model_state \<Rightarrow> model_state * statement_result" where
  "exec_sev_statements 0 _ st = (st, statement_result.Continue)"
| "exec_sev_statements (Suc n) [] st = (st,statement_result.Continue)"
| "exec_sev_statements (Suc n) ((statement_op.Assign var_name exp)#other) st =
    (exec_sev_statements n other 
      (set_symbvar st var_name 
        (the (exec_expr exp st))))"
| "exec_sev_statements (Suc n) ((statement_op.AssignArray var_name exp)#other) st =
     (let (pos_stack,new_stack1) = (get_expr exp);
          (val_stack,_) = (get_expr new_stack1);
          new_st = (set_arvar st var_name (the (exec_expr pos_stack st)) (the (exec_expr val_stack st)))
        in (exec_sev_statements n other new_st))"
(*TO DO FunctionBlockCall 
| "exec_sev_statements (Suc n) ((stack_op.FunctionBlockCall fb_name param_assign_list )#other) st = "
*)
| "exec_sev_statements (Suc n) ((statement_op.SetPoint p)#other) st = (exec_sev_statements n other st)"
| "exec_sev_statements (Suc n) ((statement_op.GoPoint p)#other) st = 
    (case p of 
      point_type.Break \<Rightarrow> (st, statement_result.Break)
    | point_type.Exit \<Rightarrow>  (st, statement_result.Exit)
    | point_type.Return \<Rightarrow>  (st, statement_result.Return))"
| "exec_sev_statements (Suc n) ((statement_op.SetState state_name_option)#other) st =
    (case state_name_option of
    None \<Rightarrow> (st, statement_result.NextState) |
    (Some st_name) \<Rightarrow> (set_state st st_name, statement_result.Return))"
| "exec_sev_statements (Suc n) ((statement_op.ProcessStatement proc_name_option proc_mod)#other) st =
  (case proc_name_option of
    None \<Rightarrow> 
      (case proc_mod of
        (process_mod.Restart) \<Rightarrow> (reset_same_process st, statement_result.Return)
      | (process_mod.Stop) \<Rightarrow> (stop_same_process st, statement_result.Return)
      | (process_mod.Error) \<Rightarrow> (error_same_process st, statement_result.Return))
  | (Some proc_name) \<Rightarrow> 
      (exec_sev_statements n other
        (case proc_mod of
          (process_mod.Restart) \<Rightarrow> (reset_process st proc_name)
        | (process_mod.Stop) \<Rightarrow> (stop_process st proc_name)
        | (process_mod.Error) \<Rightarrow> (error_process st proc_name))))"
(*| "exec_sev_statements (Suc n) ((statement_op.IfStatement exp)#(statement_op.StatementList st_stack)#other) st =
      (if (unpack_bool (the (exec_expr exp st))) 
        then 
          (let (new_st,st_result) = (exec_sev_statements (length st_stack) st_stack st)
              in (case st_result of
                    (statement_result.Break) => (exec_sev_statements n (skip_after_break other) new_st)
                  | (_) \<Rightarrow> (new_st,st_result)))
        else 
          (exec_sev_statements n other st))"*)
| "exec_sev_statements (Suc n) ((statement_op.StatementList loc_stack)#other) st =
 (let (new_st,st_res) = (exec_sev_statements (length loc_stack) loc_stack st) in 
  (case st_res of
    statement_result.Break \<Rightarrow> (exec_sev_statements n (skip_after_break other) new_st) |
    statement_result.Continue \<Rightarrow> (exec_sev_statements n other new_st) |
    _ \<Rightarrow> (new_st,st_res)))"
| "exec_sev_statements (Suc n) ((statement_op.WhileStatement exp)#(statement_op.StatementList loc_stack)#other) =
    "


end