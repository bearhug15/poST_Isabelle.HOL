theory poSTVM_parser_alt
  imports
    "~~/poST/poST_model/poST_model" 
    "~~/poST/poST_utils/poST_vars_utils"

begin

datatype expr_op =
  Unary unary_op | 
  Binary binary_op | 
  Value basic_post_type | 
  Get symbolic_var |
  GetArray symbolic_var |
  CheckProcStat process_name proc_status |
  FunctionCall func_name "param_assign list"

type_synonym expr_stack = "expr_op list"

text "transforms expr into stack form"
fun stack_expr :: "expr \<Rightarrow> expr_stack" where
  "stack_expr (expr.Unary unary_op exp) = (expr_op.Unary unary_op)# (stack_expr exp)"
| "stack_expr (expr.Binary bin_op exp1 exp2) = ((expr_op.Binary bin_op) # (stack_expr exp1)) @ (stack_expr exp2)"
| "stack_expr (expr.Const c) = [expr_op.Value (const_to_basic c)]" 
| "stack_expr (expr.SymbolicVar var_name) = [expr_op.Get var_name ]" 
| "stack_expr (expr.ArrayVar var_name exp) = (expr_op.GetArray var_name) #(stack_expr exp)" 
| "stack_expr (expr.ProcStatEpxr proc_name proc_stat) = [expr_op.CheckProcStat proc_name proc_stat]" 
| "stack_expr (expr.FunctionCall f_name param_assign_list) = [expr_op.FunctionCall f_name param_assign_list]"
declare stack_expr.simps [simp]
declare stack_expr.elims [elim]

datatype stmt = 
  AssignSt common_var expr |
  FBInvocation func_block_name  "(param_assign list)" |
  Return |
  Exit |
  ProcessSt process_contextment |
  SetStateSt set_state_statement |
  ResetSt |
  IfSt expr stmt stmt |
  WhileSt expr stmt |
  Comb stmt stmt |
  Blank 

text "transforms case branch into if branch"
fun case_list_to_if :: "expr \<Rightarrow> case_list \<Rightarrow> expr" where
  "case_list_to_if _ [] = expr.Const (const.Bool False)"
| "case_list_to_if exp [val] = 
    expr.Binary binary_op.Eq exp (expr.Const (const.Nat val))"
| "case_list_to_if exp (val#other) = 
    expr.Binary binary_op.Or
      (expr.Binary binary_op.Eq exp (expr.Const (const.Nat val)))
      (case_list_to_if exp other)"
declare case_list_to_if.simps [simp]
declare case_list_to_if.elims [elim]

text "transforms statement into stmt" 
function (sequential) statement_to_stmt :: "statement \<Rightarrow> stmt" and
        st_list_to_stmt :: "statement list \<Rightarrow> stmt" and
        if_to_stmt :: "(expr * statement_list) list \<Rightarrow> statement_list option \<Rightarrow> stmt" and
        case_to_stmt :: "expr \<Rightarrow> (case_list *(statement list)) list \<Rightarrow> statement_list option \<Rightarrow> stmt"where
  "statement_to_stmt (statement.AssignSt cv exp) = stmt.AssignSt cv exp"
| "statement_to_stmt (statement.FBInvocation fb1 fb2) = stmt.FBInvocation fb1 fb2"
| "statement_to_stmt (statement.Return) = stmt.Return"
| "statement_to_stmt (statement.Exit) = stmt.Exit"
| "statement_to_stmt (statement.ProcessSt st) = stmt.ProcessSt st"
| "statement_to_stmt (statement.SetStateSt st) = stmt.SetStateSt st"
| "statement_to_stmt (statement.ResetSt) = stmt.ResetSt"
| "statement_to_stmt (statement.SelectSt (select_statement.IfSt branches else_option)) =(if_to_stmt branches else_option)"
| "statement_to_stmt (statement.SelectSt (select_statement.CaseSt exp cases_list else_option)) =(case_to_stmt exp cases_list else_option)"
| "st_list_to_stmt [] = stmt.Blank"
| "st_list_to_stmt (st#[]) = (statement_to_stmt st)"
| "st_list_to_stmt (st#other) = 
    stmt.Comb (statement_to_stmt st) (st_list_to_stmt other)"
| "if_to_stmt [] else_option= 
    (case else_option of
      None \<Rightarrow> stmt.Blank
    | Some st_list\<Rightarrow> st_list_to_stmt st_list)"
| "if_to_stmt (branch#other) else_option =
    (case branch of (exp,st_list) \<Rightarrow> 
      stmt.IfSt exp 
        (st_list_to_stmt st_list) 
        (if_to_stmt other else_option))"
| "case_to_stmt exp [] else_option = 
    (case else_option of
      None \<Rightarrow> stmt.Blank
    | Some st_list\<Rightarrow> st_list_to_stmt st_list)"
| "case_to_stmt exp (cas#other) else_option = 
    (case cas of (val_list,st_list) \<Rightarrow>
      stmt.IfSt 
        (case_list_to_if exp val_list)
        (st_list_to_stmt st_list)
        (case_to_stmt exp other else_option))"
| "statement_to_stmt (statement.IterSt (iter_statement.WhileSt exp st_list)) =
    stmt.WhileSt exp (st_list_to_stmt st_list)"
| "statement_to_stmt (statement.IterSt 
                        (iter_statement.RepeatSt st_list exp)) =
    (let body = (st_list_to_stmt st_list) 
      in stmt.Comb body (stmt.WhileSt exp body))"
| "statement_to_stmt (statement.IterSt 
                        (iter_statement.ForSt 
                            var_name 
                            (start,end,step_option) 
                            st_list)) =
    stmt.Comb 
      (stmt.AssignSt (common_var.Symbolic var_name) start)
      (let cond = expr.Binary 
                    binary_op.Less 
                    (expr.SymbolicVar var_name) end;
           body = (st_list_to_stmt st_list);
           step_st = stmt.AssignSt 
                      (common_var.Symbolic var_name) 
                        (expr.Binary binary_op.Sum
                          (expr.SymbolicVar var_name) 
                          (case step_option of
                            None \<Rightarrow> expr.Const (const.Nat 1)
                          | Some step \<Rightarrow> step));
           new_body = stmt.Comb body step_st
        in stmt.WhileSt cond new_body)"
  by pat_completeness auto
termination by size_change
declare statement_to_stmt.simps [simp]
declare st_list_to_stmt.simps [simp]
declare if_to_stmt.simps [simp]
declare case_to_stmt.simps [simp]
declare statement_to_stmt.elims [elim]
declare st_list_to_stmt.elims [elim]
declare if_to_stmt.elims [elim]
declare case_to_stmt.elims [elim]

text "Stacked version of variables"
datatype stacked_array_interval = Expr expr_stack expr_stack | Int int int
datatype stacked_var_init = 
  Symbolic basic_post_type "expr_stack option" |
  Array stacked_array_interval "basic_post_type list" "(expr_stack list) option" |
  FunctionBlock func_block_name
type_synonym stacked_vars = "((symbolic_var, stacked_var_init) fmap)"
(*
(*TO DO stack process var*)
text "Stacked version of process variables"
datatype stacked_proc_var = 
  Var stacked_vars |
  ProcessVar process_var_decl |
  InOutVar stacked_vars |
  InVar stacked_vars |
  OutVar stacked_vars
*)

type_synonym stacked_process_var = "process_var list"
datatype stacked_proc_var = 
    Var stacked_var_init
  | ProcessVar stacked_process_var
  | InOutVar stacked_var_init
  | InVar stacked_var_init
  | OutVar stacked_var_init

text "Extract var initializer from process var"
definition extr_stacked_proc_var_init :: "stacked_proc_var \<Rightarrow> stacked_var_init" where
"extr_stacked_proc_var_init var = 
  (case var of 
    stacked_proc_var.Var val \<Rightarrow> val
  | stacked_proc_var.InOutVar val \<Rightarrow> val
  | stacked_proc_var.InVar val \<Rightarrow> val
  | stacked_proc_var.OutVar val \<Rightarrow> val)"
declare extr_stacked_proc_var_init_def [simp]

type_synonym stacked_proc_vars = "(id,stacked_proc_var) fmap"

text "Converting array interval to it's stacked version "
definition ainter_to_sainter :: "array_interval \<Rightarrow> stacked_array_interval" where
"ainter_to_sainter ar_inter =
  (case ar_inter of
    (array_interval.Int val1 val2) \<Rightarrow> (stacked_array_interval.Int val1 val2) |
    (array_interval.Expr exp1 exp2) \<Rightarrow> (stacked_array_interval.Expr (stack_expr exp1) (stack_expr exp2)))"
declare ainter_to_sainter_def [simp]

text "Converting variable initialization to stacked version"
definition stack_var_init_decl :: "var_init_decl \<Rightarrow> stacked_var_init" where
"stack_var_init_decl decl =
  (case decl of 
    (var_init_decl.Symbolic value exp_option) \<Rightarrow> 
      (stacked_var_init.Symbolic 
        value 
        (case exp_option of (Some exp) \<Rightarrow> (Some (stack_expr exp))| None \<Rightarrow> None)) |
    (var_init_decl.Array ar_inter values array_init_option) \<Rightarrow> 
      (stacked_var_init.Array 
        (ainter_to_sainter ar_inter) 
        values 
        (case array_init_option of (Some ar_init) \<Rightarrow> (Some (map (\<lambda>exp. stack_expr exp) ar_init))| None \<Rightarrow> None)) |
    (var_init_decl.FunctionBlock fb_name) \<Rightarrow> (stacked_var_init.FunctionBlock fb_name))"
declare stack_var_init_decl_def [simp]

text "Converting map of variables to stacked version"
definition stack_var_decl :: "((symbolic_var, var_init_decl) fmap) \<Rightarrow> ((symbolic_var, stacked_var_init) fmap)" where
"stack_var_decl var_map = 
  (fmmap_keys
    (\<lambda>name vid. (stack_var_init_decl vid) ) 
    var_map)"
declare stack_var_decl_def [simp]

text "Converting process var to stacked version"
definition stack_proc_var :: "proc_var \<Rightarrow> stacked_proc_vars" where
"stack_proc_var var = 
  (case var of
    (proc_var.Var (is_const, vars)) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_proc_var.Var (stack_var_init_decl val)))vars))
  | (proc_var.ProcessVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(vals,name). (name,stacked_proc_var.ProcessVar vals)) vars))
  | (proc_var.InOutVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_proc_var.InOutVar (stack_var_init_decl val)))vars)) 
  | (proc_var.InVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_proc_var.InVar (stack_var_init_decl val)))vars))
  | (proc_var.OutVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_proc_var.OutVar (stack_var_init_decl val)))vars)))"
declare stack_proc_var_def [simp]

text "Converting process vars list to stacked version"
definition stack_proc_vars :: "proc_var list \<Rightarrow> stacked_proc_vars" where
"stack_proc_vars pl = (fold (\<lambda>val fm. (fmadd fm (stack_proc_var val))) pl fmempty)"
declare stack_proc_vars_def [simp]

datatype stacked_prog_var = 
    Var stacked_var_init
  | ExtVar stacked_var_init
  | InOutVar stacked_var_init
  | InVar stacked_var_init
  | OutVar stacked_var_init

type_synonym stacked_prog_vars = "(symbolic_var,stacked_prog_var) fmap"

text "Extract var initializer from program var"
definition extr_stacked_prog_var_init :: "stacked_prog_var \<Rightarrow> stacked_var_init" where
"extr_stacked_prog_var_init var = 
  (case var of 
    stacked_prog_var.Var val \<Rightarrow> val
  | stacked_prog_var.InOutVar val \<Rightarrow> val
  | stacked_prog_var.InVar val \<Rightarrow> val
  | stacked_prog_var.OutVar val \<Rightarrow> val)"
declare extr_stacked_prog_var_init_def [simp]

text "Converting program vars to stacked version"
definition stack_prog_var :: "prog_var \<Rightarrow> stacked_prog_vars" where
"stack_prog_var var = 
  (case var of
    (prog_var.Var (is_const, vars)) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_prog_var.Var (stack_var_init_decl val)))vars))
  | (prog_var.ExtVar (is_const, vars)) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_prog_var.ExtVar (stacked_var_init.Symbolic val None)))vars))
  | (prog_var.InOutVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_prog_var.InOutVar (stack_var_init_decl val)))vars)) 
  | (prog_var.InVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_prog_var.InVar (stack_var_init_decl val)))vars))
  | (prog_var.OutVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_prog_var.OutVar (stack_var_init_decl val)))vars)))"
declare stack_prog_var_def [simp]

text "Converting program vars list to stacked version"
definition stack_prog_vars :: "prog_var list \<Rightarrow> stacked_prog_vars" where
"stack_prog_vars pl = (fold (\<lambda>val fm. (fmadd fm (stack_prog_var val))) pl fmempty)"
declare stack_prog_vars_def [simp]

text "Stacked version of state declaration"
datatype timeout = Const const stmt | SymbolicVar symbolic_var stmt
type_synonym stacked_state = "state_name * bool * stmt * (timeout option)"

text "Converting state declaration to stacked version"
fun stack_state :: "state_decl \<Rightarrow> stacked_state" where
  "stack_state (st_name, is_looped, st_list, None) = 
  (st_name, is_looped, (st_list_to_stmt st_list), None)" 
| "stack_state (st_name, is_looped, st_list, (Some (timeout_statement.Const val sl))) = 
  (st_name, is_looped, (st_list_to_stmt st_list), (Some (timeout.Const val (st_list_to_stmt sl))))" 
| "stack_state (st_name, is_looped, st_list, (Some (timeout_statement.SymbolicVar val sl))) = 
  (st_name, is_looped, (st_list_to_stmt st_list), (Some (timeout.SymbolicVar val (st_list_to_stmt sl))))" 
declare stack_state.simps [simp]
declare stack_state.elims [elim]

text "Get state by name from list of states"
primrec get_state_by_name :: "stacked_state list \<Rightarrow> state_name \<Rightarrow> stacked_state" where
"get_state_by_name (ss#other) name = (let (st_name,_,_,_) = ss in (if st_name = name then ss else (get_state_by_name other name)) )"
declare get_state_by_name.simps [simp]

text "Get next state from name of current state"
primrec get_next_state_sub :: "stacked_state list \<Rightarrow> state_name \<Rightarrow> stacked_state option" where
  "get_next_state_sub [] _ = None"
| "get_next_state_sub (ss#other) name = 
    (let (st_name,_,_,_) = ss in
      (if st_name = name 
      then (case other of
              [] \<Rightarrow> None
            | (ss1#other) \<Rightarrow> (Some ss1)) 
      else (get_next_state_sub other name)))"
declare get_next_state_sub.simps [simp]

text "Stacked version of process declaration"
type_synonym stacked_process = "process_name * stacked_proc_vars * stacked_state list"

text "Converting process declaration to stacked version"
definition stack_process :: "process_decl \<Rightarrow> stacked_process" where
"stack_process pd =  
    (let (p_name, p_var_list, st_decl_list ) = pd in (p_name, 
    (stack_proc_vars p_var_list), 
    (map
      (\<lambda>st_decl. stack_state st_decl)
      st_decl_list)))"
declare stack_process_def [simp]

text "Stacked version of program declaration"
type_synonym stacked_program = "program_name * stacked_prog_vars * stacked_process list"

text "Converting program declaration to stacked version"
definition stack_program :: "program_decl \<Rightarrow> stacked_program" where
"stack_program pd =
  (let (p_name, p_var_list, p_decl_list) = pd in (p_name,
   (stack_prog_vars p_var_list),
   (map
      (\<lambda>p_decl. stack_process p_decl)
      p_decl_list)))"
declare stack_program_def [simp]

(*TO DO function block stacking*)
datatype stacked_func_block_var =  
  ExtVar stacked_vars |
  Var stacked_vars |
  InOutVar stacked_vars |
  InVar stacked_vars |
  OutVar stacked_vars

datatype stacked_func_var = 
  Var stacked_var_init
| InOutVar stacked_var_init
| InVar stacked_var_init
| OutVar stacked_var_init

type_synonym stacked_func_vars = "(id,stacked_func_var) fmap"

text "Converting program vars to stacked version"
definition stack_func_var :: "func_var \<Rightarrow> stacked_func_vars" where
"stack_func_var var = 
  (case var of
    (func_var.Var (is_const, vars)) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_func_var.Var (stack_var_init_decl val)))vars))
  | (func_var.InOutVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_func_var.InOutVar (stack_var_init_decl val)))vars)) 
  | (func_var.InVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_func_var.InVar (stack_var_init_decl val)))vars))
  | (func_var.OutVar vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). (name,stacked_func_var.OutVar (stack_var_init_decl val)))vars)))"
declare stack_func_var_def [simp]

text "Converting program vars list to stacked version"
definition stack_func_vars :: "func_var list \<Rightarrow> stacked_func_vars" where
"stack_func_vars pl = (fold (\<lambda>val fm. (fmadd fm (stack_func_var val))) pl fmempty)"
declare stack_func_vars_def [simp]

type_synonym stacked_func_block = "func_block_name * stacked_func_block_var list * stacked_process list"
(*TO DO*)
type_synonym stacked_func_blocks = "function_block_decl list"

type_synonym stacked_func = "func_name * basic_post_type * stacked_func_vars * stmt"
type_synonym stacked_funcs = "(func_name,stacked_func) fmap"

text "Transform function in stacked form"
definition stack_function :: "function_decl \<Rightarrow> stacked_func" where
"stack_function fd = 
  (let (f_name,val,vars,st_list) = fd
  in (f_name,val,(stack_func_vars vars),(st_list_to_stmt st_list)))"
declare stack_function_def [simp]

text "Stack list of function into map"
definition stack_functions :: "function_decl list \<Rightarrow> stacked_funcs" where
"stack_functions fd_list = fmap_of_list (map (\<lambda>fd. (fst fd, stack_function fd)) fd_list)"
declare stack_functions_def [simp]

datatype stacked_global_var =
  Var stacked_var_init
| Global direct_var  basic_post_type

type_synonym stacked_global_vars = "(symbolic_var,stacked_global_var) fmap"

text "Stack global var"
definition stack_global_var :: "global_var_decl \<Rightarrow> stacked_global_vars" where
"stack_global_var var = 
  (case var of
    (_,vars) \<Rightarrow> (fmap_of_list (map (\<lambda>(name,val). 
                  (name,(case val of 
                          all_var_init_decl.Var val \<Rightarrow> stacked_global_var.Var (stack_var_init_decl val)
                        | all_var_init_decl.GlobalVar (val1,val2) \<Rightarrow> stacked_global_var.Global val1 val2)))vars)))"
declare stack_global_var_def [simp]

text "Stack list of global vars"
definition stack_global_vars :: "global_var_decl list \<Rightarrow> stacked_global_vars" where
"stack_global_vars vars = (fold (\<lambda>var fm. fmadd fm (stack_global_var var)) vars fmempty)"
declare stack_global_vars_def [simp]

(*TO DO stacking configuration, function blocks *)
type_synonym stacked_model = "(configuration_decl option) * stacked_global_vars * (stacked_program list) * stacked_func_blocks * stacked_funcs"

text "Converting model declaration to stacked version"
definition stack_model :: "model \<Rightarrow> stacked_model" where
"stack_model m = 
  (case m of (conf, glob, prog_list, f_list, fb_list) \<Rightarrow>
  (conf,
  stack_global_vars glob, 
  (map 
    (\<lambda>prog. (stack_program prog))
    prog_list),
  fb_list,
  stack_functions f_list))"
declare stack_model_def [simp]

end