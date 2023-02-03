theory poSTVM_parser_alt
  imports
    "~~/poST/poST_model/poST_model" 
    "~~/poST/poST_utils/poST_vars_utils"

begin

datatype point_type = Break | Return | Exit
datatype process_mod = Restart | Stop | Error

datatype expr_op =
  Unary "unary_op option" | 
  Binary binary_op | 
  Value basic_post_type | 
  Get symbolic_var |
  GetArray symbolic_var |
  CheckProcStat process_name proc_status |
  FunctionCall func_name "param_assign list"

type_synonym expr_stack = "expr_op list"

fun stack_expr :: "expr \<Rightarrow> expr_stack" where
  "stack_expr (expr.Unary unary_option exp) = (expr_op.Unary unary_option)# (stack_expr exp)"
| "stack_expr (expr.Binary bin_op exp1 exp2) = ((expr_op.Binary bin_op) # (stack_expr exp1)) @ (stack_expr exp2)"
| "stack_expr (expr.Const c) = [expr_op.Value (const_to_basic c)]" 
| "stack_expr (expr.SymbolicVar var_name) = [expr_op.Get var_name ]" 
| "stack_expr (expr.ArrayVar var_name exp) = (expr_op.GetArray var_name) #(stack_expr exp)" 
| "stack_expr (expr.ProcStatEpxr proc_name proc_stat) = [expr_op.CheckProcStat proc_name proc_stat]" 
| "stack_expr (expr.FunctionCall f_name param_assign_list) = [expr_op.FunctionCall f_name param_assign_list]"

datatype statement_op = 
  Assign symbolic_var expr_stack |
  AssignArray symbolic_var expr_stack |
  FunctionBlockCall func_block_name "param_assign list" |
  SetPoint point_type |
  GoPoint point_type |
  SetState "state_name option" |
  ProcessStatement "process_name option" process_mod |
  StatementList "statement_op list" |
  IfStatement expr_stack |
  CaseHeadStatement expr_stack |
  CaseStatement "nat list" |
  WhileStatement expr_stack |
  ResetTimer

type_synonym statement_stack = "statement_op list"

text "Parses nuturals to stack of values"
definition nat_to_values_stack :: "nat list \<Rightarrow> expr_stack" where
"nat_to_values_stack nl = (map (\<lambda>val. (expr_op.Value (basic_post_type.Nat val))) nl) "

text "Parses values of basic type tp stack_of_values"
definition basics_to_values_stack :: "basic_post_type list \<Rightarrow> expr_stack" where
"basics_to_values_stack bl = (map (\<lambda>val. (expr_op.Value val)) bl)"

fun stack_statement :: "statement \<Rightarrow> statement_stack" and
    stack_statement_list:: "statement list \<Rightarrow>statement_stack" and
    stack_if_statements :: "(expr * statement_list) list \<Rightarrow> statement_stack" and
    stack_case_statements :: "(case_list * (statement list)) list \<Rightarrow> statement_stack"  where
  "stack_statement (statement.AssignSt (var, exp)) = 
    (case var of 
      (common_var.Symbolic var_name) \<Rightarrow> [(statement_op.Assign var_name (stack_expr exp))] 
    | (common_var.Array  var_name exp2) \<Rightarrow>[(statement_op.AssignArray var_name ((stack_expr exp2)@ (stack_expr exp)))])" 
| "stack_statement (statement.Return) = [statement_op.GoPoint point_type.Return]" 
| "stack_statement (statement.Exit) = [statement_op.GoPoint point_type.Exit]" 
| "stack_statement (statement.ProcessSt proc_statement) = 
  (case proc_statement of
    process_statement.Start(process_name_option) \<Rightarrow> 
      [statement_op.ProcessStatement process_name_option process_mod.Restart] |
    process_statement.Stop(process_name_option) \<Rightarrow>
      [statement_op.ProcessStatement process_name_option process_mod.Stop] |
    process_statement.Error(process_name_option) \<Rightarrow> 
      [statement_op.ProcessStatement process_name_option process_mod.Error])" 
| "stack_statement (statement.SetStateSt state_name_option) = [statement_op.SetState state_name_option]" 
| "stack_statement (statement.SelectSt (select_statement.IfSt  if_then_list else_option )) = 
  (let if_stack = (stack_if_statements if_then_list) in  
        (case else_option of None \<Rightarrow> if_stack |
          Some(st_list) \<Rightarrow> if_stack @ (stack_statement_list st_list))
          @[statement_op.SetPoint point_type.Break])" 
| "stack_statement_list [] = []" 
| "stack_statement_list (st#other) = (stack_statement st) @ (stack_statement_list other)" 
| "stack_if_statements [] = []" 
| "stack_if_statements (ifs#other) = 
    (let (exp,st_list) = ifs 
      in (case st_list of (st_list) \<Rightarrow>  
            ([statement_op.IfStatement (stack_expr exp)]) 
            @ [statement_op.StatementList ((stack_statement_list st_list)@ [(statement_op.GoPoint point_type.Break)])]))  
      @ (stack_if_statements other)" 
| "stack_statement (statement.SelectSt (select_statement.CaseSt  exp case_then_list else_option)) =
    (statement_op.CaseHeadStatement (stack_expr exp))
    #(case else_option of
        None \<Rightarrow> (stack_case_statements case_then_list)
      | Some(st_list) \<Rightarrow> (stack_case_statements case_then_list) @ [statement_op.StatementList (stack_statement_list st_list)])
    @ [statement_op.SetPoint point_type.Break]"
| "stack_case_statements [] = []"
| "stack_case_statements (cas#other) =
    (case cas of
      (nat_list, st_list) \<Rightarrow>
        (statement_op.CaseStatement nat_list)
      # [statement_op.StatementList ((stack_statement_list st_list) @ [(statement_op.GoPoint point_type.Break)])]
      @ (stack_case_statements other))"
| "stack_statement (statement.IterSt (iter_statement.ForSt  var_name (exp1,exp2,exp_option) st_list)) = 
  [statement_op.Assign var_name (stack_expr exp1)] 
  @ [statement_op.WhileStatement
      (stack_expr (expr.Binary 
                    binary_op.LessEq 
                    (expr.Unary None (expr.SymbolicVar var_name) )
                    exp2))]
  @ [statement_op.StatementList 
      ((stack_statement_list (st_list ))
      @ [statement_op.Assign 
          var_name
          (case exp_option of
            None \<Rightarrow> [expr_op.Binary binary_op.Sum ,expr_op.Get var_name, expr_op.Value (basic_post_type.Nat 1)] 
          | Some(exp) \<Rightarrow>[expr_op.Binary binary_op.Sum ,expr_op.Get var_name] @ (stack_expr exp))])] " 
| "stack_statement (statement.IterSt (iter_statement.WhileSt  exp st_list)) = 
   [statement_op.WhileStatement (stack_expr exp)]
   @ [statement_op.StatementList (stack_statement_list st_list)]
   @ [statement_op.SetPoint point_type.Break]" 
| "stack_statement (statement.IterSt (iter_statement.RepeatSt  st_list exp)) =  
    (let st_list = [statement_op.StatementList (stack_statement_list st_list)] 
    in (st_list
    @[statement_op.WhileStatement (stack_expr exp)]
    @ st_list
    @[statement_op.SetPoint point_type.Break])) " 
| "stack_statement (statement.ResetSt) = [statement_op.ResetTimer]" 
| "stack_statement (FBInvocation (fb_name, param_assign_list)) =[statement_op.FunctionBlockCall fb_name param_assign_list]"


text "Stacked version of variables"
datatype stacked_array_interval = Expr expr_stack expr_stack | Int int int
datatype stacked_var_init = 
  Symbolic basic_post_type "expr option" |
  Array stacked_array_interval "basic_post_type list" "(expr list) option" |
  FunctionBlock func_block_name
type_synonym stacked_vars = "((symbolic_var, stacked_var_init) fmap)"

(*TO DO stack process var*)
text "Stacked version of process variables"
datatype stacked_proc_var = 
  Var stacked_vars |
  ProcessVar process_var_decl |
  InOutVar stacked_vars |
  InVar stacked_vars |
  OutVar stacked_vars


text "Converting array interval to it's stacked version "
definition ainter_to_sainter :: "array_interval \<Rightarrow> stacked_array_interval" where
"ainter_to_sainter ar_inter =
  (case ar_inter of
    (array_interval.Int val1 val2) \<Rightarrow> (stacked_array_interval.Int val1 val2) |
    (array_interval.Expr exp1 exp2) \<Rightarrow> (stacked_array_interval.Expr (stack_expr exp1) (stack_expr exp2)))"


text "Flattening list of stacks"
primrec stack_list_to_stack :: "statement_stack list \<Rightarrow> statement_stack" where
"stack_list_to_stack [] = []" |
"stack_list_to_stack (st#other) = (st @ (stack_list_to_stack other))"

text "Converting variable initialization to stacked version"
definition stack_var_init_decl :: "var_init_decl \<Rightarrow> stacked_var_init" where
"stack_var_init_decl decl =
  (case decl of 
    (var_init_decl.Simple (value,exp_option)) \<Rightarrow> 
      (stacked_var_init.Symbolic 
        value 
        exp_option) |
    (var_init_decl.Array ((ar_inter,values),array_init_option)) \<Rightarrow> 
      (stacked_var_init.Array 
        (ainter_to_sainter ar_inter) 
        values 
        array_init_option) |
    (var_init_decl.FunctionBlock fb_name) \<Rightarrow> (stacked_var_init.FunctionBlock fb_name))"

text "Converting map of variables to stacked version"
definition stack_var_decl :: "((symbolic_var, var_init_decl) fmap) \<Rightarrow> ((symbolic_var, stacked_var_init) fmap)" where
"stack_var_decl var_map = 
  (fmmap_keys
    (\<lambda>name vid. (stack_var_init_decl vid) ) 
    var_map)"

text "Converting process var to stacked version"
definition stack_proc_var :: "proc_var \<Rightarrow> stacked_proc_var" where
"stack_proc_var var = 
  (case var of
    (proc_var.Var (is_const, var)) \<Rightarrow> (stacked_proc_var.Var (stack_var_decl var))|
    (proc_var.ProcessVar var) \<Rightarrow> (stacked_proc_var.ProcessVar var)|
    (proc_var.InOutVar var) \<Rightarrow> (stacked_proc_var.InOutVar (stack_var_decl var)) |
    (proc_var.InVar var) \<Rightarrow> (stacked_proc_var.InVar (stack_var_decl var))|
    (proc_var.OutVar var) \<Rightarrow> (stacked_proc_var.OutVar (stack_var_decl var)))"

text "Converting process vars list to stacked version"
definition stack_proc_vars :: "proc_var list \<Rightarrow> stacked_proc_var list" where
"stack_proc_vars pl = (map (\<lambda>val. (stack_proc_var val)) pl)"

text "Stacked version of program variables"
datatype stacked_prog_var =
  ExtVar stacked_vars |
  Var stacked_vars |
  InOutVar stacked_vars |
  InVar stacked_vars |
  OutVar stacked_vars

text "Converting external vars map to stacked version"
definition stack_ext_var_decl :: "((symbolic_var, basic_post_type) fmap) \<Rightarrow> ((symbolic_var, stacked_var_init) fmap)" where
"stack_ext_var_decl var_map =
  (fmmap_keys 
    (\<lambda>name val. (stacked_var_init.Symbolic val None))
    var_map)"

text "Converting program vars to stacked version"
definition stack_prog_var :: "program_var \<Rightarrow> stacked_prog_var" where
"stack_prog_var var = 
  (case var of
    (program_var.Var (is_const, var)) \<Rightarrow> (stacked_prog_var.Var (stack_var_decl var))|
    (program_var.ExtVar (is_const, var)) \<Rightarrow> (stacked_prog_var.ExtVar (stack_ext_var_decl var))|
    (program_var.InOutVar var) \<Rightarrow> (stacked_prog_var.InOutVar (stack_var_decl var)) |
    (program_var.InVar var) \<Rightarrow> (stacked_prog_var.InVar (stack_var_decl var))|
    (program_var.OutVar var) \<Rightarrow> (stacked_prog_var.OutVar (stack_var_decl var)))"

text "Converting program vars list to stacked version"
definition stack_prog_vars :: "program_var list \<Rightarrow> stacked_prog_var list" where
"stack_prog_vars pl = (map (\<lambda>val. (stack_prog_var val)) pl)"

text "Stacked version of state declaration"
datatype timeout = Const const statement_stack | SymbolicVar symbolic_var statement_stack
type_synonym stacked_state = "state_name * bool * statement_stack * (timeout option)"

text "Converting state declaration to stacked version"
fun stack_state :: "state_decl \<Rightarrow> stacked_state" where
"stack_state (st_name, is_looped, st_list, None) = 
  (st_name, is_looped, (stack_statement_list st_list), None)" |
"stack_state (st_name, is_looped, st_list, (Some (timeout_statement.Const val sl))) = 
  (st_name, is_looped, (stack_statement_list st_list), (Some (timeout.Const val (stack_statement_list sl))))" |
"stack_state (st_name, is_looped, st_list, (Some (timeout_statement.SymbolicVar val sl))) = 
  (st_name, is_looped, (stack_statement_list st_list), (Some (timeout.SymbolicVar val (stack_statement_list sl))))" 

text "Stacked version of process declaration"
type_synonym stacked_process = "process_name * stacked_proc_var list * stacked_state list"

text "Converting process declaration to stacked version"
fun stack_process :: "process_decl \<Rightarrow> stacked_process" where
"stack_process (p_name, p_var_list, st_decl_list ) =  
    (p_name, 
    (stack_proc_vars p_var_list), 
    (map
      (\<lambda>st_decl. stack_state st_decl)
      st_decl_list))"

text "Stacked version of program declaration"
type_synonym stacked_program = "program_name * stacked_prog_var list * stacked_process list"

text "Converting program declaration to stacked version"
fun stack_program :: "program_decl \<Rightarrow> stacked_program" where
"stack_program (p_name, p_var_list, p_decl_list) =
  (p_name,
   (stack_prog_vars p_var_list),
   (map
      (\<lambda>p_decl. stack_process p_decl)
      p_decl_list))"

(*TO DO function block and function stacking*)
datatype stacked_func_block_var =  
  ExtVar stacked_vars |
  Var stacked_vars |
  InOutVar stacked_vars |
  InVar stacked_vars |
  OutVar stacked_vars
datatype func_var =
  Var stacked_vars |
  InOutVar stacked_vars |
  InVar stacked_vars |
  OutVar stacked_vars

type_synonym stacked_function_block = "func_block_name * stacked_func_block_var list * stacked_process list"

type_synonym stacked_function = "func_name * basic_post_type * func_var list * statement_stack"

(*TO DO stacking configuration, function blocks and functions*)
type_synonym stacked_model = "(configuration_decl option) * (global_var_decl list) * (stacked_program list) * (function_block_decl list) * (function_decl list)"

text "Converting model declaration to stacked version"
fun stack_model :: "model \<Rightarrow> stacked_model" where
"stack_model (conf, glob, prog_list, fb_list, f_list) = 
  (conf,
  glob, 
  (map 
    (\<lambda>prog. (stack_program prog))
    prog_list),
  fb_list,
  f_list)"


end