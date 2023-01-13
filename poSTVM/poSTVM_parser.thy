theory poSTVM_parser
  imports
    "~~/poST/poST_model/poST_model" 
    "~~/poST/poST_utils/poST_vars_utils"

begin

subsection "Parsing model to it's version based an stacks"

datatype point_type = Break | Return | Exit
datatype process_mod = Restart | Stop | Error

text "Stack instructions"
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

text "Parses expressions to stack of instructions"
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

text "Parses nuturals to stack of values"
definition nat_to_values_stack :: "nat list \<Rightarrow> stack" where
"nat_to_values_stack nl = (map (\<lambda>val. (stack_op.Value (basic_post_type.Nat val))) nl) "

text "Parses values of basic type tp stack_of_values"
definition basics_to_values_stack :: "basic_post_type list \<Rightarrow> stack" where
"basics_to_values_stack bl = (map (\<lambda>val. (stack_op.Value val)) bl)"

(*parses statements to stack of instructions*)
text "Parses statements to stack of instructions"
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

text "Stacked version of variables"
datatype stacked_array_interval = Expr stack stack | Int int int
datatype stacked_var_init = 
  Symbolic basic_post_type "stack option" |
  Array stacked_array_interval "basic_post_type list" "(stack list)option" |
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
primrec stack_list_to_stack :: "stack list \<Rightarrow> stack" where
"stack_list_to_stack [] = []" |
"stack_list_to_stack (st#other) = (st @ (stack_list_to_stack other))"

text "Converting variable initialization to stacked version"
definition stack_var_init_decl :: "var_init_decl \<Rightarrow> stacked_var_init" where
"stack_var_init_decl decl =
  (case decl of 
    (var_init_decl.Simple (value,exp_option)) \<Rightarrow> 
      (stacked_var_init.Symbolic 
        value 
        (case exp_option of 
          None \<Rightarrow> None | (Some exp) \<Rightarrow> 
          (Some (stack_expr exp)))) |
    (var_init_decl.Array ((ar_inter,values),array_init_option)) \<Rightarrow> 
      (stacked_var_init.Array 
        (ainter_to_sainter ar_inter) 
        values 
        (case array_init_option of
          None \<Rightarrow> None |
          (Some ar_init) \<Rightarrow> (Some ((map (\<lambda>exp. (stack_expr exp))ar_init))))) |
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
datatype timeout = Const const stack | SymbolicVar symbolic_var stack
type_synonym stacked_state = "state_name * bool * stack * (timeout option)"

text "Converting state declaration to stacked version"
fun stack_state :: "state_decl \<Rightarrow> stacked_state" where
"stack_state (st_name, is_looped, statement_list.StList (st_list), None) = 
  (st_name, is_looped, (stack_statement_list st_list), None)" |
"stack_state (st_name, is_looped, statement_list.StList (st_list), (Some (timeout_statement.Const val (statement_list.StList sl)))) = 
  (st_name, is_looped, (stack_statement_list st_list), (Some (timeout.Const val (stack_statement_list sl))))" |
"stack_state (st_name, is_looped, statement_list.StList (st_list), (Some (timeout_statement.SymbolicVar val (statement_list.StList sl)))) = 
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

type_synonym stacked_function = "func_name * basic_post_type * func_var list * stack"

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
end