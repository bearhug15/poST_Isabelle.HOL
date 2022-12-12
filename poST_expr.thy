theory poST_expr
  imports basic_post_types
begin
datatype proc_status = 
Active |
Inactive |
Stop |
Error
datatype unary_op = Not | Minus
datatype binary_op = And | 
                     Eq | 
                     NotEq | 
                     Less | 
                     More | 
                     LessEq | 
                     MoreEq | 
                     Sum | 
                     Sub | 
                     Mul | 
                     Div | 
                     Mod |
                     Or |
                     Xor
datatype assign_type = ColonEq | Conseq
type_synonym reset_timer_statement = bool

type_synonym proc_status_expr = "process_name * proc_status"

datatype expr = Unary unary_expr |
                Binary binary_op expr expr
  and unary_expr = UnaryExpr "unary_op option"  prim_expr
  and prim_expr = Const const | 
                  SymbolicVar symbolic_var | 
                  ArrayVar array_var |
                  Expression expr | 
                  ProcStatEpxr proc_status_expr | 
                  FunctionCall function_call	
  and array_var = ArrayVar symbolic_var expr
  and function_call =FuncCall func_name "param_assign list"
  and param_assign =SymbolicVar  symbolic_var assign_type expr 

translations
  (type) "proc_status_expr" <= (type) "process_name * proc_status"

definition proc_status_is :: "proc_status \<Rightarrow> proc_status \<Rightarrow> bool" where
"proc_status_is s1 s2 = 
(case (s1,s2) of 
  (proc_status.Active,proc_status.Active) \<Rightarrow> True |
  (proc_status.Inactive,proc_status.Inactive) \<Rightarrow> True |
  (proc_status.Stop,proc_status.Stop) \<Rightarrow> True |
  (proc_status.Error,proc_status.Error) \<Rightarrow> True |
  (proc_status.Stop,proc_status.Inactive) \<Rightarrow> True |
  (proc_status.Error,proc_status.Inactive) \<Rightarrow> True |
  (_,_) \<Rightarrow> False)"

end