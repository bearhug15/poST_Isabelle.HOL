theory poST_expr
  imports basic_post_types
begin
datatype proc_status = 
Active |
Inactive |
Stop |
Error |
Timeout time

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

end