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

datatype expr = Unary "unary_op option"  expr |
                Binary binary_op expr expr |
                Const const | 
                SymbolicVar symbolic_var | 
                ArrayVar symbolic_var expr |
                ProcStatEpxr process_name proc_status | 
                FunctionCall func_name "param_assign list"	
  and param_assign =SymbolicVar  symbolic_var assign_type expr 

end