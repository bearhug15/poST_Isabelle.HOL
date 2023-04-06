theory poST_expr
  imports basic_post_types
begin
datatype proc_status = 
Active |
Inactive |
Stop |
Error 

datatype unary_op = Not | Minus
datatype binary_op =
And | Eq | NotEq | Less | More | LessEq | MoreEq | 
Sum | Sub | Mul | Div | Mod | Or | Xor | Pow

datatype assign_type = ColonEq | Conseq

datatype expr = 
Unary unary_op expr |
Binary binary_op expr expr |
Const const | 
SymbolicVar symbolic_var | 
ArrayVar symbolic_var expr |
ProcStatEpxr process_name proc_status | 
FunctionCall func_name "param_assign list"	
  and param_assign =SymbolicVar symbolic_var assign_type expr 

type_synonym func_params = "param_assign list"

end