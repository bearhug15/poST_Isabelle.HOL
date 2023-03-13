theory poST_function
  imports poST_statement poST_vars
begin
datatype func_var = 
  Var var_decl |
  InVar in_var_decl |
  OutVar out_var_decl |
  InOutVar inout_var_decl
type_synonym function_decl = "func_name * 
                              basic_post_type *
                              (func_var list)* 
                              statement_list"

translations
  (type) "function_decl" <= (type) "func_name * basic_post_type * (func_var list)* statement_list"

end