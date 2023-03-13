theory poST_function_block
  imports poST_process
begin

datatype func_block_var = 
  ExtVar ext_var_decl |
  Var var_decl |
  InOutVar inout_var_decl |
  InVar in_var_decl |
  OutVar out_var_decl
type_synonym function_block_decl = "function_block_name * 
                                    (func_block_var list) * 
                                    (process_decl list)"

translations
  (type) "function_block_decl" <= (type) "function_block_name * (func_block_var list) * (process_decl list)"
end