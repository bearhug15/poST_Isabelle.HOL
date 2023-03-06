theory poST_model
  imports poST_program poST_configuration poST_function_block poST_function
begin 

type_synonym model = "(configuration_decl option) * 
                      (global_var_decl list) * 
                      (program_decl list) * 
                      (function_decl list) *
                      (function_block_decl list)"

translations
  (type) "model" <= (type) "(configuration_decl option) * (global_var_decl list) * (program_decl list) * (function_block_decl list) * (function_decl list)"

end