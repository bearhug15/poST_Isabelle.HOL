theory poST_program
  imports poST_process
begin

datatype prog_var = ExtVar ext_var_decl |
                    Var var_decl |
                    InOutVar inout_var_decl |
                    InVar in_var_decl |
                    OutVar out_var_decl
type_synonym program_decl = "program_name * 
                            (prog_var list) * 
                            (process_decl list)"

translations
  (type) "program_decl" <= (type) "program_name * (prog_var list) * (process_decl list)"

end