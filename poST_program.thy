theory poST_program
  imports poSt_process
begin
datatype program_var = ExtVar ext_var_decl |
                    Var var_decl |
                    InOutVar inout_var_decl |
                    InVar in_var_decl |
                    OutVar out_var_decl
type_synonym program_decl = "program_name * (program_var list) * (process_decl list)"

type_synonym working_program = "program_decl * time"
translations
  (type) "program_decl" <= (type) "program_name * (program_var list) * (process_decl list)"

end