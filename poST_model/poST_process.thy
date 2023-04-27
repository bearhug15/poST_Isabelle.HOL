theory poST_process
  imports poST_state poST_vars
begin

datatype proc_var = Var var_decl |
                    ProcessVar process_var_decl |
                    InOutVar inout_var_decl |
                    InVar in_var_decl |
                    OutVar out_var_decl
type_synonym process_decl = 
              "process_name * 
               (proc_var list) * 
               (state_decl list)"

translations
  (type) "process_decl" <= (type) "process_name * (proc_var list) * (state_decl list)"

end