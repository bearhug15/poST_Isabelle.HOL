theory poST_process
  imports poST_state poST_vars
begin

type_synonym process_var_init_decl = "(process_var list) * process_name"
type_synonym process_var_decl = "process_var_init_decl list"

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
  (type) "process_var_init_decl" <= (type) "(process_var list) * process_name"
  (type) "process_var_decl" <= (type) "process_var_init_decl list"
  (type) "process_decl" <= (type) "process_name * (proc_var list) * (state_decl list)"

end