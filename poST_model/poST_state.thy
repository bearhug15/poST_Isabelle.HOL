theory poST_state
  imports poST_statement
begin
datatype timeout_statement = 
          Const const statement_list |
          SymbolicVar symbolic_var statement_list 
type_synonym state_decl = 
              "state_name * is_looped * 
               statement_list * (timeout_statement option)"

translations
  (type) "state_decl" <= (type) "state_name * is_looped * statement_list * (timeout_statement option)"

end