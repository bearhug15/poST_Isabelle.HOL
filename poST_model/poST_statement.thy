theory poST_statement
 imports poST_expr
begin 

datatype common_var = Symbolic symbolic_var | Array symbolic_var expr
type_synonym assign_statement = "common_var * expr"
type_synonym start_process_contextment = "process_name option"
type_synonym stop_process_contextment =  "process_name option"
type_synonym error_process_contextment = "process_name option"
datatype process_contextment = Start start_process_contextment |
                             Stop stop_process_contextment |
                             Error error_process_contextment
type_synonym set_state_statement = "state_name option"

type_synonym for_list = "expr * expr * (expr option)"
type_synonym case_list = "nat list"
    datatype statement = AssignSt common_var expr |
                         FBInvocation func_block_name  "(param_assign list)" |
                         Return |
                         Exit |
                         ProcessSt process_contextment |
                         SetStateSt set_state_statement |
                         ResetSt |
                         SelectSt select_statement |
                         IterSt iter_statement
        and  select_statement = 
                IfSt "(expr * (statement list)) list" 
                     "(statement list) option" | 
                CaseSt expr "(case_list * (statement list)) list" 
                            "(statement list) option"
        and  iter_statement = 
                ForSt symbolic_var for_list "statement list" | 
                WhileSt expr "statement list" | 
                RepeatSt "statement list" expr

type_synonym statement_list = "statement list"
(*
primrec add_statement :: "statement_list \<Rightarrow> statement \<Rightarrow> statement_list"where
"add_statement (statement_list.StList st_list) st =(statement_list.StList (st_list @ [st]))" 
*)
translations
  (type) "for_list" <= (type) "expr * expr * (expr option)"

end