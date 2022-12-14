theory poST_test
  imports "~~/poST/poST_model/poST_model"
begin

datatype prog_name' = HandDryer'
datatype symbolic_var' = hands' | control' 
datatype process_name' = HandDryer''
datatype state_name' = Wait' | Work'

axiomatization prog_name' :: "prog_name' \<Rightarrow> program_name"
  where
    inj_prog_name': "(prog_name' x = prog_name' y) = (x = y)" and
    surj_prog_name': "\<exists> m. n = prog_name' m"
axiomatization symbolic_var' :: "symbolic_var' \<Rightarrow> symbolic_var"
  where
    inj_symbolic_var': "(symbolic_var' x = symbolic_var' y) = (x = y)" and
    surj_symbolic_var': "\<exists> m. n = symbolic_var' m"
axiomatization process_name' :: "process_name' \<Rightarrow> process_name"
  where
    inj_process_name': "(process_name' x = process_name' y) = (x = y)" and
    surj_process_name': "\<exists> m. n = process_name' m"
axiomatization state_name' :: "state_name' \<Rightarrow> state_name"
  where
    inj_state_name': "(state_name' x = state_name' y) = (x = y)" and
    surj_state_name': "\<exists> m. n = state_name' m"
declare inj_prog_name' [simp] inj_symbolic_var' [simp] inj_process_name' [simp] inj_state_name' [simp]

abbreviation HandDryerProgram :: program_name
  where "HandDryerProgram == prog_name' HandDryer'"
abbreviation hands :: symbolic_var
  where "hands == symbolic_var' hands'"
abbreviation control :: symbolic_var
  where "control == symbolic_var' control'"
abbreviation HandDryerProcess :: process_name
  where "HandDryerProcess == process_name' HandDryer''"
abbreviation Wait :: state_name
  where "Wait == state_name' Wait'"
abbreviation Work :: state_name
  where "Work == state_name' Work'"


(*state_decl = "state_name * is_looped * statement_list * (timeout_statement option)"*)


definition Wait_HandDryer :: state_decl
  where "Wait_HandDryer == (Wait,False,StList 
[(statement.SelectSt 
  (select_statement.IfSt
      [(expr.Unary 
        (unary_expr.UnaryExpr 
          None 
          (prim_expr.SymbolicVar hands)), 
        StList 
          [statement.AssignSt 
            ((common_var.SymbolicVar control), 
             (expr.Unary 
               (unary_expr.UnaryExpr 
                 None 
                (prim_expr.Const (const.Bool True)))))])] 
      None)),
  (statement.SetStateSt None)
],
None)"

definition Work_HandDryer :: state_decl
  where "Work_HandDryer == (Work,False,StList
[(statement.SelectSt 
  (select_statement.IfSt
      [(expr.Unary 
        (unary_expr.UnaryExpr 
          None 
          (prim_expr.SymbolicVar hands)), 
        StList 
          [statement.ResetSt])]
      None))],
Some (timeout_statement.Const 
  (const.Time (time.Time 0 0 0 2 0)) 
  (StList [
    statement.AssignSt 
      ((common_var.SymbolicVar control), 
       (expr.Unary 
         (unary_expr.UnaryExpr 
           None 
          (prim_expr.Const (const.Bool False)))))])))"




end