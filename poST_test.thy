theory poST_test
  imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin

value "fmempty :: (nat,nat) fmap"
definition test_process_state1 :: "process_state" where
"test_process_state1 = 
  ([stacked_proc_var.Var (fmupd 
                            ''var1'' 
                            (stacked_var_init.Symbolic (basic_post_type.Nat 0) None) 
                          fmempty)],
  ''state1'',
  ''state1'',
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_state1 :: "program_state" where
"test_program_state1 = 
  ([],
  (fmupd
    ''process1''
    test_process_state1
    fmempty),
  ''process1'')"
definition test_ms1 :: "model_state" where
"test_ms1 = model_state.ST
  []
  ((fmupd
    ''program1''
    test_program_state1
    fmempty),''program1'')
  []
  []"

definition test_process_state2 :: "process_state" where
"test_process_state2 = 
  ([stacked_proc_var.Var (fmupd 
                            ''var1'' 
                            (stacked_var_init.Symbolic (basic_post_type.Nat 1) None) 
                          fmempty)],
  ''state1'',
  ''state1'',
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_state2 :: "program_state" where
"test_program_state2 = 
  ([],
  (fmupd
    ''process1''
    test_process_state2
    fmempty),
  ''process1'')"
definition test_ms2 :: "model_state" where
"test_ms2 = model_state.ST
  []
  ((fmupd
    ''program1''
    test_program_state2
    fmempty),''program1'')
  []
  []"

definition test_statement1 :: "stmt" where
"test_statement1 = stmt.AssignSt (common_var.Symbolic ''var1'',expr.Const (const.Nat 1))"

lemma "(statement_result.Continue,test_ms1)\<turnstile>test_statement1\<longrightarrow>(statement_result.Continue,test_ms2)"
  apply (simp add: test_statement1_def 
                test_ms1_def 
                test_ms2_def 
                test_process_state1_def
                test_process_state2_def
                test_program_state1_def
                test_program_state2_def)
  apply (rule AssignS)
   apply (rule Const)
   apply (auto)
  apply (auto simp add: const_to_basic_def
set_symbvar_def
get_cur_var_by_name_def
set_symbvar_in_ps_in_cur_prog_def
set_symbvar_in_ps_in_cur_proc_def
get_var_by_name.simps
get_cur_var_list_def
get_cur_proc_var_list_def
find_var_by_name_def
get_cur_var_by_name_def
get_var_by_name.simps
get_cur_proc_state_by_prog_def
get_cur_prog_state_def
set_symbvar_in_ps_def
fstOp_def
sndOp_def)
  done

definition test_process_state3 :: "process_state" where
"test_process_state3 = 
  ([stacked_proc_var.Var (fmupd 
                            ''var1'' 
                            (stacked_var_init.Symbolic (basic_post_type.Nat 2) None) 
                          fmempty)],
  ''state1'',
  ''state1'',
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_state3 :: "program_state" where
"test_program_state3 = 
  ([],
  (fmupd
    ''process1''
    test_process_state3
    fmempty),
  ''process1'')"
definition test_ms3 :: "model_state" where
"test_ms3 = model_state.ST
  []
  ((fmupd
    ''program1''
    test_program_state3
    fmempty),''program1'')
  []
  []"

definition test_statement2 :: "stmt" where
"test_statement2 = stmt.AssignSt (common_var.Symbolic ''var1'',
  expr.Binary (binary_op.Sum) (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 2)))"

lemma "(statement_result.Continue,test_ms1)\<turnstile>test_statement2\<longrightarrow>(statement_result.Continue,test_ms3)"
  apply (simp add: test_statement2_def 
                test_ms1_def 
                test_ms3_def 
                test_process_state1_def
                test_process_state3_def
                test_program_state1_def
                test_program_state3_def)
  apply (rule AssignS)
   apply (rule BinOp)
     apply (rule Var)
   apply (auto)
  apply (auto simp add: const_to_basic_def
set_symbvar_def
get_cur_var_by_name_def
set_symbvar_in_ps_in_cur_prog_def
set_symbvar_in_ps_in_cur_proc_def
get_var_by_name.simps
get_cur_var_list_def
get_cur_proc_var_list_def
find_var_by_name_def
get_cur_var_by_name_def
get_var_by_name.simps
get_cur_proc_state_by_prog_def
get_cur_prog_state_def
set_symbvar_in_ps_def
fstOp_def
sndOp_def)
   apply (rule Const)
apply (auto simp add: const_to_basic_def
set_symbvar_def
get_cur_var_by_name_def
set_symbvar_in_ps_in_cur_prog_def
set_symbvar_in_ps_in_cur_proc_def
get_var_by_name.simps
get_cur_var_list_def
get_cur_proc_var_list_def
find_var_by_name_def
get_cur_var_by_name_def
get_var_by_name.simps
get_cur_proc_state_by_prog_def
get_cur_prog_state_def
set_symbvar_in_ps_def
get_symbvar_by_name_def
binary_op_exec_def
basic_post_type_sum_def
fstOp_def
sndOp_def
Num.numeral_2_eq_2
)
done
(* Don't work now
definition test_process_state4 :: "process_state" where
"test_process_state4 = 
  ([stacked_proc_var.Var (fmupd 
                            ''var2'' 
                            (stacked_var_init.Symbolic (basic_post_type.Nat 0) None)
                          (fmupd 
                            ''var1'' 
                            (stacked_var_init.Symbolic (basic_post_type.Nat 0) None) 
                          fmempty))],
  ''state1'',
  ''state1'',
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_state4 :: "program_state" where
"test_program_state4 = 
  ([],
  (fmupd
    ''process1''
    test_process_state4
    fmempty),
  ''process1'')"
definition test_ms4 :: "model_state" where
"test_ms4 = model_state.ST
  []
  ((fmupd
    ''program1''
    test_program_state4
    fmempty),''program1'')
  []
  []"

definition test_process_state5 :: "process_state" where
"test_process_state5 = 
  ([stacked_proc_var.Var (fmupd 
                            ''var2'' 
                            (stacked_var_init.Symbolic (basic_post_type.Nat 2) None)
                          (fmupd 
                            ''var1'' 
                            (stacked_var_init.Symbolic (basic_post_type.Nat 1) None) 
                          fmempty))],
  ''state1'',
  ''state1'',
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_state5 :: "program_state" where
"test_program_state5 = 
  ([],
  (fmupd
    ''process1''
    test_process_state5
    fmempty),
  ''process1'')"
definition test_ms5 :: "model_state" where
"test_ms5 = model_state.ST
  []
  ((fmupd
    ''program1''
    test_program_state5
    fmempty),''program1'')
  []
  []"

definition test_statement3 :: "stmt" where
"test_statement3 = stmt.Comb
  (stmt.AssignSt (common_var.Symbolic ''var1'',
    expr.Binary (binary_op.Sum) (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 1))))
  (stmt.AssignSt (common_var.Symbolic ''var2'',
    expr.Binary (binary_op.Sum) (expr.SymbolicVar ''var2'') (expr.Const (const.Nat 2))))"

lemma "(statement_result.Continue,test_ms4)\<turnstile>test_statement3\<longrightarrow>(statement_result.Continue,test_ms5)"
  apply (simp add: test_statement3_def 
                test_ms4_def 
                test_ms5_def 
                test_process_state4_def
                test_process_state5_def
                test_program_state4_def
                test_program_state5_def)
apply (rule Comb)
  apply (rule AssignS)
   apply (rule BinOp)
     apply (rule Var)
   apply (auto)
  apply (auto simp add: const_to_basic_def
set_symbvar_def
get_cur_var_by_name_def
set_symbvar_in_ps_in_cur_prog_def
set_symbvar_in_ps_in_cur_proc_def
get_var_by_name.simps
get_cur_var_list_def
get_cur_proc_var_list_def
find_var_by_name_def
get_cur_var_by_name_def
get_var_by_name.simps
get_cur_proc_state_by_prog_def
get_cur_prog_state_def
set_symbvar_in_ps_def
fstOp_def
sndOp_def)
   apply (rule Const)
apply (auto simp add: const_to_basic_def
set_symbvar_def
get_cur_var_by_name_def
set_symbvar_in_ps_in_cur_prog_def
set_symbvar_in_ps_in_cur_proc_def
get_var_by_name.simps
get_cur_var_list_def
get_cur_proc_var_list_def
find_var_by_name_def
get_cur_var_by_name_def
get_var_by_name.simps
get_cur_proc_state_by_prog_def
get_cur_prog_state_def
set_symbvar_in_ps_def
get_symbvar_by_name_def
binary_op_exec_def
basic_post_type_sum_def
fstOp_def
sndOp_def
Nat.One_nat_def
)
  apply (rule AssignS)
   apply (rule BinOp)
     apply (rule Var)
   apply (auto)
  apply (auto simp add: const_to_basic_def
set_symbvar_def
get_cur_var_by_name_def
set_symbvar_in_ps_in_cur_prog_def
set_symbvar_in_ps_in_cur_proc_def
get_var_by_name.simps
get_cur_var_list_def
get_cur_proc_var_list_def
find_var_by_name_def
get_cur_var_by_name_def
get_var_by_name.simps
get_cur_proc_state_by_prog_def
get_cur_prog_state_def
set_symbvar_in_ps_def
fstOp_def
sndOp_def)
   apply (rule Const)
apply (auto simp add: const_to_basic_def
set_symbvar_def
get_cur_var_by_name_def
set_symbvar_in_ps_in_cur_prog_def
set_symbvar_in_ps_in_cur_proc_def
get_var_by_name.simps
get_cur_var_list_def
get_cur_proc_var_list_def
find_var_by_name_def
get_cur_var_by_name_def
get_var_by_name.simps
get_cur_proc_state_by_prog_def
get_cur_prog_state_def
set_symbvar_in_ps_def
get_symbvar_by_name_def
binary_op_exec_def
basic_post_type_sum_def
fstOp_def
sndOp_def
Num.numeral_2_eq_2
)
done*)

find_theorems "(Suc 0)"
(*
fmupd ''program1''
     ([],
      fmupd ''process1''
       ([stacked_proc_var.Var
          (fmupd ''var1'' (stacked_var_init.Symbolic (basic_post_type.Nat 2) None) fmempty)],
        ''state1'', ''state1'', Active, time.Time 0 0 0 0 0)
       fmempty,
      ''process1'')
     fmempty =
    fmupd ''program1''
     ([],
      fmupd ''process1''
       ([stacked_proc_var.Var
          (fmupd ''var1'' (stacked_var_init.Symbolic (basic_post_type.Nat (Suc (Suc 0))) None) fmempty)],
        ''state1'', ''state1'', Active, time.Time 0 0 0 0 0)
       fmempty,
      ''process1'')
     fmempty
*)
(*
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
*)



end