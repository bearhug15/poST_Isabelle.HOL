theory poST_tests
  imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin

value "fmempty :: (nat,nat) fmap"
definition test_process_context1 :: "process_context" where
"test_process_context1 = 
  (fmap_of_list [(''var1'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 0) None))],
  ''state1'',
  ''state1'',
  [''state1''],
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_context1 :: "program_context" where
"test_program_context1 = 
  (fmempty,
  (fmupd
    ''process1''
    test_process_context1
    fmempty),
  ''process1'')"
definition test_ms1 :: "model_context" where
"test_ms1 = model_context.ST
  fmempty
  (fmupd
    ''program1''
    test_program_context1
    fmempty)
  ''program1''
  []
  fmempty"

definition test_process_context2 :: "process_context" where
"test_process_context2 = 
  (fmap_of_list [(''var1'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 1) None))],
  ''state1'',
  ''state1'',
  [''state1''],
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_context2 :: "program_context" where
"test_program_context2 = 
  (fmempty,
  (fmupd
    ''process1''
    test_process_context2
    fmempty),
  ''process1'')"
definition test_ms2 :: "model_context" where
"test_ms2 = model_context.ST
  fmempty
  (fmupd
    ''program1''
    test_program_context2
    fmempty)
  ''program1''
  []
  fmempty"



definition test_statement1 :: "stmt" where
"test_statement1 = stmt.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Nat 1))"

lemma "(statement_result.Continue,test_ms1)\<turnstile>test_statement1\<longrightarrow>(statement_result.Continue,test_ms2)"
  apply (auto simp add: test_statement1_def 
                test_ms1_def 
                test_ms2_def 
                test_process_context1_def
                test_process_context2_def
                test_program_context1_def
                test_program_context2_def)
  apply (rule AssignS)
   apply (rule Const)
  apply auto
  done

definition test_process_context3 :: "process_context" where
"test_process_context3 = 
  (fmap_of_list [(''var1'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 2) None))],
  ''state1'',
  ''state1'',
  [''state1''],
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_context3 :: "program_context" where
"test_program_context3 = 
  (fmap_of_list [],
  (fmupd
    ''process1''
    test_process_context3
    fmempty),
  ''process1'')"
definition test_ms3 :: "model_context" where
"test_ms3 = model_context.ST
  fmempty
  (fmupd
    ''program1''
    test_program_context3
    fmempty)
  ''program1''
  []
  fmempty"

definition test_statement2 :: "stmt" where
"test_statement2 = stmt.AssignSt (common_var.Symbolic ''var1'')
  (expr.Binary (binary_op.Sum) (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 2)))"

lemma "(statement_result.Continue,test_ms1)\<turnstile>test_statement2\<longrightarrow>(statement_result.Continue,test_ms3)"
  apply (simp add: test_statement2_def 
                test_ms1_def 
                test_ms3_def 
                test_process_context1_def
                test_process_context3_def
                test_program_context1_def
                test_program_context3_def)
  apply (rule AssignS)
   apply (rule BinOp)
     apply (rule Var)
   apply (auto)
   apply (rule Const)
apply (auto)
done
(* Don't work now*)
definition test_process_context4 :: "process_context" where
"test_process_context4 = 
  (fmap_of_list [(''var1'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 0) None)),
                 (''var2'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 0) None))],
  ''state1'',
  ''state1'',
  [''state1''],
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_context4 :: "program_context" where
"test_program_context4 = 
  (fmap_of_list[],
  (fmupd
    ''process1''
    test_process_context4
    fmempty),
  ''process1'')"
definition test_ms4 :: "model_context" where
"test_ms4 = model_context.ST
  fmempty
  (fmupd
    ''program1''
    test_program_context4
    fmempty)
  ''program1''
  []
  fmempty"

definition test_process_context5 :: "process_context" where
"test_process_context5 = 
  (fmap_of_list [(''var1'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 1) None)),
                 (''var2'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 2) None))],
  ''state1'',
  ''state1'',
  [''state1''],
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_context5 :: "program_context" where
"test_program_context5 = 
  (fmap_of_list[],
  (fmupd
    ''process1''
    test_process_context5
    fmempty),
  ''process1'')"
definition test_ms5 :: "model_context" where
"test_ms5 = model_context.ST
  fmempty
  (fmupd
    ''program1''
    test_program_context5
    fmempty)
  ''program1''
  []
  fmempty"

definition test_statement3 :: "stmt" where
"test_statement3 = stmt.Comb
  (stmt.AssignSt (common_var.Symbolic ''var1'')(
    expr.Binary (binary_op.Sum) (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 1))))
  (stmt.AssignSt (common_var.Symbolic ''var2'')(
    expr.Binary (binary_op.Sum) (expr.SymbolicVar ''var2'') (expr.Const (const.Nat 2))))"

find_theorems "Suc (Suc 0)"

lemma "(fmupd 2 3 (fmupd 1 2 fmempty)) = (fmupd 2 3 (fmupd 1 2 (fmupd 2 1 (fmupd 1 1 fmempty))))"
  apply (metis fmupd_idem fmupd_reorder_neq)
  done

lemma "(statement_result.Continue,test_ms4)\<turnstile>test_statement3\<longrightarrow>(statement_result.Continue,test_ms5)"
  apply (simp add: test_statement3_def 
                test_ms4_def 
                test_ms5_def 
                test_process_context4_def
                test_process_context5_def
                test_program_context4_def
                test_program_context5_def)
  apply (rule Comb)
   apply (rule AssignS)
    apply (rule BinOp)
      apply (rule Var)
      apply (auto)
   apply (rule Const)
   apply (auto)
  apply (rule AssignS)
   apply (rule BinOp)
     apply (rule Var)
     apply (auto)
   apply (rule Const)
   apply (auto)
  done
(**)

find_theorems "(Suc 0)"

definition test_process_context6 :: "process_context" where
"test_process_context6 = 
  (fmap_of_list [(''var1'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 1) None)),
                 (''var2'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 3) None))],
  ''state1'',
  ''state1'',
  [''state1''],
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_context6 :: "program_context" where
"test_program_context6 = 
  (fmap_of_list [],
  (fmupd
    ''process1''
    test_process_context6
    fmempty),
  ''process1'')"
definition test_ms6 :: "model_context" where
"test_ms6 = model_context.ST
  fmempty
  (fmupd
    ''program1''
    test_program_context6
    fmempty)
  ''program1''
  []
  fmempty"

(*
var1 = var1 + 1;
IF var1 = 1 
THEN
  var2 = var2 + 3;
ELSE 
  var2 = var2 - 2;
*)
definition test_statement4 :: "stmt" where
"test_statement4 = stmt.Comb
  (stmt.AssignSt (common_var.Symbolic ''var1'')(
    expr.Binary (binary_op.Sum) (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 1))))
  (stmt.IfSt 
    (expr.Binary binary_op.Eq (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 1)))
    (stmt.AssignSt (common_var.Symbolic ''var2'')(
      expr.Binary (binary_op.Sum) (expr.SymbolicVar ''var2'') (expr.Const (const.Nat 3))))
    (stmt.AssignSt (common_var.Symbolic ''var2'')(
      expr.Binary (binary_op.Sub) (expr.SymbolicVar ''var2'') (expr.Const (const.Nat 2)))))"

lemma "(statement_result.Continue,test_ms4)\<turnstile>test_statement4 \<longrightarrow> (statement_result.Continue,test_ms6)"
  apply (simp add:test_statement4_def 
                test_ms4_def test_process_context4_def test_program_context4_def
                test_ms6_def test_process_context6_def test_program_context6_def)
  apply (rule Comb)
   apply (rule AssignS)
    apply (rule BinOp)
      apply (rule Var)
  apply (auto)
   apply (rule Const)
   apply (auto)
  apply (rule If)
   apply (rule BinOp)
     apply (rule Var)
     apply (auto)
   apply (rule Const)
   apply (auto)
  apply (rule AssignS)
   apply (rule BinOp)
     apply (rule Var)
     apply (auto)
   apply (rule Const)
  apply (auto)
  done

definition test_process_context7 :: "process_context" where
"test_process_context7 = 
  (fmap_of_list [(''var1'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 6) None)),
                 (''var2'',stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 0) None))],
  ''state1'',
  ''state1'',
  [''state1''],
  proc_status.Active, 
  time.Time 0 0 0 0 0)"
definition test_program_context7 :: "program_context" where
"test_program_context7 = 
  (fmap_of_list [],
  (fmupd
    ''process1''
    test_process_context7
    fmempty),
  ''process1'')"
definition test_ms7 :: "model_context" where
"test_ms7 = model_context.ST
  fmempty
  (fmupd
    ''program1''
    test_program_context7
    fmempty)
  ''program1''
  []
  fmempty"

definition statement6 :: "statement" where
"statement6 = statement.IterSt (iter_statement.RepeatSt
  [(statement.AssignSt (common_var.Symbolic ''var1'')( (expr.Binary binary_op.Sum (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 2)))))]
  (expr.Binary binary_op.Less (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 5))))"
(*
definition test_statement6 :: "stmt" where 
"test_statement6 = statement_to_stmt (statement5)" 

value "test_statement6"
*)
definition test_statement6 :: "stmt" where
"test_statement6 = 
Comb (Comb
  (Comb
    (stmt.AssignSt
      (common_var.Symbolic ''var1'')( expr.Binary binary_op.Sum (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 2))))
    Blank)
  (stmt.WhileSt (expr.Binary Less (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 4)))
    (Comb
      (stmt.AssignSt
        (common_var.Symbolic ''var1'')( expr.Binary binary_op.Sum (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 2))))
      Blank)))
  (stmt.AssignSt
        (common_var.Symbolic ''var1'')( expr.Binary binary_op.Sum (expr.SymbolicVar ''var1'') (expr.Const (const.Nat 2))))"



lemma "(statement_result.Continue,test_ms4)\<turnstile> test_statement6 \<longrightarrow> (statement_result.Continue,test_ms7)"
  apply (auto simp add: test_statement6_def 
                test_ms4_def test_process_context4_def test_program_context4_def
                test_ms7_def test_process_context7_def test_program_context7_def)
  apply (rule Comb)
  apply (rule Comb)
   apply (rule Comb)
    apply (rule AssignS)
     apply (rule BinOp)
       apply (rule Var)
       apply (auto)
    apply (rule Const)
    apply (auto)
   apply (rule Blank)
  apply (auto)

  apply (rule LoopT)
   apply (rule BinOp)
       apply (rule Var)
       apply (auto)
     apply (rule Const)
      apply (auto)
    apply (rule Comb)
  apply (rule AssignS)
     apply (rule BinOp)
       apply (rule Var)
       apply (auto)
    apply (rule Const)
     apply (auto)
    apply (rule Blank)

  apply (rule LoopF)
    apply (rule BinOp)
       apply (rule Var)
       apply (auto)
     apply (rule Const)
    apply (auto)
  apply (rule AssignS)
     apply (rule BinOp)
       apply (rule Var)
       apply (auto)
    apply (rule Const)
   apply (auto)
  done


end