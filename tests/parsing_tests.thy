theory parsing_tests
  imports "~~/poST/poSTVM/poSTVM_parser_alt"
begin
definition expr1 :: "expr" where
"expr1 = 
  (expr.Binary
    binary_op.Sum
    (expr.Unary
      unary_op.Minus
      (expr.SymbolicVar ''var1''))
    (expr.Binary
      binary_op.Mul
      (expr.ArrayVar 
        ''var2'' 
        (expr.Const (const.Nat 0)))
      (expr.ProcStatEpxr 
        ''process1''
        proc_status.Active)))"

definition stacked_expr1 :: "expr_stack" where
"stacked_expr1 = 
  [
  (expr_op.Binary binary_op.Sum),
  (expr_op.Unary unary_op.Minus),
  (expr_op.Get ''var1''),
  (expr_op.Binary binary_op.Mul),
  (expr_op.GetArray ''var2''),
  (expr_op.Value (basic_post_type.Nat 0)),
  (expr_op.CheckProcStat ''process1'' proc_status.Active)]"

definition check_expr_parse :: "expr \<Rightarrow> expr_stack \<Rightarrow> bool" where
"check_expr_parse exp sexp = ((stack_expr expr1) = stacked_expr1)"

value "check_expr_parse expr1 stacked_expr1"

definition statements1 :: "statement list" where
"statements1 = 
  [
  (statement.AssignSt 
    (common_var.Symbolic ''var1'')
    (expr.Const (const.Nat 0))),
  (statement.FBInvocation
    ''FB1''
    [(param_assign.SymbolicVar
        ''var1''
        assign_type.ColonEq
        (expr.Const (const.Nat 1))),
     (param_assign.SymbolicVar
        ''var1''
        assign_type.Conseq
        (expr.Const (const.Nat 2)))]),
  (statement.Return),
  (statement.Exit),
  (statement.ProcessSt 
    (process_contextment.Start None)),
  (statement.SetStateSt None),
  (statement.ResetSt),
  (statement.SelectSt
    (select_statement.IfSt
      [((expr.Const (const.Bool True)),
          [])]
      None)),
  (statement.SelectSt 
    (select_statement.CaseSt 
      (expr.Const (const.Nat 0))
      ([([1],[(statement.Return)])])
      None)),
  (statement.IterSt
    (iter_statement.ForSt
      ''i''
      ((expr.Const (const.Nat 0)),(expr.Const (const.Nat 2)),None)
      []))]"

definition stmt1 :: "stmt" where
"stmt1 = 
  (stmt.Comb
    (stmt.AssignSt
      (common_var.Symbolic ''var1'')
      (expr.Const (const.Nat 0)))
    (stmt.Comb
      (stmt.FBInvocation
        ''FB1''
        [(param_assign.SymbolicVar
            ''var1''
            assign_type.ColonEq
            (expr.Const (const.Nat 1))),
         (param_assign.SymbolicVar
            ''var1''
            assign_type.Conseq
            (expr.Const (const.Nat 2)))])
      (stmt.Comb
        (stmt.Return)
        (stmt.Comb
          (stmt.Exit)
          (stmt.Comb
            (stmt.ProcessSt (process_contextment.Start None))
            (stmt.Comb
              (stmt.SetStateSt None)
              (stmt.Comb
                (stmt.ResetSt)
                (stmt.Comb
                  (stmt.IfSt
                    (expr.Const (const.Bool True))
                    (stmt.Blank)
                    (stmt.Blank))
                  (stmt.Comb
                    (stmt.IfSt
                      (expr.Binary
                        binary_op.Eq
                        (expr.Const (const.Nat 0))
                        (expr.Const (const.Nat 1)))
                        (stmt.Return)
                      (stmt.Blank))
                      (stmt.Comb
                        (stmt.AssignSt
                          (common_var.Symbolic ''i'')
                          (expr.Const (const.Nat 0)))
                        (stmt.WhileSt
                          (expr.Binary
                            binary_op.Less
                            (expr.SymbolicVar ''i'')
                            (expr.Const (const.Nat 2)))
                          (stmt.Comb
                            (stmt.Blank)
                            (stmt.AssignSt
                              (common_var.Symbolic ''i'')
                              (expr.Binary
                                binary_op.Sum
                                (expr.SymbolicVar ''i'')
                                (expr.Const (const.Nat 1)))))))
                      )))))))))"

definition check_statement_parse :: "statement list \<Rightarrow> stmt \<Rightarrow> bool" where
"check_statement_parse st stm = ((st_list_to_stmt st) = stm)"

value "check_statement_parse statements1 stmt1"


definition state1 :: "state_decl" where
"state1 = (''state1'',False,statements1, (Some (timeout_statement.SymbolicVar ''time_var'' statements1)))"

definition stacked_state1 :: "stacked_state" where
"stacked_state1 = (''state1'',False,stmt1, (Some (timeout.SymbolicVar ''time_var'' stmt1)))"

definition check_state_parse :: "state_decl \<Rightarrow> stacked_state \<Rightarrow> bool" where
"check_state_parse sd ssd= ((stack_state sd) = ssd)"

value "check_state_parse state1 stacked_state1"


definition process_vars1 :: "proc_var list" where
"process_vars1 = 
  [(proc_var.Var (False,[(''var1'', var_init_decl.Symbolic (basic_post_type.Nat 0) (Some (expr.Const (const.Int 1))))])),
   (proc_var.ProcessVar []),
   (proc_var.InOutVar [(''var2'', var_init_decl.Array (array_interval.Int 0 1) [] None)]),
   (proc_var.InVar [(''var3'', var_init_decl.Symbolic (basic_post_type.Nat 1) None)]),
   (proc_var.OutVar [(''var4'', var_init_decl.Symbolic (basic_post_type.Nat 2) None)])]"

definition stacked_process_vars1 :: "stacked_proc_vars" where
"stacked_process_vars1 = 
  (fmap_of_list
    [(''var1'', stacked_proc_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 0) (Some [(expr_op.Value (basic_post_type.Int 1))]))),
     (''var2'', stacked_proc_var.InOutVar (stacked_var_init.Array (stacked_array_interval.Int 0 1) [] None)),
     (''var3'', stacked_proc_var.InVar (stacked_var_init.Symbolic (basic_post_type.Nat 1) None)),
     (''var4'', stacked_proc_var.OutVar (stacked_var_init.Symbolic (basic_post_type.Nat 2) None))])"

definition check_proc_var_parse :: "proc_var list \<Rightarrow> stacked_proc_vars \<Rightarrow> bool" where
"check_proc_var_parse pv spv = ((stack_proc_vars pv) = spv)"

value "check_proc_var_parse process_vars1 stacked_process_vars1"


definition process1 :: "process_decl" where
"process1 = (''process1'',process_vars1,[state1])"

definition stacked_process1 :: "stacked_process" where
"stacked_process1 = (''process1'',stacked_process_vars1,[stacked_state1])"

definition check_process_parse :: "process_decl \<Rightarrow> stacked_process \<Rightarrow> bool" where
"check_process_parse pd sp = ((stack_process pd) = sp)"

value "check_process_parse process1 stacked_process1"


definition prog_vars1 :: "prog_var list" where
"prog_vars1 = 
  [(prog_var.ExtVar (False,[(''var1'',basic_post_type.Nat 0)])),
   (prog_var.Var (False,[(''var2'',var_init_decl.Symbolic (basic_post_type.Nat 1) None)])),
   (prog_var.InOutVar [(''var3'',var_init_decl.Symbolic (basic_post_type.Nat 2) None)]),
   (prog_var.InVar [(''var4'', var_init_decl.Symbolic (basic_post_type.Nat 3) None)]),
   (prog_var.OutVar [(''var5'', var_init_decl.Symbolic (basic_post_type.Nat 4) None)])]"

definition stacked_prog_vars1 :: "stacked_prog_vars" where
"stacked_prog_vars1 =
  (fmap_of_list 
    [(''var1'', stacked_prog_var.ExtVar (stacked_var_init.Symbolic (basic_post_type.Nat 0) None)),
     (''var2'', stacked_prog_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 1) None)),
     (''var3'', stacked_prog_var.InOutVar (stacked_var_init.Symbolic (basic_post_type.Nat 2) None)),
     (''var4'', stacked_prog_var.InVar (stacked_var_init.Symbolic (basic_post_type.Nat 3) None)),
     (''var5'', stacked_prog_var.OutVar (stacked_var_init.Symbolic (basic_post_type.Nat 4) None))])"

definition check_prog_vars_parse :: "prog_var list \<Rightarrow> stacked_prog_vars \<Rightarrow> bool" where
"check_prog_vars_parse pv spv = ((stack_prog_vars pv) = spv)"

value "check_prog_vars_parse prog_vars1 stacked_prog_vars1"

definition program1 :: "program_decl" where
"program1 = (''program1'',prog_vars1,[process1])"

definition stacked_program1 :: "stacked_program" where
"stacked_program1 = (''program1'',stacked_prog_vars1,[stacked_process1])"

definition check_program_parse :: "program_decl \<Rightarrow> stacked_program \<Rightarrow> bool" where
"check_program_parse pd sp = ((stack_program pd) = sp)"

value "check_program_parse program1 stacked_program1"


definition global_vars1 :: "global_var_decl list" where
"global_vars1 =
  [(False,[(''var1'', all_var_init_decl.Var (var_init_decl.Symbolic (basic_post_type.Nat 0) None)),
           (''var2'', all_var_init_decl.GlobalVar ((direct_type_perfix.I,direct_size_prefix.X,[]), basic_post_type.Nat 1))])]"

definition stacked_global_vars1 :: "stacked_global_vars" where
"stacked_global_vars1 =
  (fmap_of_list
    [(''var1'', stacked_global_var.Var (stacked_var_init.Symbolic (basic_post_type.Nat 0) None)),
     (''var2'', stacked_global_var.Global (direct_type_perfix.I,direct_size_prefix.X,[]) (basic_post_type.Nat 1))])"

definition check_global_vars_parse :: "global_var_decl list \<Rightarrow> stacked_global_vars \<Rightarrow> bool" where
"check_global_vars_parse gvd sgv = ((stack_global_vars gvd) = sgv)"

value "stack_global_vars global_vars1"

value "check_global_vars_parse global_vars1 stacked_global_vars1"


definition model1 :: "model" where
"model1 = (None,global_vars1,[program1],[],[])"

definition stacked_model1 :: "stacked_model" where
"stacked_model1 = (None,stacked_global_vars1,[stacked_program1],[],fmempty)"

definition check_model_parse :: "model \<Rightarrow> stacked_model \<Rightarrow> bool" where
"check_model_parse m sm = ((stack_model m) = sm)"

value "check_model_parse model1 stacked_model1"


end