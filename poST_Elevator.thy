theory poST_Elevator
  imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin

definition Elevator :: "model" where
"Elevator = 
  (None,[],
  [(''Controller'',
    [(program_var.InVar 
      (fmap_of_list 
        [(''onfloor0'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''onfloor1'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''onfloor2'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''call0'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''call1'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''call2'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''button0'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''button1'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''button2'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''door0closed'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''door1closed'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''door2closed'',var_init_decl.Simple (basic_post_type.Bool False,None))])),
     (program_var.OutVar 
      (fmap_of_list 
        [(''up'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''down'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''open0'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''open1'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''open2'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''call0_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''call1_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''call2_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''button0_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''button1_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''button2_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''floor0_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''floor1_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''floor2_LED'',var_init_decl.Simple (basic_post_type.Bool False,None)),
         (''cur'',var_init_decl.Simple (basic_post_type.Int 0,None))])),
     (program_var.Var (False, 
      (fmap_of_list 
        [(''target'',var_init_decl.Simple (basic_post_type.Int 0,None))])))],
    [(''Init'',
      [],
      [(''begin'',
        False,
        [(statement.ProcessSt (process_statement.Start (Some ''Call0Latch''))),
         (statement.ProcessSt (process_statement.Start (Some ''Call1Latch''))),
         (statement.ProcessSt (process_statement.Start (Some ''Call2Latch''))),
         (statement.ProcessSt (process_statement.Start (Some ''Button0Latch''))),
         (statement.ProcessSt (process_statement.Start (Some ''Button1Latch''))),
         (statement.ProcessSt (process_statement.Start (Some ''Button2Latch''))),
         (statement.ProcessSt (process_statement.Start (Some ''CheckCurFloor''))),
         (statement.ProcessSt (process_statement.Start (Some ''UpControl''))),
         (statement.ProcessSt (process_statement.Stop None))],
        None)::state_decl])::process_decl,
     (''Call0Latch'',
      [(proc_var.Var (False,
        (fmap_of_list
          [(''prev_in'',var_init_decl.Simple (basic_post_type.Bool False,None)),
           (''prev_out'',var_init_decl.Simple (basic_post_type.Bool False,None))])))],
      [(''init'',
        False,
        [(statement.AssignSt (common_var.Symbolic ''prev_in'', expr.Unary (Some unary_op.Not) (expr.SymbolicVar ''call0''))),
         (statement.AssignSt (common_var.Symbolic ''prev_out'', expr.Unary (Some unary_op.Not) (expr.SymbolicVar ''open0''))),
         (statement.SetStateSt None)],
        None),
       (''check_ON_OFF'',
        True,
        [(statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''call0'') (expr.Unary (Some unary_op.Not) (expr.SymbolicVar ''prev_in'')),
                                  [(statement.AssignSt (common_var.Symbolic ''call0_LED'', expr.Const (const.Bool True)))])]
                                None)),
         (statement.SelectSt (select_statement.IfSt
                                [(expr.Binary (binary_op.And) (expr.SymbolicVar ''open0'') (expr.Unary (Some unary_op.Not) (expr.SymbolicVar ''prev_out'')),
                                  [(statement.AssignSt (common_var.Symbolic ''call0_LED'', expr.Const (const.Bool False)))])]
                                None)),
         (statement.AssignSt (common_var.Symbolic ''prev_in'', expr.SymbolicVar ''call0'')),
         (statement.AssignSt (common_var.Symbolic ''prev_out'', expr.SymbolicVar ''open0''))],
        None)])])::program_decl],
  [],[])"

end