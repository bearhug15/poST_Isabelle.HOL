theory poST_Test
	imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin
definition task1_test :: "task" where
"task1_test = 
(''Task2'', (task_init.Interval (const.Int (10))), 2)"

definition ProgConf_test :: "program_conf_decl" where
"ProgConf_test = 
(''ProgramConfiguration1'',
 (Some ''Task1''),
 ''Program1'',
 (Some 
 	[(''var2'', assign_type.Conseq, (attach_var.SymbolicVar ''var2''))]))"

definition Test :: "model" where
"Test =
	(None,
	 [(False, 
	 	[(''var1'', (all_var_init_decl.Var 
	 		(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))),
	 	(''var1'', (all_var_init_decl.GlobalVar ((direct_type_perfix.I, direct_size_prefix.D, [(10), (10)]), (basic_post_type.Int 0))))])],
	 
	 [(''Program1'',
	  [(prog_var.ExtVar (False, 
	  	[(''var1'', (basic_post_type.Int 0))]))],
	 	[(''process1'',
	 	 [(proc_var.Var (True, 
	 	 	[(''var1'', 
	 	 	 (var_init_decl.Array 
	 	 	 	(array_interval.Expr (expr.Const (const.Int (-5))) (expr.Const (const.Int (-5))))
	 	 	 	[]
	 	 	 	(Some [(expr.Const (const.Int (-5))), (expr.Const (const.Int (-5)))])))])),
	 	 (proc_var.Var (False, 
	 	 	[(''var1'', 
	 	 	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5)))))),
	 	 	(''var2'', 
	 	 	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])), 
	 	 (proc_var.InVar 
	 	 	[(''var1'', 
	 	 	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	 	 (proc_var.OutVar 
	 	 	[(''var1'', 
	 	 	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	 	 (proc_var.InOutVar 
	 	 	[(''var1'', 
	 	 	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])],
	 		[(''State1'', 
	 			True, 
	 			[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	 			 (statement.SetStateSt None)], 
	 			None), 
	 		 (''State2'', 
	 			False, 
	 			[], 
	 			(Some (timeout_statement.Const (const.Nat 0)
	 				[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	 				 (statement.SetStateSt None)])))]), 
	 	 (''process1'',
	 	 [(proc_var.Var (True, 
	 	 	[(''var1'', 
	 	 	 (var_init_decl.Array 
	 	 	 	(array_interval.Expr (expr.Const (const.Int (-5))) (expr.Const (const.Int (-5))))
	 	 	 	[]
	 	 	 	(Some [(expr.Const (const.Int (-5))), (expr.Const (const.Int (-5)))])))])),
	 	 (proc_var.Var (False, 
	 	 	[(''var1'', 
	 	 	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5)))))),
	 	 	(''var2'', 
	 	 	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])), 
	 	 (proc_var.InVar 
	 	 	[(''var1'', 
	 	 	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	 	 (proc_var.OutVar 
	 	 	[(''var1'', 
	 	 	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	 	 (proc_var.InOutVar 
	 	 	[(''var1'', 
	 	 	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])],
	 		[(''State1'', 
	 			True, 
	 			[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	 			 (statement.SetStateSt None)], 
	 			None), 
	 		 (''State2'', 
	 			False, 
	 			[], 
	 			(Some (timeout_statement.Const (const.Nat 0)
	 				[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	 				 (statement.SetStateSt None)])))])])],
	 
	 [(''Function1'',
	  (basic_post_type.Int 0),
	  [],
	  [(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	   (statement.SetStateSt None)])],
	 
	 [(''FunctionBlock1'',
	  [(func_block_var.ExtVar (False, 
	  	[(''var1'', (basic_post_type.Int 0))]))],
	  [(''process1'',
	   [(proc_var.Var (True, 
	   	[(''var1'', 
	   	 (var_init_decl.Array 
	   	 	(array_interval.Expr (expr.Const (const.Int (-5))) (expr.Const (const.Int (-5))))
	   	 	[]
	   	 	(Some [(expr.Const (const.Int (-5))), (expr.Const (const.Int (-5)))])))])),
	   (proc_var.Var (False, 
	   	[(''var1'', 
	   	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5)))))),
	   	(''var2'', 
	   	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])), 
	   (proc_var.InVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	   (proc_var.OutVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	   (proc_var.InOutVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])],
	  	[(''State1'', 
	  		True, 
	  		[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	  		 (statement.SetStateSt None)], 
	  		None), 
	  	 (''State2'', 
	  		False, 
	  		[], 
	  		(Some (timeout_statement.Const (const.Nat 0)
	  			[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	  			 (statement.SetStateSt None)])))]), 
	  (''process1'',
	   [(proc_var.Var (True, 
	   	[(''var1'', 
	   	 (var_init_decl.Array 
	   	 	(array_interval.Expr (expr.Const (const.Int (-5))) (expr.Const (const.Int (-5))))
	   	 	[]
	   	 	(Some [(expr.Const (const.Int (-5))), (expr.Const (const.Int (-5)))])))])),
	   (proc_var.Var (False, 
	   	[(''var1'', 
	   	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5)))))),
	   	(''var2'', 
	   	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])), 
	   (proc_var.InVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	   (proc_var.OutVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	   (proc_var.InOutVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])],
	  	[(''State1'', 
	  		True, 
	  		[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	  		 (statement.SetStateSt None)], 
	  		None), 
	  	 (''State2'', 
	  		False, 
	  		[], 
	  		(Some (timeout_statement.Const (const.Nat 0)
	  			[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	  			 (statement.SetStateSt None)])))])]), 
	 
	 (''FunctionBlock1'',
	  [(func_block_var.ExtVar (False, 
	  	[(''var1'', (basic_post_type.Int 0))]))],
	  [(''process1'',
	   [(proc_var.Var (True, 
	   	[(''var1'', 
	   	 (var_init_decl.Array 
	   	 	(array_interval.Expr (expr.Const (const.Int (-5))) (expr.Const (const.Int (-5))))
	   	 	[]
	   	 	(Some [(expr.Const (const.Int (-5))), (expr.Const (const.Int (-5)))])))])),
	   (proc_var.Var (False, 
	   	[(''var1'', 
	   	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5)))))),
	   	(''var2'', 
	   	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])), 
	   (proc_var.InVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	   (proc_var.OutVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	   (proc_var.InOutVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])],
	  	[(''State1'', 
	  		True, 
	  		[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	  		 (statement.SetStateSt None)], 
	  		None), 
	  	 (''State2'', 
	  		False, 
	  		[], 
	  		(Some (timeout_statement.Const (const.Nat 0)
	  			[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	  			 (statement.SetStateSt None)])))]), 
	  (''process1'',
	   [(proc_var.Var (True, 
	   	[(''var1'', 
	   	 (var_init_decl.Array 
	   	 	(array_interval.Expr (expr.Const (const.Int (-5))) (expr.Const (const.Int (-5))))
	   	 	[]
	   	 	(Some [(expr.Const (const.Int (-5))), (expr.Const (const.Int (-5)))])))])),
	   (proc_var.Var (False, 
	   	[(''var1'', 
	   	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5)))))),
	   	(''var2'', 
	   	 (var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])), 
	   (proc_var.InVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	   (proc_var.OutVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))]), 
	   (proc_var.InOutVar 
	   	[(''var1'', 
	   	(var_init_decl.Symbolic (basic_post_type.Int 0) (Some (expr.Const (const.Int (-5))))))])],
	  	[(''State1'', 
	  		True, 
	  		[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	  		 (statement.SetStateSt None)], 
	  		None), 
	  	 (''State2'', 
	  		False, 
	  		[], 
	  		(Some (timeout_statement.Const (const.Nat 0)
	  			[(statement.AssignSt (common_var.Symbolic ''var1'') (expr.Const (const.Int (-5)))), 
	  			 (statement.SetStateSt None)])))])])])"
end