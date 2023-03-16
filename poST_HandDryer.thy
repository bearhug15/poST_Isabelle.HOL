theory poST_HandDryer
  imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin


definition HandDryer :: "model" where
"HandDryer = 
  (None,[],
  [(''HandDryer'',
    [(program_var.InVar (fmap_of_list [(''hands'',var_init_decl.Simple (basic_post_type.Bool False,None))])),
     (program_var.OutVar (fmap_of_list [(''control'',var_init_decl.Simple (basic_post_type.Bool False,None))]))],
    [(''HandDryer'',
     [],
     [(''Wait'',
       False,
       [(statement.SelectSt 
          (select_statement.IfSt [(expr.SymbolicVar ''hands'',
                                  [statement.AssignSt (common_var.Symbolic ''control'',expr.Const (const.Bool True)),
                                   statement.SetStateSt None])] None))],
       None),
       (''Work'',
        False,
        [(statement.SelectSt 
          (select_statement.IfSt [(expr.SymbolicVar ''hands'',
                                  [statement.ResetSt])] None))],
        Some (timeout_statement.Const 
              (const.Time (time.Time 0 0 0 2 0))
              [statement.AssignSt (common_var.Symbolic ''control'',expr.Const (const.Bool False)),
               statement.SetStateSt None]))
    :: state_decl]) 
  :: process_decl]):: program_decl],
  [],[]) "
declare HandDryer_def [simp]

definition stacked_HandDryer :: "stacked_model" where
"stacked_HandDryer = stack_model HandDryer"
declare stacked_HandDryer_def [simp]

value "stacked_HandDryer"

definition stacked_HandDaryer_model :: "model_state" where
"stacked_HandDaryer_model = initialize_model_state stacked_HandDryer"
declare stacked_HandDaryer_model_def [simp]

value "stacked_HandDaryer_model"


text "If the dryer is on, then it turns off after no hands are present for 1 second"
text "If process time > 1s then control = false"
definition rule1 :: "model_state \<Rightarrow> bool" where
"rule1 st = 
  ((time_more (get_time st ''HandDryer'') (time.Time 0 0 0 1 0)) \<longrightarrow> \<not>(basic_post_type_to_bool (get_symbvar_by_name st ''control''))) "
declare rule1_def [simp]

lemma "\<lbrakk>st = stacked_HandDaryer_model;
        model = stacked_HandDryer\<rbrakk> \<Longrightarrow>\<forall>n::nat. (n\<Zspot>t:st\<turnstile>model\<mapsto>st1) \<longrightarrow> (rule1 st1)"
  apply auto




end