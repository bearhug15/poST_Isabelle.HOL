theory poST_HandDryer
  imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin


definition HandDryer :: "model" where
"HandDryer = 
  (None,[],
  [(''HandDryer'',
    [(program_var.InVar (fmap_of_list [(''hands'',var_init_decl.Simple (basic_post_type.Bool False,None))])),
     (program_var.OutVar (fmap_of_list [(''control'',var_init_decl.Simple (basic_post_type.Bool False,None))]))],
    [(''Init'',
     [],
     [(''Wait'',
       False,
       [(statement.SelectSt 
          (select_statement.IfSt [(expr.SymbolicVar ''hands'',
                                  [statement.AssignSt (common_var.Symbolic ''control'') (expr.Const (const.Bool True)),
                                   statement.SetStateSt None])] None))],
       None),
       (''Work'',
        False,
        [(statement.SelectSt 
          (select_statement.IfSt [(expr.SymbolicVar ''hands'',
                                  [statement.ResetSt])] None))],
        Some (timeout_statement.Const 
              (const.Time (time.Time 0 0 0 2 0))
              [statement.AssignSt (common_var.Symbolic ''control'') (expr.Const (const.Bool False)),
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

definition model_time :: "time" where
"model_time = time.Time 0 0 0 0 100"
declare model_time_def [simp]

lemma "(Suc 0)\<Zspot>model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st"
  apply (auto)
  apply (rule ModelCons)
  apply (rule ModelStep)
   apply (rule ProgCons)
    apply (rule ProgStep)
      apply (auto)
    apply (rule ProcCons)
     apply (auto)
     apply (rule ProcStep)
        apply (auto)
     apply (rule StateStep)
      apply (rule Comb)
       apply (rule If)
        apply (auto)
         apply (rule Var)
         apply (auto)
       apply (rule Blank)
      apply (auto)
      apply (rule Blank)
     apply (auto)
    apply (rule ProcNil)
   apply (auto)
   apply (rule ProgNil)
done

(*
lemma "(Suc 1)\<Zspot>model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st"
  apply (auto)
  apply (rule ModelCons)
  apply (rule ModelStep)
   apply (rule ProgCons)
    apply (rule ProgStep)
      apply (auto)
    apply (rule ProcCons)
     apply (auto)
     apply (rule ProcStep)
        apply (auto)
     apply (rule StateStep)
      apply (rule Comb)
       apply (rule If)
        apply (auto)
         apply (rule Var)
         apply (auto)
       apply (rule Blank)
      apply (auto)
      apply (rule Blank)
     apply (auto)
    apply (rule ProcNil)
   apply (auto)
   apply (rule ProgNil)

  apply (rule ModelCons)
  apply (rule ModelStep)
   apply (rule ProgCons)
    apply (rule ProgStep)
      apply (simp)
    apply (rule ProcCons)
     apply (auto)
     apply (rule ProcStep)
        apply (auto)
     apply (rule StateStep)
      apply (rule Comb)
       apply (rule If)
         apply (rule Var)
           apply (auto)
           apply (rule Comb)
            apply (rule Reset)
           apply (auto)
           apply (rule Blank)
          apply (auto)
          apply (rule Blank)
         apply (rule Blank)
        apply (auto)
  apply (rule Comb)
  apply (rule ProcCons)       
  done
*)
end