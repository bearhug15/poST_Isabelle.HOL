theory poST_HandDryer
  imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin


definition HandDryer :: "model" where
"HandDryer = 
  (None,[],
  [(''HandDryer'',
    [(prog_var.InVar ( [(''hands'',var_init_decl.Symbolic (ptype.Bool False) None)])),
     (prog_var.OutVar ( [(''control'',var_init_decl.Symbolic (ptype.Bool False) None)]))],
    [(''Init'',
     [],
     [(''Wait'',
       False,
       [(statement.SelectSt 
          (select_statement.IfSt 
            [(expr.SymbolicVar ''hands'',
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
               statement.SetStateSt (Some ''Wait'')]))
    :: state_decl]) 
  :: process_decl]):: program_decl],
  [],[]) "
declare HandDryer_def [simp]

definition stacked_HandDryer :: "stacked_model" where
"stacked_HandDryer = stack_model HandDryer"
declare stacked_HandDryer_def [simp]

value "stacked_HandDryer"

definition stacked_HandDaryer_model :: "model_context" where
"stacked_HandDaryer_model = initialize_model_context stacked_HandDryer"
declare stacked_HandDaryer_model_def [simp]

value "stacked_HandDaryer_model"

definition model_time :: "time" where
"model_time = time.Time 0 0 0 0 100"
declare model_time_def [simp]

definition set_hands :: "model_context \<Rightarrow> model_context" where
"set_hands st = set_cur_symbvar st ''hands'' (ptype.Bool True)"
declare set_hands_def [simp]

definition remove_hands :: "model_context \<Rightarrow> model_context" where
"remove_hands st = set_cur_symbvar st ''hands'' (ptype.Bool False)"
declare remove_hands_def [simp]


schematic_goal "model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>?st"
  apply (auto)
  apply (rule ModelStep)
  apply (auto)
   apply (rule ProgCons)
    apply (rule ProgStep)
      apply (auto)
    apply (rule ProcCons)
     apply (auto)
     apply (rule ProcStep)
        apply (auto)
     apply (rule StateStep)
       apply (rule IfF)
        apply (auto)
         apply (rule Symbolic)
         apply (auto)
       apply (rule Blank)
    apply (rule ProcNil)
   apply (rule ProgNil)
  done

schematic_goal "model_time:(set_hands stacked_HandDaryer_model)\<turnstile>stacked_HandDryer\<mapsto>?st"
  apply (auto)
  apply (rule ModelStep)
  apply (auto)
  apply (rule ProgCons)
    apply (rule ProgStep)
      apply (auto)
    apply (rule ProcCons)
     apply (auto)
     apply (rule ProcStep)
        apply (auto)
     apply (rule StateStep)
       apply (rule IfT)
        apply (auto)
         apply (rule Symbolic)
        apply (auto)
      apply (rule Comb)
       apply (rule AssignS)
        apply (rule Const)
        apply (auto)
       apply (rule SetState)
       apply (auto)
   apply (rule ProcNil)
  apply (rule ProgNil)
  done

definition set_control :: "model_context \<Rightarrow> model_context" where
"set_control st = set_cur_symbvar st ''control'' (ptype.Bool True)"
declare set_control_def [simp]

schematic_goal "model_time:(set_control stacked_HandDaryer_model)\<turnstile>stacked_HandDryer\<mapsto>?st"
  apply (auto)
  apply (rule ModelStep) apply (auto)
  apply (rule ProgCons)
   apply (rule ProgStep) apply (auto)
   apply (rule ProcCons) apply (auto)
    apply (rule ProcStep) apply (auto)
    apply (rule StateStep)
      apply (rule IfF) apply (auto)
        apply (rule Symbolic) apply (auto)
      apply (rule Blank)
   apply (rule ProcNil)
  apply (rule ProgNil)
  done

definition set_overtime :: "model_context \<Rightarrow> model_context" where
"set_overtime st = add_time_to_active_processes st (time.Time 0 0 0 2 1)"
declare set_overtime_def [simp]

definition set_work_state :: "model_context \<Rightarrow> model_context" where
"set_work_state st = set_into_next_state (set_state st ''Work'')"
declare set_work_state_def [simp]
(*
schematic_goal "model_time:(set_work_state (set_overtime (set_control stacked_HandDaryer_model)))\<turnstile>stacked_HandDryer\<mapsto>?st"
  apply (auto)
  apply (rule ModelStep) apply (auto)
  apply (rule ProgCons)
   apply (rule ProgStep) apply (auto)
   apply (rule ProcCons) apply (auto)
     apply (rule ProcStep) apply (auto)
       apply (rule StateStep)
         apply (rule IfF) apply (auto)
           apply (rule Symbolic) apply (auto)
     apply (rule Blank) apply (auto)
    apply (rule Comb)
     apply (rule AssignS) apply (auto)
     apply (rule Const) apply (auto)
    apply (rule SetState) apply (auto) 
   apply (rule ProcNil)
  apply (rule ProgNil)
  done
*) 



text "If the dryer is on, then it turns off after no hands are present for 2 second."
lemma
  assumes "time_step:st\<turnstile>stacked_HandDryer\<mapsto>st1" 
  and     "time_more (get_cur_time st) (time.Time 0 0 0 2 0)" 
  and     "\<not>(ptype_to_bool (get_cur_symbvar_by_name st ''hands''))" 
  shows   "\<not>(ptype_to_bool (get_cur_symbvar_by_name st1 ''control''))"
proof 
qed


(*
text "If the dryer was not turned on and hands appeared, it will turn on ASAP."
lemma
  "model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st \<Longrightarrow> 
  \<not>(ptype_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''control'')) 
  (ptype_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''hands'')) \<Longrightarrow>
  (ptype_to_bool (get_cur_symbvar_by_name st ''control''))"
proof sorry
qed
*)

(*
text "If the hands are present and the dryer is on, it will not turn off."
lemma
  "model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st \<Longrightarrow> 
  (ptype_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''hands'')) \<Longrightarrow>
  (ptype_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''control'')) \<Longrightarrow>
  (ptype_to_bool (get_cur_symbvar_by_name st ''control''))"
proof sorry
qed
*)

(*
text "If there is no hands and the dryer is not turned on, the dryer will not turn on until the hands appear."
lemma
  "model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st \<Longrightarrow> 
  \<not>(ptype_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''hands'')) \<Longrightarrow>
  \<not>(ptype_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''control'')) \<Longrightarrow>
  \<not>(ptype_to_bool (get_cur_symbvar_by_name st ''control''))"
proof sorry
qed
*)

end