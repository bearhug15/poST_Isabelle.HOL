theory poST_HandDryer
  imports "~~/poST/poSTVM/poSTVM_alt_inductive"
begin


definition HandDryer :: "model" where
"HandDryer = 
  (None,[],
  [(''HandDryer'',
    [(prog_var.InVar ( [(''hands'',var_init_decl.Symbolic (basic_post_type.Bool False) None)])),
     (prog_var.OutVar ( [(''control'',var_init_decl.Symbolic (basic_post_type.Bool False) None)]))],
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
"set_hands st = set_symbvar st ''hands'' (basic_post_type.Bool True)"
declare set_hands_def [simp]

definition remove_hands :: "model_context \<Rightarrow> model_context" where
"remove_hands st = set_symbvar st ''hands'' (basic_post_type.Bool False)"
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
         apply (rule Var)
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
         apply (rule Var)
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
"set_control st = set_symbvar st ''control'' (basic_post_type.Bool True)"
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
        apply (rule Var) apply (auto)
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

schematic_goal "model_time:(set_work_state (set_overtime (set_control stacked_HandDaryer_model)))\<turnstile>stacked_HandDryer\<mapsto>?st"
  apply (auto)
  apply (rule ModelStep) apply (auto)
  apply (rule ProgCons)
   apply (rule ProgStep) apply (auto)
   apply (rule ProcCons) apply (auto)
     apply (rule ProcStep) apply (auto)
       apply (rule StateStep)
         apply (rule IfF) apply (auto)
           apply (rule Var) apply (auto)
     apply (rule Blank) apply (auto)
    apply (rule Comb)
     apply (rule AssignS) apply (auto)
     apply (rule Const) apply (auto)
    apply (rule SetState) apply (auto) 
   apply (rule ProcNil)
  apply (rule ProgNil)
  done

lemma 
"st\<turnstile>stmt.AssignSt (common_var.Symbolic ''hands'') (expr.Const (const.Nat 1)) \<longrightarrow> st1 \<Longrightarrow>
 basic_post_type_eq (get_cur_symbvar_by_name st1 ''hands'') (basic_post_type.Nat 1)"
  apply (induction st1 arbitrary:st)
  apply auto
  apply (rule )

(*
text "If the dryer is on, then it turns off after no hands are present for 1 second."
lemma
  "model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st \<Longrightarrow> 
  time_more (get_cur_time stacked_HandDaryer_model) (time 0 0 0 1 0) \<Longrightarrow>
  \<not>(basic_post_type_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''hands'')) \<Longrightarrow>
  \<not>(basic_post_type_to_bool (get_cur_symbvar_by_name st ''control''))"
proof 
qed
*)

(*
text "If the dryer was not turned on and hands appeared, it will turn on ASAP."
lemma
  "model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st \<Longrightarrow> 
  \<not>(basic_post_type_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''control'')) 
  (basic_post_type_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''hands'')) \<Longrightarrow>
  (basic_post_type_to_bool (get_cur_symbvar_by_name st ''control''))"
proof sorry
qed
*)

(*
text "If the hands are present and the dryer is on, it will not turn off."
lemma
  "model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st \<Longrightarrow> 
  (basic_post_type_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''hands'')) \<Longrightarrow>
  (basic_post_type_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''control'')) \<Longrightarrow>
  (basic_post_type_to_bool (get_cur_symbvar_by_name st ''control''))"
proof sorry
qed
*)

(*
text "If there is no hands and the dryer is not turned on, the dryer will not turn on until the hands appear."
lemma
  "model_time:stacked_HandDaryer_model\<turnstile>stacked_HandDryer\<mapsto>st \<Longrightarrow> 
  \<not>(basic_post_type_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''hands'')) \<Longrightarrow>
  \<not>(basic_post_type_to_bool (get_cur_symbvar_by_name stacked_HandDaryer_model ''control'')) \<Longrightarrow>
  \<not>(basic_post_type_to_bool (get_cur_symbvar_by_name st ''control''))"
proof sorry
qed
*)

end