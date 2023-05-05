theory poSTVM_alt_inductive
  imports 
    "~~/poST/poSTVM/poSTVM_state_alt" 
    "~~/poST/poSTVM/poSTVM_initializer"
begin
datatype statement_result =  Continue | Exit | Return 



value "butlast [1::nat,2,3,4]" 

(*
datatype expr = Unary "unary_op option"  prim_expr |
                Binary binary_op expr expr
  and prim_expr = Const const | 
                  SymbolicVar symbolic_var | 
                  ArrayVar symbolic_var expr |
                  Expression expr | 
                  ProcStatEpxr process_name proc_status | 
                  FunctionCall func_name "param_assign list"	
  and param_assign =SymbolicVar  symbolic_var assign_type expr

datatype stmt = 
  AssignSt assign_statement |
  FBInvocation fb_invocation |
  Return |
  Exit |
  ProcessSt process_contextment |
  SetStateSt set_state_statement |
  ResetSt |
  IfSt expr stmt stmt |
  WhileSt expr stmt |
  Comb stmt stmt |
  Blank 
*)

text "exec process statement"
definition update_process_status :: "model_context \<Rightarrow> process_contextment \<Rightarrow>(statement_result* model_context)" where
"update_process_status st ps =
  (case ps of
    process_contextment.Start name_option \<Rightarrow> 
      (case name_option of
        None \<Rightarrow> (statement_result.Return, reset_cur_process st)
      | Some name \<Rightarrow> (statement_result.Continue, reset_process st name))
  | process_contextment.Stop name_option \<Rightarrow> 
      (case name_option of
        None \<Rightarrow> (statement_result.Return, stop_cur_process st)
      | Some name \<Rightarrow> (statement_result.Continue, stop_process st name))
  | process_contextment.Error name_option \<Rightarrow> 
      (case name_option of
        None \<Rightarrow> (statement_result.Return, error_cur_process st)
  | Some name \<Rightarrow> (statement_result.Continue, error_process st name)))"
declare update_process_status_def [simp]

inductive 
  eval :: "[model_context, expr, basic_post_type] \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _") and
  exec :: "[statement_result * model_context,stmt,statement_result * model_context] \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow> _") and
  exec_func :: "[model_context,func_name,func_params,model_context*basic_post_type] \<Rightarrow> bool" ("_\<turnstile>_,_\<longrightarrow> _") and
  assign_param :: "[model_context,assign_type,param_assign list,model_context,model_context] \<Rightarrow> bool"
  where
    BinOp : "\<lbrakk>st\<turnstile>exp1\<rightarrow>val1;
              st\<turnstile>exp2\<rightarrow>val2;
              val = binary_op_exec bin_op val1 val2 \<rbrakk> \<Longrightarrow>
             st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>val"
  | UnOp : "\<lbrakk>st\<turnstile>pexp\<rightarrow>val1;
                val = (unary_op_exec un_op val1)\<rbrakk> \<Longrightarrow>
               st\<turnstile> expr.Unary un_op pexp\<rightarrow>val"
  | Const : "\<lbrakk>val = const_to_basic c\<rbrakk>\<Longrightarrow>
            st\<turnstile>expr.Const c\<rightarrow>val"
  | Var :  "\<lbrakk>val = get_cur_symbvar_by_name st var_name\<rbrakk>\<Longrightarrow>
           st\<turnstile>expr.SymbolicVar var_name\<rightarrow>val"
  | ArrayVar : "\<lbrakk>st\<turnstile>exp\<rightarrow>pos;
                 val = get_cur_arvar_by_name_by_pos st var_name pos\<rbrakk>\<Longrightarrow>
               st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>val"
  | PSE : "\<lbrakk>val = check_proc_status st p_name p_status\<rbrakk>\<Longrightarrow>
          st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>val"

  | Blank : "(res,st)\<turnstile>stmt.Blank\<longrightarrow>(res,st)"
  | Comb : "\<lbrakk>st\<turnstile>s1\<longrightarrow>st_res1;
             (st_res1)\<turnstile>(case (fst st_res1) of
                          (statement_result.Continue) \<Rightarrow> s2
                        | (res) \<Rightarrow> stmt.Blank)\<longrightarrow>st2 \<rbrakk>\<Longrightarrow>
           st\<turnstile>stmt.Comb s1 s2 \<longrightarrow> st2"
  | If : "\<lbrakk>(snd st)\<turnstile>exp\<rightarrow>val;
            st\<turnstile>(if (basic_post_type_to_bool val) then s1 else s2)\<longrightarrow>st1\<rbrakk>\<Longrightarrow>
         st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st1"
  | LoopF : "\<lbrakk>(snd st)\<turnstile>exp\<rightarrow>val; \<not>(basic_post_type_to_bool val)\<rbrakk>\<Longrightarrow>
            st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st"
  | LoopT : "\<lbrakk>(snd st)\<turnstile>exp\<rightarrow>val; (basic_post_type_to_bool val);
              st\<turnstile>s\<longrightarrow>st1;st1\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
            st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2"
  | AssignS : "\<lbrakk>(snd st)\<turnstile>exp\<rightarrow>val;
                st1 = (set_symbvar (snd st) var_name val)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Symbolic var_name) exp\<longrightarrow>(statement_result.Continue, st1)"
  | AssignA : "\<lbrakk>(snd st)\<turnstile>exp\<rightarrow>val1;
                (snd st)\<turnstile>pos\<rightarrow>val2;
                st1 = (set_arvar (snd st) var_name val2 val1)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Array var_name pos) exp\<longrightarrow>(statement_result.Continue, st1)"
  | Return : "st\<turnstile>stmt.Return\<longrightarrow>(statement_result.Continue, snd st)"
  | Exit : "st\<turnstile>stmt.Exit\<longrightarrow>(statement_result.Continue, snd st)"
  | Process : "\<lbrakk>st2 = (update_process_status (snd st) ps)\<rbrakk>\<Longrightarrow>
                st\<turnstile>stmt.ProcessSt ps\<longrightarrow>st2"
  | SetState : "\<lbrakk>st1 = (case st_name_option of
                        None \<Rightarrow> (statement_result.Continue, set_next_state_next (snd st))
                      | Some name \<Rightarrow> (statement_result.Continue, set_state (snd st) name))\<rbrakk>\<Longrightarrow>
                st\<turnstile>stmt.SetStateSt st_name_option\<longrightarrow>st1"
  | Reset : "\<lbrakk>st1 = reset_cur_timer(snd st)\<rbrakk> \<Longrightarrow> st\<turnstile>stmt.ResetSt\<longrightarrow>(statement_result.Continue,st1)"

  | FuncStep : "\<lbrakk>(f_name,res,vars,stmts) = (get_func_by_name st name);
                  proxy_state = (gen_proxy_for_func st (f_name,res,vars,stmts));
                  assign_param st assign_type.ColonEq params proxy_state as_proxy_state;
                  (statement_result.Continue, as_proxy_state)\<turnstile>stmts\<longrightarrow>(st_res,st1);
                  assign_param st1 assign_type.Conseq params st new_st;
                  res = (get_cur_symbvar_by_name st1 f_name)\<rbrakk>\<Longrightarrow>
                st\<turnstile>name,params\<longrightarrow>(new_st,res)"
  | AssignPNill : "assign_param base_st type [] st st"
  | AssignPConsCol : "\<lbrakk>base_st \<turnstile> exp \<rightarrow> val;
                       (if as_type = assign_type.ColonEq 
                        then (assign_param base_st assign_type.ColonEq other (set_symbvar st name val) new_st)
                        else (assign_param base_st assign_type.ColonEq other st new_st))\<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.ColonEq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"
  | AssignPConsCon : "\<lbrakk>base_st \<turnstile> exp \<rightarrow> val;
                       (if as_type = assign_type.Conseq 
                        then (assign_param base_st assign_type.Conseq other st new_st) 
                        else (assign_param base_st assign_type.Conseq other (set_symbvar st name val) new_st))  \<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.Conseq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"
(*
inductive_cases BinOp[elim!]: "st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>val"
inductive_cases UnOp[elim!]: "st\<turnstile>expr.Unary un_op exp\<rightarrow>val"
inductive_cases Const[elim!]: "st\<turnstile>expr.Const c\<rightarrow>val"
inductive_cases Var[elim!]: "st\<turnstile>expr.SymbolicVar var_name\<rightarrow>val"
inductive_cases ArrayVar[elim!]: "st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>val"
inductive_cases PSE[elim!]: "st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>val"
inductive_cases Blank[elim!]: "(res,st)\<turnstile>stmt.Blank\<longrightarrow>(res,st)"
inductive_cases Comb[elim!]: "st\<turnstile>stmt.Comb s1 s2 \<longrightarrow> st2"
inductive_cases If[elim!]: "st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st1"
inductive_cases Loop[elim]: "st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st"
inductive_cases AssignS[elim!]: "st\<turnstile>stmt.AssignSt (common_var.Symbolic var_name) exp\<longrightarrow>(statement_result.Continue, st1)"
inductive_cases AssignA[elim!]: "st\<turnstile>stmt.AssignSt (common_var.Array var_name pos) exp\<longrightarrow>(statement_result.Continue, st1)"
inductive_cases Return[elim!]: "st\<turnstile>stmt.Return\<longrightarrow>(statement_result.Continue, snd st)"
inductive_cases Exit[elim!]: "st\<turnstile>stmt.Exit\<longrightarrow>(statement_result.Continue, snd st)"
inductive_cases Process[elim!]: "st\<turnstile>stmt.ProcessSt ps\<longrightarrow>st2"
inductive_cases SetState[elim!]: "st\<turnstile>stmt.SetStateSt st_name_option\<longrightarrow>st1"
inductive_cases Reset[elim!]: "st\<turnstile>stmt.ResetSt\<longrightarrow>(statement_result.Continue,st1)"
*)

(*declare eval_exec_exec_func_assign_param.intros [simp,intro]*)
(*
declare eval.simps [simp]
declare exec.simps [simp]
*)
(*
declare BinOp [simp]
declare UnOp [simp]
declare Var [simp]
declare ArrayVar [simp]
declare PSE [simp]
declare Blank [simp]
declare Comb [simp]
declare If [simp]
declare LoopF [simp]
declare LoopT [simp]
declare AssignS [simp]
declare AssignA [simp]
declare Return [simp]
declare Exit [simp]
declare Process [simp]
declare SetState [simp]
declare Reset [simp]
*)
inductive 
  eval_state :: "[model_context,stacked_state,statement_result * model_context] \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
    StateStep : "\<lbrakk>(statement_result.Continue,st)\<turnstile>stm\<longrightarrow>(res,st1);
                  (case res of 
                    statement_result.Continue \<Rightarrow> 
                      (case timeout_op of
                        None \<Rightarrow> (res,st2) = (res,st1)
                      | (Some timeout) \<Rightarrow> 
                          (case (extr_timeout_stmt st1 timeout) of 
                            None \<Rightarrow> (res,st2) = (res,st1)
                          | (Some stm1) \<Rightarrow> ((statement_result.Continue,st1)\<turnstile>stm1\<longrightarrow>(res,st2))))
                  )\<rbrakk> \<Longrightarrow> 
                st \<turnstile>(name,_,stm,timeout_op):(res,st2)"
(*declare eval_state.intros [simp,intro]*)

inductive 
  eval_process :: "[model_context,stacked_process,model_context] \<Rightarrow> bool" ("_\<turnstile>_\<Rightarrow>_") and
  evals_process :: "[model_context,stacked_process list,model_context] \<Rightarrow> bool" ("_\<turnstile>_[\<Rightarrow>]_") where
    ProcStep : "\<lbrakk> new_st = (set_cur_proc_name st name);
                  new_st\<turnstile>(get_state_by_name state_list (get_cur_proc_state_name new_st)) :(res,st1);
                  st2 = (case res of 
                          statement_result.Continue \<Rightarrow> st1
                        | statement_result.Exit \<Rightarrow> stop_cur_process st1
                        | statement_result.Return \<Rightarrow> st1);
                  st3 = (set_into_next_state st2)\<rbrakk> \<Longrightarrow> 
                st\<turnstile>(name,var_list,state_list) \<Rightarrow> st3"
  | ProcNil : "st\<turnstile>[][\<Rightarrow>]st"
  | ProcCons : "\<lbrakk>active = (is_process_active st (fst pr));
                (if active 
                    then st\<turnstile>pr\<Rightarrow>st1 
                    else st\<turnstile>[][\<Rightarrow>]st1);
                 st1\<turnstile>other[\<Rightarrow>]st2 \<rbrakk> \<Longrightarrow> 
                st\<turnstile>(pr#other)[\<Rightarrow>]st2"
(*declare eval_process_evals_process.intros [simp,intro]*)

inductive 
  eval_program :: "[model_context,stacked_program,model_context] \<Rightarrow> bool" ("_\<turnstile>_\<Longrightarrow>_") and
  evals_program :: "[model_context,stacked_program list,model_context] \<Rightarrow> bool" ("_\<turnstile>_[\<Longrightarrow>]_") where
    ProgStep : "\<lbrakk>new_st = (set_cur_prog_name st name);
                 new_st\<turnstile>process_list[\<Rightarrow>]st1;
                 st2 = process_vars_distribution st1\<rbrakk>\<Longrightarrow> 
              st\<turnstile>(name,var_list,process_list) \<Longrightarrow>st2"
  | ProgNil : "st\<turnstile>[][\<Longrightarrow>]st"
  | ProgCons : "\<lbrakk>st\<turnstile>pr\<Longrightarrow>st1;
                 st1\<turnstile>other[\<Longrightarrow>]st2\<rbrakk> \<Longrightarrow> 
               st\<turnstile>(pr#other)[\<Longrightarrow>]st2"
(*declare eval_program_evals_program.intros [simp,intro]*)
print_theorems

inductive 
  eval_model :: "[time,model_context,stacked_model,model_context] \<Rightarrow> bool" ("_:_\<turnstile>_\<mapsto>_") where
    ModelStep : "\<lbrakk>timed_st = (add_time_to_active_processes st t);
                  timed_st\<turnstile>prog_list[\<Longrightarrow>]st1;
                  st2 = prog_vars_distribution st1\<rbrakk> \<Longrightarrow>
                t:st\<turnstile>(_,_,prog_list,_,_)\<mapsto>st2"
(*declare eval_model.intros [simp,intro]*)

(*ModelStep ProgCons ProgNil ProgStep ProcCons ProcNil ProcStep StateStep Reset SetState Process Exit Return AssignA AssignS LoopT LoopF If Comb Blank*)

inductive 
  model_steps :: "[nat,time,model_context,stacked_model,model_context] \<Rightarrow> bool" ("_\<Zspot>_:_\<turnstile>_\<mapsto>_") where
    ModelNil : "0\<Zspot>t:st\<turnstile>model\<mapsto>st"
  | ModelCons : "\<lbrakk>t:st\<turnstile>model\<mapsto>st1;
                  n\<Zspot>t:st1\<turnstile>model\<mapsto>st2\<rbrakk> \<Longrightarrow> 
                (Suc n)\<Zspot>t:st\<turnstile>model\<mapsto>st2"

code_pred eval.
declare eval_def [simp]



end