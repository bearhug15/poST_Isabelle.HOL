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
  ProcessSt process_statement |
  SetStateSt set_state_statement |
  ResetSt |
  IfSt expr stmt stmt |
  WhileSt expr stmt |
  Comb stmt stmt |
  Blank 
*)

text "exec process statement"
definition update_process_status :: "model_context \<Rightarrow> process_statement \<Rightarrow>(statement_result* model_context)" where
"update_process_status st ps =
  (case ps of
    process_statement.Start name_option \<Rightarrow> 
      (case name_option of
        None \<Rightarrow> (statement_result.Return, reset_cur_process st)
      | Some name \<Rightarrow> (statement_result.Continue, reset_process st name))
  | process_statement.Stop name_option \<Rightarrow> 
      (case name_option of
        None \<Rightarrow> (statement_result.Return, stop_cur_process st)
      | Some name \<Rightarrow> (statement_result.Continue, stop_process st name))
  | process_statement.Error name_option \<Rightarrow> 
      (case name_option of
        None \<Rightarrow> (statement_result.Return, error_cur_process st)
  | Some name \<Rightarrow> (statement_result.Continue, error_process st name)))"
declare update_process_status_def [simp]

inductive 
  eval :: "[model_context, expr, model_context] \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _") and
  exec :: "[model_context,stmt,model_context] \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow> _") and
  exec_func :: "[model_context,func_name,func_params,model_context] \<Rightarrow> bool" ("_\<turnstile>_,_\<longrightarrow> _") and
  assign_param :: "[model_context,assign_type,param_assign list,model_context,model_context] \<Rightarrow> bool"
  where
    BinOp : "\<lbrakk>st\<turnstile>exp1\<rightarrow>st1;
              val1 = get_value st1;
              st1\<turnstile>exp2\<rightarrow>st2;
              val2 = get_value st2;
              val = binary_op_exec bin_op val1 val2 \<rbrakk> \<Longrightarrow>
              st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>(set_value st2 val)"
  | UnOp : "\<lbrakk>st\<turnstile>pexp\<rightarrow>st1;
             val1 = get_value st1;
             val = (unary_op_exec un_op val1)\<rbrakk> \<Longrightarrow>
             st\<turnstile> expr.Unary un_op pexp\<rightarrow>(set_value st1 val)"
  | Const : "\<lbrakk>st1 = (set_value st (const_to_basic c))\<rbrakk>\<Longrightarrow>
              st\<turnstile>expr.Const c\<rightarrow>st1"
  | Symbolic :  "\<lbrakk>val = get_cur_symbvar_by_name st var_name;
                  st1 = (set_value st val)\<rbrakk>\<Longrightarrow>
                  st\<turnstile>expr.SymbolicVar var_name\<rightarrow>st1"
  | Array : "\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
              pos = get_value st1;
              val = get_cur_arvar_by_name_by_pos st1 var_name pos\<rbrakk>\<Longrightarrow>
              st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>(set_value st1 val)"
  | PSE : "\<lbrakk>val = check_proc_status st p_name p_status\<rbrakk>\<Longrightarrow>
            st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>(set_value st val)"
  | FuncCall : "\<lbrakk>st\<turnstile>name,as_list\<longrightarrow>st1\<rbrakk> \<Longrightarrow> 
                 st\<turnstile>expr.FunctionCall name as_list \<rightarrow> st1"

  | Blank : "st\<turnstile>stmt.Blank\<longrightarrow>st"
  | Comb : "\<lbrakk>st\<turnstile>s1\<longrightarrow>st1;
             st1\<turnstile>s2\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
           st\<turnstile>stmt.Comb s1 s2 \<longrightarrow>st2"
  | IfT : "\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
            (ptype_to_bool (get_value st1));
            st1\<turnstile>s1\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
         st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st2"
  | IfF : "\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
           \<not>(ptype_to_bool (get_value st1));
           st1\<turnstile>s2\<longrightarrow>st2\<rbrakk> \<Longrightarrow> st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st2"
  | LoopF : "\<lbrakk>st\<turnstile>exp\<rightarrow>st1; 
              \<not>(ptype_to_bool (get_value st1))\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st1"
  | LoopT : "\<lbrakk>st\<turnstile>exp\<rightarrow>st1; 
              (ptype_to_bool (get_value st1));
              st1\<turnstile>s\<longrightarrow>st2;
              st2\<turnstile>stmt.WhileSt exp s\<longrightarrow>st3\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st3"
  | AssignS : "\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
                st2 = (set_cur_symbvar st1 var_name (get_value st1))\<rbrakk>\<Longrightarrow>
                st\<turnstile>stmt.AssignSt (common_var.Symbolic var_name) exp\<longrightarrow>st2"
  | AssignA : "\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
                val1 = get_value st1;
                st1\<turnstile>pos\<rightarrow>st2;
                val2 = get_value st2;
                st3 = (set_arvar st2 var_name val2 val1)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Array var_name pos) exp\<longrightarrow>st3"
  | Return : "st\<turnstile>stmt.Return\<longrightarrow>st"
  | Exit : "st\<turnstile>stmt.Exit\<longrightarrow>st"
  | ProcessStart : "\<lbrakk>st1 = (case stm_name_option of None \<Rightarrow> reset_cur_process st | Some name \<Rightarrow> reset_process st name)\<rbrakk> \<Longrightarrow> 
                    st\<turnstile>stmt.ProcessSt (process_statement.Start stm_name_option)\<longrightarrow>st1"
  | ProcessStop : "\<lbrakk>st1 = (case stm_name_option of None \<Rightarrow> stop_cur_process st | Some name \<Rightarrow> stop_process st name)\<rbrakk> \<Longrightarrow> 
                    st\<turnstile>stmt.ProcessSt (process_statement.Start stm_name_option)\<longrightarrow>st1"
  | ProcessError : "\<lbrakk>st1 = (case stm_name_option of None \<Rightarrow> error_cur_process st | Some name \<Rightarrow> error_process st name)\<rbrakk> \<Longrightarrow> 
                    st\<turnstile>stmt.ProcessSt (process_statement.Start stm_name_option)\<longrightarrow>st1"
  | SetState : "\<lbrakk>st1 = (case st_name_option of
                        None \<Rightarrow> (set_next_state_next st)
                      | Some name \<Rightarrow> (set_state st name))\<rbrakk>\<Longrightarrow>
                st\<turnstile>stmt.SetStateSt st_name_option\<longrightarrow>st1"
  | Reset : "\<lbrakk>st1 = reset_cur_timer st\<rbrakk> \<Longrightarrow> st\<turnstile>stmt.ResetSt\<longrightarrow>st1"

  | FuncStep : "\<lbrakk>(f_name,res,vars,stmts) = (get_func_by_name st name);
                  proxy_state = (gen_proxy_for_func st (f_name,res,vars,stmts));
                  assign_param st assign_type.ColonEq params proxy_state as_proxy_state;
                  as_proxy_state\<turnstile>stmts\<longrightarrow>st1;
                  assign_param st1 assign_type.Conseq params st new_st;
                  res = (get_cur_symbvar_by_name st1 f_name)\<rbrakk>\<Longrightarrow>
                st\<turnstile>name,params\<longrightarrow>(set_value new_st res)"
  | AssignPNill : "assign_param base_st type [] st st"
  | AssignPConsCol : "\<lbrakk>base_st \<turnstile> exp \<rightarrow> st;
                       val = get_value st;
                       (if as_type = assign_type.ColonEq 
                        then (assign_param base_st assign_type.ColonEq other (set_cur_symbvar st name val) new_st)
                        else (assign_param base_st assign_type.ColonEq other st new_st))\<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.ColonEq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"
  | AssignPConsCon : "\<lbrakk>base_st \<turnstile> exp \<rightarrow> st;
                       val = get_value st;
                       (if as_type = assign_type.Conseq 
                        then (assign_param base_st assign_type.Conseq other st new_st) 
                        else (assign_param base_st assign_type.Conseq other (set_cur_symbvar st name val) new_st))  \<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.Conseq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"

print_theorems 

text "eval code_pred_intro lemmas"
lemma [code_pred_intro]: 
"\<lbrakk>st\<turnstile>exp1\<rightarrow>st1;
              val1 = get_value st1;
              st1\<turnstile>exp2\<rightarrow>st2;
              val2 = get_value st2;
              val = binary_op_exec bin_op val1 val2 \<rbrakk> \<Longrightarrow>
              st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>(set_value st2 val)"
  using BinOp by auto
lemma [code_pred_intro]:
"\<lbrakk>st\<turnstile>pexp\<rightarrow>st1;
             val1 = get_value st1;
             val = (unary_op_exec un_op val1)\<rbrakk> \<Longrightarrow>
             st\<turnstile> expr.Unary un_op pexp\<rightarrow>(set_value st1 val)"
  using UnOp by auto
lemma [code_pred_intro]:
"\<lbrakk>val = const_to_basic c\<rbrakk>\<Longrightarrow>
              st\<turnstile>expr.Const c\<rightarrow>(set_value st val)"
  using Const by auto
lemma [code_pred_intro]:
"\<lbrakk>val = get_cur_symbvar_by_name st var_name\<rbrakk>\<Longrightarrow>
             st\<turnstile>expr.SymbolicVar var_name\<rightarrow>(set_value st val)"
  using Symbolic by auto
lemma [code_pred_intro]:
"\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
                 pos = get_value st1;
                 val = get_cur_arvar_by_name_by_pos st1 var_name pos\<rbrakk>\<Longrightarrow>
                 st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>(set_value st1 val)"
  using Array by auto
lemma [code_pred_intro]:
"\<lbrakk>val = check_proc_status st p_name p_status\<rbrakk>\<Longrightarrow>
            st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>(set_value st val)"
  using PSE by auto
lemma [code_pred_intro]:
"\<lbrakk>st\<turnstile>name,as_list\<longrightarrow>st1\<rbrakk> \<Longrightarrow> 
                 st\<turnstile>expr.FunctionCall name as_list \<rightarrow> st1"
  using FuncCall by auto

inductive_cases BinOpE[elim!]: "st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>st3"
inductive_cases UnOpE[elim!]: "st\<turnstile> expr.Unary un_op pexp\<rightarrow>st2"
inductive_cases ConstE[elim!]: "st\<turnstile>expr.Const c\<rightarrow>st1"
inductive_cases SymbolicE[elim!]: "st\<turnstile>expr.SymbolicVar var_name\<rightarrow>st1"
inductive_cases ArrayE[elim!]: "st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>st2"
inductive_cases PSE[elim!]: "st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>st1"
inductive_cases FuncCallE[elim!]: "st\<turnstile>expr.FunctionCall name as_list \<rightarrow> st1"

text "exec code_pred_intro lemmas"
lemma [code_pred_intro]:
"st\<turnstile>stmt.Blank\<longrightarrow>st"
"\<lbrakk>st\<turnstile>s1\<longrightarrow>st1;
             st1\<turnstile>s2\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
           st\<turnstile>stmt.Comb s1 s2 \<longrightarrow>st2"
"\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
            (ptype_to_bool (get_value st1));
            st1\<turnstile>s1\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
         st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st2"
"\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
           \<not>(ptype_to_bool (get_value st1));
           st1\<turnstile>s2\<longrightarrow>st2\<rbrakk> \<Longrightarrow> st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st2"
"\<lbrakk>st\<turnstile>exp\<rightarrow>st1; 
              \<not>(ptype_to_bool (get_value st1))\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st1"
"\<lbrakk>st\<turnstile>exp\<rightarrow>st1; 
              (ptype_to_bool (get_value st1));
              st1\<turnstile>s\<longrightarrow>st2;
              st2\<turnstile>stmt.WhileSt exp s\<longrightarrow>st3\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st3"
"\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
                st2 = (set_cur_symbvar st1 var_name (get_value st1))\<rbrakk>\<Longrightarrow>
                st\<turnstile>stmt.AssignSt (common_var.Symbolic var_name) exp\<longrightarrow>st2"
"\<lbrakk>st\<turnstile>exp\<rightarrow>st1;
                val1 = get_value st1;
                st1\<turnstile>pos\<rightarrow>st2;
                val2 = get_value st2;
                st3 = (set_arvar st2 var_name val2 val1)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Array var_name pos) exp\<longrightarrow>st3"
"st\<turnstile>stmt.Return\<longrightarrow>st"
"st\<turnstile>stmt.Exit\<longrightarrow>st"
"\<lbrakk>st1 = (case stm_name_option of None \<Rightarrow> reset_cur_process st | Some name \<Rightarrow> reset_process st name)\<rbrakk> \<Longrightarrow> 
                    st\<turnstile>stmt.ProcessSt (process_statement.Start stm_name_option)\<longrightarrow>st1"
"\<lbrakk>st1 = (case stm_name_option of None \<Rightarrow> stop_cur_process st | Some name \<Rightarrow> stop_process st name)\<rbrakk> \<Longrightarrow> 
                    st\<turnstile>stmt.ProcessSt (process_statement.Start stm_name_option)\<longrightarrow>st1"
"\<lbrakk>st1 = (case stm_name_option of None \<Rightarrow> error_cur_process st | Some name \<Rightarrow> error_process st name)\<rbrakk> \<Longrightarrow> 
                    st\<turnstile>stmt.ProcessSt (process_statement.Start stm_name_option)\<longrightarrow>st1"
"\<lbrakk>st1 = (case st_name_option of
                        None \<Rightarrow> (set_next_state_next st)
                      | Some name \<Rightarrow> (set_state st name))\<rbrakk>\<Longrightarrow>
                st\<turnstile>stmt.SetStateSt st_name_option\<longrightarrow>st1"
"\<lbrakk>st1 = reset_cur_timer st\<rbrakk> \<Longrightarrow> st\<turnstile>stmt.ResetSt\<longrightarrow>st1"
by (auto intro: eval_exec_exec_func_assign_param.intros)

inductive_cases BlankE[elim!]: "st\<turnstile>stmt.Blank\<longrightarrow>st1"
thm BlankE
inductive_cases CombE[elim!]: "st\<turnstile>stmt.Comb s1 s2 \<longrightarrow>st2"
thm CombE
inductive_cases IfE[elim!]: "st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st1"
thm IfE
inductive_cases LoopE[elim!]: "st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2"
thm LoopE
inductive_cases AssignSE[elim!]: "st\<turnstile>stmt.AssignSt (common_var.Symbolic v) exp\<longrightarrow>st2"
thm AssignSE
inductive_cases AssignAE[elim!]: "st\<turnstile>stmt.AssignSt (common_var.Array v exp1) exp2\<longrightarrow>st2"
inductive_cases ReturnE[elim!]: "st\<turnstile>stmt.Return\<longrightarrow>st"
inductive_cases ExitE[elim!]: "st\<turnstile>stmt.Exit\<longrightarrow>st"
inductive_cases ProcessE[elim!]: "st\<turnstile>stmt.ProcessSt p\<longrightarrow>st1"
inductive_cases SetStateE[elim!]: "st\<turnstile>stmt.SetStateSt st_name_option\<longrightarrow>st1"
inductive_cases ResetE[elim!]: "st\<turnstile>stmt.ResetSt\<longrightarrow>st1"

text "param_assign code_pred_intro lemmas"
lemma [code_pred_intro]:
"assign_param base_st type [] st st"
"\<lbrakk>base_st \<turnstile> exp \<rightarrow> st;
                       val = get_value st;
                       (if as_type = assign_type.ColonEq 
                        then (assign_param base_st assign_type.ColonEq other (set_cur_symbvar st name val) new_st)
                        else (assign_param base_st assign_type.ColonEq other st new_st))\<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.ColonEq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"
"\<lbrakk>base_st \<turnstile> exp \<rightarrow> st;
                       val = get_value st;
                       (if as_type = assign_type.Conseq 
                        then (assign_param base_st assign_type.Conseq other st new_st) 
                        else (assign_param base_st assign_type.Conseq other (set_cur_symbvar st name val) new_st))  \<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.Conseq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"
  by (auto intro: eval_exec_exec_func_assign_param.intros)

inductive_cases AssignPE[elim!]: "assign_param base_st at pa st new_st"

(*
text "exec_func code_pred_intro lemmas"
lemma [code_pred_intro]:
"\<lbrakk>(f_name,res,vars,stmts) = (get_func_by_name st name);
                  proxy_state = (gen_proxy_for_func st (f_name,res,vars,stmts));
                  assign_param st assign_type.ColonEq params proxy_state as_proxy_state;
                  as_proxy_state\<turnstile>stmts\<longrightarrow>st1;
                  assign_param st1 assign_type.Conseq params st new_st;
                  res = (get_cur_symbvar_by_name st1 f_name)\<rbrakk>\<Longrightarrow>
                st\<turnstile>name,params\<longrightarrow>new_st1"
  by sledgehammer

inductive_cases FuncE[elim!]:"st\<turnstile>name,params\<longrightarrow>(new_st,res)"
*)
inductive 
  eval_state :: "[model_context,stacked_state,model_context] \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
    StateStep : "\<lbrakk>st\<turnstile>stm\<longrightarrow>st1;
                  (case timeout_op of
                    None \<Rightarrow> st2 = st1
                    | (Some timeout) \<Rightarrow> 
                      (case (extr_timeout_stmt st1 timeout) of 
                        None \<Rightarrow> st2 = st1
                        | (Some stm1) \<Rightarrow> (st1\<turnstile>stm1\<longrightarrow>st2)))\<rbrakk> \<Longrightarrow> 
                st \<turnstile>(name,stm,timeout_op):st2"
(*declare eval_state.intros [simp,intro]*)

inductive 
  eval_process :: "[model_context,stacked_process,model_context] \<Rightarrow> bool" ("_\<turnstile>_\<Rightarrow>_") and
  evals_process :: "[model_context,stacked_process list,model_context] \<Rightarrow> bool" ("_\<turnstile>_[\<Rightarrow>]_") where
    ProcStep : "\<lbrakk> new_st = (set_cur_proc_name st name);
                  state = (get_state_by_name state_list (get_cur_proc_state_name new_st));
                  new_st\<turnstile>state:st1;
                  st3 = (set_into_next_state st1)\<rbrakk> \<Longrightarrow> 
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


lemma comb_assoc:
"st\<turnstile>stmt.Comb (stmt.Comb c1 c2) c3 \<longrightarrow> st1 \<longleftrightarrow> st\<turnstile>stmt.Comb c1 (stmt.Comb c2 c3) \<longrightarrow> st1"
proof 
  assume "st\<turnstile>stmt.Comb (stmt.Comb c1 c2) c3 \<longrightarrow> st1"
  then obtain s1 s2 where
    c1: "st\<turnstile>c1\<longrightarrow>s1" and
    c2: "s1\<turnstile>c2\<longrightarrow>s2" and
    c3: "s2\<turnstile>c3\<longrightarrow>st1" by auto
  from c2 c3
  have "s1\<turnstile>stmt.Comb c2 c3 \<longrightarrow>st1" by (rule Comb)
  with c1
  show "st\<turnstile>(stmt.Comb c1 (stmt.Comb c2 c3))\<longrightarrow>st1" by (rule Comb)
next
  assume "st\<turnstile>stmt.Comb c1 (stmt.Comb c2 c3)\<longrightarrow>st1"
  then obtain s1 s2 where
    c1: "st\<turnstile>c1\<longrightarrow>s1" and
    c2: "s1\<turnstile>c2\<longrightarrow>s2" and
    c3: "s2\<turnstile>c3\<longrightarrow>st1" by auto
  from c1 c2
  have "st\<turnstile>stmt.Comb c1 c2 \<longrightarrow>s2" by (rule Comb)
  with c3
  show "st\<turnstile>(stmt.Comb (stmt.Comb c1 c2) c3)\<longrightarrow>st1" by (simp add: Comb)
qed

(*
Doesn't because b may has side effects 
lemma
"st\<turnstile>stmt.IfSt b stmt.Blank stmt.Blank \<longrightarrow> st1 \<Longrightarrow> st = st1"
  by sledgehammer
*)  

abbreviation equiv_c :: "stmt \<Rightarrow> stmt \<Rightarrow> bool" (infix "\<sim>" 50) where
"c \<sim> c' \<equiv> (\<forall>s t. s\<turnstile>c\<longrightarrow>t = s\<turnstile>c'\<longrightarrow>t)"

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto

lemma unfold_while:
"(stmt.WhileSt b c) \<sim> (stmt.IfSt b (stmt.Comb c (stmt.WhileSt b c)) (stmt.Blank))" (is "?w \<sim> ?iw")
proof -
  have "st\<turnstile>?iw\<longrightarrow>st1" if assm: "st\<turnstile>?w\<longrightarrow>st1" for st st1
  proof - 
    from assm show ?thesis
    proof cases
      case LoopF
      thus ?thesis by (simp add: Blank IfF)
    next
      case LoopT
      thus ?thesis by (simp add: Comb IfT)
    qed
  qed
  moreover
  have "st\<turnstile>?w\<longrightarrow>st1" if assm: "st\<turnstile>?iw\<longrightarrow>st1" for st st1
  proof -
    from assm show ?thesis
    proof cases
      case IfF
      thus ?thesis using LoopF by fastforce
    next
      case IfT
      thus ?thesis using LoopT by force
    qed
  qed
  ultimately
  show ?thesis by meson
qed

(*
Doesn't because b may has side effects
lemma triv_if:
"st\<turnstile>(stmt.IfSt b c c)\<longrightarrow>st1 \<Longrightarrow> st\<turnstile>c\<longrightarrow>st1"
proof -
  assume "st\<turnstile>(stmt.IfSt b c c)\<longrightarrow>st1"
  then show ?thesis
  proof cases
    case IfF
    thus ?thesis by blast
  next
    case IfT
    thus ?thesis by blast
  qed
qed
*)
(*
lemma triv_if:
"(stmt.IfSt b c c) \<sim> c" (is "?w \<sim>?iw")
proof -
  have "st\<turnstile>?iw\<longrightarrow>st1" if assm: "st\<turnstile>?w\<longrightarrow>st1" for st st1
  proof -
    from assm show ?thesis
    proof cases
      case IfF
      thus ?thesis by blast
    next
      case IfT
      thus ?thesis by blast
    qed
  qed
  moreover
  have "st\<turnstile>?w\<longrightarrow>st1" if assm: "st\<turnstile>?iw\<longrightarrow>st1" for st st1
  proof -
    fix b::expr
    from assm show ?thesis
    proof (induction b arbitrary:?iw rule: eval_exec_exec_func_assign_param.induct)
*)
(*
lemma comute_if:
  "st\<turnstile>(stmt.IfSt b1 (stmt.IfSt b2 c11 c12) c2)\<longrightarrow>st1 \<longleftrightarrow> st\<turnstile>(stmt.IfSt b2 (stmt.IfSt b1 c11 c2) (stmt.IfSt b1 c12 c2))\<longrightarrow>st1" (is "?w\<longleftrightarrow>?iw")
proof -
  have ?iw if assm: ?w
*)

(*   
lemma commute_if:
  "(stmt.IfSt b1 (stmt.IfSt b2 c11 c12) c2) 
    \<sim>
   (stmt.IfSt b2 (stmt.IfSt b1 c11 c2) (stmt.IfSt b1 c12 c2))" (is "?w \<sim> ?iw")
*)
(*
theorem
  "st\<turnstile>c\<longrightarrow>st1 \<Longrightarrow> st\<turnstile>c\<longrightarrow>st2 \<Longrightarrow> st1=st2"
proof (induction arbitrary: st2 rule: eval_exec_exec_func_assign_param.induct)
*)

declare eval_def [simp]


lemma const_simp[simp]: "const_to_basic (const.Nat val) = ptype.Nat val"by auto

lemma value_mirror[simp]: "get_value (set_value st val) = val"
  apply (induction st)
  apply auto
  done

lemma global_vars_mirror1[simp]: "get_global_vars (set_global_vars st vars) = vars"
  apply (induction st)
  apply auto
  done

lemma global_vars_mirror2[simp]:
  "(get_var_from_global_vars_by_name (set_var_in_global_vars_by_name st name val) name) = val"
proof -
  show ?thesis sorry
qed

lemma prog_vars_mirror1[simp]: "get_cur_prog_vars (set_cur_prog_vars st vars) = vars" 
proof -
  show ?thesis sorry
qed

lemma prog_vars_mirror2[simp]: "(get_prog_var_by_name (set_var_in_prog_vars_by_name st name val) name) = val" 
proof -
  show ?thesis sorry
qed

lemma basic_eq[simp]: "ptype_eq (ptype.Nat v1) (ptype.Nat v2) \<longleftrightarrow> v1 = v2" by auto

declare Let_def[simp] option.split[split]

lemma set_symbvar_global_level_keep[simp]:
  assumes "get_var_level_by_name st name = var_level.Global"
  shows "get_var_level_by_name (set_global_var st name val) name = var_level.Global"
proof -
  show ?thesis sorry
qed

lemma set_symbvar_program_level_keep[simp]:
  assumes "get_var_level_by_name st name = var_level.Program"
  shows "get_var_level_by_name (set_cur_prog_var st name val) name = var_level.Program"
proof -
  show ?thesis sorry
qed

lemma set_symbvar_process_level_keep[simp]:
  assumes "get_var_level_by_name st name = var_level.Process"
  shows "get_var_level_by_name (set_cur_proc_var st name val) name = var_level.Process"
proof -
  show ?thesis sorry
qed

lemma set_symbvar_level_keep[simp]:
  fixes level :: var_level
  assumes "get_var_level_by_name st name = level"
  shows "get_var_level_by_name (set_cur_symbvar st name val) name = level"
proof (cases level)
  case Global
  hence "get_var_level_by_name (set_cur_symbvar st name val) name = get_var_level_by_name (set_global_var st name (stacked_var_init.Symbolic val None)) name" using assms by auto
  then show ?thesis using set_symbvar_global_level_keep using Global assms by simp
next
  case Program
  hence "get_var_level_by_name (set_cur_symbvar st name val) name = get_var_level_by_name (set_cur_prog_var st name (stacked_var_init.Symbolic val None)) name" using assms by auto
  then show ?thesis using set_symbvar_program_level_keep using Program assms by simp
next
  case Process
  hence "get_var_level_by_name (set_cur_symbvar st name val) name = get_var_level_by_name (set_cur_proc_var st name (stacked_var_init.Symbolic val None)) name" using assms by auto
  then show ?thesis using set_symbvar_process_level_keep using Process assms by simp
qed

lemma global_var_mirror[simp]:
  assumes "get_var_level_by_name st name = var_level.Global"
  shows "(get_cur_var_init_by_name (set_global_var st name val) name) = val"
proof -
  from assms have 
   "(get_cur_var_init_by_name (set_global_var st name val) name) = 
    (get_var_from_global_vars_by_name (get_global_vars 
      (set_global_var st name val)) 
    name)" using set_symbvar_global_level_keep by auto
  hence
    "(get_cur_var_init_by_name (set_global_var st name val) name) =
     (get_var_from_global_vars_by_name (get_global_vars 
      (set_global_vars st (set_var_in_global_vars_by_name (get_global_vars st) name val))) 
      name)" by simp
  hence
    "(get_cur_var_init_by_name (set_global_var st name val) name) =
     (get_var_from_global_vars_by_name (set_var_in_global_vars_by_name (get_global_vars st) 
      name val) name)" using global_vars_mirror1 by simp
  thus ?thesis using global_vars_mirror2 by simp
qed

lemma program_var_mirror[simp]:
  assumes "get_var_level_by_name st name = var_level.Program"
  shows "(get_cur_var_init_by_name (set_cur_prog_var st name val) name) = val"
proof -
  from assms have
  "(get_cur_var_init_by_name (set_cur_prog_var st name val) name) =
    (get_prog_var_by_name (get_cur_prog_vars 
    (set_cur_prog_var st name val)) 
    name)" using set_symbvar_program_level_keep by auto
  hence "(get_cur_var_init_by_name (set_cur_prog_var st name val) name) =
          (get_prog_var_by_name (get_cur_prog_vars
          (set_cur_prog_vars st (set_var_in_prog_vars_by_name (get_cur_prog_vars st) name val))) 
          name)" by simp
  hence "(get_cur_var_init_by_name (set_cur_prog_var st name val) name) =
          (get_prog_var_by_name (set_var_in_prog_vars_by_name (get_cur_prog_vars st) name val)
          name)" using prog_vars_mirror1 by simp
  thus ?thesis using prog_vars_mirror2 by simp
qed

lemma process_var_mirror[simp]:
  assumes "get_var_level_by_name st name = var_level.Process"
  shows "(get_cur_var_init_by_name (set_cur_proc_var st name val) name) = val"
proof -
  show ?thesis sorry
qed

lemma symbvar_mirror[simp]:
  shows "get_cur_symbvar_by_name (set_cur_symbvar st name val) name = val"
  
proof (cases "(get_var_level_by_name st name)")
  case g:Global
  hence "get_cur_symbvar_by_name (set_cur_symbvar st name val) name = get_cur_symbvar_by_name (set_global_var st name (stacked_var_init.Symbolic val None)) name" by simp
  from g and this show ?thesis using global_var_mirror by auto
next
  case p:Program
  hence "get_cur_symbvar_by_name (set_cur_symbvar st name val) name = get_cur_symbvar_by_name (set_cur_prog_var st name (stacked_var_init.Symbolic val None)) name" by simp
  from p and this show ?thesis using program_var_mirror by auto
next
  case p:Process
  hence "get_cur_symbvar_by_name (set_cur_symbvar st name val) name = get_cur_symbvar_by_name (set_cur_proc_var st name (stacked_var_init.Symbolic val None)) name" by simp
  from p and this show ?thesis using process_var_mirror by auto
qed


declare [[smt_timeout = 1000]]

lemma
  assumes assms: "st\<turnstile>expr.Const (const.Nat val) \<rightarrow> st_res"
  shows "st_res = (set_value st (const_to_basic (const.Nat val)))"
proof -
  show ?thesis using assms by auto
qed


lemma nat_const_expr[simp]:
  fixes st st_res :: model_context and name :: string and val :: nat
  assumes assms: "st\<turnstile>expr.Const (const.Nat val) \<rightarrow> st_res" 
  shows "(ptype.Nat val) =  (get_value st_res)"
proof -
  from assms have "st_res = (set_value st (const_to_basic (const.Nat val)))" using assms by auto
  hence "get_value st_res = get_value (set_value st (const_to_basic (const.Nat val)))" by simp
  hence "get_value st_res = (const_to_basic (const.Nat val))" using value_mirror by simp
  thus ?thesis by simp 
qed
  
(*st\<turnstile>exp\<rightarrow>st1;
st2 = (set_cur_symbvar st1 var_name (get_value st1))*)

lemma
  fixes st st_res :: model_context and name :: string and val :: nat
  assumes assms: "st\<turnstile>stmt.AssignSt (common_var.Symbolic name) (expr.Const (const.Nat val)) \<longrightarrow> st_res" 
  shows "ptype_eq (get_cur_symbvar_by_name st_res name) (ptype.Nat val)"
proof -
  from assms obtain st1 where
    c1: "st\<turnstile>(expr.Const (const.Nat val))\<rightarrow>st1" and
    c2: "st_res = (set_cur_symbvar st1 name (get_value st1))" 
  by (smt (z3) common_var.distinct(1) common_var.inject(1) exec.simps stmt.distinct(11) stmt.distinct(13) stmt.distinct(15) stmt.distinct(17) stmt.distinct(19) stmt.distinct(3) stmt.distinct(5) stmt.distinct(7) stmt.distinct(9) stmt.inject(1))
  from c1 have "(ptype.Nat val) =  (get_value st1)" by simp
  from c2 and this have "st_res = (set_cur_symbvar st1 name (ptype.Nat val))" by simp
  then have "(get_cur_symbvar_by_name st_res name) = (get_cur_symbvar_by_name (set_cur_symbvar st1 name (ptype.Nat val)) name)" by simp
  then have "(get_cur_symbvar_by_name st_res name) = (ptype.Nat val)" using symbvar_mirror by simp
  then show "?thesis" using basic_eq by simp
qed


end