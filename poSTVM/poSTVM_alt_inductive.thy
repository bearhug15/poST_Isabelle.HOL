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
  eval :: "[model_context, expr, model_context * basic_post_type] \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _") and
  exec :: "[model_context,stmt,model_context] \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow> _") and
  exec_func :: "[model_context,func_name,func_params,model_context*basic_post_type] \<Rightarrow> bool" ("_\<turnstile>_,_\<longrightarrow> _") and
  assign_param :: "[model_context,assign_type,param_assign list,model_context,model_context] \<Rightarrow> bool"
  where
    BinOp : "\<lbrakk>st\<turnstile>exp1\<rightarrow>(st1,val1);
              st1\<turnstile>exp2\<rightarrow>(st2,val2);
              val = binary_op_exec bin_op val1 val2 \<rbrakk> \<Longrightarrow>
             st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>(st2,val)"
  | UnOp : "\<lbrakk>st\<turnstile>pexp\<rightarrow>(st1,val1);
                val = (unary_op_exec un_op val1)\<rbrakk> \<Longrightarrow>
               st\<turnstile> expr.Unary un_op pexp\<rightarrow>(st1,val)"
  | Const : "\<lbrakk>val = const_to_basic c\<rbrakk>\<Longrightarrow>
            st\<turnstile>expr.Const c\<rightarrow>(st,val)"
  | Var :  "\<lbrakk>val = get_cur_symbvar_by_name st var_name\<rbrakk>\<Longrightarrow>
           st\<turnstile>expr.SymbolicVar var_name\<rightarrow>(st,val)"
  | ArrayVar : "\<lbrakk>st\<turnstile>exp\<rightarrow>(_,pos);
                 val = get_cur_arvar_by_name_by_pos st var_name pos\<rbrakk>\<Longrightarrow>
               st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>(st,val)"
  | PSE : "\<lbrakk>val = check_proc_status st p_name p_status\<rbrakk>\<Longrightarrow>
          st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>(st,val)"
 |FuncCall : "\<lbrakk>st\<turnstile>name,as_list\<longrightarrow>(st1,val)\<rbrakk> \<Longrightarrow> st\<turnstile>expr.FunctionCall name as_list \<rightarrow> (st1,val)"

  | Blank : "st\<turnstile>stmt.Blank\<longrightarrow>st"
  | Comb : "\<lbrakk>st\<turnstile>s1\<longrightarrow>st1;
             st1\<turnstile>s2\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
           st\<turnstile>stmt.Comb s1 s2 \<longrightarrow>st2"
  | IfT : "\<lbrakk>st\<turnstile>exp\<rightarrow>(st_res,val);
            (basic_post_type_to_bool val);
            st\<turnstile>s1\<longrightarrow>st1\<rbrakk>\<Longrightarrow>
         st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st1"
  | IfF : "\<lbrakk>st\<turnstile>exp\<rightarrow>(st_res,val);
           \<not>(basic_post_type_to_bool val);
           st\<turnstile>s2\<longrightarrow>st1\<rbrakk> \<Longrightarrow> st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st1"
  | LoopF : "\<lbrakk>st\<turnstile>exp\<rightarrow>(st_sub,val); \<not>(basic_post_type_to_bool val)\<rbrakk>\<Longrightarrow>
            st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st"
  | LoopT : "\<lbrakk>st\<turnstile>exp\<rightarrow>(st_sub,val); (basic_post_type_to_bool val);
              st\<turnstile>s\<longrightarrow>st1;st1\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2"
  | AssignS : "\<lbrakk>st\<turnstile>exp\<rightarrow>(st1,val);
                st2 = (set_symbvar st1 var_name val)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Symbolic var_name) exp\<longrightarrow>st2"
  | AssignA : "\<lbrakk>st\<turnstile>exp\<rightarrow>(st1,val1);
                st1\<turnstile>pos\<rightarrow>(st1,val2);
                st2 = (set_arvar st1 var_name val2 val1)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Array var_name pos) exp\<longrightarrow>st2"
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
                st\<turnstile>name,params\<longrightarrow>(new_st,res)"
  | AssignPNill : "assign_param base_st type [] st st"
  | AssignPConsCol : "\<lbrakk>base_st \<turnstile> exp \<rightarrow> (st,val);
                       (if as_type = assign_type.ColonEq 
                        then (assign_param base_st assign_type.ColonEq other (set_symbvar st name val) new_st)
                        else (assign_param base_st assign_type.ColonEq other st new_st))\<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.ColonEq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"
  | AssignPConsCon : "\<lbrakk>base_st \<turnstile> exp \<rightarrow> (st,val);
                       (if as_type = assign_type.Conseq 
                        then (assign_param base_st assign_type.Conseq other st new_st) 
                        else (assign_param base_st assign_type.Conseq other (set_symbvar st name val) new_st))  \<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.Conseq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"

print_theorems 

text "eval code_pred_intro lemmas"
lemma [code_pred_intro]: 
"\<lbrakk>st\<turnstile>exp1\<rightarrow>(st1,val1);
              st1\<turnstile>exp2\<rightarrow>(st2,val2);
              val = binary_op_exec bin_op val1 val2 \<rbrakk> \<Longrightarrow>
             st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>(st2,val)"
"\<lbrakk>st\<turnstile>pexp\<rightarrow>(st1,val1);
                val = (unary_op_exec un_op val1)\<rbrakk> \<Longrightarrow>
               st\<turnstile> expr.Unary un_op pexp\<rightarrow>(st1,val)"
"\<lbrakk>val = const_to_basic c\<rbrakk>\<Longrightarrow>
            st\<turnstile>expr.Const c\<rightarrow>(st,val)"
"\<lbrakk>val = get_cur_symbvar_by_name st var_name\<rbrakk>\<Longrightarrow>
           st\<turnstile>expr.SymbolicVar var_name\<rightarrow>(st,val)"
"\<lbrakk>st\<turnstile>exp\<rightarrow>(st1,pos);
                 val = get_cur_arvar_by_name_by_pos st var_name pos\<rbrakk>\<Longrightarrow>
               st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>(st,val)"
"\<lbrakk>val = check_proc_status st p_name p_status\<rbrakk>\<Longrightarrow>
          st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>(st,val)"
"\<lbrakk>st\<turnstile>name,as_list\<longrightarrow>(st1,val)\<rbrakk> \<Longrightarrow> st\<turnstile>expr.FunctionCall name as_list \<rightarrow> (st1,val)"
  by (auto intro: eval_exec_exec_func_assign_param.intros)

inductive_cases BinOpE[elim!]: "st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>(st2,val)"
inductive_cases UnOpE[elim!]: "st\<turnstile> expr.Unary un_op pexp\<rightarrow>(st1,val)"
inductive_cases ConstE[elim!]: "st\<turnstile>expr.Const c\<rightarrow>(st,val)"
inductive_cases VarE[elim!]: "st\<turnstile>expr.SymbolicVar var_name\<rightarrow>(st,val)"
inductive_cases ArrayVarE[elim!]: "st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>(st,val)"
inductive_cases PSE[elim!]: "st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>(st,val)"
inductive_cases FuncCallE[elim!]: "st\<turnstile>expr.FunctionCall name as_list \<rightarrow> (st1,val)"

text "exec code_pred_intro lemmas"
lemma [code_pred_intro]:
"st\<turnstile>stmt.Blank\<longrightarrow>st"
"\<lbrakk>st\<turnstile>s1\<longrightarrow>st1;
             st1\<turnstile>s2\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
           st\<turnstile>stmt.Comb s1 s2 \<longrightarrow>st2"
"\<lbrakk>st\<turnstile>exp\<rightarrow>(st_res,val);
            (basic_post_type_to_bool val);
            st\<turnstile>s1\<longrightarrow>st1\<rbrakk>\<Longrightarrow>
         st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st1"
"\<lbrakk>st\<turnstile>exp\<rightarrow>(st_res,val);
           \<not>(basic_post_type_to_bool val);
           st\<turnstile>s2\<longrightarrow>st1\<rbrakk> \<Longrightarrow> st\<turnstile>stmt.IfSt exp s1 s2\<longrightarrow>st1"
"\<lbrakk>st\<turnstile>exp\<rightarrow>(st1,val); \<not>(basic_post_type_to_bool val)\<rbrakk>\<Longrightarrow>
            st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st"
"\<lbrakk>st\<turnstile>exp\<rightarrow>(st1,val); (basic_post_type_to_bool val);
              st\<turnstile>s\<longrightarrow>st1;st1\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2"
"\<lbrakk>st\<turnstile>exp\<rightarrow>(st1,val);
                st2 = (set_symbvar st1 var_name val)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Symbolic var_name) exp\<longrightarrow>st2"
"\<lbrakk>st\<turnstile>exp\<rightarrow>(st1,val1);
                st1\<turnstile>pos\<rightarrow>(st1,val2);
                st2 = (set_arvar st1 var_name val2 val1)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Array var_name pos) exp\<longrightarrow>st2"
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
inductive_cases AssignE[elim!]: "st\<turnstile>stmt.AssignSt v exp\<longrightarrow>st2"
inductive_cases ReturnE[elim!]: "st\<turnstile>stmt.Return\<longrightarrow>st"
inductive_cases ExitE[elim!]: "st\<turnstile>stmt.Exit\<longrightarrow>st"
inductive_cases ProcessE[elim!]: "st\<turnstile>stmt.ProcessSt p\<longrightarrow>st1"
inductive_cases SetStateE[elim!]: "st\<turnstile>stmt.SetStateSt st_name_option\<longrightarrow>st1"
inductive_cases ResetE[elim!]: "st\<turnstile>stmt.ResetSt\<longrightarrow>st1"

text "exec_func code_pred_intro lemmas"
lemma [code_pred_intro]:
"\<lbrakk>(f_name,res,vars,stmts) = (get_func_by_name st name);
                  proxy_state = (gen_proxy_for_func st (f_name,res,vars,stmts));
                  assign_param st assign_type.ColonEq params proxy_state as_proxy_state;
                  as_proxy_state\<turnstile>stmts\<longrightarrow>st1;
                  assign_param st1 assign_type.Conseq params st new_st;
                  res = (get_cur_symbvar_by_name st1 f_name)\<rbrakk>\<Longrightarrow>
                st\<turnstile>name,params\<longrightarrow>(new_st,res)"
  by (auto intro: eval_exec_exec_func_assign_param.FuncStep)

inductive_cases FuncE[elim!]:"st\<turnstile>name,params\<longrightarrow>(new_st,res)"

text "param_assign code_pred_intro lemmas"
lemma [code_pred_intro]:
"assign_param base_st type [] st st"
"\<lbrakk>base_st \<turnstile> exp \<rightarrow> (st,val);
                       (if as_type = assign_type.ColonEq 
                        then (assign_param base_st assign_type.ColonEq other (set_symbvar st name val) new_st)
                        else (assign_param base_st assign_type.ColonEq other st new_st))\<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.ColonEq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"
"\<lbrakk>base_st \<turnstile> exp \<rightarrow> (st,val);
                       (if as_type = assign_type.Conseq 
                        then (assign_param base_st assign_type.Conseq other st new_st) 
                        else (assign_param base_st assign_type.Conseq other (set_symbvar st name val) new_st))  \<rbrakk> \<Longrightarrow> 
                      assign_param base_st assign_type.Conseq ((param_assign.SymbolicVar name as_type exp)#other) st new_st"
  by (auto intro: eval_exec_exec_func_assign_param.intros)

inductive_cases AssignPE[elim!]: "assign_param base_st at pa st new_st"

inductive 
  eval_state :: "[model_context,stacked_state,statement_result * model_context] \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
    StateStep : "\<lbrakk>st\<turnstile>stm\<longrightarrow>st1;
                  (case timeout_op of
                    None \<Rightarrow> (res,st2) = (res,st1)
                    | (Some timeout) \<Rightarrow> 
                      (case (extr_timeout_stmt st1 timeout) of 
                        None \<Rightarrow> (res,st2) = (res,st1)
                        | (Some stm1) \<Rightarrow> (st1\<turnstile>stm1\<longrightarrow>st2)))\<rbrakk> \<Longrightarrow> 
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

lemma
"st\<turnstile>stmt.IfSt b stmt.Blank stmt.Blank \<longrightarrow> st1 \<Longrightarrow> st =st1"
  by blast
  

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
(*
code_pred (expected_modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o)exec_func
proof - 
  case exec_func
  from exec_func.prems show thesis
  proof (cases)
    case (FuncStep f_name vars stmts proxy_state as_proxy_state st1)
    then show ?thesis by (simp add: exec_func.that(1))
  qed
qed

code_pred (expected_modes: i \<Rightarrow> i \<Rightarrow> o)eval
proof -
  case eval
  from eval.prems show thesis
  proof (cases)
    case (BinOp exp1 st1 val1 exp2 val2 bin_op)
    from BinOp show thesis by (simp add: eval.that(1))
  next
    case (UnOp pexp val1 un_op)
    from UnOp show thesis by (simp add: eval.that(2))
  next
    case (Const c)
    from Const show thesis by (simp add: eval.that(3))
  next
    case (Var var_name)
    from Var show thesis by (simp add: eval.that(4))
  next
    case (PSE p_name p_status)
    from PSE show thesis by (simp add: eval.that(6))
  next
    case (FuncCall name as_list)
    from FuncCall show thesis by (simp add: eval.that(7))
  next
    case (ArrayVar exp uu pos var_name)
    from ArrayVar  show thesis by (auto simp add: eval.that(5))
  qed
  case exec_func
  from exec_func.prems show thesis
  proof (cases)
    case (FuncStep f_name vars stmts proxy_state as_proxy_state st1)
    then show ?thesis by (simp add: exec_func.that(1))
  qed
  
qed
  *)
  

(*
proof -
  case exec
  from this show thesis by (smt (verit) exec.cases)
qed
*)


end