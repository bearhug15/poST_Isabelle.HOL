theory poSTVM_alt_inductive
  imports 
    "~~/poST/poSTVM/poSTVM_state_alt" 
begin
datatype statement_result =  Continue | Exit | Return | NextState



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

type_synonym exec_res = "statement_result * model_state"

inductive 
  eval :: "[model_state, expr, basic_post_type] \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _") and
  exec :: "[statement_result * model_state,stmt,statement_result * model_state] \<Rightarrow> bool" ("_ \<turnstile> _ \<longrightarrow> _")
  where
    XcptE : "st\<turnstile>exp\<rightarrow>val"
  | BinOp : "\<lbrakk>st\<turnstile>exp1\<rightarrow>val1;
              st\<turnstile>exp2\<rightarrow>val2;
              val = binary_op_exec bin_op val1 val2 \<rbrakk> \<Longrightarrow>
             st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>val"
  | UnOp : "\<lbrakk>st\<turnstile>pexp\<rightarrow>val1;
                val = (case un_op of
                        None \<Rightarrow> val1
                      | Some un_op \<Rightarrow> unary_op_exec un_op val1)\<rbrakk> \<Longrightarrow>
               st\<turnstile> expr.Unary un_op pexp\<rightarrow>val"
  | Const : "\<lbrakk>val = const_to_basic c\<rbrakk>\<Longrightarrow>
            st\<turnstile>expr.Const c\<rightarrow>val"
  | Var :  "\<lbrakk>val = get_symbvar_by_name st var_name\<rbrakk>\<Longrightarrow>
           st\<turnstile>expr.SymbolicVar var_name\<rightarrow>val"
  | ArrayVar : "\<lbrakk>st\<turnstile>exp\<rightarrow>pos;
                 val = get_arvar_by_name st var_name pos\<rbrakk>\<Longrightarrow>
               st\<turnstile>expr.ArrayVar var_name exp\<rightarrow>val"
  | PSE : "\<lbrakk>val = check_proc_status st p_name p_status\<rbrakk>\<Longrightarrow>
          st\<turnstile>expr.ProcStatEpxr p_name p_status\<rightarrow>val "

  | XcptS : "st\<turnstile>s\<longrightarrow>st "
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
              st\<turnstile>s\<longrightarrow>st1;st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2\<rbrakk>\<Longrightarrow>
            st\<turnstile>stmt.WhileSt exp s\<longrightarrow>st2"
  | AssignS : "\<lbrakk>(snd st)\<turnstile>exp\<rightarrow>val;
                st1 = (set_symbvar (snd st) var_name val)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Symbolic var_name, exp)\<longrightarrow>(statement_result.Continue, st1)"
  | AssignA : "\<lbrakk>(snd st)\<turnstile>exp\<rightarrow>val1;
                (snd st)\<turnstile>pos\<rightarrow>val2;
                st1 = (set_arvar (snd st) var_name val2 val1)\<rbrakk>\<Longrightarrow>
              st\<turnstile>stmt.AssignSt (common_var.Array var_name pos, exp)\<longrightarrow>(statement_result.Continue, st1)"
  | Return : "st\<turnstile>stmt.Return\<longrightarrow>(statement_result.Return, snd st)"
  | Exit : "st\<turnstile>stmt.Exit\<longrightarrow>(statement_result.Exit, snd st)"
  | Process : "\<lbrakk>st2 = (case ps of
                          process_statement.Start name_option \<Rightarrow> 
                            (case name_option of
                              None \<Rightarrow> (statement_result.Return, reset_same_process (snd st))
                            | Some name \<Rightarrow> (statement_result.Continue, reset_process (snd st) name))
                        | process_statement.Stop name_option \<Rightarrow> 
                            (case name_option of
                              None \<Rightarrow> (statement_result.Return, stop_same_process (snd st))
                            | Some name \<Rightarrow> (statement_result.Continue, stop_process (snd st) name))
                        | process_statement.Error name_option \<Rightarrow> 
                            (case name_option of
                              None \<Rightarrow> (statement_result.Return, error_same_process (snd st))
                            | Some name \<Rightarrow> (statement_result.Continue, error_process (snd st) name)))\<rbrakk>\<Longrightarrow>
                st\<turnstile>stmt.ProcessSt ps\<longrightarrow>st2"
  | SetState : "\<lbrakk>st = (case st_name_option of
                        None \<Rightarrow> (statement_result.NextState, (snd st))
                      | Some name \<Rightarrow> (statement_result.Return, set_state (snd st) name))\<rbrakk>\<Longrightarrow>
                st\<turnstile>stmt.SetStateSt st_name_option\<longrightarrow>st2"
  | Reset : "\<lbrakk>st2 = (statement_result.Continue, (reset_timer (snd st)))\<rbrakk>\<Longrightarrow>
            st\<turnstile>stmt.ResetSt\<longrightarrow>st2"

print_theorems

inductive eval_state :: "[model_state,stacked_state,statement_result * model_state] \<Rightarrow> bool" ("_ \<turnstile> _ : _") where
    XcptState : "st\<turnstile>state:(res,st)"   
  | Base : "\<lbrakk>(statement_result.Continue,st)\<turnstile>stm\<longrightarrow>(res,st1)\<rbrakk> \<Longrightarrow> st \<turnstile>(name,looped,stm,timeout_op):(res,st1)"


(*
apply (simp add: const_to_basic_def
set_symbvar_def
get_cur_var_by_name_def
set_symbvar_in_ps_in_cur_prog_def
get_var_by_name.simps
get_cur_var_list_def
get_cur_proc_var_list_def
find_var_by_name_def
get_cur_var_by_name_def
get_var_by_name.simps
get_cur_proc_state_by_prog_def)
*)
end