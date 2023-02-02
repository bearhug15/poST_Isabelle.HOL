theory poSTVM_alt_inductive
  imports 
    "~~/poST/poSTVM/poSTVM_state_alt" 
begin
datatype statement_result = Break | Continue | Exit | Return | Reset | NextState

text "Executing unary operation"
definition unary_op_exec :: "unary_op => basic_post_type \<Rightarrow> basic_post_type" where
"unary_op_exec op var = (case op of unary_op.Not \<Rightarrow> (basic_post_type_not var) | unary_op.Minus \<Rightarrow> (basic_post_type_minus var))"

text "Executing binary operation"
definition binary_op_exec :: "binary_op \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
"binary_op_exec op var1 var2 = 
  (case op of 
    binary_op.And \<Rightarrow> basic_post_type.Bool(basic_post_type_and var1 var2)|
 binary_op.Or \<Rightarrow> basic_post_type.Bool(basic_post_type_or var1 var2)|
    binary_op.Xor \<Rightarrow> basic_post_type.Bool(basic_post_type_xor var1 var2) | 
    binary_op.Eq \<Rightarrow> basic_post_type.Bool(basic_post_type_or var1 var2)| 
    binary_op.NotEq \<Rightarrow>basic_post_type.Bool(basic_post_type_noteq var1 var2)| 
    binary_op.Less \<Rightarrow>basic_post_type.Bool(basic_post_type_less var1 var2)| 
    binary_op.More \<Rightarrow>basic_post_type.Bool(basic_post_type_more var1 var2)| 
    binary_op.LessEq \<Rightarrow>basic_post_type.Bool(basic_post_type_lesseq var1 var2)| 
    binary_op.MoreEq \<Rightarrow>basic_post_type.Bool(basic_post_type_moreeq var1 var2)| 
    binary_op.Sum \<Rightarrow> basic_post_type_sum var1 var2| 
    binary_op.Sub \<Rightarrow> basic_post_type_sub var1 var2| 
    binary_op.Mul \<Rightarrow> basic_post_type_mul var1 var2| 
    binary_op.Div \<Rightarrow> basic_post_type_div var1 var2| 
    binary_op.Mod \<Rightarrow> basic_post_type_mod var1 var2)"

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

value "butlast [1::nat,2,3,4]" 

fun case_list_to_if :: "expr \<Rightarrow> case_list \<Rightarrow> expr" where
  "case_list_to_if _ [] = expr.Const (const.Bool False)"
| "case_list_to_if exp [val] = expr.Binary binary_op.Eq exp (expr.Const (const.Nat val))"
| "case_list_to_if exp (val#other) = 
    expr.Binary binary_op.Or
      (expr.Binary binary_op.Eq exp (expr.Const (const.Nat val)))
      (case_list_to_if exp other)"



function (sequential) statement_to_stmt :: "statement \<Rightarrow> stmt" and
        st_list_to_stmt :: "statement list \<Rightarrow> stmt" and
        if_to_stmt :: "(expr * statement_list) list \<Rightarrow> statement_list option \<Rightarrow> stmt" and
        case_to_stmt :: "expr \<Rightarrow> (case_list *(statement list)) list \<Rightarrow> statement_list option \<Rightarrow> stmt"where
  "statement_to_stmt (statement.AssignSt st) = stmt.AssignSt st"
| "statement_to_stmt (statement.FBInvocation fb) = stmt.FBInvocation fb"
| "statement_to_stmt (statement.Return) = stmt.Return"
| "statement_to_stmt (statement.Exit) = stmt.Exit"
| "statement_to_stmt (statement.ProcessSt st) = stmt.ProcessSt st"
| "statement_to_stmt (statement.SetStateSt st) = stmt.SetStateSt st"
| "statement_to_stmt (statement.ResetSt) = stmt.ResetSt"
| "statement_to_stmt (statement.SelectSt (select_statement.IfSt branches else_option)) =(if_to_stmt branches else_option)"
| "statement_to_stmt (statement.SelectSt (select_statement.CaseSt exp cases_list else_option)) =(case_to_stmt exp cases_list else_option)"
| "st_list_to_stmt [] = stmt.Blank"
| "st_list_to_stmt (st#other) = stmt.Comb (statement_to_stmt st) (st_list_to_stmt other)"
| "if_to_stmt [] else_option= 
    (case else_option of
      None \<Rightarrow> stmt.Blank
    | Some st_list\<Rightarrow> st_list_to_stmt st_list)"
| "if_to_stmt (branch#other) else_option =
    (case branch of (exp,st_list) \<Rightarrow> 
      stmt.IfSt exp 
        (st_list_to_stmt st_list) 
        (if_to_stmt other else_option))"
| "case_to_stmt exp [] else_option = 
    (case else_option of
      None \<Rightarrow> stmt.Blank
    | Some st_list\<Rightarrow> st_list_to_stmt st_list)"
| "case_to_stmt exp (cas#other) else_option = 
    (case cas of (val_list,st_list) \<Rightarrow>
      stmt.IfSt 
        (case_list_to_if exp val_list)
        (st_list_to_stmt st_list)
        (case_to_stmt exp other else_option))"
| "statement_to_stmt (statement.IterSt (iter_statement.WhileSt exp st_list)) =
    stmt.WhileSt exp (st_list_to_stmt st_list)"
| "statement_to_stmt (statement.IterSt (iter_statement.RepeatSt st_list exp)) =
    (let body = (st_list_to_stmt st_list) 
      in stmt.Comb body (stmt.WhileSt exp body))"
| "statement_to_stmt (statement.IterSt (iter_statement.ForSt var_name (start,end,step_option) st_list)) =
    stmt.Comb 
      (stmt.AssignSt (common_var.Symbolic var_name,start))
      (let cond = expr.Binary binary_op.Less (expr.SymbolicVar var_name) end;
           body = (st_list_to_stmt st_list);
           step_st = stmt.AssignSt 
                      (common_var.Symbolic var_name, 
                        expr.Binary binary_op.Sum
                          (expr.SymbolicVar var_name) 
                          (case step_option of
                            None \<Rightarrow> expr.Const (const.Nat 1)
                          | Some step \<Rightarrow> step));
           new_body = stmt.Comb body step_st
        in stmt.WhileSt cond new_body)"
  by pat_completeness auto
termination by size_change


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
    XcptE : "st\<turnstile>exp\<rightarrow>undefined"
  | BinOp : "\<lbrakk>st\<turnstile>exp1\<rightarrow>val1;
              st\<turnstile>exp2\<rightarrow>val2;
              val = binary_op_exec bin_op val1 val2 \<rbrakk> \<Longrightarrow>
             st\<turnstile>expr.Binary bin_op exp1 exp2\<rightarrow>val"
  | UnaryOp : "\<lbrakk>st\<turnstile>pexp\<rightarrow>val1;
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

end