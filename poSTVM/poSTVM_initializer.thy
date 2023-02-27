theory poSTVM_initializer
  imports poSTVM_state_alt
begin



fun exec_sev_expr :: "nat \<Rightarrow> expr_stack \<Rightarrow> model_state \<Rightarrow> (basic_post_type option) list" where
  "exec_sev_expr 0 _ st = [None]"
| "exec_sev_expr (Suc n) [] st = [None]"
| "exec_sev_expr (Suc n) ((expr_op.Unary unary_op_option)#other) st = 
  (case (unary_op_option,(exec_sev_expr (Suc n) other st)) of
    (None,(first#rest)) \<Rightarrow> (first#rest) 
  | (Some un_op,(first#rest)) \<Rightarrow> ((Some (unary_op_exec un_op (the first)))# rest))"
| "exec_sev_expr (Suc n) ((expr_op.Binary bin_op)#other) st =
  (case (exec_sev_expr (Suc (Suc n)) other st) 
    of (first#second#rest) \<Rightarrow> (Some (binary_op_exec bin_op (the first) (the second)))#rest)"
| "exec_sev_expr (Suc n) ((expr_op.Value val)#other) st = 
    (Some val)#(exec_sev_expr n other st)"
| "exec_sev_expr (Suc n) ((expr_op.Get var_name)#other) st = 
 (Some (get_symbvar_by_name st var_name))#(exec_sev_expr n other st) " 

| "exec_sev_expr (Suc n) ((expr_op.GetArray var_name) #other) st =
  (case (exec_sev_expr (Suc n) other st)
    of (first#rest) \<Rightarrow> (Some (get_arvar_by_name st var_name (the first)))#rest )" 

| "exec_sev_expr (Suc n) ((expr_op.CheckProcStat proc_name proc_stat)#other) st = 
  (Some (check_proc_status st proc_name proc_stat))#(exec_sev_expr n other st)" 
(*TO DO Function Call*)
| "exec_sev_expr (Suc n) ((expr_op.FunctionCall v1 v2)#other) st  =
  None#(exec_sev_expr n other st)" 

fun exec_expr :: "expr_stack \<Rightarrow> model_state \<Rightarrow> basic_post_type option" where
 "exec_expr st model_st = nth (exec_sev_expr 1 st model_st) 0"

text "Initialization of array"
fun initialize_array :: "model_state \<Rightarrow> stacked_var_init \<Rightarrow> stacked_var_init" where
"initialize_array st var= 
  (case var of 
    (stacked_var_init.Array interval values (Some expr_list)) \<Rightarrow> 
      (stacked_var_init.Array
        (case interval of
          (stacked_array_interval.Expr exp1 exp2) \<Rightarrow> 
            (stacked_array_interval.Int (basic_post_type_to_int (the (exec_expr exp1 st))) (basic_post_type_to_int (the (exec_expr exp2 st)))) |
          (stacked_array_interval.Int int1 int2) =>
            (stacked_array_interval.Int int1 int2))
        (map 
          (\<lambda>exp. (the (exec_expr exp st)))
          expr_list)
        None) |
    (stacked_var_init.Array interval values None) \<Rightarrow> 
      (stacked_var_init.Array 
        (case interval of
          (stacked_array_interval.Expr exp1 exp2) \<Rightarrow> 
            (stacked_array_interval.Int (basic_post_type_to_int (the (exec_expr exp1 st))) (basic_post_type_to_int (the (exec_expr exp2 st)))) |
          (stacked_array_interval.Int int1 int2) =>
            (stacked_array_interval.Int int1 int2)) 
        values 
        None))"

text "Initialization of symbolic variable"
fun initialize_symbolic :: "model_state \<Rightarrow> stacked_var_init  \<Rightarrow> stacked_var_init" where
"initialize_symbolic st var= 
  (case var of
    (stacked_var_init.Symbolic value (Some init_stack)) \<Rightarrow> 
      (stacked_var_init.Symbolic (the (exec_expr init_stack st)) None) |
    (stacked_var_init.Symbolic value None) \<Rightarrow> 
      (stacked_var_init.Symbolic value None))"

(*TO DO FunctionBlock init*)
text "Initialization of stacked var"
fun initialize_stacked_vars :: "model_state \<Rightarrow> stacked_vars \<Rightarrow> stacked_vars" where
"initialize_stacked_vars st vars =
  (fmmap
    (\<lambda>init.
      (case init of
        (stacked_var_init.Symbolic value init_option) \<Rightarrow> (initialize_symbolic st init) |
        (stacked_var_init.Array interval values init_option) \<Rightarrow> (initialize_array st init) |
        (stacked_var_init.FunctionBlock name) \<Rightarrow> (stacked_var_init.FunctionBlock name)) )
    vars) "

text "Initialization of proc_vars"
definition initialize_stacked_proc_vars :: "model_state \<Rightarrow> stacked_proc_vars \<Rightarrow> stacked_proc_vars" where
"initialize_stacked_proc_vars st (proc_var#other) = 
  ((case proc_var of
    (stacked_proc_var.Var stacked_vars) \<Rightarrow> (stacked_proc_var.Var (initialize_stacked_vars st stacked_vars))|
    (stacked_proc_var.ProcessVar var) \<Rightarrow> (stacked_proc_var.ProcessVar var)|
    (stacked_proc_var.InOutVar stacked_vars) \<Rightarrow> (stacked_proc_var.InOutVar (initialize_stacked_vars st stacked_vars)) |
    (stacked_proc_var.InVar stacked_vars) \<Rightarrow> (stacked_proc_var.InVar (initialize_stacked_vars st stacked_vars))|
    (stacked_proc_var.OutVar stacked_vars) \<Rightarrow> (stacked_proc_var.OutVar (initialize_stacked_vars st stacked_vars)))
  #(initialize_stacked_proc_vars st other))"

(*TO DO*)
text "Initialization of process variables"
fun initialize_process_vars :: "model_state \<Rightarrow> model_state" where
"initialize_process_vars (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list) =
  (let st = (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list) 
  in  (model_state.ST 
    global_vars_list 
    (fmmap 
       (\<lambda>(var_list,proc_map,proc_name). 
          (var_list,
            (fmmap 
              (\<lambda>(var_list,v1,v2,v3,v4).
                (initialize_stacked_proc_vars st var_list,v1,v2,v3,v4))
              proc_map),
          proc_name)) 
       program_map,
      cur_prog_name) 
    fb_decl_list 
    f_decl_list))"

text "Initialization of prog_vars"
fun initialize_stacked_prog_vars :: "model_state \<Rightarrow> stacked_prog_var list \<Rightarrow> stacked_prog_var list" where
"initialize_stacked_prog_vars _ [] = []" |
"initialize_stacked_prog_vars st (prog_var#other) = 
  ((case prog_var of
    (stacked_prog_var.ExtVar stacked_vars) \<Rightarrow> (stacked_prog_var.ExtVar (initialize_stacked_vars st stacked_vars))|
    (stacked_prog_var.Var stacked_vars) \<Rightarrow> (stacked_prog_var.Var (initialize_stacked_vars st stacked_vars))|
    (stacked_prog_var.InOutVar stacked_vars) \<Rightarrow> (stacked_prog_var.InOutVar (initialize_stacked_vars st stacked_vars))|
    (stacked_prog_var.InVar stacked_vars) \<Rightarrow> (stacked_prog_var.InVar (initialize_stacked_vars st stacked_vars))|
    (stacked_prog_var.OutVar stacked_vars) \<Rightarrow> (stacked_prog_var.OutVar (initialize_stacked_vars st stacked_vars)))
   #(initialize_stacked_prog_vars st other))"

(*TO DO*)
text "Initialization of program variables"
fun initialize_program_vars :: "model_state \<Rightarrow> model_state" where
"initialize_program_vars (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list) =
  (let st = (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list)
  in (model_state.ST 
    global_vars_list 
    (fmmap 
       (\<lambda>(var_list,proc_map,proc_name). 
          (initialize_stacked_prog_vars st var_list,proc_map,proc_name)) 
       program_map,
      cur_prog_name) 
    fb_decl_list 
    f_decl_list))"

end