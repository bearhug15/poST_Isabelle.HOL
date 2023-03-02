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
declare exec_sev_expr.simps [simp]
declare exec_sev_expr.elims [elim]

definition exec_expr :: "expr_stack \<Rightarrow> model_state \<Rightarrow> basic_post_type option" where
 "exec_expr st model_st = nth (exec_sev_expr 1 st model_st) 0"
declare exec_expr_def [simp]

text "Initialization of array"
definition initialize_array :: "model_state \<Rightarrow> stacked_var_init \<Rightarrow> stacked_var_init" where
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
declare initialize_array_def [simp]

text "Initialization of symbolic variable"
definition initialize_symbolic :: "model_state \<Rightarrow> stacked_var_init  \<Rightarrow> stacked_var_init" where
"initialize_symbolic st var= 
  (case var of
    (stacked_var_init.Symbolic value (Some init_stack)) \<Rightarrow> 
      (stacked_var_init.Symbolic (the (exec_expr init_stack st)) None) |
    (stacked_var_init.Symbolic value None) \<Rightarrow> 
      (stacked_var_init.Symbolic value None))"
declare initialize_symbolic_def [simp]

(*TO DO FunctionBlock init*)
text "Initialization of stacked var"
definition initialize_stacked_var :: "model_state \<Rightarrow> stacked_var_init \<Rightarrow> stacked_var_init" where
"initialize_stacked_var st var =
  (case var of
        (stacked_var_init.Symbolic value init_option) \<Rightarrow> (initialize_symbolic st var) |
        (stacked_var_init.Array interval values init_option) \<Rightarrow> (initialize_array st var) |
        (stacked_var_init.FunctionBlock name) \<Rightarrow> (stacked_var_init.FunctionBlock name)) "
declare initialize_stacked_var_def [simp]

text "Initialization of proc_vars"
definition initialize_stacked_proc_vars :: "model_state \<Rightarrow> stacked_proc_vars \<Rightarrow> stacked_proc_vars" where
"initialize_stacked_proc_vars st vars = 
  (fmmap_keys
    (\<lambda>name var. (case var of
                  stacked_proc_var.Var val \<Rightarrow> (stacked_proc_var.Var (initialize_stacked_var st val))
                | stacked_proc_var.ProcessVar val \<Rightarrow> (stacked_proc_var.ProcessVar val)
                | stacked_proc_var.InOutVar val \<Rightarrow> (stacked_proc_var.InOutVar (initialize_stacked_var st val))
                | stacked_proc_var.InVar val \<Rightarrow> (stacked_proc_var.InVar (initialize_stacked_var st val))
                | stacked_proc_var.OutVar val \<Rightarrow> (stacked_proc_var.OutVar (initialize_stacked_var st val)) ))
    vars)"
declare initialize_stacked_proc_vars_def [simp]

text "Initialization of process variables"
definition initialize_process_vars :: "model_state \<Rightarrow> model_state" where
"initialize_process_vars st =
  (case st of (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list) \<Rightarrow>
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
    f_decl_list)))"
declare initialize_process_vars_def [simp]

text "Initialization of prog_vars"
definition initialize_stacked_prog_vars :: "model_state \<Rightarrow> stacked_prog_vars \<Rightarrow> stacked_prog_vars" where
"initialize_stacked_prog_vars st vars = 
  (fmmap
    (\<lambda>var. (case var of
             stacked_prog_var.Var val \<Rightarrow> (stacked_prog_var.Var (initialize_stacked_var st val))
           | stacked_prog_var.ExtVar val \<Rightarrow> (stacked_prog_var.ExtVar (initialize_stacked_var st val))
           | stacked_prog_var.InOutVar val \<Rightarrow> (stacked_prog_var.InOutVar (initialize_stacked_var st val))
           | stacked_prog_var.InVar val \<Rightarrow> (stacked_prog_var.InVar (initialize_stacked_var st val))
           | stacked_prog_var.OutVar val \<Rightarrow> (stacked_prog_var.OutVar (initialize_stacked_var st val)) ))
    vars)"
declare initialize_stacked_prog_vars_def [simp]

text "Initialization of program variables"
definition initialize_program_vars :: "model_state \<Rightarrow> model_state" where
"initialize_program_vars st  =
  (case st of (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list) \<Rightarrow> 
   (let st = (model_state.ST global_vars_list (program_map,cur_prog_name) fb_decl_list f_decl_list)
  in (model_state.ST 
    global_vars_list 
    (fmmap 
       (\<lambda>(var_list,proc_map,proc_name). 
          (initialize_stacked_prog_vars st var_list,proc_map,proc_name)) 
       program_map,
      cur_prog_name) 
    fb_decl_list 
    f_decl_list)))"
declare initialize_program_vars_def [simp]

text "Initialization of global_vars"
definition initialize_stacked_global_vars :: "model_state \<Rightarrow> stacked_global_vars \<Rightarrow> stacked_global_vars" where
"initialize_stacked_global_vars st vars = 
  (fmmap
    (\<lambda>var. (case var of
            stacked_global_var.Var val \<Rightarrow> stacked_global_var.Var (initialize_stacked_var st val)))
    vars)"
declare initialize_stacked_global_vars_def [simp]

definition initialize_global_vars :: "model_state \<Rightarrow> model_state" where
"initialize_global_vars st =
  (case st of (model_state.ST global_vars (program_map,cur_prog_name) fb_decl_list f_decl_list) \<Rightarrow> 
   (model_state.ST 
    (initialize_stacked_global_vars st global_vars) 
    (program_map,cur_prog_name) fb_decl_list f_decl_list))"

text "Extracting new process state from stacked process"
definition extract_process_state :: "stacked_process \<Rightarrow> process_state" where
"extract_process_state sp  = 
  (case sp of 
    (proc_name, var_list,stst_list) \<Rightarrow> 
    (let states = (map (\<lambda>(name,_,_,_). name) stst_list)
      in (var_list, hd states, hd states, states, proc_status.Inactive, (time.Time 0 0 0 0 0))))"
declare extract_process_state_def [simp]

text "Extracting new program state from stacked program"
definition extract_program_state :: "stacked_program \<Rightarrow> program_state" where 
"extract_program_state sp =
  (case sp of
    (prog_name, var_list, st_proc_list) \<Rightarrow>
      (let (name,_,_) = (nth st_proc_list 0);
       proc_states = (fmap_of_list 
                        (map 
                          (\<lambda>(proc_name,var_list,state_list). 
                            (proc_name,(extract_process_state (proc_name,var_list,state_list)))) 
                          st_proc_list))
    in (var_list,proc_states,name)))"
declare extract_program_state_def [simp]

text "Extracting new model state from stacked model"
definition extract_model_state :: "stacked_model \<Rightarrow> model_state" where
"extract_model_state sm =
  (case sm of 
    (conf, global, prog_list, fb_list, f_list) \<Rightarrow>
(let (name, _, _) = (nth prog_list 0);
        prog_map = (fmap_of_list
    (map
      (\<lambda>(name, var_list, proc_list). (name, (extract_program_state (name, var_list, proc_list))))
      prog_list))
  in (model_state.ST global (prog_map,name) fb_list f_list)))"
declare extract_model_state_def [simp]

definition initialize_model_state :: "stacked_model \<Rightarrow> model_state" where
"initialize_model_state smodel = 
  (let new_model = extract_model_state smodel;
      m1 = initialize_global_vars new_model;
      m2 = initialize_program_vars m1;
      m3 = initialize_process_vars m2
    in new_model)"
declare initialize_model_state_def [simp]


end