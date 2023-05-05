theory poSTVM_state_alt
  imports 
    "~~/poST/poST_model/poST_model"
    "~~/poST/poST_utils/poST_vars_utils"
    "~~/poST/poSTVM/poSTVM_parser_alt"
begin 

type_synonym current_time = "time"

text "Process state in form of process vars list, current state, next_state, list of states, process status, process time"
type_synonym process_context = "stacked_proc_vars * 
                              state_name * 
                              state_name * 
                              (state_name list) * 
                              proc_status * 
                              current_time"

text "Program state in form of program vars list, processes map, current process"
type_synonym program_context ="stacked_prog_vars * 
                             ((process_name,process_context) fmap) * 
                             process_name"

text "Model state in form of global vars, programs map, current program, function blocks list, functions list"
datatype model_context = ST 
                       stacked_global_vars  
                       "(program_name,program_context) fmap" 
                       program_name 
                       stacked_func_blocks  
                       stacked_funcs

datatype var_level = Global | Program | Process

text "Getting var init from process vars by name"
definition get_proc_var_by_name :: "stacked_proc_vars \<Rightarrow>  symbolic_var \<Rightarrow>  stacked_var_init option" where
  "get_proc_var_by_name vars name =
    (case the (fmlookup vars name) of
      (stacked_proc_var.Var var) \<Rightarrow> Some var
    | (stacked_proc_var.InOutVar var) \<Rightarrow> Some var
    | (stacked_proc_var.InVar var) \<Rightarrow> Some var
    | (stacked_proc_var.OutVar var) \<Rightarrow> Some var
    | (stacked_proc_var.ProcessVar var) \<Rightarrow> None)"
declare get_proc_var_by_name_def [simp]

text "Getting var init from program vars by name"
definition get_prog_var_by_name :: "stacked_prog_vars \<Rightarrow>  symbolic_var \<Rightarrow>  stacked_var_init option" where
  "get_prog_var_by_name vars name =
    (case the (fmlookup vars name) of
      (stacked_prog_var.Var var) \<Rightarrow> Some var
    | (stacked_prog_var.InOutVar var) \<Rightarrow> Some var
    | (stacked_prog_var.InVar var) \<Rightarrow> Some var
    | (stacked_prog_var.OutVar var) \<Rightarrow> Some var
    | (stacked_prog_var.ExtVar var) \<Rightarrow>Some var)"
declare get_prog_var_by_name_def [simp]

text "Getting var init from global vars by name"
definition get_global_var_by_name :: "stacked_global_vars \<Rightarrow>  symbolic_var \<Rightarrow>  stacked_var_init option" where
  "get_global_var_by_name vars name =
    (case the (fmlookup vars name) of
      (stacked_global_var.Var var) \<Rightarrow> Some var
    | (stacked_global_var.Global _ var) \<Rightarrow> None)"
declare get_global_var_by_name_def [simp]

print_theorems

text "Getting current process state from program state"
definition get_cur_procst_from_progst :: "program_context \<Rightarrow> process_context" where
"get_cur_procst_from_progst ps = (case (fmlookup (fst (snd ps)) (snd (snd ps))) of Some (st) \<Rightarrow> st)"
declare get_cur_procst_from_progst_def [simp]

definition get_procst_from_progst_by_name :: "program_context \<Rightarrow> process_name \<Rightarrow> process_context" where
"get_procst_from_progst_by_name pg pc_name = 
  (let (_,pc_map,_) = pg in (case (fmlookup pc_map pc_name) of Some st \<Rightarrow> st))"
declare get_procst_from_progst_by_name_def [simp]

text "Getting process vars list in current process from program state"
definition get_cur_proc_vars_from_progst :: "program_context \<Rightarrow>stacked_proc_vars" where 
  "get_cur_proc_vars_from_progst ps_state = 
    (let (proc_var_list,st_name,proc_stat,cur_time) = get_cur_procst_from_progst ps_state in
      proc_var_list)"
declare get_cur_proc_vars_from_progst_def [simp]

text "Getting current program state from model state"
definition get_cur_progst :: "model_context \<Rightarrow> program_context" where
"get_cur_progst st = 
  (case st of 
    (ST global_var_decl_list ps_map p_name function_block_decl_list function_decl_list) \<Rightarrow>
      (case (fmlookup ps_map p_name) of 
        Some(p_state) \<Rightarrow> p_state))"
declare get_cur_progst_def [simp]

text "Getting current process state name"
definition get_cur_proc_state_name :: "model_context \<Rightarrow> state_name" where
"get_cur_proc_state_name st = fst (snd (get_cur_procst_from_progst (get_cur_progst st)))"
declare get_cur_proc_state_name_def [simp]

text "Getting process state by process name from model state" 
definition get_procst_by_name :: "model_context \<Rightarrow> process_name \<Rightarrow> process_context" where 
"get_procst_by_name st var_name =
  get_procst_from_progst_by_name (get_cur_progst st) var_name"
declare get_procst_by_name_def [simp]

text "Get vars of current process from model state"
definition get_cur_proc_vars :: "model_context \<Rightarrow> stacked_proc_vars" where
"get_cur_proc_vars st = get_cur_proc_vars_from_progst (get_cur_progst st)"
declare get_cur_proc_vars_def [simp]

text "Get vars of current program from model state"
definition get_cur_prog_vars :: "model_context \<Rightarrow> stacked_prog_vars" where
"get_cur_prog_vars st = (let (vars,_,_) = (get_cur_progst st) in vars)"
declare get_cur_prog_vars_def [simp]

text "Get global vars"
definition get_global_vars :: "model_context \<Rightarrow> stacked_global_vars" where
"get_global_vars st = (case st of (ST vars _ _ _ _) \<Rightarrow> vars)"
declare get_global_vars_def [simp]

text "Getting level of var by name for setting purpose"
definition get_var_level_by_name_for_set :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> var_level" where
"get_var_level_by_name_for_set st var_name =
  (case (fmlookup (get_global_vars st) var_name) of
    Some _ \<Rightarrow> var_level.Global
  | None \<Rightarrow> (case (fmlookup (get_cur_prog_vars st) var_name) of
              Some _ \<Rightarrow> var_level.Program
            | None \<Rightarrow> (case (fmlookup (get_cur_proc_vars st) var_name) of
                        Some _ \<Rightarrow> var_level.Process)))"
declare get_var_level_by_name_for_set_def [simp]

text "Getting level of var by name for getting purpose"
definition get_var_level_by_name_for_get :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> var_level" where
"get_var_level_by_name_for_get st var_name =
  (case (fmlookup (get_global_vars st) var_name) of
    Some _ \<Rightarrow> var_level.Global
  | None \<Rightarrow> (case (fmlookup (get_cur_prog_vars st) var_name) of
              Some _ \<Rightarrow> var_level.Program
            | None \<Rightarrow> (case (fmlookup (get_cur_proc_vars st) var_name) of
                        Some _ \<Rightarrow> var_level.Process)))"
declare get_var_level_by_name_for_get_def [simp]

text "Getting variable init by name from model state"
definition get_cur_var_init_by_name :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init" where
"get_cur_var_init_by_name st var_name = 
  (case (get_var_level_by_name_for_get st var_name) of
    var_level.Global \<Rightarrow> the (get_global_var_by_name (get_global_vars st) var_name)
  | var_level.Program \<Rightarrow> the (get_prog_var_by_name (get_cur_prog_vars st) var_name)
  | var_level.Process \<Rightarrow> the (get_proc_var_by_name (get_cur_proc_vars st) var_name))"
declare get_cur_var_init_by_name_def [simp]

text "Getting symbolic variable value by name from model state"
definition get_cur_symbvar_by_name :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type" where
"get_cur_symbvar_by_name st var_name = 
  (case (get_cur_var_init_by_name st var_name) of
    (stacked_var_init.Symbolic val opt) \<Rightarrow> val)"
declare get_cur_symbvar_by_name_def [simp]

text "Getting value from list of values by basic_post_type position"
definition get_val_from_list_by_basic :: "'a list \<Rightarrow> basic_post_type \<Rightarrow> 'a" where
"get_val_from_list_by_basic bl pos =
  (case pos of
    (basic_post_type.Nat val) \<Rightarrow> (nth bl val) |
    (basic_post_type.Int val) \<Rightarrow> (nth bl (nat val)))"
declare get_val_from_list_by_basic_def [simp]

text "Getting array variable single values by name and absolute position from model state"
definition get_cur_arvar_by_name_by_pos :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
"get_cur_arvar_by_name_by_pos st var_name pos =
  (case (get_cur_var_init_by_name st var_name) of
    (stacked_var_init.Array (stacked_array_interval.Int val1 val2) values  opt) \<Rightarrow>
      (get_val_from_list_by_basic values (basic_post_type_sum (basic_post_type.Int val1) pos)))"
declare get_cur_arvar_by_name_by_pos_def [simp]

text "Setting in process vars list new var init value by name"
definition set_symbvar_in_proc_vars :: "(stacked_proc_vars) \<Rightarrow>  symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> stacked_proc_vars" where
"set_symbvar_in_proc_vars vars name val= 
  (case the (fmlookup vars name) of
    (stacked_proc_var.Var var) \<Rightarrow> (fmupd name (stacked_proc_var.Var val) vars)
  | (stacked_proc_var.InOutVar var) \<Rightarrow> (fmupd name (stacked_proc_var.InOutVar val) vars)
  | (stacked_proc_var.InVar var) \<Rightarrow> (fmupd name (stacked_proc_var.InVar val) vars)
  | (stacked_proc_var.OutVar var) \<Rightarrow> (fmupd name (stacked_proc_var.OutVar val) vars))"
declare set_symbvar_in_proc_vars_def [simp]

text "Setting symbolic var in current process in model state"
definition set_cur_proc_symbvar :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> model_context" where
"set_cur_proc_symbvar st var_name val = 
  (case st of (ST global_vars pg_map pg_name  f1 f2) \<Rightarrow>
    (let (prog_vars,pc_map,pc_name) = the (fmlookup pg_map pg_name);
         (proc_vars,v1,v2,v3,v4,v5) = the (fmlookup pc_map pc_name)
     in (ST
         global_vars 
         (fmupd
          pg_name
          (prog_vars,
           (fmupd
            pc_name
            (set_symbvar_in_proc_vars proc_vars var_name val,v1,v2,v3,v4,v5)
            pc_map),
           pc_name)
          pg_map)
          pg_name
         f1
         f2)))"
declare set_cur_proc_symbvar_def [simp]

text "Setting symbolic var in program vars"
definition set_symbvar_in_prog_vars :: "stacked_prog_vars \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> stacked_prog_vars" where
"set_symbvar_in_prog_vars vars name val= 
  (case the (fmlookup vars name) of
    (stacked_prog_var.Var var) \<Rightarrow> (fmupd name (stacked_prog_var.Var val) vars)
  | (stacked_prog_var.InOutVar var) \<Rightarrow> (fmupd name (stacked_prog_var.InOutVar val) vars)
  | (stacked_prog_var.InVar var) \<Rightarrow> (fmupd name (stacked_prog_var.InVar val) vars)
  | (stacked_prog_var.OutVar var) \<Rightarrow> (fmupd name (stacked_prog_var.OutVar val) vars)
  | (stacked_prog_var.ExtVar var) \<Rightarrow> (fmupd name (stacked_prog_var.ExtVar val) vars))"
declare set_symbvar_in_prog_vars_def [simp]

text "Setting symbolic var in current program in model state"
definition set_cur_prog_symbvar :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> model_context" where
"set_cur_prog_symbvar st var_name val = 
  (case st of (ST global_vars pg_map pg_name  f1 f2) \<Rightarrow>
    (let (prog_vars,pc_map,pc_name) = the (fmlookup pg_map pg_name)
     in (ST
         global_vars 
         (fmupd
          pg_name
          (set_symbvar_in_prog_vars prog_vars var_name val,
           pc_map,
           pc_name)
          pg_map)
         pg_name
         f1
         f2)))"
declare set_cur_prog_symbvar_def [simp]

text "Setting symbolic var in global vars"
definition set_symbvar_in_global_vars :: "stacked_global_vars \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> stacked_global_vars" where
"set_symbvar_in_global_vars vars name val= 
  (case the (fmlookup vars name) of
    (stacked_global_var.Var var) \<Rightarrow> (fmupd name (stacked_global_var.Var val) vars))"
declare set_symbvar_in_global_vars_def [simp]

text "Setting global symbolic var in model state"
definition set_global_symbvar :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> model_context" where
"set_global_symbvar st var_name val = 
  (case st of (ST global_vars pg_map pg_name  funcs funblocks) \<Rightarrow>
    (ST
     (set_symbvar_in_global_vars global_vars var_name val) 
     pg_map pg_name 
     funcs
     funblocks))"
declare set_global_symbvar_def [simp]

text "Setting in model state new symbolic var value by name"
definition set_symbvar :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type => model_context" where
"set_symbvar st var_name value =
  (let val = (stacked_var_init.Symbolic value None) in
  (case (get_var_level_by_name_for_set st var_name) of
    var_level.Global \<Rightarrow> (set_global_symbvar st var_name val)
  | var_level.Program \<Rightarrow> (set_cur_prog_symbvar st var_name val)
  | var_level.Process \<Rightarrow> (set_cur_proc_symbvar st var_name val)))"
declare set_symbvar_def [simp]

text "Setting new val to list in basic_post_type position"
definition set_val_to_list_by_basic :: "'a list \<Rightarrow> basic_post_type \<Rightarrow> 'a \<Rightarrow> 'a list" where
"set_val_to_list_by_basic l pos new_val = 
  (case pos of 
    basic_post_type.Nat pos \<Rightarrow> (list_update l pos new_val) |
    basic_post_type.Int pos \<Rightarrow> (list_update l (nat pos) new_val))"
declare set_val_to_list_by_basic_def [simp]

text "Setting in model state new array variable single values by name and absolute position"
definition set_arvar :: "model_context \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type \<Rightarrow>  model_context" where
"set_arvar st var_name pos value =
  (case (get_cur_var_init_by_name st var_name) of
    (stacked_var_init.Array (stacked_array_interval.Int val1 val2) values  opt) \<Rightarrow> 
      (let val = (stacked_var_init.Array 
                  (stacked_array_interval.Int val1 val2)
                  (set_val_to_list_by_basic values (basic_post_type_sum (basic_post_type.Int val1) pos) value)
                  opt) in 
  (case (get_var_level_by_name_for_set st var_name) of
    var_level.Global \<Rightarrow> (set_global_symbvar st var_name val)
  | var_level.Program \<Rightarrow> (set_cur_prog_symbvar st var_name val)
  | var_level.Process \<Rightarrow> (set_cur_proc_symbvar st var_name val)))) "
declare set_arvar_def [simp]

text "Compare process status and estimated status"
definition check_proc_status :: "model_context \<Rightarrow> process_name \<Rightarrow> proc_status \<Rightarrow> basic_post_type" where
"check_proc_status st name proc_stat = 
  (let (_,_,_,_, cur_proc_stat,_) = (get_procst_by_name st name) 
    in (basic_post_type.Bool (proc_status_is cur_proc_stat proc_stat)))"
declare check_proc_status_def [simp]

text "Setting current process name in current program"
definition set_cur_proc_name :: "model_context \<Rightarrow> process_name \<Rightarrow> model_context" where
"set_cur_proc_name st name = 
  (case st of (ST g_list pg_map pg_name f1 f2) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st)
           
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,p_map,name)
              pg_map)
            pg_name f1 f2)))"
declare set_cur_proc_name_def [simp]

text "Setting current program name"
definition set_cur_prog_name :: "model_context \<Rightarrow> program_name \<Rightarrow> model_context" where
"set_cur_prog_name st name =
  (case st of
    (ST g_list pg_map pg_name f1 f2) \<Rightarrow>
      (ST g_list pg_map name f1 f2))"
declare set_cur_prog_name_def [simp]

text "Resetting timer in current process in model state"
definition reset_cur_timer :: "model_context \<Rightarrow> model_context" where
"reset_cur_timer st = 
  (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_cur_procst_from_progst (var_list,p_map,p_name))
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 p_name 
                 (process_vars, current_state, next_state, state_names, process_status, time.Time 0 0 0 0 0)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare reset_cur_timer_def [simp]

text "Stopping process by name in model state"
definition stop_process :: "model_context \<Rightarrow> process_name \<Rightarrow> model_context" where
"stop_process st target_proc_name =
    (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) target_proc_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 target_proc_name 
                 (process_vars, current_state, next_state, state_names, proc_status.Stop, t)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare stop_process_def [simp]

text "Stopping current process in model state"
definition stop_cur_process :: "model_context  \<Rightarrow> model_context" where
"stop_cur_process st =
  (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) p_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 p_name 
                 (process_vars, current_state, next_state, state_names, proc_status.Stop, t)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare stop_cur_process_def [simp]

text "Erroring process by name in model state"
definition error_process :: "model_context \<Rightarrow> process_name \<Rightarrow> model_context" where
"error_process st target_proc_name =
   (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) target_proc_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 target_proc_name 
                 (process_vars, current_state, next_state, state_names, proc_status.Error, t)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare error_process_def [simp]

text "Erroring current process in model state"
definition error_cur_process :: "model_context \<Rightarrow> model_context" where
"error_cur_process st=
   (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) p_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 p_name 
                 (process_vars, current_state, next_state, state_names, proc_status.Error, t)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare error_cur_process_def [simp]

text "Resetting process by name in model state"
definition reset_process :: "model_context \<Rightarrow> process_name \<Rightarrow> model_context" where
"reset_process st target_proc_name =
 (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) target_proc_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 target_proc_name 
                 (process_vars, current_state, next_state, state_names, proc_status.Active, time.Time 0 0 0 0 0)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare reset_process_def [simp]

text "Resetting current process in model state"
definition reset_cur_process :: "model_context \<Rightarrow> model_context" where
"reset_cur_process st  =
 (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) p_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 p_name 
                 (process_vars, current_state, next_state, state_names, proc_status.Active, time.Time 0 0 0 0 0)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare reset_cur_process_def [simp]

definition inactive_cur_process :: "model_context \<Rightarrow> model_context" where
"inactive_cur_process st =
  (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) p_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 p_name 
                 (process_vars, current_state, next_state, state_names, proc_status.Inactive, t)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare inactive_cur_process_def [simp]

definition inactive_process :: "model_context \<Rightarrow> process_name \<Rightarrow> model_context" where
"inactive_process st target_proc_name =
   (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) target_proc_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 target_proc_name 
                 (process_vars, current_state, next_state, state_names, proc_status.Inactive, t)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare inactive_process_def [simp]

text "Setting new state by name in current process in model state"
definition set_state :: "model_context \<Rightarrow> state_name \<Rightarrow> model_context" where
"set_state st st_name = 
  (case st of
    (ST g_list pg_map pg_name fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_progst st);
           (process_vars, current_state, next_state, state_names, process_status, t) = (get_procst_from_progst_by_name (var_list,p_map,p_name) p_name)
        in (ST g_list 
          (fmupd 
              pg_name 
              (var_list,(fmupd 
                 p_name 
                 (process_vars, current_state, st_name, state_names, process_status, t)
                 p_map),p_name)
              pg_map) 
            pg_name fb_list f_list)))"
declare set_state_def [simp]

text "Getting timeout of state"
definition get_state_timeout :: "model_context \<Rightarrow> stacked_state \<Rightarrow> time" where
"get_state_timeout st ss =
  (case ss of
    (_,_,_, Some (timeout.Const t _)) => basic_to_time (const_to_basic t)
  | (_,_,_, Some (timeout.SymbolicVar var_name _)) => basic_to_time (get_cur_symbvar_by_name st var_name))"
declare get_state_timeout_def [simp]

text "Getting time of current process"
definition get_cur_time :: "model_context \<Rightarrow> time" where
"get_cur_time st = 
 (case st of (ST global_var_decl_list pg_map p_name function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup pg_map p_name) of Some(p_state) \<Rightarrow> p_state);
        (proc_vars,st_name,next_state,state_names, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of Some(proc_state) \<Rightarrow> proc_state)
    in cur_time)) "
declare get_cur_time_def [simp]

text "Getting time of process by name"
definition get_process_time_by_name :: "model_context \<Rightarrow> process_name \<Rightarrow> time" where
"get_process_time_by_name st proc_name= 
 (case st of (ST global_var_decl_list pg_map pg_name  function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, _) = (case (fmlookup pg_map pg_name) of Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list),st_name,next_state,state_names, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of Some(proc_state) \<Rightarrow> proc_state)
  in cur_time)) "
declare get_process_time_by_name_def [simp]

text "Getting name of next state"
primrec get_next_state_name :: "state_name list \<Rightarrow> state_name \<Rightarrow> state_name" where
"get_next_state_name (st_name#other) name =
  (if (st_name = name) then (hd other) else get_next_state_name other name)"
declare get_next_state_name.simps [simp]

text "Setting next state name in next state"
definition set_next_state_next :: "model_context \<Rightarrow> model_context" where
"set_next_state_next st = 
 (case st of (ST global_var_decl_list pg_map pg_name function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup pg_map pg_name) of Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list),st_name,next_state,state_names, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state);
    next_state_name = get_next_state_name state_names st_name
  in (ST 
        global_var_decl_list 
        (fmupd 
            pg_name
            (var_list,(fmupd 
                 proc_name
                 ((proc_var_list), st_name,next_state_name,state_names, proc_stat, cur_time)
                 proc_map), 
              proc_name) 
            pg_map)
          pg_name 
        function_block_decl_list 
        function_decl_list))) " 
declare set_next_state_next_def [simp]

text "Setting current state into next state"
definition set_into_next_state :: "model_context \<Rightarrow> model_context" where
"set_into_next_state st = 
 (case st of (ST global_var_decl_list pg_map pg_name  function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup pg_map pg_name) of Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list),st_name,next_state,state_names, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state) 
  in (ST 
        global_var_decl_list 
        (fmupd 
            pg_name
            (var_list,(fmupd 
                 proc_name
                 (proc_var_list, next_state,next_state,state_names, proc_stat, (if (st_name = next_state) then cur_time else (time.Time 0 0 0 0 0)))
                 proc_map), 
              proc_name) 
            pg_map)
          pg_name 
        function_block_decl_list 
        function_decl_list))) " 
declare set_into_next_state_def [simp]

text "Extract timeout stmt if cur process time more than timeout "
definition extr_timeout_stmt :: "model_context \<Rightarrow> timeout \<Rightarrow> (stmt option)" where
"extr_timeout_stmt st timeo = 
  (case st of (ST global_var_decl_list pg_map pg_name function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup pg_map pg_name) of Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list),st_name,next_state,state_names, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state) 
  in (case timeo of
       (timeout.Const c stm) \<Rightarrow>  (if (time_less (basic_to_time (const_to_basic c)) cur_time) then (Some stm) else None)
     | (timeout.SymbolicVar sv stm) \<Rightarrow> (if (time_less (basic_to_time (get_cur_symbvar_by_name st sv)) cur_time) then (Some stm) else None))))"
declare extr_timeout_stmt_def [simp]

text "Gather out and inout vars from process vars"
definition gather_process_out_vars :: "stacked_proc_vars \<Rightarrow> stacked_proc_vars" where
"gather_process_out_vars vars = 
  (ffold 
    (\<lambda>(name,val) fm. fmupd name val fm)
    fmempty
    (ffilter
      (\<lambda>(name,val).(case val of
                    stacked_proc_var.OutVar _ \<Rightarrow> True
                  | stacked_proc_var.InOutVar _ \<Rightarrow> True
                  | (_) \<Rightarrow> False)) 
      (fset_of_fmap vars)))"
declare gather_process_out_vars_def [simp]

text "Gather out and inout vars from all processes vars"
definition gather_processes_out_vars :: "((process_name,process_context) fmap) \<Rightarrow> stacked_proc_vars" where
"gather_processes_out_vars proc_map = 
  ffold 
    (\<lambda>(vars,_,_,_,_,_) var_map. fmadd (gather_process_out_vars vars) var_map) 
    fmempty 
    (fmran proc_map)" 
declare gather_processes_out_vars_def [simp]

text "Updates In and InOut vars in process vars: old vars => vars to update => updated vars"
definition update_process_in_vars :: "stacked_proc_vars \<Rightarrow> stacked_proc_vars \<Rightarrow> stacked_proc_vars" where
"update_process_in_vars old up = 
  (fmmap_keys 
    (\<lambda>name val. (case val of
                  stacked_proc_var.InVar _ \<Rightarrow> 
                    (case (fmlookup up name) of 
                      None \<Rightarrow> val
                    | Some new_val \<Rightarrow> (stacked_proc_var.InVar (extr_stacked_proc_var_init new_val)))
                | stacked_proc_var.InOutVar _ \<Rightarrow> 
                    (case (fmlookup up name) of 
                      None \<Rightarrow> val
                    | Some new_val \<Rightarrow> (stacked_proc_var.InOutVar (extr_stacked_proc_var_init new_val)))
                | _ \<Rightarrow> val))
    old)"
declare update_process_in_vars_def [simp]

text "Updates In and InOut vars in processes vars: old vars => vars to update => updated vars"
definition update_processes_in_vars :: "((process_name,process_context) fmap) \<Rightarrow> stacked_proc_vars \<Rightarrow>((process_name,process_context) fmap)" where
"update_processes_in_vars proc_map new_vars= 
  (fmmap
    (\<lambda>(proc_vars,v1,v2,v3,v4,v5). (update_process_in_vars proc_vars new_vars,v1,v2,v3,v4,v5))
    proc_map)"
declare update_processes_in_vars_def [simp]

text "Distribution of process out vars values"
definition process_vars_distribution :: "model_context \<Rightarrow> model_context" where
"process_vars_distribution st = 
  (case st of (ST global_var_decl_list pg_map pg_name f1 f2) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup pg_map pg_name) of Some(p_state) \<Rightarrow> p_state);
        put_vars = gather_processes_out_vars proc_map 
  in (ST global_var_decl_list 
      (fmupd
        pg_name
        (var_list,
          update_processes_in_vars proc_map put_vars,
          proc_name)
        pg_map)
      pg_name f1 f2)))"
declare process_vars_distribution_def [simp]

text "gather Out and InOut vars from program vars"
definition gather_program_out_vars :: "stacked_prog_vars \<Rightarrow> stacked_prog_vars" where
"gather_program_out_vars vars = 
  (ffold 
    (\<lambda>(name,val) fm. fmupd name val fm)
    fmempty
    (ffilter
      (\<lambda>(name,val).(case val of
                    stacked_prog_var.OutVar _ \<Rightarrow> True
                  | stacked_prog_var.InOutVar _ \<Rightarrow> True
                  | (_) \<Rightarrow> False)) 
      (fset_of_fmap vars)))"
declare gather_program_out_vars_def [simp]

text "Gather out and inout vars from all programs vars"
definition gather_programs_out_vars :: "((program_name,program_context) fmap) \<Rightarrow> stacked_prog_vars" where
"gather_programs_out_vars prog_map = 
  ffold 
    (\<lambda>(vars,_,_) var_map. fmadd (gather_program_out_vars vars) var_map) 
    fmempty 
    (fmran prog_map)" 
declare gather_programs_out_vars_def [simp]

text "Updates In and InOut vars in process: old vars => vars to update => updated vars"
definition update_program_in_vars :: "stacked_prog_vars \<Rightarrow> stacked_prog_vars \<Rightarrow> stacked_prog_vars" where
"update_program_in_vars old up = 
  (fmmap_keys 
    (\<lambda>name val. (case val of
                  stacked_prog_var.InVar _ \<Rightarrow> 
                    (case (fmlookup up name) of 
                      None \<Rightarrow> val
                    | Some new_val \<Rightarrow> (stacked_prog_var.InVar (extr_stacked_prog_var_init new_val)))
                | stacked_prog_var.InOutVar _ \<Rightarrow> 
                    (case (fmlookup up name) of 
                      None \<Rightarrow> val
                    | Some new_val \<Rightarrow> (stacked_prog_var.InOutVar (extr_stacked_prog_var_init new_val)))
                | _ \<Rightarrow> val))
    old)"
declare update_program_in_vars_def [simp]

text "Updates In and InOut vars in programs vars: old vars => vars to update => updated vars"
definition update_programs_in_vars :: "((program_name,program_context) fmap) \<Rightarrow> stacked_prog_vars \<Rightarrow>((program_name,program_context) fmap)" where
"update_programs_in_vars prog_map new_vars= 
  (fmmap
    (\<lambda>(proc_vars,v1,v2). (update_program_in_vars proc_vars new_vars,v1,v2))
    prog_map)"
declare update_programs_in_vars_def [simp]

text "Distribution of program out vars values"
definition prog_vars_distribution :: "model_context \<Rightarrow> model_context" where
"prog_vars_distribution st = 
  (case st of (ST global_var_decl_list ps_map p_name f1 f2) \<Rightarrow>
    (let put_vars = gather_programs_out_vars ps_map 
  in (ST global_var_decl_list
      (update_programs_in_vars ps_map put_vars)
      p_name f1 f2)))"
declare prog_vars_distribution_def [simp]

text "Incrementing active processes time by time step"
definition add_time_to_active_processes :: "model_context \<Rightarrow> time \<Rightarrow> model_context" where
"add_time_to_active_processes st t = 
  (case st of (ST global_var_decl_list pg_map pg_name function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup pg_map pg_name) of Some(p_state) \<Rightarrow> p_state)
  in (ST 
        global_var_decl_list 
        (fmmap
            (\<lambda>(vars,pc_map,pc_name). 
              (vars,
              fmmap
              (\<lambda>(v1,v2,v3,v4,stat,t1).
                (v1,v2,v3,v4,stat, (if (proc_status_is stat proc_status.Active) then (time_sum t1 t) else t1)))
              pc_map,
              pc_name))
            pg_map)
          pg_name
        function_block_decl_list 
        function_decl_list)))"
declare add_time_to_active_processes_def [simp]

text "Checking is process active by name"
definition is_process_active :: "model_context \<Rightarrow> process_name \<Rightarrow> bool" where
"is_process_active st name = 
  (case st of (ST global_var_decl_list pg_map pg_name function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup pg_map pg_name) of Some(p_state) \<Rightarrow> p_state);
         (_,_,_,_,status,_) = (case (fmlookup proc_map name) of Some(proc_state) \<Rightarrow> proc_state)
    in (proc_status_is status proc_status.Active)))"
declare is_process_active_def [simp]

text "Getting function body by name"
definition get_func_by_name :: "model_context \<Rightarrow> func_name \<Rightarrow> stacked_func" where
"get_func_by_name st name = 
  (case st of (ST _ _ _ _ f_map) \<Rightarrow> the (fmlookup f_map name))"
declare get_func_by_name_def [simp] 

declare fmupd_reorder_neq [simp]
(*declare fmran_def [simp]
declare ffold_def [simp]*)
end