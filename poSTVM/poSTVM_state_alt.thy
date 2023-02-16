theory poSTVM_state_alt
  imports 
    "~~/poST/poST_model/poST_model"
    "~~/poST/poST_utils/poST_vars_utils"
    "~~/poST/poSTVM/poSTVM_parser_alt"
begin 

type_synonym current_time = "time"

text "Process state in form of process vars list, current state, starting state, process status, process time"
(*maybe delete starting state?*)
type_synonym process_state = "(stacked_proc_var list) * state_name * state_name * proc_status * current_time"

text "Program state in form of program vars list, processes map, current process"
type_synonym program_state = "(stacked_prog_var list) * ((process_name,process_state) fmap) * process_name"

text "Model state in form of global vars, programs map, current program, function blocks list, functions list"
datatype model_state = ST "(global_var_decl list)"  "((program_name,program_state) fmap * program_name)"  "(function_block_decl list)"  "(function_decl list)"

(*TO DO add getting and setting vars not only from process vision, but program and global*)

text "Getting var init from vars map by name"
definition find_var_by_name :: "symbolic_var  \<Rightarrow>(symbolic_var, stacked_var_init) fmap \<Rightarrow> stacked_var_init option" where
"find_var_by_name var val =(fmlookup val var) "
declare find_var_by_name_def [simp]

text "Getting var init from process vars by name"
primrec get_var_by_name :: "(stacked_proc_var list) \<Rightarrow>  symbolic_var \<Rightarrow>  stacked_var_init option" where
  "get_var_by_name [] _ = None"
| "get_var_by_name (x#yz) var_name  =
    (let res = 
      (case x of 
        stacked_proc_var.ProcessVar var \<Rightarrow> None 
      | stacked_proc_var.Var  var \<Rightarrow> find_var_by_name var_name var 
      | stacked_proc_var.InVar var \<Rightarrow> find_var_by_name var_name var 
      | stacked_proc_var.OutVar var \<Rightarrow> find_var_by_name var_name var 
      | stacked_proc_var.InOutVar var \<Rightarrow> find_var_by_name var_name var) 
    in (if res = None 
          then get_var_by_name yz var_name 
          else res))"
declare get_var_by_name.simps [simp]
print_theorems

text "Getting current process state from program state"
definition get_cur_proc_state_by_prog :: "program_state \<Rightarrow> process_state" where
"get_cur_proc_state_by_prog ps = (case (fmlookup (fst (snd ps)) (snd (snd ps))) of Some (st) \<Rightarrow> st)"
declare get_cur_proc_state_by_prog_def [simp]

text "Getting process vars list in current process from program state"
definition get_cur_proc_var_list :: "program_state \<Rightarrow>stacked_proc_var list" where 
  "get_cur_proc_var_list ps_state = 
    (let (proc_var_list,st_name,proc_stat,cur_time) = get_cur_proc_state_by_prog ps_state in
      proc_var_list)"
declare get_cur_proc_var_list_def [simp]

text "Getting current program state from model state"
definition get_cur_prog_state :: "model_state \<Rightarrow> program_state" where
"get_cur_prog_state st = 
  (case st of 
    (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
      (case (fmlookup ps_map p_name) of 
        Some(p_state) \<Rightarrow> p_state))"
declare get_cur_prog_state_def [simp]

text "Getting program state by program name from model state"
definition get_proc_state_by_prog :: "program_state \<Rightarrow> process_name \<Rightarrow> process_state" where
"get_proc_state_by_prog ps var_name = (case (fmlookup (fst (snd ps)) var_name) of Some (st) \<Rightarrow> st)"
declare get_proc_state_by_prog_def [simp]

text "Getting process state by process name from model state" 
definition get_proc_state :: "model_state \<Rightarrow> process_name \<Rightarrow> process_state" where 
"get_proc_state st var_name =
  get_proc_state_by_prog (get_cur_prog_state st) var_name"
declare get_proc_state_def [simp]

text "Getting process vars list of current process of current program from model state"
definition get_cur_var_list :: "model_state \<Rightarrow> stacked_proc_var list" where
"get_cur_var_list st = get_cur_proc_var_list (get_cur_prog_state st)"
declare get_cur_var_list_def [simp]

text "Getting variable init by name from model state"
definition get_cur_var_by_name :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init" where
"get_cur_var_by_name st var_name = the (get_var_by_name (get_cur_var_list st) var_name)"
declare get_cur_var_by_name_def [simp]

text "Getting symbolic variable value by name from model state"
definition get_symbvar_by_name :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type" where
"get_symbvar_by_name st var_name = 
  (case (get_cur_var_by_name st var_name) of
    (stacked_var_init.Symbolic val opt) \<Rightarrow> val)"
declare get_symbvar_by_name_def [simp]

text "Getting values from list of values"
definition get_bval_from_list :: "basic_post_type list \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
"get_bval_from_list bl pos =
  (case pos of
    (basic_post_type.Nat val) \<Rightarrow> (nth bl val) |
    (basic_post_type.Int val) \<Rightarrow> (nth bl (nat val)))"
declare get_bval_from_list_def [simp]

text "Getting array variable single values by name and absolute position from model state"
definition get_arvar_by_name :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
"get_arvar_by_name st var_name pos =
  (case (get_cur_var_by_name st var_name) of
    (stacked_var_init.Array (stacked_array_interval.Int val1 val2) values  opt) \<Rightarrow>
      (get_bval_from_list values (basic_post_type_sum (basic_post_type.Int val1) pos)))"
declare get_arvar_by_name_def [simp]

text "Setting in process vars list new var init value by name"
primrec set_symbvar_in_ps_in_var_list :: "(stacked_proc_var list) \<Rightarrow>  symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> (stacked_proc_var list)" where
"set_symbvar_in_ps_in_var_list [] var_name value = []" |
"set_symbvar_in_ps_in_var_list (x # xs ::stacked_proc_var list) var_name value =
  (let res = (case x of 
   stacked_proc_var.ProcessVar var \<Rightarrow> None |
   stacked_proc_var.Var var \<Rightarrow> find_var_by_name var_name var |
   stacked_proc_var.InVar var \<Rightarrow> find_var_by_name var_name var | 
   stacked_proc_var.OutVar var \<Rightarrow> find_var_by_name var_name var | 
   stacked_proc_var.InOutVar var \<Rightarrow> find_var_by_name var_name var) in
   (if res = None
      then ([x] @ (set_symbvar_in_ps_in_var_list xs var_name value))
      else ([(case x of 
   stacked_proc_var.ProcessVar var \<Rightarrow>(stacked_proc_var.ProcessVar var) |
   stacked_proc_var.Var   var \<Rightarrow>(stacked_proc_var.Var (fmupd var_name value var)) |
   stacked_proc_var.InVar var \<Rightarrow>(stacked_proc_var.InVar (fmupd var_name value var)) | 
   stacked_proc_var.OutVar var \<Rightarrow>(stacked_proc_var.OutVar (fmupd var_name value var)) | 
   stacked_proc_var.InOutVar var \<Rightarrow>(stacked_proc_var.InOutVar (fmupd var_name value var)))] @ xs)
)) "
declare set_symbvar_in_ps_in_var_list.simps [simp]

text "Setting in process state new var init value by name"
definition set_symbvar_in_ps :: "process_state \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> process_state" where
"set_symbvar_in_ps ps var_name value = 
  (set_symbvar_in_ps_in_var_list (fst ps) var_name value, (fst (snd ps)), (fst (snd (snd ps))), (snd (snd (snd ps))))"
declare set_symbvar_in_ps_def [simp]

text "Setting in program state in current process new var value by name" 
definition set_symbvar_in_ps_in_cur_proc :: "program_state \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> program_state" where
"set_symbvar_in_ps_in_cur_proc ps var_name value = 
  (case (fmlookup (fst (snd ps)) (snd (snd ps))) of 
    Some(proc_state) \<Rightarrow> ((fst ps), fmupd (snd (snd ps)) (set_symbvar_in_ps proc_state var_name value) (fst (snd ps)), (snd (snd ps))))"
declare set_symbvar_in_ps_in_cur_proc_def [simp]

text "Setting in model state in current program new var init value by name"
definition set_symbvar_in_ps_in_cur_prog :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> stacked_var_init \<Rightarrow> model_state" where 
"set_symbvar_in_ps_in_cur_prog st var_name value = 
  (case st of 
    (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
      (case (fmlookup ps_map p_name) of
        Some(p_state) \<Rightarrow> 
          (ST global_var_decl_list 
            ((fmupd p_name (set_symbvar_in_ps_in_cur_proc p_state var_name value) ps_map), p_name) 
            function_block_decl_list function_decl_list)))"
declare set_symbvar_in_ps_in_cur_prog_def [simp]
print_theorems

text "Setting in model state new symbolic var value by name"
definition set_symbvar :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type => model_state" where
"set_symbvar st var_name value =
  (case (get_cur_var_by_name st var_name) of
    (stacked_var_init.Symbolic old_val opt) \<Rightarrow> (set_symbvar_in_ps_in_cur_prog st var_name (stacked_var_init.Symbolic value opt)) )"
declare set_symbvar_def [simp]

text "Setting new val to list in position"
definition set_bval_to_list :: "basic_post_type list \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type list" where
"set_bval_to_list l pos new_val = 
  (case pos of 
    basic_post_type.Nat pos \<Rightarrow> (list_update l pos new_val) |
    basic_post_type.Int pos \<Rightarrow> (list_update l (nat pos) new_val))"
declare set_bval_to_list_def [simp]

text "Setting in model state new array variable single values by name and absolute position"
definition set_arvar :: "model_state \<Rightarrow> symbolic_var \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type \<Rightarrow>  model_state" where
"set_arvar st var_name pos value =
  (case (get_cur_var_by_name st var_name) of
    (stacked_var_init.Array (stacked_array_interval.Int val1 val2) values  opt) \<Rightarrow> 
      (set_symbvar_in_ps_in_cur_prog 
        st 
        var_name 
        (stacked_var_init.Array 
          (stacked_array_interval.Int val1 val2)
          (set_bval_to_list values (basic_post_type_sum (basic_post_type.Int val1) pos) value)
          opt)) )"
declare set_arvar_def [simp]

text "Compare process status and estimated status"
definition check_proc_status :: "model_state \<Rightarrow> process_name \<Rightarrow> proc_status \<Rightarrow> basic_post_type" where
"check_proc_status st name proc_stat = 
  (let (_,_,_, cur_proc_stat,_) = (get_proc_state st name) 
    in (basic_post_type.Bool (proc_status_is cur_proc_stat proc_stat)))"
declare check_proc_status_def [simp]

text "Resetting timer in current process in model state"
definition reset_timer :: "model_state \<Rightarrow> model_state" where
"reset_timer st = 
  (case st of
    (ST g_list (pr_map,pr_name) fb_list f_list) \<Rightarrow>
      (let (var_list, p_map,p_name) = (get_cur_prog_state (ST g_list (pr_map,pr_name) fb_list f_list));
           (process_vars, current_state, start_state, process_status, t) = (get_cur_proc_state_by_prog (var_list,p_map,p_name))
        in (ST g_list 
          ((fmupd 
              pr_name 
              (var_list,(fmupd 
                 p_name 
                 (process_vars, current_state, start_state, process_status, t)
                 p_map),p_name)
              pr_map),
            pr_name) fb_list f_list)))"
declare reset_timer_def [simp]

text "Stopping process by name in model state"
definition stop_process :: "model_state \<Rightarrow> process_name \<Rightarrow> model_state" where
"stop_process st target_proc_name =
   (case st of 
    (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
      (let (var_list,proc_map, proc_name) = 
        (case (fmlookup ps_map p_name) of
          Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = 
          (case (fmlookup proc_map target_proc_name) of 
            Some(proc_state) \<Rightarrow> proc_state)
        in (ST global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,
              (fmupd 
                target_proc_name
                ((proc_var_list), st_name,start_st_name, proc_status.Stop, cur_time)
                proc_map), 
              proc_name) 
            ps_map),
          p_name) function_block_decl_list function_decl_list)))"
declare stop_process_def [simp]

text "Stopping current process in model state"
definition stop_same_process :: "model_state  \<Rightarrow> model_state" where
"stop_same_process st =
  (case st of
    (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
(let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
    in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Stop, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare stop_same_process_def [simp]

text "Erroring process by name in model state"
definition error_process :: "model_state \<Rightarrow> process_name \<Rightarrow> model_state" where
"error_process st target_proc_name =
   (case st of 
      (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
(let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map target_proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
    in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 target_proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Error, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare error_process_def [simp]

text "Erroring current process in model state"
definition error_same_process :: "model_state \<Rightarrow> model_state" where
"error_same_process st =
   (case st of 
(ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
(let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
    in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Error, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare error_same_process_def [simp]

text "Resetting process by name in model state"
definition reset_process :: "model_state \<Rightarrow> process_name \<Rightarrow> model_state" where
"reset_process st target_proc_name =
  (case st of
(ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
(let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), _ ,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map target_proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 target_proc_name
                 ((proc_var_list), start_st_name,start_st_name, proc_stat, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare reset_process_def [simp]

text "Resetting current process in model state"
definition reset_same_process :: "model_state \<Rightarrow> model_state" where
"reset_same_process st  =
  (case st of 
(ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
(let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), _,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 proc_name
                 ((proc_var_list), start_st_name,start_st_name, proc_stat, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare reset_same_process_def [simp]

definition inactive_same_process :: "model_state \<Rightarrow> model_state" where
"inactive_same_process st =
(case st of 
(ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
(let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), _,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 proc_name
                 ((proc_var_list), start_st_name,start_st_name, proc_status.Inactive, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare inactive_same_process_def [simp]

definition inactive_process :: "model_state \<Rightarrow> process_name \<Rightarrow> model_state" where
"inactive_process st target_proc_name =
   (case st of 
      (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
(let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map target_proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
    in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 target_proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Inactive, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare inactive_process_def [simp]

text "Setting new state by name in current process in model state"
definition set_state :: "model_state \<Rightarrow> state_name \<Rightarrow> model_state" where
"set_state st st_name = 
  (case st of
(ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
(let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of
                              Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list), _ ,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 proc_name
                 ((proc_var_list), st_name,start_st_name, proc_stat, cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare set_state_def [simp]

text "Extracting new process state from stacked process"
definition extract_process_state :: "stacked_process \<Rightarrow> process_state" where
"extract_process_state sp  = 
  (case sp of 
    (proc_name, var_list,((name, _, _, _)#other)) \<Rightarrow> 
    (var_list, name, name, proc_status.Inactive, (time.Time 0 0 0 0 0)))"
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

fun get_timeout :: "model_state \<Rightarrow> stacked_state \<Rightarrow> time" where
"get_timeout st ss =
  (case ss of
    (_,_,_, Some (timeout.Const t _)) => basic_to_time (const_to_basic t)
  | (_,_,_, Some (timeout.SymbolicVar var_name _)) => basic_to_time (get_symbvar_by_name st var_name))"
declare get_timeout.simps [simp]

definition set_timeout :: "model_state \<Rightarrow> timeout \<Rightarrow> model_state" where
"set_timeout st t = 
  (case st of (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list),st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Timeout (case t of
                                                                                (timeout.Const t _) \<Rightarrow> basic_to_time (const_to_basic t)
                                                                              | (timeout.SymbolicVar var_name _) \<Rightarrow> basic_to_time (get_symbvar_by_name st var_name)), cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare set_timeout_def [simp]

definition set_timeout_from_state :: "model_state \<Rightarrow> stacked_state \<Rightarrow> model_state" where
"set_timeout_from_state st ss =
  (case st of (ST global_var_decl_list (ps_map,p_name) function_block_decl_list function_decl_list) \<Rightarrow>
    (let (var_list,proc_map, proc_name) = (case (fmlookup ps_map p_name) of Some(p_state) \<Rightarrow> p_state);
        ((proc_var_list),st_name,start_st_name, proc_stat, cur_time) = (case (fmlookup proc_map proc_name) of 
                                    Some(proc_state) \<Rightarrow> proc_state)
  in (ST 
        global_var_decl_list 
        ((fmupd 
            p_name
            (var_list,(fmupd 
                 proc_name
                 ((proc_var_list), st_name,start_st_name, proc_status.Timeout (get_timeout st ss), cur_time)
                 proc_map), 
              proc_name) 
            ps_map),
          p_name) 
        function_block_decl_list 
        function_decl_list)))"
declare set_timeout_from_state_def [simp]

end