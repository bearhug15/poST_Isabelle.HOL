theory poSTVM_state_lemmas
  imports 
    "~~/poST/poSTVM/poSTVM_state"
    "~~/poST/poST_lemmas/ptypes_lemmas"
begin 

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

lemma proc_vars_mirror1[simp]: "get_cur_proc_vars (set_cur_proc_vars st vars) = vars" 
proof -
  show ?thesis sorry
qed

lemma proc_vars_mirror2[simp]: "(get_proc_var_by_name (set_var_in_proc_vars_by_name st name val) name) = val" 
proof -
  show ?thesis sorry
qed

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
  from assms have
  "(get_cur_var_init_by_name (set_cur_proc_var st name val) name) =
    (get_proc_var_by_name (get_cur_proc_vars 
    (set_cur_proc_var st name val)) 
    name)" using set_symbvar_process_level_keep by auto
  hence "(get_cur_var_init_by_name (set_cur_proc_var st name val) name) = 
          (get_proc_var_by_name (get_cur_proc_vars 
          (set_cur_proc_vars st (set_var_in_proc_vars_by_name (get_cur_proc_vars st) name val))) 
           name)" by simp
  hence "(get_cur_var_init_by_name (set_cur_proc_var st name val) name) = 
          (get_proc_var_by_name (set_var_in_proc_vars_by_name (get_cur_proc_vars st) name val)
          name)" using proc_vars_mirror1 by simp
  thus ?thesis using proc_vars_mirror2 by simp
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
end