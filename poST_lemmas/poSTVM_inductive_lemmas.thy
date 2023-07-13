theory poSTVM_inductive_lemmas
  imports 
    "~~/poST/poST_lemmas/poSTVM_state_lemmas"
    "~~/poST/poSTVM/poSTVM_inductive"
begin
(*
theorem
   "st\<turnstile>stm\<longrightarrow>st1 \<Longrightarrow> st\<turnstile>stm\<longrightarrow>st2 \<Longrightarrow> st2 = st1"
  apply (induction arbitrary: st2 rule:eval_exec_exec_func_assign_param.induct)
proof (induction arbitrary: st2 rule: eval_exec_exec_func_assign_param.inducts) 
  fix b exp st st' st1 st2 
  assume  
*)
(*
abbreviation equiv_c :: "stmt \<Rightarrow> stmt \<Rightarrow> bool" (infix "\<sim>" 50) where
"c \<sim> c' \<equiv> (\<forall>s t. s\<turnstile>c\<longrightarrow>t = s\<turnstile>c'\<longrightarrow>t)"

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto
*)
(*
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
*)

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
  then show "?thesis" using ptype_nat_eq by simp
qed

(*
lemma
  fixes st st_res sub_st:: model_context and name :: string and val :: ptype
  assumes assms: "st\<turnstile>stmt.AssignSt (common_var.Symbolic name) exp \<longrightarrow> st_res" and
          exp_ev: "st\<turnstile>exp\<rightarrow>sub_st" and
          val_eq: "get_value sub_st = val"
  shows "ptype_eq (get_cur_symbvar_by_name st_res name) val"
proof -
  from assms obtain st1 where
    c1: "st\<turnstile>exp\<rightarrow>st1" and
    c2: "st_res = (set_cur_symbvar st1 name (get_value st1))" 
  by (smt (z3) common_var.distinct(1) common_var.inject(1) exec.cases stmt.distinct(11) stmt.distinct(13) stmt.distinct(15) stmt.distinct(17) stmt.distinct(19) stmt.distinct(3) stmt.distinct(5) stmt.distinct(7) stmt.distinct(9) stmt.inject(1))
  from c1 and exp_ev have "st1 = sub_st" by blast
qed
*)
end