theory poST_time_utils
  imports "~~/poST/poST_model/poST_time"
begin

definition nat_to_time :: "nat \<Rightarrow> time" where
"nat_to_time var = 
  (let miliseconds = (var mod 1000);
       seconds = (var div 1000 mod 60);
       minutes = (var div 1000 div 60 mod 60);
       hours = (var div 1000 div 60 div 60 mod 24);
       days = (var div 1000 div 60 div 60 div 24) in
       Time days hours minutes seconds miliseconds)"
declare nat_to_time_def [simp]

definition int_to_time :: "int \<Rightarrow> time" where
"int_to_time var1 = (let var = (nat var1) in nat_to_time var)"
declare int_to_time_def [simp]

definition real_to_time :: "real \<Rightarrow> time" where
"real_to_time var = (let var = (nat \<lfloor>var\<rfloor>) in nat_to_time var)"
declare real_to_time_def [simp]

definition bool_to_time :: "bool \<Rightarrow> time" where 
"bool_to_time var = (if var then Time 0 0 0 0 1 else Time 0 0 0 0 0) "
declare bool_to_time_def [simp]

definition time_sum :: "time \<Rightarrow> time \<Rightarrow> time" where
"time_sum t1 t2 = 
  (case (t1,t2) of 
    ((Time v1d v1h v1m v1s v1ms),(Time v2d v2h v2m v2s v2ms)) \<Rightarrow>
    (let miliseconds = (v1ms + v2ms) mod 1000;
      seconds = (v1s + v2s + (v1ms + v2ms) div 1000) mod 60 ;
      minutes = (v1m + v2m + (v1s + v2s) div 60) mod 60;
      hours = (v1h + v2h + (v1m + v2m) div 60) mod 24;
      days = v1d + v2d + (v1h + v2h) div 60
      in Time days hours minutes seconds miliseconds))"
declare time_sum_def [simp]
(*
fun time_sub :: "time \<Rightarrow> time \<Rightarrow> time" where
"time_sub (Time v1d v1h v1m v1s v1ms) (Time v2d v2h v2m v2s v2ms) = 
  (let d = (int v1d) -(int v2d) -1;
       h = 23 + v1h -v2h ;
       m = 59 + v1m -v2m ;
       s = 59 + v1s -v2s ;
       ms = 1000 + v1ms - v2ms;
       resms = ms mod 1000;
       buffs = (s + ms div 1000);
       ress = buffs mod 60;
       buffm = m + buffs div 60;
       resm =  buffm mod 60; 
       buffh = h + buffm div 60;
       resh = buffh mod 24;
       resd = d + buffh div 24 in
        (if resd < 0 | resh < 0 | resm < 0 | ress < 0 | resms < 0 
          then Time 0 0 0 0 0 
          else Time (nat resd) (nat resh) (nat resm) (nat ress) (nat resms)))"
*)

definition time_eq :: "time \<Rightarrow> time \<Rightarrow>bool" where
"time_eq t1 t2 = 
  (case (t1,t2) of 
    ((Time v14 v13 v12 v11 v10),(Time v24 v23 v22 v21 v20)) \<Rightarrow>
    ((v14 = v24) \<and> (v13 = v23) \<and> (v12 = v22) \<and> (v11 = v21) \<and> (v10 = v20)))"
declare time_eq_def [simp]

definition time_noteq :: "time \<Rightarrow> time \<Rightarrow>bool" where
"time_noteq t1 t2 = 
  (case (t1,t2) of 
    ((Time v14 v13 v12 v11 v10),(Time v24 v23 v22 v21 v20)) \<Rightarrow>
    ((v14 \<noteq> v24) \<or> (v13 \<noteq> v23) \<or> (v12 \<noteq> v22) \<or> (v11 \<noteq> v21) \<or> (v10 \<noteq> v20)))"
declare time_noteq_def [simp]

definition time_less :: "time \<Rightarrow> time \<Rightarrow>bool" where
"time_less t1 t2 =
(case (t1,t2) of 
    ((Time v14 v13 v12 v11 v10),(Time v24 v23 v22 v21 v20)) \<Rightarrow>
  ((v10 < v20) \<or>
  ((v10 = v20) \<and> ((v11 < v21) \<or> 
                  (v11 = v21) \<and> ((v12 < v22) \<or> 
                                 (v12 = v22) \<and> ((v13 < v23) \<or>
                                                (v13 = v23) \<and> (v14 < v24)))))))"
declare time_less_def [simp]

definition time_more :: "time \<Rightarrow> time \<Rightarrow>bool" where
"time_more t1 t2 =
(case (t1,t2) of 
    ((Time v14 v13 v12 v11 v10),(Time v24 v23 v22 v21 v20)) \<Rightarrow>
  ((v10 > v20) \<or>
  ((v10 = v20) \<and> ((v11 > v21) \<or> 
                  (v11 = v21) \<and> ((v12 > v22) \<or> 
                                 (v12 = v22) \<and> ((v13 > v23) \<or>
                                                (v13 = v23) \<and> (v14 > v24)))))))"
declare time_more_def [simp]

definition time_eqless :: "time \<Rightarrow> time \<Rightarrow>bool" where
"time_eqless t1 t2 =
(case (t1,t2) of 
    ((Time v14 v13 v12 v11 v10),(Time v24 v23 v22 v21 v20)) \<Rightarrow> 
 ((v10 \<le> v20) \<or>
  ((v10 = v20) \<and> ((v11 \<le> v21) \<or> 
                  (v11 = v21) \<and> ((v12 \<le> v22) \<or> 
                                 (v12 = v22) \<and> ((v13 \<le> v23) \<or>
                                                (v13 = v23) \<and> (v14 \<le> v24)))))))"
declare time_eqless_def [simp]

definition time_eqmore :: "time \<Rightarrow> time \<Rightarrow>bool" where
"time_eqmore t1 t2 = 
(case (t1,t2) of 
    ((Time v14 v13 v12 v11 v10),(Time v24 v23 v22 v21 v20)) \<Rightarrow>
 ((v10 \<ge> v20) \<or>
  ((v10 = v20) \<and> ((v11 \<ge> v21) \<or> 
                  (v11 = v21) \<and> ((v12 \<ge> v22) \<or> 
                                 (v12 = v22) \<and> ((v13 \<ge> v23) \<or>
                                                (v13 = v23) \<and> (v14 \<ge> v24)))))))"
declare time_eqmore_def [simp]
end