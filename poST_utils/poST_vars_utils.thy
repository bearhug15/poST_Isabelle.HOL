theory poST_vars_utils
  imports "~~/poST/poST_model/poST_vars" "~~/poST/poST_utils/poST_expr_utils"
begin

definition basics_to_array_interval :: "ptype \<Rightarrow> ptype \<Rightarrow> array_interval" where
"basics_to_array_interval var1 var2 = 
  (case (var1,var2) of 
    ((ptype.Int val1), (ptype.Int val2)) \<Rightarrow> array_interval.Int val1 val2
  | ((ptype.Nat val1), (ptype.Nat val2)) \<Rightarrow> array_interval.Int val1 val2)"
declare basics_to_array_interval_def [simp]

end