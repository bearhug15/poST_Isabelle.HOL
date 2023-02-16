theory poST_vars_utils
  imports "~~/poST/poST_model/poST_vars" "~~/poST/poST_utils/poST_expr_utils"
begin

definition basics_to_array_interval :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> array_interval" where
"basics_to_array_interval var1 var2 = 
  (case (basic_post_type_to_bptint var1,basic_post_type_to_bptint var2) of 
    ((basic_post_type.Int val1), (basic_post_type.Int val2)) \<Rightarrow> array_interval.Int val1 val2)"
declare basics_to_array_interval_def [simp]

end