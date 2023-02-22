theory poST_expr_utils
  imports basic_poST_types_utils "~~/poST/poST_model/poST_expr"
begin
definition proc_status_is :: "proc_status \<Rightarrow> proc_status \<Rightarrow> bool" where
"proc_status_is s1 s2 = 
(case (s1,s2) of 
  (proc_status.Active,proc_status.Active) \<Rightarrow> True |
  (proc_status.Inactive,proc_status.Inactive) \<Rightarrow> True |
  (proc_status.Stop,proc_status.Stop) \<Rightarrow> True |
  (proc_status.Error,proc_status.Error) \<Rightarrow> True |
  (proc_status.Stop,proc_status.Inactive) \<Rightarrow> True |
  (proc_status.Error,proc_status.Inactive) \<Rightarrow> True |
  (_,_) \<Rightarrow> False)"
declare proc_status_is_def [simp]

text "Executing unary operation"
definition unary_op_exec :: "unary_op => basic_post_type \<Rightarrow> basic_post_type" where
"unary_op_exec op var = (case op of unary_op.Not \<Rightarrow> (basic_post_type_not var) | unary_op.Minus \<Rightarrow> (basic_post_type_minus var))"
declare unary_op_exec_def [simp]

text "Executing binary operation"
definition binary_op_exec :: "binary_op \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
"binary_op_exec op var1 var2 = 
  (case op of 
    binary_op.And \<Rightarrow> basic_post_type.Bool(basic_post_type_and var1 var2)|
 binary_op.Or \<Rightarrow> basic_post_type.Bool(basic_post_type_or var1 var2)|
    binary_op.Xor \<Rightarrow> basic_post_type.Bool(basic_post_type_xor var1 var2) | 
    binary_op.Eq \<Rightarrow> basic_post_type.Bool(basic_post_type_eq var1 var2)| 
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
declare binary_op_exec_def [simp]

end