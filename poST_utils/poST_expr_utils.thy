theory poST_expr_utils
  imports ptypes_utils "~~/poST/poST_model/poST_expr"
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
definition unary_op_exec :: "unary_op => ptype \<Rightarrow> ptype" where
"unary_op_exec op var = (case op of unary_op.Not \<Rightarrow> (ptype_not var) | unary_op.Minus \<Rightarrow> (ptype_minus var))"
declare unary_op_exec_def [simp]

text "Executing binary operation"
definition binary_op_exec :: "binary_op \<Rightarrow> ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
"binary_op_exec op var1 var2 = 
  (case op of 
    binary_op.And \<Rightarrow> ptype.Bool(ptype_and var1 var2)|
 binary_op.Or \<Rightarrow> ptype.Bool(ptype_or var1 var2)|
    binary_op.Xor \<Rightarrow> ptype.Bool(ptype_xor var1 var2) | 
    binary_op.Eq \<Rightarrow> ptype.Bool(ptype_eq var1 var2)| 
    binary_op.NotEq \<Rightarrow>ptype.Bool(ptype_noteq var1 var2)| 
    binary_op.Less \<Rightarrow>ptype.Bool(ptype_less var1 var2)| 
    binary_op.More \<Rightarrow>ptype.Bool(ptype_more var1 var2)| 
    binary_op.LessEq \<Rightarrow>ptype.Bool(ptype_lesseq var1 var2)| 
    binary_op.MoreEq \<Rightarrow>ptype.Bool(ptype_moreeq var1 var2)| 
    binary_op.Sum \<Rightarrow> ptype_sum var1 var2| 
    binary_op.Sub \<Rightarrow> ptype_sub var1 var2| 
    binary_op.Mul \<Rightarrow> ptype_mul var1 var2| 
    binary_op.Div \<Rightarrow> ptype_div var1 var2| 
    binary_op.Mod \<Rightarrow> ptype_mod var1 var2)"
declare binary_op_exec_def [simp]

end