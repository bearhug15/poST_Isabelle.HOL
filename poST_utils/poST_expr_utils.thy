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
  (proc_status.Timeout _, proc_status.Inactive) \<Rightarrow> False |
  (_,_) \<Rightarrow> False)"
end