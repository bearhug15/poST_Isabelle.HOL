theory poST_vars
  imports 
    poST_expr "HOL-Library.Finite_Map"
begin
(*type_synonym var_list = "symbolic_var list"*)

type_synonym simple_spec_init = "basic_post_type * (expr option)"

datatype array_interval = Expr expr expr | Int int int
type_synonym array_spec = "array_interval * (basic_post_type list)"
type_synonym array_init = "expr list"
type_synonym array_spec_init = "array_spec * (array_init option)"

datatype var_init_decl = Simple simple_spec_init |
                         Array array_spec_init |
                         FunctionBlock func_block_name

type_synonym in_var_decl = "((symbolic_var, var_init_decl) fmap)"
type_synonym out_var_decl = "((symbolic_var, var_init_decl) fmap)"
type_synonym inout_var_decl = "((symbolic_var, var_init_decl) fmap)"
type_synonym var_decl = "is_const * ((symbolic_var, var_init_decl) fmap)"

datatype ext_var_init_decl = ExtVarInitDecl "basic_post_type"
type_synonym ext_var_decl = "is_const * ((symbolic_var, ext_var_init_decl) fmap)"

type_synonym direct_var = "direct_type_perfix * direct_size_prefix * (int list)"
type_synonym global_var_init_decl = "direct_var * basic_post_type"

datatype all_var_init_decl = Var var_init_decl | GlobalVar global_var_init_decl

type_synonym global_var_decl = "is_const * ((symbolic_var, all_var_init_decl) fmap)"

type_synonym process_var = id

definition basics_to_array_interval :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> array_interval" where
"basics_to_array_interval var1 var2 = 
  (case (basic_post_type_to_bptint var1,basic_post_type_to_bptint var2) of 
    ((basic_post_type.Int val1), (basic_post_type.Int val2)) \<Rightarrow> array_interval.Int val1 val2)"
(*
translations
  (type) "array_spec" <= (type) "array_interval * basic_post_type"
  (type) "array_spec_init" <= (type) "array_spec * (array_init option)"
  (type) "var_decl" <= (type) "is_const * (var_init_decl list)"
 (* (type) "ext_var_init_decl" <= (type) "symbolic_var  * basic_post_type"*)
  (type) "ext_var_decl" <= (type) "is_const * (ext_var_init_decl list)"
  (type) "direct_var" <= (type) "direct_type_perfix * direct_size_prefix * (int list)"
 (* (type) "global_var_init_decl" <= (type) "symbolic_var  * direct_var * basic_post_type"*)
  (type) "global_var_decl" <= (type) "is_const * ((symbolic_var, all_var_init_decl) fmap)"
*)
end