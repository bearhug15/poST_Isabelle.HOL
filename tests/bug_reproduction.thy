theory bug_reproduction
  imports Main "HOL-Library.Finite_Map" HOL.String
begin
type_synonym var_name = string

datatype val = Int int | Bool bool

type_synonym vars = "(var_name, val) fmap"

datatype model_state = Work | Stop

type_synonym model_context = "vars * model_state"

definition set_var :: "model_context \<Rightarrow> var_name \<Rightarrow> val \<Rightarrow> model_context" where
"set_var cont name v = (fmupd name v (fst cont), snd cont)"
definition get_var :: "model_context \<Rightarrow> var_name \<Rightarrow> val" where
"get_var cont name = the (fmlookup (fst cont) name)"

datatype bin_op = Sum | Mul | MoreEq
datatype un_op = Minus | Not

definition make_bin_op :: "bin_op \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val" where
"make_bin_op op v1 v2 = 
  (case op of
    bin_op.Sum \<Rightarrow> 
      (case (v1,v2) of
        (val.Int v1, val.Int v2) \<Rightarrow> val.Int (v1 + v2)
      | (val.Int v1, val.Bool v2) \<Rightarrow> val.Int (v1 + (if v2 then 1 else 0))
      | (val.Bool v1, val.Int v2) \<Rightarrow> val.Int (v2 + (if v1 then 1 else 0))
      | (val.Bool v1, val.Bool v2) \<Rightarrow> val.Bool (v1 \<or> v2))
  | bin_op.Mul \<Rightarrow> 
      (case (v1,v2) of
        (val.Int v1, val.Int v2) \<Rightarrow> val.Int (v1 * v2)
      | (val.Int v1, val.Bool v2) \<Rightarrow> val.Int (v1 * (if v2 then 1 else 0))
      | (val.Bool v1, val.Int v2) \<Rightarrow> val.Int (v2 * (if v1 then 1 else 0))
      | (val.Bool v1, val.Bool v2) \<Rightarrow> val.Bool (v1 \<and> v2))
  | bin_op.MoreEq \<Rightarrow> 
      (case (v1,v2) of
        (val.Int v1, val.Int v2) \<Rightarrow> val.Bool (v1 \<ge> v2)
      | (val.Int v1, val.Bool v2) \<Rightarrow> val.Bool (v1 \<ge> (if v2 then 1 else 0))
      | (val.Bool v1, val.Int v2) \<Rightarrow> val.Bool ((if v1 then 1 else 0) \<ge> v2)
      | (val.Bool v1, val.Bool v2) \<Rightarrow> val.Bool (\<not>v1 \<longrightarrow> \<not>v2)))"

definition make_un_op :: "un_op \<Rightarrow> val \<Rightarrow> val" where
"make_un_op op v1 =
  (case op of
    un_op.Minus \<Rightarrow>
      (case v1 of
        val.Int v1 \<Rightarrow> val.Int (-v1)
      | val.Bool v1 \<Rightarrow> val.Int (if v1 then 0 else 1))
  | un_op.Not \<Rightarrow> 
      (case v1 of
        val.Int v1 \<Rightarrow> val.Bool (v1 = 0)
      | val.Bool v1 \<Rightarrow> val.Bool (\<not>v1)))"

datatype expr = 
  Binary bin_op expr expr
  | Unary un_op expr
  | Var var_name

datatype stmt =
  Assign var_name expr |
  While expr "stmt list" |
  Comb stmt stmt |
  Blank

datatype exec_res =  Work | Stop | Error

inductive eval :: "[model_context \<Rightarrow> expr \<Rightarrow> val] \<Rightarrow> bool"
and exec :: "[model_context * exec_res \<Rightarrow> expr \<Rightarrow> model_context * exec_res] \<Rightarrow> bool"
  

end