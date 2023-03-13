theory basic_poST_types_utils
  imports "~~/poST/poST_model/basic_poST_types" "~~/poST/poST_utils/bit_types_utils" "~~/poST/poST_utils/poST_time_utils"
begin

definition const_to_basic :: "const \<Rightarrow> basic_post_type" where
  "const_to_basic c = (case c of 
    (const.Nat c) \<Rightarrow> basic_post_type.Nat c |
    (const.Int c) \<Rightarrow> basic_post_type.Int c |
    (const.Time c) \<Rightarrow> basic_post_type.Time c |
    (const.Bool c) \<Rightarrow> basic_post_type.Bool c |
    (const.Real c) \<Rightarrow> basic_post_type.Real c)"
declare const_to_basic_def [simp]

definition basic_to_time :: "basic_post_type \<Rightarrow> time" where
  "basic_to_time c = 
    (case c of
      (basic_post_type.Nat v) \<Rightarrow> (nat_to_time v)
    | (basic_post_type.Int v) \<Rightarrow> (nat_to_time (nat v))
    | (basic_post_type.Time v) \<Rightarrow> v)"
declare basic_to_time_def [simp]

definition basic_post_type_to_bptint :: "basic_post_type \<Rightarrow> basic_post_type" where
  "basic_post_type_to_bptint value = 
    (case value of 
      (basic_post_type.Nat val) \<Rightarrow> basic_post_type.Int val |
      (basic_post_type.Int val) \<Rightarrow> basic_post_type.Int val |
      (basic_post_type.Real val) \<Rightarrow> basic_post_type.Int (floor val) )"
declare basic_post_type_to_bptint_def [simp]

definition basic_post_type_to_int :: "basic_post_type \<Rightarrow> int" where
"basic_post_type_to_int value = 
    (case value of 
      (basic_post_type.Nat val) \<Rightarrow> (int val) |
      (basic_post_type.Int val) \<Rightarrow> val |
      (basic_post_type.Real val) \<Rightarrow> (floor val) )"
declare basic_post_type_to_int_def [simp]

definition basic_post_type_to_Bool :: "basic_post_type \<Rightarrow> basic_post_type" where
"basic_post_type_to_Bool var = (case var of
  (basic_post_type.Nat val) \<Rightarrow> (basic_post_type.Bool (if val > 0 then True else False)) |
  (basic_post_type.Int val) \<Rightarrow> (basic_post_type.Bool (if val \<noteq> 0 then True else False)) |
  (basic_post_type.Real val) \<Rightarrow> (basic_post_type.Bool (if val \<noteq> 0 then True else False)) | 
  (basic_post_type.Time val) \<Rightarrow> (basic_post_type.Bool (\<not> (time_eq val (time.Time 0 0 0 0 0)))) |
  (basic_post_type.Bool val) \<Rightarrow> (basic_post_type.Bool val))"
declare basic_post_type_to_Bool_def [simp]

definition basic_post_type_to_bool :: "basic_post_type \<Rightarrow> bool" where
"basic_post_type_to_bool var = (case var of
  (basic_post_type.Nat val) \<Rightarrow>  (if val > 0 then True else False) |
  (basic_post_type.Int val) \<Rightarrow> (if val \<noteq> 0 then True else False) |
  (basic_post_type.Real val) \<Rightarrow>  (if val \<noteq> 0 then True else False) | 
  (basic_post_type.Time val) \<Rightarrow>  (\<not> (time_eq val (time.Time 0 0 0 0 0))) |
  (basic_post_type.Bool val) \<Rightarrow>  val)"
declare basic_post_type_to_bool_def [simp]

definition basic_post_type_sum :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "basic_post_type_sum var1 var2 = (case (var1,var2) of
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Nat (var1 + var2) |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int (var1 + var2) |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 + var2) |
    ((basic_post_type.Bool var1 ),(basic_post_type.Bool var2)) \<Rightarrow> basic_post_type.Bool (var1 \<or> var2) |
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> basic_post_type.Byte (byte_sum var1 var2) |
    ((basic_post_type.Time var1),(basic_post_type.Time var2)) \<Rightarrow> basic_post_type.Time (time_sum var1 var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int ((int var1) + var2) | 
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Int (var1 + (int var2)) |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 + var2) |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Real (var1 + var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 + var2) |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Real (var1 + var2)) "
declare basic_post_type_sum_def [simp]

definition const_basic_sum :: "const \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "const_basic_sum c var = basic_post_type_sum (const_to_basic c) var"
declare const_basic_sum_def [simp]

definition basic_const_sum :: "basic_post_type \<Rightarrow> const \<Rightarrow> basic_post_type" where
  "basic_const_sum var c = basic_post_type_sum var (const_to_basic c)"
declare basic_const_sum_def [simp]

(*
((basic_post_type.Bool var1 ),(basic_post_type.Bool var2)) \<Rightarrow> basic_post_type.Bool (xor var1 var2) |
((basic_post_type.Time var1),(basic_post_type.Time var2)) \<Rightarrow> basic_post_type.Time (time_sum var1 var2) |
*)
definition basic_post_type_sub :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "basic_post_type_sub var1 var2 = (case (var1,var2) of
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Nat (var1 - var2) |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int (var1 - var2) |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 - var2) |
    
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> basic_post_type.Byte (byte_sub var1 var2) |
    
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int ((int var1) - var2) | 
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Int (var1 - (int var2)) |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 - var2) |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Real (var1 - var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 - var2) |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Real (var1 - var2))"
declare basic_post_type_sub_def [simp]

definition const_basic_sub :: "const \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "const_basic_sub c var = basic_post_type_sub (const_to_basic c) var"
declare const_basic_sub_def [simp]

definition basic_const_sub :: "basic_post_type \<Rightarrow> const \<Rightarrow> basic_post_type" where
  "basic_const_sub var c = basic_post_type_sub var (const_to_basic c)"
declare basic_const_sub_def [simp]

definition basic_post_type_mul :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "basic_post_type_mul var1 var2 = (case (var1,var2) of
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Nat (var1 * var2) |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int (var1 * var2) |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 * var2) |
    
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> basic_post_type.Byte (byte_mul var1 var2) |
    
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int (var1 * var2) | 
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Int (var1 * var2) |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 * var2) |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Real (var1 * var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 * var2) |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Real (var1 * var2))"
declare basic_post_type_mul_def [simp]

definition const_basic_mul :: "const \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "const_basic_mul c var = basic_post_type_mul (const_to_basic c) var"
declare const_basic_mul_def [simp]
definition basic_const_mul :: "basic_post_type \<Rightarrow> const \<Rightarrow> basic_post_type" where
  "basic_const_mul var c = basic_post_type_mul var (const_to_basic c)"
declare basic_const_mul_def [simp]

definition basic_post_type_div :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "basic_post_type_div var1 var2 = (case (var1,var2) of
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Nat (var1 div var2) |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int (var1 div var2) |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 div var2) |
    
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> basic_post_type.Byte (byte_divide var1 var2) |
    
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int (var1 div var2) | 
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Int (var1 div var2) |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 div var2) |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Real (var1 div var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> basic_post_type.Real (var1 div var2) |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Real (var1 div var2))"
declare basic_post_type_div_def [simp]

definition const_basic_div :: "const \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "const_basic_div c var = basic_post_type_div (const_to_basic c) var"
declare const_basic_div_def [simp]

definition basic_const_div :: "basic_post_type \<Rightarrow> const \<Rightarrow> basic_post_type" where
  "basic_const_div var c = basic_post_type_div var (const_to_basic c)"
declare basic_const_div_def [simp]

definition basic_post_type_mod :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "basic_post_type_mod var1 var2 = (case (var1,var2) of
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Nat (var1 mod var2) |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int (var1 mod var2) |
    
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> basic_post_type.Byte (byte_mod var1 var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> basic_post_type.Int (var1 mod var2) | 
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> basic_post_type.Int (var1 mod var2))"
declare basic_post_type_mod_def [simp]

definition const_basic_mod :: "const \<Rightarrow> basic_post_type \<Rightarrow> basic_post_type" where
  "const_basic_mod c var = basic_post_type_mod (const_to_basic c) var"
declare const_basic_mod_def [simp]

definition basic_const_mod :: "basic_post_type \<Rightarrow> const \<Rightarrow> basic_post_type" where
  "basic_const_mod var c = basic_post_type_mod var (const_to_basic c)"
declare basic_const_mod_def [simp]

definition basic_post_type_minus :: "basic_post_type \<Rightarrow> basic_post_type" where
"basic_post_type_minus var = (case var of 
  (basic_post_type.Int val) \<Rightarrow> (basic_post_type.Int (val * -1)) |
  (basic_post_type.Real val) \<Rightarrow> (basic_post_type.Real (val * -1)) |
  (basic_post_type.Bool val) \<Rightarrow> (basic_post_type.Bool (\<not> val)))"
declare basic_post_type_minus_def [simp]

definition basic_post_type_not:: "basic_post_type \<Rightarrow> basic_post_type" where
"basic_post_type_not var = (let res = basic_post_type_to_Bool var in
  (case res of (basic_post_type.Bool val) \<Rightarrow> (basic_post_type.Bool val) ))"
declare basic_post_type_not_def [simp]

definition basic_post_type_eq :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_eq var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 = var2 |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> var1 = var2 |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> var1 = var2 |
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> (byte_eq var1 var2) |
    ((basic_post_type.Time var1),(basic_post_type.Time var2)) \<Rightarrow> (time_eq var1 var2) |
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 = var2 |
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> (int var1) = var2 |
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 = (int var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> var1 = var2 |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 = var2 |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> var1 = var2 |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> var1 = var2 |
    ((basic_post_type.String var1),(basic_post_type.String var2)) \<Rightarrow> var1 = var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_eq_def [simp]

definition const_basic_eq :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_eq c var = basic_post_type_eq (const_to_basic c) var"
declare const_basic_eq_def [simp]

definition basic_const_eq :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_eq var c = basic_post_type_eq var (const_to_basic c)"
declare basic_const_eq_def [simp]

definition basic_post_type_less :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_less var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 < var2 |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> var1 < var2 |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> var1 < var2 |
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> (byte_less var1 var2) |
    ((basic_post_type.Time var1),(basic_post_type.Time var2)) \<Rightarrow> (time_less var1 var2) |
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 < var2 |
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> (int var1) < var2 |
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 < (int var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> var1 < var2 |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 < var2 |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> var1 < var2 |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> var1 < var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_less_def [simp]

definition const_basic_less :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_less c var = basic_post_type_less (const_to_basic c) var"
declare const_basic_less_def [simp]

definition basic_const_less :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_less var c = basic_post_type_less var (const_to_basic c)"
declare basic_const_less_def [simp]

definition basic_post_type_more :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_more var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 > var2 |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> var1 > var2 |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> var1 > var2 |
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> (byte_more var1 var2) |
    ((basic_post_type.Time var1),(basic_post_type.Time var2)) \<Rightarrow> (time_more var1 var2) |
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 > var2 |
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> (int var1) > var2 |
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 > (int var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> var1 > var2 |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 > var2 |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> var1 > var2 |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> var1 > var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_more_def [simp]

definition const_basic_more :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_more c var = basic_post_type_more (const_to_basic c) var"
declare const_basic_more_def [simp]

definition basic_const_more :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_more var c = basic_post_type_more var (const_to_basic c)"
declare basic_const_more_def [simp]

definition basic_post_type_lesseq :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_lesseq var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<le> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> var1 \<le> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<le> var2 |
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> (byte_eqless var1 var2) |
    ((basic_post_type.Time var1),(basic_post_type.Time var2)) \<Rightarrow> (time_eqless var1 var2) |
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 \<le> var2 |
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> (int var1) \<le> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<le> (int var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<le> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<le> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<le> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> var1 \<le> var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_lesseq_def [simp]

definition const_basic_lesseq :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_lesseq c var = basic_post_type_lesseq (const_to_basic c) var"
declare const_basic_lesseq_def [simp]

definition basic_const_lesseq :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_lesseq var c = basic_post_type_lesseq var (const_to_basic c)"
declare basic_const_lesseq_def [simp]

definition basic_post_type_moreeq :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_moreeq var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<ge> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> var1 \<ge> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<ge> var2 |
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> (byte_eqmore var1 var2) |
    ((basic_post_type.Time var1),(basic_post_type.Time var2)) \<Rightarrow> (time_eqmore var1 var2) |
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 \<ge> var2 |
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> (int var1) \<ge> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<ge> (int var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<ge> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<ge> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<ge> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> var1 \<ge> var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_moreeq_def [simp]

definition const_basic_moreeq :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_moreeq c var = basic_post_type_moreeq (const_to_basic c) var"
declare const_basic_moreeq_def [simp]

definition basic_const_moreeq :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_moreeq var c = basic_post_type_moreeq var (const_to_basic c)"
declare basic_const_moreeq_def [simp]

definition basic_post_type_noteq :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_noteq var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Nat var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<noteq> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Int var2)) \<Rightarrow> var1 \<noteq> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<noteq> var2 |
    ((basic_post_type.Byte var1),(basic_post_type.Byte var2)) \<Rightarrow> (byte_noteq var1 var2) |
    ((basic_post_type.Time var1),(basic_post_type.Time var2)) \<Rightarrow> (time_noteq var1 var2) |
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 \<noteq> var2 |
    ((basic_post_type.Nat var1),(basic_post_type.Int var2)) \<Rightarrow> (int var1) \<noteq> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<noteq> (int var2) |
    ((basic_post_type.Nat var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<noteq> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Nat var2)) \<Rightarrow> var1 \<noteq> var2 |
    ((basic_post_type.Int var1),(basic_post_type.Real var2)) \<Rightarrow> var1 \<noteq> var2 |
    ((basic_post_type.Real var1),(basic_post_type.Int var2)) \<Rightarrow> var1 \<noteq> var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_noteq_def [simp]

definition const_basic_noteq :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_noteq c var = basic_post_type_noteq (const_to_basic c) var"
declare const_basic_noteq_def [simp]

definition basic_const_noteq :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_noteq var c = basic_post_type_noteq var (const_to_basic c)"
declare basic_const_noteq_def [simp]

definition basic_post_type_and :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_and var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 \<and> var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_and_def [simp]

definition const_basic_and :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_and c var = basic_post_type_and (const_to_basic c) var"
declare const_basic_and_def [simp]

definition basic_const_and :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_and var c = basic_post_type_and var (const_to_basic c)"
declare basic_const_and_def [simp]

definition basic_post_type_or :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_or var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 \<or> var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_or_def [simp]

definition const_basic_or :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_or c var = basic_post_type_or (const_to_basic c) var"
declare const_basic_or_def [simp]

definition basic_const_or :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_or var c = basic_post_type_or var (const_to_basic c)"
declare basic_const_or_def [simp]

definition basic_post_type_xor :: "basic_post_type \<Rightarrow> basic_post_type \<Rightarrow> bool" where
  "basic_post_type_xor var1 var2 = (case (var1,var2) of 
    ((basic_post_type.Bool var1),(basic_post_type.Bool var2)) \<Rightarrow> var1 \<noteq> var2 |
    (_,_) \<Rightarrow> False )"
declare basic_post_type_xor_def [simp]

definition const_basic_xor :: "const \<Rightarrow> basic_post_type \<Rightarrow> bool" where 
"const_basic_xor c var = basic_post_type_xor (const_to_basic c) var"
declare const_basic_xor_def [simp]

definition basic_const_xor :: "basic_post_type \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_xor var c = basic_post_type_xor var (const_to_basic c)"
declare basic_const_xor_def [simp]

end