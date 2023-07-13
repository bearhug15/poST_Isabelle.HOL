theory ptypes_utils
  imports "~~/poST/poST_model/ptypes" "~~/poST/poST_utils/bit_types_utils" "~~/poST/poST_utils/poST_time_utils"
begin

definition is_value :: "ptype \<Rightarrow> bool" where
  "is_value v =
    (case v of 
      ptype.Return \<Rightarrow> False
    | ptype.Exit \<Rightarrow> False
    | _ \<Rightarrow> True)"
declare is_value_def [simp]

definition const_to_basic :: "const \<Rightarrow> ptype" where
  "const_to_basic c = 
    (case c of 
      (const.Nat c) \<Rightarrow> ptype.Nat c 
    | (const.Int c) \<Rightarrow> ptype.Int c 
    | (const.Time c) \<Rightarrow> ptype.Time c 
    | (const.Bool c) \<Rightarrow> ptype.Bool c 
    | (const.Real c) \<Rightarrow> ptype.Real c)"
declare const_to_basic_def [simp]

definition basic_to_time :: "ptype \<Rightarrow> time" where
  "basic_to_time c = 
    (case c of
      (ptype.Nat v) \<Rightarrow> (nat_to_time v)
    | (ptype.Int v) \<Rightarrow> (nat_to_time (nat v))
    | (ptype.Time v) \<Rightarrow> v)"
declare basic_to_time_def [simp]

definition ptype_to_pint :: "ptype \<Rightarrow> ptype" where
  "ptype_to_pint value = 
    (case value of 
      (ptype.Nat val) \<Rightarrow> ptype.Int val 
    | (ptype.Int val) \<Rightarrow> ptype.Int val 
    | (ptype.Real val) \<Rightarrow> ptype.Int (floor val) )"
declare ptype_to_pint_def [simp]

definition ptype_to_int :: "ptype \<Rightarrow> int" where
  "ptype_to_int value = 
    (case value of 
      (ptype.Nat val) \<Rightarrow> (int val) 
    | (ptype.Int val) \<Rightarrow> val 
    | (ptype.Real val) \<Rightarrow> (floor val) )"
declare ptype_to_int_def [simp]

definition ptype_to_bool :: "ptype \<Rightarrow> bool" where
  "ptype_to_bool var = 
    (case var of
      (ptype.Bool val) \<Rightarrow>  val)"
declare ptype_to_bool_def [simp]

definition ptype_sum :: "ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
  "ptype_sum var1 var2 = 
    (case (var1,var2) of
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> ptype.Nat (var1 + var2) 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> ptype.Int (var1 + var2) 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 + var2) 
    | ((ptype.Time var1),(ptype.Time var2)) \<Rightarrow> ptype.Time (time_sum var1 var2) 
    | ((ptype.String var1), (ptype.String var2)) => ptype.String (var1@var2) 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> ptype.Int ((int var1) + var2) 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> ptype.Int (var1 + (int var2))
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 + var2) 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> ptype.Real (var1 + var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 + var2) 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> ptype.Real (var1 + var2)) "
declare ptype_sum_def [simp]

definition const_basic_sum :: "const \<Rightarrow> ptype \<Rightarrow> ptype" where
  "const_basic_sum c var = ptype_sum (const_to_basic c) var"
declare const_basic_sum_def [simp]

definition basic_const_sum :: "ptype \<Rightarrow> const \<Rightarrow> ptype" where
  "basic_const_sum var c = ptype_sum var (const_to_basic c)"
declare basic_const_sum_def [simp]

definition ptype_sub :: "ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
  "ptype_sub var1 var2 = 
    (case (var1,var2) of
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> ptype.Nat (var1 - var2) 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> ptype.Int (var1 - var2) 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 - var2) 
    | ((ptype.Time var1),(ptype.Time var2)) \<Rightarrow> ptype.Time (time_sub var1 var2) 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> ptype.Int ((int var1) - var2) 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> ptype.Int (var1 - (int var2)) 
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 - var2) 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> ptype.Real (var1 - var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 - var2) 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> ptype.Real (var1 - var2))"
declare ptype_sub_def [simp]

definition const_basic_sub :: "const \<Rightarrow> ptype \<Rightarrow> ptype" where
  "const_basic_sub c var = ptype_sub (const_to_basic c) var"
declare const_basic_sub_def [simp]

definition basic_const_sub :: "ptype \<Rightarrow> const \<Rightarrow> ptype" where
  "basic_const_sub var c = ptype_sub var (const_to_basic c)"
declare basic_const_sub_def [simp]

definition ptype_mul :: "ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
  "ptype_mul var1 var2 = 
    (case (var1,var2) of
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> ptype.Nat (var1 * var2) 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> ptype.Int (var1 * var2) 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 * var2) 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> ptype.Int (var1 * var2) 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> ptype.Int (var1 * var2) 
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 * var2) 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> ptype.Real (var1 * var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 * var2) 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> ptype.Real (var1 * var2))"
declare ptype_mul_def [simp]

definition const_basic_mul :: "const \<Rightarrow> ptype \<Rightarrow> ptype" where
  "const_basic_mul c var = ptype_mul (const_to_basic c) var"
declare const_basic_mul_def [simp]
definition basic_const_mul :: "ptype \<Rightarrow> const \<Rightarrow> ptype" where
  "basic_const_mul var c = ptype_mul var (const_to_basic c)"
declare basic_const_mul_def [simp]

definition ptype_div :: "ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
  "ptype_div var1 var2 = 
    (case (var1,var2) of
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> ptype.Nat (var1 div var2) 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> ptype.Int (var1 div var2) 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 / var2) 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> ptype.Int (var1 div var2) 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> ptype.Int (var1 div var2) 
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 div var2) 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> ptype.Real (var1 div var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> ptype.Real (var1 div var2) 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> ptype.Real (var1 div var2))"
declare ptype_div_def [simp]

definition const_basic_div :: "const \<Rightarrow> ptype \<Rightarrow> ptype" where
  "const_basic_div c var = ptype_div (const_to_basic c) var"
declare const_basic_div_def [simp]

definition basic_const_div :: "ptype \<Rightarrow> const \<Rightarrow> ptype" where
  "basic_const_div var c = ptype_div var (const_to_basic c)"
declare basic_const_div_def [simp]

definition ptype_mod :: "ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
  "ptype_mod var1 var2 = 
    (case (var1,var2) of
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> ptype.Nat (var1 mod var2) 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> ptype.Int (var1 mod var2) 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> ptype.Int (var1 mod var2) 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> ptype.Int (var1 mod var2))"
declare ptype_mod_def [simp]

definition const_basic_mod :: "const \<Rightarrow> ptype \<Rightarrow> ptype" where
  "const_basic_mod c var = ptype_mod (const_to_basic c) var"
declare const_basic_mod_def [simp]

definition basic_const_mod :: "ptype \<Rightarrow> const \<Rightarrow> ptype" where
  "basic_const_mod var c = ptype_mod var (const_to_basic c)"
declare basic_const_mod_def [simp]

definition ptype_minus :: "ptype \<Rightarrow> ptype" where
"ptype_minus var = 
  (case var of 
    (ptype.Nat val) \<Rightarrow> (ptype.Int ((int val)*-1))
  | (ptype.Int val) \<Rightarrow> (ptype.Int (val * -1))
  | (ptype.Real val) \<Rightarrow> (ptype.Real (val * -1)))"
declare ptype_minus_def [simp]

definition ptype_not:: "ptype \<Rightarrow> ptype" where
  "ptype_not var = 
    (case var of 
      (ptype.Bool val) \<Rightarrow> (ptype.Bool (\<not>val))
    | (ptype.Byte val) \<Rightarrow> (ptype.Byte (byte_not val))
    | (ptype.Word val) \<Rightarrow> (ptype.Word (word_not val))
    | (ptype.Dword val) \<Rightarrow> (ptype.Dword (dword_not val))
    | (ptype.Lword val) \<Rightarrow> (ptype.Lword (lword_not val)))"
declare ptype_not_def [simp]

definition ptype_eq :: "ptype \<Rightarrow> ptype \<Rightarrow> bool" where
  "ptype_eq var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> var1 = var2 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> var1 = var2 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> var1 = var2 
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (byte_eq var1 var2)
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (word_eq var1 var2)
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (dword_eq var1 var2)
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (lword_eq var1 var2) 
    | ((ptype.Time var1),(ptype.Time var2)) \<Rightarrow> (time_eq var1 var2) 
    | ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> var1 = var2 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> (int var1) = var2 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> var1 = (int var2) 
    | ((ptype.String var1),(ptype.String var2)) \<Rightarrow> var1 = var2)"
declare ptype_eq_def [simp]

definition const_basic_eq :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
"const_basic_eq c var = ptype_eq (const_to_basic c) var"
declare const_basic_eq_def [simp]

definition basic_const_eq :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_eq var c = ptype_eq var (const_to_basic c)"
declare basic_const_eq_def [simp]

definition ptype_less :: "ptype \<Rightarrow> ptype \<Rightarrow> bool" where
  "ptype_less var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> var1 < var2 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> var1 < var2 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> var1 < var2 
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (byte_less var1 var2)
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (word_less var1 var2)
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (dword_less var1 var2)
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (lword_less var1 var2) 
    | ((ptype.Time var1),(ptype.Time var2)) \<Rightarrow> (time_less var1 var2) 
    | ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> var1 < var2 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> (int var1) < var2 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> var1 < (int var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> var1 < var2 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> var1 < var2 
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> var1 < var2 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> var1 < var2 )"
declare ptype_less_def [simp]

definition const_basic_less :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
"const_basic_less c var = ptype_less (const_to_basic c) var"
declare const_basic_less_def [simp]

definition basic_const_less :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_less var c = ptype_less var (const_to_basic c)"
declare basic_const_less_def [simp]

definition ptype_more :: "ptype \<Rightarrow> ptype \<Rightarrow> bool" where
  "ptype_more var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> var1 > var2 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> var1 > var2 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> var1 > var2 
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (byte_more var1 var2)
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (word_more var1 var2)
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (dword_more var1 var2)
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (lword_more var1 var2)  
    | ((ptype.Time var1),(ptype.Time var2)) \<Rightarrow> (time_more var1 var2) 
    | ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> var1 > var2 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> (int var1) > var2 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> var1 > (int var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> var1 > var2 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> var1 > var2 
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> var1 > var2 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> var1 > var2)"
declare ptype_more_def [simp]

definition const_basic_more :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
"const_basic_more c var = ptype_more (const_to_basic c) var"
declare const_basic_more_def [simp]

definition basic_const_more :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_more var c = ptype_more var (const_to_basic c)"
declare basic_const_more_def [simp]

definition ptype_eqless :: "ptype \<Rightarrow> ptype \<Rightarrow> bool" where
  "ptype_eqless var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> var1 \<le> var2 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> var1 \<le> var2 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> var1 \<le> var2 
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (byte_eqless var1 var2) 
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (word_eqless var1 var2)
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (dword_eqless var1 var2)
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (lword_eqless var1 var2) 
    | ((ptype.Time var1),(ptype.Time var2)) \<Rightarrow> (time_eqless var1 var2) 
    | ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> var1 \<le> var2 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> (int var1) \<le> var2 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> var1 \<le> (int var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> var1 \<le> var2 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> var1 \<le> var2 
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> var1 \<le> var2 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> var1 \<le> var2 )"
declare ptype_eqless_def [simp]

definition const_basic_eqless :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
"const_basic_eqless c var = ptype_eqless (const_to_basic c) var"
declare const_basic_eqless_def [simp]

definition basic_const_eqless :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
"basic_const_eqless var c = ptype_eqless var (const_to_basic c)"
declare basic_const_eqless_def [simp]

definition ptype_eqmore :: "ptype \<Rightarrow> ptype \<Rightarrow> bool" where
  "ptype_eqmore var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> var1 \<ge> var2 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> var1 \<ge> var2 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> var1 \<ge> var2 
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (byte_eqmore var1 var2) 
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (word_eqmore var1 var2)
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (dword_eqmore var1 var2)
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (lword_eqmore var1 var2) 
    | ((ptype.Time var1),(ptype.Time var2)) \<Rightarrow> (time_eqmore var1 var2) 
    | ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> var1 \<ge> var2 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> (int var1) \<ge> var2 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> var1 \<ge> (int var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> var1 \<ge> var2 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> var1 \<ge> var2 
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> var1 \<ge> var2 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> var1 \<ge> var2 )"
declare ptype_eqmore_def [simp]

definition const_basic_eqmore :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
  "const_basic_eqmore c var = ptype_eqmore (const_to_basic c) var"
declare const_basic_eqmore_def [simp]

definition basic_const_eqmore :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
  "basic_const_eqmore var c = ptype_eqmore var (const_to_basic c)"
declare basic_const_eqmore_def [simp]

definition ptype_noteq :: "ptype \<Rightarrow> ptype \<Rightarrow> bool" where
  "ptype_noteq var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Nat var1),(ptype.Nat var2)) \<Rightarrow> var1 \<noteq> var2 
    | ((ptype.Int var1),(ptype.Int var2)) \<Rightarrow> var1 \<noteq> var2 
    | ((ptype.Real var1),(ptype.Real var2)) \<Rightarrow> var1 \<noteq> var2 
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (byte_noteq var1 var2)
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (word_noteq var1 var2)
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (dword_noteq var1 var2)
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (lword_noteq var1 var2)  
    | ((ptype.Time var1),(ptype.Time var2)) \<Rightarrow> (time_noteq var1 var2) 
    | ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> var1 \<noteq> var2 
    | ((ptype.Nat var1),(ptype.Int var2)) \<Rightarrow> (int var1) \<noteq> var2 
    | ((ptype.Int var1),(ptype.Nat var2)) \<Rightarrow> var1 \<noteq> (int var2) 
    | ((ptype.Nat var1),(ptype.Real var2)) \<Rightarrow> var1 \<noteq> var2 
    | ((ptype.Real var1),(ptype.Nat var2)) \<Rightarrow> var1 \<noteq> var2 
    | ((ptype.Int var1),(ptype.Real var2)) \<Rightarrow> var1 \<noteq> var2 
    | ((ptype.Real var1),(ptype.Int var2)) \<Rightarrow> var1 \<noteq> var2 )"
declare ptype_noteq_def [simp]

definition const_basic_noteq :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
  "const_basic_noteq c var = ptype_noteq (const_to_basic c) var"
declare const_basic_noteq_def [simp]

definition basic_const_noteq :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
  "basic_const_noteq var c = ptype_noteq var (const_to_basic c)"
declare basic_const_noteq_def [simp]

definition ptype_and :: "ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
  "ptype_and var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> (ptype.Bool (var1 \<and> var2))
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (ptype.Byte (byte_and var1 var2))
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (ptype.Word (word_and var1 var2))
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (ptype.Dword (dword_and var1 var2))
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (ptype.Lword (lword_and var1 var2)))"
declare ptype_and_def [simp]

(*
definition const_basic_and :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
  "const_basic_and c var = ptype_and (const_to_basic c) var"
declare const_basic_and_def [simp]

definition basic_const_and :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
  "basic_const_and var c = ptype_and var (const_to_basic c)"
declare basic_const_and_def [simp]
*)

definition ptype_or :: "ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
  "ptype_or var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> (ptype.Bool (var1 \<or> var2)) 
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (ptype.Byte (byte_or var1 var2))
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (ptype.Word (word_or var1 var2))
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (ptype.Dword (dword_or var1 var2))
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (ptype.Lword (lword_or var1 var2)))"
declare ptype_or_def [simp]

(*
definition const_basic_or :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
  "const_basic_or c var = ptype_or (const_to_basic c) var"
declare const_basic_or_def [simp]

definition basic_const_or :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
  "basic_const_or var c = ptype_or var (const_to_basic c)"
declare basic_const_or_def [simp]
*)

definition ptype_xor :: "ptype \<Rightarrow> ptype \<Rightarrow> ptype" where
  "ptype_xor var1 var2 = 
    (case (var1,var2) of 
      ((ptype.Bool var1),(ptype.Bool var2)) \<Rightarrow> (ptype.Bool (var1 \<noteq> var2)) 
    | ((ptype.Byte var1),(ptype.Byte var2)) \<Rightarrow> (ptype.Byte (byte_xor var1 var2))
    | ((ptype.Word var1),(ptype.Word var2)) \<Rightarrow> (ptype.Word (word_xor var1 var2))
    | ((ptype.Dword var1),(ptype.Dword var2)) \<Rightarrow> (ptype.Dword (dword_xor var1 var2))
    | ((ptype.Lword var1),(ptype.Lword var2)) \<Rightarrow> (ptype.Lword (lword_xor var1 var2)))"
declare ptype_xor_def [simp]

(*
definition const_basic_xor :: "const \<Rightarrow> ptype \<Rightarrow> bool" where 
  "const_basic_xor c var = ptype_xor (const_to_basic c) var"
declare const_basic_xor_def [simp]

definition basic_const_xor :: "ptype \<Rightarrow> const \<Rightarrow> bool" where 
  "basic_const_xor var c = ptype_xor var (const_to_basic c)"
declare basic_const_xor_def [simp]
*)

end