theory ptypes_lemmas
  imports "~~/poST/poST_utils/ptypes_utils"
begin

lemma const_nat_simp[simp]: "const_to_basic (const.Nat val) = ptype.Nat val"by auto
lemma const_int_simp[simp]: "const_to_basic (const.Int val) = ptype.Int val"by auto
lemma const_real_simp[simp]: "const_to_basic (const.Real val) = ptype.Real val" by auto
lemma const_time_simp[simp]: "const_to_basic (const.Time val) = ptype.Time val"by auto
lemma const_bool_simp[simp]: "const_to_basic (const.Bool val) = ptype.Bool val"by auto

lemma ptype_nat_nat_sum[simp]: "v1 + v2 = v3 \<longleftrightarrow> ptype_sum (ptype.Nat v1) (ptype.Nat v2) = (ptype.Nat v3)" by simp
lemma ptype_int_int_sum[simp]: "v1 + v2 = v3 \<longleftrightarrow> ptype_sum (ptype.Int v1) (ptype.Int v2) = (ptype.Int v3)" by simp
lemma ptype_real_real_sum[simp]: "v1 + v2 = v3 \<longleftrightarrow> ptype_sum (ptype.Real v1) (ptype.Real v2) = (ptype.Real v3)" by simp
lemma ptype_time_time_sum[simp]: "time_sum v1 v2 = v3 \<longleftrightarrow> ptype_sum (ptype.Time v1) (ptype.Time v2) = (ptype.Time v3)" by auto
lemma ptype_string_string_sum[simp]: "v1 @ v2 = v3 \<longleftrightarrow> ptype_sum (ptype.String v1) (ptype.String v2) = (ptype.String v3)" by simp

lemma ptype_nat_nat_sub[simp]: "v1 - v2 = v3 \<longleftrightarrow> ptype_sub (ptype.Nat v1) (ptype.Nat v2) = (ptype.Nat v3)" by simp
lemma ptype_int_int_sub[simp]: "v1 - v2 = v3 \<longleftrightarrow> ptype_sub (ptype.Int v1) (ptype.Int v2) = (ptype.Int v3)" by simp
lemma ptype_real_real_sub[simp]: "v1 - v2 = v3 \<longleftrightarrow> ptype_sub (ptype.Real v1) (ptype.Real v2) = (ptype.Real v3)" by simp
lemma ptype_time_time_sub[simp]: "time_sub v1 v2 = v3 \<longleftrightarrow> ptype_sub (ptype.Time v1) (ptype.Time v2) = (ptype.Time v3)" by auto

lemma ptype_nat_nat_mul[simp]: "v1 * v2 = v3 \<longleftrightarrow> ptype_mul (ptype.Nat v1) (ptype.Nat v2) = (ptype.Nat v3)" by simp
lemma ptype_int_int_mul[simp]: "v1 * v2 = v3 \<longleftrightarrow> ptype_mul (ptype.Int v1) (ptype.Int v2) = (ptype.Int v3)" by simp
lemma ptype_real_real_mul[simp]: "v1 * v2 = v3 \<longleftrightarrow> ptype_mul (ptype.Real v1) (ptype.Real v2) = (ptype.Real v3)" by simp

lemma ptype_nat_nat_div[simp]: "v1 div v2 = v3 \<longleftrightarrow> ptype_div (ptype.Nat v1) (ptype.Nat v2) = (ptype.Nat v3)" by simp
lemma ptype_int_int_div[simp]: "v1 div v2 = v3 \<longleftrightarrow> ptype_div (ptype.Int v1) (ptype.Int v2) = (ptype.Int v3)" by simp
lemma ptype_real_real_div[simp]: "v1 / v2 = v3 \<longleftrightarrow> ptype_div (ptype.Real v1) (ptype.Real v2) = (ptype.Real v3)" by simp

lemma ptype_nat_mod[simp]: "v1 mod v2 = v3 \<longleftrightarrow> ptype_mod (ptype.Nat v1) (ptype.Nat v2) = (ptype.Nat v3)" by simp
lemma ptype_int_mod[simp]: "v1 mod v2 = v3 \<longleftrightarrow> ptype_mod (ptype.Int v1) (ptype.Int v2) = (ptype.Int v3)" by simp

lemma ptype_nat_minus[simp]: "-v1 = v2 \<longleftrightarrow> ptype_minus (ptype.Nat v1) = (ptype.Int v2)" by auto
lemma ptype_int_minus[simp]: "-v1 = v2 \<longleftrightarrow> ptype_minus (ptype.Int v1) = (ptype.Int v2)" by auto
lemma ptype_real_minus[simp]: "-v1 = v2 \<longleftrightarrow> ptype_minus (ptype.Real v1) = (ptype.Real v2)" by auto

lemma ptype_bool_not[simp]: "\<not>v1 = v2 \<longleftrightarrow> ptype_not (ptype.Bool v1) = (ptype.Bool v2)" by auto
lemma ptype_byte_not[simp]: "byte_not v1 = v2 \<longleftrightarrow> ptype_not (ptype.Byte v1) = (ptype.Byte v2)" by auto
lemma ptype_word_not[simp]: "word_not v1 = v2 \<longleftrightarrow> ptype_not (ptype.Word v1) = (ptype.Word v2)" by auto
lemma ptype_dword_not[simp]: "dword_not v1 = v2 \<longleftrightarrow> ptype_not (ptype.Dword v1) = (ptype.Dword v2)" by auto
lemma ptype_lword_not[simp]: "lword_not v1 = v2 \<longleftrightarrow> ptype_not (ptype.Lword v1) = (ptype.Lword v2)" by auto

lemma ptype_nat_eq[simp]: "ptype_eq (ptype.Nat v1) (ptype.Nat v2) \<longleftrightarrow> v1 = v2" by auto
lemma ptype_int_eq[simp]: "ptype_eq (ptype.Int v1) (ptype.Int v2) \<longleftrightarrow> v1 = v2" by auto
lemma ptype_real_eq[simp]: "ptype_eq (ptype.Real v1) (ptype.Real v2) \<longleftrightarrow> v1 = v2" by auto
lemma ptype_byte_eq[simp]: "ptype_eq (ptype.Byte v1) (ptype.Byte v2) \<longleftrightarrow> byte_eq v1 v2" by auto
lemma ptype_word_eq[simp]: "ptype_eq (ptype.Word v1) (ptype.Word v2) \<longleftrightarrow> word_eq v1 v2" by auto
lemma ptype_dword_eq[simp]: "ptype_eq (ptype.Dword v1) (ptype.Dword v2) \<longleftrightarrow> dword_eq v1 v2" by auto
lemma ptype_lword_eq[simp]: "ptype_eq (ptype.Lword v1) (ptype.Lword v2) \<longleftrightarrow> lword_eq v1 v2" by auto
lemma ptype_time_eq[simp]: "ptype_eq (ptype.Time v1) (ptype.Time v2) \<longleftrightarrow> time_eq v1 v2" by auto
lemma ptype_bool_eq[simp]: "ptype_eq (ptype.Bool v1) (ptype.Bool v2) \<longleftrightarrow> v1 = v2" by auto

lemma ptype_nat_less[simp]: "ptype_less (ptype.Nat v1) (ptype.Nat v2) \<longleftrightarrow> v1 < v2" by auto
lemma ptype_int_less[simp]: "ptype_less (ptype.Int v1) (ptype.Int v2) \<longleftrightarrow> v1 < v2" by auto
lemma ptype_real_less[simp]: "ptype_less (ptype.Real v1) (ptype.Real v2) \<longleftrightarrow> v1 < v2" by auto
lemma ptype_byte_less[simp]: "ptype_less (ptype.Byte v1) (ptype.Byte v2) \<longleftrightarrow> byte_less v1 v2" by auto
lemma ptype_word_less[simp]: "ptype_less (ptype.Word v1) (ptype.Word v2) \<longleftrightarrow> word_less v1 v2" by auto
lemma ptype_dword_less[simp]: "ptype_less (ptype.Dword v1) (ptype.Dword v2) \<longleftrightarrow> dword_less v1 v2" by auto
lemma ptype_lword_less[simp]: "ptype_less (ptype.Lword v1) (ptype.Lword v2) \<longleftrightarrow> lword_less v1 v2" by auto
lemma ptype_time_less[simp]: "ptype_less (ptype.Time v1) (ptype.Time v2) \<longleftrightarrow> time_less v1 v2" by auto
lemma ptype_bool_less[simp]: "ptype_less (ptype.Bool v1) (ptype.Bool v2) \<longleftrightarrow> v1 < v2" by auto

lemma ptype_nat_more[simp]: "ptype_more (ptype.Nat v1) (ptype.Nat v2) \<longleftrightarrow> v1 > v2" by auto
lemma ptype_int_more[simp]: "ptype_more (ptype.Int v1) (ptype.Int v2) \<longleftrightarrow> v1 > v2" by auto
lemma ptype_real_more[simp]: "ptype_more (ptype.Real v1) (ptype.Real v2) \<longleftrightarrow> v1 > v2" by auto
lemma ptype_byte_more[simp]: "ptype_more (ptype.Byte v1) (ptype.Byte v2) \<longleftrightarrow> byte_more v1 v2" by auto
lemma ptype_word_more[simp]: "ptype_more (ptype.Word v1) (ptype.Word v2) \<longleftrightarrow> word_more v1 v2" by auto
lemma ptype_dword_more[simp]: "ptype_more (ptype.Dword v1) (ptype.Dword v2) \<longleftrightarrow> dword_more v1 v2" by auto
lemma ptype_lword_more[simp]: "ptype_more (ptype.Lword v1) (ptype.Lword v2) \<longleftrightarrow> lword_more v1 v2" by auto
lemma ptype_time_more[simp]: "ptype_more (ptype.Time v1) (ptype.Time v2) \<longleftrightarrow> time_more v1 v2" by auto
lemma ptype_bool_more[simp]: "ptype_more (ptype.Bool v1) (ptype.Bool v2) \<longleftrightarrow> v1 > v2" by auto

lemma ptype_nat_eqless[simp]: "ptype_eqless (ptype.Nat v1) (ptype.Nat v2) \<longleftrightarrow> v1 \<le> v2" by auto
lemma ptype_int_eqless[simp]: "ptype_eqless (ptype.Int v1) (ptype.Int v2) \<longleftrightarrow> v1 \<le>v2" by auto
lemma ptype_real_eqless[simp]: "ptype_eqless (ptype.Real v1) (ptype.Real v2) \<longleftrightarrow> v1 \<le> v2" by auto
lemma ptype_byte_eqless[simp]: "ptype_eqless (ptype.Byte v1) (ptype.Byte v2) \<longleftrightarrow> byte_eqless v1 v2" by auto
lemma ptype_word_eqless[simp]: "ptype_eqless (ptype.Word v1) (ptype.Word v2) \<longleftrightarrow> word_eqless v1 v2" by auto
lemma ptype_dword_eqless[simp]: "ptype_eqless (ptype.Dword v1) (ptype.Dword v2) \<longleftrightarrow> dword_eqless v1 v2" by auto
lemma ptype_lword_eqless[simp]: "ptype_eqless (ptype.Lword v1) (ptype.Lword v2) \<longleftrightarrow> lword_eqless v1 v2" by auto
lemma ptype_time_eqless[simp]: "ptype_eqless (ptype.Time v1) (ptype.Time v2) \<longleftrightarrow> time_eqless v1 v2" by auto
lemma ptype_bool_eqless[simp]: "ptype_eqless (ptype.Bool v1) (ptype.Bool v2) \<longleftrightarrow> v1 \<le> v2" by auto

lemma ptype_nat_eqmore[simp]: "ptype_eqmore (ptype.Nat v1) (ptype.Nat v2) \<longleftrightarrow> v1 \<ge> v2" by auto
lemma ptype_int_eqmore[simp]: "ptype_eqmore (ptype.Int v1) (ptype.Int v2) \<longleftrightarrow> v1 \<ge> v2" by auto
lemma ptype_real_eqmore[simp]: "ptype_eqmore (ptype.Real v1) (ptype.Real v2) \<longleftrightarrow> v1 \<ge> v2" by auto
lemma ptype_byte_eqmore[simp]: "ptype_eqmore (ptype.Byte v1) (ptype.Byte v2) \<longleftrightarrow> byte_eqmore v1 v2" by auto
lemma ptype_word_eqmore[simp]: "ptype_eqmore (ptype.Word v1) (ptype.Word v2) \<longleftrightarrow> word_eqmore v1 v2" by auto
lemma ptype_dword_eqmore[simp]: "ptype_eqmore (ptype.Dword v1) (ptype.Dword v2) \<longleftrightarrow> dword_eqmore v1 v2" by auto
lemma ptype_lword_eqmore[simp]: "ptype_eqmore (ptype.Lword v1) (ptype.Lword v2) \<longleftrightarrow> lword_eqmore v1 v2" by auto
lemma ptype_time_eqmore[simp]: "ptype_eqmore (ptype.Time v1) (ptype.Time v2) \<longleftrightarrow> time_eqmore v1 v2" by auto
lemma ptype_bool_eqmore[simp]: "ptype_eqmore (ptype.Bool v1) (ptype.Bool v2) \<longleftrightarrow> v1 \<ge> v2" by auto

lemma ptype_nat_noteq[simp]: "ptype_noteq (ptype.Nat v1) (ptype.Nat v2) \<longleftrightarrow> v1 \<noteq> v2" by auto
lemma ptype_int_noteq[simp]: "ptype_noteq (ptype.Int v1) (ptype.Int v2) \<longleftrightarrow> v1 \<noteq> v2" by auto
lemma ptype_real_noteq[simp]: "ptype_noteq (ptype.Real v1) (ptype.Real v2) \<longleftrightarrow> v1 \<noteq> v2" by auto
lemma ptype_byte_noteq[simp]: "ptype_noteq (ptype.Byte v1) (ptype.Byte v2) \<longleftrightarrow> byte_noteq v1 v2" by auto
lemma ptype_word_noteq[simp]: "ptype_noteq (ptype.Word v1) (ptype.Word v2) \<longleftrightarrow> word_noteq v1 v2" by auto
lemma ptype_dword_noteq[simp]: "ptype_noteq (ptype.Dword v1) (ptype.Dword v2) \<longleftrightarrow> dword_noteq v1 v2" by auto
lemma ptype_lword_noteq[simp]: "ptype_noteq (ptype.Lword v1) (ptype.Lword v2) \<longleftrightarrow> lword_noteq v1 v2" by auto
lemma ptype_time_noteq[simp]: "ptype_noteq (ptype.Time v1) (ptype.Time v2) \<longleftrightarrow> time_noteq v1 v2" by auto
lemma ptype_bool_noteq[simp]: "ptype_noteq (ptype.Bool v1) (ptype.Bool v2) \<longleftrightarrow> v1 \<noteq> v2" by auto

lemma ptype_byte_and[simp]: "ptype_and (ptype.Byte v1) (ptype.Byte v2) = (ptype.Byte v3) \<longleftrightarrow> byte_and v1 v2 = v3" by auto
lemma ptype_word_and[simp]: "ptype_and (ptype.Word v1) (ptype.Word v2) = (ptype.Word v3)\<longleftrightarrow> word_and v1 v2 = v3" by auto
lemma ptype_dword_and[simp]: "ptype_and (ptype.Dword v1) (ptype.Dword v2) = (ptype.Dword v3) \<longleftrightarrow> dword_and v1 v2 = v3" by auto
lemma ptype_lword_and[simp]: "ptype_and (ptype.Lword v1) (ptype.Lword v2) = (ptype.Lword v3) \<longleftrightarrow> lword_and v1 v2 = v3" by auto
lemma ptype_bool_and[simp]: "ptype_and (ptype.Bool v1) (ptype.Bool v2) = (ptype.Bool v3) \<longleftrightarrow> (v1 \<and> v2) = v3" by auto

lemma ptype_byte_or[simp]: "ptype_or (ptype.Byte v1) (ptype.Byte v2) = (ptype.Byte v3) \<longleftrightarrow> byte_or v1 v2 = v3" by auto
lemma ptype_word_or[simp]: "ptype_or (ptype.Word v1) (ptype.Word v2) = (ptype.Word v3)\<longleftrightarrow> word_or v1 v2 = v3" by auto
lemma ptype_dword_or[simp]: "ptype_or (ptype.Dword v1) (ptype.Dword v2) = (ptype.Dword v3) \<longleftrightarrow> dword_or v1 v2 = v3" by auto
lemma ptype_lword_or[simp]: "ptype_or (ptype.Lword v1) (ptype.Lword v2) = (ptype.Lword v3) \<longleftrightarrow> lword_or v1 v2 = v3" by auto
lemma ptype_bool_or[simp]: "ptype_or (ptype.Bool v1) (ptype.Bool v2) = (ptype.Bool v3) \<longleftrightarrow> (v1 \<or> v2) = v3" by auto

lemma ptype_byte_xor[simp]: "ptype_xor (ptype.Byte v1) (ptype.Byte v2) = (ptype.Byte v3) \<longleftrightarrow> byte_xor v1 v2 = v3" by auto
lemma ptype_word_xor[simp]: "ptype_xor (ptype.Word v1) (ptype.Word v2) = (ptype.Word v3)\<longleftrightarrow> word_xor v1 v2 = v3" by auto
lemma ptype_dword_xor[simp]: "ptype_xor (ptype.Dword v1) (ptype.Dword v2) = (ptype.Dword v3) \<longleftrightarrow> dword_xor v1 v2 = v3" by auto
lemma ptype_lword_xor[simp]: "ptype_xor (ptype.Lword v1) (ptype.Lword v2) = (ptype.Lword v3) \<longleftrightarrow> lword_xor v1 v2 = v3" by auto
lemma ptype_bool_xor[simp]: "ptype_xor (ptype.Bool v1) (ptype.Bool v2) = (ptype.Bool v3) \<longleftrightarrow> (v1 \<noteq> v2) = v3" by auto
end