theory bit_types_utils
  imports "~~/poST/poST_model/bit_types"
begin

definition byte_sum :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_sum var1 var2 = byte_of_integer ((integer_of_byte var1) + (integer_of_byte var2))"

definition byte_sub :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_sub var1 var2 = byte_of_integer ((integer_of_byte var1) - (integer_of_byte var2))"

definition byte_mul :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_mul var1 var2 = byte_of_integer ((integer_of_byte var1) * (integer_of_byte var2))"

fun byte_div :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_div var1 (Byte False False False False False False False False) = Byte False False False False False False False False " |
  "byte_div var1 var2 = byte_of_integer (divide (integer_of_byte var1)  (integer_of_byte var2))"

definition byte_divide :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_divide var1 var2 =byte_of_integer (divide (integer_of_byte var1) (integer_of_byte var2))"

definition byte_mod :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_mod var1 var2 =byte_of_integer ((integer_of_byte var1) mod (integer_of_byte var2))"

definition word_sum :: "word \<Rightarrow> word \<Rightarrow> word" where
  "word_sum var1 var2 = 
    (let (var11,var12) = var1 ;
         (var21,var22) = var2 ;
         res = ((integer_of_byte var11) + 
               ((integer_of_byte var12) * 256) + 
               (integer_of_byte var21) + 
               ((integer_of_byte var22) * 256)) in
      (byte_of_integer (divide res 256), byte_of_integer res))"


definition byte_eq :: "byte \<Rightarrow> byte \<Rightarrow> bool" where
"byte_eq b1 b2 = (of_byte b1 = (of_byte b2 :: nat))"
definition byte_eqless :: "byte \<Rightarrow> byte \<Rightarrow> bool" where
"byte_eqless b1 b2 = (of_byte b1 \<le> (of_byte b2 :: nat))"
definition byte_less :: "byte \<Rightarrow> byte \<Rightarrow> bool" where
"byte_less b1 b2 = (of_byte b1 < (of_byte b2 :: nat))"
definition byte_eqmore :: "byte \<Rightarrow> byte \<Rightarrow> bool" where
"byte_eqmore b1 b2 = (of_byte b1 \<ge> (of_byte b2 :: nat))"
definition byte_more :: "byte \<Rightarrow> byte \<Rightarrow> bool" where
"byte_more b1 b2 = (of_byte b1 > (of_byte b2 :: nat))"
definition byte_noteq :: "byte \<Rightarrow> byte \<Rightarrow> bool" where
"byte_noteq b1 b2 = (of_byte b1 \<noteq> (of_byte b2 :: nat))"

end

