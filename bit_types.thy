theory bit_types
  imports Main HOL.Bit_Operations 
begin
datatype byte = 
Byte (digit0: bool) (digit1: bool) (digit2: bool) (digit3: bool)
     (digit4: bool) (digit5: bool) (digit6: bool) (digit7: bool)
type_synonym word = "(byte * byte)"
type_synonym dword = "(byte * byte * byte * byte)"
type_synonym lword = "(byte * byte * byte * byte * byte * byte * byte * byte)"

context comm_semiring_1
begin

definition of_byte :: \<open>byte \<Rightarrow> 'a\<close>
  where \<open>of_byte c = horner_sum of_bool 2 [digit0 c, digit1 c, digit2 c, digit3 c, digit4 c, digit5 c, digit6 c, digit7 c]\<close>

lemma of_byte_Byte [simp]:
  \<open>of_byte (Byte b0 b1 b2 b3 b4 b5 b6 b7) =
    horner_sum of_bool 2 [b0, b1, b2, b3, b4, b5, b6, b7]\<close>
  by (simp add: of_byte_def)

end

lemma (in comm_semiring_1) of_nat_of_char:
  \<open>of_nat (of_byte c) = of_byte c\<close>
  by (cases c) simp

lemma (in comm_ring_1) of_int_of_char:
  \<open>of_int (of_byte c) = of_byte c\<close>
  by (cases c) simp

lemma nat_of_byte [simp]:
  \<open>nat (of_byte c) = of_byte c\<close>
  by (cases c) (simp only: of_byte_Byte nat_horner_sum)

context unique_euclidean_semiring_with_bit_operations
begin
definition byte_of :: \<open>'a \<Rightarrow> byte\<close>
  where \<open>byte_of n = Byte (bit n 0) (bit n 1) (bit n 2) (bit n 3) (bit n 4) (bit n 5) (bit n 6) (bit n 7)\<close>
end

definition byte_of_integer :: "integer \<Rightarrow> byte"
  where [code_abbrev]: "byte_of_integer = byte_of"

definition integer_of_byte :: "byte \<Rightarrow> integer"
  where [code_abbrev]: "integer_of_byte = of_byte"

lemma byte_of_integer_code [code]:
  "byte_of_integer k = (let
     (q0, b0) = bit_cut_integer k;
     (q1, b1) = bit_cut_integer q0;
     (q2, b2) = bit_cut_integer q1;
     (q3, b3) = bit_cut_integer q2;
     (q4, b4) = bit_cut_integer q3;
     (q5, b5) = bit_cut_integer q4;
     (q6, b6) = bit_cut_integer q5;
     (_, b7) = bit_cut_integer q6
    in Byte b0 b1 b2 b3 b4 b5 b6 b7)"
  by (simp add: bit_cut_integer_def byte_of_integer_def byte_of_def div_mult2_numeral_eq bit_iff_odd_drop_bit drop_bit_eq_div)

lemma integer_of_byte_code [code]:
  "integer_of_byte (Byte b0 b1 b2 b3 b4 b5 b6 b7) =
    ((((((of_bool b7 * 2 + of_bool b6) * 2 +
      of_bool b5) * 2 + of_bool b4) * 2 +
        of_bool b3) * 2 + of_bool b2) * 2 +
          of_bool b1) * 2 + of_bool b0"
  by (simp add: integer_of_byte_def of_byte_def)

definition byte_sum :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_sum var1 var2 = byte_of_integer ((integer_of_byte var1) + (integer_of_byte var2))"

definition byte_sub :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_sub var1 var2 = byte_of_integer ((integer_of_byte var1) - (integer_of_byte var2))"

definition byte_mul :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_mul var1 var2 = byte_of_integer ((integer_of_byte var1) * (integer_of_byte var2))"
(*
fun byte_div :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_div var1 (Byte False False False False False False False False) = Byte False False False False False False False False " |
  "byte_div var1 var2 = byte_of_integer ((integer_of_byte var1) / (integer_of_byte var2))"
*)
(*
notation byte_sum (infixl "+" 65)
notation byte_sub (infixl "-" 65)
notation byte_mul (infixl "*" 70)
*)

definition byte_divide :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_divide var1 var2 =byte_of_integer (divide (integer_of_byte var1) (integer_of_byte var2))"

definition byte_mod :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_mod var1 var2 =byte_of_integer ((integer_of_byte var1) mod (integer_of_byte var2))"
(*
definition word_sum :: "word \<Rightarrow> word \<Rightarrow> word" where
  "word_sum var1 var2 = 
    (let (var11,var12) = var1 ;
         (var21,var22) = var2 ;
         res = ((integer_of_byte var11) + 
               ((integer_of_byte var12) * 256) + 
               (integer_of_byte var21) + 
               ((integer_of_byte var22) * 256)) in
      (byte_of_integer (divide res 256), byte_of_integer res))"
*)

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