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



end