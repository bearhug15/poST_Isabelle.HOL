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

definition byte_not :: "byte \<Rightarrow> byte" where
  "byte_not b = byte.Byte (\<not> digit0 b) (\<not> digit1 b) (\<not> digit2 b) (\<not> digit3 b) (\<not> digit4 b) (\<not> digit5 b) (\<not> digit6 b) (\<not> digit7 b)"
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
definition byte_and :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_and b1 b2 = 
    (Byte (digit0 b1 \<and> digit0 b2)
          (digit1 b1 \<and> digit1 b2)
          (digit2 b1 \<and> digit2 b2)
          (digit3 b1 \<and> digit3 b2)
          (digit4 b1 \<and> digit4 b2)
          (digit5 b1 \<and> digit5 b2)
          (digit6 b1 \<and> digit6 b2)
          (digit7 b1 \<and> digit7 b2))"
definition byte_or :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_or b1 b2 = 
    (Byte (digit0 b1 \<or> digit0 b2)
          (digit1 b1 \<or> digit1 b2)
          (digit2 b1 \<or> digit2 b2)
          (digit3 b1 \<or> digit3 b2)
          (digit4 b1 \<or> digit4 b2)
          (digit5 b1 \<or> digit5 b2)
          (digit6 b1 \<or> digit6 b2)
          (digit7 b1 \<or> digit7 b2))"

definition byte_xor :: "byte \<Rightarrow> byte \<Rightarrow> byte" where
  "byte_xor b1 b2 = 
    (Byte ((digit0 b1) \<noteq> (digit0 b2))
          ((digit1 b1) \<noteq> (digit1 b2))
          ((digit2 b1) \<noteq> (digit2 b2))
          ((digit3 b1) \<noteq> (digit3 b2))
          ((digit4 b1) \<noteq> (digit4 b2))
          ((digit5 b1) \<noteq> (digit5 b2))
          ((digit6 b1) \<noteq> (digit6 b2))
          ((digit7 b1) \<noteq> (digit7 b2)))"

primrec byte_arr_not :: "byte list \<Rightarrow> byte list" where
  "byte_arr_not [] = []"
| "byte_arr_not (b#bs) = ((byte_not b) # (byte_arr_not bs))"
primrec byte_couple_eq :: "(byte*byte) list \<Rightarrow> bool" where
  "byte_couple_eq [] = True" 
| "byte_couple_eq (b#bs) = ((byte_eq (fst b) (snd b)) \<and> (byte_couple_eq bs))"
primrec byte_couple_less :: "(byte*byte) list \<Rightarrow> bool" where
  "byte_couple_less [] = False"
| "byte_couple_less (b#bs) = ((byte_less (fst b) (snd b)) \<or> (byte_couple_less bs))"
primrec byte_couple_more :: "(byte*byte) list \<Rightarrow> bool" where
  "byte_couple_more [] = False"
| "byte_couple_more (b#bs) = ((byte_more (fst b) (snd b)) \<or> (byte_couple_more bs))"
definition byte_couple_eqless :: "(byte*byte) list \<Rightarrow> bool" where
  "byte_couple_eqless ls = ((byte_couple_eq ls) \<or> (byte_couple_less ls))"
definition byte_couple_eqmore :: "(byte*byte) list \<Rightarrow> bool" where
  "byte_couple_eqmore ls = ((byte_couple_eq ls) \<or> (byte_couple_more ls))"
primrec byte_couple_noteq :: "(byte*byte) list \<Rightarrow> bool" where
  "byte_couple_noteq [] = False" 
| "byte_couple_noteq (b#bs) = ((byte_noteq (fst b) (snd b)) \<or> (byte_couple_noteq bs))"
primrec byte_couple_and :: "(byte*byte) list \<Rightarrow> byte list" where
  "byte_couple_and [] = []"
| "byte_couple_and (b#bs) = (byte_and (fst b) (snd b))#(byte_couple_and bs)"
primrec byte_couple_or :: "(byte*byte) list \<Rightarrow> byte list" where
  "byte_couple_or [] = []"
| "byte_couple_or (b#bs) = (byte_or (fst b) (snd b))#(byte_couple_or bs)"
primrec byte_couple_xor :: "(byte*byte) list \<Rightarrow> byte list" where
  "byte_couple_xor [] = []"
| "byte_couple_xor (b#bs) = (byte_xor (fst b) (snd b))#(byte_couple_xor bs)"

definition word_not :: "word \<Rightarrow> word" where
  "word_not w = 
    (let (b0,b1) = w;
         res = (byte_arr_not [b0,b1])
      in (nth res 0, nth res 1))"
definition word_eq :: "word \<Rightarrow> word \<Rightarrow> bool" where
  "word_eq w1 w2 = 
    (case (w1,w2) of
      ((b11,b12),(b21,b22)) \<Rightarrow> (byte_couple_eq [(b11,b21),(b12,b22)]))"
definition word_eqless :: "word \<Rightarrow> word \<Rightarrow> bool" where
  "word_eqless w1 w2 =
    (case (w1,w2) of
      ((b11,b12),(b21,b22)) \<Rightarrow> (byte_couple_eqless [(b11,b21),(b12,b22)]))"
definition word_less :: "word \<Rightarrow> word \<Rightarrow> bool" where
  "word_less w1 w2 =
    (case (w1,w2) of
      ((b11,b12),(b21,b22)) \<Rightarrow> (byte_couple_less [(b11,b21),(b12,b22)]))"
definition word_eqmore :: "word \<Rightarrow> word \<Rightarrow> bool" where
  "word_eqmore w1 w2 =
    (case (w1,w2) of
      ((b11,b12),(b21,b22)) \<Rightarrow> (byte_couple_eqmore [(b11,b21),(b12,b22)]))"
definition word_more :: "word \<Rightarrow> word \<Rightarrow> bool" where
  "word_more w1 w2 =
    (case (w1,w2) of
      ((b11,b12),(b21,b22)) \<Rightarrow> (byte_couple_more [(b11,b21),(b12,b22)]))"
definition word_noteq :: "word \<Rightarrow> word \<Rightarrow> bool" where
  "word_noteq w1 w2 = 
    (case (w1,w2) of
      ((b11,b12),(b21,b22)) \<Rightarrow> (byte_couple_noteq [(b11,b21),(b12,b22)]))"
definition word_and :: "word \<Rightarrow> word \<Rightarrow> word" where
  "word_and w1 w2 =
    (let (b11,b12) = w1;
         (b21,b22) = w2;
         res = (byte_couple_and [(b11,b21),(b12,b22)])
     in (nth res 0, nth res 1))"
definition word_or :: "word \<Rightarrow> word \<Rightarrow> word" where
  "word_or w1 w2 =
    (let (b11,b12) = w1;
         (b21,b22) = w2;
         res = (byte_couple_or [(b11,b21),(b12,b22)])
     in (nth res 0, nth res 1))"
definition word_xor :: "word \<Rightarrow> word \<Rightarrow> word" where
  "word_xor w1 w2 =
    (let (b11,b12) = w1;
         (b21,b22) = w2;
         res = (byte_couple_xor [(b11,b21),(b12,b22)])
     in (nth res 0, nth res 1))"

definition dword_not :: "dword \<Rightarrow> dword" where
  "dword_not w= 
    (let (b0,b1,b2,b3) = w;
         res = (byte_arr_not [b0,b1,b2,b3])
      in (nth res 0, nth res 1, nth res 2, nth res 3))"
definition dword_eq :: "dword \<Rightarrow> dword \<Rightarrow> bool" where
  "dword_eq w1 w2 = 
    (case (w1,w2) of
      ((b11,b12,b13,b14),(b21,b22,b23,b24)) \<Rightarrow> (byte_couple_eq [(b11,b21),(b12,b22),(b13,b23),(b14,b24)]))"
definition dword_eqless :: "dword \<Rightarrow> dword \<Rightarrow> bool" where
  "dword_eqless w1 w2 = 
    (case (w1,w2) of
      ((b11,b12,b13,b14),(b21,b22,b23,b24)) \<Rightarrow> (byte_couple_eqless [(b11,b21),(b12,b22),(b13,b23),(b14,b24)]))"
definition dword_less :: "dword \<Rightarrow> dword \<Rightarrow> bool" where
  "dword_less w1 w2 = 
    (case (w1,w2) of
      ((b11,b12,b13,b14),(b21,b22,b23,b24)) \<Rightarrow> (byte_couple_less [(b11,b21),(b12,b22),(b13,b23),(b14,b24)]))"
definition dword_eqmore :: "dword \<Rightarrow> dword \<Rightarrow> bool" where
  "dword_eqmore w1 w2 = 
    (case (w1,w2) of
      ((b11,b12,b13,b14),(b21,b22,b23,b24)) \<Rightarrow> (byte_couple_eqmore [(b11,b21),(b12,b22),(b13,b23),(b14,b24)]))"
definition dword_more :: "dword \<Rightarrow> dword \<Rightarrow> bool" where
  "dword_more w1 w2 = 
    (case (w1,w2) of
      ((b11,b12,b13,b14),(b21,b22,b23,b24)) \<Rightarrow> (byte_couple_more [(b11,b21),(b12,b22),(b13,b23),(b14,b24)]))"
definition dword_noteq :: "dword \<Rightarrow> dword \<Rightarrow> bool" where
  "dword_noteq w1 w2 = 
    (case (w1,w2) of
      ((b11,b12,b13,b14),(b21,b22,b23,b24)) \<Rightarrow> (byte_couple_noteq [(b11,b21),(b12,b22),(b13,b23),(b14,b24)]))"
definition dword_and :: "dword \<Rightarrow> dword \<Rightarrow> dword" where
  "dword_and w1 w2 =
    (let (b11,b12,b13,b14) = w1;
         (b21,b22,b23,b24) = w2;
         res = (byte_couple_and [(b11,b21),(b12,b22),(b13,b23),(b14,b24)])
     in (nth res 0, nth res 1, nth res 2, nth res 3))"
definition dword_or :: "dword \<Rightarrow> dword \<Rightarrow> dword" where
  "dword_or w1 w2 =
    (let (b11,b12,b13,b14) = w1;
         (b21,b22,b23,b24) = w2;
         res = (byte_couple_or [(b11,b21),(b12,b22),(b13,b23),(b14,b24)])
     in (nth res 0, nth res 1, nth res 2, nth res 3))"
definition dword_xor :: "dword \<Rightarrow> dword \<Rightarrow> dword" where
  "dword_xor w1 w2 =
    (let (b11,b12,b13,b14) = w1;
         (b21,b22,b23,b24) = w2;
         res = (byte_couple_or [(b11,b21),(b12,b22),(b13,b23),(b14,b24)])
     in (nth res 0, nth res 1, nth res 2, nth res 3))"

definition lword_not :: "lword \<Rightarrow> lword" where
"lword_not w = 
  (let (b0,b1,b2,b3,b4,b5,b6,b7) = w;
         res = (byte_arr_not [b0,b1,b2,b3,b4,b5,b6,b7])
      in (nth res 0, nth res 1, nth res 2, nth res 3, nth res 4, nth res 5, nth res 6, nth res 7))"
definition lword_eq :: "lword \<Rightarrow> lword \<Rightarrow> bool" where
"lword_eq w1 w2 = 
  (case (w1,w2) of
    ((b11,b12,b13,b14,b15,b16,b17,b18),(b21,b22,b23,b24,b25,b26,b27,b28)) \<Rightarrow> 
      (byte_couple_eq [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)]))"
definition lword_eqless :: "lword \<Rightarrow> lword \<Rightarrow> bool" where
"lword_eqless w1 w2 =
  (case (w1,w2) of
    ((b11,b12,b13,b14,b15,b16,b17,b18),(b21,b22,b23,b24,b25,b26,b27,b28)) \<Rightarrow> 
      (byte_couple_eqless [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)]))"
definition lword_less :: "lword \<Rightarrow> lword \<Rightarrow> bool" where
"lword_less w1 w2 =
  (case (w1,w2) of
    ((b11,b12,b13,b14,b15,b16,b17,b18),(b21,b22,b23,b24,b25,b26,b27,b28)) \<Rightarrow> 
      (byte_couple_less [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)]))"
definition lword_eqmore :: "lword \<Rightarrow> lword \<Rightarrow> bool" where
"lword_eqmore w1 w2 = 
  (case (w1,w2) of
    ((b11,b12,b13,b14,b15,b16,b17,b18),(b21,b22,b23,b24,b25,b26,b27,b28)) \<Rightarrow> 
      (byte_couple_eqmore [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)]))"
definition lword_more :: "lword \<Rightarrow> lword \<Rightarrow> bool" where
"lword_more w1 w2 =
  (case (w1,w2) of
    ((b11,b12,b13,b14,b15,b16,b17,b18),(b21,b22,b23,b24,b25,b26,b27,b28)) \<Rightarrow> 
      (byte_couple_more [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)]))"
definition lword_noteq :: "lword \<Rightarrow> lword \<Rightarrow> bool" where
"lword_noteq w1 w2 = 
  (case (w1,w2) of
    ((b11,b12,b13,b14,b15,b16,b17,b18),(b21,b22,b23,b24,b25,b26,b27,b28)) \<Rightarrow> 
      (byte_couple_noteq [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)]))"
definition lword_and :: "lword \<Rightarrow> lword \<Rightarrow> lword" where
  "lword_and w1 w2 =
    (let (b11,b12,b13,b14,b15,b16,b17,b18) = w1;
         (b21,b22,b23,b24,b25,b26,b27,b28) = w2;
         res = (byte_couple_and [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)])
     in (nth res 0, nth res 1, nth res 2, nth res 3, nth res 4, nth res 5, nth res 6, nth res 7))"
definition lword_or :: "lword \<Rightarrow> lword \<Rightarrow> lword" where
  "lword_or w1 w2 =
    (let (b11,b12,b13,b14,b15,b16,b17,b18) = w1;
         (b21,b22,b23,b24,b25,b26,b27,b28) = w2;
         res = (byte_couple_or [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)])
     in (nth res 0, nth res 1, nth res 2, nth res 3, nth res 4, nth res 5, nth res 6, nth res 7))"
definition lword_xor :: "lword \<Rightarrow> lword \<Rightarrow> lword" where
  "lword_xor w1 w2 =
    (let (b11,b12,b13,b14,b15,b16,b17,b18) = w1;
         (b21,b22,b23,b24,b25,b26,b27,b28) = w2;
         res = (byte_couple_xor [(b11,b21),(b12,b22),(b13,b23),(b14,b24),(b15,b25),(b16,b26),(b17,b27),(b18,b28)])
     in (nth res 0, nth res 1, nth res 2, nth res 3, nth res 4, nth res 5, nth res 6, nth res 7))"

end

