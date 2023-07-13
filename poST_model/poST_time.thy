theory poST_time
  imports Main HOL.Real
begin
(*days/hours/minutes/seconds/miliseconds*)
datatype time = Time (D:nat) (H: nat) (M: nat) (S: nat) (MS: nat) 

end
