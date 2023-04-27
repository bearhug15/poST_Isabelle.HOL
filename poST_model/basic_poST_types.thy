theory basic_poST_types
  imports Main HOL.Real bit_types poST_time
begin 

type_synonym  wstring = "(char * char) list"

datatype basic_post_type =
Nat nat |
Int int |
Real real |
Bool bool |
Byte byte |
Word word |
Dword dword |
Lword lword |
String string |
Wstring wstring |
Time time

datatype direct_type_perfix = I | Q | M
datatype direct_size_prefix = X | B | W | D | L

datatype const = 
Nat nat |
Int int |
Real real |
Time time |
Bool bool

type_synonym id = string
type_synonym conf_name = id
type_synonym resource_name = id
type_synonym task_name = id
type_synonym prog_conf_name = id
type_synonym prog_name = id
type_synonym func_block_name = id
type_synonym func_name = id
type_synonym state_name = id
type_synonym process_name = id
type_synonym function_block_name = id
type_synonym program_name = id
type_synonym configuration_name = id
type_synonym symbolic_var = id

type_synonym is_looped  = bool
type_synonym is_const = bool


end