theory poST_configuration
  imports poST_vars
begin
type_synonym task_name = id
type_synonym program_conf_name = id

datatype task_init = Single const |
                     Interval const int
type_synonym task = "task_name * task_init"

datatype attach_var = Const const |
                      SymbolicVar symbolic_var
type_synonym attach_var_conf_element = "symbolic_var * assign_type * attach_var"
type_synonym program_conf_element = attach_var_conf_element
type_synonym program_conf_elements = "program_conf_element list"
type_synonym program_conf_decl = "program_conf_name * (task_name option) * program_name * (program_conf_elements option)"

datatype single_resource_var = Task task |
                               ProgConfDecl program_conf_decl
type_synonym single_resource = "single_resource_var list"
type_synonym resource = "resource_name * id * (global_var_decl list) * single_resource"

datatype configuration_param = Resource resource |
                               GlobalVarDecl global_var_decl

type_synonym configuration_decl = "configuration_name * (configuration_param list) "

translations
  (type) "attach_var_conf_element" <= (type) "symbolic_var * assign_type * attach_var"
  (type) "program_conf_elements" <= (type) "program_conf_element list"
  (type) "program_conf_decl" <= (type) "program_conf_name * (task_name option) * program_name * (program_conf_elements option)"
  (type) "single_resource" <= (type) "single_resource_var list"
  (type) "resource" <= (type) "resource_name * id * (global_var_decl list) * single_resource"
  (type) "configuration_decl" <= (type) "configuration_name * (configuration_param list) "

end