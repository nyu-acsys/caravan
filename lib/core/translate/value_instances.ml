(** Dictionary-parameterized module instances shared by all emission scopes. *)

open Base
open Translate_context

let member ~loc (instance : function_instance) =
  R.Member.instance ~loc
    ~def:
      ( qualified_name ~loc instance.instance_worker,
        List.map instance.instance_arguments ~f:(fun argument ->
            R.Type.named ~loc (qualified_name ~loc argument) []) )
    (R.Ident.make ~loc instance.instance_name)
    (qualified_name ~loc instance.instance_worker)
