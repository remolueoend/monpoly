(*<*)
theory Monitor_Code
  imports Monitor_Impl
begin
(*>*)

export_code convert_multiway mmonitorable_exec vminit_safe minit_safe vmstep mstep
   checking OCaml?

export_code
  (*basic types*)
  nat_of_integer integer_of_nat int_of_integer integer_of_int enat
  interval empty_db insert_into_db RBT_set rbt_fold Sum_Type.Inl
  (*term, formula, and regex constructors*)
  EInt Formula.Var Formula.Agg_Cnt Formula.Pred Regex.Skip Regex.Wild Typing.TAny Formula.TInt
  (*main functions*)
  convert_multiway mmonitorable_exec minit_safe mstep type_check
  in OCaml module_name Monitor file_prefix "verified"

(*<*)
end
(*>*)
