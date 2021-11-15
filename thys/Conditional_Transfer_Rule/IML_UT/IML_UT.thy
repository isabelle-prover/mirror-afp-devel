(* Title: IML_UT/IML_UT.thy
   Author: Mihails Milehins
   Copyright 2021 (C) Mihails Milehins

A minor extension of SpecCheck: courtesy of Kevin Kappelmann.
*)

section\<open>\<open>IML_UT\<close>\<close>
theory IML_UT
  imports SpecCheck.SpecCheck
begin

ML\<open>
open SpecCheck;
structure Prop = SpecCheck_Property;
structure Show = SpecCheck_Show;

fun style_error show_opt =
  SpecCheck_Output_Style_Custom.style_custom writeln error show_opt

fun check_list_unit show ts name prop ctxt _ =
  check_list_style style_error (SOME show) ts name prop ctxt
  |> K ();
\<close>

end