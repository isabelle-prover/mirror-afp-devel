(*
   Mike Stannett
   Feb 2023
*)

section \<open> AXIOM: AxSelfMinus \<close>

text \<open>This theory declares the axiom AxSelfMinus.\<close>

theory AxSelfMinus
  imports WorldView
begin

text \<open>AxSelfMinus:
  The worldline of an observer is a subset of the time axis in their own
  worldview.\<close>

(*
  (\<forall>m \<in> Ob) wline_m(m) \<subseteq> t-axis
*)
class axSelfMinus = WorldView
begin
  abbreviation axSelfMinus :: "Body \<Rightarrow> 'a Point \<Rightarrow> bool" 
    where "axSelfMinus m p \<equiv> (m sees m at p) \<longrightarrow> onTimeAxis p"
end (* of class axSelfMinus *)


class AxSelfMinus = axSelfMinus +
  assumes AxSelfMinus : "\<forall> m p    . axSelfMinus  m p"
begin
end (* of class AxSelfMinus *)

end (* of theory AxSelfMinus *)

