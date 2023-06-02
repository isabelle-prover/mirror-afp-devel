(*
   Mike Stannett
   Feb 2023
*)

section \<open> AXIOM: AxEventMinus \<close>

text \<open>This theory declares the axiom AxEventMinus \<close>

theory AxEventMinus
  imports WorldView
begin

text \<open>AxEventMinus: 
  An observer encounters the events in which they are observed.
\<close>
(*
  (\<forall>m,k \<in> Ob)(\<forall>p \<in> Q4)
    k \<in> ev_m(p) \<longrightarrow> (\<exists>q \<in> Q4) ev_m(p) = ev_k(q)

*)
class axEventMinus = WorldView
begin

  abbreviation axEventMinus :: "Body \<Rightarrow> Body \<Rightarrow> 'a Point \<Rightarrow> bool" 
    where "axEventMinus m k p \<equiv> (m sees k at p) 
                   \<longrightarrow> (\<exists> q . \<forall> b . ( (m sees b at p) \<longleftrightarrow> (k sees b at q)))"

end (* of class axEventMinus *)





class AxEventMinus = axEventMinus +
  assumes AxEventMinus: "\<forall> m k p  . axEventMinus m k p"
begin
end (* of class AxEventMinus *)

end (* of theory AxEventMinus *)

