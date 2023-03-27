(*
  Mike Stannett
  Feb 2023
*)

section \<open> AXIOM: AxEField \<close>

text \<open>This theory defines the axiom AxEField, which states that 
the linearly ordered field of quantities is Euclidean, i.e. that
all non-negative values have square roots in the field. \<close>

theory AxEField
  imports Sorts
begin

class axEField = Quantities
begin
  abbreviation axEField :: "'a \<Rightarrow> bool"
    where "axEField x \<equiv> (x \<ge> 0) \<longrightarrow> hasRoot x"
end (* of class axEField *)


class AxEField = axEField +
  assumes AxEField: "\<forall> x . axEField x"
begin
end (* of class AxEField *)


end (* of theory AxEField *)

