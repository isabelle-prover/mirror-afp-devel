(* Author: Tassilo Lemke *)

subsection\<open>$Pre^*$ Example\<close>

text\<open>The algorithm is executable. This theory shows a quick example.\<close>

theory Pre_Star_Example
  imports Pre_Star
begin

text\<open>Consider the following grammar, with \<open>V = {A,B}\<close> and \<open>\<Sigma> = {a,b}\<close>:\<close>

datatype n = A | B
datatype t = a | b

definition "P \<equiv> {
  \<comment> \<open>\<open>A \<rightarrow> a | BB\<close>\<close>
  (A, [Tm a]),
  (A, [Nt B, Nt B]),

  \<comment> \<open>\<open>B \<rightarrow> AB | b\<close>\<close>
  (B, [Nt A, Nt B]),
  (B, [Tm b])
}"

text\<open>The following NFA accepts the regular language, whose predecessors we want to find:\<close>

definition M :: "(nat, (n, t) sym) auto" where "M \<equiv> \<lparr>
  auto.lts = {
    (0, Tm a, 1),
    (1, Tm b, 2),
    (2, Tm a, 1)
  },
  start = 0 :: nat,
  finals = {0, 1, 2}
\<rparr>"

lemma "pre_star_auto P M =
  \<lparr>auto.lts =
    {(2, Tm a, 1), (1, Tm b, 2), (0, Tm a, 1), (0, Nt A, 1), (0, Nt A, 2), (0, Nt B, 2), (0, Nt A, 1),
     (1, Nt A, 2), (1, Nt B, 2), (2, Nt A, 1), (2, Nt A, 2), (2, Nt B, 2), (2, Nt A, 1), (1, Nt A, 2),
     (1, Nt B, 2)},
   start = 0, finals = {0, 1, 2}\<rparr>"
by eval

end
