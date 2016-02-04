section \<open>Factorization Oracle\<close>

text \<open>We define an overloaded constant which serves as an arbitrary factorization oracle
  for the rational factorization process. We provide one oracle with the Berlekamp-Hensel
  factorization algorithm, but one can later on easily
  change the oracle by just loading another theory.\<close>

theory Factorization_Oracle
imports
  Rat
  "~~/src/HOL/Library/Polynomial"
begin

consts factorization_oracle :: "rat poly \<Rightarrow> rat \<times> (rat poly \<times> nat) list"

end