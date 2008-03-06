(*  Title:      Heap.thy
    Author:     Norbert Schirmer, TU Muenchen

Copyright (C) 2004-2008 Norbert Schirmer 
Some rights reserved, TU Muenchen

This library is free software; you can redistribute it and/or modify
it under the terms of the GNU Lesser General Public License as
published by the Free Software Foundation; either version 2.1 of the
License, or (at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307
USA
*)

theory Heap 
imports "Ref"
begin

subsection "References"


lemma finite_nat_ex_max: 
  assumes fin: "finite (N::nat set)"
  shows "\<exists>m. \<forall>n\<in>N. n < m"
using fin
proof (induct)
  case empty
  show ?case by auto
next
  case (insert k N)
  have "\<exists>m. \<forall>n\<in>N. n < m".
  then obtain m where m_max: "\<forall>n\<in>N. n < m"..
  show "\<exists>m. \<forall>n\<in>insert k N. n < m"
  proof (rule exI [where x="Suc (max k m)"])
  qed (insert m_max, auto simp add: max_def)
qed

lemma infinite_nat: "\<not>finite (UNIV::nat set)"
proof 
  assume fin: "finite (UNIV::nat set)"
  then obtain m::nat where "\<forall>n\<in>UNIV. n < m"
    by (rule finite_nat_ex_max [elim_format] ) auto
  moreover have "m\<in>UNIV"..
  ultimately show False by blast
qed 

lemma infinite_ref [simp,intro]: "\<not>finite (UNIV::ref set)"
proof
  assume "finite (UNIV::ref set)"
  hence "finite (range Rep_ref)"
    by simp
  moreover
  have "range Rep_ref = ref"
  proof
    show "range Rep_ref \<subseteq> ref"
      by (simp add: ref_def)
  next
    show "ref \<subseteq> range Rep_ref"
    proof
      fix x
      assume x: "x \<in> ref"
      show "x \<in> range Rep_ref"
	by (rule Rep_ref_induct) (auto simp add: ref_def)
    qed
  qed
  ultimately have "finite ref"
    by simp
  thus False
    by (simp add: ref_def infinite_nat)
qed


defs new_def: "new A == SOME a. a \<notin> {Null} \<union> A"

lemma new_notin [simp,intro]:
 "\<lbrakk>finite A\<rbrakk> \<Longrightarrow> new (A) \<notin> A"
apply(unfold new_def)
apply(rule someI2_ex)
apply (fastsimp intro: ex_new_if_finite)
apply simp
done

lemma new_not_Null [simp,intro]: "\<lbrakk>finite A\<rbrakk> \<Longrightarrow> new (A) \<noteq> Null"
apply(unfold new_def)
apply(rule someI2_ex)
apply (fastsimp intro: ex_new_if_finite)
apply simp
done

end
