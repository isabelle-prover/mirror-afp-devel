(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Conversions between automata"

theory Automata
imports DA NAe
begin

definition
 na2da :: "('a,'s)na \<Rightarrow> ('a,'s set)da" where
"na2da A = ({start A}, \<lambda>a Q. Union(next A a ` Q), \<lambda>Q. \<exists>q\<in>Q. fin A q)"

definition
 nae2da :: "('a,'s)nae \<Rightarrow> ('a,'s set)da" where
"nae2da A = ({start A},
              \<lambda>a Q. Union(next A (Some a) ` ((eps A)\<^sup>* `` Q)),
              \<lambda>Q. \<exists>p \<in> (eps A)\<^sup>* `` Q. fin A p)"

(*** Equivalence of NA and DA ***)

lemma DA_delta_is_lift_NA_delta:
 "\<And>Q. DA.delta (na2da A) w Q = Union(NA.delta A w ` Q)"
by (induct w)(auto simp:na2da_def)

lemma NA_DA_equiv:
  "NA.accepts A w = DA.accepts (na2da A) w"
  unfolding DA.accepts_def NA.accepts_def DA_delta_is_lift_NA_delta
  by (simp add: na2da_def)

(*** Direct equivalence of NAe and DA ***)

lemma espclosure_DA_delta_is_steps:
 "\<And>Q. (eps A)\<^sup>* `` (DA.delta (nae2da A) w Q) = steps A w `` Q"
  by (induct w) (auto simp add: step_def nae2da_def)

lemma NAe_DA_equiv:
  "DA.accepts (nae2da A) w = NAe.accepts A w"
proof -
  have "NAe.accepts A w"
    if "fin A x"
      and "(y, x) \<in> (eps A)\<^sup>*"
      and "y \<in> DA.delta ({start A}, \<lambda>a Q. \<Union> (next A (Some a) ` (eps A)\<^sup>* `` Q), \<lambda>Q. \<exists>x\<in>(eps A)\<^sup>* `` Q. fin A x) w {start A}"
    for x y
    by (metis (lifting) that ext ImageI Image_singleton_iff NAe.accepts_def
      espclosure_DA_delta_is_steps nae2da_def)
  moreover have "\<exists>x\<in>(eps A)\<^sup>* `` DA.delta ({start A}, \<lambda>a Q. \<Union> (next A (Some a) ` (eps A)\<^sup>* `` Q), 
                   \<lambda>Q. \<exists>x\<in>(eps A)\<^sup>* `` Q. fin A x) w {start A}. fin A x"
    if "NAe.accepts A w"
    using that unfolding  NAe.accepts_def
    by (metis Image_singleton_iff espclosure_DA_delta_is_steps nae2da_def)
  ultimately show ?thesis
    by (auto simp: nae2da_def DA.accepts_def)
qed

end
