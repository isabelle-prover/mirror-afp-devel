theory Higher_Projective_Space_Axioms
  imports Main
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk .*)

text \<open>
Contents:
\<^item> We introduce the types of 'point and 'line and an incidence relation between them.
\<^item> A set of axioms for higher projective spaces, i.e. we allow models of dimension \<open>>\<close> 3. 
\<close>

section \<open>The axioms for Higher Projective Geometry\<close>

lemma distinct4_def:
  "distinct [A,B,C,D] = ((A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D) \<and> (B \<noteq> C) \<and> (B \<noteq> D) \<and> (C \<noteq> D))"
  by auto

lemma distinct3_def:
  "distinct [A,B,C] = ((A \<noteq> B) \<and> (A \<noteq> C) \<and> (B \<noteq> C))"
  by auto

locale higher_projective_space =
(* One has a type of 'point *)
(* One has a type of 'line *)
(* One has a relation of incidence between 'point and 'line *)
  fixes incid :: "'point \<Rightarrow> 'line \<Rightarrow> bool"

(* We have the following axioms *)

(* Ax1: Any two distinct 'point are incident with just one line *)
  assumes ax1_existence: "\<exists>l. (incid P l) \<and> (incid M l)"
  assumes ax1_uniqueness: "(incid P k) \<longrightarrow> (incid M k) \<longrightarrow> (incid P l) \<longrightarrow> (incid M l) \<longrightarrow> (P = M) \<or> (k = l)"


(* Ax2: If A B C D are four distinct 'point such that AB meets CD, then AC meets BD.
Sometimes this is called Pasch's axiom, but according to Wikipedia it is misleading
since Pasch's axiom refers to something else. *)
assumes ax2: "distinct [A,B,C,D] \<longrightarrow> (incid A lAB \<and> incid B lAB) 
\<longrightarrow> (incid C lCD \<and> incid D lCD) \<longrightarrow> (incid A lAC \<and> incid C lAC) \<longrightarrow> 
(incid B lBD \<and> incid D lBD) \<longrightarrow> (\<exists>I.(incid I lAB \<and> incid I lCD)) \<longrightarrow> 
(\<exists>J.(incid J lAC \<and> incid J lBD))"



(** Dimension-related axioms **)
(* Ax3: Every line is incident with at least three 'point.
As I understand it, this axiom makes sure that 'line are not degenerated into 'point
and since it asks for three distinct 'point, not only 2, it captures the idea that
'line have unlimited extent, i.e. there is always a point between two distinct 'point. *)
assumes ax3: "\<exists>A B C. distinct [A,B,C] \<and> (incid A l) \<and> (incid B l) \<and> (incid C l)"

(* Ax4: There exists two 'line that do not meet, hence the geometry is at least 3-dimensional *)
assumes ax4: "\<exists>l m.\<forall>P. \<not>(incid P l \<and> incid P m)"


end
