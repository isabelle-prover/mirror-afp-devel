theory Projective_Space_Axioms
  imports Main
begin

(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

text \<open>
Contents:
\<^item> We introduce the types @{typ 'point} of points and @{typ 'line} of lines and an incidence relation 
between them.
\<^item> A set of axioms for the (3-dimensional) projective space. 
An alternative set of axioms could use planes as basic objects in addition to points and lines  
\<close>

section \<open>The axioms of the Projective Space\<close>

lemma distinct4_def:
"distinct [A,B,C,D] = ((A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D)\<and> (B \<noteq> C) \<and> (B \<noteq> D) \<and> (C \<noteq> D))"
  by auto

lemma distinct3_def:
  "distinct [A, B, C] = (A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C)"
  by auto

locale projective_space =
  (* One has a type of 'point *)
  (* We don't need an axiom for the existence of at least one point, 
  since we know that the type "'point" is not empty  
  TODO: why would that be true? *)
  (* One has a type of 'line *)
  (* There is a relation of incidence between 'point and 'line *)
  fixes incid :: "'point \<Rightarrow> 'line \<Rightarrow> bool"
  fixes meet :: "'line \<Rightarrow> 'line \<Rightarrow> 'point"
  assumes meet_def:  "(incid (meet l m) l \<and> incid (meet l m) m)"

  (* The relation of incidence is decidable *)
  assumes incid_dec: "(incid P l) \<or> \<not>(incid P l)"

  (* Ax1: Any two distinct 'point are incident with just one line *)
  assumes ax1_existence: "\<exists>l. (incid P l) \<and> (incid M l)"
  assumes ax1_uniqueness: "(incid P k) \<longrightarrow> (incid M k) \<longrightarrow> (incid P l) \<longrightarrow> (incid M l) \<longrightarrow> (P = M) \<or> (k = l)"


  (* Ax2: If A B C D are four distinct 'point such that AB meets CD then AC meets BD.
  Sometimes this is called Pasch's axiom, but according to Wikipedia it is misleading
  since Pasch's axiom refers to something else. *)
  assumes ax2: "distinct [A,B,C,D] \<longrightarrow> (incid A lAB \<and> incid B lAB) 
  \<longrightarrow> (incid C lCD \<and> incid D lCD) \<longrightarrow> (incid A lAC \<and> incid C lAC) \<longrightarrow> 
  (incid B lBD \<and> incid D lBD) \<longrightarrow> (\<exists>I.(incid I lAB \<and> incid I lCD)) \<longrightarrow> 
  (\<exists>J.(incid J lAC \<and> incid J lBD))"



  (** Dimension-related axioms **)
  (* Ax3: Every line is incident with at least three Points.
  As I understand it, this axiom makes sure that Lines are not degenerated into 'point
  and since it asks for three distinct Points, not only 2, it captures the idea that
  Lines are continuous, i.e. there is always a point between two distinct Points. *)
  assumes ax3: "\<exists>A B C. distinct3 A B C \<and> (incid A l) \<and> (incid B l) \<and> (incid C l)"

  (* Ax4: There exists two Lines that do not meet, 
  hence the geometry is at least 3-dimensional *)
  assumes ax4: "\<exists>l m.\<forall>P. \<not>(incid P l \<and> incid P m)"


  (* Ax5: The geometry is not 4-dimensional, hence it is exactly 3-dimensional *)
  assumes ax5: "distinct [l1,l2,l3] \<longrightarrow> (\<exists>l4 J1 J2 J3. distinct [J1,J2,J3] \<and> 
  meet l1 l4 = J1 \<and> meet l2 l4 = J2 \<and> meet l3 l4 = J3)"


end