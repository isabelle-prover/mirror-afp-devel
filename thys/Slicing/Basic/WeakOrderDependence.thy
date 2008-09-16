header {* \isaheader{Weak order dependence} *}

theory WeakOrderDependence imports CFG DataDependence begin

text {* Weak order dependence is just defined as a static control dependence *}

subsection{* Definition and some lemmas *}

definition (in CFG) weak_order_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> bool"
   ("_ \<longrightarrow>\<^bsub>wod\<^esub> _,_")
where wod_def:"n \<longrightarrow>\<^bsub>wod\<^esub> n\<^isub>1,n\<^isub>2 \<equiv> ((n\<^isub>1 \<noteq> n\<^isub>2) \<and>
   (\<exists>as. (n -as\<rightarrow>* n\<^isub>1) \<and> (n\<^isub>2 \<notin> set (sourcenodes as))) \<and>
   (\<exists>as. (n -as\<rightarrow>* n\<^isub>2) \<and> (n\<^isub>1 \<notin> set (sourcenodes as))) \<and>
   (\<exists>a. (valid_edge a) \<and> (n = sourcenode a) \<and> 
        ((\<exists>as. (targetnode a -as\<rightarrow>* n\<^isub>1) \<and>  
               (\<forall>as'. (targetnode a -as'\<rightarrow>* n\<^isub>2) \<longrightarrow> n\<^isub>1 \<in> set(sourcenodes as'))) \<or>
         (\<exists>as. (targetnode a -as\<rightarrow>* n\<^isub>2) \<and>  
               (\<forall>as'. (targetnode a -as'\<rightarrow>* n\<^isub>1) \<longrightarrow> n\<^isub>2 \<in> set(sourcenodes as'))))))"




inductive_set (in CFG_wf) wod_backward_slice :: "'node \<Rightarrow> 'node set" 
for n :: "'node"
  where refl:"valid_node n \<Longrightarrow> n \<in> wod_backward_slice n"
  
  | cd_closed:
  "\<lbrakk>n' \<longrightarrow>\<^bsub>wod\<^esub> n\<^isub>1,n\<^isub>2; n\<^isub>1 \<in> wod_backward_slice n; n\<^isub>2 \<in> wod_backward_slice n\<rbrakk>
  \<Longrightarrow> n' \<in> wod_backward_slice n"

  | dd_closed:"\<lbrakk>n' influences V in n''; n'' \<in> wod_backward_slice n\<rbrakk>
  \<Longrightarrow> n' \<in> wod_backward_slice n"


lemma (in CFG_wf) 
  wod_backward_slice_valid_node:"n \<in> wod_backward_slice n\<^isub>c \<Longrightarrow> valid_node n"
by(induct rule:wod_backward_slice.induct,
   auto dest:path_valid_node simp:wod_def data_dependence_def)


end