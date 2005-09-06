(*  Title:      HOL/MicroJava/BV/Product.thy
    ID:         $Id: Product.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Products as semilattices
*)

header {* \isaheader{Products as Semilattices} *}

theory Product imports Err begin

constdefs
  le :: "'a ord \<Rightarrow> 'b ord \<Rightarrow> ('a \<times> 'b) ord"
  "le r\<^isub>A r\<^isub>B \<equiv> \<lambda>(a\<^isub>1,b\<^isub>1) (a\<^isub>2,b\<^isub>2). a\<^isub>1 \<sqsubseteq>\<^bsub>r\<^isub>A\<^esub> a\<^isub>2 \<and> b\<^isub>1 \<sqsubseteq>\<^bsub>r\<^isub>B\<^esub> b\<^isub>2"

  sup :: "'a ebinop \<Rightarrow> 'b ebinop \<Rightarrow> ('a \<times> 'b) ebinop"
  "sup f g \<equiv> \<lambda>(a\<^isub>1,b\<^isub>1)(a\<^isub>2,b\<^isub>2). Err.sup Pair (a\<^isub>1 \<squnion>\<^sub>f a\<^isub>2) (b\<^isub>1 \<squnion>\<^sub>g b\<^isub>2)"

  esl :: "'a esl \<Rightarrow> 'b esl \<Rightarrow> ('a \<times> 'b ) esl"
  "esl \<equiv> \<lambda>(A,r\<^isub>A,f\<^isub>A) (B,r\<^isub>B,f\<^isub>B). (A \<times> B, le r\<^isub>A r\<^isub>B, sup f\<^isub>A f\<^isub>B)"

(*<*)
syntax
  "@lesubprod" :: "'a \<times> 'b \<Rightarrow> 'a ord \<Rightarrow> 'b ord \<Rightarrow> 'b \<Rightarrow> bool" 
  ("(_ /<='(_,_') _)" [50, 0, 0, 51] 50)
(*>*)

syntax (xsymbols)
  "@lesubprod" :: "'a \<times> 'b \<Rightarrow> 'a ord \<Rightarrow> 'b ord \<Rightarrow> 'b \<Rightarrow> bool" 
  ("(_ /\<sqsubseteq>'(_,_') _)" [50, 0, 0, 51] 50)

translations "p \<sqsubseteq>(rA,rB) q" == "p \<sqsubseteq>\<^bsub>Product.le rA rB\<^esub> q"

lemma unfold_lesub_prod: "x \<sqsubseteq>(r\<^isub>A,r\<^isub>B) y \<equiv> le r\<^isub>A r\<^isub>B x y"
(*<*) by (simp add: lesub_def) (*>*)

lemma le_prod_Pair_conv [iff]: "((a\<^isub>1,b\<^isub>1) \<sqsubseteq>(r\<^isub>A,r\<^isub>B) (a\<^isub>2,b\<^isub>2)) = (a\<^isub>1 \<sqsubseteq>\<^bsub>r\<^isub>A\<^esub> a\<^isub>2 & b\<^isub>1 \<sqsubseteq>\<^bsub>r\<^isub>B\<^esub> b\<^isub>2)"
(*<*) by (simp add: lesub_def le_def) (*>*)

lemma less_prod_Pair_conv:
  "((a\<^isub>1,b\<^isub>1) \<sqsubset>\<^bsub>Product.le r\<^isub>A r\<^isub>B\<^esub> (a\<^isub>2,b\<^isub>2)) = 
  (a\<^isub>1 \<sqsubset>\<^bsub>r\<^isub>A\<^esub> a\<^isub>2 & b\<^isub>1 \<sqsubseteq>\<^bsub>r\<^isub>B\<^esub> b\<^isub>2 | a\<^isub>1 \<sqsubseteq>\<^bsub>r\<^isub>A\<^esub> a\<^isub>2 & b\<^isub>1 \<sqsubset>\<^bsub>r\<^isub>B\<^esub> b\<^isub>2)"
(*<*)
apply (unfold lesssub_def)
apply simp
apply blast
done
(*>*)

lemma order_le_prod [iff]: "order(Product.le r\<^isub>A r\<^isub>B) = (order r\<^isub>A & order r\<^isub>B)"
(*<*)
apply (unfold order_def)
apply simp
apply safe
apply blast+
done 
(*>*)


lemma acc_le_prodI [intro!]:
  "\<lbrakk> acc r\<^isub>A; acc r\<^isub>B \<rbrakk> \<Longrightarrow> acc(Product.le r\<^isub>A r\<^isub>B)"
(*<*)
apply (unfold acc_def)
apply (rule wf_subset)
 apply (erule wf_lex_prod)
 apply assumption
apply (auto simp add: lesssub_def less_prod_Pair_conv lex_prod_def)
done
(*>*)


lemma closed_lift2_sup:
  "\<lbrakk> closed (err A) (lift2 f); closed (err B) (lift2 g) \<rbrakk> \<Longrightarrow> 
  closed (err(A\<times>B)) (lift2(sup f g))";
(*<*)
apply (unfold closed_def plussub_def lift2_def err_def' sup_def)
apply (simp split: err.split)
apply blast
done 
(*>*)

lemma unfold_plussub_lift2: "e\<^isub>1 \<squnion>\<^bsub>lift2 f\<^esub> e\<^isub>2 \<equiv> lift2 f e\<^isub>1 e\<^isub>2"
(*<*) by (simp add: plussub_def) (*>*)


lemma plus_eq_Err_conv [simp]:
  "\<lbrakk> x\<in>A; y\<in>A; semilat(err A, Err.le r, lift2 f) \<rbrakk> 
  \<Longrightarrow> (x \<squnion>\<^sub>f y = Err) = (\<not>(\<exists>z\<in>A. x \<sqsubseteq>\<^sub>r z \<and> y \<sqsubseteq>\<^sub>r z))"
(*<*)
proof -
  have plus_le_conv2:
    "\<And>r f z. \<lbrakk> z \<in> err A; semilat (err A, r, f); OK x \<in> err A; OK y \<in> err A;
                 OK x \<squnion>\<^sub>f OK y \<sqsubseteq>\<^sub>r z\<rbrakk> \<Longrightarrow> OK x \<sqsubseteq>\<^sub>r z \<and> OK y \<sqsubseteq>\<^sub>r z"
(*<*) by (rule semilat.plus_le_conv [THEN iffD1]) (*>*)
  case rule_context
  thus ?thesis
  apply (rule_tac iffI)
   apply clarify
   apply (drule OK_le_err_OK [THEN iffD2])
   apply (drule OK_le_err_OK [THEN iffD2])
   apply (drule semilat.lub[of _ _ _ "OK x" _ "OK y"])
        apply assumption
       apply assumption
      apply simp
     apply simp
    apply simp
   apply simp
  apply (case_tac "x \<squnion>\<^sub>f y")
   apply assumption
  apply (rename_tac "z")
  apply (subgoal_tac "OK z: err A")
  apply (frule plus_le_conv2)
       apply assumption
      apply simp
      apply blast
     apply simp
    apply (blast dest: semilat.orderI order_refl)
   apply blast
  apply (erule subst)
  apply (unfold semilat_def err_def' closed_def)
  apply simp
  done
qed
(*>*)

lemma err_semilat_Product_esl:
  "\<And>L\<^isub>1 L\<^isub>2. \<lbrakk> err_semilat L\<^isub>1; err_semilat L\<^isub>2 \<rbrakk> \<Longrightarrow> err_semilat(Product.esl L\<^isub>1 L\<^isub>2)"
(*<*)
apply (unfold esl_def Err.sl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
apply (simp (no_asm) only: semilat_Def)
apply (simp (no_asm_simp) only: semilat.closedI closed_lift2_sup)
apply (simp (no_asm) only: unfold_lesub_err Err.le_def unfold_plussub_lift2 sup_def)
apply (auto elim: semilat_le_err_OK1 semilat_le_err_OK2
            simp add: lift2_def  split: err.split)
apply (blast dest: semilat.orderI)
apply (blast dest: semilat.orderI)

apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst, subst OK_lift2_OK [symmetric], rule semilat.lub)
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp

apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst, subst OK_lift2_OK [symmetric], rule semilat.lub)
apply simp
apply simp
apply simp
apply simp
apply simp
apply simp
done 
(*>*)

end
