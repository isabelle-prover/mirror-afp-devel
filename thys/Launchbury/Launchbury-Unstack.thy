theory "Launchbury-Unstack"
imports Launchbury LaunchburyStacked LaunchburyMoreFree
begin

subsubsection {* Stacked evaluation implies original evaluation. *}

lemma forget_stack:
  assumes "\<Gamma> : \<Gamma>' \<Down> \<Delta> : \<Delta>'"
  and "supp S \<subseteq> supp (tl \<Gamma>')"
  shows "\<Gamma> : snd (hd \<Gamma>') \<Down>\<^bsub>S\<^esub> \<Delta> : snd (hd \<Delta>')"
using assms
proof (nominal_induct avoiding: S rule: LaunchburyStacked.reds.strong_induct)
case (Lambda \<Gamma> x y e \<Gamma>')
  show ?case
    by (auto intro: Launchbury.reds.intros)
next
case (Application n \<Gamma> \<Gamma>' \<Delta> \<Delta>' x e y \<Theta> \<Theta>' z  e' S)
  have "atom z \<sharp> \<Gamma>'" using Application by (simp add: fresh_Pair)
  hence "atom z \<sharp> map fst \<Gamma>'"
    by (induct \<Gamma>')(auto simp add: fresh_Cons fresh_Nil)
  moreover
  have  "atom z \<sharp> snd (hd \<Theta>')"
    using Application stack_not_empty[OF Application(24)]
    by (cases \<Theta>', auto simp add: fresh_Cons fresh_Pair)
  ultimately
  have fresh: "atom z \<sharp> (\<Gamma>, e, y, S, \<Delta>, \<Theta>, snd (hd \<Theta>'))"
    using Application
    by (simp add: fresh_Pair fresh_Cons fresh_at_base)[1]

  have "supp (y # S) \<subseteq> supp ( (x, App (Var n) y) # \<Gamma>')"
    using Application.prems(1)
    by (auto simp add: supp_Cons supp_Pair exp_assn.supp)
  hence hyp1: "\<Gamma> : e \<Down>\<^bsub>y # S\<^esub> \<Delta> : Lam [z]. e'" 
    by (rule Application.hyps(23)[simplified])
  have "supp S \<subseteq> supp \<Delta>'"
    using Application.prems(1)
    using stack_unchanged[OF Application.hyps(22)]
    by simp
  hence hyp2: "\<Delta> : e'[z::=y] \<Down>\<^bsub>S\<^esub> \<Theta> : snd (hd \<Theta>')"
    by (rule Application.hyps(25)[simplified])
   
  show ?case
    by (simp, rule Launchbury.Application[OF fresh hyp1 hyp2])
next
case (Variable y e \<Gamma> x \<Gamma>' \<Delta> z \<Delta>' S)
  have "supp (y # S) \<subseteq> supp ((x, Var y) # \<Gamma>')"
    using Variable.prems(1)
    by (auto simp add: supp_Cons supp_Pair exp_assn.supp)
  hence hyp: "delete y \<Gamma> : e \<Down>\<^bsub>y # S\<^esub> \<Delta> : z"
    by (rule Variable.hyps(3)[simplified])
  show ?case
    by (simp, rule Launchbury.Variable[OF `_ \<in> set _` hyp])   
next
case (Let as \<Gamma> x  \<Gamma>' body \<Delta> \<Delta>' S)
  have "supp S \<subseteq> supp \<Gamma>'"
    using Let.prems[simplified].
  hence hyp: "asToHeap as @ \<Gamma> : body \<Down>\<^bsub>S\<^esub> \<Delta> : snd (hd \<Delta>')"
    by (rule Let.hyps(6)[simplified])

  have "set (bn as) \<sharp>* S"
    using Let(3) using `supp S \<subseteq> supp \<Gamma>'`
    by (auto simp add: fresh_star_def fresh_def)

  hence fresh: "set (bn as) \<sharp>* (\<Gamma>, S)"
    using Let by (auto simp add: fresh_star_Pair)

  show ?case
    by (simp, rule Launchbury.Let[OF fresh Let.hyps(4) hyp])
qed

lemma forget_stack_nice:
  assumes "\<Gamma> : (x, e) # \<Gamma>' \<Down> \<Delta> : (x, z) # \<Delta>'"
  and "supp L \<subseteq> supp \<Gamma>'"
  shows "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
using forget_stack[OF assms(1)] assms(2) by auto

subsubsection {* Original evaluation implies stacked evaluation. *}

lemma add_stack:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  assumes "x \<in> set L"
  assumes "supp \<Gamma>' \<subseteq> supp L"
  shows "\<Gamma> : (x,e) # \<Gamma>' \<Down> \<Delta> : (x,z) # \<Gamma>'"
using assms
proof (nominal_induct avoiding: \<Gamma>' x rule: reds_with_n_strong_induct)
case (Lambda \<Gamma> xa e L \<Gamma>')
  show ?case
    by (auto intro: LaunchburyStacked.reds.intros)
next
case (Application y \<Gamma> e xa L \<Delta> \<Theta> z n e' \<Gamma>' x)
  have fresh_n: "atom n \<sharp> (\<Gamma>, \<Gamma>', \<Delta>, \<Gamma>', x, e, xa, \<Theta>, (x, z) # \<Gamma>', y)"
    using Application
    by (simp add: fresh_Pair fresh_Cons fresh_at_base)

  have fresh_y: "atom y \<sharp> (\<Gamma>, \<Gamma>', \<Delta>, \<Gamma>', x, e, xa, \<Theta>, (x, z) # \<Gamma>')"
    using Application
    by (simp add: fresh_Pair fresh_Cons)

  have "supp ((x, App (Var n) xa) # \<Gamma>') \<subseteq> supp (n # xa # L)"
     using set_mp[OF supp_set_mem[OF `x \<in> set L`]] set_mp[OF `supp \<Gamma>' \<subseteq> supp L`]
     by (auto simp add: supp_Pair supp_Cons exp_assn.supp)
  hence hyp1: "\<Gamma> : (n, e) # (x, App (Var n) xa) # \<Gamma>' \<Down> \<Delta> : (n, Lam [y]. e') # (x, App (Var n) xa) # \<Gamma>'"
    apply (rule Application(21)[rotated])
    apply simp
    done
 
  have hyp2: "\<Delta> : (x, e'[y::=xa]) # \<Gamma>' \<Down> \<Theta> : (x, z) # \<Gamma>'"
    apply (rule Application(23)[OF Application.prems])
    done

  show ?case
    by (rule LaunchburyStacked.reds.Application[OF fresh_n fresh_y hyp1 hyp2])
next
case (Variable x e \<Gamma> L \<Delta> z \<Gamma>' xa)
  have "supp ((xa, Var x) # \<Gamma>') \<subseteq> supp (x # L)"
     using set_mp[OF supp_set_mem[OF `xa \<in> set L`]] set_mp[OF `supp \<Gamma>' \<subseteq> supp L`]
     by (auto simp add: supp_Pair supp_Cons exp_assn.supp)
  hence hyp: "delete x \<Gamma> : (x, e) # (xa, Var x) # \<Gamma>' \<Down> \<Delta> : (x, z) # (xa, Var x) # \<Gamma>'"
    apply (rule Variable.hyps(3)[rotated])
    apply (simp)
    done
  show ?case
    by (rule LaunchburyStacked.reds.Variable[OF `(x,e) \<in> set _` hyp])
next
case (Let as \<Gamma> L body \<Delta> z \<Gamma>' x)
  from `x \<in> set L` and `_ \<sharp>* L`
  have [simp]:"set (bn as) \<sharp>* x"
    by (metis fresh_star_Cons fresh_star_list(1) in_set_conv_decomp)

  from `supp \<Gamma>' \<subseteq> supp L` and `_ \<sharp>* L`
  have [simp]:"set (bn as) \<sharp>* \<Gamma>'"
    by (auto simp add: fresh_star_def fresh_def)

  have fresh: "set (bn as) \<sharp>* (\<Gamma>, x, \<Gamma>')"
    using Let(1-3)
    by (simp add: fresh_star_Pair)
 
  have hyp: "asToHeap as @ \<Gamma> : (x, body) # \<Gamma>' \<Down> \<Delta> : (x, z) # \<Gamma>'"
    apply (rule Let.hyps(5)[OF Let.prems])
    done

  show ?case
    by (rule LaunchburyStacked.reds.Let[OF fresh `distinctVars (asToHeap as)` hyp])
qed

end
