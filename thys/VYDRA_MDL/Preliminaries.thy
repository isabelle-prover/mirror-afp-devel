theory Preliminaries
  imports MDL
begin

section \<open>Formulas and Satisfiability\<close>

declare [[typedef_overloaded]]

context
begin

qualified datatype ('a, 't :: timestamp) formula = Bool bool | Atom 'a | Neg "('a, 't) formula" |
  Bin "bool \<Rightarrow> bool \<Rightarrow> bool" "('a, 't) formula" "('a, 't) formula" |
  Prev "'t \<I>" "('a, 't) formula" | Next "'t \<I>" "('a, 't) formula" |
  Since "('a, 't) formula" "'t \<I>" "('a, 't) formula" |
  Until "('a, 't) formula" "'t \<I>" "('a, 't) formula" |
  MatchP "'t \<I>" "('a, 't) regex" | MatchF "'t \<I>" "('a, 't) regex"
  and ('a, 't) regex = Test "('a, 't) formula" | Wild |
  Plus "('a, 't) regex" "('a, 't) regex" | Times "('a, 't) regex" "('a, 't) regex" |
  Star "('a, 't) regex"

end

fun mdl2mdl :: "('a, 't :: timestamp) Preliminaries.formula \<Rightarrow> ('a, 't) formula"
  and embed :: "('a, 't) Preliminaries.regex \<Rightarrow> ('a, 't) regex" where
  "mdl2mdl (Preliminaries.Bool b) = Bool b"
| "mdl2mdl (Preliminaries.Atom a) = Atom a"
| "mdl2mdl (Preliminaries.Neg phi) = Neg (mdl2mdl phi)"
| "mdl2mdl (Preliminaries.Bin f phi psi) = Bin f (mdl2mdl phi) (mdl2mdl psi)"
| "mdl2mdl (Preliminaries.Prev I phi) = Prev I (mdl2mdl phi)"
| "mdl2mdl (Preliminaries.Next I phi) = Next I (mdl2mdl phi)"
| "mdl2mdl (Preliminaries.Since phi I psi) = Since (mdl2mdl phi) I (mdl2mdl psi)"
| "mdl2mdl (Preliminaries.Until phi I psi) = Until (mdl2mdl phi) I (mdl2mdl psi)"
| "mdl2mdl (Preliminaries.MatchP I r) = MatchP I (Times (embed r) (Symbol (Bool True)))"
| "mdl2mdl (Preliminaries.MatchF I r) = MatchF I (Times (embed r) (Symbol (Bool True)))"
| "embed (Preliminaries.Test phi) = Lookahead (mdl2mdl phi)"
| "embed Preliminaries.Wild = Symbol (Bool True)"
| "embed (Preliminaries.Plus r s) = Plus (embed r) (embed s)"
| "embed (Preliminaries.Times r s) = Times (embed r) (embed s)"
| "embed (Preliminaries.Star r) = Star (embed r)"

lemma mdl2mdl_wf:
  fixes phi :: "('a, 't :: timestamp) Preliminaries.formula"
  shows "wf_fmla (mdl2mdl phi)"
  by (induction phi rule: mdl2mdl_embed.induct(1)[where ?Q="\<lambda>r. wf_regex (Times (embed r) (Symbol (Bool True))) \<and> (\<forall>phi \<in> atms (embed r). wf_fmla phi)"]) auto

fun embed' :: "(('a, 't :: timestamp) formula \<Rightarrow> ('a, 't) Preliminaries.formula) \<Rightarrow> ('a, 't) regex \<Rightarrow> ('a, 't) Preliminaries.regex" where
  "embed' f (Lookahead phi) = Preliminaries.Test (f phi)"
| "embed' f (Symbol phi) = Preliminaries.Times (Preliminaries.Test (f phi)) Preliminaries.Wild"
| "embed' f (Plus r s) = Preliminaries.Plus (embed' f r) (embed' f s)"
| "embed' f (Times r s) = Preliminaries.Times (embed' f r) (embed' f s)"
| "embed' f (Star r) = Preliminaries.Star (embed' f r)"

lemma embed'_cong[fundef_cong]: "(\<And>phi. phi \<in> atms r \<Longrightarrow> f phi = f' phi) \<Longrightarrow> embed' f r = embed' f' r"
  by (induction r) auto

fun mdl2mdl' :: "('a, 't :: timestamp) formula \<Rightarrow> ('a, 't) Preliminaries.formula" where
  "mdl2mdl' (Bool b) = Preliminaries.Bool b"
| "mdl2mdl' (Atom a) = Preliminaries.Atom a"
| "mdl2mdl' (Neg phi) = Preliminaries.Neg (mdl2mdl' phi)"
| "mdl2mdl' (Bin f phi psi) = Preliminaries.Bin f (mdl2mdl' phi) (mdl2mdl' psi)"
| "mdl2mdl' (Prev I phi) = Preliminaries.Prev I (mdl2mdl' phi)"
| "mdl2mdl' (Next I phi) = Preliminaries.Next I (mdl2mdl' phi)"
| "mdl2mdl' (Since phi I psi) = Preliminaries.Since (mdl2mdl' phi) I (mdl2mdl' psi)"
| "mdl2mdl' (Until phi I psi) = Preliminaries.Until (mdl2mdl' phi) I (mdl2mdl' psi)"
| "mdl2mdl' (MatchP I r) = Preliminaries.MatchP I (embed' mdl2mdl' (rderive r))"
| "mdl2mdl' (MatchF I r) = Preliminaries.MatchF I (embed' mdl2mdl' (rderive r))"

context MDL
begin

fun rvsat :: "('a, 't) Preliminaries.formula \<Rightarrow> nat \<Rightarrow> bool"
  and rvmatch :: "('a, 't) Preliminaries.regex \<Rightarrow> (nat \<times> nat) set" where
  "rvsat (Preliminaries.Bool b) i = b"
| "rvsat (Preliminaries.Atom a) i = (a \<in> \<Gamma> \<sigma> i)"
| "rvsat (Preliminaries.Neg \<phi>) i = (\<not> rvsat \<phi> i)"
| "rvsat (Preliminaries.Bin f \<phi> \<psi>) i = (f (rvsat \<phi> i) (rvsat \<psi> i))"
| "rvsat (Preliminaries.Prev I \<phi>) i = (case i of 0 \<Rightarrow> False | Suc j \<Rightarrow> mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> rvsat \<phi> j)"
| "rvsat (Preliminaries.Next I \<phi>) i = (mem (\<tau> \<sigma> i) (\<tau> \<sigma> (Suc i)) I \<and> rvsat \<phi> (Suc i))"
| "rvsat (Preliminaries.Since \<phi> I \<psi>) i = (\<exists>j\<le>i. mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> rvsat \<psi> j \<and> (\<forall>k \<in> {j<..i}. rvsat \<phi> k))"
| "rvsat (Preliminaries.Until \<phi> I \<psi>) i = (\<exists>j\<ge>i. mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I \<and> rvsat \<psi> j \<and> (\<forall>k \<in> {i..<j}. rvsat \<phi> k))"
| "rvsat (Preliminaries.MatchP I r) i = (\<exists>j\<le>i. mem (\<tau> \<sigma> j) (\<tau> \<sigma> i) I \<and> (j, i) \<in> rvmatch r)"
| "rvsat (Preliminaries.MatchF I r) i = (\<exists>j\<ge>i. mem (\<tau> \<sigma> i) (\<tau> \<sigma> j) I \<and> (i, j) \<in> rvmatch r)"
| "rvmatch (Preliminaries.Test \<phi>) = {(i, i) | i. rvsat \<phi> i}"
| "rvmatch Preliminaries.Wild = {(i, i + 1) | i. True}"
| "rvmatch (Preliminaries.Plus r s) = rvmatch r \<union> rvmatch s"
| "rvmatch (Preliminaries.Times r s) = rvmatch r O rvmatch s"
| "rvmatch (Preliminaries.Star r) = rtrancl (rvmatch r)"

lemma mdl2mdl_equivalent:
  fixes phi :: "('a, 't :: timestamp) Preliminaries.formula"
  shows "\<And>i. sat (mdl2mdl phi) i \<longleftrightarrow> rvsat phi i"
  by (induction phi rule: mdl2mdl_embed.induct(1)[where ?Q="\<lambda>r. match (embed r) = rvmatch r"]) (auto split: nat.splits)

lemma mdlstar2mdl:
  fixes phi :: "('a, 't :: timestamp) Preliminaries.formula"
  shows "wf_fmla (mdl2mdl phi)" "\<And>i. sat (mdl2mdl phi) i \<longleftrightarrow> rvsat phi i"
  apply (rule mdl2mdl_wf)
  apply (rule mdl2mdl_equivalent)
  done

lemma rvmatch_embed':
  assumes "\<And>phi i. phi \<in> atms r \<Longrightarrow> rvsat (mdl2mdl' phi) i \<longleftrightarrow> sat phi i"
  shows "rvmatch (embed' mdl2mdl' r) = match r"
  using assms
  by (induction r) auto

lemma mdl2mdlstar:
  fixes phi :: "('a, 't :: timestamp) formula"
  assumes "wf_fmla phi"
  shows "\<And>i. rvsat (mdl2mdl' phi) i \<longleftrightarrow> sat phi i"
  using assms
  apply (induction phi rule: mdl2mdl'.induct)
                apply (auto split: nat.splits)[8]
  subgoal for I r i
    by auto (metis atms_rderive match_rderive rvmatch_embed' wf_fmla.simps(1))+
  subgoal for I r i
    by auto (metis atms_rderive match_rderive rvmatch_embed' wf_fmla.simps(1))+
  done

end

end
