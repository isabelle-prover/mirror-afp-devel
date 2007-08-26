(*  Title:      InfDesc.thy
    Author:     Roelof Oosterhuis
                2007  Rijksuniversiteit Groningen
*)

header {* The proof method `infinite descent' *}

theory InfDesc 
  imports Main
begin

text {* The method of infinite descent, frequently used in number theory. Based on \textit{less-induct}. $P(n)$ is true for all $n\in\mathbb{N}$ if \begin{itemize}
  \item case ``0'': given $n=0$ prove $P(n)$,
  \item case ``smaller'': given $n>0$ and $\neg P(n)$ prove there exists a smaller integer $m$ such that $\neg P(m)$. \end{itemize} *}

lemma nat_infinite_descent: 
  "\<lbrakk> P 0; !!n. n>0 \<Longrightarrow> \<not> P n \<Longrightarrow> (\<exists>m::nat. m < n \<and> \<not>P m) \<rbrakk> \<Longrightarrow> P n"
  by (induct n rule: less_induct, case_tac "n>0", auto)

lemmas infinite_descent 
  = nat_infinite_descent [rule_format, case_names 0 smaller]

text {* Infinite descent using a mapping to $\mathbb{N}$: $P(x)$ is true for all $x\in D$ if there exists a $V: D \to \mathbb{N}$ and\begin{itemize}
\item case ``0'': given $V(x)=0$ prove $P(x)$,
\item case ``smaller'': given $V(x)>0$ and $\neg P(x)$ prove there exists a $y \in D$ such that $V(y)<V(x)$ and $~\neg P(y)$.\end{itemize} NB: the proof also shows how to use the previous lemma. *}

corollary nat_val_infinite_descent:
  fixes V:: "'a \<Rightarrow> nat" 
  assumes ass0: "!!x. V x = 0 \<Longrightarrow> P x" 
    and assn: "!!x. V x > 0 \<Longrightarrow> \<not>P x \<Longrightarrow> (\<exists>y. V y < V x \<and> \<not>P y)"
  shows "P x"
proof -
  obtain n where "n = V x" by auto
  moreover have "!!x. V x = (n::nat) \<Longrightarrow> P x"
  proof (induct n rule: infinite_descent)
    case 0 -- "i.e. $V(x) = 0$"
    with ass0 show "P x" by auto
  next -- "now $n>0$ and $P(x)$ does not hold for some $x$ with $V(x)=n$"
    case (smaller n) 
    then obtain x where vxn: "V x = n " and "V x > 0 \<and> \<not> P x" by auto
    with assn obtain y where "V y < V x \<and> \<not> P y" by auto
    with vxn obtain m where "m = V y \<and> m<n \<and> \<not> P y" by auto
    thus ?case by auto
  qed
  ultimately show "P x" by auto
qed
   
lemmas val_infinite_descent 
  = nat_val_infinite_descent [rule_format, case_names 0 smaller]

end