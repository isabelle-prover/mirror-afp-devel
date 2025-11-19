(* Author: Tassilo Lemke *)

subsection \<open>Examples\<close>

(* TODO: Disjointness and Subset Problem *)

theory Applications_Example
imports Applications
begin

text\<open>Consider the following grammar, with \<open>V = {A,B,C,D}\<close> and \<open>\<Sigma> = {a,b,c,d}\<close>:\<close>

datatype n = A | B | C | D
datatype t = a | b | c | d

definition P :: "(n, t) Prods" where "P \<equiv> {
  \<comment>\<open>\<open>A \<rightarrow> a | BB | C\<close>\<close>
  (A, [Tm a]),
  (A, [Nt B, Nt B]),
  (A, [Nt C]),

  \<comment>\<open>\<open>B \<rightarrow> AB | b\<close>\<close>
  (B, [Nt A, Nt B]),
  (B, [Tm b]),

  \<comment>\<open>\<open>C \<rightarrow> c | \<epsilon>\<close>\<close>
  (C, [Tm c]),
  (C, []),

  \<comment>\<open>\<open>D \<rightarrow> d\<close>\<close>
  (D, [Tm d])
}"

text\<open>Checking whether a symbol is nullable is straight-forward:\<close>

value "is_nullable P A"
\<comment> \<open>@{value "is_nullable P A"}\<close>

value "is_nullable P B"
\<comment> \<open>@{value "is_nullable P B"}\<close>

value "is_nullable P C"
\<comment> \<open>@{value "is_nullable P C"}\<close>

value "is_nullable P D"
\<comment> \<open>@{value "is_nullable P D"}\<close>

text\<open>Instead of using \texttt{value}, it can also be proven by \texttt{eval} in theorems:\<close>

lemma "is_nullable P A" by eval

lemma "\<not> is_nullable P B" by eval

lemma "is_nullable P C" by eval

lemma "\<not> is_nullable P D" by eval

text\<open>Similarily, derivability can also be checked and proven as simple:\<close>

\<comment>\<open>\<open>A \<Rightarrow>* ABB\<close> is valid:\<close>
lemma "P \<turnstile> [Nt A] \<Rightarrow>* [Nt A, Nt B, Nt B]"
  by eval

\<comment>\<open>But \<open>A \<Rightarrow>* AB\<close> is not:\<close>
lemma "\<not> P \<turnstile> [Nt A] \<Rightarrow>* [Nt A, Nt B]"
  by eval

text\<open>Following derivability, the membership problem is straight-forward:\<close>

\<comment>\<open>\<open>a \<in> L(G)\<close>:\<close>
lemma "[a] \<in> Lang P A"
  by eval

\<comment>\<open>While \<open>b \<in> L(G)\<close>:\<close>
lemma "[b] \<notin> Lang P A"
  by eval

\<comment>\<open>But \<open>bb \<in> L(G)\<close> again holds:\<close>
lemma "[b,b] \<in> Lang P A"
  by eval

text\<open>
  To check if the accepted language is empty, one first needs to unfold @{thm is_empty_def},
  from which automatic evaluation is again possible:
\<close>

\<comment>\<open>Language obviously not empty:\<close>
lemma "\<not> Lang P A = {}"
  unfolding is_empty_def[symmetric] by eval

text\<open>
  Similar to derivability, reachability (i.e., derivability with an arbitrary prefix and suffix),
  can also be automated:
\<close>

lemma "P \<turnstile> A \<Rightarrow>\<^sup>? B"
  by eval

lemma "P \<turnstile> B \<Rightarrow>\<^sup>? A"
  by eval

lemma "P \<turnstile> A \<Rightarrow>\<^sup>? C"
  by eval

lemma "P \<turnstile> B \<Rightarrow>\<^sup>? C"
  by eval

lemma "\<not> P \<turnstile> C \<Rightarrow>\<^sup>? A"
  by eval

lemma "\<not> P \<turnstile> C \<Rightarrow>\<^sup>? A"
  by eval

end
