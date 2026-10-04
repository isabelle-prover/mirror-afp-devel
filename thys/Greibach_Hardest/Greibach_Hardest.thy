(*
Author: Claude, Tobias Nipkow
*)

section \<open>Greibach's Hardest Context-Free Language\<close>

theory Greibach_Hardest
imports
  "Context_Free_Grammar.Context_Free_Language"
  "Greibach_Normal_Form.Greibach_Normal_Form"
  "Dyck_Language.Dyck_Language"
begin

text \<open>
  Formalization of Theorem 2.1 by Sheila Greibach \cite{Greibach73}:

  \textbf{Theorem} For every context-free language \<open>L\<close> there is a homomorphism \<open>h\<close> with
  \<open>L - {\<epsilon>} = h\<^sup>-\<^sup>1(L\<^sub>0 - {\<epsilon>})\<close>, where \<open>L\<^sub>0\<close> is one fixed ``hardest'' context-free language.

  The construction encodes the leftmost derivations of a
  Greibach Normal Form (GNF) grammar as a nondeterministic Dyck word (the encoding homomorphism \<open>enc_h\<close>);
  the general case is reduced to GNF using the AFP entry \verb!Greibach_Normal_Form! (the function \<open>gnf_of\<close>).
\<close>

(* TODO globalize in CFG? Replace current usage of ^^ in CFG? *)
abbreviation Cons_power :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" (infixl "#^" 70) where
"a #^ n \<equiv> replicate n a"

(* TODO rm with next release; should all exist already *)
lemma bal_stk_append_split:
  assumes "bal_stk s (xs @ ys) = (t, [])"
  obtains s' where "bal_stk s xs = (s', [])" and "bal_stk s' ys = (t, [])"
  using assms by (auto simp: bal_stk_append split: prod.splits if_splits)
lemma bal_stk_replicate_Open: "bal_stk s (Open a #^i) = (a#^i @ s, [])"
  by (induction i arbitrary: s) (auto simp: replicate_append_same)
lemma bal_stk_replicate_Close: "bal_stk (a#^i @ t) (Close a #^ i) = (t, [])"
  by (induction i arbitrary: t) auto
lemma bal_stk_replicate_Close_inv:
  "bal_stk t (replicate i (Close a) @ rest) = (s, []) \<Longrightarrow>
   \<exists>t'. t = replicate i a @ t' \<and> bal_stk t' rest = (s, [])"
proof (induction i arbitrary: t)
  case 0 thus ?case by auto
next
  case (Suc i)
  from Suc.prems obtain b t1 where t: "t = b # t1" by (cases t) auto
  with Suc.prems have "a = b" "bal_stk t1 (replicate i (Close a) @ rest) = (s, [])"
    by (auto split: if_splits)
  with Suc.IH obtain t' where "t1 = replicate i a @ t'" "bal_stk t' rest = (s, [])" by blast
  with t \<open>a = b\<close> show ?case by auto
qed
lemmas derives_Nt_map_TmD = derives_start1
lemma Lang_lfp_unfold:
  "Lang_lfp P A = (\<Union>\<alpha> \<in> Rhss P A. inst_syms (Lang_lfp P) \<alpha>)"
unfolding Lang_lfp_def
using fun_cong[OF subst_lang_def[of P "lfp(subst_lang P)"], of A,symmetric]
by (metis lfp_unfold[OF mono_if_omega_cont[OF omega_cont_Lang_lfp]])
corollary Lang_unfold: "Lang P A = (\<Union>\<alpha> \<in> Rhss P A. inst_syms (Lang P) \<alpha>)"
  by(fact Lang_lfp_unfold[unfolded Lang_lfp_eq_Lang])
lemma concats_simps[simp]:
  "concats [] = {[]}"
  "concats (L#Ls) = L @@ concats Ls"
  by(auto simp: concats_def)
lemma concats_append[simp]: "concats (Ls1 @ Ls2) = concats Ls1 @@ concats Ls2"
by (simp add: concats_def foldr_conc_conc)
lemma inst_sym_simps[simp]:
  "inst_sym L (Tm a) = {[a]}"
  "inst_sym L (Nt A) = L A"
by(auto simp: inst_sym_def)
lemma inst_syms_Nil[simp]: "inst_syms L [] = {[]}"
by(simp add: inst_syms_def)
lemma inst_syms_Cons[simp]: "inst_syms L (s # \<beta>) = inst_sym L s @@ inst_syms L \<beta>"
  by(simp add: inst_syms_def)
lemma inst_syms_append[simp]: "inst_syms L (\<alpha> @ \<beta>) = inst_syms L \<alpha> @@ inst_syms L \<beta>"
by(simp add: inst_syms_def)
lemma Lang_I: "(A, \<alpha>) \<in> P \<Longrightarrow> w \<in> inst_syms (Lang P) \<alpha> \<Longrightarrow> w \<in> Lang P A"
  by (subst Lang_unfold) (auto simp: Rhss_def)
lemma Lang_subset_if:
  assumes "\<And>A \<alpha>. (A,\<alpha>) \<in> P \<Longrightarrow> inst_syms R \<alpha> \<subseteq> R A"
  shows "Lang P A \<subseteq> R A"
proof -
  have "subst_lang P R \<le> R"
    using assms by (fastforce simp: subst_lang_def le_fun_def Rhss_def)
  hence "lfp (subst_lang P) \<le> R" by (rule lfp_lowerbound)
  hence "Lang_lfp P \<le> R" by (simp add: Lang_lfp_def)
  thus ?thesis by (simp add: Lang_lfp_eq_Lang le_fun_def)
qed

subsection \<open>The hardest language \<open>L\<^sub>0\<close>\<close>

subsubsection \<open>The terminal alphabet of \<open>L\<^sub>0\<close>\<close>

text \<open>Greibach's alphabet is \<open>T = {a\<^sub>1, a\<^sub>2, \<bar>a\<^sub>1, \<bar>a\<^sub>2, c, \<cent>}\<close> together with a fresh separator \<open>d\<close>.
  There are two bracket \<^emph>\<open>kinds\<close> \<open>a\<^sub>1, a\<^sub>2\<close>, modelled by the type \<open>t0_A\<close>. A bracket letter is \<open>Aa\<close>
  applied to an opening or closing bracket (of type @{typ \<open>'a bracket\<close>}) over a kind: thus
  \<open>Aa (Open A1) = a\<^sub>1\<close>, \<open>Aa (Close A1) = \<bar>a\<^sub>1\<close>, and analogously for \<open>a\<^sub>2\<close>. The remaining letters are
  \<open>Cc\<close> for \<open>c\<close>, \<open>Ce\<close> for \<open>\<cent>\<close>, and \<open>Dd\<close> for \<open>d\<close>.\<close>

datatype t0_A = A1 | A2

datatype t0 = Aa "t0_A bracket" | Cc | Ce | Dd

subsubsection \<open>The Dyck set \<open>D\<close> on two letters\<close>

text \<open>\<open>D\<close> is the Dyck set generated by \<open>S \<rightarrow> SS \<bar> a\<^sub>1 S \<bar>a\<^sub>1 \<bar> a\<^sub>2 S \<bar>a\<^sub>2 \<bar> \<epsilon>\<close>, i.e.\ the set of
  balanced words over the two bracket pairs \<open>(a\<^sub>1, \<bar>a\<^sub>1)\<close> and \<open>(a\<^sub>2, \<bar>a\<^sub>2)\<close>. As each bracket letter
  \<open>Aa b\<close> already carries a @{typ \<open>t0_A bracket\<close>}, we reuse @{const Dyck_Language.bal} directly via the
  projection \<open>brk\<close>; no separate integer tagging is needed.\<close>

fun brk :: "t0 \<Rightarrow> t0_A bracket" where
  "brk (Aa b) = b"

definition bracks :: "t0 set" where
  "bracks = Aa ` UNIV"

definition D :: "t0 list set" where
  "D = {w. set w \<subseteq> bracks \<and> bal (map brk w)}"

subsubsection \<open>The hardest language \<open>L\<^sub>0\<close>\<close>

text \<open>The alphabet \<open>T\<close> (note: \<open>d \<notin> T\<close>, since \<open>d\<close> separates the blocks):\<close>

definition Talph :: "t0 set" where
  "Talph = insert Cc (insert Ce bracks)"

text \<open>A single block \<open>x c y c z d\<close>:\<close>

definition blk :: "t0 list \<times> t0 list \<times> t0 list \<Rightarrow> t0 list" where
  "blk = (\<lambda>(x,y,z). x @ Cc # y @ Cc # z @ [Dd])"

text \<open>\<open>L\<^sub>0 = {\<epsilon>} \<union> {x\<^sub>1 c y\<^sub>1 c z\<^sub>1 d \<dots> x\<^sub>n c y\<^sub>n c z\<^sub>n d \<bar> n \<ge> 1, y\<^sub>1\<dots>y\<^sub>n \<in> \<cent>D, x\<^sub>i z\<^sub>i \<in> T\<^sup>*,
   y\<^sub>i \<in> {a\<^sub>1,a\<^sub>2,\<bar>a\<^sub>1,\<bar>a\<^sub>2}\<^sup>* for i \<ge> 2}\<close>. The \<open>n\<close> blocks are given by a non-empty list of triples
  \<open>bs = [(x\<^sub>1,y\<^sub>1,z\<^sub>1), \<dots>]\<close>; the constraint \<open>y\<^sub>i \<in> brackets\<close> for \<open>i \<ge> 2\<close> is \<open>tl bs\<close>; and
  \<open>y\<^sub>1\<dots>y\<^sub>n \<in> \<cent>D\<close> means the concatenation of the \<open>y\<close>s is \<open>\<cent>\<close> followed by a word of \<open>D\<close>.\<close>

definition L0 :: "t0 list set" where
  "L0 = {[]} \<union>
    { concat (map blk bs) | bs.
        bs \<noteq> [] \<and>
        (\<forall>(x,y,z) \<in> set bs. set x \<subseteq> Talph \<and> set z \<subseteq> Talph) \<and>
        (\<forall>(x,y,z) \<in> set (tl bs). set y \<subseteq> bracks) \<and>
        (\<exists>v \<in> D. concat (map (\<lambda>(x,y,z). y) bs) = Ce # v) }"

subsection \<open>Homomorphisms\<close>

text \<open>A (string) homomorphism is determined by its action \<open>h\<close> on single letters and lifts to words
  by \<^term>\<open>\<lambda>w. concat (map h w)\<close>. The inverse image of a language under it:\<close>

definition inv_hom :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'b list set \<Rightarrow> 'a list set" where
  "inv_hom h L = {w. concat (map h w) \<in> L}"

text \<open>The nonterminals \<open>Y\<^sub>1, \<dots>, Y\<^sub>n\<close> (with \<open>Y\<^sub>1 = S\<close>) are identified with natural-number indices via an
  injective map \<open>idx\<close> (only injectivity matters; the specific values, in particular \<open>idx S\<close>, are
  immaterial). The nonterminal \<open>Y\<^sub>i\<close> is encoded in unary: it is
  \<^emph>\<open>pushed\<close> as \<open>a\<^sub>1 a\<^sub>2\<^sup>i a\<^sub>1\<close> and \<^emph>\<open>popped\<close> as \<open>\<bar>a\<^sub>1 \<bar>a\<^sub>2\<^sup>i \<bar>a\<^sub>1\<close>.\<close>

definition pushcode :: "nat \<Rightarrow> t0 list" where
  "pushcode i = Aa (Open A1) # (Aa (Open A2) #^ i) @ [Aa (Open A1)]"

definition popcode :: "nat \<Rightarrow> t0 list" where
  "popcode i = Aa (Close A1) # (Aa (Close A2) #^ i) @ [Aa (Close A1)]"

text \<open>\<open>\<xi>(p)\<close> for a standard-form production \<open>p = (Y\<^sub>i \<rightarrow> a Y\<^sub>j\<^sub>1 \<dots> Y\<^sub>j\<^sub>m)\<close>: pop \<open>Y\<^sub>i\<close>, then push the
  right-hand-side nonterminals. The pushes are in \<^emph>\<open>reverse\<close> order so that, with the standard Dyck
  convention (a closing bracket matches the nearest \<^emph>\<open>left\<close> opening, i.e.\ LIFO), the stack is
  encoded with its top (the leftmost / next-to-expand nonterminal) at the \<^emph>\<open>right\<close>: expanding the
  top \<open>Y\<^sub>i\<close> pops it and the new nonterminals \<open>Y\<^sub>j\<^sub>1 \<dots> Y\<^sub>j\<^sub>m\<close> become the new top, \<open>Y\<^sub>j\<^sub>1\<close> rightmost.\<close>

definition xi :: "('n \<Rightarrow> nat) \<Rightarrow> ('n,'t) prod \<Rightarrow> t0 list" where
  "xi idx p =
     popcode (idx (fst p)) @
     concat (map (\<lambda>s. case s of Nt B \<Rightarrow> pushcode (idx B) | Tm _ \<Rightarrow> []) (rev (tl (snd p))))"

text \<open>\<open>\<xi>\<^bsup>^\<^esup>(p)\<close>: for productions of the start symbol \<open>S\<close>, prepend \<open>\<cent>\<close> and the push code of \<open>S\<close>
  (which initializes the stack with \<open>S\<close> and the marker \<open>\<cent>\<close>).\<close>

definition xihat :: "('n \<Rightarrow> nat) \<Rightarrow> 'n \<Rightarrow> ('n,'t) prod \<Rightarrow> t0 list" where
  "xihat idx S p = (if fst p = S then Ce # pushcode (idx S) @ xi idx p else xi idx p)"

text \<open>\<open>h(a) = c \<xi>\<^bsup>^\<^esup>(p\<^sub>1) c \<dots> c \<xi>\<^bsup>^\<^esup>(p\<^sub>m) c d\<close>, where \<open>p\<^sub>1, \<dots>, p\<^sub>m\<close> are all productions whose
  right-hand side starts with the terminal \<open>a\<close>.\<close>

definition enc_h :: "('n \<Rightarrow> nat) \<Rightarrow> 'n \<Rightarrow> ('n,'t) prods \<Rightarrow> 't \<Rightarrow> t0 list" where
  "enc_h idx S ps a =
     concat (map (\<lambda>p. Cc # xihat idx S p)
                 (filter (\<lambda>p. \<exists>Bs. snd p = Tm a # map Nt Bs) ps))
     @ [Cc, Dd]"

subsection \<open>Basic machinery\<close>

subsubsection \<open>Stack machinery: running the encoded brackets through @{const bal_stk}\<close>

text \<open>The bracket image of a word over \<open>t0\<close>:\<close>

abbreviation brks :: "t0 list \<Rightarrow> t0_A bracket list" where
  "brks w \<equiv> map brk w"

text \<open>A single nonterminal \<open>Y\<^sub>i\<close> occupies the stack fragment \<open>frag i\<close>; a whole nonterminal stack
  (top first) is encoded by \<open>stkenc\<close>. With the cons-stack of @{const bal_stk} (top = head), reading
  \<open>pushcode i\<close> pushes \<open>frag i\<close> and reading \<open>popcode i\<close> pops it.\<close>

definition frag :: "nat \<Rightarrow> t0_A list" where
  "frag i = A1 # A2#^i @ [A1]"

definition stkenc :: "nat list \<Rightarrow> t0_A list" where
  "stkenc cs = concat (map frag cs)"

lemma bal_stk_pushcode: "bal_stk s (brks (pushcode i)) = (frag i @ s, [])"
by (simp add: bal_stk_append bal_stk_replicate_Open frag_def pushcode_def)

lemma bal_stk_popcode: "bal_stk (frag i @ s) (brks (popcode i)) = (s, [])"
by (simp add: popcode_def frag_def bal_stk_append bal_stk_replicate_Close)

text \<open>Reading the concatenated push codes of a list of nonterminal indices pushes the whole
  encoded stack (note the reversal: the first index ends up deepest).\<close>

lemma bal_stk_pushes:
  "bal_stk s (brks (concat (map pushcode is))) = (stkenc (rev is) @ s, [])"
proof (induction "is" arbitrary: s)
  case Nil show ?case by (simp add: stkenc_def)
next
  case (Cons i "is")
  thus ?case by (simp add: bal_stk_append bal_stk_pushcode stkenc_def)
qed

text \<open>The right-hand side of @{const xi} as an explicit pop followed by pushes.\<close>

lemma xi_eq:
  "snd p = Tm a # map Nt Bs \<Longrightarrow>
   xi idx p = popcode (idx (fst p)) @ concat (map pushcode (rev (map idx Bs)))"
  by (simp add: xi_def rev_map o_def)

text \<open>Running \<open>\<xi>(p)\<close> for a standard-form production \<open>p = (A \<rightarrow> a B\<^sub>1 \<dots> B\<^sub>m)\<close> on a stack whose top is
  \<open>A\<close>: it pops \<open>A\<close> and pushes \<open>B\<^sub>1 \<dots> B\<^sub>m\<close> (with \<open>B\<^sub>1\<close> becoming the new top), exactly modelling one
  leftmost derivation step.\<close>

lemma bal_stk_xi:
  assumes "snd p = Tm a # map Nt Bs"
  shows "bal_stk (frag (idx (fst p)) @ s) (brks (xi idx p)) = (stkenc (map idx Bs) @ s, [])"
by (simp add: xi_eq[OF assms] bal_stk_append bal_stk_popcode bal_stk_pushes)

subsubsection \<open>Letters occurring in the encoded words\<close>

lemma set_pushcode: "set (pushcode i) \<subseteq> bracks" by (auto simp: pushcode_def bracks_def)
lemma set_popcode: "set (popcode i) \<subseteq> bracks" by (auto simp: popcode_def bracks_def)

text \<open>A \<open>\<xi>\<close>-code uses only the four bracket letters; a \<open>\<xi>\<^bsup>^\<^esup>\<close>-code may additionally use \<open>\<cent>\<close>.\<close>

lemma set_xi: "set (xi idx p) \<subseteq> bracks"
  unfolding xi_def using set_popcode set_pushcode by (auto)

lemma set_xihat: "set (xihat idx S p) \<subseteq> insert Ce bracks"
using set_xi[of idx p] set_pushcode[of "idx S"] by (auto simp: xihat_def)

text \<open>For productions not expanding the start symbol, \<open>\<xi>\<^bsup>^\<^esup>\<close> coincides with \<open>\<xi>\<close>.\<close>

lemma map_xihat_no_S:
  "\<forall>p \<in> set ps. fst p \<noteq> S \<Longrightarrow> map (xihat idx S) ps = map (xi idx) ps"
  by (induction ps) (auto simp: xihat_def)

subsubsection \<open>Block decomposition of the encoded word\<close>

lemma set_xihat_Talph: "set (xihat idx S q) \<subseteq> Talph"
  using set_xihat[of idx S q] by (auto simp: Talph_def bracks_def)

lemma set_Cc_xihat: "set (Cc # xihat idx S q) \<subseteq> Talph"
  using set_xihat_Talph[of idx S q] by (auto simp: Talph_def)

lemma set_concat_Cc_xihat: "set (concat (map (\<lambda>q. Cc # xihat idx S q) qs)) \<subseteq> Talph"
using set_Cc_xihat[where idx=idx] by auto

lemma set_concat_xihat_Cc: "set (concat (map (\<lambda>q. xihat idx S q @ [Cc]) qs)) \<subseteq> Talph"
using set_Cc_xihat[where idx=idx] by auto

text \<open>Single-\<open>c\<close> separators: peeling a leading \<open>c\<close> off the \<open>c d\<close>-terminated block body turns the
  \<open>c\<close>-prefixed fragments into \<open>c\<close>-suffixed ones. This is the key rewriting for splitting a block at
  a chosen production.\<close>

lemma cc_shift2:
  "concat (map (\<lambda>p. Cc # xihat idx S p) qs) @ [Cc, Dd]
   = Cc # concat (map (\<lambda>q. xihat idx S q @ [Cc]) qs) @ [Dd]"
  by (induction qs) auto

text \<open>One block of \<open>enc_h idx S P a\<close>: any production \<open>p\<close> of \<open>P\<close> whose right-hand side starts with
  \<open>Tm a\<close> can be selected as the middle \<open>y\<close>, the surrounding \<open>x z\<close> (the other c-delimited fragments)
  being words over \<open>T\<close>.\<close>

lemma enc_h_block:
  assumes pin: "p \<in> set P" and snd_p: "snd p = Tm a # map Nt Bs"
  shows "\<exists>x z. enc_h idx S P a = blk (x, xihat idx S p, z) \<and> set x \<subseteq> Talph \<and> set z \<subseteq> Talph"
proof -
  have "p \<in> set (filter (\<lambda>p. \<exists>Bs. snd p = Tm a # map Nt Bs) P)" using pin snd_p by auto
  then obtain qs1 qs2 where split: "filter (\<lambda>p. \<exists>Bs. snd p = Tm a # map Nt Bs) P = qs1 @ p # qs2"
    by (meson split_list)
  define x where "x = concat (map (\<lambda>p. Cc # xihat idx S p) qs1)"
  define z where "z = concat (map (\<lambda>q. xihat idx S q @ [Cc]) qs2)"
  have "enc_h idx S P a = blk (x, xihat idx S p, z)" by (simp add: blk_def x_def z_def cc_shift2 enc_h_def split)
  moreover have "set x \<subseteq> Talph" unfolding x_def by (rule set_concat_Cc_xihat)
  moreover have "set z \<subseteq> Talph" unfolding z_def by (rule set_concat_xihat_Cc)
  ultimately show ?thesis by blast
qed

text \<open>Lifting the block decomposition over a whole word: given a list of productions matching the
  letters of \<open>w\<close>, the encoded word \<open>h(w)\<close> is a concatenation of blocks whose middles are exactly the
  \<open>\<xi>\<^bsup>^\<^esup>\<close>-codes of the productions.\<close>

lemma block_decomp:
  "list_all2 (\<lambda>b p. p \<in> set P \<and> (\<exists>Bs. snd p = Tm b # map Nt Bs)) w ps \<Longrightarrow>
   \<exists>bs. concat (map (enc_h idx S P) w) = concat (map blk bs)
      \<and> map (\<lambda>(x,y,z). y) bs = map (xihat idx S) ps
      \<and> (\<forall>(x,y,z) \<in> set bs. set x \<subseteq> Talph \<and> set z \<subseteq> Talph)"
proof (induction w ps rule: list_all2_induct)
  case Nil
  show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons b w' p ps')
  from Cons.hyps(1) obtain Bs where pin: "p \<in> set P" and snd_p: "snd p = Tm b # map Nt Bs" by blast
  from enc_h_block[OF pin snd_p] obtain x z where
    blk_eq: "enc_h idx S P b = blk (x, xihat idx S p, z)" and
    xT: "set x \<subseteq> Talph" and zT: "set z \<subseteq> Talph" by blast
  from Cons.IH obtain bs where
    bs_eq: "concat (map (enc_h idx S P) w') = concat (map blk bs)" and
    bs_y: "map (\<lambda>(x,y,z). y) bs = map (xihat idx S) ps'" and
    bs_T: "\<forall>(x,y,z) \<in> set bs. set x \<subseteq> Talph \<and> set z \<subseteq> Talph" by blast
  let ?bs = "(x, xihat idx S p, z) # bs"
  have "concat (map (enc_h idx S P) (b # w')) = concat (map blk ?bs)"
    by (simp add: blk_eq bs_eq)
  moreover have "map (\<lambda>(x,y,z). y) ?bs = map (xihat idx S) (p # ps')" by (simp add: bs_y)
  moreover have "\<forall>(x,y,z) \<in> set ?bs. set x \<subseteq> Talph \<and> set z \<subseteq> Talph" using xT zT bs_T by auto
  ultimately show ?case by blast
qed

subsubsection \<open>Inverting the stack machinery (for the backward direction)\<close>

text \<open>The fragment \<open>frag i = A1 A2\<^sup>i A1\<close> determines \<open>i\<close> and the rest uniquely as a prefix.\<close>

lemma frag_append_inj:
  "frag i @ xs = frag j @ ys \<Longrightarrow> i = j \<and> xs = ys"
unfolding frag_def by (auto simp add: append_Cons_eq_append_Cons)

lemma stkenc_eq_Nil: "stkenc cs = [] \<Longrightarrow> cs = []"
  by (cases cs) (auto simp: stkenc_def frag_def)

text \<open>Inverse of @{thm [source] bal_stk_popcode}: a successful pop forces the stack to start with
  the matching fragment.\<close>

lemma bal_stk_popcode_inv:
  assumes "bal_stk t (brks (popcode i)) = (s, [])" shows "t = frag i @ s"
proof -
  from assms have A: "bal_stk t (replicate 1 (Close A1) @ (replicate i (Close A2) @ [Close A1])) = (s, [])"
    by (simp add: popcode_def)
  from bal_stk_replicate_Close_inv[OF A] obtain t1 where
    t1: "t = replicate 1 A1 @ t1" and
    B: "bal_stk t1 (replicate i (Close A2) @ [Close A1]) = (s, [])" by blast
  from bal_stk_replicate_Close_inv[OF B] obtain t2 where
    t2: "t1 = replicate i A2 @ t2" and C: "bal_stk t2 [Close A1] = (s, [])" by blast
  have "t2 = A1 # s"
  proof (cases t2)
    case Nil thus ?thesis using C by simp
  next
    case (Cons c t3) thus ?thesis using C by (auto split: if_splits)
  qed
  with t1 t2 show "t = frag i @ s" by (simp add: frag_def)
qed

text \<open>Inverse of @{thm [source] bal_stk_xi}: if running \<open>\<xi>(p)\<close> on the encoded stack \<open>\<alpha>\<close> consumes all
  input, then \<open>\<alpha>\<close>'s top is \<open>fst p\<close> (this uses injectivity of \<open>idx\<close>) and the resulting stack is the
  encoding of \<open>Bs\<close> on top of the remaining stack.\<close>

lemma bal_stk_xi_inv:
  assumes inj: "inj_on idx N" and snd_p: "snd p = Tm a # map Nt Bs"
    and fpN: "fst p \<in> N" and \<alpha>N: "set \<alpha> \<subseteq> N"
    and run: "bal_stk (stkenc (map idx \<alpha>)) (brks (xi idx p)) = (s, [])"
  shows "\<exists>\<alpha>'. \<alpha> = fst p # \<alpha>' \<and> s = stkenc (map idx (Bs @ \<alpha>'))"
proof -
  from run snd_p have
    "bal_stk (stkenc (map idx \<alpha>))
       (brks (popcode (idx (fst p))) @ brks (concat (map pushcode (rev (map idx Bs))))) = (s, [])"
    by (simp add: xi_eq)
  then obtain s' where
    pop: "bal_stk (stkenc (map idx \<alpha>)) (brks (popcode (idx (fst p)))) = (s', [])" and
    push: "bal_stk s' (brks (concat (map pushcode (rev (map idx Bs))))) = (s, [])"
    by (rule bal_stk_append_split)
  from bal_stk_popcode_inv[OF pop] have stk_eq: "stkenc (map idx \<alpha>) = frag (idx (fst p)) @ s'" .
  have s_eq: "s = stkenc (map idx Bs) @ s'"
    using bal_stk_pushes[of s' "rev (map idx Bs)"] push by simp
  have "\<alpha> \<noteq> []"
  proof
    assume "\<alpha> = []" with stk_eq show False by (simp add: frag_def stkenc_def)
  qed
  then obtain A' \<alpha>' where \<alpha>c: "\<alpha> = A' # \<alpha>'" by (cases \<alpha>) auto
  with stk_eq have "frag (idx A') @ stkenc (map idx \<alpha>') = frag (idx (fst p)) @ s'"
    by (simp add: stkenc_def)
  from frag_append_inj[OF this] have iA: "idx A' = idx (fst p)" and seq': "stkenc (map idx \<alpha>') = s'"
    by auto
  from \<alpha>c \<alpha>N have "A' \<in> N" by simp
  with iA inj fpN have "A' = fst p" by (auto dest: inj_onD)
  with \<alpha>c have "\<alpha> = fst p # \<alpha>'" by simp
  moreover have "s = stkenc (map idx (Bs @ \<alpha>'))"
    using s_eq seq'[symmetric] by (simp add: stkenc_def)
  ultimately show ?thesis by blast
qed

subsubsection \<open>Parsing a block word back into productions (for the backward direction)\<close>

text \<open>Two lists of \<open>s\<close>-terminated, \<open>s\<close>-internal-free blocks with equal concatenation are equal.\<close>

lemma concat_block_align:
  "concat xss = concat yss \<Longrightarrow>
   (\<forall>xs\<in>set xss. \<exists>p. xs = p @ [s] \<and> s \<notin> set p) \<Longrightarrow>
   (\<forall>ys\<in>set yss. \<exists>p. ys = p @ [s] \<and> s \<notin> set p) \<Longrightarrow> xss = yss"
proof (induction xss arbitrary: yss)
  case Nil
  thus ?case by (cases yss) auto
next
  case (Cons xs xss')
  from Cons.prems(2) obtain p1 where xs: "xs = p1 @ [s]" and p1: "s \<notin> set p1" by auto
  show ?case
  proof (cases yss)
    case Nil
    with Cons.prems(1) xs show ?thesis by simp
  next
    case (Cons ys yss')
    from Cons.prems(3) \<open>yss = ys # yss'\<close> obtain p2 where ys: "ys = p2 @ [s]" and p2: "s \<notin> set p2"
      by auto
    from Cons.prems(1) xs ys \<open>yss = ys # yss'\<close>
    have "p1 @ s # concat xss' = p2 @ s # concat yss'" by simp
    from this p1 p2
    have "p1 = p2" and "concat xss' = concat yss'" by (auto simp add: append_Cons_eq_append_Cons)
    have "xss' = yss'"
      using Cons.IH[OF \<open>concat xss' = concat yss'\<close>] Cons.prems(2) Cons.prems(3) \<open>yss = ys # yss'\<close>
      by auto
    with \<open>p1 = p2\<close> xs ys \<open>yss = ys # yss'\<close> show ?thesis by simp
  qed
qed

text \<open>A \<open>c\<close>-free middle delimited by two \<open>c\<close>s inside a single-\<open>c\<close>-separated block body must be one
  of the fragments.\<close>

lemma cfrag_parse_gen:
  assumes "c \<notin> set y" and fc: "\<And>q. c \<notin> set (f q)"
  shows "x @ c # y @ c # z = concat (map (\<lambda>q. c # f q) qs) @ [c] \<Longrightarrow> y \<in> set (map f qs)"
proof (induction qs arbitrary: x z)
  case Nil thus ?case by (cases x) auto
next
  case (Cons q qs')
  have rhs: "concat (map (\<lambda>q. c # f q) (q # qs')) @ [c]
             = (c # f q) @ (concat (map (\<lambda>q. c # f q) qs') @ [c])" by simp
  let ?REST = "concat (map (\<lambda>q. c # f q) qs') @ [c]"
  have restCc: "?REST = c # tl ?REST" by (cases qs') auto
  from Cons.prems rhs have eq: "x @ c # y @ c # z = (c # f q) @ ?REST" by simp
  show ?case
  proof (cases x)
    case Nil
    with eq have "y @ c # z = f q @ c # tl ?REST" using restCc by simp
    from this assms(1) fc have "y = f q" by (simp add: append_Cons_eq_append_Cons)
    thus ?thesis by simp
  next
    case (Cons xa x')
    with eq obtain t where
      "x' = f q @ t \<and> t @ (c # y @ c # z) = ?REST \<or> x' @ t = f q \<and> c # y @ c # z = t @ ?REST"
      using append_eq_append_conv2[of x' "c # y @ c # z" "f q" ?REST] by auto
    thus ?thesis
    proof
      assume "x' = f q @ t \<and> t @ (c # y @ c # z) = ?REST"
      with Cons.IH show ?thesis by auto
    next
      assume "x' @ t = f q \<and> c # y @ c # z = t @ ?REST"
      hence fqt: "f q = x' @ t" and ceq: "c # y @ c # z = t @ ?REST" by auto
      have ct: "c \<notin> set t" using fqt fc[of q] by auto
      have "t = []" using ceq ct by (cases t) auto
      with ceq have "[] @ c # y @ c # z = ?REST" by simp
      from Cons.IH[OF this] show ?thesis by simp
    qed
  qed
qed

text \<open>Each block \<open>enc_h idx S P a\<close> ends in exactly one \<open>d\<close>.\<close>

lemma enc_h_Dd: "\<exists>p. enc_h idx S P a = p @ [Dd] \<and> Dd \<notin> set p"
using set_xihat unfolding enc_h_def Talph_def bracks_def by fastforce

text \<open>Inverting one block: if \<open>blk (x,y,z)\<close> equals an encoded block \<open>enc_h idx S P a\<close> and the middle
  \<open>y\<close> is free of \<open>c\<close> (which holds for every block of an \<open>L\<^sub>0\<close>-witness), then \<open>y\<close> is the \<open>\<xi>\<^bsup>^\<^esup>\<close>-code of
  some production of \<open>P\<close> whose right-hand side starts with \<open>a\<close>.\<close>

lemma block_parse:
  assumes eq: "blk (x,y,z) = enc_h idx S P a"
      and yset: "set y \<subseteq> insert Ce bracks"
  shows "\<exists>p. p \<in> set P \<and> (\<exists>Bs. snd p = Tm a # map Nt Bs) \<and> y = xihat idx S p"
proof -
  let ?qs = "filter (\<lambda>p. \<exists>Bs. snd p = Tm a # map Nt Bs) P"
  have eq': "x @ Cc # y @ Cc # z = concat (map (\<lambda>p. Cc # xihat idx S p) ?qs) @ [Cc]"
    using eq by (simp add: blk_def enc_h_def)
  have ccy: "Cc \<notin> set y" using yset by (auto simp: bracks_def)
  have ccf: "Cc \<notin> set (xihat idx S q)" for q
    using set_xihat[of idx S q] by (auto simp: bracks_def)
  from cfrag_parse_gen[OF ccy ccf eq']
  show ?thesis by fastforce
qed

text \<open>For a complete derivation read off from an \<open>L\<^sub>0\<close>-witness, the concatenation of the encoded
  middles is \<open>\<cent>\<close> followed by the push of \<open>S\<close> and the \<open>\<xi>\<close>-codes. This is justified directly from the
  \<open>\<cent>/D\<close>-conditions (the first production expands \<open>S\<close>, the later ones do not).\<close>

lemma concat_xihat_eq_fst:
  assumes ne: "ps \<noteq> []" and fp0: "fst (hd ps) = S" and tlS: "\<forall>p\<in>set (tl ps). fst p \<noteq> S"
  shows "concat (map (xihat idx S) ps) = Ce # pushcode (idx S) @ concat (map (xi idx) ps)"
using assms fp0 tlS by(auto simp: neq_Nil_conv xihat_def map_xihat_no_S)

text \<open>Inverting a whole block word: a list of blocks matching the letters of \<open>w\<close> (with \<open>c\<close>-free
  middles) yields a production list \<open>ps\<close> matching \<open>w\<close>, whose \<open>\<xi>\<^bsup>^\<^esup>\<close>-codes are the middles.\<close>

lemma blocks_to_ps:
  "list_all2 (\<lambda>b a. blk b = enc_h idx S P a) bs w \<Longrightarrow>
   (\<forall>(x,y,z)\<in>set bs. set y \<subseteq> insert Ce bracks) \<Longrightarrow>
   \<exists>ps. list_all2 (\<lambda>a p. p \<in> set P \<and> (\<exists>Bs. snd p = Tm a # map Nt Bs)) w ps
      \<and> map (\<lambda>(x,y,z). y) bs = map (xihat idx S) ps"
proof (induction bs w rule: list_all2_induct)
  case Nil
  show ?case by (intro exI[of _ "[]"]) auto
next
  case (Cons b bs' a w')
  obtain x y z where "b = (x,y,z)" by (cases b)
  with Cons block_parse show ?case by fastforce
qed


subsection \<open>Theorem 2.1\<close>

text \<open>We fix a grammar in Greibach \<^emph>\<open>standard form\<close>: every production is \<open>A \<rightarrow> a B\<^sub>1 \<dots> B\<^sub>m\<close> (a
  terminal followed by nonterminals) and the start symbol \<open>S\<close> occurs on no right-hand side. The
  nonterminals are indexed injectively by \<open>idx\<close> (only injectivity on \<open>insert S (Nts (set P))\<close> matters;
  the specific index values, in particular \<open>idx S\<close>, are immaterial).\<close>

locale greibach_std =
  fixes P :: "('n,'t) prods"
    and S :: "'n"
    and idx :: "'n \<Rightarrow> nat"
  assumes std: "\<And>A \<alpha>. (A,\<alpha>) \<in> set P \<Longrightarrow> \<exists>a Bs. \<alpha> = Tm a # map Nt Bs"
      and S_notin_rhs: "\<And>A a Bs. (A, Tm a # map Nt Bs) \<in> set P \<Longrightarrow> S \<notin> set Bs"
      and idx_inj: "inj_on idx (insert S (Nts (set P)))"
begin

text \<open>\<open>drives ps \<alpha> w \<beta>\<close>: applying the production list \<open>ps\<close> as successive \<^emph>\<open>leftmost\<close> steps to the
  nonterminal stack \<open>\<alpha>\<close> (top first) emits the terminal word \<open>w\<close> and reaches stack \<open>\<beta>\<close>. Each step
  expands the stack top by a standard-form production from \<open>P\<close>.\<close>

inductive drives :: "('n,'t) prod list \<Rightarrow> 'n list \<Rightarrow> 't list \<Rightarrow> 'n list \<Rightarrow> bool" where
  drives_Nil: "drives [] \<alpha> [] \<alpha>"
| drives_Cons: "(A, Tm a # map Nt Bs) \<in> set P \<Longrightarrow> drives ps (Bs @ \<alpha>) w \<beta> \<Longrightarrow>
                drives ((A, Tm a # map Nt Bs) # ps) (A # \<alpha>) (a # w) \<beta>"

text \<open>\<^bold>\<open>Central invariant.\<close> Running the encoded \<open>\<xi>\<close>-brackets of \<open>ps\<close> through @{const bal_stk},
  starting from the encoded stack \<open>\<alpha>\<close>, ends at the encoded stack \<open>\<beta>\<close>. Each leftmost step is one
  application of @{thm [source] bal_stk_xi}: pop the top nonterminal, push the production's
  right-hand-side nonterminals.\<close>

lemma drives_bal_stk:
  "drives ps \<alpha> w \<beta> \<Longrightarrow>
   bal_stk (stkenc (map idx \<alpha>)) (brks (concat (map (xi idx) ps))) = (stkenc (map idx \<beta>), [])"
proof (induction rule: drives.induct)
  case (drives_Nil \<alpha>)
  show ?case by simp
next
  case (drives_Cons A a Bs ps \<alpha> w \<beta>)
  let ?p = "(A, Tm a # map Nt Bs)"
  show ?case using drives_Cons bal_stk_xi[of ?p a Bs idx "stkenc (map idx \<alpha>)"]
    by (simp add: stkenc_def  bal_stk_append step)
qed

text \<open>For a complete leftmost derivation (the stack \<open>[S]\<close> is emptied), the bracket word after the
  leading \<open>\<cent>\<close> (namely \<open>pushcode (idx S)\<close> followed by the \<open>\<xi>\<close>-codes) is balanced, i.e.\ in \<open>D\<close>.\<close>

lemma drives_bal_complete:
  assumes "drives ps [S] w []"
  shows "bal (brks (pushcode (idx S) @ concat (map (xi idx) ps)))"
using drives_bal_stk[OF assms]
by (simp add: bal_stk_append bal_stk_pushcode stkenc_def bal_iff_bal_stk)


subsubsection \<open>Bridge between @{const drives} and the grammar language @{const Lang}\<close>

text \<open>Easy direction: a @{const drives} sequence is a leftmost derivation.\<close>

lemma drives_imp_derivels:
  "drives ps \<alpha> w \<beta> \<Longrightarrow> set P \<turnstile> map Nt \<alpha> \<Rightarrow>l* map Tm w @ map Nt \<beta>"
proof (induction rule: drives.induct)
  case (drives_Nil \<alpha>)
  show ?case by simp
next
  case (drives_Cons A a Bs ps \<alpha> w \<beta>)
  have step: "set P \<turnstile> Nt A # map Nt \<alpha> \<Rightarrow>l Tm a # map Nt (Bs @ \<alpha>)"
    using derivel.intros[OF drives_Cons.hyps(1), of "[]" "map Nt \<alpha>"] by simp
  have "set P \<turnstile> Tm a # map Nt (Bs @ \<alpha>) \<Rightarrow>l* Tm a # (map Tm w @ map Nt \<beta>)"
    using drives_Cons.IH by (simp add: derivels_Tm_Cons)
  with step have "set P \<turnstile> Nt A # map Nt \<alpha> \<Rightarrow>l* Tm a # (map Tm w @ map Nt \<beta>)"
    by (rule converse_rtranclp_into_rtranclp)
  thus ?case by simp
qed

text \<open>Hard direction: a leftmost derivation to a terminal word yields a @{const drives} sequence.
  Induction on the number of leftmost steps. (We suppress @{thm [source] relpowp.simps(2)} so that
  the leftmost-step lemmas for \<open>\<Rightarrow>l(Suc n)\<close> fire before the relation power is unfolded.)\<close>

lemma deriveln_imp_drives:
  "set P \<turnstile> map Nt \<alpha> \<Rightarrow>l(n) map Tm w \<Longrightarrow> \<exists>ps. drives ps \<alpha> w []"
proof (induction n arbitrary: \<alpha> w)
  case 0
  hence "map Nt \<alpha> = map Tm w" by simp
  hence "\<alpha> = [] \<and> w = []" by (cases \<alpha>; cases w; auto)
  thus ?case using drives_Nil by auto
next
  case (Suc n)
  show ?case
  proof (cases \<alpha>)
    case Nil
    with Suc.prems have "set P \<turnstile> [] \<Rightarrow>l(Suc n) map Tm w" by simp
    hence False by (simp del: relpowp.simps(2))
    thus ?thesis ..
  next
    case (Cons A \<alpha>')
    with Suc.prems have "set P \<turnstile> Nt A # map Nt \<alpha>' \<Rightarrow>l(Suc n) map Tm w" by simp
    then obtain \<gamma> where \<gamma>: "(A, \<gamma>) \<in> set P" and der: "set P \<turnstile> \<gamma> @ map Nt \<alpha>' \<Rightarrow>l(n) map Tm w"
      by (auto simp: deriveln_Nt_Cons simp del: relpowp.simps(2))
    from std[OF \<gamma>] obtain a Bs where \<gamma>eq: "\<gamma> = Tm a # map Nt Bs" by blast
    from der \<gamma>eq have "set P \<turnstile> Tm a # map Nt (Bs @ \<alpha>') \<Rightarrow>l(n) map Tm w" by simp
    then obtain w' where weq: "map Tm w = Tm a # w'" and der': "set P \<turnstile> map Nt (Bs @ \<alpha>') \<Rightarrow>l(n) w'"
      by (auto simp: deriveln_Tm_Cons simp del: relpowp.simps(2))
    from weq obtain w'' where w_eq: "w = a # w''" and w'_eq: "w' = map Tm w''"
      by (cases w) auto
    from der' w'_eq have der'': "set P \<turnstile> map Nt (Bs @ \<alpha>') \<Rightarrow>l(n) map Tm w''" by simp
    from Suc.IH[OF der''] obtain ps where ps: "drives ps (Bs @ \<alpha>') w'' []" by blast
    have "drives ((A, Tm a # map Nt Bs) # ps) (A # \<alpha>') (a # w'') []"
      using \<gamma> \<gamma>eq ps by (auto intro: drives_Cons)
    thus ?thesis using Cons w_eq by auto
  qed
qed

text \<open>Combining both directions with the leftmost/standard derivation equivalence
  @{thm [source] derivels_iff_derives}: membership in the grammar's language is exactly the
  existence of a @{const drives} sequence from \<open>[S]\<close> to the empty stack.\<close>

lemma drives_iff_Lang:
  "(\<exists>ps. drives ps [S] w []) \<longleftrightarrow> w \<in> Lang (set P) S"
proof
  assume "\<exists>ps. drives ps [S] w []"
  with drives_imp_derivels
  show "w \<in> Lang (set P) S" unfolding Lang_def
    using derivels_iff_derives by fastforce
next
  assume "w \<in> Lang (set P) S"
  hence "set P \<turnstile> [Nt S] \<Rightarrow>l* map Tm w" by (simp add: Lang_def derivels_iff_derives)
  thus "\<exists>ps. drives ps [S] w []"
    using deriveln_imp_drives rtranclp_power by fastforce
qed

subsubsection \<open>Block structure of the encoded word\<close>

text \<open>Once \<open>S\<close> has left the stack it never returns (it is on no right-hand side), so no later
  production expands \<open>S\<close>.\<close>

lemma drives_no_S:
  "drives ps \<alpha> w \<beta> \<Longrightarrow> S \<notin> set \<alpha> \<Longrightarrow> (\<forall>p \<in> set ps. fst p \<noteq> S)"
proof (induction rule: drives.induct)
  case (drives_Nil \<alpha>) show ?case by simp
next
  case (drives_Cons A a Bs ps \<alpha> w \<beta>)
  show ?case using S_notin_rhs drives_Cons by auto
qed

text \<open>The concatenation of the encoded middles of a complete derivation: only the first production
  (which expands \<open>S\<close>) contributes the \<open>\<cent>\<close> marker and the initial push of \<open>S\<close>; all later productions
  contribute pure \<open>\<xi>\<close>-codes.\<close>

lemma concat_xihat_eq:
  assumes "drives ps [S] w []"
  shows "concat (map (xihat idx S) ps) = Ce # pushcode (idx S) @ concat (map (xi idx) ps)"
proof -
  from assms obtain a Bs ps' w' where
      ps_eq: "ps = (S, Tm a # map Nt Bs) # ps'"
      and mem: "(S, Tm a # map Nt Bs) \<in> set P"
      and rest: "drives ps' Bs w' []"
    by (auto elim: drives.cases)
  have "S \<notin> set Bs" using S_notin_rhs[OF mem] by simp
  with drives_no_S[OF rest] have "\<forall>p \<in> set (tl ps). fst p \<noteq> S" by (simp add: ps_eq)
  from concat_xihat_eq_fst[OF _ _ this] show ?thesis by (simp add: ps_eq)
qed

subsubsection \<open>Forward direction of Theorem 2.1\<close>

text \<open>The terminal letters of \<open>w\<close> are matched, in order, by the productions of any \<open>drives\<close>
  sequence producing \<open>w\<close>.\<close>

lemma drives_list_all2:
  "drives ps \<alpha> w \<beta> \<Longrightarrow> list_all2 (\<lambda>b p. p \<in> set P \<and> (\<exists>Bs. snd p = Tm b # map Nt Bs)) w ps"
by (induction rule: drives.induct) auto

text \<open>If \<open>w \<in> L(G)\<close> (witnessed by a complete \<open>drives\<close> sequence) then the encoded word \<open>h(w)\<close> lies in
  \<open>L\<^sub>0\<close>: the blocks select the \<open>\<xi>\<^bsup>^\<^esup>\<close>-codes, whose concatenation is \<open>\<cent>\<close> followed by a balanced
  (\<open>\<in> D\<close>) word.\<close>

lemma forward:
  assumes drv: "drives ps [S] w []"
  shows "concat (map (enc_h idx S P) w) \<in> L0"
proof -
  from drv obtain a Bs ps' w' where
      ps_eq: "ps = (S, Tm a # map Nt Bs) # ps'"
      and mem: "(S, Tm a # map Nt Bs) \<in> set P"
      and rest: "drives ps' Bs w' []"
    by (auto elim: drives.cases)
  have SnotBs: "S \<notin> set Bs" using S_notin_rhs[OF mem] by simp
  have noS: "\<forall>p \<in> set ps'. fst p \<noteq> S" using drives_no_S[OF rest] SnotBs by simp
  from block_decomp[OF drives_list_all2[OF drv]] obtain bs where
      bw: "concat (map (enc_h idx S P) w) = concat (map blk bs)" and
      by_eq: "map (\<lambda>(x,y,z). y) bs = map (xihat idx S) ps" and
      bT: "\<forall>(x,y,z) \<in> set bs. set x \<subseteq> Talph \<and> set z \<subseteq> Talph" by blast
  have bs_ne: "bs \<noteq> []" using by_eq ps_eq by (cases bs) auto
  let ?v = "pushcode (idx S) @ concat (map (xi idx) ps)"
  have ys: "concat (map (\<lambda>(x,y,z). y) bs) = Ce # ?v"
    using by_eq concat_xihat_eq[OF drv] by simp
  have vD: "?v \<in> D"
  proof -
    have "bal (brks ?v)" by (rule drives_bal_complete[OF drv])
    moreover have "set ?v \<subseteq> bracks"
      unfolding set_append using Un_least[OF set_pushcode] set_xi by fastforce
    ultimately show ?thesis by (simp add: D_def)
  qed
  have tl_y: "map (\<lambda>(x,y,z). y) (tl bs) = map (xihat idx S) ps'"
  proof -
    have "map (\<lambda>(x,y,z). y) bs = map (xihat idx S) ((S, Tm a # map Nt Bs) # ps')"
      using by_eq ps_eq by simp
    thus ?thesis by (cases bs) auto
  qed
  have key: "set y \<subseteq> bracks" if "(x,y,z) \<in> set (tl bs)" for x y z
  proof -
    from that have "y \<in> set (map (\<lambda>(x,y,z). y) (tl bs))" by force
    then obtain p where p: "p \<in> set ps'" and yp: "y = xihat idx S p" using tl_y by auto
    have "fst p \<noteq> S" using p noS by simp
    hence "y = xi idx p" using yp by (simp add: xihat_def)
    thus ?thesis using set_xi by simp
  qed
  have tl_bracks: "\<forall>(x,y,z) \<in> set (tl bs). set y \<subseteq> bracks" using key by fast
  have exv: "\<exists>v\<in>D. concat (map (\<lambda>(x,y,z). y) bs) = Ce # v" using ys vD by blast
  have "concat (map blk bs) \<in> L0"
    unfolding L0_def using bs_ne bT tl_bracks exv by (auto intro!: exI[of _ bs])
  thus ?thesis using bw by simp
qed

subsubsection \<open>Backward direction of Theorem 2.1\<close>

text \<open>\<^bold>\<open>Converse of the central invariant.\<close> If the encoded \<open>\<xi>\<close>-brackets of a production list \<open>ps\<close>
  (whose productions are standard-form and match the letters of \<open>w\<close>) run successfully on the encoded
  stack \<open>\<alpha>\<close> (consuming everything, ending empty), then \<open>ps\<close> really is a leftmost derivation
  \<open>drives ps \<alpha> w []\<close>. Each step is inverted by @{thm [source] bal_stk_xi_inv}, which (using
  injectivity of \<open>idx\<close>) forces the production's left-hand side to be the current stack top.\<close>

lemma drives_bal_stk_inv:
  "list_all2 (\<lambda>b p. p \<in> set P \<and> (\<exists>Bs. snd p = Tm b # map Nt Bs)) w ps \<Longrightarrow>
   set \<alpha> \<subseteq> insert S (Nts (set P)) \<Longrightarrow>
   bal_stk (stkenc (map idx \<alpha>)) (brks (concat (map (xi idx) ps))) = ([], []) \<Longrightarrow>
   drives ps \<alpha> w []"
proof (induction w ps arbitrary: \<alpha> rule: list_all2_induct)
  case (Nil \<alpha>)
  from Nil.prems(2) have "stkenc (map idx \<alpha>) = []" by simp
  hence "\<alpha> = []" using stkenc_eq_Nil by auto
  thus ?case by (simp add: drives.drives_Nil)
next
  case (Cons b w' p ps' \<alpha>)
  from Cons.hyps(1) obtain Bs where pin: "p \<in> set P" and snd_p: "snd p = Tm b # map Nt Bs" by blast
  have fpN: "fst p \<in> insert S (Nts (set P))" using pin by (force simp: Nts_Lhss_Rhs_Nts Lhss_def)
  have BsN: "set Bs \<subseteq> insert S (Nts (set P))"
  proof -
    have "(fst p, Tm b # map Nt Bs) = p" using snd_p by (cases p) auto
    with pin have "(fst p, Tm b # map Nt Bs) \<in> set P" by simp
    hence "Nts_syms (Tm b # map Nt Bs) \<subseteq> Rhs_Nts (set P)" by (auto simp: Rhs_Nts_def)
    moreover have "set Bs \<subseteq> Nts_syms (Tm b # map Nt Bs)" by (auto simp: Nts_syms_def)
    ultimately have "set Bs \<subseteq> Rhs_Nts (set P)" by blast
    also have "Rhs_Nts (set P) \<subseteq> insert S (Nts (set P))" by (auto simp: Nts_Lhss_Rhs_Nts)
    finally show ?thesis .
  qed
  from Cons.prems(1) have \<alpha>N: "set \<alpha> \<subseteq> insert S (Nts (set P))" .
  from Cons.prems(2) have "bal_stk (stkenc (map idx \<alpha>))
          (brks (xi idx p) @ brks (concat (map (xi idx) ps'))) = ([], [])" by simp
  then obtain s' where
    step: "bal_stk (stkenc (map idx \<alpha>)) (brks (xi idx p)) = (s', [])" and
    rest: "bal_stk s' (brks (concat (map (xi idx) ps'))) = ([], [])"
    by (rule bal_stk_append_split)
  from bal_stk_xi_inv[OF idx_inj snd_p fpN \<alpha>N step] obtain \<alpha>' where
    \<alpha>eq: "\<alpha> = fst p # \<alpha>'" and s'eq: "s' = stkenc (map idx (Bs @ \<alpha>'))" by blast
  from \<alpha>eq \<alpha>N have "set \<alpha>' \<subseteq> insert S (Nts (set P))" by auto
  with BsN have Bs\<alpha>N: "set (Bs @ \<alpha>') \<subseteq> insert S (Nts (set P))" by auto
  from rest s'eq have
    "bal_stk (stkenc (map idx (Bs @ \<alpha>'))) (brks (concat (map (xi idx) ps'))) = ([], [])" by simp
  from Cons.IH[OF Bs\<alpha>N this] have driv': "drives ps' (Bs @ \<alpha>') w' []" .
  have peq: "p = (fst p, Tm b # map Nt Bs)" using snd_p by (cases p) auto
  with pin have memP: "(fst p, Tm b # map Nt Bs) \<in> set P" by simp
  from drives_Cons[OF memP driv']
  have "drives ((fst p, Tm b # map Nt Bs) # ps') (fst p # \<alpha>') (b # w') []" .
  thus ?case using \<alpha>eq peq by simp
qed

text \<open>\<^bold>\<open>Backward direction.\<close> If the encoded word \<open>h(w)\<close> is a non-empty member of \<open>L\<^sub>0\<close>, parse its
  block structure back into a production list and run the converse central invariant to obtain a
  \<open>drives\<close> sequence (hence \<open>w \<in> L(G)\<close>). Block alignment uses that both \<open>blk\<close>- and \<open>enc_h\<close>-blocks end
  in exactly one \<open>d\<close>; each middle is \<open>c\<close>-free, so equals a \<open>\<xi>\<^bsup>^\<^esup>\<close>-code (@{thm [source] block_parse});
  the \<open>\<cent>/D\<close>-condition gives the balanced run feeding @{thm [source] drives_bal_stk_inv}.\<close>

lemma backward_drives:
  assumes inL0: "concat (map (enc_h idx S P) w) \<in> L0"
      and ne: "concat (map (enc_h idx S P) w) \<noteq> []"
  shows "\<exists>ps. drives ps [S] w []"
proof -
  from inL0 ne have "\<exists>bs. concat (map (enc_h idx S P) w) = concat (map blk bs) \<and> bs \<noteq> [] \<and>
       (\<forall>(x,y,z)\<in>set bs. set x \<subseteq> Talph \<and> set z \<subseteq> Talph) \<and>
       (\<forall>(x,y,z)\<in>set (tl bs). set y \<subseteq> bracks) \<and>
       (\<exists>v\<in>D. concat (map (\<lambda>(x,y,z). y) bs) = Ce # v)"
    by (auto simp: L0_def)
  then obtain bs where
    cc: "concat (map (enc_h idx S P) w) = concat (map blk bs)" and
    bs_ne0: "bs \<noteq> []" and
    xzT: "\<forall>(x,y,z)\<in>set bs. set x \<subseteq> Talph \<and> set z \<subseteq> Talph" and
    tlb: "\<forall>(x,y,z)\<in>set (tl bs). set y \<subseteq> bracks" and
    cD: "\<exists>v\<in>D. concat (map (\<lambda>(x,y,z). y) bs) = Ce # v"
    by blast
  from cD obtain v where vD: "v \<in> D" and yv: "concat (map (\<lambda>(x,y,z). y) bs) = Ce # v" by blast

  \<comment> \<open>Every middle is \<open>c\<close>-free (it is part of the \<open>\<cent>/D\<close>-word).\<close>
  have ysub_one: "set y \<subseteq> insert Ce bracks" if "(x,y,z) \<in> set bs" for x y z
  proof -
    from that have "y \<in> set (map (\<lambda>(x,y,z). y) bs)" by force
    hence "set y \<subseteq> set (concat (map (\<lambda>(x,y,z). y) bs))" by auto
    also have "\<dots> = insert Ce (set v)" using yv by simp
    also have "\<dots> \<subseteq> insert Ce bracks" using vD by (auto simp: D_def)
    finally show ?thesis .
  qed
  have ysub: "\<forall>(x,y,z)\<in>set bs. set y \<subseteq> insert Ce bracks" using ysub_one by fast

  \<comment> \<open>Each \<open>blk\<close>-block ends in exactly one \<open>d\<close>, just like each \<open>enc_h\<close>-block.\<close>
  have blkDd: "\<exists>p. b = p @ [Dd] \<and> Dd \<notin> set p" if "b \<in> set (map blk bs)" for b
  proof -
    from that obtain t where tin: "t \<in> set bs" and bt: "b = blk t" by auto
    obtain x y z where t: "t = (x,y,z)" by (cases t)
    have "Dd \<notin> set (x @ Cc # y @ Cc # z)"
      using ysub tin t xzT by (auto simp: Talph_def bracks_def)
    moreover have "b = (x @ Cc # y @ Cc # z) @ [Dd]" using bt t by (simp add: blk_def)
    ultimately show ?thesis by blast
  qed
  have align: "map blk bs = map (enc_h idx S P) w"
  proof (rule concat_block_align)
    show "concat (map blk bs) = concat (map (enc_h idx S P) w)" using cc by simp
    show "\<forall>xs\<in>set (map blk bs). \<exists>p. xs = p @ [Dd] \<and> Dd \<notin> set p" using blkDd by blast
    show "\<forall>ys\<in>set (map (enc_h idx S P) w). \<exists>p. ys = p @ [Dd] \<and> Dd \<notin> set p"
      using enc_h_Dd by auto
  qed

  \<comment> \<open>Recover a matching production list \<open>ps\<close> whose \<open>\<xi>\<^bsup>^\<^esup>\<close>-codes are the middles.\<close>
  have len: "length bs = length w" using align by (metis length_map)
  have la2blk: "list_all2 (\<lambda>b a. blk b = enc_h idx S P a) bs w"
  proof (rule list_all2_all_nthI[OF len])
    fix n assume "n < length bs"
    thus "blk (bs ! n) = enc_h idx S P (w ! n)" using align len by (metis nth_map)
  qed
  from blocks_to_ps[OF la2blk ysub] obtain ps where
    la2match: "list_all2 (\<lambda>a p. p \<in> set P \<and> (\<exists>Bs. snd p = Tm a # map Nt Bs)) w ps" and
    yps: "map (\<lambda>(x,y,z). y) bs = map (xihat idx S) ps" by blast

  have xihatps: "concat (map (xihat idx S) ps) = Ce # v"
  proof -
    have "concat (map (xihat idx S) ps) = concat (map (\<lambda>(x,y,z). y) bs)" using yps by simp
    thus ?thesis using yv by simp
  qed

  \<comment> \<open>\<open>w\<close> (hence \<open>ps\<close>) is non-empty.\<close>
  have w_ne: "w \<noteq> []" using ne by auto
  have ps_ne: "ps \<noteq> []" using la2match w_ne by (cases w; cases ps) auto
  obtain p0 ps' where psc: "ps = p0 # ps'" using ps_ne by (cases ps) auto

  \<comment> \<open>The first production expands \<open>S\<close> (its code begins with \<open>\<cent>\<close>).\<close>
  have fp0: "fst p0 = S"
  proof (rule ccontr)
    assume ne0: "fst p0 \<noteq> S"
    have h: "hd (xihat idx S p0) = Aa (Close A1)" using ne0 by (simp add: xihat_def xi_def popcode_def)
    have nemp: "xihat idx S p0 \<noteq> []" using ne0 by (simp add: xihat_def xi_def popcode_def)
    have "concat (map (xihat idx S) ps) = xihat idx S p0 @ concat (map (xihat idx S) ps')"
      using psc by simp
    hence "hd (concat (map (xihat idx S) ps)) = Aa (Close A1)" using h nemp by (simp add: hd_append)
    with xihatps show False by simp
  qed
  have hdps: "fst (hd ps) = S" using fp0 psc by simp

  \<comment> \<open>No later production expands \<open>S\<close> (their middles are bracket-only).\<close>
  have tlmap: "map (\<lambda>(x,y,z). y) (tl bs) = map (xihat idx S) ps'"
    by (simp add: map_tl psc yps)
  have tlS: "fst p \<noteq> S" if asm: "p\<in>set ps'" for p
  proof -
    from asm have "xihat idx S p \<in> set (map (xihat idx S) ps')" by simp
    also have "set (map (xihat idx S) ps') = set (map (\<lambda>(x,y,z). y) (tl bs))"
      using tlmap by simp
    finally have "xihat idx S p \<in> set (map (\<lambda>(x,y,z). y) (tl bs))" .
    then obtain x y z where bin: "(x,y,z) \<in> set (tl bs)" and yeq: "xihat idx S p = y" by auto
    have "set y \<subseteq> bracks" using tlb bin by auto
    hence "Ce \<notin> set (xihat idx S p)" using yeq by (auto simp: bracks_def)
    thus "fst p \<noteq> S" by (auto simp: xihat_def)
  qed
  have tlps: "\<forall>p\<in>set (tl ps). fst p \<noteq> S" using tlS psc by simp

  \<comment> \<open>Assemble the balanced run and invoke the converse central invariant.\<close>
  have "Ce # v = Ce # pushcode (idx S) @ concat (map (xi idx) ps)"
    using xihatps concat_xihat_eq_fst[OF ps_ne hdps tlps] by simp
  hence v_eq: "v = pushcode (idx S) @ concat (map (xi idx) ps)" by simp
  have "bal_stk [] (brks v) = ([], [])"
    using vD by (simp add: D_def bal_iff_bal_stk)
  hence "bal_stk [] (brks (pushcode (idx S)) @ brks (concat (map (xi idx) ps))) = ([], [])"
    by (simp add: v_eq)
  hence "bal_stk (frag (idx S)) (brks (concat (map (xi idx) ps))) = ([], [])"
    by (simp add: bal_stk_append bal_stk_pushcode)
  hence run: "bal_stk (stkenc (map idx [S])) (brks (concat (map (xi idx) ps))) = ([], [])"
    by (simp add: stkenc_def)
  have "set [S] \<subseteq> insert S (Nts (set P))" by simp
  from drives_bal_stk_inv[OF la2match this run] show ?thesis ..
qed

subsubsection \<open>The core of Theorem 2.1\<close>

text \<open>For a Greibach-standard-form grammar, the language minus the empty word is exactly the inverse
  image under the encoding homomorphism @{const enc_h} of \<open>L\<^sub>0 - {\<epsilon>}\<close>.\<close>

lemma core: "Lang (set P) S - {[]} = inv_hom (enc_h idx S P) (L0 - {[]})"
proof (rule set_eqI)
  fix w
  show "(w \<in> Lang (set P) S - {[]}) = (w \<in> inv_hom (enc_h idx S P) (L0 - {[]}))"
  proof
    assume "w \<in> Lang (set P) S - {[]}"
    hence wL: "w \<in> Lang (set P) S" and wne: "w \<noteq> []" by auto
    from wL obtain ps where "drives ps [S] w []" using drives_iff_Lang by blast
    hence inL0: "concat (map (enc_h idx S P) w) \<in> L0" by (rule forward)
    have "concat (map (enc_h idx S P) w) \<noteq> []"
    proof -
      from wne obtain a w' where wc: "w = a # w'" by (cases w) auto
      obtain p where ep: "enc_h idx S P a = p @ [Dd]" using enc_h_Dd[of idx S P a] by blast
      show ?thesis by (simp add: wc ep)
    qed
    with inL0 show "w \<in> inv_hom (enc_h idx S P) (L0 - {[]})" by (simp add: inv_hom_def)
  next
    assume "w \<in> inv_hom (enc_h idx S P) (L0 - {[]})"
    hence inL0: "concat (map (enc_h idx S P) w) \<in> L0"
      and ne: "concat (map (enc_h idx S P) w) \<noteq> []" by (auto simp: inv_hom_def)
    from backward_drives[OF inL0 ne] obtain ps where "drives ps [S] w []" by blast
    hence "w \<in> Lang (set P) S" using drives_iff_Lang by blast
    moreover have "w \<noteq> []" using ne by auto
    ultimately show "w \<in> Lang (set P) S - {[]}" by simp
  qed
qed

end

text \<open>The locale-free form of @{thm [source] greibach_std.core}: for \<^emph>\<open>any\<close> production list \<open>P\<close> in
  Greibach standard form (every right-hand side a terminal followed by nonterminals, the start symbol
  \<open>S\<close> on no right-hand side) together with an injective index \<open>idx\<close>, the language
  with the empty word removed is exactly the inverse image of \<open>L\<^sub>0 - {\<epsilon>}\<close> under the concrete encoding
  homomorphism @{term "enc_h idx S P"}. This is the full content of Greibach's construction; the
  general \<open>Greibach_2_1\<close> below would follow by reducing an arbitrary grammar to this form.\<close>

theorem Greibach_2_1_std:
  fixes P :: "('n,'t) prods" and S :: 'n and idx :: "'n \<Rightarrow> nat"
  assumes "\<And>A \<alpha>. (A, \<alpha>) \<in> set P \<Longrightarrow> \<exists>a Bs. \<alpha> = Tm a # map Nt Bs"
      and "\<And>A a Bs. (A, Tm a # map Nt Bs) \<in> set P \<Longrightarrow> S \<notin> set Bs"
      and "inj_on idx (insert S (Nts (set P)))"
  shows "Lang (set P) S - {[]} = inv_hom (enc_h idx S P) (L0 - {[]})"
proof -
  interpret greibach_std P S idx using assms by unfold_locales
  show ?thesis by (rule core)
qed


subsubsection \<open>Reduction of an arbitrary grammar to the standard form\<close>

text \<open>Adding a fresh start symbol \<open>A'\<close> (not occurring in \<open>R\<close>) that copies all productions of \<open>A\<close>
  preserves the language and makes \<open>A'\<close> occur on no right-hand side. This is the standard
  ``new start symbol'' trick, needed to meet the @{locale greibach_std} side condition \<open>S_notin_rhs\<close>.\<close>

lemma Lang_fresh_start:
  assumes "A' \<notin> Nts R"
  shows "Lang (R \<union> {(A', \<gamma>) |\<gamma>. (A, \<gamma>) \<in> R}) A' = Lang R A"
proof -
  let ?N = "{(A', \<gamma>) |\<gamma>. (A, \<gamma>) \<in> R}"
  have notinL: "A' \<notin> Lhss R" and notinR: "A' \<notin> Rhs_Nts R"
    using assms by (auto simp: Nts_Lhss_Rhs_Nts)
  have lhssN: "Lhss ?N \<subseteq> {A'}" by (auto simp: Lhss_def)
  have disj: "Rhs_Nts R \<inter> Lhss ?N = {}" using lhssN notinR by auto
  have rhs_sub: "A' \<notin> Nts_syms \<gamma>" if "(A, \<gamma>) \<in> R" for \<gamma>
    using notinR that by (auto simp: Rhs_Nts_def)
  show ?thesis
  proof
    show "Lang (R \<union> ?N) A' \<subseteq> Lang R A"
    proof
      fix w assume "w \<in> Lang (R \<union> ?N) A'"
      then have der: "R \<union> ?N \<turnstile> [Nt A'] \<Rightarrow>* map Tm w" by (simp add: Lang_def)
      from derives_Nt_map_TmD[OF der] obtain \<gamma>
        where \<gamma>R: "(A', \<gamma>) \<in> R \<union> ?N" and d: "R \<union> ?N \<turnstile> \<gamma> \<Rightarrow>* map Tm w" by blast
      from \<gamma>R notinL have "(A', \<gamma>) \<in> ?N" by (auto simp: Lhss_def)
      then have A\<gamma>R: "(A, \<gamma>) \<in> R" by auto
      hence "A' \<notin> Nts_syms \<gamma>" by (rule rhs_sub)
      with lhssN have "Nts_syms \<gamma> \<inter> Lhss ?N = {}" by auto
      from derives_disj_Un_iff[OF disj this] d have dR: "R \<turnstile> \<gamma> \<Rightarrow>* map Tm w" by simp
      have "R \<turnstile> [Nt A] \<Rightarrow> \<gamma>" using A\<gamma>R by (simp add: derive_singleton)
      from this dR have "R \<turnstile> [Nt A] \<Rightarrow>* map Tm w" by (rule converse_rtranclp_into_rtranclp)
      then show "w \<in> Lang R A" by (simp add: Lang_def)
    qed
  next
    show "Lang R A \<subseteq> Lang (R \<union> ?N) A'"
    proof
      fix w assume "w \<in> Lang R A"
      then have der: "R \<turnstile> [Nt A] \<Rightarrow>* map Tm w" by (simp add: Lang_def)
      from derives_Nt_map_TmD[OF der] obtain \<gamma>
        where A\<gamma>R: "(A, \<gamma>) \<in> R" and d: "R \<turnstile> \<gamma> \<Rightarrow>* map Tm w" by blast
      from A\<gamma>R have "(A', \<gamma>) \<in> R \<union> ?N" by auto
      then have "R \<union> ?N \<turnstile> [Nt A'] \<Rightarrow> \<gamma>" by (simp add: derive_singleton)
      moreover from d have "R \<union> ?N \<turnstile> \<gamma> \<Rightarrow>* map Tm w" by (meson Un_upper1 derives_mono)
      ultimately have "R \<union> ?N \<turnstile> [Nt A'] \<Rightarrow>* map Tm w" by (rule converse_rtranclp_into_rtranclp)
      then show "w \<in> Lang (R \<union> ?N) A'" by (simp add: Lang_def)
    qed
  qed
qed


text \<open>A nonterminal with no productions generates the empty language; and a non-empty member of
  \<open>L\<^sub>0\<close> always contains the separator \<open>d\<close>. Both are needed to handle the degenerate case where the
  start symbol does not occur in the grammar.\<close>

lemma L0_Dd: "x \<in> L0 \<Longrightarrow> x \<noteq> [] \<Longrightarrow> Dd \<in> set x"
proof -
  assume "x \<in> L0" "x \<noteq> []"
  then obtain bs where x: "x = concat (map blk bs)" and ne: "bs \<noteq> []" by (auto simp: L0_def)
  from ne obtain b bs' where bbs: "bs = b # bs'" by (cases bs) auto
  obtain x1 y1 z1 where "b = (x1, y1, z1)" by (cases b)
  hence "Dd \<in> set (blk b)" by (simp add: blk_def)
  with x bbs show "Dd \<in> set x" by simp
qed

lemma inv_hom_Cc_empty: "inv_hom (\<lambda>_. [Cc]) (L0 - {[]}) = {}"
proof -
  have "concat (map (\<lambda>_. [Cc]) w) \<notin> L0 - {[]}" for w :: "'a list"
  proof
    assume "concat (map (\<lambda>_. [Cc]) w) \<in> L0 - {[]}"
    hence A: "concat (map (\<lambda>_. [Cc]) w) \<in> L0" and B: "concat (map (\<lambda>_. [Cc]) w) \<noteq> []" by auto
    from L0_Dd[OF A B] have "Dd \<in> set (concat (map (\<lambda>_. [Cc]) w))" .
    moreover have "set (concat (map (\<lambda>_. [Cc]) w)) \<subseteq> {Cc}" by auto
    ultimately show False by auto
  qed
  thus ?thesis by (auto simp: inv_hom_def)
qed

subsubsection \<open>Theorem 2.1 for grammars with a fresh-symbol supply\<close>

text \<open>The construction proper, for a nonterminal type with a fresh-symbol supply (sort \<open>fresh0\<close>, as
  required by @{const gnf_of}): the language minus \<open>\<epsilon>\<close> is the inverse homomorphic image of the one
  fixed hardest language \<open>L\<^sub>0 - {\<epsilon>}\<close>. The grammar is put into Greibach standard form by @{const gnf_of}
  together with a fresh start symbol; the (finitely many) nonterminals of the resulting grammar are
  then indexed injectively into @{typ nat} by @{thm [source] finite_imp_inj_to_nat_seg} — that
  injection is exactly the index \<open>idx\<close> the encoding @{const enc_h} requires (no countability needed).
  The general \<open>Greibach_2_1\<close> below lifts this to an arbitrary nonterminal type by renaming.\<close>

theorem Greibach_2_1_fresh0:
  fixes P :: "('n::fresh0,'t) Prods"
  assumes finP: "finite P"
  shows "\<exists>h::'t \<Rightarrow> t0 list. Lang P S - {[]} = inv_hom h (L0 - {[]})"
proof (cases "S \<in> Nts P")
  case False
  hence "S \<notin> Lhss P" by (simp add: Nts_Lhss_Rhs_Nts)
  hence "Lang P S = {}" by (rule Lang_empty_if_notin_Lhss)
  hence "Lang P S - {[]} = inv_hom (\<lambda>_. [Cc]) (L0 - {[]})" by (simp add: inv_hom_Cc_empty)
  thus ?thesis by blast
next
  case True
  obtain ps where psP: "set ps = P" using finP finite_list by blast
  have Snts: "S \<in> set (nts ps)" using True psP by (simp add: set_nts)
  define Pg where "Pg = set (gnf_of ps)"
  \<comment> \<open>@{const gnf_of} produces a grammar in full Greibach normal form, preserving the language
     (minus \<open>\<epsilon>\<close>).\<close>
  have GNF_Pg: "\<exists>a Bs. \<alpha> = Tm a # map Nt Bs" if "(A, \<alpha>) \<in> Pg" for A \<alpha>
    using gnf_gnf_of[of ps] that by (auto simp: Pg_def GNF_def)
  have LangPg: "Lang Pg S = Lang P S - {[]}"
    using lang_gnf_of[OF Snts] psP by (simp add: Pg_def)
  \<comment> \<open>A fresh start symbol \<open>S0\<close> copying \<open>S\<close>'s productions: meets \<open>S_notin_rhs\<close>, keeps the language.\<close>
  have finPg: "finite (Nts Pg)" by (simp add: Pg_def finite_Nts)
  define S0 where "S0 = fresh (Nts Pg) S"
  have S0_fresh: "S0 \<notin> Nts Pg" unfolding S0_def using finPg by (rule fresh_notIn)
  define R where "R = Pg \<union> {(S0, \<gamma>) |\<gamma>. (S, \<gamma>) \<in> Pg}"
  have LangR: "Lang R S0 = Lang P S - {[]}"
    using Lang_fresh_start[OF S0_fresh, of S] LangPg by (simp add: R_def)
  have GNF_R: "\<exists>a Bs. \<alpha> = Tm a # map Nt Bs" if "(A, \<alpha>) \<in> R" for A \<alpha>
    using that GNF_Pg by (auto simp: R_def)
  have "S0 \<notin> Rhs_Nts Pg" using S0_fresh by (simp add: Nts_Lhss_Rhs_Nts)
  moreover have "Rhs_Nts {(S0, \<gamma>) |\<gamma>. (S, \<gamma>) \<in> Pg} \<subseteq> Rhs_Nts Pg" by (auto simp: Rhs_Nts_def)
  ultimately have notinRhsR: "S0 \<notin> Rhs_Nts R" by (auto simp: R_def Rhs_Nts_def)
  have Snr: "S0 \<notin> set Bs" if "(A, Tm a # map Nt Bs) \<in> R" for A a Bs
    using notinRhsR that by(auto simp: Nts_syms_def Rhs_Nts_def)
  \<comment> \<open>@{term R} is finite; pick a list representation \<open>qs\<close>.\<close>
  have finR: "finite R"
  proof -
    have "{(S0, \<gamma>) |\<gamma>. (S, \<gamma>) \<in> Pg} \<subseteq> (\<lambda>\<gamma>. (S0, \<gamma>)) ` (snd ` Pg)" by force
    moreover have "finite ((\<lambda>\<gamma>. (S0, \<gamma>)) ` (snd ` Pg))" by (simp add: Pg_def)
    ultimately have "finite {(S0, \<gamma>) |\<gamma>. (S, \<gamma>) \<in> Pg}" by (rule finite_subset)
    thus ?thesis by (simp add: R_def Pg_def)
  qed
  obtain qs where qsR: "set qs = R" using finR finite_list by blast
  have std_qs: "(A, \<alpha>) \<in> set qs \<Longrightarrow> \<exists>a Bs. \<alpha> = Tm a # map Nt Bs" for A \<alpha>
    using GNF_R[of A \<alpha>] by (simp add: qsR)
  have Snr_qs: "(A, Tm a # map Nt Bs) \<in> set qs \<Longrightarrow> S0 \<notin> set Bs" for A a Bs
    using Snr[of A a Bs] by (simp add: qsR)
  \<comment> \<open>Index the (finite) nonterminals of the standard-form grammar injectively into @{typ nat}; this
     index is exactly the \<open>idx\<close> the encoding requires.\<close>
  have "finite (insert S0 (Nts (set qs)))" using finR qsR by (simp add: finite_Nts)
  from finite_imp_inj_to_nat_seg[OF this] obtain idx :: "'n \<Rightarrow> nat"
    where idxinj: "inj_on idx (insert S0 (Nts (set qs)))" by blast
  have key: "Lang (set qs) S0 - {[]} = inv_hom (enc_h idx S0 qs) (L0 - {[]})"
    by (rule Greibach_2_1_std[OF std_qs Snr_qs idxinj])
  have "Lang (set qs) S0 = Lang P S - {[]}" using qsR LangR by simp
  hence "Lang (set qs) S0 - {[]} = Lang P S - {[]}" by auto
  with key have "Lang P S - {[]} = inv_hom (enc_h idx S0 qs) (L0 - {[]})" by simp
  thus ?thesis by blast
qed

subsubsection \<open>Theorem 2.1 in full generality\<close>

text \<open>Greibach's Theorem 2.1 for an \<^emph>\<open>arbitrary\<close> finite grammar, over \<^emph>\<open>any\<close> nonterminal type: every
  context-free language, minus \<open>\<epsilon>\<close>, is the inverse homomorphic image of the one fixed hardest language
  \<open>L\<^sub>0 - {\<epsilon>}\<close>. Since \<open>P\<close> is finite, its (finitely many) nonterminals can be renamed injectively into
  @{typ nat} by @{thm [source] finite_imp_inj_to_nat_seg}; the renamed grammar is over @{typ nat},
  which has a fresh-symbol supply, so @{thm [source] Greibach_2_1_fresh0} applies, and the renaming
  preserves the language by @{thm [source] Lang_rename_Prods}.\<close>

theorem Greibach_2_1:
  fixes P :: "('n,'t) Prods"
  assumes finP: "finite P"
  shows "\<exists>h::'t \<Rightarrow> t0 list. Lang P S - {[]} = inv_hom h (L0 - {[]})"
proof -
  have finNts: "finite (Nts P \<union> {S})" using finP by (simp add: finite_Nts)
  from finite_imp_inj_to_nat_seg[OF finNts] obtain f :: "'n \<Rightarrow> nat"
    where f: "inj_on f (Nts P \<union> {S})" by blast
  have "finite (rename_Prods f P)" using finP by simp
  from Greibach_2_1_fresh0[OF this, of "f S"] obtain h :: "'t \<Rightarrow> t0 list"
    where "Lang (rename_Prods f P) (f S) - {[]} = inv_hom h (L0 - {[]})" by blast
  moreover have "Lang (rename_Prods f P) (f S) = Lang P S" using f by (rule Lang_rename_Prods)
  ultimately have "Lang P S - {[]} = inv_hom h (L0 - {[]})" by simp
  thus ?thesis by blast
qed

text \<open>The same statement at the level of languages: every context-free language, minus \<open>\<epsilon>\<close>, is the
  inverse homomorphic image of \<open>L\<^sub>0 - {\<epsilon>}\<close>. Together with \<open>CFL_L0\<close> below (\<open>L\<^sub>0\<close> is itself
  context-free) this is the precise sense in which \<open>L\<^sub>0\<close> is a \<^emph>\<open>hardest\<close> context-free language.\<close>

corollary Greibach_2_1_CFL:
  assumes "CFL TYPE('n) L"
  shows "\<exists>h. L - {[]} = inv_hom h (L0 - {[]})"
proof -
  from assms obtain P and S :: 'n where L: "L = Lang P S" and finP: "finite P"
    by (auto simp: CFL_def)
  from Greibach_2_1[OF finP, of S] show ?thesis unfolding L by blast
qed


subsection \<open>\<open>L\<^sub>0\<close> is context-free\<close>

text \<open>This property is left implicit in Greibach's paper.\<close>

subsubsection \<open>A grammar for \<open>L\<^sub>0\<close>\<close>

abbreviation (input) "oA1 \<equiv> Aa (Open A1)"
abbreviation (input) "cA1 \<equiv> Aa (Close A1)"
abbreviation (input) "oA2 \<equiv> Aa (Open A2)"
abbreviation (input) "cA2 \<equiv> Aa (Close A2)"

datatype N = NZ | NF | NM

definition G :: "(N, t0) Prods" where
  "G = {(NZ, []),
        (NZ, [Nt NF, Tm Cc, Tm Ce, Nt NM, Tm Cc, Nt NF, Tm Dd]),
        (NF, []),
        (NM, []),
        (NM, [Nt NM, Nt NM]),
        (NM, [Tm oA1, Nt NM, Tm cA1]),
        (NM, [Tm oA2, Nt NM, Tm cA2]),
        (NM, [Tm Cc, Nt NF, Tm Dd, Nt NF, Tm Cc])}
     \<union> {(NF, [Tm t, Nt NF]) | t. t \<in> Talph}"

lemma bracks_eq: "bracks = {oA1, cA1, oA2, cA2}"
using t0_A.exhaust by (auto simp: bracks_def)

lemma finite_Talph: "finite Talph"
  by (simp add:  Talph_def bracks_eq)

lemma finite_G: "finite G"
  using finite_Talph by (simp add: G_def full_SetCompr_eq)


subsubsection \<open>The free language \<open>T\<^sup>*\<close> generated by \<open>NF\<close> (\<open>\<supseteq>\<close> direction)\<close>

lemma Talph_sub_Lang_NF:
  "set w \<subseteq> Talph \<Longrightarrow> w \<in> Lang G NF"
proof (induction w)
  case Nil
  thus ?case using Lang_I[of NF "[]" G "[]"] by (simp add: G_def)
next
  case (Cons t w')
  hence t: "t \<in> Talph" and w': "w' \<in> Lang G NF" by auto
  have prod: "(NF, [Tm t, Nt NF]) \<in> G" using t by (auto simp: G_def)
  have "t # w' \<in> inst_syms (Lang G) [Tm t, Nt NF]" using w' by (auto simp: conc_def)
  thus ?case using Lang_I[OF prod] by blast
qed

subsubsection \<open>The ``middle'' language generated by \<open>NM\<close>\<close>

inductive mbal :: "t0 list \<Rightarrow> bool" where
  mbal_Nil:  "mbal []"
| mbal_app:  "mbal w \<Longrightarrow> mbal w' \<Longrightarrow> mbal (w @ w')"
| mbal_wrap: "mbal w \<Longrightarrow> mbal (Aa (Open a) # w @ [Aa (Close a)])"
| mbal_gap:  "set z \<subseteq> Talph \<Longrightarrow> set x \<subseteq> Talph \<Longrightarrow> mbal (Cc # z @ Dd # x @ [Cc])"

lemma mbal_imp_Lang_NM: "mbal w \<Longrightarrow> w \<in> Lang G NM"
proof (induction rule: mbal.induct)
  case mbal_Nil
  have "(NM, []) \<in> G" by (simp add: G_def)
  thus ?case using Lang_I[of NM "[]" G "[]"] by simp
next
  case (mbal_app w w')
  have prod: "(NM, [Nt NM, Nt NM]) \<in> G" by (simp add: G_def)
  have "w @ w' \<in> inst_syms (Lang G) [Nt NM, Nt NM]"
    using mbal_app.IH by (auto simp: conc_def)
  thus ?case using Lang_I[OF prod] by blast
next
  case (mbal_wrap w a)
  show ?case
  proof (cases a)
    case A1
    have prod: "(NM, [Tm oA1, Nt NM, Tm cA1]) \<in> G" by (simp add: G_def)
    have "Aa (Open a) # w @ [Aa (Close a)] \<in> inst_syms (Lang G) [Tm oA1, Nt NM, Tm cA1]"
      using mbal_wrap.IH A1 by (auto simp: conc_def)
    thus ?thesis using Lang_I[OF prod] by blast
  next
    case A2
    have prod: "(NM, [Tm oA2, Nt NM, Tm cA2]) \<in> G" by (simp add: G_def)
    have "Aa (Open a) # w @ [Aa (Close a)] \<in> inst_syms (Lang G) [Tm oA2, Nt NM, Tm cA2]"
      using mbal_wrap.IH A2 by (auto simp: conc_def)
    thus ?thesis using Lang_I[OF prod] by blast
  qed
next
  case (mbal_gap z x)
  have prod: "(NM, [Tm Cc, Nt NF, Tm Dd, Nt NF, Tm Cc]) \<in> G" by (simp add: G_def)
  have "Cc # z @ Dd # x @ [Cc] \<in> inst_syms (Lang G) [Tm Cc, Nt NF, Tm Dd, Nt NF, Tm Cc]"
    using Talph_sub_Lang_NF[OF mbal_gap.hyps(1)] Talph_sub_Lang_NF[OF mbal_gap.hyps(2)]
    by (auto simp: conc_def)
  thus ?case using Lang_I[OF prod] by blast
qed

subsubsection \<open>Gaps and the interleaving of bracket blocks with gaps\<close>

definition Gap :: "t0 list set" where
  "Gap = {Cc # z @ Dd # x @ [Cc] | x z. set z \<subseteq> Talph \<and> set x \<subseteq> Talph}"

lemma GapI: "set z \<subseteq> Talph \<Longrightarrow> set x \<subseteq> Talph \<Longrightarrow> Cc # z @ Dd # x @ [Cc] \<in> Gap"
  by (auto simp: Gap_def)

fun interl :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
  "interl [] _ = []"
| "interl (y#ys) [] = y @ interl ys []"
| "interl (y#ys) (g#gs) = y @ g @ interl ys gs"

lemma interl_merge:
  "length ya = length gs1 \<Longrightarrow>
   interl (ya @ [yl]) gs1 @ interl (yr # ys2) gs2
   = interl (ya @ (yl @ yr) # ys2) (gs1 @ gs2)"
proof (induction ya arbitrary: gs1)
  case Nil
  thus ?case by (cases gs2) auto
next
  case (Cons a ya')
  then obtain g gs1' where "gs1 = g # gs1'" by (cases gs1) auto
  with Cons show ?case by auto
qed

text \<open>\<open>Ymid W\<close>: \<open>W\<close> is a sequence of bracket blocks separated by gaps, whose concatenation is balanced.\<close>

definition Ymid :: "t0 list \<Rightarrow> bool" where
  "Ymid W \<longleftrightarrow> (\<exists>ys gs. W = interl ys gs \<and> length ys = Suc (length gs) \<and>
                (\<forall>g\<in>set gs. g \<in> Gap) \<and> (\<forall>y\<in>set ys. set y \<subseteq> bracks) \<and>
                bal (map brk (concat ys)))"

lemma Ymid_Nil: "Ymid []"
  unfolding Ymid_def
  by (rule exI[of _ "[[]]"], rule exI[of _ "[]"]) auto

lemma Ymid_gap: "g \<in> Gap \<Longrightarrow> Ymid g"
  unfolding Ymid_def
  by (rule exI[of _ "[[],[]]"], rule exI[of _ "[g]"]) auto

lemma Ymid_app:
  assumes "Ymid Wa" and "Ymid Wb" shows "Ymid (Wa @ Wb)"
proof -
  from assms(1) obtain ys1 gs1 where Wa: "Wa = interl ys1 gs1" and len1: "length ys1 = Suc (length gs1)"
    and g1: "\<forall>g\<in>set gs1. g \<in> Gap" and y1: "\<forall>y\<in>set ys1. set y \<subseteq> bracks"
    and bl1: "bal (map brk (concat ys1))" by (auto simp: Ymid_def)
  from assms(2) obtain ys2 gs2 where Wb: "Wb = interl ys2 gs2" and len2: "length ys2 = Suc (length gs2)"
    and g2: "\<forall>g\<in>set gs2. g \<in> Gap" and y2: "\<forall>y\<in>set ys2. set y \<subseteq> bracks"
    and bl2: "bal (map brk (concat ys2))" by (auto simp: Ymid_def)
  from len1 obtain ya yl where ys1: "ys1 = ya @ [yl]" and lenya: "length ya = length gs1"
    by (metis length_Suc_conv_rev)
  from len2 obtain yr ys2' where ys2: "ys2 = yr # ys2'" by (cases ys2) auto
  let ?ys = "ya @ (yl @ yr) # ys2'"
  let ?gs = "gs1 @ gs2"
  have wcat: "Wa @ Wb = interl ?ys ?gs"
    using Wa Wb ys1 ys2 interl_merge[OF lenya, of yl yr ys2' gs2] by simp
  have lenc: "length ?ys = Suc (length ?gs)"
    using lenya len1 len2 ys1 ys2 by simp
  have ccat: "concat ?ys = concat ys1 @ concat ys2"
    using ys1 ys2 by simp
  have "bal (map brk (concat ?ys))"
    using bl1 bl2 ccat by simp
  moreover have "\<forall>g\<in>set ?gs. g \<in> Gap" using g1 g2 by auto
  moreover have "\<forall>y\<in>set ?ys. set y \<subseteq> bracks"
    using y1 y2 ys1 ys2 by auto
  ultimately have "Wa @ Wb = interl ?ys ?gs \<and> length ?ys = Suc (length ?gs) \<and>
      (\<forall>g\<in>set ?gs. g \<in> Gap) \<and> (\<forall>y\<in>set ?ys. set y \<subseteq> bracks) \<and> bal (map brk (concat ?ys))"
    using wcat lenc by blast
  thus ?thesis unfolding Ymid_def by blast
qed

lemma interl_prepend_first: "interl ((p @ y) # ys) gs = p @ interl (y # ys) gs"
  by (cases gs) auto

lemma interl_append_last:
  "length ys = length gs \<Longrightarrow> interl (ys @ [yl @ s]) gs = interl (ys @ [yl]) gs @ s"
by (metis append.right_neutral interl.simps(1,2) interl_merge)

lemma Ymid_wrap:
  assumes "Ymid W" shows "Ymid (Aa (Open a) # W @ [Aa (Close a)])"
proof -
  from assms obtain ys gs where W: "W = interl ys gs" and len: "length ys = Suc (length gs)"
    and gG: "\<forall>g\<in>set gs. g \<in> Gap" and yB: "\<forall>y\<in>set ys. set y \<subseteq> bracks"
    and bl: "bal (map brk (concat ys))" by (auto simp: Ymid_def)
  from len have "ys \<noteq> []" by auto
  then obtain yf ys' where ys: "ys = yf # ys'" by (cases ys) auto
  show ?thesis
  proof (cases "ys' = []")
    case True
    with ys have ys1: "ys = [yf]" by simp
    with len have gnil: "gs = []" by auto
    let ?ys = "[Aa (Open a) # yf @ [Aa (Close a)]]"
    have eqW: "Aa (Open a) # W @ [Aa (Close a)] = interl ?ys []"
      using W ys1 gnil by simp
    have mb1: "map brk (concat ?ys) = Open a # map brk (concat ys) @ [Close a]"
      using ys1 by simp
    have "bal (map brk (concat ?ys))" unfolding mb1 by (rule bal.intros(3)[OF bl])
    moreover have "\<forall>y\<in>set ?ys. set y \<subseteq> bracks"
      using yB ys1 by (auto simp: bracks_def)
    ultimately show ?thesis using eqW gnil unfolding Ymid_def
      by (intro exI[of _ ?ys] exI[of _ "[]"]) simp
  next
    case False
    then obtain ysm yl where ys': "ys' = ysm @ [yl]" by (metis rev_exhaust)
    let ?ys = "(Aa (Open a) # yf) # ysm @ [yl @ [Aa (Close a)]]"
    have lenfm: "length (yf # ysm) = length gs"
      using len ys ys' by simp
    have eqW: "Aa (Open a) # W @ [Aa (Close a)] = interl ?ys gs"
    proof -
      have "interl ?ys gs = Aa (Open a) # interl (yf # ysm @ [yl @ [Aa (Close a)]]) gs"
        using interl_prepend_first[of "[Aa (Open a)]" yf "ysm @ [yl @ [Aa (Close a)]]" gs] by simp
      also have "interl (yf # ysm @ [yl @ [Aa (Close a)]]) gs
                 = interl ((yf # ysm) @ [yl @ [Aa (Close a)]]) gs" by simp
      also have "\<dots> = interl ((yf # ysm) @ [yl]) gs @ [Aa (Close a)]"
        using interl_append_last[OF lenfm] by simp
      also have "interl ((yf # ysm) @ [yl]) gs = W" using W ys ys' by simp
      finally show ?thesis by simp
    qed
    have ccat: "concat ?ys = Aa (Open a) # concat ys @ [Aa (Close a)]"
      using ys ys' by simp
    have mb: "map brk (concat ?ys) = Open a # map brk (concat ys) @ [Close a]"
      using ys ys' by simp
    have "bal (map brk (concat ?ys))"
      unfolding mb by (rule bal.intros(3)[OF bl])
    moreover have "\<forall>y\<in>set ?ys. set y \<subseteq> bracks"
      using yB ys ys' by (auto simp: bracks_def)
    moreover have "length ?ys = Suc (length gs)" using lenfm by simp
    ultimately show ?thesis using eqW gG unfolding Ymid_def
      by (intro exI[of _ ?ys] exI[of _ gs]) simp
  qed
qed

subsubsection \<open>From \<open>Ymid\<close> to \<open>mbal\<close>: inserting gaps into a balanced skeleton\<close>

lemma Gap_imp_mbal: "g \<in> Gap \<Longrightarrow> mbal g"
  by (auto simp: Gap_def mbal_gap)

inductive sprd :: "t0 list \<Rightarrow> t0_A bracket list \<Rightarrow> bool" where
  sprd_Nil:  "sprd [] []"
| sprd_gap:  "g \<in> Gap \<Longrightarrow> sprd W bw \<Longrightarrow> sprd (g @ W) bw"
| sprd_brk:  "sprd W bw \<Longrightarrow> sprd (Aa b # W) (b # bw)"

lemma sprd_emptybw: "sprd W [] \<Longrightarrow> mbal W"
proof (induction W "[] :: t0_A bracket list" rule: sprd.induct)
  case sprd_Nil thus ?case by (simp add: mbal_Nil)
next
  case (sprd_gap g W) thus ?case by (simp add: Gap_imp_mbal mbal_app)
qed

lemma sprd_brk_list:
  "set y \<subseteq> bracks \<Longrightarrow> sprd Wr bw \<Longrightarrow> sprd (y @ Wr) (map brk y @ bw)"
proof (induction y)
  case Nil thus ?case by simp
next
  case (Cons c y') thus ?case using sprd_brk by (auto simp: bracks_def)
qed

lemma interl_sprd:
  "length ys = Suc (length gs) \<Longrightarrow> (\<forall>g\<in>set gs. g \<in> Gap) \<Longrightarrow> (\<forall>y\<in>set ys. set y \<subseteq> bracks)
   \<Longrightarrow> sprd (interl ys gs) (map brk (concat ys))"
proof (induction ys arbitrary: gs)
  case Nil thus ?case by simp
next
  case (Cons y ys')
  show ?case
  proof (cases gs)
    case Nil then show ?thesis using Cons.prems sprd_brk_list[OF _ sprd_Nil] by auto
  next
    case (Cons g gs') thus ?thesis using sprd_brk_list sprd_gap Cons.IH Cons.prems by auto
  qed
qed

lemma sprd_split:
  "sprd W bw \<Longrightarrow> bw = bw1 @ bw2 \<Longrightarrow> \<exists>W1 W2. W = W1 @ W2 \<and> sprd W1 bw1 \<and> sprd W2 bw2"
proof (induction arbitrary: bw1 bw2 rule: sprd.induct)
  case sprd_Nil
  thus ?case by (auto intro: sprd.sprd_Nil)
next
  case (sprd_gap g W bw)
  thus ?case using sprd_gap.IH[OF sprd_gap.prems]
    by (metis append.assoc sprd.sprd_gap)
next
  case (sprd_brk W bw b)
  show ?case
  proof (cases bw1)
    case Nil
    thus ?thesis using sprd_brk by (auto intro: sprd.sprd_Nil sprd.sprd_brk)
  next
    case (Cons c bw1')
    thus ?thesis
      using sprd_brk sprd.sprd_brk by (metis append_Cons list.inject)
  qed
qed

lemma sprd_head:
  "sprd W bw \<Longrightarrow> bw = b # bw' \<Longrightarrow> \<exists>U Wr. W = U @ Aa b # Wr \<and> mbal U \<and> sprd Wr bw'"
proof (induction arbitrary: b bw' rule: sprd.induct)
  case sprd_Nil thus ?case by simp
next
  case (sprd_gap g W bw)
  thus ?case
    using Gap_imp_mbal mbal_app by (metis append.assoc)
next
  case (sprd_brk W bw c)
  thus ?case by (auto intro: mbal_Nil)
qed

lemma sprd_tail:
  "sprd W bw \<Longrightarrow> bw = bw' @ [b] \<Longrightarrow> \<exists>Wl U. W = Wl @ Aa b # U \<and> sprd Wl bw' \<and> mbal U"
proof (induction arbitrary: bw' b rule: sprd.induct)
  case sprd_Nil thus ?case by simp
next
  case (sprd_gap g W bw)
  with sprd_gap.IH[OF sprd_gap.prems] show ?case
    by (metis append.assoc sprd.sprd_gap)
next
  case (sprd_brk W bw c)
  show ?case
  proof (cases bw')
    case Nil
    thus ?thesis using sprd_brk sprd_emptybw
      by (auto intro: sprd.sprd_Nil)
  next
    case (Cons d bw'')
    thus ?thesis
      using sprd_brk sprd.sprd_brk by (metis append_Cons list.inject)
  qed
qed

lemma sprd_bal_imp_mbal: "bal bw \<Longrightarrow> sprd W bw \<Longrightarrow> mbal W"
proof (induction arbitrary: W rule: bal.induct[case_names Emp App Wrap])
  case Emp
  thus ?case by (rule sprd_emptybw)
next
  case (App xs ys)
  with sprd_split[OF App.prems refl] show ?case by(auto simp add: mbal_app)
next
  case (Wrap xs a)
  from sprd_head[OF Wrap.prems refl] obtain U Wr
    where Wdef: "W = U @ Aa (Open a) # Wr" and mU: "mbal U"
      and sWr: "sprd Wr (xs @ [Close a])" by blast
  from sprd_tail[OF sWr refl] obtain Wl U2
    where Wrdef: "Wr = Wl @ Aa (Close a) # U2" and sWl: "sprd Wl xs" and mU2: "mbal U2" by blast
  show ?case
    using Wdef Wrdef using Wrap.IH sWl mbal_app[OF mU mbal_app[OF _ mU2]] mbal_wrap
    by fastforce
qed

subsubsection \<open>Bridging \<open>Ymid\<close> and the block-list form of \<open>L\<^sub>0\<close>\<close>

text \<open>From a balanced \<open>Ymid\<close>-decomposition build the \<open>L\<^sub>0\<close> block list: the gaps split into the
  \<open>z\<^sub>i\<close>/\<open>x\<^sub>i\<^sub>+\<^sub>1\<close> parts of adjacent blocks.\<close>

lemma mkblocks:
  "length ys = Suc (length gs) \<Longrightarrow> (\<forall>g\<in>set gs. g \<in> Gap) \<Longrightarrow> set x \<subseteq> Talph \<Longrightarrow> set z \<subseteq> Talph \<Longrightarrow>
   \<exists>bs. bs \<noteq> [] \<and> (\<forall>(a,b,c)\<in>set bs. set a \<subseteq> Talph \<and> set c \<subseteq> Talph) \<and>
        map (\<lambda>(a,b,c). b) bs = ys \<and>
        concat (map blk bs) = x @ [Cc] @ interl ys gs @ [Cc] @ z @ [Dd]"
proof (induction ys arbitrary: gs x)
  case Nil thus ?case by simp
next
  case (Cons y0 ys')
  show ?case
  proof (cases "gs = []")
    case True
    thus ?thesis using Cons by (intro exI[of _ "[(x, y0, z)]"]) (simp add: blk_def)
  next
    case False
    then obtain g gs' where gs: "gs = g # gs'" by (cases gs) auto
    from Cons.prems(2) gs obtain zz xx where g: "g = Cc # zz @ Dd # xx @ [Cc]"
      and zzT: "set zz \<subseteq> Talph" and xxT: "set xx \<subseteq> Talph" by (auto simp: Gap_def)
    have len': "length ys' = Suc (length gs')" using Cons.prems(1) gs by simp
    have "\<forall>g\<in>set gs'. g \<in> Gap" using Cons.prems(2) gs by simp
    from Cons.IH[OF len' this xxT Cons.prems(4)] obtain bs' where
      bs'ne: "bs' \<noteq> []" and ac': "\<forall>(a,b,c)\<in>set bs'. set a \<subseteq> Talph \<and> set c \<subseteq> Talph"
      and mid': "map (\<lambda>(a,b,c). b) bs' = ys'"
      and cc': "concat (map blk bs') = xx @ [Cc] @ interl ys' gs' @ [Cc] @ z @ [Dd]" by blast
    have "concat (map blk ((x, y0, zz) # bs')) = x @ [Cc] @ interl (y0 # ys') gs @ [Cc] @ z @ [Dd]"
      using cc' g gs by (simp add: blk_def)
    moreover have "\<forall>(a,b,c)\<in>set ((x, y0, zz) # bs'). set a \<subseteq> Talph \<and> set c \<subseteq> Talph"
      using ac' Cons.prems(3) zzT by auto
    moreover have "map (\<lambda>(a,b,c). b) ((x, y0, zz) # bs') = y0 # ys'" using mid' by simp
    ultimately show ?thesis using bs'ne by (intro exI[of _ "(x, y0, zz) # bs'"]) simp
  qed
qed

text \<open>The inverse: every \<open>L\<^sub>0\<close> block list arises this way.\<close>

lemma blocks_decomp:
  "bs \<noteq> [] \<Longrightarrow> (\<forall>(a,b,c)\<in>set bs. set a \<subseteq> Talph \<and> set c \<subseteq> Talph) \<Longrightarrow>
   \<exists>x ys gs z. set x \<subseteq> Talph \<and> set z \<subseteq> Talph \<and> length ys = Suc (length gs) \<and> (\<forall>g\<in>set gs. g \<in> Gap) \<and>
     map (\<lambda>(a,b,c). b) bs = ys \<and>
     concat (map blk bs) = x @ [Cc] @ interl ys gs @ [Cc] @ z @ [Dd]"
proof (induction bs)
  case Nil thus ?case by simp
next
  case (Cons abc bs')
  obtain a b c where abc: "abc = (a, b, c)" by (cases abc)
  have aT: "set a \<subseteq> Talph" and cT: "set c \<subseteq> Talph" using Cons.prems(2) abc by auto
  show ?case
  proof (cases "bs' = []")
    case True thus ?thesis
      using abc aT cT by (auto simp add: blk_def)
  next
    case False
    have ac': "\<forall>(a,b,c)\<in>set bs'. set a \<subseteq> Talph \<and> set c \<subseteq> Talph" using Cons.prems(2) by auto
    from Cons.IH[OF False ac'] obtain x ys gs z where
      xT: "set x \<subseteq> Talph" and zT: "set z \<subseteq> Talph" and len: "length ys = Suc (length gs)"
      and gG: "\<forall>g\<in>set gs. g \<in> Gap" and mid: "map (\<lambda>(a,b,c). b) bs' = ys"
      and cc: "concat (map blk bs') = x @ [Cc] @ interl ys gs @ [Cc] @ z @ [Dd]" by blast
    have gGap: "(Cc # c @ Dd # x @ [Cc]) \<in> Gap" using cT xT by (rule GapI)
    have "concat (map blk ((a, b, c) # bs'))
        = a @ [Cc] @ interl (b # ys) ((Cc # c @ Dd # x @ [Cc]) # gs) @ [Cc] @ z @ [Dd]"
      using cc by (simp add: blk_def)
    moreover have "length (b # ys) = Suc (length ((Cc # c @ Dd # x @ [Cc]) # gs))" using len by simp
    moreover have "\<forall>g\<in>set ((Cc # c @ Dd # x @ [Cc]) # gs). g \<in> Gap" using gG gGap by simp
    moreover have "map (\<lambda>(a,b,c). b) ((a, b, c) # bs') = b # ys" using mid by simp
    ultimately show ?thesis using abc aT zT
      by (intro exI[of _ a] exI[of _ "b # ys"] exI[of _ "(Cc # c @ Dd # x @ [Cc]) # gs"] exI[of _ z]) auto
  qed
qed

text \<open>The two halves of the characterisation \<open>L\<^sub>0 - {\<epsilon>} = T\<^sup>* c \<cent> (Ymid) c T\<^sup>* d\<close>.\<close>

lemma Ymid_imp_L0:
  assumes Y: "Ymid W" and xT: "set x \<subseteq> Talph" and zT: "set z \<subseteq> Talph"
  shows "x @ [Cc, Ce] @ W @ [Cc] @ z @ [Dd] \<in> L0"
proof -
  from Y obtain ys gs where W: "W = interl ys gs" and len: "length ys = Suc (length gs)"
    and gG: "\<forall>g\<in>set gs. g \<in> Gap" and yB: "\<forall>y\<in>set ys. set y \<subseteq> bracks"
    and bl: "bal (map brk (concat ys))" by (auto simp: Ymid_def)
  from len have "ys \<noteq> []" by auto
  then obtain y0 ys' where ys: "ys = y0 # ys'" by (cases ys) auto
  have len2: "length ((Ce # y0) # ys') = Suc (length gs)" using len ys by simp
  from mkblocks[OF len2 gG xT zT] obtain bs where bsP:
    "bs \<noteq> [] \<and> (\<forall>(a,b,c)\<in>set bs. set a \<subseteq> Talph \<and> set c \<subseteq> Talph) \<and>
     map (\<lambda>(a,b,c). b) bs = (Ce # y0) # ys' \<and>
     concat (map blk bs) = x @ [Cc] @ interl ((Ce # y0) # ys') gs @ [Cc] @ z @ [Dd]" ..
  have ceW: "interl ((Ce # y0) # ys') gs = Ce # W"
    using interl_prepend_first[of "[Ce]" y0 ys' gs] W ys by simp
  have word: "concat (map blk bs) = x @ [Cc, Ce] @ W @ [Cc] @ z @ [Dd]"
    using bsP ceW by simp
  have midtl: "map (\<lambda>(a,b,c). b) (tl bs) = ys'" by (simp add: map_tl bsP)
  have tlmid: "set b \<subseteq> bracks" if tabc: "(a,b,c)\<in>set (tl bs)" for a b c
    using tabc midtl yB ys  by force
  have midD: "\<exists>v\<in>D. concat (map (\<lambda>(a,b,c). b) bs) = Ce # v"
  proof -
    have "concat ys \<in> D" by (simp add: D_def UN_least bl yB)
    then show ?thesis using bsP ys by simp
  qed
  have "concat (map blk bs) \<in> L0" unfolding L0_def using bsP tlmid midD by blast
  thus ?thesis using word by simp
qed

lemma L0_imp_Ymid:
  assumes "w \<in> L0" and "w \<noteq> []"
  shows "\<exists>x z W. w = x @ [Cc, Ce] @ W @ [Cc] @ z @ [Dd] \<and> set x \<subseteq> Talph \<and> set z \<subseteq> Talph \<and> Ymid W"
proof -
  from assms obtain bs where wbs: "w = concat (map blk bs)" and bsne: "bs \<noteq> []"
    and acT: "\<forall>(x,y,z)\<in>set bs. set x \<subseteq> Talph \<and> set z \<subseteq> Talph"
    and tlb: "\<forall>(x,y,z)\<in>set (tl bs). set y \<subseteq> bracks"
    and cD: "\<exists>v\<in>D. concat (map (\<lambda>(x,y,z). y) bs) = Ce # v"
    by (auto simp: L0_def)
  from blocks_decomp[OF bsne acT] obtain x ys gs z where
    xT: "set x \<subseteq> Talph" and zT: "set z \<subseteq> Talph" and len: "length ys = Suc (length gs)"
    and gG: "\<forall>g\<in>set gs. g \<in> Gap" and bmid: "map (\<lambda>(a,b,c). b) bs = ys"
    and wcc: "concat (map blk bs) = x @ [Cc] @ interl ys gs @ [Cc] @ z @ [Dd]" by blast
  from cD obtain v where vD: "v \<in> D" and cyv: "concat (map (\<lambda>(x,y,z). y) bs) = Ce # v" by blast
  have ysv: "concat ys = Ce # v" using cyv bmid by simp
  from len obtain y0 ys' where ys: "ys = y0 # ys'" by (cases ys) auto
  have ys'brk: "\<forall>y\<in>set ys'. set y \<subseteq> bracks"
    using bmid ys tlb by (fastforce simp add: map_tl)
  have y0ne: "y0 \<noteq> []"
  proof
    assume y0nil: "y0 = []"
    have "Ce \<in> set (concat ys)" using ysv by simp
    moreover have "set (concat ys) = set (concat ys')" using ys y0nil by simp
    ultimately show False using ys y0nil ys'brk by (auto simp add: bracks_def)
  qed
  then obtain h b0 where y0split: "y0 = h # b0" by (cases y0) auto
  have "h = Ce" and bv: "b0 @ concat ys' = v" using ysv ys y0split by auto
  hence y0: "y0 = Ce # b0" using y0split by simp
  let ?W = "interl (b0 # ys') gs"
  have ceW: "interl ys gs = Ce # ?W"
    using interl_prepend_first[of "[Ce]" b0 ys' gs] ys y0 by simp
  have wword: "w = x @ [Cc, Ce] @ ?W @ [Cc] @ z @ [Dd]"
    using wbs wcc ceW by simp
  have b0brk: "set b0 \<subseteq> bracks" using bv vD by (auto simp: D_def)
  have "Ymid ?W" using bv b0brk vD ys ys'brk gG len unfolding Ymid_def D_def mem_Collect_eq
    by (metis (no_types, lifting) concat.simps(2) length_Cons set_ConsD) 
  thus ?thesis using wword xT zT by blast
qed

subsection \<open>\<open>Lang G NZ = L\<^sub>0\<close> and context-freeness of \<open>L\<^sub>0\<close>\<close>

text \<open>The candidate solution assigning each nonterminal its intended language.\<close>

definition Rsol :: "N \<Rightarrow> t0 list set" where
  "Rsol A = (case A of NZ \<Rightarrow> L0 | NF \<Rightarrow> {w. set w \<subseteq> Talph} | NM \<Rightarrow> {W. Ymid W})"

text \<open>Each production keeps the candidate solution closed (the \<open>\<subseteq>\<close>-obligations).\<close>

lemma incl_NZ_big: "inst_syms Rsol [Nt NF, Tm Cc, Tm Ce, Nt NM, Tm Cc, Nt NF, Tm Dd] \<subseteq> Rsol NZ"
proof
  fix w assume "w \<in> inst_syms Rsol [Nt NF, Tm Cc, Tm Ce, Nt NM, Tm Cc, Nt NF, Tm Dd]"
  then obtain x W z where w: "w = x @ [Cc, Ce] @ W @ [Cc] @ z @ [Dd]"
    and xT: "set x \<subseteq> Talph" and YW: "Ymid W" and zT: "set z \<subseteq> Talph"
    by (auto simp: Rsol_def conc_def)
  show "w \<in> Rsol NZ"
    using Ymid_imp_L0[OF YW xT zT] w by (simp add: Rsol_def)
qed

lemma Lang_G_subset: "Lang G A \<subseteq> Rsol A"
proof (rule Lang_subset_if)
  fix A \<alpha> assume aG: "(A, \<alpha>) \<in> G"
  consider "(A,\<alpha>) = (NZ, [])"
    | "(A,\<alpha>) = (NZ, [Nt NF, Tm Cc, Tm Ce, Nt NM, Tm Cc, Nt NF, Tm Dd])"
    | "(A,\<alpha>) = (NF, [])" | "(A,\<alpha>) = (NM, [])" | "(A,\<alpha>) = (NM, [Nt NM, Nt NM])"
    | "(A,\<alpha>) = (NM, [Tm oA1, Nt NM, Tm cA1])" | "(A,\<alpha>) = (NM, [Tm oA2, Nt NM, Tm cA2])"
    | "(A,\<alpha>) = (NM, [Tm Cc, Nt NF, Tm Dd, Nt NF, Tm Cc])"
    | t where "t \<in> Talph" "(A,\<alpha>) = (NF, [Tm t, Nt NF])"
    using aG unfolding G_def by (elim UnE insertE CollectE exE conjE) simp_all
  then show "inst_syms Rsol \<alpha> \<subseteq> Rsol A"
  proof cases
    case 1 thus ?thesis by (auto simp: Rsol_def L0_def)
  next
    case 2 thus ?thesis using incl_NZ_big by simp
  next
    case 3 thus ?thesis by (auto simp: Rsol_def)
  next
    case 4 thus ?thesis by (auto simp: Rsol_def Ymid_Nil)
  next
    case 5 thus ?thesis by (auto simp: Rsol_def conc_def intro: Ymid_app)
  next
    case 6 thus ?thesis by (auto simp: Rsol_def conc_def intro: Ymid_wrap)
  next
    case 7 thus ?thesis by (auto simp: Rsol_def conc_def intro: Ymid_wrap)
  next
    case 8 thus ?thesis by (auto simp: Rsol_def conc_def intro: Ymid_gap GapI)
  next
    case (9 t) thus ?thesis by (auto simp: Rsol_def conc_def)
  qed
qed

text \<open>The \<open>\<supseteq>\<close> direction for the start symbol.\<close>

lemma Ymid_imp_Lang_NM: "Ymid W \<Longrightarrow> W \<in> Lang G NM"
using Ymid_def interl_sprd sprd_bal_imp_mbal mbal_imp_Lang_NM by auto

lemma L0_subset_Lang: "L0 \<subseteq> Lang G NZ"
proof
  fix w assume wL0: "w \<in> L0"
  show "w \<in> Lang G NZ"
  proof (cases "w = []")
    case True
    thus ?thesis using Lang_I[of NZ "[]" G "[]"] True by (simp add: G_def)
  next
    case False
    from L0_imp_Ymid[OF wL0 False] obtain x z W where
      w: "w = x @ [Cc, Ce] @ W @ [Cc] @ z @ [Dd]"
      and xT: "set x \<subseteq> Talph" and zT: "set z \<subseteq> Talph" and YW: "Ymid W" by blast
    have prod: "(NZ, [Nt NF, Tm Cc, Tm Ce, Nt NM, Tm Cc, Nt NF, Tm Dd]) \<in> G" by (simp add: G_def)
    have "w \<in> inst_syms (Lang G) [Nt NF, Tm Cc, Tm Ce, Nt NM, Tm Cc, Nt NF, Tm Dd]"
    proof -
      let ?ws = "[x, [Cc], [Ce], W, [Cc], z, [Dd]]"
      let ?al = "[Nt NF, Tm Cc, Tm Ce, Nt NM, Tm Cc, Nt NF, Tm Dd]"
      have "\<forall>i < length ?ws. ?ws ! i \<in> inst_sym (Lang G) (?al ! i)"
        using Talph_sub_Lang_NF[OF xT] Talph_sub_Lang_NF[OF zT] Ymid_imp_Lang_NM[OF YW]
        by (auto simp: nth_Cons' split: if_splits)
      from inst_syms_decomp[OF this] show ?thesis using w by simp
    qed
    thus ?thesis using Lang_I[OF prod] by blast
  qed
qed

lemma Lang_G_NZ: "Lang G NZ = L0"
  using Lang_G_subset[of NZ] L0_subset_Lang by (auto simp: Rsol_def)

text \<open>Greibach's hardest language \<open>L\<^sub>0\<close> is itself context-free.\<close>

theorem CFL_L0: "CFL TYPE(N) L0"
using CFL_def Lang_G_NZ finite_G by blast

end
