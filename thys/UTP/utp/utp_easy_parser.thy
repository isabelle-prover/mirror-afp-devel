section \<open> UTP Easy Expression Parser \<close>

theory utp_easy_parser
  imports utp_full
begin

subsection \<open> Replacing the Expression Grammar \<close>

text \<open> The following theory provides an easy to use expression parser that is primarily targetted
  towards expressing programs. Unlike the built-in UTP expression syntax, this uses a closed grammar
  separate to the HOL \emph{logic} nonterminal, that gives more freedom in what can be expressed.
  In particular, identifiers are interpreted as UTP variables rather than HOL variables and functions
  do not require subscripts and other strange decorations. 

  The first step is to remove the from the UTP parse the following grammar rule that uses arbitrary
  HOL logic to represent expressions. Instead, we will populate the \emph{uexp} grammar manually.
\<close>

purge_syntax
  "_uexp_l"  :: "logic \<Rightarrow> uexp" (\<open>_\<close> [64] 64)

subsection \<open> Expression Operators \<close>

syntax
  "_ue_quote" :: "uexp \<Rightarrow> logic" (\<open>'(_')\<^sub>e\<close>)
  "_ue_tuple" :: "uexprs \<Rightarrow> uexp" (\<open>'(_')\<close>)
  "_ue_lit"   :: "logic \<Rightarrow> uexp" (\<open>\<guillemotleft>_\<guillemotright>\<close>)
  "_ue_var"   :: "svid \<Rightarrow> uexp" (\<open>_\<close>)
  "_ue_eq"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix \<open>=\<close> 150)
  "_ue_uop"   :: "id   \<Rightarrow> uexp \<Rightarrow> uexp" (\<open>_'(_')\<close> [999,0] 999)
  "_ue_bop"   :: "id   \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" (\<open>_'(_, _')\<close> [999,0,0] 999)
  "_ue_trop"  :: "id   \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp \<Rightarrow> uexp" (\<open>_'(_, _, _')\<close> [999,0,0,0] 999)
  "_ue_apply" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (\<open>_[_]\<close> [999] 999)

translations
  "_ue_quote e" => "e"
  "_ue_tuple (_uexprs x (_uexprs y z))" => "_ue_tuple (_uexprs x (_ue_tuple (_uexprs y z)))"
  "_ue_tuple (_uexprs x y)" => "CONST bop CONST Pair x y"
  "_ue_tuple x" => "x"
  "_ue_lit x"    => "CONST lit x"
  "_ue_var x"    => "CONST utp_expr.var (CONST pr_var x)"
  "_ue_eq x y"   => "x =\<^sub>u y"
  "_ue_uop f x"   => "CONST uop f x"
  "_ue_bop f x y" => "CONST bop f x y"
  "_ue_trop f x y" => "CONST trop f x y"
  "_ue_apply f x" => "f(x)\<^sub>a"

subsection \<open> Predicate Operators \<close>

syntax
  "_ue_true"  :: "uexp" (\<open>true\<close>)
  "_ue_false" :: "uexp" (\<open>false\<close>)
  "_ue_not"   :: "uexp \<Rightarrow> uexp" (\<open>\<not> _\<close> [40] 40)
  "_ue_conj"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr \<open>\<and>\<close> 135)
  "_ue_disj"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr \<open>\<or>\<close> 130)
  "_ue_impl"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr \<open>\<Rightarrow>\<close> 125)
  "_ue_iff"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr \<open>\<Rightarrow>\<close> 125)
  "_ue_mem"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (\<open>(_/ \<in> _)\<close> [151, 151] 150)
  "_ue_nmem"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (\<open>(_/ \<notin> _)\<close> [151, 151] 150)

translations
  "_ue_true" => "CONST true_upred"
  "_ue_false" => "CONST false_upred"
  "_ue_not p" => "CONST not_upred p"
  "_ue_conj p q" => "p \<and>\<^sub>p q"
  "_ue_disj p q" => "p \<or>\<^sub>p q"
  "_ue_impl p q" => "p \<Rightarrow> q"
  "_ue_iff p q"  => "p \<Leftrightarrow> q"
  "_ue_mem x A"  => "x \<in>\<^sub>u A"
  "_ue_nmem x A" => "x \<notin>\<^sub>u A"

subsection \<open> Arithmetic Operators \<close>

syntax
  "_ue_num"    :: "num_const \<Rightarrow> uexp" (\<open>_\<close>)
  "_ue_size"   :: "uexp \<Rightarrow> uexp" (\<open>#_\<close> [999] 999)
  "_ue_eq"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix \<open>=\<close> 150)
  "_ue_le"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix \<open>\<le>\<close> 150)
  "_ue_lt"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix \<open><\<close> 150)
  "_ue_ge"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix \<open>\<ge>\<close> 150)
  "_ue_gt"     :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infix \<open>>\<close> 150)
  "_ue_zero"   :: "uexp" (\<open>0\<close>)
  "_ue_one"    :: "uexp" (\<open>1\<close>)
  "_ue_plus"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl \<open>+\<close> 165)
  "_ue_uminus" :: "uexp \<Rightarrow> uexp" (\<open>- _\<close> [181] 180)
  "_ue_minus"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl \<open>-\<close> 165)
  "_ue_times"  :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl \<open>*\<close> 170)
  "_ue_div"    :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixl \<open>div\<close> 170)

translations
  "_ue_num x"    => "_Numeral x"
  "_ue_size e"   => "#\<^sub>u(e)"
  "_ue_le x y"   => "x \<le>\<^sub>u y"
  "_ue_lt x y"   => "x <\<^sub>u y"
  "_ue_ge x y"   => "x \<ge>\<^sub>u y"
  "_ue_gt x y"   => "x >\<^sub>u y"
  "_ue_zero"     => "0" 
  "_ue_one"      => "1"
  "_ue_plus x y" => "x + y"
  "_ue_uminus x" => "- x"
  "_ue_minus x y" => "x - y"
  "_ue_times x y" => "x * y"
  "_ue_div x y"   => "CONST divide x y"

subsection \<open> Sets \<close>

syntax
  "_ue_empset"          :: "uexp" (\<open>{}\<close>)
  "_ue_setprod"         :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (infixr \<open>\<times>\<close> 80)
  "_ue_atLeastAtMost"   :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (\<open>(1{_.._})\<close>)
  "_ue_atLeastLessThan" :: "uexp \<Rightarrow> uexp \<Rightarrow> uexp" (\<open>(1{_..<_})\<close>)

translations
  "_ue_empset" => "{}\<^sub>u"
  "_ue_setprod e f" =>  "CONST bop (CONST Product_Type.Times) e f"
  "_ue_atLeastAtMost m n" => "{m..n}\<^sub>u"
  "_ue_atLeastLessThan m n" => "{m..<n}\<^sub>u"

subsection \<open> Imperative Program Syntax \<close>

syntax
  "_ue_if_then"    :: "uexp \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>if _ then _ else _ fi\<close>)
  "_ue_hoare"      :: "uexp \<Rightarrow> logic \<Rightarrow> uexp \<Rightarrow> logic" (\<open>{{_}} / _ / {{_}}\<close>)
  "_ue_wp"         :: "logic \<Rightarrow> uexp \<Rightarrow> uexp" (infix \<open>wp\<close> 60)

translations
  "_ue_if_then b P Q" => "P \<triangleleft> b \<triangleright>\<^sub>r Q"
  "_ue_hoare b P c" => "\<lbrace>b\<rbrace>P\<lbrace>c\<rbrace>\<^sub>u"
  "_ue_wp P b" => "P wp b"

end