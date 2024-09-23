theory utp_expr_funcs
  imports utp_expr_insts
begin

syntax \<comment> \<open> Polymorphic constructs \<close>
  "_uceil"      :: "logic \<Rightarrow> logic" (\<open>\<lceil>_\<rceil>\<^sub>u\<close>)
  "_ufloor"     :: "logic \<Rightarrow> logic" (\<open>\<lfloor>_\<rfloor>\<^sub>u\<close>)
  "_umin"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>min\<^sub>u'(_, _')\<close>)
  "_umax"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>max\<^sub>u'(_, _')\<close>)
  "_ugcd"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>gcd\<^sub>u'(_, _')\<close>)

translations
  \<comment> \<open> Type-class polymorphic constructs \<close>
  "min\<^sub>u(x, y)"  == "CONST bop (CONST min) x y"
  "max\<^sub>u(x, y)"  == "CONST bop (CONST max) x y"
  "gcd\<^sub>u(x, y)"  == "CONST bop (CONST gcd) x y"
  "\<lceil>x\<rceil>\<^sub>u" == "CONST uop CONST ceiling x"
  "\<lfloor>x\<rfloor>\<^sub>u" == "CONST uop CONST floor x"

syntax \<comment> \<open> Lists / Sequences \<close>
  "_ucons"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr \<open>#\<^sub>u\<close> 65)
  "_unil"       :: "('a list, '\<alpha>) uexpr" (\<open>\<langle>\<rangle>\<close>)
  "_ulist"      :: "args => ('a list, '\<alpha>) uexpr"    (\<open>\<langle>(_)\<rangle>\<close>)
  "_uappend"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixr \<open>^\<^sub>u\<close> 80)
  "_udconcat"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr \<open>\<^sup>\<frown>\<^sub>u\<close> 90)
  "_ulast"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" (\<open>last\<^sub>u'(_')\<close>)
  "_ufront"     :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (\<open>front\<^sub>u'(_')\<close>)
  "_uhead"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr" (\<open>head\<^sub>u'(_')\<close>)
  "_utail"      :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (\<open>tail\<^sub>u'(_')\<close>)
  "_utake"      :: "(nat, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (\<open>take\<^sub>u'(_,/ _')\<close>)
  "_udrop"      :: "(nat, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (\<open>drop\<^sub>u'(_,/ _')\<close>)
  "_ufilter"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl \<open>\<restriction>\<^sub>u\<close> 75)
  "_uextract"   :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr \<Rightarrow> ('a list, '\<alpha>) uexpr" (infixl \<open>\<upharpoonleft>\<^sub>u\<close> 75)
  "_uelems"     :: "('a list, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (\<open>elems\<^sub>u'(_')\<close>)
  "_usorted"    :: "('a list, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (\<open>sorted\<^sub>u'(_')\<close>)
  "_udistinct"  :: "('a list, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (\<open>distinct\<^sub>u'(_')\<close>)
  "_uupto"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>\<langle>_.._\<rangle>\<close>)
  "_uupt"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>\<langle>_..<_\<rangle>\<close>)
  "_umap"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>map\<^sub>u\<close>)
  "_uzip"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>zip\<^sub>u\<close>)

translations
  "x #\<^sub>u ys" == "CONST bop (#) x ys"
  "\<langle>\<rangle>"       == "\<guillemotleft>[]\<guillemotright>"
  "\<langle>x, xs\<rangle>"  == "x #\<^sub>u \<langle>xs\<rangle>"
  "\<langle>x\<rangle>"      == "x #\<^sub>u \<guillemotleft>[]\<guillemotright>"
  "x ^\<^sub>u y"   == "CONST bop (@) x y"
  "A \<^sup>\<frown>\<^sub>u B" == "CONST bop (\<^sup>\<frown>) A B"
  "last\<^sub>u(xs)" == "CONST uop CONST last xs"
  "front\<^sub>u(xs)" == "CONST uop CONST butlast xs"
  "head\<^sub>u(xs)" == "CONST uop CONST hd xs"
  "tail\<^sub>u(xs)" == "CONST uop CONST tl xs"
  "drop\<^sub>u(n,xs)" == "CONST bop CONST drop n xs"
  "take\<^sub>u(n,xs)" == "CONST bop CONST take n xs"
  "elems\<^sub>u(xs)" == "CONST uop CONST set xs"
  "sorted\<^sub>u(xs)" == "CONST uop CONST sorted xs"
  "distinct\<^sub>u(xs)" == "CONST uop CONST distinct xs"
  "xs \<restriction>\<^sub>u A"   == "CONST bop CONST seq_filter xs A"
  "A \<upharpoonleft>\<^sub>u xs"   == "CONST bop (\<upharpoonleft>\<^sub>l) A xs"
  "\<langle>n..k\<rangle>" == "CONST bop CONST upto n k"
  "\<langle>n..<k\<rangle>" == "CONST bop CONST upt n k"
  "map\<^sub>u f xs" == "CONST bop CONST map f xs"
  "zip\<^sub>u xs ys" == "CONST bop CONST zip xs ys"

syntax \<comment> \<open> Sets \<close>
  "_ufinite"    :: "logic \<Rightarrow> logic" (\<open>finite\<^sub>u'(_')\<close>)
  "_uempset"    :: "('a set, '\<alpha>) uexpr" (\<open>{}\<^sub>u\<close>)
  "_uset"       :: "args => ('a set, '\<alpha>) uexpr" (\<open>{(_)}\<^sub>u\<close>)
  "_uunion"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl \<open>\<union>\<^sub>u\<close> 65)
  "_uinter"     :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (infixl \<open>\<inter>\<^sub>u\<close> 70)
  "_uinsert"    :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>insert\<^sub>u\<close>)
  "_uimage"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>_\<lparr>_\<rparr>\<^sub>u\<close> [10,0] 10)
  "_usubset"    :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix \<open>\<subset>\<^sub>u\<close> 50)
  "_usubseteq"  :: "('a set, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr" (infix \<open>\<subseteq>\<^sub>u\<close> 50)
  "_uconverse"  :: "logic \<Rightarrow> logic" (\<open>(_\<^sup>~)\<close> [1000] 999)
  "_ucarrier"   :: "type \<Rightarrow> logic" (\<open>[_]\<^sub>T\<close>)
  "_uid"        :: "type \<Rightarrow> logic" (\<open>id[_]\<close>)
  "_uproduct"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr \<open>\<times>\<^sub>u\<close> 80)
  "_urelcomp"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixr \<open>;\<^sub>u\<close> 75)

translations
  "finite\<^sub>u(x)" == "CONST uop (CONST finite) x"
  "{}\<^sub>u"      == "\<guillemotleft>{}\<guillemotright>"
  "insert\<^sub>u x xs" == "CONST bop CONST insert x xs"
  "{x, xs}\<^sub>u" == "insert\<^sub>u x {xs}\<^sub>u"
  "{x}\<^sub>u"     == "insert\<^sub>u x \<guillemotleft>{}\<guillemotright>"
  "A \<union>\<^sub>u B"   == "CONST bop (\<union>) A B"
  "A \<inter>\<^sub>u B"   == "CONST bop (\<inter>) A B"
  "f\<lparr>A\<rparr>\<^sub>u"     == "CONST bop CONST image f A"
  "A \<subset>\<^sub>u B"   == "CONST bop (\<subset>) A B"
  "f \<subset>\<^sub>u g"   <= "CONST bop (\<subset>\<^sub>p) f g"
  "f \<subset>\<^sub>u g"   <= "CONST bop (\<subset>\<^sub>f) f g"
  "A \<subseteq>\<^sub>u B"   == "CONST bop (\<subseteq>) A B"
  "f \<subseteq>\<^sub>u g"   <= "CONST bop (\<subseteq>\<^sub>p) f g"
  "f \<subseteq>\<^sub>u g"   <= "CONST bop (\<subseteq>\<^sub>f) f g"
  "P\<^sup>~"        == "CONST uop CONST converse P"
  "['a]\<^sub>T"     == "\<guillemotleft>CONST set_of TYPE('a)\<guillemotright>"
  "id['a]"    == "\<guillemotleft>CONST Id_on (CONST set_of TYPE('a))\<guillemotright>"
  "A \<times>\<^sub>u B"    == "CONST bop CONST Product_Type.Times A B"
  "A ;\<^sub>u B"    == "CONST bop CONST relcomp A B"

syntax \<comment> \<open> Partial functions \<close>
  "_umap_plus"  :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl \<open>\<oplus>\<^sub>u\<close> 85)
  "_umap_minus" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl \<open>\<ominus>\<^sub>u\<close> 85)

translations
  "f \<oplus>\<^sub>u g"   => "(f :: ((_, _) pfun, _) uexpr) + g"
  "f \<ominus>\<^sub>u g"   => "(f :: ((_, _) pfun, _) uexpr) - g"
  
syntax \<comment> \<open> Sum types \<close>
  "_uinl"       :: "logic \<Rightarrow> logic" (\<open>inl\<^sub>u'(_')\<close>)
  "_uinr"       :: "logic \<Rightarrow> logic" (\<open>inr\<^sub>u'(_')\<close>)
  
translations
  "inl\<^sub>u(x)" == "CONST uop CONST Inl x"
  "inr\<^sub>u(x)" == "CONST uop CONST Inr x"

subsection \<open> Lifting set collectors \<close>

text \<open> We provide syntax for various types of set collectors, including intervals and the Z-style
  set comprehension which is purpose built as a new lifted definition. \<close>
  
syntax
  "_uset_atLeastAtMost" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (\<open>(1{_.._}\<^sub>u)\<close>)
  "_uset_atLeastLessThan" :: "('a, '\<alpha>) uexpr \<Rightarrow> ('a, '\<alpha>) uexpr \<Rightarrow> ('a set, '\<alpha>) uexpr" (\<open>(1{_..<_}\<^sub>u)\<close>)
  "_uset_compr" :: "pttrn \<Rightarrow> ('a set, '\<alpha>) uexpr \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('b set, '\<alpha>) uexpr" (\<open>(1{_ :/ _ |/ _ \<bullet>/ _}\<^sub>u)\<close>)
  "_uset_compr_nset" :: "pttrn \<Rightarrow> (bool, '\<alpha>) uexpr \<Rightarrow> ('b, '\<alpha>) uexpr \<Rightarrow> ('b set, '\<alpha>) uexpr" (\<open>(1{_ |/ _ \<bullet>/ _}\<^sub>u)\<close>)

lift_definition ZedSetCompr ::
  "('a set, '\<alpha>) uexpr \<Rightarrow> ('a \<Rightarrow> (bool, '\<alpha>) uexpr \<times> ('b, '\<alpha>) uexpr) \<Rightarrow> ('b set, '\<alpha>) uexpr"
is "\<lambda> A PF b. { snd (PF x) b | x. x \<in> A b \<and> fst (PF x) b}" .

translations
  "{x..y}\<^sub>u" == "CONST bop CONST atLeastAtMost x y"
  "{x..<y}\<^sub>u" == "CONST bop CONST atLeastLessThan x y"
  "{x | P \<bullet> F}\<^sub>u" == "CONST ZedSetCompr (CONST lit CONST UNIV) (\<lambda> x. (P, F))"
  "{x : A | P \<bullet> F}\<^sub>u" == "CONST ZedSetCompr A (\<lambda> x. (P, F))"

subsection \<open> Lifting limits \<close>
  
text \<open> We also lift the following functions on topological spaces for taking function limits,
  and describing continuity. \<close>

definition ulim_left :: "'a::order_topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::t2_space" where
[uexpr_defs]: "ulim_left = (\<lambda> p f. Lim (at_left p) f)"

definition ulim_right :: "'a::order_topology \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b::t2_space" where
[uexpr_defs]: "ulim_right = (\<lambda> p f. Lim (at_right p) f)"

definition ucont_on :: "('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> 'a set \<Rightarrow> bool" where
[uexpr_defs]: "ucont_on = (\<lambda> f A. continuous_on A f)"

syntax
  "_ulim_left"  :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>lim\<^sub>u'(_ \<rightarrow> _\<^sup>-')'(_')\<close>)
  "_ulim_right" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (\<open>lim\<^sub>u'(_ \<rightarrow> _\<^sup>+')'(_')\<close>)
  "_ucont_on"   :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix \<open>cont-on\<^sub>u\<close> 90)

translations
  "lim\<^sub>u(x \<rightarrow> p\<^sup>-)(e)" == "CONST bop CONST ulim_left p (\<lambda> x \<bullet> e)"
  "lim\<^sub>u(x \<rightarrow> p\<^sup>+)(e)" == "CONST bop CONST ulim_right p (\<lambda> x \<bullet> e)"
  "f cont-on\<^sub>u A"     == "CONST bop CONST continuous_on A f"

lemma uset_minus_empty [simp]: "x - {}\<^sub>u = x"
  by (simp add: uexpr_defs, transfer, simp)

lemma uinter_empty_1 [simp]: "x \<inter>\<^sub>u {}\<^sub>u = {}\<^sub>u"
  by (transfer, simp)

lemma uinter_empty_2 [simp]: "{}\<^sub>u \<inter>\<^sub>u x = {}\<^sub>u"
  by (transfer, simp)

lemma uunion_empty_1 [simp]: "{}\<^sub>u \<union>\<^sub>u x = x"
  by (transfer, simp)

lemma uunion_insert [simp]: "(bop insert x A) \<union>\<^sub>u B = bop insert x (A \<union>\<^sub>u B)"
  by (transfer, simp)

lemma ulist_filter_empty [simp]: "x \<restriction>\<^sub>u {}\<^sub>u = \<langle>\<rangle>"
  by (transfer, simp)

lemma tail_cons [simp]: "tail\<^sub>u(\<langle>x\<rangle> ^\<^sub>u xs) = xs"
  by (transfer, simp)

lemma uconcat_units [simp]: "\<langle>\<rangle> ^\<^sub>u xs = xs" "xs ^\<^sub>u \<langle>\<rangle> = xs"
  by (transfer, simp)+

end