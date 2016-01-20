chapter{*The Hereditarily Finite Sets*}

theory HF imports "~~/src/HOL/Library/Nat_Bijection"
begin

text{*From "Finite sets and Gödel's Incompleteness Theorems" by S. Swierczkowski.
      Thanks for Brian Huffman for this development, up to the cases and induct rules.*}

section {* Basic Definitions and Lemmas *}

typedef hf = "UNIV :: nat set" ..

definition hfset :: "hf \<Rightarrow> hf set"
  where "hfset a = Abs_hf ` set_decode (Rep_hf a)"

definition HF :: "hf set \<Rightarrow> hf"
  where "HF A = Abs_hf (set_encode (Rep_hf ` A))"

definition hinsert :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "hinsert a b = HF (insert a (hfset b))"

definition hmem :: "hf \<Rightarrow> hf \<Rightarrow> bool"  (infixl "\<^bold>\<in>" 50)
  where "hmem a b \<longleftrightarrow> a \<in> hfset b"

notation (ASCII)
  hmem (infixl "<:" 50)

instantiation hf :: zero
begin
  definition Zero_hf_def: "0 = HF {}"
  instance ..
end

lemma Abs_hf_0 [simp]: "Abs_hf 0 = 0"
  by (simp add: HF_def Zero_hf_def)


text {* HF Set enumerations *}

abbreviation inserthf :: "hf \<Rightarrow> hf \<Rightarrow> hf"  (infixl "\<triangleleft>" 60)
  where "y \<triangleleft> x \<equiv> hinsert x y"

syntax (ASCII)
  "_HFinset" :: "args \<Rightarrow> hf"      ("{|(_)|}")
syntax
  "_HFinset" :: "args \<Rightarrow> hf"      ("\<lbrace>_\<rbrace>")
translations
  "{|x, y|}" == "\<lbrace>y\<rbrace> \<triangleleft> x"
  "{|x|}"    == "0 \<triangleleft> x"

lemma finite_hfset [simp]: "finite (hfset a)"
  unfolding hfset_def by simp

lemma HF_hfset [simp]: "HF (hfset a) = a"
  unfolding HF_def hfset_def
  by (simp add: image_image Abs_hf_inverse Rep_hf_inverse)

lemma hfset_HF [simp]: "finite A \<Longrightarrow> hfset (HF A) = A"
  unfolding HF_def hfset_def
  by (simp add: image_image Abs_hf_inverse Rep_hf_inverse)

lemma inj_on_HF: "inj_on HF (Collect finite)"
  by (metis hfset_HF inj_onI mem_Collect_eq)

lemma hmem_hempty [simp]: "\<not> a \<^bold>\<in> 0"
  unfolding hmem_def Zero_hf_def by simp

lemmas hemptyE [elim!] = hmem_hempty [THEN notE]

lemma hmem_hinsert [iff]:
  "hmem a (c \<triangleleft>  b) \<longleftrightarrow> a = b \<or> a \<^bold>\<in> c"
  unfolding hmem_def hinsert_def by simp

lemma hf_ext: "a = b \<longleftrightarrow> (\<forall>x. x \<^bold>\<in> a \<longleftrightarrow> x \<^bold>\<in> b)"
  unfolding hmem_def set_eq_iff [symmetric]
  by (metis HF_hfset)

lemma finite_cases [consumes 1, case_names empty insert]:
  "\<lbrakk>finite F; F = {} \<Longrightarrow> P; \<And>A x. \<lbrakk>F = insert x A; x \<notin> A; finite A\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by (induct F rule: finite_induct, simp_all)

lemma hf_cases [cases type: hf, case_names 0 hinsert]:
  obtains "y = 0" | a b where "y = b \<triangleleft> a" and "\<not> a \<^bold>\<in> b"
proof -
  have "finite (hfset y)" by (rule finite_hfset)
  thus thesis
    by (metis Zero_hf_def finite_cases hf_ext hfset_HF hinsert_def hmem_def that)
qed

lemma Rep_hf_hinsert:
  "\<not> a \<^bold>\<in> b \<Longrightarrow> Rep_hf (hinsert a b) = 2 ^ (Rep_hf a) + Rep_hf b"
  unfolding hinsert_def HF_def hfset_def
  apply (simp add: image_image Abs_hf_inverse Rep_hf_inverse)
  apply (subst set_encode_insert, simp)
  apply (clarsimp simp add: hmem_def hfset_def image_def
    Rep_hf_inject [symmetric] Abs_hf_inverse, simp)
  done

lemma less_two_power: "n < 2 ^ n"
  by (induct n, auto)

section{*Verifying the Axioms of HF*}

text{*HF1*}
lemma hempty_iff: "z=0 \<longleftrightarrow> (\<forall>x. \<not> x \<^bold>\<in> z)"
  by (simp add: hf_ext)

text{*HF2*}
lemma hinsert_iff: "z = x \<triangleleft> y \<longleftrightarrow> (\<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<^bold>\<in> x | u = y)"
  by (auto simp: hf_ext)

text{*HF induction*}
lemma hf_induct [induct type: hf, case_names 0 hinsert]:
  assumes [simp]: "P 0"
                  "\<And>x y. \<lbrakk>P x; P y; \<not> x \<^bold>\<in> y\<rbrakk> \<Longrightarrow> P (y \<triangleleft> x)"
  shows "P z"
proof (induct z rule: wf_induct [where r="measure Rep_hf", OF wf_measure])
  case (1 x) show ?case
    proof (cases x rule: hf_cases)
      case 0 thus ?thesis by simp
    next
      case (hinsert a b)
      thus ?thesis using 1
        by (simp add: Rep_hf_hinsert
                      less_le_trans [OF less_two_power le_add1])
    qed
qed

text{*HF3*}
lemma hf_induct_ax: "\<lbrakk>P 0; \<forall>x. P x \<longrightarrow> (\<forall>y. P y \<longrightarrow> P (x \<triangleleft> y))\<rbrakk> \<Longrightarrow> P x"
  by (induct x, auto)

lemma hf_equalityI [intro]: "(\<And>x. x \<^bold>\<in> a \<longleftrightarrow> x \<^bold>\<in> b) \<Longrightarrow> a = b"
  by (simp add: hf_ext)

lemma hinsert_nonempty [simp]: "A \<triangleleft> a \<noteq> 0"
  by (auto simp: hf_ext)

lemma hinsert_commute: "(z \<triangleleft> y) \<triangleleft> x = (z \<triangleleft> x) \<triangleleft> y"
  by (auto simp: hf_ext)

lemma hmem_HF_iff [simp]: "x \<^bold>\<in> HF A \<longleftrightarrow> x \<in> A \<and> finite A"
  apply (cases "finite A", auto)
  apply (simp add: hmem_def)
  apply (simp add: hmem_def)
  apply (metis HF_def Rep_hf_inject Abs_hf_0 finite_imageD hempty_iff inj_onI set_encode_inf)
  done

section {* Ordered Pairs, from ZF/ZF.thy *}

lemma singleton_eq_iff [iff]: "\<lbrace>a\<rbrace> = \<lbrace>b\<rbrace> \<longleftrightarrow> a=b"
  by (metis hmem_hempty hmem_hinsert)

lemma doubleton_eq_iff: "\<lbrace>a,b\<rbrace> = \<lbrace>c,d\<rbrace> \<longleftrightarrow> (a=c & b=d) | (a=d & b=c)"
  by auto (metis hmem_hempty hmem_hinsert)+

definition hpair :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "hpair a b = \<lbrace>\<lbrace>a\<rbrace>,\<lbrace>a,b\<rbrace>\<rbrace>"

definition hfst :: "hf \<Rightarrow> hf"
  where "hfst p \<equiv> THE x. \<exists>y. p = hpair x y"

definition hsnd :: "hf \<Rightarrow> hf"
  where "hsnd p \<equiv> THE y. \<exists>x. p = hpair x y"

definition hsplit :: "[[hf, hf] \<Rightarrow> 'a, hf] \<Rightarrow> 'a::{}"  --{*for pattern-matching*}
  where "hsplit c \<equiv> %p. c (hfst p) (hsnd p)"

text {* Ordered Pairs, from ZF/ZF.thy *}

nonterminal hfs
syntax (ASCII)
  "_Tuple"    :: "[hf, hfs] \<Rightarrow> hf"              ("<(_,/ _)>")
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   ("<_,/ _>")
syntax
  ""          :: "hf \<Rightarrow> hfs"                    ("_")
  "_Enum"     :: "[hf, hfs] \<Rightarrow> hfs"             ("_,/ _")
  "_Tuple"    :: "[hf, hfs] \<Rightarrow> hf"              ("\<langle>(_,/ _)\<rangle>")
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   ("\<langle>_,/ _\<rangle>")
translations
  "<x, y, z>"    == "<x, <y, z>>"
  "<x, y>"       == "CONST hpair x y"
  "<x, y, z>"    == "<x, <y, z>>"
  "%<x,y,zs>. b" == "CONST hsplit(%x <y,zs>. b)"
  "%<x,y>. b"    == "CONST hsplit(%x y. b)"


lemma hpair_def': "hpair a b = \<lbrace>\<lbrace>a,a\<rbrace>,\<lbrace>a,b\<rbrace>\<rbrace>"
  by (auto simp: hf_ext hpair_def)

lemma hpair_iff [simp]: "hpair a b = hpair a' b' \<longleftrightarrow> a=a' & b=b'"
  by (auto simp: hpair_def' doubleton_eq_iff)

lemmas hpair_inject = hpair_iff [THEN iffD1, THEN conjE, elim!]

lemma hfst_conv [simp]: "hfst \<langle>a,b\<rangle> = a"
  by (simp add: hfst_def)

lemma hsnd_conv [simp]: "hsnd \<langle>a,b\<rangle> = b"
  by (simp add: hsnd_def)

lemma hsplit [simp]: "hsplit c \<langle>a,b\<rangle> = c a b"
  by (simp add: hsplit_def)


section{*Unions, Comprehensions, Intersections*}

subsection{*Unions*}

text{*Theorem 1.5 (Existence of the union of two sets).*}
lemma binary_union: "\<exists>z. \<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<^bold>\<in> x | u \<^bold>\<in> y"
proof (induct x rule: hf_induct)
  case 0 thus ?case by auto
next
  case (hinsert a b) thus ?case by (metis hmem_hinsert)
qed

text{*Theorem 1.6 (Existence of the union of a set of sets).*}
lemma union_of_set: "\<exists>z. \<forall>u. u \<^bold>\<in> z \<longleftrightarrow> (\<exists>y. y \<^bold>\<in> x & u \<^bold>\<in> y)"
proof (induct x rule: hf_induct)
  case 0 thus ?case by (metis hmem_hempty)
next
  case (hinsert a b)
  then show ?case
    by (metis hmem_hinsert binary_union [of a])
qed

subsection {* Set comprehensions *}

text{*Theorem 1.7, comprehension scheme*}
lemma comprehension: "\<exists>z. \<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<^bold>\<in> x & P u"
proof (induct x rule: hf_induct)
  case 0 thus ?case by (metis hmem_hempty)
next
  case (hinsert a b) thus ?case by (metis hmem_hinsert)
qed

definition HCollect :: "(hf \<Rightarrow> bool) \<Rightarrow> hf \<Rightarrow> hf" -- "comprehension"
  where "HCollect P A = (THE z. \<forall>u. u \<^bold>\<in> z = (P u & u \<^bold>\<in> A))"

syntax (ASCII)
  "_HCollect" :: "idt \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> hf"    ("(1\<lbrace>_ <:/ _./ _\<rbrace>)")
syntax
  "_HCollect" :: "idt \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> hf"    ("(1\<lbrace>_ \<^bold>\<in>/ _./ _\<rbrace>)")
translations
  "\<lbrace>x <: A. P\<rbrace>" == "CONST HCollect (%x. P) A"

lemma HCollect_iff [iff]: "hmem x (HCollect P A) \<longleftrightarrow> P x & x \<^bold>\<in> A"
apply (insert comprehension [of A P], clarify)
apply (simp add: HCollect_def)
apply (rule theI2, blast)
apply (auto simp: hf_ext)
done

lemma HCollectI: "a \<^bold>\<in> A \<Longrightarrow> P a \<Longrightarrow> hmem a \<lbrace>x \<^bold>\<in> A. P x\<rbrace>"
  by simp

lemma HCollectE:
  assumes "a \<^bold>\<in> \<lbrace>x \<^bold>\<in> A. P x\<rbrace>" obtains "a \<^bold>\<in> A" "P a"
  using assms by auto

lemma HCollect_hempty [simp]: "HCollect P 0 = 0"
  by (simp add: hf_ext)

subsection{*Union operators*}

instantiation hf :: sup
begin
  definition "sup a b = (THE z. \<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<^bold>\<in> a | u \<^bold>\<in> b)"
  instance ..
end

abbreviation hunion :: "hf \<Rightarrow> hf \<Rightarrow> hf" (infixl "\<squnion>" 65) where
  "hunion \<equiv> sup"

lemma hunion_iff [iff]: "hmem x (a \<squnion> b) \<longleftrightarrow> x \<^bold>\<in> a | x \<^bold>\<in> b"
apply (insert binary_union [of a b], clarify)
apply (simp add: sup_hf_def)
apply (rule theI2)
apply (auto simp: hf_ext)
done

definition HUnion :: "hf \<Rightarrow> hf"        ("\<Squnion>_" [900] 900)
  where "HUnion A = (THE z. \<forall>u. u \<^bold>\<in> z \<longleftrightarrow> (\<exists>y. y \<^bold>\<in> A & u \<^bold>\<in> y))"

lemma HUnion_iff [iff]: "hmem x (\<Squnion> A) \<longleftrightarrow> (\<exists>y. y \<^bold>\<in> A & x \<^bold>\<in> y)"
apply (insert union_of_set [of A], clarify)
apply (simp add: HUnion_def)
apply (rule theI2)
apply (auto simp: hf_ext)
done

lemma HUnion_hempty [simp]: "\<Squnion> 0 = 0"
  by (simp add: hf_ext)

lemma HUnion_hinsert [simp]: "\<Squnion>(A \<triangleleft> a) = a \<squnion> \<Squnion>A"
  by (auto simp: hf_ext)

lemma HUnion_hunion [simp]: "\<Squnion>(A \<squnion> B) =  \<Squnion>A \<squnion> \<Squnion>B"
  by blast

subsection{*Definition 1.8, Intersections*}

instantiation hf :: inf
begin
  definition "inf a b = \<lbrace>x \<^bold>\<in> a. x \<^bold>\<in> b\<rbrace>"
  instance ..
end

abbreviation hinter :: "hf \<Rightarrow> hf \<Rightarrow> hf" (infixl "\<sqinter>" 70) where
  "hinter \<equiv> inf"

lemma hinter_iff [iff]: "hmem u (x \<sqinter> y) \<longleftrightarrow> u \<^bold>\<in> x & u \<^bold>\<in> y"
  by (metis HCollect_iff inf_hf_def)

definition HInter :: "hf \<Rightarrow> hf"           ("\<Sqinter>_" [900] 900)
  where "HInter(A) = \<lbrace>x \<^bold>\<in> HUnion(A). \<forall>y. y \<^bold>\<in> A \<longrightarrow> x \<^bold>\<in> y\<rbrace>"

lemma HInter_hempty [iff]: "\<Sqinter> 0 = 0"
  by (metis HCollect_hempty HUnion_hempty HInter_def)

lemma HInter_iff [simp]: "A\<noteq>0 \<Longrightarrow> hmem x (\<Sqinter> A) \<longleftrightarrow> (\<forall>y. y \<^bold>\<in> A \<longrightarrow> x \<^bold>\<in> y)"
  by (auto simp: HInter_def)

lemma HInter_hinsert [simp]: "A\<noteq>0 \<Longrightarrow> \<Sqinter>(A \<triangleleft> a) = a \<sqinter> \<Sqinter>A"
  by (auto simp: hf_ext HInter_iff [OF hinsert_nonempty])

subsection{*Set Difference*}

instantiation hf :: minus
begin
  definition "A - B = \<lbrace>x \<^bold>\<in> A. \<not> x \<^bold>\<in> B\<rbrace>"
  instance ..
end

lemma hdiff_iff [iff]: "hmem u (x - y) \<longleftrightarrow> u \<^bold>\<in> x & \<not> u \<^bold>\<in> y"
  by (auto simp: minus_hf_def)

lemma hdiff_zero [simp]: fixes x :: hf shows "(x - 0) = x"
  by blast

lemma zero_hdiff [simp]: fixes x :: hf shows "(0 - x) = 0"
  by blast

lemma hdiff_insert: "A - (B \<triangleleft> a) = A - B - \<lbrace>a\<rbrace>"
  by blast

lemma hinsert_hdiff_if:
  "(A \<triangleleft> x) - B = (if x \<^bold>\<in> B then A - B else (A - B) \<triangleleft> x)"
  by auto


section{*Replacement*}

text{*Theorem 1.9 (Replacement Scheme).*}
lemma replacement:
  "(\<forall>u v v'. u \<^bold>\<in> x \<longrightarrow> R u v \<longrightarrow> R u v' \<longrightarrow> v'=v) \<Longrightarrow> \<exists>z. \<forall>v. v \<^bold>\<in> z \<longleftrightarrow> (\<exists>u. u \<^bold>\<in> x & R u v)"
proof (induct x rule: hf_induct)
  case 0 thus ?case
    by (metis hmem_hempty)
next
  case (hinsert a b) thus ?case
    by simp (metis hmem_hinsert)
qed

lemma replacement_fun: "\<exists>z. \<forall>v. v \<^bold>\<in> z \<longleftrightarrow> (\<exists>u. u \<^bold>\<in> x & v = f u)"
  by (rule replacement [where R = "\<lambda>u v. v = f u"]) auto

definition PrimReplace :: "hf \<Rightarrow> (hf \<Rightarrow> hf \<Rightarrow> bool) \<Rightarrow> hf"
  where "PrimReplace A R = (THE z. \<forall>v. v \<^bold>\<in> z \<longleftrightarrow> (\<exists>u. u \<^bold>\<in> A & R u v))"

definition Replace :: "hf \<Rightarrow> (hf \<Rightarrow> hf \<Rightarrow> bool) \<Rightarrow> hf"
  where "Replace A R = PrimReplace A (\<lambda>x y. (\<exists>!z. R x z) & R x y)"

definition RepFun :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf"
  where "RepFun A f = Replace A (\<lambda>x y. y = f x)"


syntax (ASCII)
  "_HReplace"  :: "[pttrn, pttrn, hf, bool] \<Rightarrow> hf" ("(1{|_ ./ _<: _, _|})")
  "_HRepFun"   :: "[hf, pttrn, hf] \<Rightarrow> hf"          ("(1{|_ ./ _<: _|})" [51,0,51])
  "_HINTER"    :: "[pttrn, hf, hf] \<Rightarrow> hf"          ("(3INT _<:_./ _)" 10)
  "_HUNION"    :: "[pttrn, hf, hf] \<Rightarrow> hf"          ("(3UN _<:_./ _)" 10)
syntax
  "_HReplace"  :: "[pttrn, pttrn, hf, bool] \<Rightarrow> hf" ("(1\<lbrace>_ ./ _ \<^bold>\<in> _, _\<rbrace>)")
  "_HRepFun"   :: "[hf, pttrn, hf] \<Rightarrow> hf"          ("(1\<lbrace>_ ./ _ \<^bold>\<in> _\<rbrace>)" [51,0,51])
  "_HUNION"    :: "[pttrn, hf, hf] \<Rightarrow> hf"          ("(3\<Squnion>_\<^bold>\<in>_./ _)" 10)
  "_HINTER"    :: "[pttrn, hf, hf] \<Rightarrow> hf"          ("(3\<Sqinter>_\<^bold>\<in>_./ _)" 10)
translations
  "{|y. x<:A, Q|}" == "CONST Replace A (%x y. Q)"
  "{|b. x<:A|}"    == "CONST RepFun A (%x. b)"
  "INT x<:A. B"    == "CONST HInter(CONST RepFun A (%x. B))"
  "UN x<:A. B"     == "CONST HUnion(CONST RepFun A (%x. B))"

lemma PrimReplace_iff:
  assumes sv: "\<forall>u v v'. u \<^bold>\<in> A \<longrightarrow> R u v \<longrightarrow> R u v' \<longrightarrow> v'=v"
  shows "v \<^bold>\<in> (PrimReplace A R) \<longleftrightarrow> (\<exists>u. u \<^bold>\<in> A & R u v)"
apply (insert replacement [OF sv], clarify)
apply (simp add: PrimReplace_def)
apply (rule theI2)
apply (auto simp: hf_ext)
done

lemma Replace_iff [iff]:
  "v \<^bold>\<in> Replace A R \<longleftrightarrow> (\<exists>u. u \<^bold>\<in> A & R u v & (\<forall>y. R u y \<longrightarrow> y=v))"
apply (simp add: Replace_def)
apply (subst PrimReplace_iff, auto)
done

lemma Replace_0 [simp]: "Replace 0 R = 0"
  by blast

lemma Replace_hunion [simp]: "Replace (A \<squnion> B) R = Replace A R  \<squnion>  Replace B R"
  by blast

lemma Replace_cong [cong]:
    "\<lbrakk> A=B;  !!x y. x \<^bold>\<in> B \<Longrightarrow> P x y \<longleftrightarrow> Q x y \<rbrakk>  \<Longrightarrow> Replace A P = Replace B Q"
  by (simp add: hf_ext cong: conj_cong)

lemma RepFun_iff [iff]: "v \<^bold>\<in> (RepFun A f) \<longleftrightarrow> (\<exists>u. u \<^bold>\<in> A & v = f u)"
  by (auto simp: RepFun_def)

lemma RepFun_cong [cong]:
    "\<lbrakk> A=B;  !!x. x \<^bold>\<in> B \<Longrightarrow> f(x)=g(x) \<rbrakk>  \<Longrightarrow> RepFun A f = RepFun B g"
by (simp add: RepFun_def)

lemma triv_RepFun [simp]: "RepFun A (\<lambda>x. x) = A"
by blast

lemma RepFun_0 [simp]: "RepFun 0 f = 0"
  by blast

lemma RepFun_hinsert [simp]: "RepFun (hinsert a b) f = hinsert (f a) (RepFun b f)"
  by blast

lemma RepFun_hunion [simp]:
  "RepFun (A \<squnion> B) f = RepFun A f  \<squnion>  RepFun B f"
  by blast

lemma HF_HUnion: "\<lbrakk>finite A; \<And>x. x\<in>A \<Longrightarrow> finite (B x)\<rbrakk> \<Longrightarrow> HF (\<Union>x \<in> A. B x) = (\<Squnion>x\<^bold>\<in>HF A. HF (B x))"
  by (rule hf_equalityI) (auto)


section{*Subset relation and the Lattice Properties*}

text{*Definition 1.10 (Subset relation).*}
instantiation hf :: order
begin
  definition less_eq_hf where "A \<le> B \<longleftrightarrow> (\<forall>x. x \<^bold>\<in> A \<longrightarrow> x \<^bold>\<in> B)"

  definition less_hf    where "A < B \<longleftrightarrow> A \<le> B \<and> A \<noteq> (B::hf)"

  instance by standard (auto simp: less_eq_hf_def less_hf_def)
end

subsection{*Rules for subsets*}

lemma hsubsetI [intro!]:
    "(!!x. x\<^bold>\<in>A \<Longrightarrow> x\<^bold>\<in>B) \<Longrightarrow> A \<le> B"
  by (simp add: less_eq_hf_def)

text{*Classical elimination rule*}
lemma hsubsetCE [elim]: "\<lbrakk> A \<le> B;  ~(c\<^bold>\<in>A) \<Longrightarrow> P;  c\<^bold>\<in>B \<Longrightarrow> P \<rbrakk>  \<Longrightarrow> P"
  by (auto simp: less_eq_hf_def)

text{*Rule in Modus Ponens style*}
lemma hsubsetD [elim]: "\<lbrakk> A \<le> B;  c\<^bold>\<in>A \<rbrakk> \<Longrightarrow> c\<^bold>\<in>B"
  by (simp add: less_eq_hf_def)

text{*Sometimes useful with premises in this order*}
lemma rev_hsubsetD: "\<lbrakk> c\<^bold>\<in>A; A\<le>B \<rbrakk> \<Longrightarrow> c\<^bold>\<in>B"
  by blast

lemma contra_hsubsetD: "\<lbrakk> A \<le> B; c \<notin> B \<rbrakk>  \<Longrightarrow> c \<notin> A"
  by blast

lemma rev_contra_hsubsetD: "\<lbrakk> c \<notin> B;  A \<le> B \<rbrakk>  \<Longrightarrow> c \<notin> A"
  by blast

lemma hf_equalityE:
  fixes A :: hf shows "A = B \<Longrightarrow> (A \<le> B \<Longrightarrow> B \<le> A \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis order_refl)


subsection{*Lattice properties*}

instantiation hf :: distrib_lattice
begin
  instance by standard (auto simp: less_eq_hf_def less_hf_def inf_hf_def)
end

instantiation hf :: bounded_lattice_bot
begin
  definition "bot = (0::hf)"
  instance by standard (auto simp: less_eq_hf_def bot_hf_def)
end

lemma hinter_hempty_left [simp]: "0 \<sqinter> A = 0"
  by (metis bot_hf_def inf_bot_left)

lemma hinter_hempty_right [simp]: "A \<sqinter> 0 = 0"
  by (metis bot_hf_def inf_bot_right)

lemma hunion_hempty_left [simp]: "0 \<squnion> A = A"
  by (metis bot_hf_def sup_bot_left)

lemma hunion_hempty_right [simp]: "A \<squnion> 0 = A"
  by (metis bot_hf_def sup_bot_right)

lemma less_eq_hempty [simp]: "u \<le> 0 \<longleftrightarrow> u = (0::hf)"
  by (metis hempty_iff less_eq_hf_def)

lemma less_eq_insert1_iff [iff]: "(hinsert x y) \<le> z \<longleftrightarrow> x \<^bold>\<in> z & y \<le> z"
  by (auto simp: less_eq_hf_def)

lemma less_eq_insert2_iff:
  "z \<le> (hinsert x y) \<longleftrightarrow> z \<le> y \<or> (\<exists>u. hinsert x u = z \<and> ~ x \<^bold>\<in> u \<and> u \<le> y)"
proof (cases "x \<^bold>\<in> z")
  case True
  hence u: "hinsert x (z - \<lbrace>x\<rbrace>) = z" by auto
  show ?thesis
    proof
      assume "z \<le> (hinsert x y)"
      thus "z \<le> y \<or> (\<exists>u. hinsert x u = z \<and> \<not> x \<^bold>\<in> u \<and> u \<le> y)"
        by (simp add: less_eq_hf_def) (metis u hdiff_iff hmem_hinsert)
    next
      assume "z \<le> y \<or> (\<exists>u. hinsert x u = z \<and> \<not> x \<^bold>\<in> u \<and> u \<le> y)"
      thus "z \<le> (hinsert x y)"
        by (auto simp: less_eq_hf_def)
    qed
next
  case False thus ?thesis
    by (metis hmem_hinsert less_eq_hf_def)
qed

lemma zero_le [simp]: "0 \<le> (x::hf)"
  by blast

lemma hinsert_eq_sup: "b \<triangleleft> a = b \<squnion> \<lbrace>a\<rbrace>"
  by blast

lemma hunion_hinsert_left: "hinsert x A \<squnion> B = hinsert x (A \<squnion> B)"
  by blast

lemma hunion_hinsert_right: "B \<squnion> hinsert x A = hinsert x (B \<squnion> A)"
  by blast

lemma hinter_hinsert_left: "hinsert x A \<sqinter> B = (if x \<^bold>\<in> B then hinsert x (A \<sqinter> B) else A \<sqinter> B)"
  by auto

lemma hinter_hinsert_right: "B \<sqinter> hinsert x A = (if x \<^bold>\<in> B then hinsert x (B \<sqinter> A) else B \<sqinter> A)"
  by auto


section{*Foundation, Cardinality, Powersets*}

subsection{*Foundation*}

text{*Theorem 1.13: Foundation (Regularity) Property.*}
lemma foundation:
  assumes z: "z \<noteq> 0" shows "\<exists>w. w \<^bold>\<in> z & w \<sqinter> z = 0"
proof -
  { fix x
    assume z: "(\<forall>w. w \<^bold>\<in> z \<longrightarrow> w \<sqinter> z \<noteq> 0)"
    have "~ x \<^bold>\<in> z \<and> x \<sqinter> z = 0"
    proof (induction x rule: hf_induct)
      case 0 thus ?case
        by (metis hinter_hempty_left z)
    next
      case (hinsert x y) thus ?case
        by (metis hinter_hinsert_left z)
    qed
  }
  thus ?thesis using z
    by (metis z hempty_iff)
qed

lemma hmem_not_refl: "~ (x \<^bold>\<in> x)"
  using foundation [of "\<lbrace>x\<rbrace>"]
  by (metis hinter_iff hmem_hempty hmem_hinsert)

lemma hmem_not_sym: "~ (x \<^bold>\<in> y \<and> y \<^bold>\<in> x)"
  using foundation [of "\<lbrace>x,y\<rbrace>"]
  by (metis hinter_iff hmem_hempty hmem_hinsert)

lemma hmem_ne: "x \<^bold>\<in> y \<Longrightarrow> x \<noteq> y"
  by (metis hmem_not_refl)

lemma hmem_Sup_ne: "x <: y \<Longrightarrow> \<Squnion>x \<noteq> y"
  by (metis HUnion_iff hmem_not_sym)

lemma hpair_neq_fst: "\<langle>a,b\<rangle> \<noteq> a"
  by (metis hpair_def hinsert_iff hmem_not_sym)

lemma hpair_neq_snd: "\<langle>a,b\<rangle> \<noteq> b"
  by (metis hpair_def hinsert_iff hmem_not_sym)

lemma hpair_nonzero [simp]: "\<langle>x,y\<rangle> \<noteq> 0"
  by (auto simp: hpair_def)

lemma zero_notin_hpair: "~ 0 \<^bold>\<in> \<langle>x,y\<rangle>"
  by (auto simp: hpair_def)


subsection{*Cardinality*}

text{*First we need to hack the underlying representation*}
lemma hfset_0 [simp]: "hfset 0 = {}"
  by (metis Zero_hf_def finite.emptyI hfset_HF)

lemma hfset_hinsert: "hfset (b \<triangleleft> a) = insert a (hfset b)"
  by (metis finite_insert hinsert_def HF.finite_hfset hfset_HF)

lemma hfset_hdiff: "hfset (x - y) = hfset x - hfset y"
proof (induct x arbitrary: y rule: hf_induct)
  case 0 thus ?case
    by simp
next
  case (hinsert a b) thus ?case
    by (simp add: hfset_hinsert Set.insert_Diff_if hinsert_hdiff_if hmem_def)
qed

definition hcard :: "hf \<Rightarrow> nat"
  where "hcard x = card (hfset x)"

lemma hcard_0 [simp]: "hcard 0 = 0"
  by (simp add: hcard_def)

lemma hcard_hinsert_if: "hcard (hinsert x y) = (if x \<^bold>\<in> y then hcard y else Suc (hcard y))"
  by (simp add: hcard_def hfset_hinsert card_insert_if hmem_def)

lemma hcard_union_inter: "hcard (x \<squnion> y) + hcard (x \<sqinter> y) = hcard x + hcard y"
  apply (induct x arbitrary: y rule: hf_induct)
  apply (auto simp: hcard_hinsert_if hunion_hinsert_left hinter_hinsert_left)
  done

lemma hcard_hdiff1_less: "x \<^bold>\<in> z \<Longrightarrow> hcard (z - \<lbrace>x\<rbrace>) < hcard z"
  by (simp add: hcard_def hfset_hdiff hfset_hinsert)
     (metis card_Diff1_less finite_hfset hmem_def)

subsection{*Powerset Operator*}

text{*Theorem 1.11 (Existence of the power set).*}
lemma powerset: "\<exists>z. \<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<le> x"
proof (induction x rule: hf_induct)
 case 0 thus ?case
    by (metis hmem_hempty hmem_hinsert less_eq_hempty)
next
  case (hinsert a b)
  then obtain Pb where Pb: "\<forall>u. u \<^bold>\<in> Pb \<longleftrightarrow> u \<le> b"
    by auto
  obtain RPb where RPb: "\<forall>v. v \<^bold>\<in> RPb \<longleftrightarrow> (\<exists>u. u \<^bold>\<in> Pb & v = hinsert a u)"
    using replacement_fun ..
  thus ?case using Pb binary_union [of Pb RPb]
    apply (simp add: less_eq_insert2_iff, clarify)
    apply (rule_tac x=z in exI)
    apply (metis hinsert.hyps less_eq_hf_def)
    done
qed

definition HPow :: "hf \<Rightarrow> hf"
  where "HPow x = (THE z. \<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<le> x)"

lemma HPow_iff [iff]: "u \<^bold>\<in> HPow x \<longleftrightarrow> u \<le> x"
apply (insert powerset [of x], clarify)
apply (simp add: HPow_def)
apply (rule theI2)
apply (auto simp: hf_ext)
done

lemma HPow_mono: "x \<le> y \<Longrightarrow> HPow x \<le> HPow y"
  by (metis HPow_iff less_eq_hf_def order_trans)

lemma HPow_mono_strict: "x < y \<Longrightarrow> HPow x < HPow y"
  by (metis HPow_iff HPow_mono less_le_not_le order_eq_iff)

lemma HPow_mono_iff [simp]: "HPow x \<le> HPow y \<longleftrightarrow> x \<le> y"
  by (metis HPow_iff HPow_mono hsubsetCE order_refl)

lemma HPow_mono_strict_iff [simp]: "HPow x < HPow y \<longleftrightarrow> x < y"
  by (metis HPow_mono_iff less_le_not_le)


section{*Bounded Quantifiers*}

definition HBall :: "hf \<Rightarrow> (hf \<Rightarrow> bool) \<Rightarrow> bool" where
  "HBall A P \<longleftrightarrow> (\<forall>x. x <: A \<longrightarrow> P x)"   -- "bounded universal quantifiers"

definition HBex :: "hf \<Rightarrow> (hf \<Rightarrow> bool) \<Rightarrow> bool" where
  "HBex A P \<longleftrightarrow> (\<exists>x. x <: A \<and> P x)"   -- "bounded existential quantifiers"

syntax (ASCII)
  "_HBall"       :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3ALL _<:_./ _)" [0, 0, 10] 10)
  "_HBex"        :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX _<:_./ _)"  [0, 0, 10] 10)
  "_HBex1"       :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX! _<:_./ _)" [0, 0, 10] 10)
syntax
  "_HBall"       :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>_\<^bold>\<in>_./ _)"  [0, 0, 10] 10)
  "_HBex"        :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>_\<^bold>\<in>_./ _)"  [0, 0, 10] 10)
  "_HBex1"       :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>!_\<^bold>\<in>_./ _)" [0, 0, 10] 10)
translations
  "ALL x<:A. P" == "CONST HBall A (%x. P)"
  "EX x<:A. P" == "CONST HBex A (%x. P)"
  "EX! x<:A. P" => "EX! x. x:A & P"

lemma hball_cong [cong]:
    "\<lbrakk> A=A';  !!x. x \<^bold>\<in> A' \<Longrightarrow> P(x) \<longleftrightarrow> P'(x) \<rbrakk>  \<Longrightarrow> (\<forall>x\<^bold>\<in>A. P(x)) \<longleftrightarrow> (\<forall>x\<^bold>\<in>A'. P'(x))"
  by (simp add: HBall_def)

lemma hballI [intro!]: "(!!x. x<:A \<Longrightarrow> P x) \<Longrightarrow> ALL x<:A. P x"
  by (simp add: HBall_def)

lemma hbspec [dest?]: "ALL x<:A. P x \<Longrightarrow> x<:A \<Longrightarrow> P x"
  by (simp add: HBall_def)

lemma hballE [elim]: "ALL x<:A. P x \<Longrightarrow> (P x \<Longrightarrow> Q) \<Longrightarrow> (~ x <: A \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (unfold HBall_def) blast

lemma hbex_cong [cong]:
    "\<lbrakk> A=A';  !!x. x \<^bold>\<in> A' \<Longrightarrow> P(x) \<longleftrightarrow> P'(x) \<rbrakk>  \<Longrightarrow> (\<exists>x\<^bold>\<in>A. P(x)) \<longleftrightarrow> (\<exists>x\<^bold>\<in>A'. P'(x))"
  by (simp add: HBex_def cong: conj_cong)

lemma hbexI [intro]: "P x \<Longrightarrow> x<:A \<Longrightarrow> EX x<:A. P x"
  by (unfold HBex_def) blast

lemma rev_hbexI [intro?]: "x<:A \<Longrightarrow> P x \<Longrightarrow> EX x<:A. P x"
  by (unfold HBex_def) blast

lemma bexCI: "(ALL x<:A. ~P x \<Longrightarrow> P a) \<Longrightarrow> a<:A \<Longrightarrow> EX x<:A. P x"
  by (unfold HBex_def) blast

lemma hbexE [elim!]: "EX x<:A. P x \<Longrightarrow> (!!x. x<:A \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (unfold HBex_def) blast

lemma hball_triv [simp]: "(ALL x<:A. P) = ((EX x. x<:A) --> P)"
  -- {* Trival rewrite rule. *}
  by (simp add: HBall_def)

lemma hbex_triv [simp]: "(EX x<:A. P) = ((EX x. x<:A) & P)"
  -- {* Dual form for existentials. *}
  by (simp add: HBex_def)

lemma hbex_triv_one_point1 [simp]: "(EX x<:A. x = a) = (a<:A)"
  by blast

lemma hbex_triv_one_point2 [simp]: "(EX x<:A. a = x) = (a<:A)"
  by blast

lemma hbex_one_point1 [simp]: "(EX x<:A. x = a & P x) = (a<:A & P a)"
  by blast

lemma hbex_one_point2 [simp]: "(EX x<:A. a = x & P x) = (a<:A & P a)"
  by blast

lemma hball_one_point1 [simp]: "(ALL x<:A. x = a --> P x) = (a<:A --> P a)"
  by blast

lemma hball_one_point2 [simp]: "(ALL x<:A. a = x --> P x) = (a<:A --> P a)"
  by blast

lemma hball_conj_distrib:
  "(\<forall>x\<^bold>\<in>A. P x \<and> Q x) \<longleftrightarrow> ((\<forall>x\<^bold>\<in>A. P x) \<and> (\<forall>x\<^bold>\<in>A. Q x))"
  by blast

lemma hbex_disj_distrib:
  "(\<exists>x\<^bold>\<in>A. P x \<or> Q x) \<longleftrightarrow> ((\<exists>x\<^bold>\<in>A. P x) \<or> (\<exists>x\<^bold>\<in>A. Q x))"
  by blast

lemma hb_all_simps [simp, no_atp]:
  "\<And>A P Q. (\<forall>x \<^bold>\<in> A. P x \<or> Q) \<longleftrightarrow> ((\<forall>x \<^bold>\<in> A. P x) \<or> Q)"
  "\<And>A P Q. (\<forall>x \<^bold>\<in> A. P \<or> Q x) \<longleftrightarrow> (P \<or> (\<forall>x \<^bold>\<in> A. Q x))"
  "\<And>A P Q. (\<forall>x \<^bold>\<in> A. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x \<^bold>\<in> A. Q x))"
  "\<And>A P Q. (\<forall>x \<^bold>\<in> A. P x \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x \<^bold>\<in> A. P x) \<longrightarrow> Q)"
  "\<And>P. (\<forall>x \<^bold>\<in> 0. P x) \<longleftrightarrow> True"
  "\<And>a B P. (\<forall>x \<^bold>\<in> B \<triangleleft> a. P x) \<longleftrightarrow> (P a \<and> (\<forall>x \<^bold>\<in> B. P x))"
  "\<And>P Q. (\<forall>x \<^bold>\<in> HCollect Q A. P x) \<longleftrightarrow> (\<forall>x \<^bold>\<in> A. Q x \<longrightarrow> P x)"
  "\<And>A P. (\<not> (\<forall>x \<^bold>\<in> A. P x)) \<longleftrightarrow> (\<exists>x \<^bold>\<in> A. \<not> P x)"
  by auto

lemma hb_ex_simps [simp, no_atp]:
  "\<And>A P Q. (\<exists>x \<^bold>\<in> A. P x \<and> Q) \<longleftrightarrow> ((\<exists>x \<^bold>\<in> A. P x) \<and> Q)"
  "\<And>A P Q. (\<exists>x \<^bold>\<in> A. P \<and> Q x) \<longleftrightarrow> (P \<and> (\<exists>x \<^bold>\<in> A. Q x))"
  "\<And>P. (\<exists>x \<^bold>\<in> 0. P x) \<longleftrightarrow> False"
  "\<And>a B P. (\<exists>x \<^bold>\<in> B \<triangleleft> a. P x) \<longleftrightarrow> (P a | (\<exists>x \<^bold>\<in> B. P x))"
  "\<And>P Q. (\<exists>x \<^bold>\<in> HCollect Q A. P x) \<longleftrightarrow> (\<exists>x \<^bold>\<in> A. Q x \<and> P x)"
  "\<And>A P. (\<not>(\<exists>x \<^bold>\<in> A. P x)) \<longleftrightarrow> (\<forall>x \<^bold>\<in> A. \<not> P x)"
  by auto

lemma le_HCollect_iff: "A \<le> \<lbrace>x \<^bold>\<in> B. P x\<rbrace> \<longleftrightarrow> A \<le> B \<and> (\<forall>x \<^bold>\<in> A. P x)"
  by blast

section{*Relations and Functions*}

definition is_hpair :: "hf \<Rightarrow> bool"
  where "is_hpair z = (\<exists>x y. z = \<langle>x,y\<rangle>)"

definition hconverse :: "hf \<Rightarrow> hf"
  where "hconverse(r) = \<lbrace>z. w \<^bold>\<in> r, \<exists>x y. w = \<langle>x,y\<rangle> & z = \<langle>y,x\<rangle>\<rbrace>"

definition hdomain :: "hf \<Rightarrow> hf"
  where "hdomain(r) = \<lbrace>x. w \<^bold>\<in> r, \<exists>y. w = \<langle>x,y\<rangle>\<rbrace>"

definition hrange :: "hf \<Rightarrow> hf"
  where "hrange(r) = hdomain(hconverse(r))"

definition hrelation :: "hf \<Rightarrow> bool"
  where "hrelation(r) = (\<forall>z. z \<^bold>\<in> r \<longrightarrow> is_hpair z)"

definition hrestrict :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  --{* Restrict the relation r to the domain A *}
  where "hrestrict r A = \<lbrace>z \<^bold>\<in> r. \<exists>x \<^bold>\<in> A. \<exists>y. z = \<langle>x,y\<rangle>\<rbrace>"

definition nonrestrict :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "nonrestrict r A = \<lbrace>z \<^bold>\<in> r. \<forall>x \<^bold>\<in> A. \<forall>y. z \<noteq> \<langle>x,y\<rangle>\<rbrace>"

definition hfunction :: "hf \<Rightarrow> bool"
  where "hfunction(r) = (\<forall>x y. \<langle>x,y\<rangle> \<^bold>\<in> r \<longrightarrow> (\<forall>y'. \<langle>x,y'\<rangle> \<^bold>\<in> r \<longrightarrow> y=y'))"

definition app :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "app f x = (THE y. \<langle>x, y\<rangle> \<^bold>\<in> f)"

lemma hrestrict_iff [iff]:
    "z \<^bold>\<in> hrestrict r A \<longleftrightarrow> z \<^bold>\<in> r & (\<exists> x y. z = \<langle>x, y\<rangle> & x \<^bold>\<in> A)"
  by (auto simp: hrestrict_def)

lemma hrelation_0 [simp]: "hrelation 0"
  by (force simp add: hrelation_def)

lemma hrelation_restr [iff]: "hrelation (hrestrict r x)"
  by (metis hrelation_def hrestrict_iff is_hpair_def)

lemma hrelation_hunion [simp]: "hrelation (f \<squnion> g) \<longleftrightarrow> hrelation f \<and> hrelation g"
  by (auto simp: hrelation_def)

lemma hfunction_restr: "hfunction r \<Longrightarrow> hfunction (hrestrict r x)"
  by (auto simp: hfunction_def hrestrict_def)

lemma hdomain_restr [simp]: "hdomain (hrestrict r x) = hdomain r \<sqinter> x"
  by (force simp add: hdomain_def hrestrict_def)

lemma hdomain_0 [simp]: "hdomain 0 = 0"
  by (force simp add: hdomain_def)

lemma hdomain_ins [simp]: "hdomain (r \<triangleleft> \<langle>x, y\<rangle>) = hdomain r \<triangleleft> x"
  by (force simp add: hdomain_def)

lemma hdomain_hunion [simp]: "hdomain (f \<squnion> g) = hdomain f \<squnion> hdomain g"
  by (simp add: hdomain_def)

lemma hdomain_not_mem [iff]: "\<not> \<langle>hdomain r, a\<rangle> \<^bold>\<in> r"
  by (metis hdomain_ins hinter_hinsert_right hmem_hinsert hmem_not_refl
            hunion_hinsert_right sup_inf_absorb)

lemma app_singleton [simp]: "app \<lbrace>\<langle>x, y\<rangle>\<rbrace> x = y"
  by (simp add: app_def)

lemma app_equality: "hfunction f \<Longrightarrow> \<langle>x, y\<rangle> <: f \<Longrightarrow> app f x = y"
  by (auto simp: app_def hfunction_def intro: the1I2)

lemma app_ins2: "x' \<noteq> x \<Longrightarrow> app (f \<triangleleft> \<langle>x, y\<rangle>) x' = app f x'"
  by (simp add: app_def)

lemma hfunction_0 [simp]: "hfunction 0"
  by (force simp add: hfunction_def)

lemma hfunction_ins: "hfunction f \<Longrightarrow> ~ x <: hdomain f \<Longrightarrow> hfunction (f\<triangleleft> \<langle>x, y\<rangle>)"
  by (auto simp: hfunction_def hdomain_def)

lemma hdomainI: "\<langle>x, y\<rangle> \<^bold>\<in> f \<Longrightarrow> x \<^bold>\<in> hdomain f"
  by (auto simp: hdomain_def)

lemma hfunction_hunion: "hdomain f \<sqinter> hdomain g = 0
            \<Longrightarrow> hfunction (f \<squnion> g) \<longleftrightarrow> hfunction f \<and> hfunction g"
  by (auto simp: hfunction_def) (metis hdomainI hinter_iff hmem_hempty)+

lemma app_hrestrict [simp]: "x \<^bold>\<in> A \<Longrightarrow> app (hrestrict f A) x = app f x"
  by (simp add: hrestrict_def app_def)

section{*Operations on families of sets*}

definition HLambda :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf"
  where "HLambda A b = RepFun A (\<lambda>x. \<langle>x, b x\<rangle>)"

definition HSigma :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf"
  where "HSigma A B = (\<Squnion>x\<^bold>\<in>A. \<Squnion>y\<^bold>\<in>B(x). \<lbrace>\<langle>x,y\<rangle>\<rbrace>)"

definition HPi :: "hf \<Rightarrow> (hf \<Rightarrow> hf) \<Rightarrow> hf"
  where "HPi A B = \<lbrace> f \<^bold>\<in> HPow(HSigma A B). A \<le> hdomain(f) & hfunction(f)\<rbrace>"


syntax (ASCII)
  "_PROD"     :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3PROD _<:_./ _)" 10)
  "_SUM"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3SUM _<:_./ _)" 10)
  "_lam"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3lam _<:_./ _)" 10)
syntax
  "_PROD"     :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<Pi>_\<^bold>\<in>_./ _)" 10)
  "_SUM"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<Sigma>_\<^bold>\<in>_./ _)" 10)
  "_lam"      :: "[pttrn, hf, hf] \<Rightarrow> hf"        ("(3\<lambda>_\<^bold>\<in>_./ _)" 10)
translations
  "PROD x<:A. B" == "CONST HPi A (%x. B)"
  "SUM x<:A. B"  == "CONST HSigma A (%x. B)"
  "lam x<:A. f"  == "CONST HLambda A (%x. f)"

subsection{*Rules for Unions and Intersections of families*}

lemma HUN_iff [simp]: "b \<^bold>\<in> (\<Squnion>x\<^bold>\<in>A. B(x)) \<longleftrightarrow> (\<exists>x\<^bold>\<in>A. b \<^bold>\<in> B(x))"
  by auto

(*The order of the premises presupposes that A is rigid; b may be flexible*)
lemma HUN_I: "\<lbrakk> a \<^bold>\<in> A;  b \<^bold>\<in> B(a) \<rbrakk>  \<Longrightarrow> b \<^bold>\<in> (\<Squnion>x\<^bold>\<in>A. B(x))"
  by auto

lemma HUN_E [elim!]: assumes "b \<^bold>\<in> (\<Squnion>x\<^bold>\<in>A. B(x))" obtains x where "x \<^bold>\<in> A"  "b \<^bold>\<in> B(x)"
  using assms  by blast

lemma HINT_iff: "b \<^bold>\<in> (\<Sqinter>x\<^bold>\<in>A. B(x)) \<longleftrightarrow> (\<forall>x\<^bold>\<in>A. b \<^bold>\<in> B(x)) & A\<noteq>0"
  by (simp add: HInter_def HBall_def) (metis foundation hmem_hempty)

lemma HINT_I: "\<lbrakk> !!x. x \<^bold>\<in> A \<Longrightarrow> b \<^bold>\<in> B(x);  A\<noteq>0 \<rbrakk> \<Longrightarrow> b \<^bold>\<in> (\<Sqinter>x\<^bold>\<in>A. B(x))"
  by (simp add: HINT_iff)

lemma HINT_E: "\<lbrakk> b \<^bold>\<in> (\<Sqinter>x\<^bold>\<in>A. B(x));  a \<^bold>\<in> A \<rbrakk> \<Longrightarrow> b \<^bold>\<in> B(a)"
  by (auto simp: HINT_iff)


subsection{*Generalized Cartesian product*}

lemma HSigma_iff [simp]: "\<langle>a,b\<rangle> \<^bold>\<in> HSigma A B \<longleftrightarrow> a \<^bold>\<in> A & b \<^bold>\<in> B(a)"
  by (force simp add: HSigma_def)

lemma HSigmaI [intro!]: "\<lbrakk> a \<^bold>\<in> A;  b \<^bold>\<in> B(a) \<rbrakk>  \<Longrightarrow> \<langle>a,b\<rangle> \<^bold>\<in> HSigma A B"
  by simp

lemmas HSigmaD1 = HSigma_iff [THEN iffD1, THEN conjunct1]
lemmas HSigmaD2 = HSigma_iff [THEN iffD1, THEN conjunct2]

text{*The general elimination rule*}
lemma HSigmaE [elim!]:
  assumes "c \<^bold>\<in> HSigma A B"
  obtains x y where "x \<^bold>\<in> A" "y \<^bold>\<in> B(x)" "c=\<langle>x,y\<rangle>"
  using assms  by (force simp add: HSigma_def)

lemma HSigmaE2 [elim!]:
  assumes "\<langle>a,b\<rangle> \<^bold>\<in> HSigma A B" obtains "a \<^bold>\<in> A" and "b \<^bold>\<in> B(a)"
  using assms  by auto

lemma HSigma_empty1 [simp]: "HSigma 0 B = 0"
  by blast

instantiation hf :: times
begin
  definition "A * B = HSigma A (\<lambda>x. B)"
  instance ..
end

lemma times_iff [simp]: "\<langle>a,b\<rangle> \<^bold>\<in> A * B \<longleftrightarrow> a \<^bold>\<in> A & b \<^bold>\<in> B"
  by (simp add: times_hf_def)

lemma timesI [intro!]: "\<lbrakk> a \<^bold>\<in> A;  b \<^bold>\<in> B \<rbrakk>  \<Longrightarrow> \<langle>a,b\<rangle> \<^bold>\<in> A * B"
  by simp

lemmas timesD1 = times_iff [THEN iffD1, THEN conjunct1]
lemmas timesD2 = times_iff [THEN iffD1, THEN conjunct2]

text{*The general elimination rule*}
lemma timesE [elim!]:
  assumes c: "c \<^bold>\<in> A * B"
  obtains x y where "x \<^bold>\<in> A" "y \<^bold>\<in> B" "c=\<langle>x,y\<rangle>" using c
  by (auto simp: times_hf_def)

text{*...and a specific one*}
lemma timesE2 [elim!]:
  assumes "\<langle>a,b\<rangle> \<^bold>\<in> A * B" obtains "a \<^bold>\<in> A" and "b \<^bold>\<in> B"
using assms
  by auto

lemma times_empty1 [simp]: "0 * B = (0::hf)"
  by auto

lemma times_empty2 [simp]: "A*0 = (0::hf)"
  by blast

lemma times_empty_iff: "A*B=0 \<longleftrightarrow> A=0 | B=(0::hf)"
  by (auto simp: times_hf_def hf_ext)

instantiation hf :: mult_zero
begin
  instance by standard auto
end

section {*Disjoint Sum*}

instantiation hf :: zero_neq_one
begin
  definition One_hf_def: "1 = \<lbrace>0\<rbrace>"
  instance by standard (auto simp: One_hf_def)
end

instantiation hf :: plus
begin
  definition "A + B = (\<lbrace>0\<rbrace> * A) \<squnion> (\<lbrace>1\<rbrace> * B)"
  instance ..
end

definition Inl :: "hf=>hf" where
     "Inl(a) \<equiv> \<langle>0,a\<rangle>"

definition Inr :: "hf=>hf" where
     "Inr(b) \<equiv> \<langle>1,b\<rangle>"

lemmas sum_defs = plus_hf_def Inl_def Inr_def

lemma Inl_nonzero [simp]:"Inl x \<noteq> 0"
  by (metis Inl_def hpair_nonzero)

lemma Inr_nonzero [simp]:"Inr x \<noteq> 0"
  by (metis Inr_def hpair_nonzero)

text{* Introduction rules for the injections (as equivalences) *}

lemma Inl_in_sum_iff [iff]: "Inl(a) \<^bold>\<in> A+B \<longleftrightarrow> a \<^bold>\<in> A"
  by (auto simp: sum_defs)

lemma Inr_in_sum_iff [iff]: "Inr(b) \<^bold>\<in> A+B \<longleftrightarrow> b \<^bold>\<in> B"
  by (auto simp: sum_defs)

text{*Elimination rule*}

lemma sumE [elim!]:
  assumes u: "u \<^bold>\<in> A+B"
  obtains x where "x \<^bold>\<in> A" "u=Inl(x)" | y where "y \<^bold>\<in> B" "u=Inr(y)" using u
  by (auto simp: sum_defs)

text{* Injection and freeness equivalences, for rewriting *}

lemma Inl_iff [iff]: "Inl(a)=Inl(b) \<longleftrightarrow> a=b"
  by (simp add: sum_defs)

lemma Inr_iff [iff]: "Inr(a)=Inr(b) \<longleftrightarrow> a=b"
  by (simp add: sum_defs)

lemma Inl_Inr_iff [iff]: "Inl(a)=Inr(b) \<longleftrightarrow> False"
  by (simp add: sum_defs)

lemma Inr_Inl_iff [iff]: "Inr(b)=Inl(a) \<longleftrightarrow> False"
  by (simp add: sum_defs)

lemma sum_empty [simp]: "0+0 = (0::hf)"
  by (auto simp: sum_defs)

lemma sum_iff: "u \<^bold>\<in> A+B \<longleftrightarrow> (\<exists>x. x \<^bold>\<in> A & u=Inl(x)) | (\<exists>y. y \<^bold>\<in> B & u=Inr(y))"
  by blast

lemma sum_subset_iff:
  fixes A :: hf shows "A+B \<le> C+D \<longleftrightarrow> A\<le>C & B\<le>D"
  by blast

lemma sum_equal_iff:
  fixes A :: hf shows "A+B = C+D \<longleftrightarrow> A=C & B=D"
  by (auto simp: hf_ext sum_subset_iff)

definition is_hsum :: "hf \<Rightarrow> bool"
  where "is_hsum z = (\<exists>x. z = Inl x \<or> z = Inr x)"

definition sum_case  :: "(hf \<Rightarrow> 'a) \<Rightarrow> (hf \<Rightarrow> 'a) \<Rightarrow> hf \<Rightarrow> 'a"
  where
  "sum_case f g a \<equiv>
    THE z. (\<forall>x. a = Inl x \<longrightarrow> z = f x) \<and> (\<forall>y. a = Inr y \<longrightarrow> z = g y) \<and> (~ is_hsum a \<longrightarrow> z = undefined)"

lemma sum_case_Inl [simp]: "sum_case f g (Inl x) = f x"
  by (simp add: sum_case_def is_hsum_def)

lemma sum_case_Inr [simp]: "sum_case f g (Inr y) = g y"
  by (simp add: sum_case_def is_hsum_def)

lemma sum_case_non [simp]: "~ is_hsum a \<Longrightarrow> sum_case f g a = undefined"
  by (simp add: sum_case_def is_hsum_def)

lemma is_hsum_cases: "(\<exists>x. z = Inl x \<or> z = Inr x) \<or> ~ is_hsum z"
  by (auto simp: is_hsum_def)

lemma sum_case_split: "P (sum_case f g a) \<longleftrightarrow> (\<forall>x. a = Inl x \<longrightarrow> P(f x)) \<and> (\<forall>y. a = Inr y \<longrightarrow> P(g y)) \<and> (~ is_hsum a \<longrightarrow> P undefined)"
  by (cases "is_hsum a") (auto simp: is_hsum_def)

lemma sum_case_split_asm:
  "P (sum_case f g a) \<longleftrightarrow> ~ ((\<exists>x. a = Inl x \<and> ~ P(f x)) \<or> (\<exists>y. a = Inr y \<and> ~ P(g y)) \<or> (~ is_hsum a \<and> ~ P undefined))"
  by (auto simp add: sum_case_split)

end
