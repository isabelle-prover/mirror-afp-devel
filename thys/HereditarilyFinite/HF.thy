header{*The Hereditarily Finite Sets*}

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

definition hmem :: "hf \<Rightarrow> hf \<Rightarrow> bool"     (infixl "<:" 50)
  where "hmem a b \<longleftrightarrow> a \<in> hfset b"


instantiation hf :: zero
begin

definition
  Zero_hf_def: "0 = HF {}"

instance ..

end

text {* HF Set enumerations *}

syntax
  "_HFinset" :: "args \<Rightarrow> hf"      ("{|(_)|}")

syntax (xsymbols)
  "_HFinset" :: "args \<Rightarrow> hf"      ("\<lbrace>_\<rbrace>")
  "_inserthf" :: "hf \<Rightarrow> hf \<Rightarrow> hf"  (infixl "\<triangleleft>" 60)

notation (xsymbols)
  hmem             (infixl "\<^bold>\<in>" 50)

translations
  "y \<triangleleft> x"    == "CONST hinsert x y"
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
lemma hinsert_iff: "z = y \<triangleleft> x \<longleftrightarrow> (\<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<^bold>\<in> y | u=x)"
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

lemma singleton_eq_iff [iff]: "\<lbrace>a\<rbrace> = \<lbrace>b\<rbrace> \<longleftrightarrow> a=b"
  by (metis hmem_hempty hmem_hinsert)

lemma doubleton_eq_iff: "\<lbrace>a,b\<rbrace> = \<lbrace>c,d\<rbrace> \<longleftrightarrow> (a=c & b=d) | (a=d & b=c)"
  by (metis (hide_lams, no_types) hinsert_commute hmem_hempty hmem_hinsert)

section {* Ordered Pairs, from ZF/ZF.thy *}

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
syntax
  ""          :: "hf \<Rightarrow> hfs"                    ("_")
  "_Enum"     :: "[hf, hfs] \<Rightarrow> hfs"             ("_,/ _")
  "_Tuple"    :: "[hf, hfs] \<Rightarrow> hf"              ("<(_,/ _)>")
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   ("<_,/ _>")
syntax (xsymbols)
  "_Tuple"    :: "[hf, hfs] \<Rightarrow> hf"              ("\<langle>(_,/ _)\<rangle>")
  "_hpattern" :: "[pttrn, patterns] \<Rightarrow> pttrn"   ("\<langle>_,/ _\<rangle>")
syntax (HTML output)
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

syntax
  "_HCollect" :: "idt \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> hf"    ("(1\<lbrace>_ <:/ _./ _\<rbrace>)")
syntax (xsymbols)
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
  definition sup_hf :: "hf \<Rightarrow> hf \<Rightarrow> hf"
    where "sup_hf a b = (THE z. \<forall>u. u \<^bold>\<in> z \<longleftrightarrow> u \<^bold>\<in> a | u \<^bold>\<in> b)"
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

definition inf_hf :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "inf_hf a b = \<lbrace>x \<^bold>\<in> a. x \<^bold>\<in> b\<rbrace>"

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
  definition minus_hf where "minus A B = \<lbrace>x \<^bold>\<in> A. \<not> x \<^bold>\<in> B\<rbrace>"
  instance proof qed
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


syntax
  "_HReplace"  :: "[pttrn, pttrn, hf, bool] \<Rightarrow> hf" ("(1{|_ ./ _<: _, _|})")
  "_HRepFun"   :: "[hf, pttrn, hf] \<Rightarrow> hf"          ("(1{|_ ./ _<: _|})" [51,0,51])
  "_HINTER"    :: "[pttrn, hf, hf] \<Rightarrow> hf"          ("(3INT _<:_./ _)" 10)
  "_HUNION"    :: "[pttrn, hf, hf] \<Rightarrow> hf"          ("(3UN _<:_./ _)" 10)

syntax (xsymbols)
  "_HReplace"  :: "[pttrn, pttrn, hf, bool] \<Rightarrow> hf" ("(1\<lbrace>_ ./ _ \<^bold>\<in> _, _\<rbrace>)")
  "_HRepFun"   :: "[hf, pttrn, hf] \<Rightarrow> hf"          ("(1\<lbrace>_ ./ _ \<^bold>\<in> _\<rbrace>)" [51,0,51])
  "_HUNION"    :: "[pttrn, hf, hf] \<Rightarrow> hf"          ("(3\<Squnion>_\<^bold>\<in>_./ _)" 10)
  "_HINTER"    :: "[pttrn, hf, hf] \<Rightarrow> hf"          ("(3\<Sqinter>_\<^bold>\<in>_./ _)" 10)

syntax (HTML output)
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


section{*Subset relation and the Lattice Properties*}

text{*Definition 1.10 (Subset relation).*}
instantiation hf :: order
  begin
  definition less_eq_hf where "A \<le> B \<longleftrightarrow> (\<forall>x. x \<^bold>\<in> A \<longrightarrow> x \<^bold>\<in> B)"

  definition less_hf    where "A < B \<longleftrightarrow> A \<le> B & A \<noteq> (B::hf)"

  instance proof qed (auto simp: less_eq_hf_def less_hf_def)
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
  instance proof qed (auto simp: less_eq_hf_def less_hf_def inf_hf_def)
  end

instantiation hf :: bounded_lattice_bot
  begin
  definition bot_hf where "bot_hf = (0::hf)"
  instance proof qed (auto simp: less_eq_hf_def bot_hf_def)
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
lemma hfset_0: "hfset 0 = {}"
  by (metis Zero_hf_def finite.emptyI hfset_HF)

lemma hfset_hinsert: "hfset (b \<triangleleft> a) = insert a (hfset b)"
  by (metis finite_insert hinsert_def HF.finite_hfset hfset_HF)

lemma hfset_hdiff: "hfset (x - y) = hfset x - hfset y"
proof (induct x arbitrary: y rule: hf_induct)
  case 0 thus ?case
    by (simp add: hfset_0)
next
  case (hinsert a b) thus ?case
    by (simp add: hfset_hinsert Set.insert_Diff_if hinsert_hdiff_if hmem_def)
qed

definition hcard :: "hf \<Rightarrow> nat"
  where "hcard x = card (hfset x)"

lemma hcard_0 [simp]: "hcard 0 = 0"
  by (simp add: hcard_def hfset_0)

lemma hcard_hinsert_if: "hcard (hinsert x y) = (if x \<^bold>\<in> y then hcard y else Suc (hcard y))"
  by (simp add: hcard_def hfset_hinsert card_insert_if hmem_def)

lemma hcard_union_inter: "hcard (x \<squnion> y) + hcard (x \<sqinter> y) = hcard x + hcard y"
  apply (induct x arbitrary: y rule: hf_induct)
  apply (auto simp: hcard_hinsert_if hunion_hinsert_left hinter_hinsert_left)
  done

lemma hcard_hdiff1_less: "x \<^bold>\<in> z \<Longrightarrow> hcard (z - \<lbrace>x\<rbrace>) < hcard z"
  by (simp add: hcard_def hfset_hdiff hfset_hinsert hfset_0)
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

syntax
  "_HBall"       :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3ALL _<:_./ _)" [0, 0, 10] 10)
  "_HBex"        :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX _<:_./ _)"  [0, 0, 10] 10)
  "_HBex1"       :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX! _<:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_HBall"       :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>_\<^bold>\<in>_./ _)"  [0, 0, 10] 10)
  "_HBex"        :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>_\<^bold>\<in>_./ _)"  [0, 0, 10] 10)
  "_HBex1"       :: "pttrn \<Rightarrow> hf \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>!_\<^bold>\<in>_./ _)" [0, 0, 10] 10)

syntax (HTML output)
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

end
