(*******************************************************************************

  Title:      HOL/Auth/Message
  Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
  Copyright   1996  University of Cambridge

  Datatypes of agents and messages;
  Inductive relations "parts", "analz" and "synth"

********************************************************************************

  Edited:  Tobias Klenze, ETH Zurich <tobias.klenze@inf.ethz.ch>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>

  Integrated and adapted for security protocol refinement and to add a constructor for finite sets.

*******************************************************************************)

section \<open>Theory of ASes and Messages for Security Protocols\<close>

theory Message imports Keys "HOL-Library.Sublist" "HOL.Finite_Set" "HOL-Library.FSet"
begin

datatype msgterm =
    \<epsilon>                                  \<comment> \<open>Empty message. Used for instance to denote non-existent interface\<close>
  | AS as                              \<comment> \<open>Autonomous System identifier, i.e. agents. Note that AS is an alias of nat\<close>
  | Num nat                            \<comment> \<open>Ordinary integers, timestamps, ...\<close>
  | Key    key                         \<comment> \<open>Crypto keys\<close>
  | Nonce  nonce                       \<comment> \<open>Unguessable nonces\<close>
  | L      "msgterm list"              \<comment> \<open>Lists\<close>
  | FS     "msgterm fset"              \<comment> \<open>Finite Sets. Used to represent XOR values.\<close>
  | MPair  msgterm msgterm             \<comment> \<open>Compound messages\<close>
  | Hash    msgterm                    \<comment> \<open>Hashing\<close>
  | Crypt  key msgterm                 \<comment> \<open>Encryption, public- or shared-key\<close>

text \<open>Syntax sugar\<close>
syntax
  "_MTuple" :: "['a, args] \<Rightarrow> 'a * 'b"       ("(2\<langle>_,/ _\<rangle>)")

syntax (xsymbols)
  "_MTuple" :: "['a, args] \<Rightarrow> 'a * 'b"       ("(2\<langle>_,/ _\<rangle>)")

translations
  "\<langle>x, y, z\<rangle>" \<rightleftharpoons> "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>"    \<rightleftharpoons> "CONST MPair x y"

syntax
  "_MHF" :: "['a, 'b , 'c, 'd, 'e] \<Rightarrow> 'a * 'b * 'c * 'd * 'e"  ("(5HF\<lhd>_,/ _,/ _,/ _,/ _\<rhd>)")

abbreviation
  Mac :: "[msgterm,msgterm] \<Rightarrow> msgterm"                       ("(4Mac[_] /_)" [0, 1000])
where
  \<comment> \<open>Message Y paired with a MAC computed with the help of X\<close>
  "Mac[X] Y \<equiv> Hash \<langle>X,Y\<rangle>"

abbreviation macKey where "macKey a \<equiv> Key (macK a)"

definition
  keysFor :: "msgterm set \<Rightarrow> key set"
where
  \<comment> \<open>Keys useful to decrypt elements of a message set\<close>
  "keysFor H \<equiv> invKey ` {K. \<exists>X. Crypt K X \<in> H}"

subsubsection \<open>Inductive Definition of "All Parts" of a Message\<close>

inductive_set
  parts :: "msgterm set \<Rightarrow> msgterm set"
  for H :: "msgterm set"
  where
    Inj [intro]: "X \<in> H \<Longrightarrow> X \<in> parts H"
  | Fst:         "\<langle>X,_\<rangle> \<in> parts H \<Longrightarrow> X \<in> parts H"
  | Snd:         "\<langle>_,Y\<rangle> \<in> parts H \<Longrightarrow> Y \<in> parts H"
  | Lst:         "\<lbrakk> L xs \<in> parts H; X \<in> set xs \<rbrakk> \<Longrightarrow> X \<in> parts H"
  | FSt:          "\<lbrakk> FS xs \<in> parts H; X |\<in>| xs \<rbrakk> \<Longrightarrow> X \<in> parts H"
(*| Hd:          "L (X # xs) \<in> parts H \<Longrightarrow> X \<in> parts H"
  | Tl:          "L (X # xs) \<in> parts H \<Longrightarrow> L xs \<in> parts H" *)
  | Body:        "Crypt K X \<in> parts H \<Longrightarrow> X \<in> parts H"


text \<open>Monotonicity\<close>
lemma parts_mono: "G \<subseteq> H \<Longrightarrow> parts G \<subseteq> parts H"
apply auto
apply (erule parts.induct)
apply (blast dest: parts.Fst parts.Snd parts.Lst parts.FSt parts.Body)+
done


text \<open>Equations hold because constructors are injective.\<close>
lemma Other_image_eq [simp]: "(AS x \<in> AS`A) = (x:A)"
by auto

lemma Key_image_eq [simp]: "(Key x \<in> Key`A) = (x\<in>A)"
by auto

lemma AS_Key_image_eq [simp]: "(AS x \<notin> Key`A)"
by auto

lemma Num_Key_image_eq [simp]: "(Num x \<notin> Key`A)"
by auto

subsection \<open>keysFor operator\<close>

lemma keysFor_empty [simp]: "keysFor {} = {}"
by (unfold keysFor_def, blast)

lemma keysFor_Un [simp]: "keysFor (H \<union> H') = keysFor H \<union> keysFor H'"
by (unfold keysFor_def, blast)

lemma keysFor_UN [simp]: "keysFor (\<Union>i\<in>A. H i) = (\<Union>i\<in>A. keysFor (H i))"
by (unfold keysFor_def, blast)

text \<open>Monotonicity\<close>
lemma keysFor_mono: "G \<subseteq> H \<Longrightarrow> keysFor G \<subseteq> keysFor H"
by (unfold keysFor_def, blast)

lemma keysFor_insert_AS [simp]: "keysFor (insert (AS A) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Num [simp]: "keysFor (insert (Num N) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Key [simp]: "keysFor (insert (Key K) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Nonce [simp]: "keysFor (insert (Nonce n) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_L [simp]: "keysFor (insert (L X) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_FS [simp]: "keysFor (insert (FS X) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Hash [simp]: "keysFor (insert (Hash X) H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_MPair [simp]: "keysFor (insert \<langle>X,Y\<rangle> H) = keysFor H"
by (unfold keysFor_def, auto)

lemma keysFor_insert_Crypt [simp]:
  "keysFor (insert (Crypt K X) H) = insert (invKey K) (keysFor H)"
by (unfold keysFor_def, auto)

lemma keysFor_image_Key [simp]: "keysFor (Key`E) = {}"
by (unfold keysFor_def, auto)

lemma Crypt_imp_invKey_keysFor: "Crypt K X \<in> H \<Longrightarrow> invKey K \<in> keysFor H"
by (unfold keysFor_def, blast)


subsection \<open>Inductive relation "parts"\<close>

lemma MPair_parts:
  "\<lbrakk>
    \<langle>X,Y\<rangle> \<in> parts H;
    \<lbrakk> X \<in> parts H; Y \<in> parts H \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
by (blast dest: parts.Fst parts.Snd)

lemma L_parts:
  "\<lbrakk>
    L l \<in> parts H;
    \<lbrakk> set l \<subseteq> parts H \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (blast dest: parts.Lst)

lemma FS_parts:
  "\<lbrakk>
    FS l \<in> parts H;
    \<lbrakk> fset l \<subseteq> parts H \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (simp add: parts.FSt subsetI)
thm parts.FSt subsetI

declare MPair_parts [elim!] L_parts [elim!] FS_parts [elim] parts.Body [dest!]

text \<open>NB These two rules are UNSAFE in the formal sense, as they discard the
        compound message.  They work well on THIS FILE.
        @{text MPair_parts} is left as SAFE because it speeds up proofs.
        The Crypt rule is normally kept UNSAFE to avoid breaking up certificates.\<close>

lemma parts_increasing: "H \<subseteq> parts H"
by blast

lemmas parts_insertI = subset_insertI [THEN parts_mono, THEN subsetD]

lemma parts_empty [simp]: "parts{} = {}"
apply safe
apply (erule parts.induct, blast+)
done

lemma parts_emptyE [elim!]: "X\<in> parts{} \<Longrightarrow> P"
by simp

text \<open>WARNING: loops if H = {Y}, therefore must not be repeated!\<close>
lemma parts_singleton: "X \<in> parts H \<Longrightarrow> \<exists>Y \<in> H. X \<in> parts {Y}"
  apply (erule parts.induct, fast)
  using parts.FSt by blast+

lemma parts_singleton_set: "x \<in> parts {s . P s} \<Longrightarrow> \<exists>Y. P Y \<and> x \<in> parts {Y}"
  by(auto dest: parts_singleton)

lemma parts_singleton_set_rev: "\<lbrakk>x \<in> parts {Y}; P Y\<rbrakk> \<Longrightarrow> x \<in> parts {s . P s}"
  by (induction rule: parts.induct)
     (blast dest: parts.Fst parts.Snd parts.Lst parts.FSt parts.Body)+

lemma parts_Hash: "\<lbrakk>\<And>t . t \<in> H \<Longrightarrow> \<exists>t' . t = Hash t'\<rbrakk> \<Longrightarrow> parts H = H"
  by (auto, erule parts.induct, fast+)

subsubsection \<open>Unions\<close>

lemma parts_Un_subset1: "parts G \<union> parts H \<subseteq> parts(G \<union> H)"
by (intro Un_least parts_mono Un_upper1 Un_upper2)

lemma parts_Un_subset2: "parts(G \<union> H) \<subseteq> parts G \<union> parts H"
  by (rule subsetI) (erule parts.induct, blast+)

lemma parts_Un [simp]: "parts(G \<union> H) = parts G \<union> parts H"
by (intro equalityI parts_Un_subset1 parts_Un_subset2)

lemma parts_insert: "parts (insert X H) = parts {X} \<union> parts H"
apply (subst insert_is_Un [of _ H])
apply (simp only: parts_Un)
done

text \<open>TWO inserts to avoid looping.  This rewrite is better than nothing.
        Not suitable for Addsimps: its behaviour can be strange.\<close>
lemma parts_insert2:
  "parts (insert X (insert Y H)) = parts {X} \<union> parts {Y} \<union> parts H"
apply (simp add: Un_assoc)
apply (simp add: parts_insert [symmetric])
done

(*needed?!*)
lemma parts_two: "\<lbrakk>x \<in> parts {e1, e2}; x \<notin> parts {e1}\<rbrakk>\<Longrightarrow> x \<in> parts {e2}"
  by (simp add: parts_insert2)


text \<open>Added to simplify arguments to parts, analz and synth.\<close>


text \<open>This allows @{text blast} to simplify occurrences of
        @{term "parts(G\<union>H)"} in the assumption.\<close>
lemmas in_parts_UnE = parts_Un [THEN equalityD1, THEN subsetD, THEN UnE]
declare in_parts_UnE [elim!]


lemma parts_insert_subset: "insert X (parts H) \<subseteq> parts(insert X H)"
by (blast intro: parts_mono [THEN [2] rev_subsetD])



subsubsection \<open>Idempotence\<close>

lemma parts_partsD [dest!]: "X\<in> parts (parts H) \<Longrightarrow> X\<in> parts H"
  by (erule parts.induct, blast+)

lemma parts_idem [simp]: "parts (parts H) = parts H"
by blast

lemma parts_subset_iff [simp]: "(parts G \<subseteq> parts H) = (G \<subseteq> parts H)"
apply (rule iffI)
apply (iprover intro: subset_trans parts_increasing)
apply (frule parts_mono, simp)
done

subsubsection \<open>Transitivity\<close>
lemma parts_trans: "\<lbrakk> X\<in> parts G;  G \<subseteq> parts H \<rbrakk> \<Longrightarrow> X\<in> parts H"
by (drule parts_mono, blast)

subsubsection \<open>Unions, revisited\<close>
text \<open>You can take the union of parts h for all h in H\<close>
lemma parts_split: "parts H = \<Union> { parts {h} | h . h \<in> H}"
apply auto
apply (erule parts.induct)
apply (blast dest: parts.Fst parts.Snd parts.Lst parts.FSt parts.Body)+
using parts_trans apply blast
done

text \<open>Cut\<close>
lemma parts_cut:
  "\<lbrakk> Y\<in> parts (insert X G);  X \<in> parts H \<rbrakk> \<Longrightarrow> Y \<in> parts (G \<union> H)"
by (blast intro: parts_trans)


lemma parts_cut_eq [simp]: "X \<in> parts H \<Longrightarrow> parts (insert X H) = parts H"
by (force dest!: parts_cut intro: parts_insertI)


subsubsection \<open>Rewrite rules for pulling out atomic messages\<close>

lemmas parts_insert_eq_I = equalityI [OF subsetI parts_insert_subset]


lemma parts_insert_AS [simp]:
  "parts (insert (AS agt) H) = insert (AS agt) (parts H)"
apply (rule parts_insert_eq_I)
by (erule parts.induct, auto elim!: FS_parts)

lemma parts_insert_Epsilon [simp]:
  "parts (insert \<epsilon> H) = insert \<epsilon> (parts H)"
apply (rule parts_insert_eq_I)
  by (erule parts.induct, auto)

lemma parts_insert_Num [simp]:
  "parts (insert (Num N) H) = insert (Num N) (parts H)"
apply (rule parts_insert_eq_I)
by (erule parts.induct, auto)

lemma parts_insert_Key [simp]:
  "parts (insert (Key K) H) = insert (Key K) (parts H)"
apply (rule parts_insert_eq_I)
by (erule parts.induct, auto)

lemma parts_insert_Nonce [simp]:
  "parts (insert (Nonce n) H) = insert (Nonce n) (parts H)"
apply (rule parts_insert_eq_I)
by (erule parts.induct, auto)

lemma parts_insert_Hash [simp]:
  "parts (insert (Hash X) H) = insert (Hash X) (parts H)"
apply (rule parts_insert_eq_I)
by (erule parts.induct, auto)

lemma parts_insert_Crypt [simp]:
  "parts (insert (Crypt K X) H) = insert (Crypt K X) (parts (insert X H))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
by (blast intro: parts.Body)

lemma parts_insert_MPair [simp]:
  "parts (insert \<langle>X,Y\<rangle> H) =
    insert \<langle>X,Y\<rangle> (parts (insert X (insert Y H)))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
by (blast intro: parts.Fst parts.Snd)+

lemma parts_insert_L [simp]:
  "parts (insert (L xs) H) =
    insert (L xs) (parts ((set xs) \<union>  H))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
by (blast intro: parts.Lst)+

lemma parts_insert_FS [simp]:
  "parts (insert (FS xs) H) =
    insert (FS xs) (parts ((fset xs) \<union>  H))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
by (auto intro: parts.FSt)+

lemma parts_image_Key [simp]: "parts (Key`N) = Key`N"
apply auto
apply (erule parts.induct, auto)
done


text \<open>Parts of lists and finite sets.\<close>

lemma parts_list_set (*[simp]*):
  "parts (L`ls) =  (L`ls) \<union> (\<Union>l \<in> ls. parts (set l)) "
apply (rule equalityI, rule subsetI)
apply (erule parts.induct, auto)
by (meson L_parts image_subset_iff parts_increasing parts_trans)

lemma parts_insert_list_set (*[simp]*):
  "parts ((L`ls) \<union> H) =  (L`ls) \<union> (\<Union>l \<in> ls. parts ((set l))) \<union> parts H"
apply (rule equalityI, rule subsetI)
by (erule parts.induct, auto simp add: parts_list_set)

(*needed?!*)
lemma parts_fset_set (*[simp]*):
  "parts (FS`ls) =  (FS`ls) \<union> (\<Union>l \<in> ls. parts (fset l)) "
apply (rule equalityI, rule subsetI)
apply (erule parts.induct, auto)
by (meson FS_parts image_subset_iff parts_increasing parts_trans)

subsubsection \<open>suffix of parts\<close>
lemma suffix_in_parts:
  "suffix (x#xs) ys \<Longrightarrow> x \<in> parts {L ys}"
by (auto simp add: suffix_def)

lemma parts_L_set:
  "\<lbrakk>x \<in> parts {L ys}; ys \<in> St\<rbrakk> \<Longrightarrow> x \<in> parts (L`St)"
by (metis (no_types, lifting) image_insert insert_iff mk_disjoint_insert parts.Inj
    parts_cut_eq parts_insert parts_insert2)

lemma suffix_in_parts_set:
  "\<lbrakk>suffix (x#xs) ys; ys \<in> St\<rbrakk> \<Longrightarrow> x \<in> parts (L`St)"
using parts_L_set suffix_in_parts
by blast

subsection \<open>Inductive relation "analz"\<close>

text \<open>Inductive definition of "analz" -- what can be broken down from a set of
        messages, including keys.  A form of downward closure.  Pairs can
        be taken apart; messages decrypted with known keys.\<close>

inductive_set
  analz :: "msgterm set \<Rightarrow> msgterm set"
  for H :: "msgterm set"
  where
    Inj [intro,simp] : "X \<in> H \<Longrightarrow> X \<in> analz H"
  | Fst:               "\<langle>X,Y\<rangle> \<in> analz H \<Longrightarrow> X \<in> analz H"
  | Snd:               "\<langle>X,Y\<rangle> \<in> analz H \<Longrightarrow> Y \<in> analz H"
  | Lst:               "(L y) \<in> analz H  \<Longrightarrow> x \<in> set (y) \<Longrightarrow> x \<in> analz H "
  | FSt:               "\<lbrakk> FS xs \<in> analz H; X |\<in>| xs \<rbrakk> \<Longrightarrow> X \<in> analz H"
  | Decrypt [dest]:    "\<lbrakk> Crypt K X \<in> analz H; Key (invKey K) \<in> analz H \<rbrakk> \<Longrightarrow> X \<in> analz H"


text \<open>Monotonicity; Lemma 1 of Lowe's paper\<close>
lemma analz_mono: "G \<subseteq> H \<Longrightarrow> analz(G) \<subseteq> analz(H)"
apply auto
apply (erule analz.induct)
apply (auto dest: analz.Fst analz.Snd analz.Lst analz.FSt )
done

lemmas analz_monotonic = analz_mono [THEN [2] rev_subsetD]

text \<open>Making it safe speeds up proofs\<close>
lemma MPair_analz [elim!]:
  "\<lbrakk>
    \<langle>X,Y\<rangle> \<in> analz H;
    \<lbrakk> X \<in> analz H; Y \<in> analz H \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
by (blast dest: analz.Fst analz.Snd)

lemma L_analz [elim!]:
  "\<lbrakk>
    L l \<in> analz H;
    \<lbrakk> set l \<subseteq> analz H \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
by (blast dest: analz.Lst analz.FSt)

lemma FS_analz [elim!]:
  "\<lbrakk>
    FS l \<in> analz H;
    \<lbrakk> fset l \<subseteq> analz H \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (simp add: analz.FSt subsetI)

thm parts.FSt subsetI
lemma analz_increasing: "H \<subseteq> analz(H)"
by blast

lemma analz_subset_parts: "analz H \<subseteq> parts H"
  by (rule subsetI) (erule analz.induct, blast+)


text \<open>If there is no cryptography, then analz and parts is equivalent.\<close>
lemma no_crypt_analz_is_parts:
  "\<not> (\<exists> K X . Crypt K X \<in> parts A) \<Longrightarrow> analz A = parts A"
apply (rule equalityI, simp add: analz_subset_parts)
apply (rule subsetI)
by (erule parts.induct, blast+, auto)

lemmas analz_into_parts = analz_subset_parts [THEN subsetD]

lemmas not_parts_not_analz = analz_subset_parts [THEN contra_subsetD]


lemma parts_analz [simp]: "parts (analz H) = parts H"
apply (rule equalityI)
apply (rule analz_subset_parts [THEN parts_mono, THEN subset_trans], simp)
apply (blast intro: analz_increasing [THEN parts_mono, THEN subsetD])
done

lemma analz_parts [simp]: "analz (parts H) = parts H"
apply auto
apply (erule analz.induct, auto)
done

lemmas analz_insertI = subset_insertI [THEN analz_mono, THEN [2] rev_subsetD]

subsubsection \<open>General equational properties\<close>

lemma analz_empty [simp]: "analz {} = {}"
apply safe
apply (erule analz.induct, blast+)
done

text \<open>Converse fails: we can analz more from the union than from the
        separate parts, as a key in one might decrypt a message in the other\<close>
lemma analz_Un: "analz(G) \<union> analz(H) \<subseteq> analz(G \<union> H)"
by (intro Un_least analz_mono Un_upper1 Un_upper2)

lemma analz_insert: "insert X (analz H) \<subseteq> analz(insert X H)"
by (blast intro: analz_mono [THEN [2] rev_subsetD])

subsubsection \<open>Rewrite rules for pulling out atomic messages\<close>

lemmas analz_insert_eq_I = equalityI [OF subsetI analz_insert]

lemma analz_insert_AS [simp]:
  "analz (insert (AS agt) H) = insert (AS agt) (analz H)"
apply (rule analz_insert_eq_I)
by (erule analz.induct, auto)

lemma analz_insert_Num [simp]:
  "analz (insert (Num N) H) = insert (Num N) (analz H)"
apply (rule analz_insert_eq_I)
by (erule analz.induct, auto)

text \<open>Can only pull out Keys if they are not needed to decrypt the rest\<close>
lemma analz_insert_Key [simp]:
  "K \<notin> keysFor (analz H) \<Longrightarrow>
    analz (insert (Key K) H) = insert (Key K) (analz H)"
apply (unfold keysFor_def)
apply (rule analz_insert_eq_I)
by (erule analz.induct, auto)

lemma analz_insert_LEmpty [simp]:
  "analz (insert (L []) H) = insert (L []) (analz H)"
apply (rule analz_insert_eq_I)
by (erule analz.induct, auto)


lemma analz_insert_L [simp]:
  "analz (insert (L l) H) = insert (L l) (analz (set l \<union> H))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct, auto)
apply (erule analz.induct, auto)
using analz.Inj by blast

lemma analz_insert_FS [simp]:
  "analz (insert (FS l) H) = insert (FS l) (analz (fset l \<union> H))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct, auto)
apply (erule analz.induct, auto)
using analz.Inj by blast

lemma "L[] \<in> analz {L[L[]]}"
using analz.Inj by simp

lemma analz_insert_Hash [simp]:
  "analz (insert (Hash X) H) = insert (Hash X) (analz H)"
apply (rule analz_insert_eq_I)
by (erule analz.induct, auto)

lemma analz_insert_MPair [simp]:
  "analz (insert \<langle>X,Y\<rangle> H) =
    insert \<langle>X,Y\<rangle> (analz (insert X (insert Y H)))"
apply (rule equalityI)
apply (rule subsetI)
apply (erule analz.induct, auto)
apply (erule analz.induct, auto)
using Fst Snd analz.Inj insertI1
by (metis)+


text \<open>Can pull out enCrypted message if the Key is not known\<close>
lemma analz_insert_Crypt:
  "Key (invKey K) \<notin> analz H
    \<Longrightarrow> analz (insert (Crypt K X) H) = insert (Crypt K X) (analz H)"
apply (rule analz_insert_eq_I)
by (erule analz.induct, auto)

lemma analz_insert_Decrypt1:
  "Key (invKey K) \<in> analz H \<Longrightarrow>
    analz (insert (Crypt K X) H) \<subseteq>
    insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
by (erule_tac x = x in analz.induct, auto)

lemma analz_insert_Decrypt2:
  "Key (invKey K) \<in> analz H \<Longrightarrow>
    insert (Crypt K X) (analz (insert X H)) \<subseteq>
    analz (insert (Crypt K X) H)"
apply auto
apply (erule_tac x = x in analz.induct, auto)
by (blast intro: analz_insertI analz.Decrypt)

lemma analz_insert_Decrypt:
  "Key (invKey K) \<in> analz H \<Longrightarrow>
    analz (insert (Crypt K X) H) =
    insert (Crypt K X) (analz (insert X H))"
by (intro equalityI analz_insert_Decrypt1 analz_insert_Decrypt2)

text \<open>Case analysis: either the message is secure, or it is not! Effective,
        but can cause subgoals to blow up! Use with @{text "split_if"}; apparently
        @{text "split_tac"} does not cope with patterns such as @{term"analz (insert
        (Crypt K X) H)"}\<close>
lemma analz_Crypt_if [simp]:
  "analz (insert (Crypt K X) H) =
    (if (Key (invKey K) \<in> analz H)
     then insert (Crypt K X) (analz (insert X H))
     else insert (Crypt K X) (analz H))"
by (simp add: analz_insert_Crypt analz_insert_Decrypt)


text \<open>This rule supposes "for the sake of argument" that we have the key.\<close>
lemma analz_insert_Crypt_subset:
  "analz (insert (Crypt K X) H) \<subseteq>
    insert (Crypt K X) (analz (insert X H))"
apply (rule subsetI)
by (erule analz.induct, auto)

lemma analz_image_Key [simp]: "analz (Key`N) = Key`N"
apply auto
apply (erule analz.induct, auto)
done


subsubsection \<open>Idempotence and transitivity\<close>

lemma analz_analzD [dest!]: "X\<in> analz (analz H) \<Longrightarrow> X\<in> analz H"
by (erule analz.induct, auto)

lemma analz_idem [simp]: "analz (analz H) = analz H"
by blast

lemma analz_subset_iff [simp]: "(analz G \<subseteq> analz H) = (G \<subseteq> analz H)"
apply (rule iffI)
apply (iprover intro: subset_trans analz_increasing)
apply (frule analz_mono, simp)
done

lemma analz_trans: "\<lbrakk> X\<in> analz G;  G \<subseteq> analz H \<rbrakk> \<Longrightarrow> X\<in> analz H"
by (drule analz_mono, blast)

text \<open>Cut; Lemma 2 of Lowe\<close>
lemma analz_cut: "\<lbrakk> Y\<in> analz (insert X H);  X\<in> analz H \<rbrakk> \<Longrightarrow> Y\<in> analz H"
by (erule analz_trans, blast)

(*Cut can be proved easily by induction on
   "Y: analz (insert X H) \<Longrightarrow> X: analz H --> Y: analz H"
*)

text \<open>This rewrite rule helps in the simplification of messages that involve
        the forwarding of unknown components (X).  Without it, removing occurrences
        of X can be very complicated.\<close>
lemma analz_insert_eq: "X\<in> analz H \<Longrightarrow> analz (insert X H) = analz H"
by (blast intro: analz_cut analz_insertI)


text \<open>A congruence rule for "analz"\<close>

lemma analz_subset_cong:
  "\<lbrakk> analz G \<subseteq> analz G'; analz H \<subseteq> analz H' \<rbrakk>
    \<Longrightarrow> analz (G \<union> H) \<subseteq> analz (G' \<union> H')"
apply simp
apply (iprover intro: conjI subset_trans analz_mono Un_upper1 Un_upper2)
done

lemma analz_cong:
  "\<lbrakk> analz G = analz G'; analz H = analz H' \<rbrakk>
    \<Longrightarrow> analz (G \<union> H) = analz (G' \<union> H')"
by (intro equalityI analz_subset_cong, simp_all)

lemma analz_insert_cong:
  "analz H = analz H' \<Longrightarrow> analz(insert X H) = analz(insert X H')"
by (force simp only: insert_def intro!: analz_cong)

text \<open>If there are no pairs, lists or encryptions then analz does nothing\<close>
(*needed?*)
lemma analz_trivial:
  "\<lbrakk>
    \<forall>X Y. \<langle>X,Y\<rangle> \<notin> H; \<forall>xs. L xs \<notin> H; \<forall>xs. FS xs \<notin> H;
    \<forall>X K. Crypt K X \<notin> H
   \<rbrakk> \<Longrightarrow> analz H = H"
apply safe
by (erule analz.induct, auto)

text \<open>These two are obsolete (with a single Spy) but cost little to prove...\<close>
lemma analz_UN_analz_lemma:
  "X\<in> analz (\<Union>i\<in>A. analz (H i)) \<Longrightarrow> X\<in> analz (\<Union>i\<in>A. H i)"
apply (erule analz.induct)
by (auto intro: analz_mono [THEN [2] rev_subsetD])

lemma analz_UN_analz [simp]: "analz (\<Union>i\<in>A. analz (H i)) = analz (\<Union>i\<in>A. H i)"
by (blast intro: analz_UN_analz_lemma analz_mono [THEN [2] rev_subsetD])


subsubsection \<open>Lemmas assuming absense of keys\<close>
text \<open>If there are no keys in analz H, you can take the union of analz h for all h in H\<close>

lemma analz_split:
  "\<not>(\<exists> K . Key K \<in> analz H)
    \<Longrightarrow> analz H = \<Union> { analz {h} | h . h \<in> H}"
apply auto
subgoal
  apply (erule analz.induct)
  apply (auto dest: analz.Fst analz.Snd analz.Lst analz.FSt)
done
  apply (erule analz.induct)
  apply (auto dest: analz.Fst analz.Snd analz.Lst analz.FSt)
done

lemma analz_Un_eq:
  assumes "\<not>(\<exists> K . Key K \<in> analz H)" and "\<not>(\<exists> K . Key K \<in> analz G)"
  shows "analz (H \<union> G) = analz H \<union> analz G"
apply (intro equalityI, rule subsetI)
apply (erule analz.induct)
using assms by auto

lemma analz_Un_eq_Crypt:
  assumes "\<not>(\<exists> K . Key K \<in> analz G)" and "\<not>(\<exists> K X . Crypt K X \<in> analz G)"
  shows "analz (H \<union> G) = analz H \<union> analz G"
apply (intro equalityI, rule subsetI)
apply (erule analz.induct)
using assms by auto

lemma analz_list_set (*[simp]*):
  "\<not>(\<exists> K . Key K \<in> analz (L`ls))
    \<Longrightarrow> analz (L`ls) =  (L`ls) \<union> (\<Union>l \<in> ls. analz (set l)) "
apply (rule equalityI, rule subsetI)
apply (erule analz.induct, auto)
using L_analz image_subset_iff analz_increasing analz_trans by metis

lemma analz_fset_set (*[simp]*):
  "\<not>(\<exists> K . Key K \<in> analz (FS`ls))
    \<Longrightarrow> analz (FS`ls) =  (FS`ls) \<union> (\<Union>l \<in> ls. analz (fset l)) "
apply (rule equalityI, rule subsetI)
apply (erule analz.induct, auto)
using FS_analz image_subset_iff analz_increasing analz_trans by metis


subsection \<open>Inductive relation "synth"\<close>

text \<open>Inductive definition of "synth" -- what can be built up from a set of
        messages.  A form of upward closure.  Pairs can be built, messages
        encrypted with known keys.  AS names are public domain.
        Nums can be guessed, but Nonces cannot be.\<close>

inductive_set
  synth :: "msgterm set \<Rightarrow> msgterm set"
  for H :: "msgterm set"
  where
    Inj    [intro]:   "X \<in> H \<Longrightarrow> X \<in> synth H"
  | \<epsilon>  [simp,intro!]:   "\<epsilon> \<in> synth H"
  | AS  [simp,intro!]:   "AS agt \<in> synth H"
  | Num [simp,intro!]:   "Num n  \<in> synth H"
  | Lst [intro]:      "\<lbrakk> \<And>x . x \<in> set xs \<Longrightarrow> x \<in> synth H \<rbrakk> \<Longrightarrow> L xs \<in> synth H"
  | FSt [intro]:      "\<lbrakk> \<And>x . x \<in> fset xs \<Longrightarrow> x \<in> synth H;
                         \<And>x ys . x \<in> fset xs \<Longrightarrow> x \<noteq> FS ys \<rbrakk>
                      \<Longrightarrow> FS xs \<in> synth H"
  | Hash   [intro]:   "X \<in> synth H \<Longrightarrow> Hash X \<in> synth H"
  | MPair  [intro]:   "\<lbrakk> X \<in> synth H;  Y \<in> synth H \<rbrakk> \<Longrightarrow> \<langle>X,Y\<rangle> \<in> synth H"
  | Crypt  [intro]:   "\<lbrakk> X \<in> synth H;  Key K \<in> H \<rbrakk> \<Longrightarrow> Crypt K X \<in> synth H"


(*removed fcard xs \<noteq> Suc 0 from FSt premise*)


text \<open>Monotonicity\<close>
lemma synth_mono: "G \<subseteq> H \<Longrightarrow> synth(G) \<subseteq> synth(H)"
  apply (auto, erule synth.induct, auto)
  by blast

text \<open>NO @{text AS_synth}, as any AS name can be synthesized.
        The same holds for @{term Num}\<close>
inductive_cases Key_synth   [elim!]: "Key K \<in> synth H"
inductive_cases Nonce_synth [elim!]: "Nonce n \<in> synth H"
inductive_cases Hash_synth  [elim!]: "Hash X \<in> synth H"
inductive_cases MPair_synth [elim!]: "\<langle>X,Y\<rangle> \<in> synth H"
inductive_cases L_synth     [elim!]: "L X \<in> synth H"
inductive_cases FS_synth    [elim!]: "FS X \<in> synth H"
inductive_cases Crypt_synth [elim!]: "Crypt K X \<in> synth H"

lemma synth_increasing: "H \<subseteq> synth(H)"
by blast

lemma synth_analz_self: "x \<in> H \<Longrightarrow> x \<in> synth (analz H)"
  by blast

subsubsection \<open>Unions\<close>

text \<open>Converse fails: we can synth more from the union than from the
        separate parts, building a compound message using elements of each.\<close>
lemma synth_Un: "synth(G) \<union> synth(H) \<subseteq> synth(G \<union> H)"
by (intro Un_least synth_mono Un_upper1 Un_upper2)

lemma synth_insert: "insert X (synth H) \<subseteq> synth(insert X H)"
by (blast intro: synth_mono [THEN [2] rev_subsetD])

subsubsection \<open>Idempotence and transitivity\<close>

lemma synth_synthD [dest!]: "X\<in> synth (synth H) \<Longrightarrow> X \<in> synth H"
apply (erule synth.induct, blast)
apply auto by blast

lemma synth_idem: "synth (synth H) = synth H"
by blast

lemma synth_subset_iff [simp]: "(synth G \<subseteq> synth H) = (G \<subseteq> synth H)"
apply (rule iffI)
apply (iprover intro: subset_trans synth_increasing)
apply (frule synth_mono, simp add: synth_idem)
done

lemma synth_trans: "\<lbrakk> X\<in> synth G;  G \<subseteq> synth H \<rbrakk> \<Longrightarrow> X\<in> synth H"
by (drule synth_mono, blast)

text \<open>Cut; Lemma 2 of Lowe\<close>
lemma synth_cut: "\<lbrakk> Y\<in> synth (insert X H);  X\<in> synth H \<rbrakk> \<Longrightarrow> Y\<in> synth H"
by (erule synth_trans, blast)

lemma Nonce_synth_eq [simp]: "(Nonce N \<in> synth H) = (Nonce N \<in> H)"
by blast

lemma Key_synth_eq [simp]: "(Key K \<in> synth H) = (Key K \<in> H)"
by blast

lemma Crypt_synth_eq [simp]:
  "Key K \<notin> H \<Longrightarrow> (Crypt K X \<in> synth H) = (Crypt K X \<in> H)"
by blast


lemma keysFor_synth [simp]:
  "keysFor (synth H) = keysFor H \<union> invKey`{K. Key K \<in> H}"
by (unfold keysFor_def, blast)

lemma L_cons_synth [simp]:
  "(set xs \<subseteq> H) \<Longrightarrow> (L xs \<in> synth H)"
by auto

lemma FS_cons_synth [simp]:
  "\<lbrakk>fset xs \<subseteq> H; \<And>x ys. x \<in> fset xs \<Longrightarrow> x \<noteq> FS ys; fcard xs \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> (FS xs \<in> synth H)"
by auto

subsubsection \<open>Combinations of parts, analz and synth\<close>

lemma parts_synth [simp]: "parts (synth H) = parts H \<union> synth H"
proof (safe del: UnCI)
  fix X
  assume "X \<in> parts (synth H)"
  thus "X \<in> parts H \<union> synth H"
  by (induct rule: parts.induct)
     (auto intro: parts.Fst parts.Snd parts.Lst parts.FSt parts.Body)
next
  fix X
  assume "X \<in> parts H"
  thus "X \<in> parts (synth H)"
  by (induction rule: parts.induct)
     (auto intro: parts.Fst parts.Snd  parts.Lst parts.FSt parts.Body)
next
  fix X
  assume "X \<in> synth H"
  thus "X \<in> parts (synth H)"
    apply (induction rule: synth.induct)
    apply(auto intro: parts.Fst parts.Snd  parts.Lst parts.FSt parts.Body)
    by blast
qed


lemma analz_analz_Un [simp]: "analz (analz G \<union> H) = analz (G \<union> H)"
apply (intro equalityI analz_subset_cong)+
apply simp_all
done

lemma analz_synth_Un [simp]: "analz (synth G \<union> H) = analz (G \<union> H) \<union> synth G"
proof (safe del: UnCI)
  fix X
  assume "X \<in> analz (synth G \<union> H)"
  thus "X \<in> analz (G \<union> H) \<union> synth G"
  by (induction rule: analz.induct)
     (auto intro: analz.Fst analz.Snd analz.Lst analz.FSt analz.Decrypt)
qed (auto elim: analz_mono [THEN [2] rev_subsetD])

lemma analz_synth [simp]: "analz (synth H) = analz H \<union> synth H"
apply (cut_tac H = "{}" in analz_synth_Un)
apply (simp (no_asm_use))
done

lemma analz_Un_analz [simp]: "analz (G \<union> analz H) = analz (G \<union> H)"
by (subst Un_commute, auto)+

lemma analz_synth_Un2 [simp]: "analz (G \<union> synth H) = analz (G \<union> H) \<union> synth H"
by (subst Un_commute, auto)+


subsubsection \<open>For reasoning about the Fake rule in traces\<close>

lemma parts_insert_subset_Un: "X\<in> G \<Longrightarrow> parts(insert X H) \<subseteq> parts G \<union> parts H"
by (rule subset_trans [OF parts_mono parts_Un_subset2], blast)

text \<open>More specifically for Fake.  Very occasionally we could do with a version
  of the form  @{term"parts{X} \<subseteq> synth (analz H) \<union> parts H"}\<close>
lemma Fake_parts_insert:
  "X \<in> synth (analz H) \<Longrightarrow>
    parts (insert X H) \<subseteq> synth (analz H) \<union> parts H"
apply (drule parts_insert_subset_Un)
apply (simp (no_asm_use))
apply blast
done

lemma Fake_parts_insert_in_Un:
  "\<lbrakk>Z \<in> parts (insert X H);  X \<in> synth (analz H)\<rbrakk>
    \<Longrightarrow> Z \<in>  synth (analz H) \<union> parts H"
by (blast dest: Fake_parts_insert  [THEN subsetD, dest])

text \<open>@{term H} is sometimes @{term"Key ` KK \<union> spies evs"}, so can't put @{term "G=H"}.\<close>
lemma Fake_analz_insert:
  "X\<in> synth (analz G) \<Longrightarrow>
    analz (insert X H) \<subseteq> synth (analz G) \<union> analz (G \<union> H)"
apply (rule subsetI)
apply (subgoal_tac "x \<in> analz (synth (analz G) \<union> H) ")
prefer 2
  apply (blast intro: analz_mono [THEN [2] rev_subsetD]
                      analz_mono [THEN synth_mono, THEN [2] rev_subsetD])
apply (simp (no_asm_use))
apply blast
done

lemma analz_conj_parts [simp]:
  "(X \<in> analz H & X \<in> parts H) = (X \<in> analz H)"
by (blast intro: analz_subset_parts [THEN subsetD])

lemma analz_disj_parts [simp]:
  "(X \<in> analz H | X \<in> parts H) = (X \<in> parts H)"
by (blast intro: analz_subset_parts [THEN subsetD])

text \<open>Without this equation, other rules for synth and analz would yield
        redundant cases\<close>
lemma MPair_synth_analz [iff]:
  "(\<langle>X,Y\<rangle> \<in> synth (analz H)) =
    (X \<in> synth (analz H) & Y \<in> synth (analz H))"
by blast

lemma L_cons_synth_analz [iff]:
  "(L xs \<in> synth (analz H)) =
    (set xs \<subseteq> synth (analz H))"
by blast

lemma L_cons_synth_parts [iff]:
  "(L xs \<in> synth (parts H)) =
    (set xs \<subseteq> synth (parts H))"
by blast

lemma FS_cons_synth_analz [iff]:
  "\<lbrakk>\<And>x ys . x \<in> fset xs \<Longrightarrow> x \<noteq> FS ys; fcard xs \<noteq> Suc 0 \<rbrakk> \<Longrightarrow>
    (FS xs \<in> synth (analz H)) =
    (fset xs \<subseteq> synth (analz H))"
by blast

lemma FS_cons_synth_parts [iff]:
  "\<lbrakk>\<And>x ys . x \<in> fset xs \<Longrightarrow> x \<noteq> FS ys; fcard xs \<noteq> Suc 0 \<rbrakk> \<Longrightarrow>
    (FS xs \<in> synth (parts H)) =
    (fset xs \<subseteq> synth (parts H))"
by blast

lemma Crypt_synth_analz:
  "\<lbrakk> Key K \<in> analz H;  Key (invKey K) \<in> analz H \<rbrakk>
    \<Longrightarrow> (Crypt K X \<in> synth (analz H)) = (X \<in> synth (analz H))"
by blast

lemma Hash_synth_analz [simp]:
  "X \<notin> synth (analz H)
    \<Longrightarrow> (Hash\<langle>X,Y\<rangle> \<in> synth (analz H)) = (Hash\<langle>X,Y\<rangle> \<in> analz H)"
by blast


subsection \<open>HPair: a combination of Hash and MPair\<close>

text \<open>We do NOT want Crypt... messages broken up in protocols!!\<close>
declare parts.Body [rule del]


text \<open>Rewrites to push in Key and Crypt messages, so that other messages can
        be pulled out using the @{text analz_insert} rules\<close>

(*needed?*)
lemmas pushKeys =
  insert_commute [of "Key K" "AS C" for K C]
  insert_commute [of "Key K" "Nonce N" for K N]
  insert_commute [of "Key K" "Num N" for K N]
  insert_commute [of "Key K" "Hash X" for K X]
  insert_commute [of "Key K" "MPair X Y" for K X Y]
  insert_commute [of "Key K" "Crypt X K'" for K K' X]

(*needed?*)
lemmas pushCrypts =
  insert_commute [of "Crypt X K" "AS C" for X K C]
  insert_commute [of "Crypt X K" "AS C" for X K C]
  insert_commute [of "Crypt X K" "Nonce N" for X K N]
  insert_commute [of "Crypt X K" "Num N"  for X K N]
  insert_commute [of "Crypt X K" "Hash X'"  for X K X']
  insert_commute [of "Crypt X K" "MPair X' Y"  for X K X' Y]

text \<open>Cannot be added with @{text "[simp]"} -- messages should not always be
        re-ordered.\<close>
lemmas pushes = pushKeys pushCrypts

text \<open>By default only @{text o_apply} is built-in.  But in the presence of
        eta-expansion this means that some terms displayed as @{term "f o g"} will be
        rewritten, and others will not!\<close>
declare o_def [simp]


lemma Crypt_notin_image_Key [simp]: "Crypt K X \<notin> Key ` A"
by auto

lemma Hash_notin_image_Key [simp] :"Hash X \<notin> Key ` A"
by auto

lemma synth_analz_mono: "G\<subseteq>H \<Longrightarrow> synth (analz(G)) \<subseteq> synth (analz(H))"
by (iprover intro: synth_mono analz_mono)

lemma synth_parts_mono: "G\<subseteq>H \<Longrightarrow> synth (parts G) \<subseteq> synth (parts H)"
by (iprover intro: synth_mono parts_mono)

lemma Fake_analz_eq [simp]:
  "X \<in> synth(analz H) \<Longrightarrow> synth (analz (insert X H)) = synth (analz H)"
apply (drule Fake_analz_insert[of _ _ "H"])
apply (simp add: synth_increasing[THEN Un_absorb2])
apply (drule synth_mono)
apply (simp add: synth_idem)
apply (rule equalityI)
apply (simp add: )
apply (rule synth_analz_mono, blast)
done

text \<open>Two generalizations of @{text analz_insert_eq}\<close>
lemma gen_analz_insert_eq [rule_format]:
  "X \<in> analz H \<Longrightarrow> ALL G. H \<subseteq> G --> analz (insert X G) = analz G"
by (blast intro: analz_cut analz_insertI analz_mono [THEN [2] rev_subsetD])

lemma Fake_parts_sing:
  "X \<in> synth (analz H) \<Longrightarrow> parts{X} \<subseteq> synth (analz H) \<union> parts H"
apply (rule subset_trans)
 apply (erule_tac [2] Fake_parts_insert)
apply (rule parts_mono, blast)
done

lemmas Fake_parts_sing_imp_Un = Fake_parts_sing [THEN [2] rev_subsetD]

text \<open>For some reason, moving this up can make some proofs loop!\<close>
declare invKey_K [simp]


lemma synth_analz_insert:
  assumes "analz H \<subseteq> synth (analz H')"
  shows "analz (insert X H) \<subseteq> synth (analz (insert X H'))"
proof
  fix x
  assume "x \<in> analz (insert X H)"
  then have "x \<in> analz (insert X (synth (analz H')))"
    using assms by (meson analz_increasing analz_monotonic insert_mono)
  then show "x \<in> synth (analz (insert X H'))"
    by (metis (no_types) Un_iff analz_idem analz_insert analz_monotonic analz_synth synth.Inj
        synth_insert synth_mono)
qed

lemma synth_parts_insert:
  assumes "parts H \<subseteq> synth (parts H')"
  shows "parts (insert X H) \<subseteq> synth (parts (insert X H'))"
proof
  fix x
  assume "x \<in> parts (insert X H)"
  then have "x \<in> parts (insert X (synth (parts H')))"
    using assms parts_increasing
    by (metis UnE UnI1 analz_monotonic analz_parts parts_insert parts_insertI)
  then show "x \<in> synth (parts (insert X H'))"
  using Un_iff parts_idem parts_insert parts_synth synth.Inj
  by (metis Un_subset_iff synth_increasing synth_trans)
qed


lemma parts_insert_subset_impl:
  "\<lbrakk>x \<in> parts (insert a G); x \<in> parts G \<Longrightarrow> x \<in> synth (parts H); a \<in> synth (parts H)\<rbrakk>
    \<Longrightarrow> x \<in> synth (parts H)"
using Fake_parts_sing in_parts_UnE insert_is_Un
          parts_idem parts_synth subsetCE sup.absorb2 synth_idem synth_increasing
by (metis (no_types, lifting) analz_parts)

lemma synth_parts_subset_elem:
  "\<lbrakk>A \<subseteq> synth (parts B); x \<in> parts A\<rbrakk> \<Longrightarrow> x \<in> synth (parts B)"
by (meson parts_emptyE parts_insert_subset_impl parts_singleton subset_iff)

lemma synth_parts_subset:
  "A \<subseteq> synth (parts B) \<Longrightarrow> parts A \<subseteq> synth (parts B)"
by (auto simp add: synth_parts_subset_elem)


lemma parts_synth_parts[simp]: "parts (synth (parts H)) = synth (parts H)"
by auto

lemma synth_parts_trans:
  assumes "A \<subseteq> synth (parts B)" and "B \<subseteq> synth (parts C)"
  shows "A \<subseteq> synth (parts C)"
using assms by (metis order_trans parts_synth_parts synth_idem synth_parts_mono)

lemma synth_parts_trans_elem:
  assumes "x \<in> A" and "A \<subseteq> synth (parts B)" and "B \<subseteq> synth (parts C)"
  shows "x \<in> synth (parts C)"
using synth_parts_trans assms by auto

lemma synth_un_parts_split:
  assumes "x \<in> synth (parts A \<union> parts B)"
    and "\<And>x . x \<in> A \<Longrightarrow> x \<in> synth (parts C)"
    and "\<And>x . x \<in> B \<Longrightarrow> x \<in> synth (parts C)"
  shows "x \<in> synth (parts C)"
proof -
  have "parts A \<subseteq> synth (parts C)" "parts B \<subseteq> synth (parts C)"
    using assms(2) assms(3) synth_parts_subset by blast+
  then have "x \<in> synth (synth (parts C) \<union> synth (parts C))" using assms(1)
    using synth_trans by auto
  then show ?thesis by auto
qed


subsubsection \<open>Normalization of Messages\<close>
text\<open>Prevent FS from being contained directly in other FS.
For instance, a term @{term "FS {| FS {| Num 0 |}, Num 0 |}"} is
not normalized, whereas @{term "FS {| Hash (FS {| Num 0 |}), Num 0 |}"} is normalized.\<close>


inductive normalized :: "msgterm \<Rightarrow> bool" where
    \<epsilon>  [simp,intro!]:    "normalized \<epsilon>"
  | AS  [simp,intro!]:   "normalized (AS agt)"
  | Num [simp,intro!]:   "normalized (Num n)"
  | Key [simp,intro!]:   "normalized (Key n)"
  | Nonce [simp,intro!]:  "normalized (Nonce n)"
  | Lst [intro]:      "\<lbrakk> \<And>x . x \<in> set xs \<Longrightarrow> normalized x \<rbrakk> \<Longrightarrow> normalized (L xs)"
  | FSt [intro]:      "\<lbrakk> \<And>x . x \<in> fset xs \<Longrightarrow> normalized x;
                         \<And>x ys . x \<in> fset xs \<Longrightarrow> x \<noteq> FS ys \<rbrakk>
                      \<Longrightarrow> normalized (FS xs)"
  | Hash   [intro]:   "normalized X \<Longrightarrow> normalized (Hash X)"
  | MPair  [intro]:   "\<lbrakk> normalized X; normalized Y \<rbrakk> \<Longrightarrow> normalized \<langle>X,Y\<rangle>"
  | Crypt  [intro]:   "\<lbrakk> normalized X \<rbrakk> \<Longrightarrow> normalized (Crypt K X)"

thm normalized.simps
find_theorems normalized

text\<open>Examples\<close>
lemma "normalized (FS {| Hash (FS {| Num 0 |}), Num 0 |})" by fastforce
lemma "\<not> normalized (FS {| FS {| Num 0 |}, Num 0 |})" by (auto elim: normalized.cases)


subsubsection\<open>Closure of @{text "normalized"} under @{text "parts"}, @{text "analz"} and @{text "synth"}\<close>

text\<open>All synthesized terms are normalized (since @{text "synth"} prevents directly nested FSets).\<close>
lemma normalized_synth[elim!]: "\<lbrakk>t \<in> synth H; \<And>t. t \<in> H \<Longrightarrow> normalized t\<rbrakk> \<Longrightarrow> normalized t"
  by(induction t, auto 3 4)

lemma normalized_parts[elim!]: "\<lbrakk>t \<in> parts H; \<And>t. t \<in> H \<Longrightarrow> normalized t\<rbrakk> \<Longrightarrow> normalized t"
  by(induction t rule: parts.induct)
    (auto elim: normalized.cases)

lemma normalized_analz[elim!]: "\<lbrakk>t \<in> analz H; \<And>t. t \<in> H \<Longrightarrow> normalized t\<rbrakk> \<Longrightarrow> normalized t"
  by(induction t rule: analz.induct)
    (auto elim: normalized.cases)

subsubsection\<open>Properties of @{text "normalized"}\<close>

lemma normalized_FS[elim]: "\<lbrakk>normalized (FS xs); x |\<in>| xs\<rbrakk> \<Longrightarrow> normalized x"
  by(auto simp add: normalized.simps[of "FS xs"])

lemma normalized_FS_FS[elim]: "\<lbrakk>normalized (FS xs); x |\<in>| xs; x = FS ys\<rbrakk> \<Longrightarrow> False"
  by(auto simp add: normalized.simps[of "FS xs"])

lemma normalized_subset: "\<lbrakk>normalized (FS xs); ys |\<subseteq>| xs\<rbrakk> \<Longrightarrow> normalized (FS ys)"
  by (auto intro!: normalized.FSt)

lemma normalized_insert[elim!]: "normalized (FS (finsert x xs)) \<Longrightarrow> normalized (FS xs)"
  by(auto elim!: normalized_subset)

lemma normalized_union:
  assumes "normalized (FS xs)" "normalized (FS ys)" "zs |\<subseteq>| xs |\<union>| ys"
  shows "normalized (FS zs)"
  using assms by(auto intro!: normalized.FSt)

lemma normalized_minus[elim]:
  assumes "normalized (FS (ys |-| xs))" "normalized (FS xs)"
  shows "normalized (FS ys)"
  using normalized_union assms by blast


subsubsection\<open>Lemmas that do not use @{text "normalized"}, but are helpful in proving its properties\<close>
lemma FS_mono: "\<lbrakk>zs_s = finsert (f (FS zs_s)) zs_b; \<And> x. size (f x) > size x\<rbrakk> \<Longrightarrow> False"
  by (metis (no_types) add.right_neutral add_Suc_right finite_fset finsert.rep_eq less_add_Suc1
      msgterm.size(17) not_less_eq size_fset_simps sum.insert_remove)

lemma FS_contr: "\<lbrakk>zs = f (FS {|zs|}); \<And> x. size (f x) > size x\<rbrakk> \<Longrightarrow> False"
  using FS_mono by blast


end
