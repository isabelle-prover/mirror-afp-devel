(*  Title:      HOL/Library/Coinductive_Streams.thy
    Author:     Lawrence C Paulson and Makarius
    Adapted by Peter Gammie from Coinductive_Lists.thy
*)

header {* Infinite lists as greatest fixed-point *}

theory Coinductive_Streams
imports Main
begin

subsection {* Constructors over the datatype universe *}

definition "CONS M N = Datatype.Scons M N"

lemma CONS_inject [iff]: "(CONS K M) = (CONS L N) = (K = L \<and> M = N)"
  by (simp_all add: CONS_def)

lemma CONS_mono: "M \<subseteq> M' \<Longrightarrow> N \<subseteq> N' \<Longrightarrow> CONS M N \<subseteq> CONS M' N'"
  by (simp add: CONS_def In1_mono Scons_mono)

lemma CONS_UN1: "CONS M (\<Union>x. f x) = (\<Union>x. CONS M (f x))"
    -- {* A continuity result? *}
  by (simp add: CONS_def In1_UN1 Scons_UN1_y)

definition "Stream_case = Datatype.Split"

lemma Stream_case_CONS [simp]: "Stream_case h (CONS M N) = h M N"
  by (simp_all add: Stream_case_def CONS_def)


subsection {* Corecursive streams *}

coinductive_set Stream for A where
  CONS [intro]: "a \<in> A \<Longrightarrow> M \<in> Stream A \<Longrightarrow> CONS a M \<in> Stream A"

lemma Stream_mono:
  assumes subset: "A \<subseteq> B"
  shows "Stream A \<subseteq> Stream B"
    -- {* This justifies using @{text Stream} in other recursive type definitions. *}
proof
  fix x
  assume "x \<in> Stream A"
  then show "x \<in> Stream B"
  proof coinduct
    case Stream
    then show ?case using subset
      by cases blast+
  qed
qed

primrec
  Stream_corec_aux :: "nat \<Rightarrow> ('a \<Rightarrow> ('b Datatype.item \<times> 'a)) \<Rightarrow>
    'a \<Rightarrow> 'b Datatype.item"
where
  "Stream_corec_aux 0 f x = {}"
| "Stream_corec_aux (Suc k) f x =
    (case f x of (z, w) \<Rightarrow> CONS z (Stream_corec_aux k f w))"

definition "Stream_corec a f = (\<Union>k. Stream_corec_aux k f a)"

text {*
  Note: the subsequent recursion equation for @{text Stream_corec} may
  be used with the Simplifier, provided it operates in a non-strict
  fashion for case expressions (i.e.\ the usual @{text case}
  congruence rule needs to be present).
*}

lemma Stream_corec:
  "Stream_corec a f = (case f a of (z, w) \<Rightarrow> CONS z (Stream_corec w f))" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    apply (unfold Stream_corec_def)
    apply (rule UN_least)
    apply (case_tac k)
     apply (simp_all (no_asm_simp) split: prod.splits)
    apply (rule allI impI subset_refl [THEN CONS_mono] UNIV_I [THEN UN_upper])+
    done
  show "?rhs \<subseteq> ?lhs"
    apply (simp add: Stream_corec_def split: prod.splits)
    apply (simp add: CONS_UN1)
    apply safe
     apply (rule_tac a = "Suc ?k" in UN_I, simp, simp)+
    done
qed

lemma Stream_corec_type: "Stream_corec a f \<in> Stream UNIV"
proof -
  have "\<exists>x. Stream_corec a f = Stream_corec x f" by blast
  then show ?thesis
  proof coinduct
    case (Stream L)
    then obtain x where L: "L = Stream_corec x f" by blast
    have "Stream_corec x f = CONS (fst (f x)) (Stream_corec (snd (f x)) f)"
      apply (subst Stream_corec)
      apply (simp split: prod.split)
      done
    with L have ?CONS by auto
    then show ?case by blast
  qed
qed

(* Perhaps redundant on a better understanding of the Datatype machinery. *)
lemma FIXME_stream_inhabited: "Stream_corec a (\<lambda>x. (Datatype.Leaf x, x)) \<in> Stream (range Datatype.Leaf)"
proof -
  let ?f = "\<lambda>x. (Datatype.Leaf x, x)"
  have "\<exists>x. Stream_corec a ?f = Stream_corec x ?f" by blast
  then show ?thesis
  proof coinduct
    case (Stream L)
    then obtain x where L: "L = Stream_corec x ?f" by blast
    have "Stream_corec x ?f = CONS (fst (?f x)) (Stream_corec (snd (?f x)) ?f)"
      apply (subst Stream_corec)
      apply (simp split: prod.split)
      done
    with L have ?CONS by auto
    then show ?case by blast
  qed
qed


subsection {* Abstract type definition *}

definition "stream = Stream (range Datatype.Leaf)"

typedef (open) 'a stream = "stream :: 'a Datatype.item set"
proof
  show "Stream_corec undefined (\<lambda>x. (Datatype.Leaf x, x)) \<in> stream"
    unfolding stream_def by (rule FIXME_stream_inhabited)
qed

lemma CONS_type: "a \<in> range Datatype.Leaf \<Longrightarrow>
    M \<in> stream \<Longrightarrow> CONS a M \<in> stream"
  unfolding stream_def by (rule Stream.CONS)

lemma streamI: "x \<in> Stream (range Datatype.Leaf) \<Longrightarrow> x \<in> stream"
  by (simp add: stream_def)

lemma streamD: "x \<in> stream \<Longrightarrow> x \<in> Stream (range Datatype.Leaf)"
  by (simp add: stream_def)

lemma Rep_stream_UNIV: "Rep_stream x \<in> Stream UNIV"
proof -
  have "Rep_stream x \<in> stream" by (rule Rep_stream)
  then have "Rep_stream x \<in> Stream (range Datatype.Leaf)"
    by (simp add: stream_def)
  also have "\<dots> \<subseteq> Stream UNIV" by (rule Stream_mono) simp
  finally show ?thesis .
qed

definition "SCons x xs = Abs_stream (CONS (Datatype.Leaf x) (Rep_stream xs))"

code_datatype SCons

lemma SCons_inject [iff, induct_simp]: "(SCons x xs = SCons y ys) = (x = y \<and> xs = ys)"
  apply (simp add: SCons_def)
  apply (subst Abs_stream_inject)
    apply (auto simp add: Rep_stream_inject intro: CONS_type Rep_stream)
  done

lemma Rep_stream_SCons: "Rep_stream (SCons x l) =
    CONS (Datatype.Leaf x) (Rep_stream l)"
  by (simp add: SCons_def Abs_stream_inverse CONS_type Rep_stream)

lemma stream_cases [cases type: stream]:
  obtains (SCons) x l' where "l = SCons x l'"
proof (cases l)
  case (Abs_stream L)
  from `L \<in> stream` have "L \<in> Stream (range Datatype.Leaf)" by (rule streamD)
  then show ?thesis
  proof cases
    case (CONS a K)
    then have "K \<in> stream" by (blast intro: streamI)
    then obtain l' where "K = Rep_stream l'" by cases
    with CONS and Abs_stream obtain x where "l = SCons x l'"
      by (auto simp add: SCons_def Abs_stream_inject)
    with SCons show ?thesis .
  qed
qed


definition
  [code del]: "stream_case d l =
    Stream_case (\<lambda>x y. d (inv Datatype.Leaf x) (Abs_stream y)) (Rep_stream l)"


translations
  "case p of XCONST SCons x l \<Rightarrow> b" \<rightleftharpoons> "CONST stream_case (\<lambda>x l. b) p"
  "case p of (XCONST SCons :: 'b) x l \<Rightarrow> b" \<rightharpoonup> "CONST stream_case (\<lambda>x l. b) p"

lemma stream_case_SCons [simp, code]: "stream_case d (SCons M N) = d M N"
  by (simp add: stream_case_def SCons_def
    CONS_type Abs_stream_inverse Rep_stream Rep_stream_inverse inj_Leaf)

lemma stream_case_cert:
  assumes "CASE \<equiv> stream_case d"
  shows "CASE (SCons M N) \<equiv> d M N"
  using assms by simp

setup {*
  Code.add_case @{thm stream_case_cert}
*}

setup {*
  Nitpick.register_codatatype @{typ "'a stream"} @{const_name stream_case}
    (map dest_Const [@{term SCons}])
*}

definition
  [code del]: "stream_corec a f =
    Abs_stream (Stream_corec a
      (\<lambda>z. case f z of (v, w) \<Rightarrow> (Datatype.Leaf v, w)))"

lemma Stream_corec_type2:
  "Stream_corec a
    (\<lambda>z. case f z of (v, w) \<Rightarrow> (Datatype.Leaf v, w)) \<in> stream"
  (is "?corec a \<in> _")
proof (unfold stream_def)
  let "Stream_corec a ?g" = "?corec a"
  have "\<exists>x. ?corec a = ?corec x" by blast
  then show "?corec a \<in> Stream (range Datatype.Leaf)"
  proof coinduct
    case (Stream L)
    then obtain x where L: "L = ?corec x" by blast
    have "?corec x = CONS (Datatype.Leaf (fst (f x))) (?corec (snd (f x)))"
      apply (subst Stream_corec)
      apply (simp split: prod.split)
      done
    with L have ?CONS by auto
    then show ?case by blast
  qed
qed

lemma stream_corec [code, nitpick_simp]:
  "stream_corec a f = (case f a of (z, w) \<Rightarrow> SCons z (stream_corec w f))"
proof -
  let "?corec a" = "stream_corec a f"
  let "?rep_corec a" =
    "Stream_corec a
      (\<lambda>z. case f z of (v, w) \<Rightarrow> (Datatype.Leaf v, w))"

  have "?corec a = Abs_stream (?rep_corec a)"
    by (simp only: stream_corec_def)
  also have "?rep_corec a =
      CONS (Datatype.Leaf (fst (f a))) (?rep_corec (snd (f a)))"
    apply (subst Stream_corec)
    apply (simp split: prod.split)
    done
  also have "?rep_corec (snd (f a)) = Rep_stream (?corec (snd (f a)))"
    by (simp only: stream_corec_def Abs_stream_inverse Stream_corec_type2)
  finally have "?corec a = SCons (fst (f a)) (?corec (snd (f a)))"
    by (simp only: SCons_def)
  thus ?thesis by (simp split: prod.split)
qed

subsection {* Equality as greatest fixed-point -- the bisimulation principle *}

coinductive_set EqStream for r
where EqCONS: "(a, b) \<in> r \<Longrightarrow> (M, N) \<in> EqStream r \<Longrightarrow>
      (CONS a M, CONS b N) \<in> EqStream r"

lemma EqStream_unfold:
    "EqStream r = dprod r (EqStream r)"
  by (fast intro!: EqStream.intros [unfolded CONS_def]
           elim: EqStream.cases [unfolded CONS_def])

lemma EqStream_implies_ntrunc_equality:
    "(M, N) \<in> EqStream (Id_on A) \<Longrightarrow> ntrunc k M = ntrunc k N"
  apply (induct k arbitrary: M N rule: nat_less_induct)
  apply (erule EqStream.cases)
   apply (safe del: equalityI)
  apply (case_tac n)
   apply simp
  apply (rename_tac n')
  apply (case_tac n')
   apply (simp_all add: CONS_def less_Suc_eq)
  done

lemma Domain_EqStream: "Domain (EqStream (Id_on A)) \<subseteq> Stream A"
  apply (rule subsetI)
  apply (erule Stream.coinduct)
  apply (subst (asm) EqStream_unfold)
  apply (auto simp add: CONS_def)
  done

lemma EqStream_Id_on: "EqStream (Id_on A) = Id_on (Stream A)"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
    apply (rule subsetI)
    apply (rule_tac p = x in PairE)
    apply clarify
    apply (rule Id_on_eqI)
     apply (rule EqStream_implies_ntrunc_equality [THEN ntrunc_equality],
       assumption)
    apply (erule DomainI [THEN Domain_EqStream [THEN subsetD]])
    done
  {
    fix M N assume "(M, N) \<in> Id_on (Stream A)"
    then have "(M, N) \<in> EqStream (Id_on A)"
    proof coinduct
      case (EqStream M N)
      then obtain L where L: "L \<in> Stream A" and MN: "M = L" "N = L" by blast
      from L show ?case
      proof cases
        case CONS with MN have ?EqCONS by (simp add: Id_onI)
        then show ?thesis by blast
      qed
    qed
  }
  then show "?rhs \<subseteq> ?lhs" by auto
qed

lemma EqStream_Id_on_iff [iff]: "(p \<in> EqStream (Id_on A)) = (p \<in> Id_on (Stream A))"
  by (simp only: EqStream_Id_on)


text {*
  To show two Streams are equal, exhibit a bisimulation!  (Also admits
  true equality.)
*}

lemma Stream_equalityI
  [consumes 1, case_names EqStream, case_conclusion EqStream EqCONS]:
  assumes r: "(M, N) \<in> r"
    and step: "\<And>M N. (M, N) \<in> r \<Longrightarrow>
        (\<exists>a b M' N'.
          M = CONS a M' \<and> N = CONS b N' \<and> (a, b) \<in> Id_on A \<and>
            ((M', N') \<in> r \<or> (M', N') \<in> EqStream (Id_on A)))"
  shows "M = N"
proof -
  from r have "(M, N) \<in> EqStream (Id_on A)"
  proof coinduct
    case EqStream
    then show ?case by (rule step)
  qed
  then show ?thesis by auto
qed

lemma Stream_fun_equalityI
  [consumes 1, case_names CONS, case_conclusion CONS EqCONS]:
  assumes M: "M \<in> Stream A"
    and fun_CONS: "\<And>x l. x \<in> A \<Longrightarrow> l \<in> Stream A \<Longrightarrow>
            (\<exists>M N a b.
              (f (CONS x l), g (CONS x l)) = (CONS a M, CONS b N) \<and>
                (a, b) \<in> Id_on A \<and>
                (M, N) \<in> {(f u, g u) | u. u \<in> Stream A} \<union> Id_on (Stream A))"
      (is "\<And>x l. _ \<Longrightarrow> _ \<Longrightarrow> ?fun_CONS x l")
  shows "f M = g M"
proof -
  let ?bisim = "{(f L, g L) | L. L \<in> Stream A}"
  have "(f M, g M) \<in> ?bisim" using M by blast
  then show ?thesis
  proof (coinduct taking: A rule: Stream_equalityI)
    case (EqStream M N)
    then obtain L where MN: "M = f L" "N = g L" and L: "L \<in> Stream A" by blast
    from L show ?case
    proof (cases L)
      case (CONS a K)
      from fun_CONS and `a \<in> A` `K \<in> Stream A`
      have "?fun_CONS a K" (is "?CONS") .
      then show ?thesis
      proof -
        assume ?CONS
        with CONS obtain a b M' N' where
            fg: "(f L, g L) = (CONS a M', CONS b N')"
          and ab: "(a, b) \<in> Id_on A"
          and M'N': "(M', N') \<in> ?bisim \<union> Id_on (Stream A)"
          by blast
        from M'N' show ?thesis
        proof
          assume "(M', N') \<in> ?bisim"
          with MN fg ab show ?thesis by simp
        next
          assume "(M', N') \<in> Id_on (Stream A)"
          then have "(M', N') \<in> EqStream (Id_on A)" ..
          with MN fg ab show ?thesis by simp
        qed
      qed
    qed
  qed
qed

text {*
  Finality of @{text "stream A"}: Uniqueness of functions defined by corecursion.
*}

lemma equals_Stream_corec:
  assumes h: "\<And>x. h x = (case f x of (z, w) \<Rightarrow> CONS z (h w))"
  shows "h x = (\<lambda>x. Stream_corec x f) x"
proof -
  def h' \<equiv> "\<lambda>x. Stream_corec x f"
  then have h': "\<And>x. h' x = (case f x of (z, w) \<Rightarrow> CONS z (h' w))"
    unfolding h'_def by (subst Stream_corec) simp
  have "(h x, h' x) \<in> {(h u, h' u) | u. True}" by blast
  then show "h x = h' x"
  proof (coinduct taking: UNIV rule: Stream_equalityI)
    case (EqStream M N)
    then obtain x where MN: "M = h x" "N = h' x" by blast
    from h[of x] h'[of x] MN have "M = CONS (fst (f x)) (h (snd (f x)))"
      and "N = CONS (fst (f x)) (h' (snd (f x)))"
      by force+
    then have ?EqCONS by (auto iff: Id_on_iff)
    then show ?case by blast
  qed
qed

lemma stream_equalityI
  [consumes 1, case_names Eqstream, case_conclusion Eqstream EqSCons]:
  assumes r: "(l1, l2) \<in> r"
    and step: "\<And>q. q \<in> r \<Longrightarrow>
        (\<exists>l1 l2 a b.
          q = (SCons a l1, SCons b l2) \<and> a = b \<and>
            ((l1, l2) \<in> r \<or> l1 = l2))"
      (is "\<And>q. _ \<Longrightarrow> ?EqSCons q")
  shows "l1 = l2"
proof -
  def M \<equiv> "Rep_stream l1" and N \<equiv> "Rep_stream l2"
  with r have "(M, N) \<in> {(Rep_stream l1, Rep_stream l2) | l1 l2. (l1, l2) \<in> r}"
    by blast
  then have "M = N"
  proof (coinduct taking: UNIV rule: Stream_equalityI)
    case (EqStream M N)
    then obtain l1 l2 where
        MN: "M = Rep_stream l1" "N = Rep_stream l2" and r: "(l1, l2) \<in> r"
      by auto
    from step [OF r] show ?case
    proof -
      assume "?EqSCons (l1, l2)"
      with MN have ?EqCONS
        by (force simp add: Rep_stream_SCons EqStream_Id_on intro: Rep_stream_UNIV)
      then show ?case by blast
    qed
  qed
  then show ?thesis by (simp add: M_def N_def Rep_stream_inject)
qed

lemma stream_fun_equalityI
  [case_names SCons, case_conclusion SCons EqSCons]:
  assumes fun_SCons: "\<And>x l.
        (\<exists>l1 l2 a b.
          (f (SCons x l), g (SCons x l)) = (SCons a l1, SCons b l2) \<and>
            a = b \<and> ((l1, l2) \<in> {(f u, g u) | u. True} \<or> l1 = l2))"
      (is "\<And>x l. ?fun_SCons x l")
  shows "f l = g l"
proof -
  have "(f l, g l) \<in> {(f l, g l) | l. True}" by blast
  then show ?thesis
  proof (coinduct rule: stream_equalityI)
    case (Eqstream q)
    then obtain l where q: "q = (f l, g l)" by blast
    show ?case
    proof (cases l)
      case (SCons x l')
      with `?fun_SCons x l'` q SCons show ?thesis by blast
    qed
  qed
qed


subsection {* Derived operations -- both on the set and abstract type *}

subsubsection {* @{text Lconst} *}

definition "Lconst M \<equiv> lfp (\<lambda>N. CONS M N)"

lemma Lconst_fun_mono: "mono (CONS M)"
  by (simp add: monoI CONS_mono)

lemma Lconst: "Lconst M = CONS M (Lconst M)"
  by (rule Lconst_def [THEN def_lfp_unfold]) (rule Lconst_fun_mono)

lemma Lconst_type:
  assumes "M \<in> A"
  shows "Lconst M \<in> Stream A"
proof -
  have "Lconst M \<in> {Lconst (id M)}" by simp
  then show ?thesis
  proof coinduct
    case (Stream N)
    then have "N = Lconst M" by simp
    also have "\<dots> = CONS M (Lconst M)" by (rule Lconst)
    finally have ?CONS using `M \<in> A` by simp
    then show ?case by blast
  qed
qed

lemma Lconst_eq_Stream_corec: "Lconst M = Stream_corec M (\<lambda>x. (x, x))"
  apply (rule equals_Stream_corec)
  apply simp
  apply (rule Lconst)
  done

lemma gfp_Lconst_eq_Stream_corec:
    "gfp (\<lambda>N. CONS M N) = Stream_corec M (\<lambda>x. (x, x))"
  apply (rule equals_Stream_corec)
  apply simp
  apply (rule Lconst_fun_mono [THEN gfp_unfold])
  done


subsubsection {* @{text Smap} and @{text smap} *}

definition
  "Smap f M = Stream_corec M (Stream_case (\<lambda>x M'. (f x, M')))"
definition
  "smap f l = stream_corec l
    (\<lambda>z.
      case z of SCons y z \<Rightarrow> (f y, z))"

lemma Smap_CONS [simp]: "Smap f (CONS M N) = CONS (f M) (Smap f N)"
unfolding Smap_def by (subst Stream_corec) simp

lemma Smap_type:
  assumes M: "M \<in> Stream A"
    and f: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> B"
  shows "Smap f M \<in> Stream B"
proof -
  from M have "Smap f M \<in> {Smap f N | N. N \<in> Stream A}" by blast
  then show ?thesis
  proof coinduct
    case (Stream L)
    then obtain N where L: "L = Smap f N" and N: "N \<in> Stream A" by blast
    from N show ?case
    proof cases
      case (CONS K a)
      with f L have ?CONS by auto
      then show ?thesis by blast
    qed
  qed
qed

lemma Smap_compose:
  assumes M: "M \<in> Stream A"
  shows "Smap (f o g) M = Smap f (Smap g M)"  (is "?lhs M = ?rhs M")
proof -
  have "(?lhs M, ?rhs M) \<in> {(?lhs N, ?rhs N) | N. N \<in> Stream A}"
    using M by blast
  then show ?thesis
  proof (coinduct taking: "range (\<lambda>N. N)" rule: Stream_equalityI)
    case (EqStream L M)
    then obtain N where LM: "L = ?lhs N" "M = ?rhs N" and N: "N \<in> Stream A" by blast
    from N show ?case
    proof cases
      case CONS
      with LM have ?EqCONS by auto
      then show ?thesis by blast
    qed
  qed
qed

lemma Smap_ident:
  assumes M: "M \<in> Stream A"
  shows "Smap (\<lambda>x. x) M = M"  (is "?smap M = _")
proof -
  have "(?smap M, M) \<in> {(?smap N, N) | N. N \<in> Stream A}" using M by blast
  then show ?thesis
  proof (coinduct taking: "range (\<lambda>N. N)" rule: Stream_equalityI)
    case (EqStream L M)
    then obtain N where LM: "L = ?smap N" "M = N" and N: "N \<in> Stream A" by blast
    from N show ?case
    proof cases
      case CONS
      with LM have ?EqCONS by auto
      then show ?thesis by blast
    qed
  qed
qed

lemma smap_LCons [simp, nitpick_simp, code]:
  "smap f (SCons M N) = SCons (f M) (smap f N)"
unfolding smap_def by (subst stream_corec) simp

lemma smap_compose [simp]: "smap (f o g) l = smap f (smap g l)"
  by (coinduct l rule: stream_fun_equalityI) auto

lemma smap_ident [simp]: "smap (\<lambda>x. x) l = l"
  by (coinduct l rule: stream_fun_equalityI) auto


subsection{* iterates *}

text {* @{text stream_fun_equalityI} cannot be used here! *}

definition
  iterates :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
  "iterates f a = stream_corec a (\<lambda>x. (x, f x))"

lemma iterates [nitpick_simp]: "iterates f x = SCons x (iterates f (f x))"
  apply (unfold iterates_def)
  apply (subst stream_corec)
  apply simp
  done

lemma smap_iterates: "smap f (iterates f x) = iterates f (f x)"
proof -
  have "(smap f (iterates f x), iterates f (f x)) \<in>
    {(smap f (iterates f u), iterates f (f u)) | u. True}" by blast
  then show ?thesis
  proof (coinduct rule: stream_equalityI)
    case (Eqstream q)
    then obtain x where q: "q = (smap f (iterates f x), iterates f (f x))"
      by blast
    also have "iterates f (f x) = SCons (f x) (iterates f (f (f x)))"
      by (subst iterates) rule
    also have "iterates f x = SCons x (iterates f (f x))"
      by (subst iterates) rule
    finally have ?EqSCons by auto
    then show ?case by blast
  qed
qed

lemma iterates_smap: "iterates f x = SCons x (smap f (iterates f x))"
  by (subst smap_iterates) (rule iterates)

end
