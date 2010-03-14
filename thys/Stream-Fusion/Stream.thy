header {* Stream Iterators *}

theory Stream
imports LazyList
begin

subsection {* Type definitions for streams *}

text {* Note that everything is strict in the state type. *}

domain ('a,'s) Step = Done | Skip 's | Yield (lazy 'a) 's

domain ('a,'s) Stream = Stream (lazy "'s \<rightarrow> ('a,'s) Step") 's


subsection {* Converting from streams to lists *}

fixrec
  unfold2 :: "('s \<rightarrow> 'a LList) \<rightarrow> ('a, 's) Step \<rightarrow> 'a LList"
where
  "unfold2\<cdot>u\<cdot>Done = LNil"
| "s \<noteq> \<bottom> \<Longrightarrow> unfold2\<cdot>u\<cdot>(Skip\<cdot>s) = u\<cdot>s"
| "s \<noteq> \<bottom> \<Longrightarrow> unfold2\<cdot>u\<cdot>(Yield\<cdot>x\<cdot>s) = LCons\<cdot>x\<cdot>(u\<cdot>s)"

lemma unfold2_strict [simp]: "unfold2\<cdot>u\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

definition
  unfold1 :: "('s \<rightarrow> ('a, 's) Step) \<rightarrow> ('s \<rightarrow> 'a LList) \<rightarrow> ('s \<rightarrow> 'a LList)"
where
  "unfold1 = (\<Lambda> h u. strictify\<cdot>(\<Lambda> s. unfold2\<cdot>u\<cdot>(h\<cdot>s)))"

lemma unfold1_simps [simp]:
  "unfold1\<cdot>h\<cdot>u\<cdot>\<bottom> = \<bottom>"
  "s \<noteq> \<bottom> \<Longrightarrow> unfold1\<cdot>h\<cdot>u\<cdot>s = unfold2\<cdot>u\<cdot>(h\<cdot>s)"
unfolding unfold1_def by simp_all

definition
  unfold :: "('s \<rightarrow> ('a, 's) Step) \<rightarrow> 's \<rightarrow> 'a LList"
where
  "unfold = (\<Lambda> h. fix\<cdot>(unfold1\<cdot>h))"

lemma unfold_beta: "unfold\<cdot>h = fix\<cdot>(unfold1\<cdot>h)"
unfolding unfold_def by simp

lemma unfold: "unfold\<cdot>h\<cdot>s = unfold1\<cdot>h\<cdot>(unfold\<cdot>h)\<cdot>s"
unfolding unfold_beta by (subst fix_eq, simp)

lemma unfold_ind:
  fixes P :: "('s \<rightarrow> 'a LList) \<Rightarrow> bool"
  assumes adm: "adm P"
  assumes base: "P \<bottom>"
  assumes step: "\<And>u. P u \<Longrightarrow> P (unfold1\<cdot>h\<cdot>u)"
  shows "P (unfold\<cdot>h)"
unfolding unfold_beta by (rule fix_ind [of P, OF adm base step])

fixrec
  unstream :: "('a, 's) Stream \<rightarrow> 'a LList"
where
  "s \<noteq> \<bottom> \<Longrightarrow> unstream\<cdot>(Stream\<cdot>h\<cdot>s) = unfold\<cdot>h\<cdot>s"

lemma unstream_strict [simp]: "unstream\<cdot>\<bottom> = \<bottom>"
by fixrec_simp


subsection {* Converting from lists to streams *}

fixrec
  streamStep :: "('a LList)\<^sub>\<bottom> \<rightarrow> ('a, ('a LList)\<^sub>\<bottom>) Step"
where
  "streamStep\<cdot>(up\<cdot>LNil) = Done"
| "streamStep\<cdot>(up\<cdot>(LCons\<cdot>x\<cdot>xs)) = Yield\<cdot>x\<cdot>(up\<cdot>xs)"

lemma streamStep_strict [simp]: "streamStep\<cdot>(up\<cdot>\<bottom>) = \<bottom>"
by fixrec_simp

fixrec
  stream :: "'a LList \<rightarrow> ('a, ('a LList)\<^sub>\<bottom>) Stream"
where
  "stream\<cdot>xs = Stream\<cdot>streamStep\<cdot>(up\<cdot>xs)"

lemma stream_defined [simp]: "stream\<cdot>xs \<noteq> \<bottom>"
  by simp

lemma unstream_stream [simp]:
  fixes xs :: "'a LList"
  shows "unstream\<cdot>(stream\<cdot>xs) = xs"
by (induct xs, simp_all add: unfold)

declare stream.simps [simp del]


subsection {* Bisimilarity relation on streams *}

definition
  bisimilar :: "('a, 's) Stream \<Rightarrow> ('a, 't) Stream \<Rightarrow> bool" (infix "\<approx>" 50)
where
  "a \<approx> b \<longleftrightarrow> unstream\<cdot>a = unstream\<cdot>b \<and> a \<noteq> \<bottom> \<and> b \<noteq> \<bottom>"

lemma unstream_cong:
  "a \<approx> b \<Longrightarrow> unstream\<cdot>a = unstream\<cdot>b"
    unfolding bisimilar_def by simp

lemma stream_cong:
  "xs = ys \<Longrightarrow> stream\<cdot>xs \<approx> stream\<cdot>ys"
    unfolding bisimilar_def by simp

lemma stream_unstream_cong:
  "a \<approx> b \<Longrightarrow> stream\<cdot>(unstream\<cdot>a) \<approx> b"
    unfolding bisimilar_def by simp

end
