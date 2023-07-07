section \<open>Indexed Terms\<close>

text \<open>We provide a method to index all subterms of a term by numbers.\<close>

theory Indexed_Term
  imports 
    First_Order_Terms.Subterm_and_Context
begin

type_synonym index = int
type_synonym ('f, 'v) indexed_term = "(('f \<times> ('f,'v)term \<times> index), ('v \<times> ('f,'v)term \<times> index)) term"

fun index_term_aux :: "index \<Rightarrow> ('f, 'v) term \<Rightarrow> index \<times> ('f, 'v) indexed_term"
  and index_term_aux_list :: "index \<Rightarrow> ('f, 'v) term list \<Rightarrow> index \<times> ('f, 'v) indexed_term list"
  where
    "index_term_aux i (Var v) = (i + 1, Var (v,Var v, i))"
  | "index_term_aux i (Fun f ts) = (case index_term_aux_list i ts of (j, ss) \<Rightarrow> (j + 1, Fun (f,Fun f ts,j) ss))" 
  | "index_term_aux_list i [] = (i,[])" 
  | "index_term_aux_list i (t # ts) = (case index_term_aux i t of (j,s) \<Rightarrow> map_prod id (Cons s) (index_term_aux_list j ts))"


definition index_term :: "('f, 'v) term \<Rightarrow> ('f, 'v) indexed_term"
  where
    "index_term t = snd (index_term_aux 0 t)" 

fun unindex :: "('f, 'v) indexed_term \<Rightarrow> ('f, 'v) term"
  where
    "unindex (Var (v,_)) = Var v"
  | "unindex (Fun (f,_) ts) = Fun f (map unindex ts)"

fun stored :: "('f, 'v) indexed_term \<Rightarrow> ('f, 'v) term"
  where
    "stored (Var (v,(s,_))) = s"
  | "stored (Fun (f,(s,_)) ts) = s"

fun name_of :: "('a \<times> 'b) \<Rightarrow> 'a"
  where
    "name_of (a,_) = a"

fun index :: "('f, 'v) indexed_term \<Rightarrow> index"
  where
    "index (Var (_,(_,i))) = i"
  | "index (Fun (_,(_,i)) _) = i"

definition "index_term_prop f s = (\<forall> u. s \<unrhd> u \<longrightarrow> f (index u) = Some (unindex u) \<and> stored u = unindex u)" 

lemma index_term_aux: fixes t :: "('f,'v)term" and ts :: "('f,'v)term list"
  shows "index_term_aux i t = (j,s) \<Longrightarrow> unindex s = t \<and> i < j \<and> (\<exists> f. dom f = {i ..< j} \<and> index_term_prop f s)" 
    and "index_term_aux_list i ts = (j,ss) \<Longrightarrow> map unindex ss = ts \<and> i \<le> j \<and>
    (\<exists> f. dom f = {i ..< j} \<and> Ball (set ss) (index_term_prop f))" 
proof (induct i t and i ts arbitrary: j s and j ss rule: index_term_aux_index_term_aux_list.induct)
  case (1 i v)
  then show ?case by (auto intro!: exI[of _ "(\<lambda> _. None)(i := Some (Var v))"] split: if_splits simp: index_term_prop_def supteq_var_imp_eq) 
next
  case (2 i g ts j s)
  obtain k ss where rec: "index_term_aux_list i ts = (k,ss)" by force
  from 2(2)[unfolded index_term_aux.simps rec split]
  have j: "j = k + 1" and s: "s = Fun (g, Fun g ts, k) ss" by auto
  from 2(1)[OF rec] obtain f where fss: "map unindex ss = ts" and
    ik: "i \<le> k" and f: "dom f = {i..<k}" "\<And> s. s \<in> set ss \<Longrightarrow> index_term_prop f s" 
    by auto
  have set: "{i..< k + 1} = insert k {i..<k}" using ik by auto
  define h where "h = f(k := Some (Fun g ts))" 
  show ?case unfolding s unindex.simps fss j set index_term_prop_def
  proof (intro conjI exI[of _ h] refl allI)
    show "i < k + 1" using ik by simp
    show "dom h = insert k {i..<k}" using ik f(1) unfolding h_def by auto
    fix u
    show "Fun (g, Fun g ts, k) ss \<unrhd> u \<longrightarrow> h (index u) = Some (unindex u) \<and> stored u = unindex u" 
    proof (cases "u = Fun (g, Fun g ts, k) ss")
      case True
      thus ?thesis by (auto simp: fss h_def index_term_prop_def)
    next
      case False
      show ?thesis
      proof (intro impI)
        assume "Fun (g, Fun g ts, k) ss \<unrhd> u" 
        with False obtain si where "si \<in> set ss" and "si \<unrhd> u"
          by (metis Fun_supt suptI)
        from f(2)[unfolded index_term_prop_def, rule_format, OF this] f(1) ik 
        show "h (index u) = Some (unindex u) \<and> stored u = unindex u" unfolding h_def by auto
      qed
    qed
  qed
next
  case (4 i t ts j sss)
  obtain k s where rec1: "index_term_aux i t = (k,s)" by force
  with 4(3) obtain ss where rec2: "index_term_aux_list k ts = (j,ss)" and sss: "sss = s # ss" 
    by (cases "index_term_aux_list k ts", auto)
  from 4(1)[OF rec1] obtain f where fs: "unindex s = t" and ik: "i < k" and f: "dom f = {i..<k}" 
    "index_term_prop f s" by auto
  from 4(2)[unfolded rec1, OF refl rec2] obtain g where fss: "map unindex ss = ts" and kj: "k \<le> j" 
    and g: "dom g = {k..<j}" "\<And> si. si \<in> set ss \<Longrightarrow> index_term_prop g si"  
    by auto
  define h where "h = (\<lambda> n. if n \<in> {i..<k} then f n else g n)" 
  show ?case unfolding sss list.simps fs fss
  proof (intro conjI exI[of _ h] refl allI ballI)
    have "dom h = {i ..< k} \<union> {k ..< j}" unfolding h_def using f(1) g(1) by force
    also have "\<dots> = {i ..< j}" using ik kj by auto
    finally show "dom h = {i..<j}" by auto
    show "i \<le> j" using ik kj by auto
    fix si
    assume si: "si \<in> insert s (set ss)"
    show "index_term_prop h si"
    proof (cases "si = s")
      case True
      from f show ?thesis unfolding True h_def index_term_prop_def by auto
    next
      case False
      with si have si: "si \<in> set ss" by auto
      have disj: "{i..<k} \<inter> {k..<j} = {}" by auto
      from g(1) g(2)[OF si]
      show ?thesis unfolding index_term_prop_def h_def using disj
        by (metis disjoint_iff domI)
    qed
  qed
qed auto


lemma index_term_index_unindex: "\<exists> f. \<forall> t. index_term s \<unrhd> t \<longrightarrow> f (index t) = unindex t \<and> stored t = unindex t" 
proof -
  obtain t i where aux: "index_term_aux 0 s = (i,t)" by force
  from index_term_aux(1)[OF this] show ?thesis unfolding index_term_def aux index_term_prop_def by force
qed

lemma unindex_index_term[simp]: "unindex (index_term s) = s"
proof -
  obtain t i where aux: "index_term_aux 0 s = (i,t)" by force
  from index_term_aux(1)[OF this] show ?thesis unfolding index_term_def aux by force
qed

end
