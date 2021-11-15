subsection \<open>Instantiation for transition systems\<close>

(*<*)
theory BD_Security_TS
imports Abstract_BD_Security Filtermap Transition_System
begin
(*>*)

declare Let_def[simp]

no_notation relcomp (infixr "O" 75)


locale BD_Security_TS = Transition_System istate validTrans srcOf tgtOf
 for istate :: 'state and validTrans :: "'trans \<Rightarrow> bool"
     and srcOf :: "'trans \<Rightarrow> 'state" and tgtOf :: "'trans \<Rightarrow> 'state"
+
fixes (* value filtering and production:  *)
   \<phi> :: "'trans => bool" and f :: "'trans \<Rightarrow> 'value"
 and (* observation filtering and production: *)
   \<gamma> :: "'trans => bool" and g :: "'trans \<Rightarrow> 'obs"
 and (* declassification trigger:  *)
   T :: "'trans \<Rightarrow> bool"
 and (* declassification bound: *)
   B :: "'value list \<Rightarrow> 'value list \<Rightarrow> bool"
begin

(* The value function: *)
definition V :: "'trans list \<Rightarrow> 'value list" where "V \<equiv> filtermap \<phi> f"
(* The observation function: *)
definition O :: "'trans trace \<Rightarrow> 'obs list" where "O \<equiv> filtermap \<gamma> g"

sublocale Abstract_BD_Security
  where validSystemTrace = "validFrom istate" and V = V and O = O and B = B and TT = "never T" .

lemma O_map_filter: "O tr = map g (filter \<gamma> tr)" unfolding O_def filtermap_map_filter ..
lemma V_map_filter: "V tr = map f (filter \<phi> tr)" unfolding V_def filtermap_map_filter ..

lemma V_simps[simp]:
"V [] = []"  "\<not> \<phi> trn \<Longrightarrow> V (trn # tr) = V tr"  "\<phi> trn \<Longrightarrow> V (trn # tr) = f trn # V tr"
unfolding V_def by auto

lemma V_Cons_unfold: "V (trn # tr) = (if \<phi> trn then f trn # V tr else V tr)"
by auto

lemma O_simps[simp]:
"O [] = []"  "\<not> \<gamma> trn \<Longrightarrow> O (trn # tr) = O tr"  "\<gamma> trn \<Longrightarrow> O (trn # tr) = g trn # O tr"
unfolding O_def by auto

lemma O_Cons_unfold: "O (trn # tr) = (if \<gamma> trn then g trn # O tr else O tr)"
by auto

lemma V_append: "V (tr @ tr1) = V tr @ V tr1"
unfolding V_def using filtermap_append by auto

lemma V_snoc:
"\<not> \<phi> trn \<Longrightarrow> V (tr ## trn) = V tr"  "\<phi> trn \<Longrightarrow> V (tr ## trn) = V tr ## f trn"
unfolding V_def by auto

lemma O_snoc:
"\<not> \<gamma> trn \<Longrightarrow> O (tr ## trn) = O tr"  "\<gamma> trn \<Longrightarrow> O (tr ## trn) = O tr ## g trn"
unfolding O_def by auto

lemma V_Nil_list_ex: "V tr = [] \<longleftrightarrow> \<not> list_ex \<phi> tr"
unfolding V_def using filtermap_Nil_list_ex by auto

lemma V_Nil_never: "V tr = [] \<longleftrightarrow> never \<phi> tr"
unfolding V_def using filtermap_Nil_never by auto

lemma Nil_V_never: "[] = V tr \<longleftrightarrow> never \<phi> tr"
unfolding V_def filtermap_map_filter by (induction tr) auto

lemma list_ex_iff_length_V:
"list_ex \<phi> tr \<longleftrightarrow> length (V tr) > 0"
by (metis V_Nil_list_ex length_greater_0_conv)

lemma length_V: "length (V tr) \<le> length tr"
by (auto simp: V_def length_filtermap)

lemma V_list_all: "V tr = map f tr \<longleftrightarrow> list_all \<phi> tr"
by (auto simp: V_def length_filtermap)

lemma V_eq_Cons:
assumes "V tr = v # vl1"
shows "\<exists> trn tr2 tr1. tr = tr2 @ [trn] @ tr1 \<and> never \<phi> tr2 \<and> \<phi> trn \<and> f trn = v \<and> V tr1 = vl1"
using assms filtermap_eq_Cons unfolding V_def by auto

lemma V_eq_append:
assumes "V tr = vl1 @ vl2"
shows "\<exists> tr1 tr2. tr = tr1 @ tr2 \<and> V tr1 = vl1 \<and> V tr2 = vl2"
using assms filtermap_eq_append[of \<phi> f] unfolding V_def by auto

lemma V_eq_RCons:
assumes "V tr = vl1 ## v"
shows "\<exists> trn tr1 tr2. tr = tr1 @ [trn] @ tr2 \<and> \<phi> trn \<and> f trn = v \<and> V tr1 = vl1 \<and> never \<phi> tr2"
using assms filtermap_eq_RCons[of \<phi> f] unfolding V_def by blast

lemma V_eq_Cons_RCons:
assumes "V tr = v # vl1 ## w"
shows "\<exists> trv trnv tr1 trnw trw.
   tr = trv @ [trnv] @ tr1 @ [trnw] @ trw \<and>
   never \<phi> trv \<and> \<phi> trnv \<and> f trnv = v \<and> V tr1 = vl1 \<and> \<phi> trnw \<and> f trnw = w \<and> never \<phi> trw"
using assms filtermap_eq_Cons_RCons[of \<phi> f] unfolding V_def by blast

lemma O_append: "O (tr @ tr1) = O tr @ O tr1"
unfolding O_def using filtermap_append by auto

lemma O_Nil_list_ex: "O tr = [] \<longleftrightarrow> \<not> list_ex \<gamma> tr"
unfolding O_def using filtermap_Nil_list_ex by auto

lemma O_Nil_never: "O tr = [] \<longleftrightarrow> never \<gamma> tr"
unfolding O_def using filtermap_Nil_never by auto

lemma Nil_O_never: "[] = O tr \<longleftrightarrow> never \<gamma> tr"
unfolding O_def filtermap_map_filter by (induction tr) auto

lemma length_O: "length (O tr) \<le> length tr"
by (auto simp: O_def length_filtermap)

lemma O_list_all: "O tr = map g tr \<longleftrightarrow> list_all \<gamma> tr"
by (auto simp: O_def length_filtermap)

lemma O_eq_Cons:
assumes "O tr = obs # obsl1"
shows "\<exists> trn tr2 tr1. tr = tr2 @ [trn] @ tr1 \<and> never \<gamma> tr2 \<and> \<gamma> trn \<and> g trn = obs \<and> O tr1 = obsl1"
using assms filtermap_eq_Cons unfolding O_def by auto

lemma O_eq_append:
assumes "O tr = obsl1 @ obsl2"
shows "\<exists> tr1 tr2. tr = tr1 @ tr2 \<and> O tr1 = obsl1 \<and> O tr2 = obsl2"
using assms filtermap_eq_append[of \<gamma> g] unfolding O_def by auto

lemma O_eq_RCons:
assumes "O tr = oul1 ## ou"
shows "\<exists> trn tr1 tr2. tr = tr1 @ [trn] @ tr2 \<and> \<gamma> trn \<and> g trn = ou \<and> O tr1 = oul1 \<and> never \<gamma> tr2"
using assms filtermap_eq_RCons[of \<gamma> g] unfolding O_def by blast

lemma O_eq_Cons_RCons:
assumes "O tr0 = ou # oul1 ## ouu"
shows "\<exists> tr trn tr1 trnn trr.
   tr0 = tr @ [trn] @ tr1 @ [trnn] @ trr \<and>
   never \<gamma> tr \<and> \<gamma> trn \<and> g trn = ou \<and> O tr1 = oul1 \<and> \<gamma> trnn \<and> g trnn = ouu \<and> never \<gamma> trr"
using assms filtermap_eq_Cons_RCons[of \<gamma> g] unfolding O_def by blast

lemma O_eq_Cons_RCons_append:
assumes "O tr0 = ou # oul1 ## ouu @ oull"
shows "\<exists> tr trn tr1 trnn trr.
   tr0 = tr @ [trn] @ tr1 @ [trnn] @ trr \<and>
   never \<gamma> tr \<and> \<gamma> trn \<and> g trn = ou \<and> O tr1 = oul1 \<and> \<gamma> trnn \<and> g trnn = ouu \<and> O trr = oull"
proof-
  from O_eq_append[of tr0 "ou # oul1 ## ouu" oull] assms
  obtain tr00 trrr where 1: "tr0 = tr00 @ trrr"
  and 2: "O tr00 = ou # oul1 ## ouu" and 3: "O trrr = oull" by auto
  from O_eq_Cons_RCons[OF 2] obtain tr trn tr1 trnn trr where
  4:"tr00 = tr @ [trn] @ tr1 @ [trnn] @ trr \<and>
     never \<gamma> tr \<and>
     \<gamma> trn \<and> g trn = ou \<and> O tr1 = oul1 \<and> \<gamma> trnn \<and> g trnn = ouu \<and> never \<gamma> trr" by auto
  show ?thesis apply(rule exI[of _ tr], rule exI[of _ trn], rule exI[of _ tr1],
     rule exI[of _ trnn], rule exI[of _ "trr @ trrr"])
  using 1 3 4 by (simp add: O_append O_Nil_never)
qed

lemma O_Nil_tr_Nil: "O tr \<noteq> [] \<Longrightarrow> tr \<noteq> []"
by (induction tr) auto

lemma V_Cons_eq_append: "V (trn # tr) = V [trn] @ V tr"
by (cases "\<phi> trn") auto

lemma set_V: "set (V tr) \<subseteq> {f trn | trn . trn \<in>\<in> tr \<and> \<phi> trn}"
using set_filtermap unfolding V_def .

lemma set_O: "set (O tr) \<subseteq> {g trn | trn . trn \<in>\<in> tr \<and> \<gamma> trn}"
using set_filtermap unfolding O_def .

lemma list_ex_length_O:
assumes "list_ex \<gamma> tr"  shows "length (O tr) > 0"
by (metis assms O_Nil_list_ex length_greater_0_conv)

lemma list_ex_iff_length_O:
"list_ex \<gamma> tr \<longleftrightarrow> length (O tr) > 0"
by (metis O_Nil_list_ex length_greater_0_conv)

lemma length1_O_list_ex_iff:
"length (O tr) > 1 \<Longrightarrow> list_ex \<gamma> tr"
unfolding list_ex_iff_length_O by auto

lemma list_all_O_map: "list_all \<gamma> tr \<Longrightarrow> O tr = map g tr"
using O_list_all by auto

lemma never_O_Nil: "never \<gamma> tr \<Longrightarrow> O tr = []"
using O_Nil_never by auto

lemma list_all_V_map: "list_all \<phi> tr \<Longrightarrow> V tr = map f tr"
using V_list_all by auto

lemma never_V_Nil: "never \<phi> tr \<Longrightarrow> V tr = []"
using V_Nil_never by auto

(* Reachable states by transitions satisfying T: *)
inductive reachNT:: "'state \<Rightarrow> bool" where
Istate: "reachNT istate"
|
Step:
"\<lbrakk>reachNT (srcOf trn); validTrans trn; \<not> T trn\<rbrakk>
 \<Longrightarrow> reachNT (tgtOf trn)"

lemma reachNT_reach: assumes "reachNT s"  shows "reach s"
using assms apply induct by (auto intro: reach.intros)

lemma V_iff_non_\<phi>[simp]: "V (trn # tr) = V tr \<longleftrightarrow> \<not> \<phi> trn"
by (cases "\<phi> trn") auto

lemma V_imp_\<phi>: "V (trn # tr) = v # V tr \<Longrightarrow> \<phi> trn"
by (cases "\<phi> trn") auto

lemma V_imp_Nil: "V (trn # tr) = [] \<Longrightarrow> V tr = []"
by (cases "\<phi> trn") auto

lemma V_iff_Nil[simp]: "V (trn # tr) = [] \<longleftrightarrow> \<not> \<phi> trn \<and> V tr = []"
by (metis V_iff_non_\<phi> V_imp_Nil)

end (* locale BD_Security_TS *)

(*<*)
end
(*>*)
