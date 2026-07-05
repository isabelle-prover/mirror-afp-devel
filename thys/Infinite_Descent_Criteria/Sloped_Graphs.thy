(*Certified Infinite Descent Criteria in Isabelle/HOL *)
(*Authors: Jamie Wright, Liron Cohen, Reuben Rowe and Andrei Popescu*)

subsection "Sloped Graphs"
theory Sloped_Graphs
imports Directed_Graphs
begin


(* SLOPE-DECORATED DIRECTED GRAPHS *)

(* A slope is either Main (i.e., Maintain) or (strictly) Decrease *)
datatype slope = Main | Decr 

lemma slope_exhaust'[simp]:"c \<noteq> Decr \<longleftrightarrow> c = Main" by (auto,meson slope.exhaust) 

instantiation slope :: linorder
begin
fun less_eq_slope :: "slope \<Rightarrow> slope \<Rightarrow> bool" where
"less_eq_slope Decr Main = False"
|"less_eq_slope _ _ = True"
fun less_slope :: "slope \<Rightarrow> slope \<Rightarrow> bool" where
"less_slope Main Decr = True"
|"less_slope _ _ = False"

instance apply standard 
subgoal for x y by (cases x, (cases y, auto)+) 
subgoal for x by (cases x, auto) 
subgoal for x y z by (cases x, (cases y, (cases z, auto))+) 
subgoal for x y by (cases x, (cases y, auto)+) 
subgoal for x y by (cases x, (cases y, auto)+) 
done
end   

(* The set of sloped relations (assumes non-redundancy (single-valuedness)): *)
definition "SlopedRels \<equiv> {P . \<forall>h h' sl1 sl2. P h h' sl1 \<and> P h h' sl2 \<longrightarrow> sl1 = sl2}"

locale Sloped_Graph = Graph Node edge 
for Node :: "'node set" and edge :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
+
(* the positions of a node: *)
fixes PosOf :: "'node \<Rightarrow> 'pos set"
and RR :: "('node \<times> 'pos) \<Rightarrow> ('node \<times> 'pos) \<Rightarrow> slope \<Rightarrow> bool" 
assumes Node_finite: "finite Node"
and PosOf_finite: "\<And>nd. nd \<in> Node \<Longrightarrow> finite (PosOf nd)"
and RR_PosOf: 
"\<And>nd P nd' P' sl. RR (nd,P) (nd',P') sl \<Longrightarrow> {nd,nd'} \<subseteq> Node \<and> P \<in> PosOf nd \<and> P' \<in> PosOf nd'"
and RR_SlopeRels: "\<And>nd nd'. 
  {nd,nd'} \<subseteq> Node \<Longrightarrow> (\<lambda>P P'. RR (nd,P) (nd',P')) \<in> SlopedRels"
begin

lemma finite_Node_opt: "finite ({r. \<exists>x\<in>Node. r = Some x}:: 'node option set)"
  apply(rule finite_imageI[unfolded image_def, of _ Some]) using Node_finite by auto


lemma RR_PosOfD:"RR (nd,P) (nd',P') Main \<or> RR (nd,P) (nd',P') Decr \<Longrightarrow> nd \<in> Node \<and> nd' \<in> Node \<and> P \<in> PosOf nd \<and> P' \<in> PosOf nd'"
  apply(erule disjE) using RR_PosOf by auto

lemma RR_PosOfD':"RR (nd,P) (nd',P') s \<Longrightarrow> nd \<in> Node \<and> nd' \<in> Node \<and> P \<in> PosOf nd \<and> P' \<in> PosOf nd'"
  apply(cases s) using RR_PosOf by auto

lemma alw_shd_stl:"alw (holdsS Node) x \<Longrightarrow> shd(stl x) \<in> Node" by(drule alw_sdrop[of _ x "Suc 0"], drule alwD, unfold holdsS_def, auto)

 
(* Well-formed labeling of nodes with Ps: functional, list and stream versions *)
definition "wfLabF S1 lab \<equiv> \<forall>nd\<in>S1. lab nd \<in> PosOf nd"
definition "wfLabL ndl Pl \<equiv> length ndl = length Pl \<and> (\<forall>i<length ndl. Pl!i \<in> PosOf (ndl!i))"
definition "wfLabS nds Ps \<equiv> ev (alw (holds (\<lambda>(nd,P). P \<in> PosOf nd))) (szip nds Ps) "

definition "wfLabFS Node1 lab \<equiv> \<forall>nd\<in>Node1. lab nd \<noteq> {} \<and> lab nd \<subseteq> PosOf nd"

lemma wfLabFS_finite: "wfLabFS Node1 lab \<Longrightarrow> Node1 \<subseteq> Node \<Longrightarrow> nd\<in>Node1 \<Longrightarrow> finite (lab nd)" 
unfolding wfLabFS_def using infinite_super by (metis in_mono PosOf_finite)

lemma subgr_wfLabFS: 
"subgr Node1 edge1 S2 R2 \<Longrightarrow> wfLabFS S2 lab \<Longrightarrow> wfLabFS Node1 lab"
unfolding subgr_def subsetD wfLabFS_def by auto 
(* NB: For streams, we only care about correct labeling starting 
eventually, not necessarily from the beginning. *)

lemma wfLabS_iff_snth: 
"wfLabS nds Ps \<longleftrightarrow> (\<exists>i. \<forall>j\<ge>i. Ps!!j \<in> PosOf (nds!!j))"
unfolding wfLabS_def ev_alw_holds_iff_snth by auto

lemma path_wfLabF_wfLabL: 
assumes "pathG ndl" and "wfLabF Node lab"
shows "wfLabL ndl (map lab ndl)"
using assms unfolding wfLabF_def wfLabL_def path_iff_nth by auto

lemma ipath_wfLabF_wfLabS: 
assumes "ipath (sdrop i nds)" and "wfLabF Node lab"
shows "wfLabS nds (smap lab nds)"
using assms unfolding wfLabF_def wfLabS_iff_snth ipath_iff_snth sdrop_snth  
using nat_le_iff_add by auto

(* *)

lemma wfLabL_tl: "ndl \<noteq> [] \<Longrightarrow> wfLabL ndl Pl \<Longrightarrow> wfLabL (tl ndl) (tl Pl)"
unfolding wfLabL_def by (simp add: nth_tl)

lemma wfLabL_append: 
"length ndl1 = length Pl1 \<Longrightarrow> length ndl2 = length Pl2 \<Longrightarrow> 
 wfLabL (ndl1 @ ndl2) (Pl1 @ Pl2) \<longleftrightarrow> wfLabL ndl1 Pl1 \<and> wfLabL ndl2 Pl2"
unfolding wfLabL_def apply safe 
  subgoal by (metis length_append nth_append trans_less_add1)
  subgoal by (metis length_append nat_add_left_cancel_less nth_append_length_plus)
  by (auto simp: nth_append)

lemma wfLabL_append_inverse: 
assumes "wfLabL (ndl1 @ ndl2) Pl"
shows "\<exists>Pl1 Pl2. Pl = Pl1 @ Pl2 \<and> wfLabL ndl1 Pl1 \<and> wfLabL ndl2 Pl2"
proof-
  have 0: "length (ndl1 @ ndl2) = length Pl"
        "length ndl1 = length (take (length ndl1) Pl)" 
  using assms wfLabL_def by auto
  show ?thesis
  apply(rule exI[of _ "take (length ndl1) Pl"])
  apply(rule exI[of _ "drop (length ndl1) Pl"])
  using assms unfolding wfLabL_def apply safe
    subgoal by simp
    subgoal by simp
    subgoal for i by (metis length_append nth_append nth_take trans_less_add1)
    subgoal by simp
    subgoal for i by (metis 0 append_take_drop_id length_append nat_add_left_cancel_less 
       nth_append_length_plus) .
qed  

lemma cycle_wfLabL_repeat: 
assumes ndl: "cycleG ndl" and w: "wfLabL ndl Pl" 
shows "wfLabL (repeat n (butlast ndl) @ [last ndl]) (repeat n (butlast Pl) @ [last Pl])"
proof-
  have aux:"cycleG ndl \<Longrightarrow> ndl \<noteq> [] \<Longrightarrow> length ndl = length Pl \<Longrightarrow> \<forall>i<length ndl. Pl ! i \<in> PosOf (ndl ! i) \<Longrightarrow> 2 \<le> length ndl \<Longrightarrow> length Pl = length ndl \<Longrightarrow> length (repeat n (butlast ndl) @ [last ndl]) = length (repeat n (butlast Pl) @ [last Pl])" by simp
  have "ndl \<noteq> [] \<and> length ndl \<ge> 2 \<and> length Pl = length ndl"  
  using cycleG_def assms cycle_iff_nth not_path_Nil wfLabL_def by metis
  thus ?thesis using assms unfolding wfLabL_def apply safe 
    subgoal by auto
    subgoal for i apply(cases "i < length (repeat n (butlast ndl))")
      subgoal unfolding nth_append 
        using One_nat_def Suc_le_lessD Suc_pred length_butlast less_SucI 
         less_le_trans mod_less_divisor 
         nth_butlast numeral_2_eq_2 pos2 repeat_nth zero_less_diff 
        by (smt (verit) nth_repeat)   
      subgoal unfolding nth_append using One_nat_def diff_Suc_less 
        last_conv_nth length_0_conv less_le_trans pos2  
        by (smt (verit, ccfv_threshold) aux diff_self_eq_0 length_Suc_conv_rev linorder_less_linear not_less_eq nth_Cons') . .
qed

(* *)

(* An infinite path has the infinite descent property w.r.t. an Position-decorated 
relation RR provided there exists a trace of Ps that, 
on a tail of the path: 
--- on the one had persists w.r.t. RR (i.e., decreases or stays)
--- one the other hand always eventually decreases w.r.t. RR
NB: 
-- The existence of a tail is captured by the first "eventually"
-- To express this in temporal-logic form, I zip a trace of Ps to the path, and then talk about 
the resulted stream of pairs. 
NB: The definition uses Position streams rather than a node Position-labeling function because 
different Ps are allowed to label the same node a different places in the ipath. 
(More about this later.)
*)

definition descentIpath :: "'node stream \<Rightarrow> 'pos stream \<Rightarrow> bool" where 
"descentIpath nds Ps \<equiv>  
 (ev (alw (holds2 (\<lambda>(nd,P) (nd',P'). RR (nd,P) (nd',P') Main \<or> RR (nd,P) (nd',P') Decr))
     aand
     alw (ev (holds2 (\<lambda>(nd,P) (nd',P'). RR (nd,P) (nd',P') Decr))))
 )
 (szip nds Ps)"

(* Slightly simpler definiton, noting that ev_alw_ev is the same as alw_ev *) 
lemma descentIpath_def2: 
"descentIpath nds Ps \<longleftrightarrow> 
 (ev (alw (holds2 (\<lambda>(nd,P) (nd',P'). RR (nd,P) (nd',P') Main \<or> RR (nd,P) (nd',P') Decr)))
  aand
  alw (ev (holds2 (\<lambda>(nd,P) (nd',P'). RR (nd,P) (nd',P') Decr)))
 )
 (szip nds Ps)"
by (smt alw_ev_sdrop alw_sdrop descentIpath_def ev_iff_sdrop)

(* ... and another version using indices: *)
lemma descentIpath_iff_snth2: 
"descentIpath nds Ps \<longleftrightarrow>
  (\<exists>i. \<forall>j\<ge>i. RR (nds!!j,Ps!!j) (nds!!(Suc j),Ps!!(Suc j)) Main \<or> 
             RR (nds!!j,Ps!!j) (nds!!(Suc j),Ps!!(Suc j)) Decr) 
  \<and> 
  (\<forall>i. \<exists>j\<ge>i. RR (nds!!j,Ps!!j) (nds!!(Suc j),Ps!!(Suc j)) Decr)"
unfolding descentIpath_def2 ev_alw_holds2_iff_snth alw_ev_holds2_iff_snth by simp

lemma descentIpath_iff_snth: 
"descentIpath nds Ps \<longleftrightarrow>
  (\<exists>i. (\<forall>j\<ge>i. RR (nds!!j,Ps!!j) (nds!!(Suc j),Ps!!(Suc j)) Main \<or> 
              RR (nds!!j,Ps!!j) (nds!!(Suc j),Ps!!(Suc j)) Decr) 
       \<and> 
       (\<forall>j\<ge>i. \<exists>k\<ge>j. RR (nds!!k,Ps!!k) (nds!!(Suc k),Ps!!(Suc k)) Decr))"
unfolding descentIpath_iff_snth2 by (meson add_leE order_refl) 

(* The infinite descent property: All ipaths descend. *)
subsection "Infinite Descent"
definition InfiniteDescent :: bool where 
"InfiniteDescent \<equiv> \<forall>nds. ipath nds \<longrightarrow> (\<exists>Ps. descentIpath nds Ps)"


lemma InfiniteDescentE:"InfiniteDescent \<Longrightarrow> ipath nds \<Longrightarrow> (\<And>Ps. descentIpath nds Ps \<Longrightarrow> P) \<Longrightarrow> P" unfolding InfiniteDescent_def by auto
lemma InfiniteDescentI:"(\<And>nds. ipath nds \<Longrightarrow> \<exists>Ps. descentIpath nds Ps)\<Longrightarrow> InfiniteDescent" unfolding InfiniteDescent_def by auto

(* *)

lemma descentIpath_sdrop: "descentIpath (sdrop m nds) (sdrop m Ps) \<longleftrightarrow> descentIpath nds Ps"
unfolding descentIpath_def2 unfolding sdrop_szip[symmetric]  
  using ev_alw_aand_alw_ev_sdrop .

lemma descentIpath_stl: "descentIpath (stl nds) (stl Ps) \<longleftrightarrow> descentIpath nds Ps"
  using descentIpath_sdrop[of "Suc 0" nds Ps] by auto

(* NB: The ipath descent property already implies well-formed labeling, 
so we will not need the latter as an additional hypothesis when we assume the former. 
*)
lemma descentIpath_wfLabS:  
"descentIpath nds Ps \<Longrightarrow> wfLabS nds Ps" 
by (meson RR_PosOf descentIpath_iff_snth2 wfLabS_iff_snth)

lemma descentIpath_sdrop_any: 
"descentIpath (sdrop m nds) Ps' \<Longrightarrow> \<exists> Ps. descentIpath nds Ps"
apply(rule exI[of _ "replicate m any @- Ps'"])
using sdrop_shift_length  
  by (metis descentIpath_sdrop length_replicate)

lemma descentIpath_grow:"descentIpath r1 Ps = descentIpath (x ## r1) (y ## Ps)"
  using descentIpath_sdrop[of "Suc 0" "x##r1" "y##Ps"] unfolding sdrop_1 stream.sel(2) by auto


lemma ipath_stake_cycle:"local.ipath (srepeat u) \<Longrightarrow>
  2 \<le> length u \<Longrightarrow>
  srepeat u !! 0 = srepeat u !! (length u - 1) \<Longrightarrow>
  cycleG u"
  using ipath_stake_sdrop_cycle[of "srepeat u" "length u" 0 ] unfolding stake_srepeat by auto

lemma descentIpath_reduceAll:"\<forall>x. \<not> descentIpath (v @- srepeat u) x \<Longrightarrow>  \<forall>x. \<not> descentIpath (srepeat u) x"
  apply safe
  subgoal for x
    apply(erule allE[of _ "replicate (length v) (shd x) @- x"])
    using descentIpath_sdrop[of "length v" "(v @- srepeat u)" "replicate (length v) (shd x) @- x" ]
    using sdrop_shift_length[of v "length v" "srepeat u"] 
    unfolding sdrop_replicate by auto .


(* Necesssary criterion for infinite descent:  
that each cycle satisfies the finite version of the descent property. 
*)

definition descentPath :: "'node list \<Rightarrow> 'pos list \<Rightarrow> bool" where
"descentPath ndl Pl \<equiv> 
  (\<forall>i. Suc i < length ndl \<longrightarrow> RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) Main \<or> 
                              RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) Decr) \<and> 
  (\<exists>i. Suc i < length ndl \<and> RR (ndl!i,Pl!i) (ndl!(Suc i),Pl!(Suc i)) Decr)"

lemma descentPath_length_wfLabL: 
"descentPath ndl Pl \<Longrightarrow> length Pl = length ndl \<Longrightarrow> wfLabL ndl Pl"
unfolding descentPath_def wfLabL_def  
by (metis (no_types, lifting) RR_PosOf Suc_less_eq2 less_antisym)


(* If the ipath produced from a cycle is descending for some Ps, 
then the cycle is descending for some Ps. 
In contrapositive: The cycle not being descending implies the produced path is not descending *)
lemma cycle_descentIPath_srepeat_imp_descentPath: 
assumes 1: "cycleG ndl" and 2: "descentIpath (srepeat (butlast ndl)) Ps" 
shows "\<exists>Pl. wfLabL ndl Pl \<and> descentPath ndl Pl"
proof-
  have ndl: "ndl \<noteq> [] \<and> butlast ndl \<noteq> [] \<and> length ndl \<ge> 2" 
  using 1 not_path_Nil path_length_ge2 unfolding cycleG_def  
  by (metis append_Nil append_butlast_last_id not_path_singl)
  let ?nds = "srepeat (butlast ndl)"
  obtain i j where 
  a: "\<And>j. j \<ge> i \<Longrightarrow> 
            RR (?nds !! j, Ps !! j) (?nds !! Suc j, Ps !! Suc j) Main \<or>
            RR (?nds !! j, Ps !! j) (?nds !! Suc j, Ps !! Suc j) Decr" and 
  b: "j \<ge> i + length ndl" "RR (?nds !! j, Ps !! j) (?nds !! Suc j, Ps !! Suc j) Decr" 
  using 2 ndl unfolding wfLabS_iff_snth descentIpath_iff_snth2 by blast

  define l where "l \<equiv> (j div (length ndl-1)) * (length ndl-1)"
  have l: "l \<le> j" "j < l + (length ndl-Suc 0)" "l \<ge> i" 
  unfolding l_def apply simp 
  apply (metis One_nat_def Suc_le_lessD add.commute dividend_less_times_div mult.commute ndl numeral_2_eq_2 zero_less_diff)
  by (smt le_diff_conv2 One_nat_def add.commute b(1) diff_le_self dividend_less_div_times lessI nat_le_linear 
     ndl not_less numeral_2_eq_2 order.trans zero_less_diff)
  
  define Pl where "Pl \<equiv> stake (length ndl) (sdrop l Ps)"

  have "length Pl = length ndl" unfolding wfLabL_def 
    unfolding Pl_def using ndl by (auto simp: sdrop_snth)
  hence 0: "wfLabL ndl Pl \<and> descentPath ndl Pl \<longleftrightarrow> descentPath ndl Pl"  
    using descentPath_length_wfLabL by blast
  
  show ?thesis apply(rule exI[of _ Pl]) unfolding 0 unfolding descentPath_def 
  proof (intro allI impI conjI) 

    fix k assume sk: "Suc k < length ndl"
    have [simp]: "i \<le> l + k" by (simp add: l(3) trans_le_add1)

    have [simp]: "butlast ndl ! ((l + k) mod (length ndl - Suc 0)) = ndl!k"  
    by (metis One_nat_def Suc_less_eq Suc_pred l_def length_butlast less_le_trans mod_less 
              mod_mult_self3 ndl nth_butlast pos2 sk)
    have [simp]: "butlast ndl ! (Suc (l + k) mod (length ndl - Suc 0)) = ndl!(Suc k)"
    apply(cases "Suc k < length ndl - 1")
      apply (metis One_nat_def Suc_mod_mult_self3 l_def length_butlast mod_if nth_butlast)
      by (metis "1" One_nat_def Suc_diff_1 Suc_le_lessD Suc_mod_mult_self3 cycle_iff_nth l_def length_butlast less_SucE less_le_trans 
        mod_self nth_butlast numeral_2_eq_2 pos2 sk zero_less_diff)
    have [simp]: "Ps !! (l + k) = Pl ! k"
    by (simp add: Pl_def Suc_lessD sdrop_snth sk)
    have [simp]: "Ps !! Suc (l + k) = Pl ! Suc k"
    by (simp add: Pl_def sdrop_snth sk)

    show "RR (ndl ! k, Pl ! k) (ndl ! Suc k, Pl ! Suc k) Main \<or>
          RR (ndl ! k, Pl ! k) (ndl ! Suc k, Pl ! Suc k) Decr" 
    using ndl a[of "l+k"] by simp 
  next
    define k where k: "k \<equiv> j mod (length ndl-Suc 0)"
    show "\<exists>k. Suc k < length ndl \<and> RR (ndl ! k, Pl ! k) (ndl ! Suc k, Pl ! Suc k) Decr"
    proof(rule exI[of _ k], safe)
      show skk: "Suc k < length ndl"  
      by (metis (no_types, lifting) k One_nat_def Suc_le_lessD Suc_less_eq Suc_pred
        less_le_trans mod_less_divisor ndl numeral_2_eq_2 pos2)
      
      have [simp]: "butlast ndl ! k = ndl ! k"  
      by (metis k One_nat_def Suc_le_lessD length_butlast mod_less_divisor ndl 
          nth_butlast numeral_2_eq_2 zero_less_diff)
      have [simp]: "Ps !! j = Pl ! k"
      unfolding k Pl_def using ndl  
      by (metis One_nat_def Suc_lessD skk div_mult_mod_eq k l_def sdrop_add sdrop_simps(1) stake_nth)
      have [simp]: "Ps !! Suc j = Pl ! Suc k"
      unfolding k Pl_def  
      by (metis (no_types, lifting) ndl One_nat_def Suc_le_lessD Suc_less_eq Suc_pred add_Suc_right 
       div_mult_mod_eq l_def less_le_trans mod_less_divisor numeral_2_eq_2 pos2 sdrop_snth stake_nth)
      have [simp]: "butlast ndl ! (Suc j mod (length ndl - Suc 0)) = ndl ! (Suc k)"
      apply(cases "Suc k < length ndl - Suc 0")
        subgoal using k by auto (smt One_nat_def length_butlast mod_Suc_eq mod_if nth_butlast) 
        subgoal by (metis 1 k One_nat_def Suc_le_lessD cycle_iff_nth length_butlast mod_Suc 
          mod_less_divisor nth_butlast numeral_2_eq_2 zero_less_diff) .
        
      show "RR (ndl ! k, Pl ! k) (ndl ! Suc k, Pl ! Suc k) Decr" 
      using b ndl by (simp add: k[symmetric])
    qed
  qed  
qed 




(* An ipath satisfying descent in a strong sense, i.e., starting from its beginning: *)
definition descentIpathS :: "'node stream \<Rightarrow> 'pos stream \<Rightarrow> bool" where 
"descentIpathS nds Ps \<equiv> 
 (\<forall>i. RR (nds !! i, Ps !! i) (nds !! Suc i, Ps !! Suc i) Main \<or>
      RR (nds !! i, Ps !! i) (nds !! Suc i, Ps !! Suc i) Decr) 
 \<and>
 (\<forall>i. \<exists>j\<ge>i. RR (nds !! j, Ps !! j) (nds !! Suc j, Ps !! Suc j) Decr)"

lemma descentIpathS_imp_descentIpath: 
"descentIpathS nds Ps \<Longrightarrow> descentIpath nds Ps"
unfolding descentIpathS_def descentIpath_iff_snth2 by auto


lemma cycle_descentIPathS_srepeat_imp_descentPath:
"cycleG ndl \<Longrightarrow> descentIpathS (srepeat (butlast ndl)) Ps \<Longrightarrow> 
 \<exists>Pl. wfLabL ndl Pl \<and> descentPath ndl Pl" 
using cycle_descentIPath_srepeat_imp_descentPath descentIpathS_imp_descentIpath by blast

(* The converse of the above: *)
lemma cycle_descentPath_imp_descentIPathS_srepeat: 
assumes "cycleG ndl" and w: "wfLabL ndl Pl" and d: "descentPath ndl Pl" and 
hl: "hd Pl = last Pl"
shows "\<exists>Ps. descentIpathS (srepeat (butlast ndl)) Ps"
proof-
  have "ndl \<noteq> [] \<and> length ndl \<ge> 2" and lPl: "length Pl = length ndl"  
  using cycleG_def assms cycle_iff_nth not_path_Nil wfLabL_def apply metis
  using w wfLabL_def by auto
  have bndl: "butlast ndl \<noteq> []"  
  by (metis cycleG_def not_path_Nil not_path_singl append_Nil 
       append_butlast_last_id assms(1))
  have bPl: "butlast Pl \<noteq> []"  
  by (metis assms(2) bndl length_0_conv length_butlast wfLabL_def)
  
  show ?thesis apply(intro exI[of _ "srepeat (butlast Pl)"]) 
  unfolding descentIpathS_def proof(intro conjI allI)
    fix i
    have 0: "\<And>i. i mod length(butlast ndl) < length (butlast ndl)" 
    "\<And>i. i mod length(butlast Pl) < length (butlast Pl)" 
    apply (metis assms(2) bndl length_butlast length_greater_0_conv 
      mod_less_divisor wfLabL_def)
    by (metis One_nat_def assms(2) bndl length_butlast length_greater_0_conv 
      mod_less_divisor wfLabL_def) 
    define j where j: "j \<equiv> i mod (length (butlast ndl))" 
    have j': "j = i mod length (butlast Pl)" 
      using assms(2) j wfLabL_def by auto
    have 2: "\<And>i. (Suc i) mod (length (butlast ndl)) \<noteq> 0 \<Longrightarrow> 
              (Suc i) mod (length (butlast ndl)) = Suc (i mod (length (butlast ndl)))"
    using mod_Suc by auto
    have 3[simp]: "(Suc i) mod (length (butlast ndl)) = 0 \<Longrightarrow> length (butlast ndl)-1 = j"
    by (metis Zero_not_Suc diff_Suc_1 j mod_Suc)
    have lj[simp]: "Suc j < length ndl" 
    by (metis "0"(1) Suc_eq_plus1 j length_butlast less_diff_conv)

    show "RR (srepeat (butlast ndl) !! i, srepeat (butlast Pl) !! i)
          (srepeat (butlast ndl) !! Suc i, srepeat (butlast Pl) !! Suc i) Main \<or>
         RR (srepeat (butlast ndl) !! i, srepeat (butlast Pl) !! i)
          (srepeat (butlast ndl) !! Suc i, srepeat (butlast Pl) !! Suc i) Decr"
    unfolding srepeat_snth[OF bndl] srepeat_snth[OF bPl]
    unfolding nth_butlast[OF 0(1)] nth_butlast[OF 0(2)] 
    unfolding j[symmetric] j'[symmetric]
    apply(cases "(Suc i) mod (length (butlast ndl)) = 0")
      subgoal using hl d[unfolded descentPath_def, THEN conjunct1, rule_format, OF lj]
      by (metis "3" One_nat_def Suc_pred assms(1) bPl butlast.simps(1) cycle_iff_nth 
        hd_conv_nth lPl last_conv_nth length_butlast length_greater_0_conv)
      subgoal using d unfolding descentPath_def 
      by (metis One_nat_def j lPl length_butlast lj mod_Suc) .
(* *)
    have b: "\<And>i. butlast ndl ! (i mod length (butlast ndl)) = 
       ndl ! (i mod length (butlast ndl))"
    using "0"(1) nth_butlast by blast
    obtain k where k: "Suc k < length ndl"
    "RR (ndl ! k, Pl ! k) (ndl ! Suc k, Pl ! Suc k) Decr"
    using d[unfolded descentPath_def] by auto
    define l where "l \<equiv> i * length (butlast ndl) + k"
    have l: "l mod length (butlast ndl) = k" 
    unfolding l_def by simp (metis Suc_pred assms(1) cycle_iff_nth k(1) mod_less 
     nat_le_linear not_less not_less_eq_eq numeral_2_eq_2)
    have il: "i \<le> l" unfolding l_def  
    by (metis add.commute add_cancel_right_right bndl le_add1 le_less_linear 
      length_0_conv mod_less mod_mult_self4 mult_is_0 trans_le_add2) 
  
    show "\<exists>j\<ge>i. RR (srepeat (butlast ndl) !! j, srepeat (butlast Pl) !! j)
                     (srepeat (butlast ndl) !! Suc j, srepeat (butlast Pl) !! Suc j) Decr"
    apply(rule exI[of _ l]) 
    using k unfolding srepeat_snth[OF bndl] srepeat_snth[OF bPl]
    unfolding nth_butlast[OF 0(1)] nth_butlast[OF 0(2)] l lPl using il  
    by (metis Graph.cycle_iff_nth b  assms(1) hd_conv_nth hl l lPl last_conv_nth 
         length_0_conv length_butlast mod_Suc not_less pos2) 
  qed
qed


lemma cycle_descentPath_repeat_imp_descentIPathS_srepeat: 
assumes ndl: "cycleG ndl" and n: "n \<noteq> 0" and w: "wfLabL (repeat n (butlast ndl) @ [last ndl]) Pl" 
and d: "descentPath (repeat n (butlast ndl) @ [last ndl]) Pl" and "hd Pl = last Pl" 
shows "\<exists>Ps. descentIpathS (srepeat (butlast ndl)) Ps"
proof-
  define ndll where "ndll \<equiv> repeat n (butlast ndl) @ [last ndl]" 
  have 0: "butlast ndll = repeat n (butlast ndl)" unfolding ndll_def by simp
  have "\<exists>Ps. descentIpathS (srepeat (butlast ndll)) Ps"
  apply(rule cycle_descentPath_imp_descentIPathS_srepeat[of _ Pl])
    subgoal  by (simp add: cycle_repeat n ndl ndll_def) 
    subgoal using w ndll_def by blast
    subgoal by (simp add: d ndll_def) 
    subgoal by fact .
  thus ?thesis unfolding 0 by (simp add: n srepeat_repeat) 
qed

(* For omega-cycles, descent implies (hence is equivalent to) strong descent *)
lemma srepeat_cycle_descentIpath_imp_descentIpath: 
assumes ndl: "cycleG ndl" 
and d: "descentIpath (srepeat (butlast ndl)) Ps"
shows "\<exists> Ps. descentIpathS (srepeat (butlast ndl)) Ps"
proof-
  define nds where "nds \<equiv> srepeat (butlast ndl)"
  define l where "l = length ndl - Suc 0"

  have ndl2: "ndl \<noteq> []" "length ndl \<ge> 2" "butlast ndl \<noteq> []" 
  using ndl cycleG_def not_path_Nil apply blast  
  using cycle_iff_nth ndl apply blast
  by (metis cycleG_def not_path_Nil not_path_singl append.simps(1) append_butlast_last_id ndl)
  
  have l: "length (butlast ndl) = l" "l > 0"
  using l_def length_butlast apply simp
  using cycleG_def l_def ndl path_length_ge2 by fastforce

  obtain k where nds: 
  "\<And>i. i \<ge> k \<Longrightarrow> RR (nds !! i, Ps !! i) (nds !! Suc i, Ps !! Suc i) Main \<or>
        RR (nds !! i, Ps !! i) (nds !! Suc i, Ps !! Suc i) Decr"
  "\<And>i. \<exists>j\<ge>i. RR (nds !! j, Ps !! j) (nds !! Suc j, Ps !! Suc j) Decr"
  using d unfolding descentIpath_iff_snth2 nds_def[symmetric] by auto

  obtain n where nlk: "n*l \<ge> k" 
  by (metis One_nat_def l(2) mult.comm_neutral mult_le_mono2 not_less not_less_eq)

  have nds_repeats: "\<And>i. nds!!i = nds !! (n * l + i)"  
    using l(1) ndl2(3) nds_def by auto

  define Qs where "Qs \<equiv> sdrop (n * l) Ps"
  have nth_Qs: "\<And>i. Qs!!i = Ps !! (n * l + i)" 
    by (simp add: Qs_def sdrop_snth)

  show ?thesis apply(rule exI[of _ Qs])
  unfolding descentIpathS_def nds_def[symmetric] nth_Qs apply safe
    subgoal for i
    unfolding nds_repeats[of i] nds_repeats[of "Suc i"]  
    by (metis nlk add_Suc_right dual_order.trans le_add1 nds(1))
    subgoal for i
    using nds(2)[of "n * l + i"] apply safe
      subgoal for j
      apply(rule exI[of _ "j - n * l"])  
      unfolding nds_repeats[of "j - n * l"] nds_repeats[of "Suc (j - n * l)"] by auto
    . .
qed

lemma cycle_descentIPathS_srepeat_imp_descentPath_repeat:
assumes ndl: "cycleG ndl" and d: "descentIpathS (srepeat (butlast ndl)) Ps" 
shows "\<exists>n Pl. n \<noteq> 0 \<and> wfLabL (repeat n (butlast ndl) @ [last ndl]) Pl \<and> 
                                         descentPath (repeat n (butlast ndl) @ [last ndl]) Pl \<and> hd Pl = last Pl"
proof-
  define nds where "nds \<equiv> srepeat (butlast ndl)"
  define nd where "nd \<equiv> hd ndl"
  define l where "l = length ndl - Suc 0"

  have ndl2: "ndl \<noteq> []" "length ndl \<ge> 2" "butlast ndl \<noteq> []" 
  using ndl cycleG_def not_path_Nil apply blast  
  using cycle_iff_nth ndl apply blast
  by (metis cycleG_def not_path_Nil not_path_singl append.simps(1) append_butlast_last_id ndl)
  
  have l: "length (butlast ndl) = l" "l > 0"
  using l_def length_butlast apply simp
  using cycleG_def l_def ndl path_length_ge2 by fastforce

  have nds_repeats: "\<And>n i. nds !! (n * l + i) = nds!!i"  
    using l(1) ndl2(3) nds_def by auto

  have snth_nds: "\<And>ii. nds!!ii = ndl!(ii mod l)" 
  unfolding nds_def 
  by (metis l(1) length_greater_0_conv mod_less_divisor ndl2(3) nth_butlast srepeat_snth)

  have bl_nds: "\<And>ii. butlast ndl ! (ii mod l) = nds !! ii" 
    using l(1) ndl2(3) nds_def by auto

  have nds: 
  "\<And>i. RR (nds !! i, Ps !! i) (nds !! Suc i, Ps !! Suc i) Main \<or>
        RR (nds !! i, Ps !! i) (nds !! Suc i, Ps !! Suc i) Decr"
  "\<And>i. \<exists>j\<ge>i. RR (nds !! j, Ps !! j) (nds !! Suc j, Ps !! Suc j) Decr"
  using d unfolding descentIpathS_def nds_def[symmetric] by auto

  have nd: "nd = last ndl" "\<And>n. nds !! (n*l) = nd"
    subgoal using ndl unfolding nd_def cycleG_def by auto
    subgoal by (simp add: hd_conv_nth nd_def ndl2(1) snth_nds) .

  define f where "f \<equiv> \<lambda>n. Ps !! (n*l)"
  have "range f \<subseteq> (\<Union>nd\<in>Node. PosOf nd)"
  unfolding f_def  using RR_PosOf nds(1) by fastforce
  hence "finite (range f)" by (meson Node_finite finite_UN_I finite_subset PosOf_finite)
  moreover have "UNIV = (\<Union>P. {n. f n = P})" by auto
  ultimately obtain P where P: "infinite {n. f n = P}"  
  by (smt Collect_cong UNIV_I infinite_UNIV_char_0 pigeonhole_infinite)
  hence P2: "\<forall>n. \<exists>m>n. f m = P"  
  using infinite_nat_iff_unbounded by auto

  obtain k0 where k0: "Ps !! (k0*l) = P" using P f_def not_finite_existsD by blast
  obtain j0 where j0: "j0 \<ge> k0*l" 
  "RR (nds !! j0, Ps !! j0) (nds !! Suc j0, Ps !! Suc j0) Decr"
  using nds(2) by blast
  obtain k1 where aux: "k1 > max k0 (Suc j0)" and k1: "Ps !! (k1*l) = P"
  using P2 f_def by blast
  hence "k0 < k1" "j0 < k1*l"  
  by simp (metis aux One_nat_def Suc_lessD Suc_lessI dual_order.strict_trans l(2) 
    max_less_iff_conj mult.right_neutral n_less_n_mult_m zero_less_Suc)
  note k1 = k1 this

  define Pl where "Pl \<equiv> stake (Suc ((k1-k0)*l)) (sdrop (k0*l) Ps)"
  define n where "n \<equiv> k1-k0"

  have l_Pl[simp]: "length Pl = Suc ((k1-k0)*l)" 
    using Pl_def length_stake by blast

  have nth_Pl[simp]: "\<And>i. i<Suc ((k1-k0)*l) \<Longrightarrow> Pl!i = Ps!!(k0*l + i)"
  unfolding Pl_def 
  by (smt Suc_eq_plus1 Suc_le_lessD Suc_pred add.right_neutral leD linorder_neqE_nat 
    not_less0 not_less_eq_eq nth_Cons' 
    plus_1_eq_Suc sdrop.simps(2) sdrop_add sdrop_snth stake_nth)

  show ?thesis 
    proof(intro exI[of _ Pl] exI[of _ n], safe)
    show "0 < n" by (simp add: k1(2) n_def)
    show "wfLabL (repeat n (butlast ndl) @ [last ndl]) Pl"
    unfolding wfLabL_def apply safe
      subgoal by (simp add: n_def l_def)
      subgoal for i unfolding n_def apply(subst nth_Pl)
        subgoal by  (simp add: l_def)
        subgoal apply(cases "i < (k1 - k0) * (length ndl - Suc 0)")
          subgoal apply(subst nth_append) apply(subst repeat_nth)
            subgoal by simp
            subgoal apply simp unfolding l_def[symmetric] bl_nds  
            by (metis RR_PosOf nds(1) nds_repeats) .
          subgoal apply(subst nth_append) 
          by simp (metis RR_PosOf add_mult_distrib l_def 
             less_SucE nd(1) nd(2) nds(1)) . . .
  
    show "descentPath (repeat n (butlast ndl) @ [last ndl]) Pl"
    unfolding descentPath_def proof (intro conjI allI impI)
      fix i
      assume i: "Suc i < length (repeat n (butlast ndl) @ [last ndl])"
      hence ii: "i < n * (length ndl - Suc 0)" by simp
      hence T: "i < n * (length (butlast ndl))" by simp
      show "RR ((repeat n (butlast ndl) @ [last ndl]) ! i, Pl ! i)
          ((repeat n (butlast ndl) @ [last ndl]) ! Suc i, Pl ! Suc i) Main \<or>
         RR ((repeat n (butlast ndl) @ [last ndl]) ! i, Pl ! i)
          ((repeat n (butlast ndl) @ [last ndl]) ! Suc i, Pl ! Suc i) Decr" 
      proof(cases "Suc i < n * (length ndl - Suc 0)")
        case True
        hence TT: "Suc i < n * (length (butlast ndl))" by simp 
        show ?thesis
        unfolding nth_append using T TT apply simp 
        unfolding repeat_nth[OF T] repeat_nth[OF TT]
        unfolding bl_nds l(1) unfolding l_def[symmetric] n_def 
        apply(subst nth_Pl, simp)+
        by (metis add_Suc_right nds(1) nds_repeats) 
      next
        case False
        hence FF: "i = n * (length (butlast ndl)) - Suc 0" 
        using T by auto
        show ?thesis unfolding nth_append using False T apply simp 
        unfolding repeat_nth[OF T] unfolding bl_nds l(1) 
        unfolding l_def[symmetric] n_def nd(1)[symmetric]
        apply(subst nth_Pl, simp)+
        by (metis Suc_lessI add_Suc_right nd(2) nds(1) nds_repeats) 
      qed
    next
      have "Suc (j0 - k0 * l) < n * length ndl - n"
      by (smt Nat.lessE One_nat_def Suc_diff_le Suc_mult_less_cancel1 aux diff_less_mono 
       diff_mult_distrib diff_mult_distrib2 j0(1) k1(3) l(2) 
       l_def le_SucI max_less_iff_conj mult.right_neutral n_def not_less_eq)
      hence [simp]: "Suc (j0 - k0 * l) < n * (length ndl - Suc 0)"
      by (simp add: right_diff_distrib')
      hence [simp]: "j0 - k0 * l < n * (length ndl - Suc 0)" 
      by linarith
      have 0: "Suc (j0 - k0 * l) < n * length (butlast ndl)"
      "j0 - k0 * l < n * length (butlast ndl)" 
      by auto
      have 1: "Suc (j0 - k0 * l) < Suc ((k1 - k0) * l)"  
        using \<open>j0 - k0 * l < n * (length ndl - Suc 0)\<close> l_def n_def by blast
      hence 2: "j0 - k0 * l < Suc ((k1 - k0) * l)" 
        by linarith 
      show "\<exists>i. Suc i < length (repeat n (butlast ndl) @ [last ndl]) \<and>
        RR ((repeat n (butlast ndl) @ [last ndl]) ! i, Pl ! i)
         ((repeat n (butlast ndl) @ [last ndl]) ! Suc i, Pl ! Suc i) Decr"
      apply(rule exI[of _ "j0-k0*l"]) apply safe
        subgoal using diff_mult_distrib j0(1) k1(3) l_def n_def by auto
        subgoal unfolding nth_append apply simp
        unfolding repeat_nth[OF 0(1)] repeat_nth[OF 0(2)]
        unfolding nth_Pl[OF 1] nth_Pl[OF 2] apply(subst nth_butlast)
          subgoal using l(1) l(2) mod_less_divisor by blast
          subgoal apply(subst nth_butlast)
            subgoal using l(1) l(2) mod_less_divisor by blast
            subgoal unfolding l(1) snth_nds[symmetric] 
            by (metis add_Suc_right j0(1) j0(2) le_add_diff_inverse nds_repeats)
            . . . 
     qed
  
     have 0: "hd Pl = Pl!0" "last Pl = Pl ! ((k1-k0)*l)" 
     apply (metis Zero_not_Suc hd_conv_nth l_Pl list.size(3))
     by (metis diff_Suc_1 l_Pl last_conv_nth length_0_conv old.nat.distinct(2))
     show "hd Pl = last Pl" unfolding 0 unfolding Pl_def 
     apply(subst stake_nth)
       subgoal by blast
       subgoal apply(subst stake_nth)
         subgoal by blast 
         unfolding sdrop_snth 
         by simp (metis add_diff_inverse_nat add_mult_distrib k0 k1(1) k1(2) less_imp_triv)
         . 
  qed
qed



definition RRSetChoice :: 
"'node set \<Rightarrow> ('node \<Rightarrow> 'node \<Rightarrow> bool) \<Rightarrow> ('node \<Rightarrow> 'pos set) \<Rightarrow> 
('node \<Rightarrow> 'node \<Rightarrow> 'pos \<Rightarrow> 'pos) \<Rightarrow> bool" where 
"RRSetChoice Node1 edge1 lab f \<equiv> 
 (\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<longrightarrow> f nd nd' ` lab nd \<subseteq> lab nd') \<and>
 (\<forall>nd nd'. {nd,nd'} \<subseteq> Node1 \<and> edge1 nd nd' \<longrightarrow> 
   (\<forall>P \<in> lab nd. RR (nd,P) (nd',f nd nd' P) Main \<or> RR (nd,P) (nd',f nd nd' P) Decr))"


end (* context Sloped_Graph *)



end