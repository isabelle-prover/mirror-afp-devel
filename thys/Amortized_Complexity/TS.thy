(*  Title:       Competitive Analysis of TS
    Author:      Max Haslbeck
*)
(*<*)
theory TS
imports
OPT2
Phase_Partitioning
Move_to_Front 
List_Factoring
RExp_Var 
begin


text {*
@{thm nodouble_def[simplified, no_vars]}
*}

(*>*)

chapter "TS: another 2-competitve Algorithm"
 
section "Definition of TS"
 

(*<*)  
definition TS_step_d where
"TS_step_d s q = ((
      ( 
        let li = index (snd s) q in
        (if li = length  (snd s) then 0 (* requested for first time *)
        else (let sincelast = take li  (snd s)
          in (let S={x. x < q in (fst s) \<and> count_list sincelast x \<le> 1}
            in
             (if S={} then 0
             else
              (index (fst s) q) - Min ( (index (fst s)) ` S)))
            )
        )      
      )
      ,[]), q#(snd s))"


lemma sf_TS_step_d: "snd (fst (TS_step_d (s,is) q)) = []"
unfolding TS_step_d_def by(simp)

 
(* FIXME: generalizing regular expressions equivalence checking 
          enables relaxing the type here to 'a::linord *)
definition rTS :: "nat list \<Rightarrow> (nat,nat list) alg_on"   where "rTS h = ((\<lambda>s. h), TS_step_d)"
 
fun step2 where
  "step2 (a, is) s q = (is, step s q a)"

lemma step2_splitted: "step2 S s q = (snd S, step s q (fst S))"
apply(cases S) by(simp)

thm stepxy

lemma 1: "x\<noteq>y \<Longrightarrow> q \<in> {x, y}
    \<Longrightarrow> snd (step2 (a, is) [x,y] q) \<in> {[x,y], [y,x]}"
proof -
  case goal1
  have "snd (step2 (a, is) [x,y] q) = step [x,y] q a" by simp
  also have "\<dots> \<in> {[x,y], [y,x]}" apply(rule stepxy)
    using goal1 by simp_all
  finally show ?thesis .
qed

lemma step2_xy: "x\<noteq>y \<Longrightarrow> q \<in> {x, y} \<Longrightarrow> s \<in> {[x,y], [y,x]} 
    \<Longrightarrow> snd (step2 (a, is) s q) \<in> {[x,y], [y,x]}"
    proof(cases "s=[x,y]")
      case True
      assume assms: "x\<noteq>y" "q \<in> {x, y}" 
      show ?thesis unfolding True apply(rule 1) using assms by auto
    next
      case False
      assume assms: "x\<noteq>y" "q \<in> {x, y}" 
      assume "s \<in> {[x,y], [y,x]}"
      with False have t: "s=[y,x]" by simp
      have "snd (step2 (a, is) [y, x] q) \<in> {[y, x], [x, y]}" unfolding t apply(rule 1) using assms by auto
      then show ?thesis unfolding t by blast
    qed

lemma step2_xy2: "x\<noteq>y \<Longrightarrow> q \<in> {x, y} \<Longrightarrow> s \<in> {[x,y], [y,x]} 
    \<Longrightarrow> snd (step2 s' s q) \<in> {[x,y], [y,x]}"
using step2_xy by (metis step2.elims)

 

fun TSstep where
  "TSstep qs n (is,s) 
      = ((qs!n)#is, 
        step s (qs!n) (( 
          let li = index is (qs!n) in
          (if li = length is then 0 (* requested for first time *)
          else (let sincelast = take li is
            in (let S={x. x < (qs!n) in s \<and> count_list sincelast x \<le> 1}
              in
               (if S={} then 0
               else
                (index s (qs!n)) - Min ( (index s) ` S)))
              )
          )
          ),[]))"

lemma TSnopaid: "(snd (fst (snd (rTS initH) is q))) = []"
unfolding rTS_def by(simp add: TS_step_d_def)


abbreviation TSdet where
  "TSdet init initH qs n == config (rTS initH) init (take n qs)"
   
lemma TSdet_Suc: "Suc n \<le> length qs \<Longrightarrow> TSdet init initH qs (Suc n) = Step (rTS initH) (TSdet init initH qs n) (qs!n)"
by(simp add: take_Suc_conv_app_nth config_snoc)

(* now do the proof with TSdet *)

definition s_TS where "s_TS init initH qs n  = fst (TSdet init initH qs n)"

lemma step_xy: "step [x,y] r a \<in> { [x,y], [y,x] }" sorry


lemma s_TS_xy: "x \<noteq> y \<Longrightarrow> set xs \<subseteq> {x,y} \<Longrightarrow> i \<le> length xs
       \<Longrightarrow> s_TS [x,y] h xs i \<in> {[x,y], [y,x]}"
proof (induct i arbitrary: x y) 
  case (Suc i)
  from Suc have ixs: "i < length xs" by auto
  from Suc have "i \<le> length xs" by simp
  from Suc(1)[OF Suc(2) Suc(3) this] have grr: "s_TS [x,y] h xs i \<in> {[x,y], [y,x]}" by simp
  
  thm step2_xy
  have yo: "(xs ! i) \<in> {x,y}" using Suc(3,4) using less_le_trans nth_mem by blast
  show ?case unfolding s_TS_def 
    apply(simp add: take_Suc_conv_app_nth[OF ixs] config'_snoc Step_def split_def)
    using grr[unfolded s_TS_def]
      apply(cases "fst (TSdet [x, y] h xs i) = [x,y]")
        apply(simp) using step_xy apply fast
        apply(simp) using step_xy by fast 
qed (simp add: s_TS_def)
 

definition t_TS    where
"t_TS init initH qs n = index (s_TS init initH qs n) (qs!n)"
definition T_TS   where
"T_TS init initH qs = (\<Sum>i<length qs. t_TS init initH qs i)"

lemma T_TS_T_on: "T_on (rTS initH) init qs = T_TS init initH qs"
unfolding T_on_as_sum T_TS_def
apply(rule setsum.cong)
  apply(simp)
  unfolding t_TS_def by(simp add: t\<^sub>p_def split_def TSnopaid s_TS_def)
 

(* lemma to split the query list *)


lemma sndTSdet: "n\<le>length xs \<Longrightarrow> snd (TSdet init initH xs n) = rev (take n xs) @ initH"
apply(induct n)
  apply(simp add: rTS_def)
  by(simp add: split_def TS_step_d_def take_Suc_conv_app_nth config'_snoc Step_def rTS_def)
  


 


lemma TSdet_append: "n\<le>length xs \<Longrightarrow> TSdet init initH (xs@ys) n
        = TSdet init initH xs n"
apply(induct n) by(simp_all add: split_def nth_append)

lemma TSdet_restart: "TSdet init initH (xs @ zs) (length xs)
     = TSdet (s_TS init initH xs (length xs)) (rev xs @ initH) zs 0" 
apply(simp add: rTS_def s_TS_def prod.exhaust sndTSdet)
unfolding sndTSdet[of "length xs" xs initH init, symmetric, simplified]
by(simp add: rTS_def)
 


lemma TSdet_split: "n \<le> length zs \<Longrightarrow> TSdet init initH (xs @ zs) (length xs + n)
     = TSdet (s_TS init initH xs (length xs)) (rev xs @ initH) zs n"
sorry
(*
proof(induct n)
  case (Suc n)
  then have iH: "TSdet init initH (xs @ zs)
     (length xs + n) =
    TSdet (s_TS init initH xs (length xs))
     (rev xs @ initH) zs n" by auto

  have yeah: "(xs @ zs) ! (length xs + n) = zs ! n" by (simp add: nth_append)

  have "TSdet init initH (xs @ zs) (length xs + Suc n) =
      (case TSdet (s_TS init initH xs (length xs))
     (rev xs @ initH) zs n of
     (is, s) \<Rightarrow>
       step2
        (TS_step_d is s
          ((xs @ zs) ! (length xs + n)))
        s ((xs @ zs) ! (length xs + n)))" by(simp add: iH)
  also have "\<dots> = 
    TSdet (s_TS init initH xs (length xs))
     (rev xs @ initH) zs (Suc n)" by(simp add: yeah)
  finally show ?case .
qed (simp add: TSdet_restart)
 *)

lemma splitdet: "TSdet [x,y] h (u @ v) (length (u @ v))
      = TSdet (fst (TSdet [x,y] h u (length u))) (rev u @ h) v (length v)"
sorry (*
using TSdet_split[of "length v" v "[x,y]" h u, unfolded s_TS_def] by simp
*)

lemma t_TS_append: "n \<in> {..<length ys} \<Longrightarrow> t_TS A B ys n = t_TS A B (ys @ zs) n"
proof -
  assume a: "n \<in> {..<length ys}"
  then have "n < length ys" by auto
  then have jiji: "(ys @ zs) ! n = ys ! n"
  by (auto simp: nth_append)
  from a have a: "n\<le>length ys" by simp
      
  show " t_TS A B ys n
      =  t_TS A B (ys @ zs) n"
      unfolding t_TS_def s_TS_def
      using TSdet_append[OF a] by(simp add: jiji)
qed


lemma splitquerylist: "T_TS init initH (xs@ys)
     = T_TS init initH xs + T_TS (s_TS init initH xs (length xs)) ((rev xs)@initH) ys"
proof (induct ys rule: rev_induct)
  case (snoc y ys)
  have "T_TS init initH (xs @ ys @ [y])
      =  setsum (t_TS init initH (xs @ ys @ [y]))
     {..<length (xs @ ys) + 1}" unfolding T_TS_def  by auto
  also have "\<dots> =  setsum (t_TS init initH (xs @ ys @ [y])) {..<length (xs @ ys)}
          + (t_TS init initH (xs@ys @ [y]) (length (xs @ ys)))" by auto
  also have "\<dots> =  setsum (t_TS init initH (xs @ ys)) {..<length (xs @ ys)}
              + (t_TS init initH (xs@ys @ [y]) (length (xs @ ys)))"
  apply(simp)
  apply(rule setsum.cong)
   apply(simp)
   using t_TS_append[where ys="xs@ys"] by auto
  also have "\<dots> =  setsum (t_TS init initH xs) {..<length xs}
    + setsum (t_TS (s_TS init initH xs (length xs)) (rev xs @ initH) ys) {..<length ys}
    + t_TS init initH (xs@ys @ [y]) (length (xs @ ys))" 
     using snoc[unfolded T_TS_def]  by auto
  also have "\<dots> =  setsum (t_TS init initH xs) {..<length xs}
    + setsum (t_TS (s_TS init initH xs (length xs)) (rev xs @ initH) ys) {..<length ys}
    + t_TS (s_TS init initH xs (length xs)) (rev xs @ initH) (ys @ [y]) (length ys)"
  proof - 
    have a: "TSdet init initH (xs @ ys @ [y]) (length xs + length ys)
      = TSdet (s_TS init initH xs (length xs)) (rev xs @ initH) (ys @ [y]) (length ys)"
        apply(rule TSdet_split) by simp

    have "t_TS init initH (xs@ys @ [y]) (length (xs @ ys))
     = t_TS (s_TS init initH xs (length xs)) (rev xs @ initH) (ys @ [y]) (length ys)"
     apply(simp add: t_TS_def)
     unfolding s_TS_def a by(simp)
    then show ?thesis by auto
  qed
  also have "\<dots> =  setsum (t_TS init initH xs) {..<length xs}
    + setsum (t_TS (s_TS init initH xs (length xs)) (rev xs @ initH) (ys @ [y])) {..<length ys}
    + t_TS (s_TS init initH xs (length xs)) (rev xs @ initH) (ys @ [y]) (length ys)" 
    apply(simp)
    apply(rule setsum.cong)
      apply(simp)
      by(simp add: t_TS_append)
  also have "\<dots> =  setsum (t_TS init initH xs) {..<length xs}
    + setsum (t_TS (s_TS init initH xs (length xs)) (rev xs @ initH) (ys @ [y])) {..<length (ys @ [y])}"
    by auto
  finally show ?case unfolding T_TS_def .
qed (simp add: T_TS_def)
    


subsection "Analysis of the Phases"
 

definition "inv_TS qs x y h = (\<exists>x' y'. s_TS [x,y] h qs (length qs) = [x',y'] \<and> (\<exists>hs. (rev qs @ h) = [x',x']@hs))" 

(*
TS_A   (x+1)yy \<rightarrow>         Plus(Atom (x::nat)) One,(Atom y), (Atom y)]
TS_B   (x+1)yx(yx)*yy \<rightarrow>  Plus(Atom x) One,(Atom y),(Atom x),Star(Times (Atom y)(Atom x)),(Atom y),(Atom y)]
TS_C   (x+1)yx(yx)*x  \<rightarrow>  Plus(Atom x) One,(Atom y),(Atom x),Star(Times (Atom y)(Atom x)),(Atom x)]
TD_D   xx             \<rightarrow>  seq[(Atom x),(Atom x)]
*)

subsubsection "(yx)*?"

lemma TS_yx: "x \<noteq> y \<Longrightarrow> qs \<in> lang (Star(Times (Atom y) (Atom x)))
      \<Longrightarrow> \<exists>hs. h=[x,y]@hs \<Longrightarrow> T_TS [x,y] h (qs@r) = length qs + T_TS [x,y] ((rev qs) @h) r \<and> (\<exists>hs. ((rev qs) @h) = [x, y] @ hs)
        \<and> TSdet [x, y] h qs (length qs) = ([x,y],rev qs @ h)"
proof -
  case goal1
  then have "qs \<in> star ({[y]} @@ {[x]})" by (simp)
  from this goal1(3) show ?case
  proof (induct qs arbitrary: h rule: star_induct)
    case Nil
    then show ?case by(simp add: rTS_def)
  next
    case (append u v)
    then have uyx: "u = [y,x]" by auto
    from append obtain hs where a: "h = [x,y]@hs" by blast
    
    have "rev v @ (rev u @ h) = (rev (u@v) @ h)" by auto
    have "T_TS [x,y] (rev u @ h) (v @ r) = length v + T_TS [x, y] (rev v @ (rev u @ h)) r \<and>
    (\<exists>hs. rev v @ (rev u @ h) = [x, y] @ hs)
    \<and> TSdet [x, y] (rev u @ h) v (length v) = ([x, y], rev v @ (rev u @ h))"
        apply(simp only: uyx) apply(rule append(3)) by simp
    then have yy: "T_TS [x,y] (rev u @ h) (v @ r) = length v + T_TS [x, y] (rev v @ (rev u @ h)) r"
          and history: "(\<exists>hs. rev v @ (rev u @ h) = [x, y] @ hs)"
          and state: "TSdet [x, y] (rev u @ h) v (length v) = ([x, y], rev v @ (rev u @ h))" by auto
    
    have s0: "s_TS [x, y] h [y, x] 0 = [x,y]" unfolding s_TS_def by(simp) 

    from goal1(1) have hahah: " {xa. xa < y in [x, y] \<and> count_list [x] xa \<le> 1} = {x}"
      unfolding before_in_def by auto

    have "(let li = index (x # y # hs) y
                 in if li = length (x # y # hs) then 0
                    else let sincelast = take li (x # y # hs);
                             S = {xa. xa < y in [x, y] \<and> count_list sincelast xa \<le> 1}
                         in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S))
                  = (let S = {xa. xa < y in [x, y] \<and> count_list [x] xa \<le> 1}
                         in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S))" by auto
    also have "\<dots> = (let  S = {x}
                         in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S))" by (simp only: hahah)
    also have "\<dots> = 1" by (simp add: goal1(1))
    finally have tt: "(let li = index (x # y # hs) y
                 in if li = length (x # y # hs) then 0
                    else let sincelast = take li (x # y # hs);
                             S = {xa. xa < y in [x, y] \<and> count_list sincelast xa \<le> 1}
                         in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S)) = 1" .
                         
    have det1: "TSdet [x, y] h [y, x] 1 = ([y,x], ([y, x, y]@hs))" 
      unfolding a apply(simp add: split_def) 
      unfolding rTS_def Step_def apply(simp only: fst_conv snd_conv TS_step_d_def)
        apply(simp only: tt) by(simp add:  step_def mtf2_def swap_def)  

    then have s1: "s_TS [x, y] h [y, x] (Suc 0) = [y,x]" unfolding a unfolding s_TS_def by auto
                   
    have det2: "TSdet [x, y] h [y, x] (Suc 1) = ([x,y],([x, y, x, y]@hs))" 
      apply(subst TSdet_Suc)
        apply(simp) 
        apply(simp only: det1) unfolding rTS_def Step_def apply(simp only: fst_conv snd_conv TS_step_d_def)
        unfolding before_in_def using goal1(1) apply(auto) unfolding step_def mtf2_def by(simp add: swap_def)

    then have s2: "s_TS [x, y] h u (length u) = [x,y]" unfolding uyx a unfolding s_TS_def by simp
      
    have ta: "T_TS [x, y] h u = 2"
        unfolding T_TS_def uyx apply(simp) unfolding t_TS_def
        unfolding s0 s1 using goal1(1) by (simp)

 (*   have helper:"(step2 (TS_step_d ([x, y], h) y) [x, y] y) = ([y,x], y#h)"
        unfolding a using goal1(1) apply(auto simp add: TS_step_d_def step_def before_in_def)
        by(simp add: mtf2_def swap_def) *)

    have helper2: "fst (TSdet [x, y] h u (length u)) = [x,y]"
    unfolding uyx using det2 by simp
 
    have "TSdet [x, y] h (u @ v) (length u + length v) =
          TSdet (fst (TSdet [x, y] h u (length u))) (rev u @ h) v (length v)"
            using splitdet by auto
    also have "\<dots> = TSdet [x,y] (rev u @ h) v (length v)"
      by(simp only: helper2)
    also have "\<dots> = ([x, y], rev v @ rev u @ h)" by (simp only: state)
    finally have alles: "TSdet [x, y] h (u @ v) (length u + length v) =
                  ([x, y], rev v @ rev u @ h)" .

    thm splitquerylist
    have "T_TS [x, y] h ((u @ v) @ r) = T_TS [x, y] h (u @ (v @ r))" by auto
    also have "\<dots>
        = T_TS [x, y] h u + T_TS (s_TS [x,y] h u (length u)) (rev u @ h) (v @ r)"
        by(rule splitquerylist)
    also have "\<dots> = T_TS [x, y] h u + T_TS [x,y] (rev u @ h) (v @ r)" by(simp only: s2) 
    also have "\<dots> = T_TS [x, y] h u + length v + T_TS [x, y] (rev v @ (rev u @ h)) r" by(simp only: yy) 
    also have "\<dots> = 2 + length v + T_TS [x, y] (rev v @ (rev u @ h)) r" by(simp only: ta) 
    also have "\<dots> = length (u @ v) + T_TS [x, y] (rev v @ (rev u @ h)) r" using uyx by auto
    also have "\<dots> = length (u @ v) + T_TS [x, y] (rev (u@ v) @ h) r" by auto
    finally show ?case using history alles by simp   
  qed
qed

subsubsection "?x"

lemma TS_x: "x \<noteq> y \<Longrightarrow> \<exists>hs. h = [x, y] @ hs \<Longrightarrow>
         T_TS [x, y] h [x] = 0 \<and> TSdet [x, y] h [x] (length [x]) = ([x,y], rev [x] @ h)"
proof -
  case goal1
  then obtain hs where a: "h = [x,y]@hs" by blast
  then show ?case 
        unfolding T_TS_def apply(simp) unfolding  t_TS_def
        unfolding s_TS_def apply(simp) 
        unfolding rTS_def Step_def  by (simp add: TS_step_d_def step_def)
  qed

subsubsection "?yy"

lemma TS_xx: "x \<noteq> y \<Longrightarrow> u\<in>{[x,y],[y,x]} \<Longrightarrow> TSdet u hs [y,y] (length [y,y]) = ([y,x], rev [y,y] @ hs)"
proof -
  assume xny: "x \<noteq> y"
  assume u: "u\<in>{[x,y],[y,x]}"


  from xny have indi: "index (x # y # hs) y = 1" by simp
  from xny have puh: "{xa. xa < y in [x, y] \<and> count_list [x] xa \<le> 1} = {x}" apply(auto)
    unfolding before_in_def apply(auto) using add_is_0 by fastforce
 
   let ?expr = "((let li = index hs y in if li = length hs then 0 else let sincelast =
          take li hs; S = {x. x < y in u \<and> count_list sincelast x \<le> 1}
    in if S = {} then 0 else index u y - Min (index u ` S), []), y # hs)"
   have "fst (TSdet u hs [y,y] 1) = step u y (fst ?expr)" apply(simp)       
    unfolding rTS_def Step_def apply(simp only: fst_conv snd_conv TS_step_d_def) 
    by(auto)
   also have "\<dots> \<in> {[x,y],[y,x]}"
    using u
    apply(cases "u=[x,y]")
         apply(simp only: step_xy)
         by(simp add: step_def) 
   finally have "fst (TSdet u hs [y,y] 1) \<in> {[x,y],[y,x]}" .

  then have det2: "TSdet u hs [y, y] (Suc 1) = ([y,x],([y,y]@hs))" 
    apply(subst TSdet_Suc)
      apply(simp) 
      apply(subst surjective_pairing[of "(TSdet u hs [y, y] 1)"])
      apply(subst sndTSdet)
        apply(simp)
        apply(auto simp del: config'.simps)
        using u xny apply(simp add: Step_def split_def rTS_def TS_step_d_def step_def mtf2_def swap_def before_in_def)
        unfolding Step_def rTS_def by(simp add: split_def TS_step_d_def step_def) 

  then show ?thesis by auto
qed


lemma TS_yy: "x \<noteq> y \<Longrightarrow> \<exists>hs. h = [x, y] @ hs \<Longrightarrow>
         T_TS [x, y] h [y, y] = 1 \<and> TSdet [x, y] h [y,y] (length [y,y]) = ([y,x],rev [y,y] @ h)"
proof -
  case goal1
  then obtain hs where a: "h = [x,y]@hs" by blast
    have s0: "s_TS [x, y] ([x, y]@hs) [y, y] 0 = [x,y]" unfolding s_TS_def by(simp) 

    have det0: "TSdet [x, y] ([x, y]@hs) [y, y] 0 = ([x,y],[x, y]@hs)" by(simp add: rTS_def) 


    from goal1(1) have indi: "index (x # y # hs) y = 1" by simp
    from goal1(1) have puh: "{xa. xa < y in [x, y] \<and> count_list [x] xa \<le> 1} = {x}" apply(auto)
      unfolding before_in_def apply(auto) using add_is_0 by fastforce

    from goal1(1) have "(let li = index (x # y # hs) y
                 in if li = length (x # y # hs) then 0
                    else let sincelast = take li (x # y # hs);
                             S = {xa. xa < y in [x, y] \<and> count_list sincelast xa \<le> 1}
                         in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S))
                   = (let S = {xa. xa < y in [x, y] \<and> count_list [x] xa \<le> 1}
                         in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S))" by(simp)
    also have "\<dots> = (let S = {x}
                         in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S))"
                          by (simp only: puh)
    also have "\<dots> = 1" apply(auto) using goal1(1) by simp
    finally have hhuu: "(let li = index (x # y # hs) y
                 in if li = length (x # y # hs) then 0
                    else let sincelast = take li (x # y # hs);
                             S = {xa. xa < y in [x, y] \<and> count_list sincelast xa \<le> 1}
                         in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S)) = 1" .

    have "length (x # y # hs) \<ge> 2" by auto

    have det1: "TSdet [x, y] ([x, y]@hs) [y,y] 1 = ([y,x],([y, x, y]@hs))"
      unfolding a apply(simp add: split_def) 
      unfolding rTS_def Step_def apply(simp only: fst_conv snd_conv TS_step_d_def)
        apply(simp only: hhuu) by(simp add:  step_def mtf2_def swap_def) 

    then have s1:  "s_TS [x, y] ([x, y]@hs) [y, y] 1 = [y,x]" unfolding s_TS_def by simp
 
    have det2: "TSdet [x, y] ([x, y]@hs) [y, y] (length [y,y]) = ([y,x],(rev [y,y]@([x, y]@hs)))"
      apply(rule TS_xx)
        apply(fact) by(simp) 


    from a have cost: "T_TS [x,y] ([x,y]@ hs) [y,y] = 1"
        unfolding T_TS_def apply(simp) unfolding  t_TS_def
         apply(simp add: split_def s0[simplified] s1[simplified]) using goal1(1) by auto
    show ?case
      apply(safe)
         unfolding a apply(fact cost)
         using det2 by(simp del: config'.simps) 
  qed

subsubsection "yx(yx)*?"

lemma TS_yxyx: "x \<noteq> y \<Longrightarrow> qs \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
      \<Longrightarrow> (\<exists>hs. h=[x,x]@hs) \<or> index h y = length h \<Longrightarrow> T_TS [x,y] h (qs@r) = length qs - 1 + T_TS [x,y] (rev qs @ h) r \<and> (\<exists>hs. (rev qs @ h) = [x, y] @ hs)
            \<and> TSdet [x, y] h qs (length qs) = ([x,y], rev qs @ h)"
proof -
  case goal1
  obtain u v where uu: "u \<in> lang (Times (Atom y) (Atom x))"
                      and vv: "v \<in> lang (seq[ Star(Times (Atom y) (Atom x))])"
                      and qsuv: "qs = u @ v" 
                      using goal1(2)
                      by (auto simp: conc_def)  
  from uu have uyx: "u = [y,x]" by(auto)

  from qsuv uyx have vqs: "length v = length qs - 2" by auto
  from qsuv uyx  have vqs2: "length v + 1 = length qs - 1" by auto

  
  have s0: "s_TS [x, y] h [y, x] 0 = [x,y]" unfolding s_TS_def by(simp) 

  from goal1(1) have hahah: " {xa. xa < y in [x, y] \<and> count_list [x] xa \<le> 1} = {x}"
    unfolding before_in_def by auto

    have det1: "TSdet [x, y] h [y] (Suc 0) = ([x,y],y#h)"  
      apply(simp)
      unfolding rTS_def Step_def apply(simp only: fst_conv snd_conv TS_step_d_def)       
        proof (cases "index h y = length h")
          case False
          with goal1(3) obtain hs where "h = [x,x]@hs" by auto
          with False have "(let li = index h y
       in if li = length h then 0
          else let sincelast = take li h;
                   S = {xa.
  xa < y in [x, y] \<and>
  count_list sincelast xa \<le> 1}
               in if S = {} then 0
                  else index [x, y] y - Min (index [x, y] ` S)) =  0" by auto
          then show "(let (a, ya) =
           ((let li = index h y
             in if li = length h then 0
                else let sincelast = take li h;
                         S = {xa.
                              xa < y in [x, y] \<and>
                              count_list sincelast xa \<le> 1}
                     in if S = {} then 0
                        else index [x, y] y -
                             Min (index [x, y] ` S),
             []),
            y # h)
     in (step [x, y] y a, ya)) =
    ([x, y], y # h)" by(simp add: step_def)
      qed (simp add: step_def)

    then have s1: "s_TS [x, y] h [y, x] (Suc 0) = [x,y]" unfolding s_TS_def by auto

    have det2: "TSdet [x, y] h [y, x] (Suc (Suc 0)) = ([x,y],[x, y]@h)"
      apply(subst TSdet_Suc)
        apply(simp)
        using det1 apply(simp add: nth.simps  del: config'.simps)
        unfolding rTS_def Step_def apply(simp only: fst_conv snd_conv TS_step_d_def) 
        unfolding before_in_def using goal1(1) apply(auto) unfolding step_def mtf2_def 
          by(simp add: swap_def)

    then have s2: "s_TS [x, y] h u (length u) = [x,y]" unfolding uyx unfolding s_TS_def by simp
      
    have ta: "T_TS [x, y] h u = 1"
      unfolding T_TS_def uyx apply(simp) unfolding t_TS_def
      unfolding s0 s1 using goal1(1) by (simp)

      (* instead of TS_b1 use TS_yx *)
      thm TS_yx

   
    have ttt: " T_TS [x,y] (rev u @ h) (v@r) = 
          length v + T_TS [x, y] (rev v @ (rev u @ h)) r \<and>
              (\<exists>hs. rev v @  (rev u @ h) = [x, y] @ hs)
        \<and> TSdet [x, y] (rev u @ h) v (length v) = ([x,y],rev v @ rev u @ h)"
        apply(rule TS_yx)
      apply(fact)
      using vv apply(simp)
      using uyx by(simp)
      thm TS_yy
    then have tat: "T_TS [x,y] (rev u @ h) (v@r) =  
          length v + T_TS [x, y] (rev qs @ h) r" 
          and history:  "(\<exists>hs. rev v @  (rev u @ h) = [x, y] @ hs)"
          and state: "TSdet [x, y] (rev u @ h) v (length v) = ([x,y],rev v @ rev u @ h)" using qsuv
          by auto
    

 
    have 1: "fst (TSdet [x, y] h u (length u)) = [x,y]"
    unfolding uyx using det2 by simp

     have his: "TSdet [x, y] h qs (length qs) = ([x, y], rev qs @ h)"
      unfolding qsuv apply(subst splitdet) apply(simp only: 1 state) by auto

  thm splitquerylist
  have "T_TS [x, y] h (qs@r) = T_TS [x, y] h (u @ v @ r)" using qsuv  by auto
  also have "\<dots>
      = T_TS [x, y] h u + T_TS (s_TS [x,y] h u (length u)) (rev u @ h) (v @ r)"
      by(rule splitquerylist)
  also have "\<dots> = T_TS [x, y] h u + T_TS [x,y] (rev u @ h) (v@r)" by(simp only: s2) 
  also have "\<dots> = T_TS [x, y] h u + length v + T_TS [x, y] (rev qs @ h) r" by (simp only: tat) 
  also have "\<dots> = 1 + length v + T_TS [x, y] (rev qs @ h) r" by(simp only: ta) 
  also have "\<dots> = length qs - 1 + T_TS [x, y] (rev qs @ h) r" using vqs2 by auto
  finally show ?case 
    apply(safe)
    using history qsuv apply(simp)
    using his by auto                           
qed



lemma TS_xr: "x \<noteq> y \<Longrightarrow>
  qs \<in> lang (Plus (Atom x) One) \<Longrightarrow>
   h = [] \<or> (\<exists>hs. h = [x, x] @ hs) 
    \<Longrightarrow> T_TS [x, y] h (qs@r) = T_TS [x,y] (rev qs @ h) r
          \<and> ((\<exists>hs. (rev qs @ h) = [x, x] @ hs) \<or> (rev qs @ h) = [x] \<or> (rev qs @ h)=[]) " 
proof -
  case goal1
  then have alt: "qs=[] \<or> qs=[x]" by auto
  then have s: "s_TS [x,y] h qs (length qs) = [x,y]"
    by (auto simp: Step_def rTS_def s_TS_def TS_step_d_def step_def) 

  from alt have t: "T_TS [x, y] h qs = 0"
    by(auto simp: T_TS_def t_TS_def s_TS_def Step_def rTS_def)


  from goal1 have setux: "set qs \<subseteq> {x}" using atoms_lang by fastforce

  have fall': "(\<exists>hs. (rev qs @ h) = [x, x] @ hs) \<or> (rev qs @ h)=[x] \<or> (rev qs @ h)=[]"
    using alt goal1 by(auto) 


  have "T_TS [x, y] h (qs@r) =  T_TS [x, y] h qs + T_TS (s_TS [x,y] h qs (length qs)) (rev qs @ h) r"
      by(rule splitquerylist)
  also have "\<dots>
      = T_TS [x,y] (rev qs @ h) r" by(simp add: s t)
  finally show ?case using fall' by simp
qed


subsubsection "(x+1)yx(yx)*yy"


lemma ts_b: "x \<noteq> y \<Longrightarrow>
  v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y]) \<Longrightarrow>
  (\<exists>hs. h = [x, x] @ hs) \<or> h = [x] \<or> h = []
    \<Longrightarrow> T_TS [x, y] h v = (length v - 2)
            \<and>  (s_TS [x,y] h v (length v) = [y,x] \<and> (\<exists>hs. (rev v @ h) = [y,y]@hs))"
proof - 
  case goal1 
  from goal1 have lenvmod: "length v mod 2 = 0" apply(simp)
  proof -
    assume "v \<in> ({[y]} @@ {[x]}) @@ star ({[y]} @@ {[x]}) @@ {[y]} @@ {[y]}"
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in> {[y]} @@ {[y]}" by (metis concE)
    then have "p = [y,x]" "r=[y,y]" by auto
    with pqr have a: "length v = 4+length q" by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show ?thesis by auto
  qed

  with goal1(1,3) have fall: "(\<exists>hs. h = [x, x] @ hs) \<or> index h y = length h"
    by(auto) 
 

  from goal1(2) have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom y, Atom y])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom y, Atom y])"
                      and vab: "v = a @ b" 
                      by(erule concE) 
  then have bb: "b=[y,y]" by auto
  from aa have lena: "length a > 0" by auto
 
  from TS_yxyx[OF goal1(1) aa fall] have stars: "T_TS [x, y] h (a @ b) =
    length a - 1 + T_TS [x, y] (rev a @ h) b" 
    and history: "(\<exists>hs. rev a @ h = [x, y] @ hs)"
    and state: "TSdet [x, y] h a (length a) = ([x,y],rev a @ h)" by auto
  thm TS_yy
  have suffix: "T_TS [x, y] (rev a @ h) b = 1
                 \<and> TSdet [x, y] (rev a @ h) b (length b) = ([y,x],rev b @ rev a @ h)" unfolding bb apply(rule TS_yy)
    apply(fact)
    using history by simp
  then have jajajaj: "TSdet [x, y] (rev a @ h) b (length b) = ([y,x],rev b @ rev a @ h)" by auto

  from stars suffix have "T_TS [x, y] h (a @ b) = length a" using lena by auto
  then have whatineed: "T_TS [x, y] h v = (length v - 2)" using vab bb by auto
  
  (* was hinten raus kommt *)
 
  have splitdet2: "TSdet [x, y] h (a @ [y, y]) (length (a @ [y, y]))
      = TSdet (fst (TSdet [x,y] h a (length a))) (rev a @ h) [y, y] (length [y, y])"
      using splitdet[of h x y a "[y,y]"] by auto
 
  have ta: "fst ([x, y], rev a @ h) = [x,y]" by auto

  have grgr:"fst (TSdet [x, y] h v (length v)) = [y, x]"
     unfolding vab bb
    apply(simp only: splitdet2) apply(simp only: state)
    apply(simp only: ta jajajaj[unfolded bb]) by simp 

  from history obtain hs' where "rev a @ h = [x, y] @ hs'" by auto
  then obtain hs2 where reva: "rev a @ h = x # hs2" by auto

  show ?case using whatineed
    apply(auto) 
      using grgr apply(simp add: s_TS_def )
      by(simp add: reva vab bb)
qed

lemma TS_b': "qs \<in> Lxx x y \<Longrightarrow>
    x \<noteq> y \<Longrightarrow>
    h = [] \<or> (\<exists>hs. h = [x, x] @ hs) \<Longrightarrow>
    qs
    \<in> lang (seq [Plus (Atom x) rexp.One, Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y]) \<Longrightarrow>
    T_TS [x, y] h qs
    \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) \<and> inv_TS qs x y h"
proof -
  case goal1
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
        and qsuv: "qs = u @ v" 
        using goal1(4)
        by (auto simp: conc_def)   
 
  from TS_xr[OF goal1(2) uu goal1(3), of v] have
              T_pre: "T_TS [x, y] h (u@v) = T_TS [x,y] (rev u @ h) v"
          and fall': "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> (rev u @ h) = [x] \<or> (rev u @ h)=[]" by auto
      
  with goal1 uu have fall: "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> index (rev u @ h) y = length (rev u @ h)"
    by(auto) 

  from ts_b[OF goal1(2) vv fall'] have
              T_star: "T_TS [x, y] (rev u @ h) v = length v - 2"
          and inv1:   "s_TS [x, y] (rev u @ h) v (length v) = [y, x]"
          and inv2:   "(\<exists>hs. rev v @ rev u @ h = [y, y] @ hs)" by auto

  from T_pre T_star qsuv have TS: "T_TS [x, y] h qs = (length v - 2)" by metis

  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x, Star (Times (Atom y) (Atom x)), Atom y, Atom y])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_B) by(fact)+


  (* was hinten raus kommt *)

  have splitdet1: "TSdet [x,y] h (u @ v) (length (u @ v))
      = TSdet (fst (TSdet [x,y] h u (length u))) (rev u @ h) v (length v)" 
        using splitdet by auto 

  have first: "fst (TSdet [x,y] h u (length u)) = [x,y]"
    apply(cases "u=[]")
      apply(simp add: rTS_def)
      using uu by(simp add: rTS_def Step_def TS_step_d_def step_def)
  
  have 1: "s_TS [x, y] h qs (length qs) = [y, x]"
    unfolding s_TS_def qsuv apply(simp only: splitdet1)
    by(simp only: first inv1[unfolded s_TS_def]) 
 
  show ?case unfolding TS OPT
    apply(auto)
     unfolding inv_TS_def
     apply(rule exI[where x="y"])
     apply(rule exI[where x="x"]) 
      using 1 inv2 qsuv by(auto) 
qed


subsubsection "(x+1)yy"




lemma ts_a: "x \<noteq> y \<Longrightarrow>
  qs \<in> lang (seq [Plus (Atom x) One, Atom y, Atom y]) \<Longrightarrow>
   h = [] \<or> (\<exists>hs. h = [x, x] @ hs) \<Longrightarrow> 
    T_TS [x, y] h qs = 2
     \<and>  inv_TS qs x y h"
proof -                                             
  case goal1
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Atom y, Atom y])"
        and qsuv: "qs = u @ v" 
        using goal1(2)
        by (auto simp: conc_def) 
  
  thm star_unfold_left

  from vv have vv2: "v = [y,y]" by auto
  then have vv3: "v \<in> lang (seq [Star (Times (Atom y) (Atom x)), Atom y, Atom y])"
  apply(auto) by (metis Cons_eq_appendI Nil_in_star append_Nil concI singletonI)
        
  from uu have setux: "set u \<subseteq> {x}" using atoms_lang by fastforce

  from uu have pre: "TSdet [x,y] h u (length u) = ([x,y], (rev u) @ h)"
    apply(auto)
      apply(simp add: rTS_def)
      by(simp add: rTS_def Step_def step_def split_def TS_step_d_def)
     

  from uu have TS_prefix: "T_TS [x, y] h u = 0" unfolding T_TS_def apply(auto)
    unfolding t_TS_def s_TS_def by (simp) 


  have u: "(let li = index (rev u @ h) y
                        in if li = length (rev u @ h) then 0
                           else let sincelast = take li (rev u @ h);
                                    S = {xa. xa < y in [x, y] \<and> count_list sincelast xa \<le> 1}
                                in if S = {} then 0 else index [x, y] y - Min (index [x, y] ` S),
                        []) = (0,[])" 
  proof (cases "index (rev u @ h) y = length (rev u @ h)")
    case False
    then have "h \<noteq> []" using setux by (metis append_Nil2 goal1(1) index_conv_size_if_notin set_rev singletonD subset_code(1))
    with goal1(3) have tt: "(\<exists>hs. h = [x, x] @ hs)" by auto
    then obtain hs where tl: "h=[x,x]@hs" by auto


    have sndcase: "u \<noteq> [] \<Longrightarrow> u = [x]" using uu by (simp)

    from goal1(1) have empt: "{xa. xa < y in [x, y] \<and> count_list (take (index (rev u @ h) y) (rev u @ h)) xa \<le> 1}
        = {}"
          unfolding before_in_def apply(simp) 
    apply(cases "u=[]") 
      apply(simp) unfolding tl apply(simp add: goal1(1))
      using sndcase apply(simp add: goal1(1))
    done          

    show ?thesis apply(simp only: Let_def False if_False empt) by (simp)
  qed simp

  have e: "T_TS [x,y] (rev u @ h) [y,y] = 2" unfolding T_TS_def apply(simp)
    unfolding t_TS_def s_TS_def using goal1(1) apply(auto simp: split_def)
        unfolding rTS_def Step_def apply(simp only: fst_conv snd_conv TS_step_d_def)  
        apply(simp only: u) by(auto simp: step_def)

  have "T_TS [x, y] h qs = T_TS [x, y] h (u @ v)" using qsuv  by auto
  also have "\<dots>
      = T_TS [x, y] h u + T_TS (s_TS [x,y] h u (length u)) (rev u @ h) v"
      by(rule splitquerylist)
  also have "\<dots>
      = T_TS [x, y] h u + T_TS [x,y] (rev u @ h) [y,y]" using pre by(simp add: s_TS_def  vv2)

  also have "\<dots> = T_TS [x, y] h u + 2" by (simp only: e)
  also have "\<dots> = 2" by (simp add: TS_prefix)
  finally have TS: "T_TS [x, y] h qs = 2" .

  (* dannach *)
 

  have hel: "(fst (TSdet [x, y] h u (length u))) = [x,y]"
    using pre by simp

  have yha: "fst (TSdet [x, y] h (u @ [y, y]) (length (u @ [y, y]))) = [y, x]"
    apply(subst splitdet) apply(simp only: hel)
      apply(subst TS_xx[of x])
        apply(fact)
        by(simp_all) 

  show ?thesis unfolding TS  inv_TS_def apply(auto)
    apply(rule exI[where x="y"])
    apply(safe)                                    
      apply(rule exI[where x="x"]) unfolding qsuv s_TS_def vv2
       apply(fact)
       by(simp)
qed
 
lemma TS_a': "qs \<in> Lxx x y \<Longrightarrow>
    x \<noteq> y \<Longrightarrow>
    h = [] \<or> (\<exists>hs. h = [x, x] @ hs) \<Longrightarrow>
    qs
    \<in> lang
        (seq
          [Plus (Atom x) rexp.One, Atom y,
           Atom y]) \<Longrightarrow>
    T_TS [x, y] h qs
    \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])
    \<and>  inv_TS qs x y h"
proof -                                             
  case goal1
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = 1" using OPT2_A[OF goal1(2) goal1(4)] by auto
  show ?case using OPT ts_a[OF goal1(2,4,3)] by auto  
qed

subsubsection "x+yx(yx)*x"
                    

        
lemma ts_c: "x \<noteq> y \<Longrightarrow>
  v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x]) \<Longrightarrow>
  (\<exists>hs. h = [x, x] @ hs) \<or> h = [x] \<or> h = []
    \<Longrightarrow> T_TS [x, y] h v = (length v - 2)
            \<and>  (s_TS [x,y] h v (length v) = [x,y] \<and> (\<exists>hs. (rev v @ h) = [x,x]@hs))"
proof -
  case goal1
  then have lenvmod: "length v mod 2 = 1" apply(simp)
  proof -
    assume "v \<in> ({[y]} @@ {[x]}) @@ star({[y]} @@ {[x]}) @@ {[x]}"
    then obtain p q r where pqr: "v=p@q@r" and "p\<in>({[y]} @@ {[x]})"
              and q: "q \<in> star ({[y]} @@ {[x]})" and "r \<in> {[x]}" by (metis concE)
    then have "p = [y,x]" "r=[x]" by auto
    with pqr have a: "length v = 3+length q" by auto

    from q have b: "length q mod 2 = 0"
    apply(induct q rule: star_induct) by (auto)    
    from a b show "length v mod 2 = Suc 0" by auto
  qed
         
 

  with goal1(1,3) have fall: "(\<exists>hs. h = [x, x] @ hs) \<or> index h y = length h"
    by(auto) 

  

  from goal1(2) have "v \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])
                          @@ lang (seq[Atom x])" by (auto simp: conc_def)
  then obtain a b where aa: "a \<in> lang (seq[Times (Atom y) (Atom x), Star(Times (Atom y) (Atom x))])"
                      and "b \<in> lang (seq[Atom x])"
                      and vab: "v = a @ b" 
                      by(erule concE) 
  then have bb: "b=[x]" by auto
  from aa have lena: "length a > 0" by auto
 
  from TS_yxyx[OF goal1(1) aa fall] have stars: "T_TS [x, y] h (a @ b) =
    length a - 1 + T_TS [x, y] (rev a @ h) b"
    and history: "(\<exists>hs. rev a @ h = [x, y] @ hs)"
    and state: "TSdet [x, y] h a (length a) = ([x, y], rev a @ h)" by auto
  thm TS_x
  have "T_TS [x, y] (rev a @ h) b = 0
            \<and> TSdet [x, y] (rev a @ h) b (length b) = ([x,y], rev b @ (rev a @ h))" unfolding bb apply(rule TS_x)
    apply(fact)
    using history by simp
  then have  suffix: "T_TS [x, y] (rev a @ h) b = 0"
          and suState: "TSdet [x, y] (rev a @ h) b (length b) = ([x,y], rev b @ (rev a @ h))" by auto

  from stars suffix have "T_TS [x, y] h (a @ b) = length a - 1" by auto
  then have whatineed: "T_TS [x, y] h v = (length v - 2)" using vab bb by auto


  (* was hinten raus kommt *)
 
  have splitdet2: "TSdet [x, y] (h) (a @ [x]) (length (a @ [x]))
      = TSdet (fst (TSdet [x,y] (h) a (length a))) (rev a @ h) [x] (length [x])"
      using splitdet[of "(h)" x y a "[x]"] by auto
 
 

  have grgr:"fst (TSdet [x, y] h (v) (length (v))) = [x, y]"
     unfolding vab bb
    apply(simp only: splitdet2) apply(simp only: state[unfolded s_TS_def])
    by(simp only: fst_conv suState[unfolded bb])

  from history obtain hs' where "rev a @ h = [x, y] @ hs'" by auto
  then obtain hs2 where reva: "rev a @ h = x # hs2" by auto


  show ?case using whatineed
    apply(auto) 
      using grgr apply(simp add: s_TS_def )
      by(simp add: reva vab bb)
qed

lemma TS_c': "qs \<in> Lxx x y \<Longrightarrow>
    x \<noteq> y \<Longrightarrow>
    h = [] \<or> (\<exists>hs. h = [x, x] @ hs) \<Longrightarrow>
    qs
    \<in> lang
        (seq
          [Plus (Atom x) rexp.One, Atom y,
           Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom x]) \<Longrightarrow>
    T_TS [x, y] h qs
    \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) \<and>  inv_TS qs x y h"

proof -
  case goal1
  obtain u v where uu: "u \<in> lang (Plus (Atom x) One)"
        and vv: "v \<in> lang (seq[Times (Atom y) (Atom x), Star (Times (Atom y) (Atom x)), Atom x])"
        and qsuv: "qs = u @ v" 
        using goal1(4)
        by (auto simp: conc_def)   
 
  from TS_xr[OF goal1(2) uu goal1(3), of v] have
              T_pre: "T_TS [x, y] h (u@v) = T_TS [x,y] (rev u @ h) v"
          and fall': "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> (rev u @ h) = [x] \<or> (rev u @ h)=[]" by auto
      
  with goal1 uu have fall: "(\<exists>hs. (rev u @ h) = [x, x] @ hs) \<or> index (rev u @ h) y = length (rev u @ h)"
    by(auto) 

  from ts_c[OF goal1(2) vv fall'] have
              T_star: "T_TS [x, y] (rev u @ h) v = (length v - 2)"
          and inv1:   "s_TS [x, y] (rev u @ h) v (length v) = [x, y]"
          and inv2:   "(\<exists>hs. rev v @ rev u @ h = [x, x] @ hs)" by auto

  from T_pre T_star qsuv have TS: "T_TS [x, y] h qs = (length v - 2)" by metis

  (* OPT *)

  from uu have uuu: "u=[] \<or> u=[x]" by auto
  from vv have vvv: "v \<in> lang (seq
          [Atom y, Atom x,
           Star (Times (Atom y) (Atom x)),
           Atom x])" by(auto simp: conc_def)
  have OPT: "T\<^sub>p [x,y] qs (OPT2 qs [x,y]) = (length v) div 2" apply(rule OPT2_C) by(fact)+


  (* was hinten raus kommt *)

  have splitdet1: "TSdet [x,y] h (u @ v) (length (u @ v))
      = TSdet (fst (TSdet [x,y] h u (length u))) (rev u @ h) v (length v)" 
        using splitdet by auto 

  have first: "fst (TSdet [x,y] h u (length u)) = [x,y]"
    apply(cases "u=[]")
      apply(simp)
      using uu by(simp add: rTS_def Step_def TS_step_d_def step_def)
  
  have 1: "s_TS [x, y] h qs (length qs) = [x, y]"
    unfolding s_TS_def qsuv apply(simp only: splitdet1)
    by(simp only: first inv1[unfolded s_TS_def]) 
 
  show ?case unfolding TS OPT
    apply(auto)
     unfolding inv_TS_def
     apply(rule exI[where x="x"])
     apply(rule exI[where x="y"]) 
      using 1 inv2 qsuv by(auto) 
qed

subsubsection "xx"

lemma request_first: "x\<noteq>y \<Longrightarrow> Step (rTS h) ([x, y], is) x = ([x,y],x#is)"
unfolding rTS_def Step_def by(simp add: split_def TS_step_d_def step_def)

lemma ts_d: "qs \<in> Lxx x y \<Longrightarrow>
    x \<noteq> y \<Longrightarrow>
    h = [] \<or> (\<exists>hs. h = [x, x] @ hs) \<Longrightarrow>
    qs \<in> lang (seq [Atom x, Atom x]) \<Longrightarrow>
    T_TS [x, y] h qs = 0 \<and>
     inv_TS qs x y h"
proof -
  assume xny: "x \<noteq> y"
  assume "qs \<in> lang (seq [Atom x, Atom x])"
  then have xx: "qs = [x,x]" by auto

  have TS: "T_TS [x, y] h qs = 0" unfolding xx T_TS_def apply(auto)
  unfolding  t_TS_def s_TS_def
  by (auto simp add: split_def rTS_def Step_def TS_step_d_def step_def) 

  from TS  show ?thesis unfolding inv_TS_def apply simp
    apply(rule exI[where x="x"])
    apply(safe)
      apply(rule exI[where x="y"])
        apply(simp add: xx s_TS_def split_def  )
          apply(simp add: request_first[OF xny])
          by(simp add: xx)
qed

lemma TS_d: "qs \<in> Lxx x y \<Longrightarrow>
    x \<noteq> y \<Longrightarrow>
    h = [] \<or> (\<exists>hs. h = [x, x] @ hs) \<Longrightarrow>
    qs \<in> lang (seq [Atom x, Atom x]) \<Longrightarrow>
    T_TS [x, y] h qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) 
    \<and> inv_TS qs x y h"
using ts_d by auto


lemma D: "qs \<in> Lxx x y \<Longrightarrow> x \<noteq> y \<Longrightarrow> h=[] \<or> (\<exists>hs. h=[x,x]@hs) \<Longrightarrow> 
      T_TS [x, y] h qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y]) 
      \<and> inv_TS qs x y h"
  apply(rule LxxI[where P="(\<lambda>x y qs. T_TS [x, y] h qs \<le> 2 * T\<^sub>p [x, y] qs (OPT2 qs [x, y])
                          \<and> inv_TS qs x y h)"])
     apply(fact TS_d)
     apply(fact TS_b')
     apply(fact TS_c')
     apply(fact TS_a')
     by simp


lemma "s \<in> {[x,y],[y,x]} \<Longrightarrow> x \<noteq> y \<Longrightarrow> h=[] \<or> (\<exists>hs. h=[x,x]@hs) \<Longrightarrow> TS_step_d (s,h) y = ((0,[]), y#h)"
unfolding TS_step_d_def
apply(cases "h=[]")
  apply(simp)
  apply(cases "index h y = length h")
    apply(simp)
    using before_in_setD1 by auto


thm TS_a'[unfolded Lxx_def L_lasthasxx_def, simplified seq.simps]
 

subsection "Phase Partitioning"
 
theorem TS_OPT2: "(x::nat) \<noteq> y \<Longrightarrow> set \<sigma> \<subseteq> {x,y} \<Longrightarrow> h=[] \<or> (\<exists>hs. h=[x,x]@hs)
     \<Longrightarrow> T_TS [x,y] h \<sigma> \<le> 2 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 2"
proof (induction "length \<sigma>" arbitrary: h \<sigma> x y rule: less_induct)
  case (less \<sigma>)
  show ?case
  proof (cases "\<exists>xs ys. \<sigma>=xs@ys \<and> xs \<in> Lxx x y")
    case True
    then obtain xs ys where qs: "\<sigma>=xs@ys" and xsLxx: "xs \<in> Lxx x y" by auto

    with Lxx1 have len: "length ys < length \<sigma>" by fastforce
    from qs(1) less(3) have ysxy: "set ys \<subseteq> {x,y}" by auto

    have "set xs \<subseteq> {x, y}" using less(3) qs by auto

    from D[OF xsLxx less(2) less(4)] 
      have D1: "T_TS [x, y] h xs \<le> 2 * T\<^sub>p [x, y] xs (OPT2 xs [x, y])" 
        and D2: "\<exists>x' y'. s_TS [x,y] h xs (length xs) = [x',y'] \<and> (\<exists>hs. (rev xs @ h) = [x',x']@hs)"
          unfolding inv_TS_def by auto

    def [simp]: LTS' == "s_TS [x,y] h xs (length xs)"
    thm s_TS_xy
    have it: "s_TS [x,y] h xs (length xs) \<in> {[x,y],[y,x]}"
      apply(rule s_TS_xy)
        apply(fact)
        apply(fact)
        by (simp)

    with D2 less(2) obtain x' y' where LTS': "LTS' = [x',y']" and  xy': "x'\<in>{x,y}" "y'\<in>{x,y}" "x'\<noteq>y'"
                            and history: "(\<exists>hs. (rev xs @ h) = [x',x']@hs)" by auto

    from history have "x' = last xs" by (metis Cons_eq_append_conv Lxx_not_nullable hd_rev list.sel(1) rev_is_Nil_conv xsLxx)
    with LTS' have it2: "hd (s_TS [x, y] h xs (length xs)) = last xs" by auto

    from history obtain suff where "rev xs @ h = [x', x'] @ suff" by auto
    then have "rev (rev xs @ h) = rev ([x', x'] @ suff)" by auto
    then have gsch: "(rev h) @ xs = rev suff @ [x',x']" by auto

    from Lxx1[OF xsLxx] obtain p1 l1 where p1: "xs = p1 @ [l1]"
      by (metis Lxx_not_nullable append_butlast_last_id xsLxx)
    with Lxx1[OF xsLxx] have "length p1 > 0" by auto
    thm append_butlast_last_id
    then have "p1 \<noteq> []" by auto     
    then obtain pref l2 where p2: "p1=pref@[l2]" by (metis append_butlast_last_id)
    from p1 p2 have "xs = pref @ [l2,l1]" by auto
    with gsch have "xs = pref @ [x',x']" by auto   
    then have it3:"xs =  pref@[hd (LTS'), hd (LTS')]" using LTS' by auto

    have ys': "set ys \<subseteq> {x', y'}"  using ysxy xy' by blast

    from len have c: "T_TS LTS' (rev xs @ h) ys
           \<le> 2 *  T\<^sub>p LTS' ys (OPT2 ys LTS') + 2"
            unfolding LTS'
            apply(rule less)
              apply(simp add: xy')
              apply(fact)
              using history by simp

    have well: "T\<^sub>p [x, y] xs (OPT2 xs [x, y]) + T\<^sub>p LTS' ys (OPT2 ys LTS')
        = T\<^sub>p [x, y] (xs @ ys) (OPT2 (xs @ ys) [x, y])"
          apply(rule OPTauseinander[where pref=pref])
            apply(fact)
            using less(3) qs apply(simp)
            using less(3) qs apply(simp)
            unfolding LTS'_def apply(fact)
            apply(fact)
            using it3[unfolded LTS'_def] by simp
              

    have E0: "T_TS [x,y] h \<sigma>
          = T_TS [x,y] h (xs@ys)" using qs by auto
    thm splitquerylist
    also have E1: "\<dots> = T_TS [x,y] h xs + T_TS LTS' (rev xs @ h) ys"
        unfolding LTS'_def
        by(rule splitquerylist)
    also have E2: "\<dots> \<le> T_TS [x,y] h xs + 2 * T\<^sub>p LTS' ys (OPT2 ys LTS') + 2"
        using c by simp
    also have E3: "\<dots> \<le> 2 * T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + 2 * T\<^sub>p LTS' ys (OPT2 ys LTS') + 2"
        using D1 by simp
        
    also have "\<dots> \<le> 2 * (T\<^sub>p [x,y] xs (OPT2 xs [x,y]) + T\<^sub>p LTS' ys (OPT2 ys LTS')) + 2"
        by(auto)
    also have  "\<dots> = 2 * (T\<^sub>p [x,y] (xs@ys) (OPT2 (xs@ys) [x,y])) + 2"
      using well by auto 
    also have E4: "\<dots> = 2 * (T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y])) + 2"
        using qs by auto
    finally show ?thesis .
  next
    case False
    note f1=this
    from Lxx_othercase[OF less(3) this, unfolded hideit_def] have
        nodouble: "\<sigma> = [] \<or> \<sigma> \<in> lang (nodouble x y)" by auto
    show ?thesis
    proof (cases "\<sigma> = []")
      case True
      then show ?thesis unfolding T_TS_def by simp
    next
      case False
      (* with padding *)
      from False nodouble have qsnodouble: "\<sigma> \<in> lang (nodouble x y)" by auto
      let ?padded = "pad \<sigma> x y"
      from False pad_adds2[of \<sigma> x y] less(3) obtain addum where ui: "pad \<sigma> x y = \<sigma> @ [last \<sigma>]" by auto
      from nodouble_padded[OF False qsnodouble] have pLxx: "?padded \<in> Lxx x y" .

      have E0: " T_TS [x,y] h \<sigma> \<le> T_TS [x,y] h ?padded"
      proof -
        thm splitquerylist
        have "T_TS [x,y] h ?padded = T_TS [x,y] h \<sigma> + T_TS (s_TS [x,y] h \<sigma> (length \<sigma>)) (rev \<sigma> @ h) [last \<sigma>]"
          unfolding ui(1) using splitquerylist by auto
        also have "\<dots> \<ge> T_TS [x,y] h \<sigma>" by auto
        finally show ?thesis by auto
      qed  

      thm D[OF pLxx less(2) less(4)]
      also from pLxx have E1: "\<dots> \<le> 2 * T\<^sub>p [x,y] ?padded (OPT2 ?padded [x,y])"
        using D[OF pLxx less(2) less(4)] by simp
      also have E2: "\<dots> \<le> 2 * T\<^sub>p [x,y] \<sigma> (OPT2 \<sigma> [x,y]) + 2"
      proof -
        from False less(2) obtain \<sigma>' x' y' where qs': "\<sigma> = \<sigma>' @ [x']" and x': "x' = last \<sigma>" "y'\<noteq>x'" "y' \<in>{x,y}" 
            by (metis append_butlast_last_id insert_iff)
        have tla: "last \<sigma> \<in> {x,y}" using less(3) False last_in_set by blast
        with x' have grgr: "{x,y} = {x',y'}" by auto
        then have "(x = x' \<and> y = y') \<or> (x = y' \<and> y = x')" using less(2) by auto
        then have tts: "[x, y] \<in> {[x', y'], [y', x']}" by blast
        
        from qs' ui have pd: "?padded = \<sigma>' @ [x', x']" by auto 

        have "T\<^sub>p [x,y] (?padded) (OPT2 (?padded) [x,y])
              = T\<^sub>p [x,y] (\<sigma>' @ [x', x']) (OPT2 (\<sigma>' @ [x', x']) [x,y])"
                unfolding pd by simp
        also have gr: "\<dots>
            \<le> T\<^sub>p [x,y] (\<sigma>' @ [x']) (OPT2 (\<sigma>' @ [x']) [x,y]) + 1"
              apply(rule OPT2_padded[where x="x'" and y="y'"])
                apply(fact)
                using grgr qs' less(3) by auto
        also have "\<dots> \<le> T\<^sub>p [x,y] (\<sigma>) (OPT2 (\<sigma>) [x,y]) + 1" 
              unfolding qs' by simp
        finally show ?thesis by auto
      qed
      finally show ?thesis . 
    qed
  qed
qed  

thm TS_OPT2 OPT2_is_opt


theorem TS2': "(x::nat) \<noteq> y \<Longrightarrow> set qs \<subseteq> {x,y}
     \<Longrightarrow> T_TS [x,y] [] qs \<le> 2 * (T\<^sub>p_opt [x,y] qs) + 2"
proof -
  case goal1
  with OPT2_is_opt[OF goal1(2) goal1(1)] have a: "T\<^sub>p [x, y] qs (OPT2 qs [x, y]) = T\<^sub>p_opt [x,y] qs" by simp
  thm TS_OPT2[of x y qs "[]"]
  show ?case unfolding a[symmetric]
    apply(rule TS_OPT2[of x y qs "[]"])
    by(auto simp: goal1)
qed


theorem TS2: "(x::nat) \<noteq> y \<Longrightarrow> set qs \<subseteq> {x,y}
     \<Longrightarrow> real (T\<^sub>p_on (rTS [])  [x,y] qs) \<le> 2 * (T\<^sub>p_opt [x,y] qs) + 2"
unfolding T_TS_T_on
using TS2'[of x y qs] by auto

 
 
lemma s_TS_append: "i\<le>length as \<Longrightarrow>s_TS init h (as@bs) i = s_TS init h as i"
by (simp add: TSdet_append s_TS_def)

lemma othersdontinterfere: "qs!i\<notin>{a,b} \<Longrightarrow> a < b in s_TS init h qs i \<Longrightarrow> a < b in s_TS init h qs (Suc i)"
proof -
  have "s_TS init h qs (Suc i) = e" apply(simp add: s_TS_def split_def ) sorry
  show ?thesis sorry
qed


lemma  TS_mono:
    fixes l::nat
    assumes 1: "x < y in s_TS init h xs (length xs)"
     and l_in_cs: "l \<le> length cs"
     and firstocc: "\<forall>j<l. cs ! j \<noteq> y"
     and "x \<notin> set cs" 
    shows "x < y in s_TS init h (xs@cs) (length (xs)+l)"
proof -
  {
      fix n
      assume "n\<le>l"
      then have "x < y in s_TS init h ((xs)@cs) (length (xs)+n)"
        proof(induct n)
          case 0
          show ?case apply (simp only: s_TS_append ) using 1 by(simp) 
        next
          case (Suc n) 
          then have n_lt_l: "n<l" by auto
          show ?case apply(simp)
            apply(rule othersdontinterfere)
              apply(simp add: nth_append) apply(safe)
                using assms(4) n_lt_l l_in_cs apply fastforce
                using firstocc n_lt_l apply blast
                using Suc(1) n_lt_l by(simp)
        qed  
    }
    -- "before the request to y, x is in front of y"
    then show "x < y in s_TS init h (xs@cs) (length (xs)+l)"
      by blast
qed


lemma step_no_action: "step s q (0,[]) = s"
unfolding step_def mtf2_def by simp


lemma s_TS_set: "i \<le> length qs \<Longrightarrow> set (s_TS init h qs i) = set init"
apply(induct i)
  apply(simp add: s_TS_def  )
  apply(simp add: s_TS_def TSdet_Suc)
  by(simp add: split_def rTS_def Step_def step_def)


lemma s_TS_distinct: "i \<le> length qs \<Longrightarrow> distinct init \<Longrightarrow> distinct (s_TS init h qs i)"
apply(induct i)
  apply(simp add: s_TS_def)
  apply(simp add: s_TS_def TSdet_Suc)
  by(simp add: s_TS_def split_def Step_def step_def)

lemma count_notin2: "count_list xs x = 0 \<Longrightarrow> x \<notin> set xs"
apply (induction xs)  apply (auto del: count_notin)
  apply(case_tac "a=x") by(simp_all)+





lemma count_append: "count_list (xs@ys) x = count_list xs x + count_list ys x"
apply(induct xs) by(simp_all)

lemma count_rev: "count_list (rev xs) x = count_list xs x"
apply(induct xs) by(simp_all add: count_append )


 
lemma mtf2_q_passes: "q \<in> set xs \<Longrightarrow> distinct xs \<Longrightarrow> index xs q - n \<le> index xs x \<Longrightarrow> index xs x < index xs q
      \<Longrightarrow> q < x in (mtf2 n q xs)"
proof -
  case goal1
  then have "index xs q < length xs" by auto
  with goal1(4) have ind_x: "index xs x < length xs" by auto
  then have xinxs: "x\<in>set xs" using index_less_size_conv by metis 

  have B: "index (mtf2 n q xs) q = index xs q - n"
    apply(rule mtf2_q_after)
      by(fact)+
  also from ind_x mtf2_forward_effect3'[OF goal1]
      have A: "\<dots> < index (mtf2 n q xs) x" by auto 
  finally show ?thesis unfolding before_in_def using xinxs by force
qed
  
              
lemma twotox:
    assumes "count_list bs y \<le> 1"
      and "distinct init"
      and "x \<in> set init"
      and "y : set init" 
      and "x \<notin> set bs"
      and "x\<noteq>y"
    shows "x < y in s_TS init h (as@[x]@bs@[x]) (length (as@[x]@bs@[x]))"
proof -
  case goal1
  have aa: "snd (TSdet init h ((as @ x # bs) @ [x]) (Suc (length as + length bs)))
        = rev (take (Suc (length as + length bs)) ((as @ x # bs) @ [x])) @ h"
          apply(rule sndTSdet)  by(simp)
  then have aa': "snd (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))
        = rev (take (Suc (length as + length bs)) ((as @ x # bs) @ [x])) @ h" by auto
  have lasocc_x: "index (snd (TSdet init h ((as @ x # bs) @ [x]) (Suc (length as + length bs)))) x = length bs"
    unfolding aa
    apply(simp add:  del: config'.simps)
    using assms(5) by(simp add: index_append) 
  then have lasocc_x': "(index (snd (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x) = length bs" by auto

  let ?sincelast = "take (length bs)
                          (snd (TSdet init h ((as @ x # bs) @ [x])
                                 (Suc (length as + length bs))))"
  have sl: "?sincelast  = rev bs" unfolding aa by(simp)
  let ?S = "{xa. xa < x in fst (TSdet init h (as @ x # bs @ [x])
                                      (Suc (length as + length bs))) \<and>
                             count_list ?sincelast xa \<le> 1}"

  have y: "y \<in> ?S \<or> ~  y < x  in s_TS init h (as @ x # bs @ [x]) (Suc (length as + length bs))"
    unfolding sl unfolding s_TS_def using assms(1) by(simp add: count_rev del: config'.simps)
 
    have eklr: "length (as@[x]@bs@[x]) = Suc (length (as@[x]@bs))" by simp
  have 1: "s_TS init h (as@[x]@bs@[x]) (length (as@[x]@bs@[x]))
     = fst (Partial_Cost_Model.Step (rTS h)
          (TSdet init h (as @ [x] @ bs @ [x])
            (length (as @ [x] @ bs)))
          ((as @ [x] @ bs @ [x]) ! length (as @ [x] @ bs)))" unfolding s_TS_def unfolding eklr apply(subst TSdet_Suc)
              by(simp_all add: split_def)

  have brrr: "x\<in> set (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs))))"
    apply(subst s_TS_set[unfolded s_TS_def])
      apply(simp) by fact
  have ydrin: "y\<in>set (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs))))" 
    apply(subst s_TS_set[unfolded s_TS_def]) apply(simp) by fact
  have dbrrr: "distinct (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs))))" 
    apply(subst s_TS_distinct[unfolded s_TS_def]) using assms(2) by(simp_all)

  show ?case
  proof (cases "y < x  in s_TS init h (as @ x # bs @ [x]) (Suc (length as + length bs))")
    case True
    with y have yS: "y\<in>?S" by auto
    then have minsteps: "Min (index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) ` ?S)
              \<le> index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y"
      by auto
    let ?entf = "index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x -
                           Min (index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) ` ?S)"
    from minsteps have br: " index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x - (?entf)
          \<le> index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y" 
          by presburger
    have brr: "index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y
        < index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x"
          using True unfolding before_in_def s_TS_def by auto

    from br brr have klo: " index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x - (?entf)
          \<le> index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y
        \<and> index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) y
        < index (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))) x" by metis
   
 
    let ?result ="(mtf2 ?entf x (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))))"

    have whatsthat: "s_TS init h (as @ [x] @ bs @ [x]) (length (as @ [x] @ bs @ [x]))
        = ?result"   
        unfolding 1 apply(simp add: split_def step_def rTS_def Step_def TS_step_d_def del: config'.simps)
        apply(simp add: nth_append del: config'.simps)
          using lasocc_x'[unfolded rTS_def] apply(simp add: aa' del: config'.simps)
          using yS[unfolded sl rTS_def] apply (auto simp: take_append)  sorry


    have ydrinee: "  y \<in> set (mtf2 ?entf x (fst (TSdet init h (as @ x # bs @ [x]) (Suc (length as + length bs)))))" 
      apply(subst set_mtf2)  
      apply(subst s_TS_set[unfolded s_TS_def]) apply(simp) by fact

    show ?thesis unfolding whatsthat apply(rule mtf2_q_passes) by(fact)+       
  next
    case False
    then have 2: "x < y  in s_TS init h (as @ x # bs @ [x]) (Suc (length as + length bs))" 
      using brrr ydrin not_before_in assms(6) unfolding s_TS_def by metis
    thm x_stays_before_y_if_y_not_moved_to_front
    {
      fix e
      have "x < y in mtf2 e x (s_TS init h (as @ x # bs @ [x]) (Suc (length as + length bs)))"
        apply(rule x_stays_before_y_if_y_not_moved_to_front)
          unfolding s_TS_def
          apply(fact)+
          using assms(6) apply(simp)
          using 2 unfolding s_TS_def by simp
    } note bratz=this
    show ?thesis unfolding 1 apply(simp add: TSnopaid split_def Step_def s_TS_def TS_step_d_def step_def nth_append  del: config'.simps)
            using bratz[unfolded s_TS_def] by simp  
  qed

qed

lemma count_drop: "count_list (drop n cs) x \<le> count_list cs x"
proof -
  have "count_list cs x = count_list (take n cs @ drop n cs) x" by auto
  also have "\<dots> = count_list (take n cs) x + count_list (drop n cs) x" by (rule count_append)
  also have "\<dots> \<ge> count_list (drop n cs) x" by auto
  finally show ?thesis .
qed

lemma count_take_less: "n\<le>m \<Longrightarrow> count_list (take n cs) x \<le> count_list (take m cs) x"
proof -
    case goal1
    then
    have "count_list (take n cs) x = count_list (take n (take m cs)) x" by auto
    also have "\<dots> \<le> count_list (take n (take m cs) @ drop n (take m cs)) x" by (simp only: count_append)
    also have "\<dots> = count_list (take m cs) x" 
        by(simp only: append_take_drop_id)
    finally show ?case .
qed


lemma count_take: "count_list (take n cs) x \<le> count_list cs x"
proof -
  have "count_list cs x = count_list (take n cs @ drop n cs) x" by auto
  also have "\<dots> = count_list (take n cs) x + count_list (drop n cs) x" by (rule count_append)
  also have "\<dots> \<ge> count_list (take n cs) x" by auto
  finally show ?thesis .
qed

lemma casexxy: assumes "\<sigma>=as@[x]@bs@[x]@cs"
    and "x \<notin> set cs"
    and "set cs \<subseteq> set init"
    and "x \<in> set init"
    and "distinct init"
    and "x \<notin> set bs"
  shows "(%i. i<length cs \<longrightarrow> (\<forall>j<i. cs!j\<noteq>cs!i) \<longrightarrow> cs!i\<noteq>x
      \<longrightarrow> (cs!i) \<notin> set bs
      \<longrightarrow> x < (cs!i) in  (s_TS init h \<sigma> (length (as@[x]@bs@[x]) + i+1))) i"
proof (rule infinite_descent[where P="(%i. i<length cs \<longrightarrow> (\<forall>j<i. cs!j\<noteq>cs!i) \<longrightarrow> cs!i\<noteq>x
      \<longrightarrow> (cs!i) \<notin> set bs
      \<longrightarrow> x < (cs!i) in  (s_TS init h \<sigma> (length (as@[x]@bs@[x]) + i+1)))"])
  case (goal1 i)
  thm infinite_descent_measure
  thm infinite_descent 
  let ?y = "cs!i" 
  from goal1 have i_in_cs: "i < length cs" and
      firstocc: "(\<forall>j<i. cs ! j \<noteq> cs ! i)"
      and ynx: "cs ! i \<noteq> x"
      and ynotinbs: "cs ! i \<notin> set bs"
      and y_before_x': "~x < cs ! i in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1)" by auto

  have ss: "set (s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1)) = set init" using assms(1) i_in_cs by(simp add: s_TS_set)
  then have "cs ! i \<in> set (s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1))"
    unfolding ss using assms(3) i_in_cs by fastforce
  moreover have "x : set (s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1))"
    unfolding ss using assms(4) by fastforce

  -- "after the request to y, y is in front of x"
  ultimately have y_before_x_Suct3: "?y < x in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1)"
      using  y_before_x' ynx not_before_in by metis

  from ynotinbs have yatmostonceinbs: "count_list bs (cs!i) \<le> 1" by simp
 

  let ?y = "cs!i"
  have yininit: "?y \<in> set init" using assms(3) i_in_cs by fastforce
  {
    fix y
    assume "y \<in> set init"
    assume "x\<noteq>y"
    assume "count_list bs y \<le> 1"
    then have "x < y in s_TS init h (as@[x]@bs@[x]) (length (as@[x]@bs@[x]))"
      apply(rule twotox) by(fact)+
  } note xgoestofront=this    
  with yatmostonceinbs ynx yininit have zeitpunktt2: "x < ?y in s_TS init h (as@[x]@bs@[x]) (length (as@[x]@bs@[x]))" by blast
 
  have "i \<le> length cs" using i_in_cs by auto
  have x_before_y_t3: "x < ?y in s_TS init h ((as@[x]@bs@[x])@cs) (length (as@[x]@bs@[x])+i)"
    apply(rule TS_mono)
      by(fact)+
  
  -- "so x and y swap positions when y is requested, that means that y was inserted infront of
      some elment z (which cannot be x, has only been requested at most once since last request of y
          but is in front of x)"

  -- "first show that y must have been requested in as"
  
  have "snd (TSdet init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i)) =
          rev (take (length (as @ [x] @ bs @ [x]) + i) (as @ [x] @ bs @ [x] @ cs)) @ h"
            apply(rule sndTSdet) using i_in_cs by simp
  also have "\<dots>  = (rev (take i cs)) @ [x] @ (rev bs) @ [x] @ (rev as) @ h" by simp
  finally have fstTS_t3: "snd (TSdet init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i)) = 
                (rev (take i cs)) @ [x] @ (rev bs) @ [x] @ (rev as) @ h" .
  then have fstTS_t3': "(snd (TSdet init h \<sigma> (Suc (Suc (length as + length bs + i))))) = 
                (rev (take i cs)) @ [x] @ (rev bs) @ [x] @ (rev as) @ h" using assms(1) by auto

  let ?is = "snd (TSdet init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i))"
  let ?s = "fst (TSdet init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i))"
  let ?s_Suct3="s_TS init h (as @ [x] @ bs @ [x] @ cs) (length (as @ [x] @ bs @ [x]) + i+1)" 

  let ?S = "{xa. (xa < (as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i) in ?s \<and>
            count_list (take (index ?is ((as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i))) ?is) xa \<le> 1) }"


  (* unfold TSdet once *) 
  have once: "TSdet init h (as @ x # bs @ x # cs) (Suc (Suc (Suc (length as + length bs + i))))
        = Step (rTS h) (config\<^sub>p (rTS h) init (as @ x # bs @ x # take i cs)) (cs ! i)"
    apply(subst TSdet_Suc)
      using i_in_cs apply(simp)
      by(simp add: nth_append) 

  have aha: "(index ?is (cs ! i) \<noteq>
      length (fst (TSdet init h (as @ x # bs @ x # cs) (Suc (Suc (length as + length bs + i)))))) 
        \<and> ?S \<noteq> {}"
  proof (rule ccontr)
    case goal1
    -- "wenn (cs ! i) noch nie requested wurde, dann kann es gar nicht nach vorne gebracht werden!
        also widerspruch mit y_before_x'"
    have "?s_Suct3 = step ?s ?y (0, [])"  
      apply(simp add: s_TS_def del: config'.simps)
      unfolding once
      using i_in_cs using goal1 apply(simp add: nth_append split_def TS_step_d_def del: config'.simps)
      sorry
    then have e: "?s_Suct3 = ?s" by(simp only: step_no_action)
    from x_before_y_t3 have "x < cs ! i in ?s_Suct3" unfolding e unfolding s_TS_def by simp
    
    
    thm y_before_x'
    thm x_before_y_t3
    with y_before_x' show "False" unfolding assms(1) by auto
  qed 
  thm aha
  then have aha': "index (snd (TSdet init h (as @ x # bs @ x # cs)  (Suc (Suc (length as + length bs + i)))))
 (cs ! i) \<noteq>
length (fst (TSdet init h (as @ x # bs @ x # cs) (Suc (Suc (length as + length bs + i)))))" 
      and
      aha2: "?S \<noteq> {}" by auto
      

  from fstTS_t3' assms(1) have is_: "?is = (rev (take i cs)) @ [x] @ (rev bs) @ [x] @ (rev as) @ h" by auto
    
   have minlencsi: " min (length cs) i = i" using i_in_cs by linarith 

   let ?lastoccy="(index (rev (take i cs) @ x # rev bs @ x # rev as @ h) (cs ! i))"
   have "?y \<notin> set (rev (take i cs))" using firstocc by (simp add: in_set_conv_nth)
   then have lastoccy: "?lastoccy \<ge>
            i + 1 + length bs + 1" using ynx ynotinbs minlencsi by(simp add: index_append)

  (* x is not in S, because it is requested at least twice since the last request to y*)
  have x_nin_S: "x\<notin>?S"
      using is_ apply(simp add: split_def nth_append del: config'.simps)
  proof -
    case goal1
     have " count_list (take ?lastoccy (rev (take i cs))) x \<le>
          count_list (drop (length cs - i) (rev cs)) x" by (simp add: count_take rev_take)
     also have "\<dots> \<le> count_list (rev cs) x" by(simp add: count_drop ) 
     also have "\<dots> = 0" using assms(2) by(simp add: count_rev)
     finally have " count_list (take ?lastoccy (rev (take i cs))) x = 0" by auto
     have"
        2 \<le>
        count_list ([x] @ rev bs @ [x]) x " apply(simp only: count_append) by(simp)
     also have "\<dots> = count_list (take (1 + length bs + 1) (x # rev bs @ x # rev as @ h)) x" by auto
     also have "\<dots> \<le> count_list (take (?lastoccy - i) (x # rev bs @ x # rev as @ h)) x"
                apply(rule count_take_less)
                    using lastoccy by linarith
     also have   "\<dots> \<le>  count_list (take ?lastoccy (rev (take i cs))) x
                      + count_list (take (?lastoccy - i) (x # rev bs @ x # rev as @ h)) x" by auto
     also have "\<dots> = count_list (take ?lastoccy (rev (take i cs))
                            @ take (?lastoccy - min (length cs) i)
                            (x # rev bs @ x # rev as @ h)) x"
               by(simp add: minlencsi count_append) 
     finally show ?case by presburger
  qed

  have "Min (index ?s ` ?S) \<in> (index ?s ` ?S)" apply(rule Min_in) using aha2 by (simp_all)
  then obtain z where zminimal: "index ?s z = Min (index ?s ` ?S)"and z_in_S: "z \<in> ?S" by auto
  then have bef: "z < (as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i) in ?s"
          and "count_list (take (index ?is ((as @ [x] @ bs @ [x] @ cs) ! (length (as @ [x] @ bs @ [x]) + i))) ?is) z \<le> 1" by(blast)+ 

  with zminimal have zbeforey: "z < cs ! i in ?s"
    and zatmostonce: "count_list (take (index ?is (cs ! i)) ?is) z \<le> 1"
    and isminimal: "index ?s z = Min (index ?s ` ?S)" by(simp_all add: nth_append) 
  thm s_TS_set[unfolded s_TS_def]
  have elemins: "z \<in> set ?s" unfolding before_in_def by (meson zbeforey before_in_setD1)
  then  have zininit: "z \<in> set init" using i_in_cs apply(simp add: s_TS_set[unfolded s_TS_def] del: config'.simps)
      sorry

  from zbeforey have zbeforey_ind: "index ?s z < index ?s ?y" unfolding before_in_def by auto
  then have el_n_y: "z \<noteq> ?y" by auto

  have el_n_x: "z \<noteq> x" using x_nin_S  z_in_S by blast

  (* and because it is JUST before that element, z must be before x *)

  have "?s_Suct3 = step ?s ?y (index ?s ?y - Min (index ?s ` ?S), [])" (*
     unfolding s_TS_def  apply(simp add: split_def del: config'.simps) 
      apply(simp only: once[unfolded assms(1)])
      apply(simp add: split_def TS_step_d_def del: config'.simps) 
     apply(safe)
      using aha2 apply(simp add: split_def del: config'.simps)
      using aha aha2  apply(simp add: split_def del: config'.simps)
      using aha' apply(simp add: split_def nth_append del: config'.simps)
      apply(simp add: nth_append del: config'.simps) *) sorry
  with isminimal have state_dannach: "?s_Suct3 = step ?s ?y (index ?s ?y - index ?s z, [])" by presburger
    

  -- "so y is moved in front of z, that means:"
  thm mtf2_q_passes
  have yinfrontofz: "?y < z in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + i+1)" (*
    unfolding   assms(1) state_dannach apply(simp add: step_def del: config'.simps)
    apply(rule mtf2_q_passes)
      using i_in_cs assms(5) apply(simp_all add: s_TS_distinct[unfolded s_TS_def] s_TS_set[unfolded s_TS_def] del: TSdet.simps) 
      using yininit apply(simp)
      using zbeforey_ind apply simp *) sorry

  
 
           
  have yins: "?y \<in> set ?s"  (*
      using i_in_cs assms(3,5)  apply(simp_all add:   s_TS_set[unfolded s_TS_def] del: config'.simps) 
      by fastforce *) sorry

  have "index ?s_Suct3 ?y = index ?s z" 
    and "index ?s_Suct3 z = Suc (index ?s z)" 
    proof -
      let ?xs = "(fst (TSdet init h (as @ x # bs @ x # cs) (Suc (Suc (length as + length bs + i)))))"
      have setxs: "set ?xs = set init"
        apply(rule  s_TS_set[unfolded s_TS_def])
          using i_in_cs by auto
      then have yinxs: "cs ! i \<in> set  ?xs"
          apply(simp  add: setxs del: config'.simps) 
          using assms(3) i_in_cs by fastforce
      
      have distinctxs: "distinct ?xs"
        apply(rule  s_TS_distinct[unfolded s_TS_def])
          using i_in_cs assms(5) by auto
      

      let ?n = "(index
             (fst (TSdet init h (as @ x # bs @ x # cs)
                    (Suc (Suc (length as + length bs + i)))))
             (cs ! i) -
            index
             (fst (TSdet init h (as @ x # bs @ x # cs)
                    (Suc (Suc (length as + length bs + i)))))
             z)"

      thm mtf2_forward_effect2  s_TS_set[unfolded s_TS_def]
      have "index (mtf2 ?n ?y ?xs) (?xs ! index ?xs ?y) = index ?xs ?y - ?n\<and>
            index ?xs ?y - ?n = index (mtf2 ?n ?y ?xs) (?xs !  index ?xs ?y )"
        apply(rule mtf2_forward_effect2) 
          apply(fact)
          apply(fact)
          by simp
          
      then have  "index (mtf2 ?n ?y ?xs) (?xs ! index ?xs ?y) = index ?xs ?y - ?n" by metis
      also have "\<dots> = index ?s z" using zbeforey_ind by force
      finally have A: "index (mtf2 ?n ?y ?xs) (?xs ! index ?xs ?y) = index ?s z" .

      have aa: "index ?xs ?y - ?n \<le> index ?xs z" "index ?xs z < index ?xs ?y" 
        apply(simp)
          using zbeforey_ind by fastforce

      thm mtf2_forward_effect3'[OF yinxs distinctxs aa]
      from mtf2_forward_effect3'[OF yinxs distinctxs aa] 
        have B: "index (mtf2 ?n ?y ?xs) z = Suc (index ?xs z)" 
          using elemins yins by(simp add: nth_append split_def del: config'.simps)

      show "index ?s_Suct3 ?y = index ?s z" 
        unfolding state_dannach unfolding step_def apply(simp add: nth_append del: config'.simps) 
          using A yins by(simp add: nth_append  del: config'.simps)    

      show "index ?s_Suct3 z = Suc (index ?s z)"
        unfolding state_dannach unfolding step_def apply(simp add: nth_append del: config'.simps) 
          using B yins by(simp add: nth_append  del: config'.simps)        
  qed
      
  then have are: "Suc (index ?s_Suct3 ?y) = index ?s_Suct3 z" by presburger
        




  from are before_in_def y_before_x_Suct3 el_n_x  assms(1) have z_before_x: "z < x in ?s_Suct3"
    by (metis Suc_lessI not_before_in yinfrontofz) 
 

  have xSuct3: "x\<in>set ?s_Suct3" using assms(4) i_in_cs by(simp add: s_TS_set)
  have elSuct3: "z\<in>set ?s_Suct3" using zininit i_in_cs by(simp add: s_TS_set)

  have xt3: "x\<in>set ?s " apply(subst config_config_set) by fact

  note elt3=elemins

  have z_s: "z < x in ?s"
  proof(rule ccontr)
    case goal1
    then have "x < z in ?s" using not_before_in[OF xt3 elt3] el_n_x unfolding s_TS_def by blast
    then have "x < z in ?s_Suct3" unfolding state_dannach
      unfolding step_def apply(simp add: nth_append del: config'.simps)
      apply(rule x_stays_before_y_if_y_not_moved_to_front)
        apply(subst config_config_set) using i_in_cs assms(3) apply fastforce
        apply(subst config_config_distinct) using assms(5) apply fastforce
        apply(subst config_config_set) using assms(4) apply fastforce
        apply(subst config_config_set) using zininit apply fastforce
        using el_n_y apply(simp)
        by(simp)

    then show "False" using z_before_x not_before_in[OF xSuct3 elSuct3] by blast
  qed
  thm TS_mono


  have mind: "(index ?is (cs ! i)) \<ge> i + 1 + length bs + 1 " using lastoccy 
      using i_in_cs fstTS_t3'[unfolded assms(1)] by(simp add: split_def nth_append del: config'.simps)                    
 
  have "count_list (rev (take i cs) @ [x] @ rev bs @ [x]) z=
      count_list (take (i + 1 + length bs + 1) ?is) z" unfolding is_
        using el_n_x by(simp add: minlencsi count_append ) 
  also from mind have "\<dots> 
          \<le> count_list (take (index ?is (cs ! i)) ?is) z"
          by(rule count_take_less) 
  also have "\<dots> \<le> 1" using zatmostonce by metis
  finally have aaa: "count_list (rev (take i cs) @ [x] @ rev bs @ [x]) z \<le> 1" .
  with el_n_x have "count_list bs z + count_list (take i cs) z \<le> 1"
    by(simp add: count_append count_rev)
  moreover have "count_list (take (Suc i) cs) z = count_list (take i cs) z" 
      using i_in_cs  el_n_y by(simp add: take_Suc_conv_app_nth count_append)
  ultimately have aaaa: "count_list bs z + count_list (take  (Suc i) cs) z \<le> 1" by simp

  have z_occurs_once_in_cs: "count_list (take (Suc i) cs) z = 1"
  proof (rule ccontr)
    case goal1
    with aaaa have atmost1: "count_list bs z \<le> 1" and "count_list (take (Suc i) cs) z = 0" by force+
    have yeah: "z \<notin> set (take (Suc i) cs)" apply(rule count_notin2) by fact

    thm xgoestofront atmost1
    -- "now we know that x is in front of z after 2nd request to x, and that z is not requested any more,
        that means it stays behind x, which leads to a contradiction with z_before_x"

    have xin123: "x \<in> set (s_TS init h ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1)))"
      using i_in_cs assms(4) by(simp add: s_TS_set)
    have zin123: "z \<in> set (s_TS init h ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1)))"  
      using i_in_cs elemins apply(simp add: s_TS_set  del: config'.simps) using zininit by simp

    thm TS_mono
    have "x < z in s_TS init h ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i + 1))"
      apply(rule TS_mono)
        apply(rule xgoestofront)
          apply(fact) using el_n_x apply(simp) apply(fact)
        using i_in_cs apply(simp)
        using  yeah i_in_cs length_take min_def not_less nth_mem  apply (smt Suc_eq_plus1 `i \<le> length cs` dual_order.strict_trans1 less_SucE)
        using set_take_subset assms(2) by fast
    then have ge: "\<not> z < x in s_TS init h ((as @ [x] @ bs @ [x]) @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1))"
        using not_before_in[OF zin123 xin123] el_n_x by blast 

        have " s_TS init h ((as @ [x] @ bs @ [x]) @ cs) (length (as @ [x] @ bs @ [x]) + (i+1))
          = s_TS init h ((as @ [x] @ bs @ [x] @ (take (i+1) cs)) @ (drop (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1))" by auto
        also have "\<dots>
              = s_TS init h (as @ [x] @ bs @ [x] @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1))"
              apply(rule s_TS_append)
                using i_in_cs by(simp)
        finally have aaa: " s_TS init h ((as @ [x] @ bs @ [x]) @ cs) (length (as @ [x] @ bs @ [x]) + (i+1))
              = s_TS init h (as @ [x] @ bs @ [x] @ (take (i+1) cs)) (length (as @ [x] @ bs @ [x]) + (i+1))" .

    from ge z_before_x show "False" unfolding assms(1) using aaa by auto 
  qed
  from z_occurs_once_in_cs have kinSuci: "z \<in> set (take (Suc i) cs)" by (metis One_nat_def count_notin n_not_Suc_n)
  then have zincs: "z\<in>set cs" using set_take_subset by fast
  from z_occurs_once_in_cs  obtain k where k_def: "k=index (take (Suc i) cs) z" by blast
 
 
  then have "k=index cs z" using kinSuci by (simp add: index_take_if_set)
  then have zcsk: "z = cs!k" using zincs by simp




   have era: " cs ! index (take (Suc i) cs) z = z" using kinSuci in_set_takeD index_take_if_set by fastforce
   have ki: "k<i" unfolding k_def using kinSuci el_n_y 
    by (metis i_in_cs index_take index_take_if_set le_neq_implies_less not_less_eq_eq yes)
   have zmustbebeforex: "cs!k < x in ?s"
            unfolding k_def era by (fact z_s)
 
  -- "before the request to z, x is in front of z, analog zu oben, vllt generell machen?"


   -- "element z does not occur between t1 and position k"
   have  z_notinbs: "cs ! k \<notin> set bs"
   proof -
      case goal1
      from z_occurs_once_in_cs aaaa have "count_list bs z = 0" by auto
      then show ?case using zcsk count_notin2 by metis
   qed

   
   have "count_list bs z \<le> 1" using aaaa by linarith
   thm xgoestofront
   with xgoestofront[OF zininit el_n_x[symmetric]] have xbeforez: "x < z in s_TS init h (as @ [x] @ bs @ [x]) (length (as @ [x] @ bs @ [x]))" by auto

   obtain cs1 cs2 where v: "cs1 @ cs2 = cs" and cs1: "cs1 = take (Suc k) cs" and cs2: "cs2 = drop (Suc k) cs" by auto
  
   have z_firstocc:  "\<forall>j<k.  cs ! j \<noteq> cs ! k"
      and z_lastocc:  "\<forall>j<i-k-1.  cs2 ! j \<noteq> cs ! k" 
   proof (safe)
    case (goal1 j) 
    thm z_occurs_once_in_cs
    with ki i_in_cs have 2: "j < length (take k cs)" by auto
    have un1: "(take (Suc i) cs)!k = cs!k" apply(rule nth_take) using ki by auto
    have un2: "(take k cs)!j = cs!j" apply(rule nth_take) using goal1(1) ki by auto

    from i_in_cs ki have 1: "k < length (take (Suc i) cs)" by auto
    thm append_take_drop_id
    then have "(take (Suc i) cs) = (take k (take (Suc i) cs)) @ (take (Suc i) cs)!k # (drop (Suc k) (take (Suc i) cs))"
      by(rule id_take_nth_drop)
    also have "(take k (take (Suc i) cs)) = take k cs" using i_in_cs ki by (simp add: min_def)
    also have "... = (take j (take k cs)) @ (take k cs)!j # (drop (Suc j) (take k cs))"
        using 2 by(rule id_take_nth_drop)
    finally have "take (Suc i) cs
            =  (take j (take k cs)) @ [(take k cs)!j] @ (drop (Suc j) (take k cs)) 
                        @ [(take (Suc i) cs)!k] @ (drop (Suc k) (take (Suc i) cs))"
                        by(simp)
    then have A: "take (Suc i) cs
            =  (take j (take k cs)) @ [cs!j] @ (drop (Suc j) (take k cs)) 
                        @ [cs!k] @ (drop (Suc k) (take (Suc i) cs))"
                        unfolding un1 un2 by simp
    have "count_list ((take j (take k cs)) @ [cs!j] @ (drop (Suc j) (take k cs)) 
                        @ [cs!k] @ (drop (Suc k) (take (Suc i) cs))) z \<ge> 2"  
                     apply(simp add: count_append)
                      using zcsk goal1(2) by(simp)
    with A have "count_list (take (Suc i) cs) z \<ge> 2" by auto
    with z_occurs_once_in_cs show "False" by auto
  next
    case goal2
    then have 1: "Suc k+j < i" by auto
    then have 2: "j < length (drop (Suc k) (take (Suc i) cs))" using i_in_cs by simp 
    have 3: "(drop (Suc k) (take (Suc i) cs)) = take j (drop (Suc k) (take (Suc i) cs))
                                        @ (drop (Suc k) (take (Suc i) cs))! j
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))"
        using 2 by(rule id_take_nth_drop)
    have "(drop (Suc k) (take (Suc i) cs))! j = (take (Suc i) cs) ! (Suc k+j)"
      apply(rule nth_drop) using i_in_cs 1 by auto
    also have "\<dots> = cs ! (Suc k+j)" apply(rule nth_take) using 1 by auto
    finally have 4: "(drop (Suc k) (take (Suc i) cs)) = take j (drop (Suc k) (take (Suc i) cs))
                                        @ cs! (Suc k +j)
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))" 
                                         using 3 by auto
    have 5: "cs2 ! j = cs! (Suc k +j)" unfolding cs2
      apply(rule nth_drop) using i_in_cs 1 by auto
    
    from 4 5 goal2(2) have 6: "(drop (Suc k) (take (Suc i) cs)) = take j (drop (Suc k) (take (Suc i) cs))
                                        @ cs! k
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))" by auto
                                       
    from i_in_cs ki have 1: "k < length (take (Suc i) cs)" by auto
    thm append_take_drop_id
    then have 7: "(take (Suc i) cs) = (take k (take (Suc i) cs)) @ (take (Suc i) cs)!k # (drop (Suc k) (take (Suc i) cs))"
      by(rule id_take_nth_drop)
    have 9: "(take (Suc i) cs)!k = z" unfolding zcsk apply(rule nth_take) using ki by auto
    from 6 7 have A: "(take (Suc i) cs) = (take k (take (Suc i) cs)) @ z # take j (drop (Suc k) (take (Suc i) cs))
                                        @ z
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))" using ki 9  by auto
    
    have "count_list ((take k (take (Suc i) cs)) @ z # take j (drop (Suc k) (take (Suc i) cs))
                                        @ z
                                          # drop (Suc j) (drop (Suc k) (take (Suc i) cs))) z
                                            \<ge> 2"
                                            by(simp add: count_append)
    with A have "count_list (take (Suc i) cs) z \<ge> 2" by auto
    with z_occurs_once_in_cs show "False" by auto
qed 
 

   have k_in_cs: "k < length cs" using ki i_in_cs by auto
   with cs1 have lenkk: "length cs1 = k+1" by auto
   from k_in_cs have mincsk: "min (length cs) (Suc k) = Suc k" by auto

   have "s_TS init h (((as@[x]@bs@[x])@cs1) @ cs2) (length (as@[x]@bs@[x])+k+1)
        = s_TS init h ((as@[x]@bs@[x])@(cs1)) (length (as@[x]@bs@[x])+k+1)"
        apply(rule s_TS_append)
          using cs1 cs2 k_in_cs by(simp)
   then have spliter: "s_TS init h ((as@[x]@bs@[x])@(cs1)) (length (as@[x]@bs@[x]@(cs1)))
        = s_TS init h ((as@[x]@bs@[x])@cs) (length (as@[x]@bs@[x])+k+1) "
          using lenkk v cs1 apply(auto) by (simp add: add.commute add.left_commute)
       
   from cs2 have "length cs2 = length cs - (Suc k)" by auto

   have notxbeforez: "~ x < z in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + k + 1)"
   proof (rule ccontr)
    case goal1
    thm this TS_mono
    then have a: "x < z in s_TS init h ((as@[x]@bs@[x])@(cs1)) (length (as@[x]@bs@[x]@(cs1)))"
      unfolding spliter assms(1) by auto

    have 41: "x \<in> set(s_TS init h ((as @ [x] @ bs @ [x]) @ cs) (length (as @ [x] @ bs @ [x]) + i))"
       using i_in_cs assms(4) by(simp add: s_TS_set)
    have 42: "z \<in> set(s_TS init h ((as @ [x] @ bs @ [x]) @ cs) (length (as @ [x] @ bs @ [x]) + i))" 
       using i_in_cs zininit by(simp add: s_TS_set)
     
    have rewr: "s_TS init h ((as@[x]@bs@[x]@cs1)@cs2) (length (as@[x]@bs@[x]@cs1)+(i-k-1)) =
            s_TS init h (as@[x]@bs@[x]@cs) (length (as@[x]@bs@[x])+i)"
            using cs1 v ki  apply(simp add: mincsk) by (simp add: add.commute add.left_commute)

    have "x < z in s_TS init h ((as@[x]@bs@[x]@cs1)@cs2) (length (as@[x]@bs@[x]@cs1)+(i-k-1))"
      apply(rule TS_mono)
        using a apply(simp)
        using cs2 i_in_cs ki v cs1 apply(simp)  
        using z_lastocc zcsk apply(simp)
        using v assms(2) by force
    
    (* "contradiction to zmustbebeforex" *)
    thm zmustbebeforex 
    from zmustbebeforex this[unfolded rewr ] el_n_x zcsk 41 42 not_before_in show "False"
      unfolding s_TS_def  by fastforce
   qed
      
    thm bexI
   have 1: "k < length cs"
                   "(\<forall>j<k. cs ! j \<noteq> cs ! k)"
                   "cs ! k \<noteq> x" "cs ! k \<notin> set bs" 
              "~ x < z in s_TS init h \<sigma> (length (as @ [x] @ bs @ [x]) + k + 1)"
       apply(safe)
          using ki i_in_cs apply(simp)
          using z_firstocc apply(simp)
          using assms(2) ki i_in_cs apply(fastforce)
          using z_notinbs apply(simp)
          using notxbeforez by auto
          
          
                    
   show ?case apply(simp only: ex_nat_less_eq)
      apply(rule bexI[where x=k])
        using 1 zcsk apply(simp)
        using ki by simp
qed

lemma "set qs \<subseteq> set init \<Longrightarrow> distinct init \<Longrightarrow> x\<in>set init \<Longrightarrow> y\<in>set init \<Longrightarrow> x \<notin> set bs \<Longrightarrow> y \<notin> set bs
   \<Longrightarrow> n<length bs \<Longrightarrow>  x < y in s_TS init h (as@bs) n = x < y in s_TS init h (as@bs) 0"
proof(induct n) 
  case (Suc n)
  then have n_le: "n < length bs" by auto
  with Suc have iH: "x < y in s_TS init h (as@bs) n = x < y in s_TS init h (as@bs) 0" by auto

  
  from  n_le  have "x \<noteq> (take(posxy qs {x, y} 0) (as@bs) @ drop (posxy qs {x, y} 0) qs)!n"
    apply(simp only: nth_append) apply(simp) sorry
  then have xnq: "bs!n \<noteq> x" sorry
  from   n_le   have "y \<noteq> (take(posxy qs {x, y} 0) qs @ drop (posxy qs {x, y} 0) qs)!n"
    apply(simp only: nth_append) apply(simp) sorry
  then have ynq: "bs!n \<noteq> y" sorry

  {
    fix e
    thm xy_relativorder_mtf2
    have "x < y in mtf2 e (bs!n) (s_TS init h (as@bs) n) = x < y in (s_TS init h (as@bs) n)"
      apply(rule xy_relativorder_mtf2)
        apply(fact)+
        using n_le assms Suc.prems apply(simp_all add: s_TS_set) sorry
  } note a=this
  have qin: "qs!n \<in> set (s_TS init h (as@bs) n)" sorry

  thm x_stays_before_y_if_y_not_moved_to_front[OF qin]
  have "x < y in s_TS init h (as@bs) (Suc n)
      = x < y in (s_TS init h (as@bs) n)"
        apply(simp add: split_def step_def s_TS_def TS_step_d_def a[unfolded s_TS_def] ) sorry
  with iH show ?case by auto
qed (simp add: s_TS_def) 




lemma TS_pairwise': "qs \<in> {xs. set xs \<subseteq> set init} \<Longrightarrow>
       (x, y) \<in> {(x, y). x \<in> set init \<and> y \<in> set init \<and> x \<noteq> y} \<Longrightarrow>
       x \<noteq> y \<Longrightarrow> distinct init \<Longrightarrow>
       Pbefore_in x y (Partial_Cost_Model.embed (rTS [])) qs init =
       Pbefore_in x y (Partial_Cost_Model.embed (rTS [])) (Lxy qs {x, y}) (Lxy init {x, y})"
proof -
  case goal1 
  then have xyininit: "{x, y} \<subseteq> set init" 
        and qsininit: "set qs \<subseteq> set init" by auto
  note dinit=goal1(4)
  from goal1 have xny: "x\<noteq>y" by simp
                             
  have initpos: "Lxy init {x,y} \<in> {[x,y],[y,x]}" sorry
 

  have lq_s: "set (Lxy qs {x, y}) \<subseteq> {x,y}" by (simp add: Lxy_set_filter)
 
 (*
  have "x < y in (s_TS init [] qs (posxy qs {x, y} n))
        = x < y in (s_TS (Lxy init {x,y}) [] (Lxy qs {x,y}) n)"  
  proof (rule ahahahha[of _ "Lxy qs {x,y}" x y])
    case goal1
    show ?case sorry
  next
    case goal2
    then obtain prefix a b where ahae: "Lxy qs {x,y} = prefix @ [a] @ [a] @ [b]" "a\<in>{x,y}" "b\<in>{x,y}"
        by (auto simp: mycasexxy_def conc_def) 
    then obtain as bs cs ds where "qs = as @ [a] @ bs @ [a] @ cs @ [b] @ ds"
                "set bs \<inter> {x,y} = {}" "set cs \<inter> {x,y} = {}"  unfolding Lxy_def
      sorry
    thm casexxy
    have "(Lxy init {x, y}) \<in> {[x,y], [y,x]}" sorry
    then have " x < y in s_TS (Lxy init {x, y}) [] (Lxy qs {x, y}) n"
      unfolding ahae unfolding s_TS_def apply(simp)
    

*)
  show ?case sorry
qed



theorem TS_pairwise: "pairwise (embed (rTS []))"
apply(rule pairwise_property_lemma)
  apply(rule TS_pairwise') by (simp_all add: rTS_def TS_step_d_def)

(*
    proof (cases "n>0")
      case True 
      show ?thesis
      proof (cases "n>1")
        case True
        show ?thesis
        proof (cases "(Lxy init {x,y})!n-1 = (Lxy init {x,y})!n-2")
          case True
          show ?thesis sorry (* fall1 ...xx / ...yy*)
        next
          case False
          note different=this
          show ?thesis 
          proof (cases "n>2")
            case True 
            show ?thesis
            proof (cases "(Lxy init {x,y})!n-3 = (Lxy init {x,y})!n-2")
              case True 
              obtain prefix where "(Lxy init {x,y}) = prefix @ [(Lxy init {x,y})

              thm casexxy
              show ?thesis sorry (* fall 2 ...yyx / ...xxy*)
            next
              case False
              show ?thesis sorry (* fall 1 ...yxy / ...xyx *)
            qed
          next
            case False
            with `n>1` have "n=Suc (Suc 0)" by force
            then have "(s_TS (Lxy init {x,y}) [] (Lxy init {x,y})  n) =  (Lxy init {x,y}) "
              using different apply(auto simp add: s_TS_def TS_step_d_def step_def TS_init_d_def)
                using initpos by auto
            show ?thesis sorry (* fall xy / yx *)
          qed
        qed        
      next
        case False
        with `n>0` have "n=1" by force
        then have "(s_TS (Lxy init {x,y}) [] (Lxy init {x,y})  n) =  (Lxy init {x,y}) "
          by(simp add: s_TS_def TS_step_d_def step_def TS_init_d_def)
        show ?thesis sorry (* n=1 x / y *)
      qed
    next 
      case False
      then have 1: "n=0" by auto
      then
      have "(s_TS (Lxy init {x,y}) [] (Lxy init {x,y})  n) =  (Lxy init {x,y}) "
        by(simp add: s_TS_def TS_init_d_def)
      show ?thesis apply(simp) sorry (* [] *)
    qed


    case False
    then have "n<2" by auto
    then have "n=0 \<or> n=1" by auto
    then have sn: "(s_TS (Lxy init {x,y}) [] (Lxy qs {x,y}) n) = (Lxy init {x,y})"
      using initpos lq_s
        by(auto simp: s_TS_def TS_init_d_def TS_step_d_def step_def)
    have "x < y in (s_TS (Lxy init {x,y}) [] (Lxy qs {x,y}) n)
          = x < y in Lxy init {x,y}" by(simp add: sn)
    have "x < y in Lxy init {x,y} = x < y in init" sorry
    {
      fix m
      assume "m \<le> (posxy qs {x, y} n)"
      have "x < y in Lxy init {x,y} = x < y in (s_TS init [] qs m)"


    
    show ?thesis sorry
  next
    case True
    show ?thesis sorry
  qed


  thm config_rTS

  then 
  show ?case unfolding Pbefore_in_def
        by(simp add:  map_pmf_def bind_return_pmf config_rTS s_TS_def)
        


  { 
    fix n
    have "n\<le>length qs \<Longrightarrow> 
      Pbefore_in x y (rTS []) qs init n =
      Pbefore_in x y (rTS []) (Lxy qs {x, y}) (Lxy init {x, y}) (nrofnextxy {x,y} qs n)"
    proof (induct n)
      case 0
      have indexinprojectedlist: "(nrofnextxy {x,y} qs 0) = 0" using nrofnextxy0 by auto
      show ?case unfolding Pbefore_in_def  rTS_def indexinprojectedlist
        apply(simp add: TS_init_def bind_return_pmf)
        apply(rule Lxy_mono)
          apply(fact xyininit)
          by(fact dinit)
    next
      case (Suc n)
      then have iH: "Pbefore_in x y (rTS []) qs init n =
        Pbefore_in x y (rTS []) (Lxy qs {x, y})
          (Lxy init {x, y})
          (nrofnextxy {x,y} qs n)" by auto
          
      have n_le_qs: "n<length qs" using Suc(2) lastxy_index_le_size Suc_le_lessD le_trans by blast
      thm iH[unfolded Pbefore_in_def]

      thm bind_return_pmf map_bind_pmf
      have "Pbefore_in x y (rTS []) qs init (Suc n)
         = config\<^sub>p (TS_init [], TS_step) qs init n \<guillemotright>=
    (\<lambda>xa. return_pmf (x < y in step (snd xa) (qs ! n) (fst (TS_step_d (fst xa) (snd xa) (qs ! n)))))"
            unfolding Pbefore_in_def rTS_def
         by(auto simp add: TS_step_def bind_return_pmf map_bind_pmf split_def)
      also have "\<dots> = map_pmf (\<lambda>xa. (x < y in step (snd xa) (qs ! n) (fst (TS_step_d (fst xa) (snd xa) (qs ! n)))))
              (config\<^sub>p (TS_init [], TS_step) qs init n)" unfolding map_pmf_def by simp
      also have "\<dots> = map_pmf (\<lambda>p. x < y in snd p)
                      (config\<^sub>p (TS_init [], TS_step) (Lxy qs {x, y}) (Lxy init {x, y})
                      (nrofnextxy {x,y} qs (Suc n)))"
      proof (cases "qs!n \<in> {x,y}")
        case True
        then have step: "(nrofnextxy {x,y} qs (Suc n))
                  = Suc (nrofnextxy {x,y} qs n)" using nrofnextxy_Suc[OF n_le_qs] by auto

          have A: "(Lxy qs {x, y} ! nrofnextxy {x,y} qs n) = qs!n"
            using nrofnextxy_Lxy_nth True n_le_qs by auto
                                            

        have "map_pmf (\<lambda>xa. (x < y in step (snd xa) (qs ! n) (fst (TS_step_d (fst xa) (snd xa) (qs ! n)))))
              (config\<^sub>p (TS_init [], TS_step) qs init n)
            =  map_pmf 
            (\<lambda>xa. (x < y in step (snd xa) (Lxy qs {x, y} ! nrofnextxy {x,y} qs n)
                  (fst (TS_step_d (fst xa) (snd xa) (Lxy qs {x, y} ! nrofnextxy {x,y} qs n))))) 
              (config\<^sub>p (TS_init [], TS_step) (Lxy qs {x, y}) (Lxy init {x, y}) (nrofnextxy {x,y} qs n))
              "
        proof (cases "qs!n=x")
          case True

          have "map_pmf (\<lambda>xa. (x < y in step (snd xa) (qs ! n) (fst (TS_step_d (fst xa) (snd xa) (qs ! n)))))
              (config\<^sub>p (TS_init [], TS_step) qs init n)
      =  map_pmf (\<lambda>xa. True) (config\<^sub>p (MTF_init, MTF_step) qs init n)"
            unfolding True
              proof (rule pmf.map_cong0)
                case goal1
                then have 1: "distinct (snd z)" using config_config_distinct dinit sorry (* by metis *)
                have "set (snd z) = set init" using goal1 config_config_set sorry (* by metis *)
                then have 2: "x \<in> set (snd z)" "y \<in> set (snd z)" "qs!n \<in> set (snd z)"
                      using xyininit n_le_qs qsininit by auto                  
                from 1 2 xny show ?case using mtf2_moves_to_front' by metis  
              qed
          also have "\<dots> = return_pmf True" by auto
          also have "\<dots> = map_pmf (\<lambda>xa. True) (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y})
                (Lxy init {x, y}) (nrofnextxy {x,y} qs n))" by auto
          also have "\<dots> = map_pmf
            (\<lambda>xa. x < y in mtf2 (length (snd xa)) (qs!n) (snd xa))
              (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y})
                (Lxy init {x, y}) (nrofnextxy {x,y} qs n))" unfolding True
                proof (rule pmf.map_cong0)
                  case goal1
                  then have 1: "distinct (snd z)" using config_config_distinct dinit Lxy_distinct by metis
                  have "set (snd z) = set (Lxy init {x, y})" using goal1 config_config_set by metis
                  also have "\<dots> = {x,y}" using Lxy_set_filter xyininit by auto
                  finally have 2: "x\<in>set (snd z)" "y\<in>set (snd z)" by auto
                  from 1 2 xny show ?case using mtf2_moves_to_front' by metis  
                qed
          finally show ?thesis unfolding A .
        next



          case False
          with True have yreq: "qs!n=y" by simp
          have " map_pmf (\<lambda>xa. x < y in mtf2 (length (snd xa)) (qs ! n) (snd xa))
                  (config\<^sub>p (MTF_init, MTF_step) qs init n)
                   =  map_pmf (\<lambda>xa. False) (config\<^sub>p (MTF_init, MTF_step) qs init n)"
            unfolding yreq
            proof (rule pmf.map_cong0)
              case goal1
              then have 1: "distinct (snd z)" using config_config_distinct dinit by metis
              have "set (snd z) = set init" using goal1 config_config_set by metis
              then have 2: "x \<in> set (snd z)" "y \<in> set (snd z)" "qs!n \<in> set (snd z)"
                    using xyininit n_le_qs qsininit by auto                   
              from 1 2 xny have "y < x in mtf2 (length (snd z)) y (snd z) = True"
                  using mtf2_moves_to_front' by metis  
              then show ?case using xny 2 by simp
            qed
          also have "\<dots> = return_pmf False" by auto
          also have "\<dots> = map_pmf (\<lambda>xa. False) (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y})
                    (Lxy init {x, y}) (nrofnextxy {x,y} qs n))" by auto
          also have "\<dots> = map_pmf (\<lambda>xa. x < y in mtf2 (length (snd xa)) (qs!n) (snd xa))
                    (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y})
                    (Lxy init {x, y}) (nrofnextxy {x,y} qs n))" unfolding yreq
            proof (rule pmf.map_cong0)
              case goal1
              then have 1: "distinct (snd z)" using config_config_distinct dinit Lxy_distinct by metis
              have "set (snd z) = set (Lxy init {x, y})" using goal1 config_config_set by metis
              also have "\<dots> = {x,y}" using Lxy_set_filter xyininit by auto
              finally have 2: "x\<in>set (snd z)" "y\<in>set (snd z)" by auto
              from 1 2 xny have "y < x in mtf2 (length (snd z)) y (snd z) = True"
                  using mtf2_moves_to_front' by metis  
              then show ?case using xny 2 by simp  
            qed
          finally show ?thesis unfolding A .         
        qed
        also have "\<dots> =  bind_pmf (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y})
              (Lxy init {x, y}) (nrofnextxy {x,y} qs n))
              (\<lambda>xa. return_pmf (x < y in mtf2 (length (snd xa))
                (Lxy qs {x, y} ! nrofnextxy {x,y} qs n)
                (snd xa)))"
                unfolding map_pmf_def by simp 
        also have "\<dots> = 
              map_pmf (\<lambda>p. x < y in snd p)
                (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y}) (Lxy init {x, y})
                  (Suc (nrofnextxy {x,y} qs n)))"
                  by(simp add: MTF_step_def bind_return_pmf map_bind_pmf split_def step_def)
        also have "\<dots> = 
              map_pmf (\<lambda>p. x < y in snd p)
                (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y}) (Lxy init {x, y})
                  (nrofnextxy {x,y} qs (Suc n)))" using step by(simp)
        finally show ?thesis .
      next


        case False
        have step: "nrofnextxy {x,y} qs (Suc n) = nrofnextxy {x,y} qs n"
          using nrofnextxy_Suc2[OF n_le_qs] False  by auto

        have "map_pmf (\<lambda>xa. x < y in mtf2 (length (snd xa)) (qs ! n) (snd xa))
                (config\<^sub>p (MTF_init, MTF_step) qs init n)
            = map_pmf (\<lambda>p. x < y in snd p)
                (config\<^sub>p (MTF_init, MTF_step) qs init n)" 
             proof(rule pmf.map_cong0)
                case goal1
                (* x < y
         in mtf2 (length (snd z)) (qs ! n) (snd z) =
         x < y in snd z *)
                from False have 1: "qs!n\<noteq>x" "qs!n\<noteq>y" by auto
                have 2: "distinct (snd z)" using goal1 config_config_distinct dinit by (metis)
                have "set (snd z) = set init" using goal1 config_config_set by metis
                then have 3: "x \<in> set (snd z)" "y \<in> set (snd z)" "qs!n \<in> set (snd z)"
                      using xyininit n_le_qs qsininit by auto                  
                from 1 2 3 show ?case by (metis xy_relativorder_mtf2)
             qed
        also have "\<dots> =
              map_pmf (\<lambda>p. x < y in snd p)
                (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y}) (Lxy init {x, y})
                  (nrofnextxy {x,y} qs n))"
                  using iH[unfolded Pbefore_in_def MTF_def] by auto
        also have "\<dots> = 
              map_pmf (\<lambda>p. x < y in snd p)
                (config\<^sub>p (MTF_init, MTF_step) (Lxy qs {x, y}) (Lxy init {x, y})
                  (nrofnextxy {x,y} qs (Suc n)))" using step by(simp)
        finally show ?thesis .
      qed
      also have "\<dots> = Pbefore_in x y MTF (Lxy qs {x, y})
                   (Lxy init {x, y})
                   (nrofnextxy {x,y} qs (Suc n))"
                   unfolding Pbefore_in_def MTF_def by simp
      finally show ?case .
    qed
  } note fine=this

  (* posxy :      index in Lxy \<mapsto> index in qs
     nrofnextxy:  index in qs \<mapsto> index in Lxy
     *)
  from goal1(4)  have "(posxy qs {x, y} n) < length qs"
    using posxy_in_bounds by metis
  then have img_in_bounds: "(posxy qs {x, y} n) \<le> length qs" by auto
  
  from goal1(4) have bij: "(nrofnextxy {x, y} qs (posxy qs {x, y} n)) = n"
    using nrofnextxy_posxy_id by auto

  from fine[OF img_in_bounds,unfolded bij] show ?case .
qed




*)

lemma TS_compet':   "pairwise (embed (rTS [])) \<Longrightarrow> 
      \<forall>s0\<in>{init::(nat list). distinct init \<and> init\<noteq>[]}. \<exists>b\<ge>0. \<forall>qs\<in>{x. set x \<subseteq> set s0}. T\<^sub>p_on_rand (embed (rTS [])) s0 qs \<le> (2::real) *  T\<^sub>p_opt s0 qs + b"
unfolding rTS_def 
apply(rule factoringlemma_withconstant)
  proof -
    case goal5
    show ?case
    proof (safe)
      case (goal1 init)
      note out=this
      show ?case
        apply(rule exI[where x=2])
          apply(simp)
          proof (safe)
            case (goal1 qs a b)
            then have a: "a\<noteq>b" by simp
            have twist: "{a,b}={b, a}" by auto
            have b1: "set (Lxy qs {a, b}) \<subseteq> {a, b}" unfolding Lxy_def by auto
            with this[unfolded twist] have b2: "set (Lxy qs {b, a}) \<subseteq> {b, a}" by(auto)
        
            have "set (Lxy init {a, b}) = {a,b} \<inter> (set init)" apply(induct init)
                unfolding Lxy_def by(auto)
            with goal1 have A: "set (Lxy init {a, b}) = {a,b}" by auto
            have "finite {a,b}" by auto
            from out have B: "distinct (Lxy init {a, b})" unfolding Lxy_def by auto
            have C: "length (Lxy init {a, b}) = 2"
              using distinct_card[OF B, unfolded A] using a by auto
        
            have "{xs. set xs = {a,b} \<and> distinct xs \<and> length xs =(2::nat)} 
                    = { [a,b], [b,a] }"
                  apply(auto simp: a a[symmetric])
                  proof -
                    case (goal1 xs)
                    from goal1(4) obtain x xs' where r:"xs=x#xs'" by (metis Suc_length_conv add_2_eq_Suc' append_Nil length_append)
                    with goal1(4) have "length xs' = 1" by auto
                    then obtain y where s: "[y] = xs'" by (metis One_nat_def length_0_conv length_Suc_conv)
                    from r s have t: "[x,y] = xs" by auto
                    moreover from t goal1(1) have "x=b" using doubleton_eq_iff goal1(2) by fastforce
                    moreover from t goal1(1) have "y=a" using doubleton_eq_iff goal1(2) by fastforce
                    ultimately show ?case by auto
                  qed
        
            with A B C have pos: "(Lxy init {a, b}) = [a,b]
                  \<or> (Lxy init {a, b}) = [b,a]" by auto
            
            { fix a::nat
              fix b::nat
              fix qs
              assume as: "a \<noteq> b" "set qs \<subseteq> {a, b}"
              have "T_on_rand' (embed (rTS [])) (fst (embed (rTS [])) [a,b] \<bind> (\<lambda>is. return_pmf ([a,b], is))) qs
                    = T\<^sub>p_on (rTS []) [a, b] qs" by (rule  T_on_embed[symmetric])
              also from as have "\<dots> \<le> 2 * T\<^sub>p_opt [a, b] qs + 2" by (rule TS2) 
              finally have "T_on_rand' (embed (rTS [])) (fst (embed (rTS [])) [a,b] \<bind> (\<lambda>is. return_pmf ([a,b], is))) qs
                    \<le> 2 * T\<^sub>p_opt [a, b] qs + 2"  .
            } note ye=this

            show ?case
              apply(cases "(Lxy init {a, b}) = [a,b]")  
                using ye[OF a b1, unfolded rTS_def] apply(simp)
                using pos ye[OF a[symmetric] b2, unfolded rTS_def] by(simp add: twist) 
          qed
    qed
next
  case goal6
  show ?case unfolding TS_step_d_def by (simp add: split_def TS_step_d_def)
next
  case goal7 
  then show ?case
    apply(induct x) 
      by (simp_all add: rTS_def split_def take_Suc_conv_app_nth config'_rand_snoc ) 
next
  case goal4 then show ?case by simp (* strange subtype effect here, that i dont understande *)
qed (simp_all)

thm TS_compet'[OF TS_pairwise, unfolded T_on_embed[symmetric]]

lemma TS_compet: "compet_rand (embed (rTS [])) 2 {init. distinct init \<and> init \<noteq> []}"
unfolding compet_rand_def static_def
using TS_compet'[OF TS_pairwise] by simp


thm TS_compet[unfolded Partial_Cost_Model.compet_embed[symmetric]]

 
end