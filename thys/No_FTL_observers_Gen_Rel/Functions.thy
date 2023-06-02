(*
   Mike Stannett
   Date: April 2020
   Updated: Jan 2023
*)

section \<open> Functions \<close>

text \<open>This theory characterises the various types of function 
(injective, bijective, etc).\<close>

theory Functions
  imports Points
begin

text \<open> We do not assume a priori that all of the functions we define are
well-defined or total. We therefore need to allow for functions which are 
only partially defined, and also for "functions" which might be multi-valued.
For example, we cannot say in advance whether one observer might see another's
worldline as a bifurcating structure rather than a basic single-valued trajectory.

To achieve this we'll often think of functions as relations and write
"f x y = true" instead of "f x = y". Similarly, a spacetime set S will be 
sometimes be expressed as its characteristic function.
\<close>


class Functions = Points 
begin

abbreviation bounded :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> bool" 
  where "bounded f \<equiv> \<exists> bnd > 0 . (\<forall> p . (norm2 (f p)  \<le> bnd * (norm2 p)))"


(* Standard terminology translated to the relational viewpoint *)

abbreviation composeRel :: 
" ('a Point \<Rightarrow> 'a Point \<Rightarrow> bool)
\<Rightarrow>('a Point \<Rightarrow> 'a Point \<Rightarrow> bool)
\<Rightarrow>('a Point \<Rightarrow> 'a Point \<Rightarrow> bool)"
  where "(composeRel g f) p r \<equiv> (\<exists> q . ((f p q) \<and> (g q r)))"


abbreviation injective :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> bool" 
  where "injective f \<equiv> \<forall> x1 x2 y1 y2. 
                (f x1 y1 \<and> f x2 y2) \<and> (x1 \<noteq> x2) \<longrightarrow> (y1 \<noteq> y2)"

abbreviation definedAt :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "definedAt f x \<equiv> \<exists> y . f x y"

abbreviation domain :: "('a Point => 'a Point \<Rightarrow> bool) \<Rightarrow> 'a Point set"
  where "domain f  \<equiv> { x . definedAt f x }"

abbreviation total :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> bool" 
  where "total f \<equiv> \<forall> x . (definedAt f x)"

abbreviation surjective :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> bool" 
  where "surjective f \<equiv> \<forall> y . \<exists> x . f x y"

abbreviation bijective :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> bool" 
  where "bijective f \<equiv> (injective f) \<and> (surjective f)"

abbreviation invertible :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> bool"
  where "invertible f \<equiv> \<forall> q . (\<exists> p . (f p = q) \<and> (\<forall>x. f x = q \<longrightarrow> x = p))"

  (* Image of a set *)

fun applyToSet :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> 'a Point set \<Rightarrow> 'a Point set" 
  where "applyToSet f s = { q . \<exists> p \<in> s . f p q }" 


(* Recovering normal-style functions *)
abbreviation singleValued :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "singleValued f x  \<equiv>   \<forall> y z . (((f x y) \<and> (f x z)) \<longrightarrow> (y = z))"

abbreviation isFunction :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> bool"
  where "isFunction f \<equiv> \<forall> x . singleValued f x"

abbreviation isTotalFunction :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> bool"
  where "isTotalFunction f \<equiv> (total f) \<and> (isFunction f)"

fun toFunc:: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> 'a Point \<Rightarrow> 'a Point"
  where "toFunc f x = (SOME y . f x y)"

fun asFunc :: "('a Point \<Rightarrow> 'a Point) \<Rightarrow> ('a Point \<Rightarrow> 'a Point \<Rightarrow> bool)"
  where "(asFunc f) x y = (y = f x)"



(* g approximates f at x *)
(* Email of 16/07/2019 says final inequality should be \<le> not <. *)

subsection \<open> Differentiable approximation \<close>

text \<open>Here we define differentiable approximation. This will be used later
when we define what it means for a worldview transformation to be "approximated"
by an affine transformation.\<close>

abbreviation diffApprox :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> 
                            ('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow>
                             'a Point \<Rightarrow> bool"
  where "diffApprox g f x \<equiv> (definedAt f x) \<and>
    (\<forall> \<epsilon> > 0 . (\<exists> \<delta> > 0 . (\<forall> y .
      ( (y within \<delta> of x)
        \<longrightarrow> 
        ( (definedAt f y) \<and> (\<forall> u v . (f y u \<and> g y v) \<longrightarrow>
         ( sep2 v u ) \<le> (sqr \<epsilon>) * sep2 y x )))  )
  ))"


abbreviation cts ::  "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> 'a Point \<Rightarrow> bool"
  where "cts f x \<equiv> \<forall>y . (f x y) \<longrightarrow> (\<forall>\<epsilon>>0. \<exists>\<delta>>0. 
          (applyToSet f (ball x \<delta>)) \<subseteq> ball y \<epsilon>)"
                    

fun invFunc :: "('a Point \<Rightarrow> 'a Point \<Rightarrow> bool) \<Rightarrow> ('a Point \<Rightarrow> 'a Point \<Rightarrow> bool)"
  where "(invFunc f) p q = f q p"


(* ********************************************************************** *)
(* LEMMAS *)

lemma lemBijInv: "bijective (asFunc f) \<longleftrightarrow> invertible f"  
  by (metis asFunc.elims(1))
  

(* if g approximates f at x, then g(x) and f(x) share at least one value *)
subsection \<open> lemApproxEqualAtBase \<close>

text \<open>The following lemma shows (as one would expect) that when one 
function differentiably approximates another at a point, they take equal values 
at that point.\<close>

lemma lemApproxEqualAtBase:
assumes "diffApprox g f x"
shows "(f x y \<and> g x z) \<longrightarrow> (y = z)"
proof -
  { fix y z
    assume hyp: "f x y \<and> g x z"

    have lt01: "0 < 1" by auto
    then obtain d where dprops: "(d > 0) \<and> (\<forall> y .
        ( (y within d of x) 
          \<longrightarrow> 
          ( \<forall> u v . (f y u \<and> g y v) \<longrightarrow>
           ( sep2 v u ) \<le> (sqr 1) * sep2 y x ))  )
        " using assms(1) by best
  
    hence "x within d of x" by auto
    hence "\<forall> u v . (f x u \<and> g x v) \<longrightarrow> (sep2 v u) \<le> (sqr 1) * sep2 x x" 
      using dprops by blast
    hence sep0: "(sep2 z y) \<le> 0" using hyp by auto
    { assume "z \<noteq> y"
      hence "sep2 z y > 0" using lemNotEqualImpliesSep2Pos[of "z" "y"] by auto
      hence "False" using sep0 by auto
    }
    hence "z = y" by auto
  }
  thus ?thesis by auto
qed


lemma lemCtsOfCtsIsCts:
  assumes "cts f x"
and       "\<forall>y . (f x y) \<longrightarrow> (cts g y)"
shows     "cts (composeRel g f) x"
proof -
  { fix z
    assume z: "(composeRel g f) x z"
    then obtain y where y: "f x y \<and> g y z" by auto

    { fix e
      assume epos: "e > 0"

      have "(\<forall>\<epsilon>>0. \<exists>\<delta>>0.(applyToSet g (ball y \<delta>)) \<subseteq> ball z \<epsilon>)"
        using assms(2) y by auto
      then obtain dy 
        where dy: "(dy > 0) \<and> ((applyToSet g (ball y dy)) \<subseteq> ball z e)"
        using epos y by auto

      have "(\<forall>\<epsilon>>0. \<exists>\<delta>>0.(applyToSet f (ball x \<delta>)) \<subseteq> ball y \<epsilon>)"
        using y assms(1) by auto
      then obtain d
        where d: "(d > 0) \<and> ((applyToSet f (ball x d)) \<subseteq> ball y dy)"
        using dy by auto

      { fix w
        assume w: "w \<in> applyToSet (composeRel g f) (ball x d)"
        then obtain u v 
          where v: "(u \<in> ball x d) \<and> (f u v) \<and> (g v w)" by auto
        hence "v \<in> ball y dy" using d by auto
        hence "w \<in> ball z e" using v dy by auto
      }
      hence "applyToSet (composeRel g f) (ball x d) \<subseteq> ball z e" by auto
      hence "\<exists>d>0. (applyToSet (composeRel g f) (ball x d) \<subseteq> ball z e)" 
        using d by auto
    }
    hence "\<forall>e>0. \<exists>d>0. applyToSet (composeRel g f) (ball x d) \<subseteq> ball z e" by auto
  }
  thus ?thesis by auto
qed


lemma lemInjOfInjIsInj:
  assumes "injective f"
and       "injective g"
shows     "injective (composeRel g f)"
proof -
  { fix x1 z1 x2 z2
    assume hyp: "(composeRel g f) x1 z1 \<and> (composeRel g f) x2 z2 \<and> (x1 \<noteq> x2)"
    then obtain y1 y2 
      where ys: "(f x1 y1) \<and> (g y1 z1) \<and> (f x2 y2) \<and> (g y2 z2)" by auto
    hence "y1 \<noteq> y2" using hyp assms(1) by auto
    hence "z1 \<noteq> z2" using  assms(2) ys by auto
  }
  thus ?thesis by auto
qed


lemma lemInverseComposition:
  assumes "h = composeRel g f"
  shows   "(invFunc h) = composeRel (invFunc f) (invFunc g)"
proof -
  { fix p r
    { assume hyp: "h p r"
      then obtain q where "f p q \<and> g q r" using assms by auto
      hence "(invFunc g) r q \<and> (invFunc f) q p" by force
      hence "(composeRel (invFunc f) (invFunc g)) r p" by blast
    }
    hence l2r: "(invFunc h) r p  \<longrightarrow> (composeRel (invFunc f) (invFunc g)) r p" by auto

    { assume "(composeRel (invFunc f) (invFunc g)) r p"
      then obtain q where "(invFunc g) r q  \<and>  (invFunc f) q p" by auto
      hence "(invFunc h) r p" using assms by auto
    }

    hence "(composeRel (invFunc f) (invFunc g)) r p  \<longleftrightarrow> (invFunc h) r p"
      using l2r by auto
  }
  thus ?thesis by fastforce
qed


lemma lemToFuncAsFunc:
  assumes "isFunction f"
and       "total f"
shows     "asFunc (toFunc f) = f"
proof -
  { fix p r
    { assume "(asFunc (toFunc f)) p r"
      hence "f p r" using someI[of "f p"] assms(2) by auto
    }
    hence l2r: "(asFunc (toFunc f)) p r \<longrightarrow> f p r" by auto
    { assume fpr: "f p r"
      hence "(asFunc (toFunc f)) p r" using someI[of "f p"] assms(1) by auto
    }

    hence "f p r \<longleftrightarrow> (asFunc (toFunc f)) p r" using l2r by auto
  }
  thus ?thesis by blast
qed


lemma lemAsFuncToFunc: "toFunc (asFunc f) = f"
  by fastforce




end (* of class Functions *)

end (* of theory Functions *)

