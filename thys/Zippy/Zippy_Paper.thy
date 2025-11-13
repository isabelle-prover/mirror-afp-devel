\<^marker>\<open>creator "Kevin Kappelmann"\<close>
section \<open>Zippy Paper Guide\<close>
theory Zippy_Paper
  imports
    Pure
begin

paragraph \<open>Summary\<close>
text \<open>Guide for the preprint\<^cite>\<open>zippy\<close>\<close>

text \<open>
\<^item> General Information
  \<^item> Unfortunately, employing the polymorphic record extension mechanism described in the paper
    hits severe performance problems of the Poly/ML compiler.
    To get around minute-long compilation times, all data fields of the zipper have to be
    instantiated in one go rather than by repeated instantiation of polymorphic fields,
    cf. @{file "Zippy/Instances/zippy_instance_base.ML"}.
    Relevant issue on GitHub: https://github.com/polyml/polyml/issues/213

\<^item> Section 2
  \<^item> Nodes @{file "Gen_Zippers/Zippers5/Alternating_Zippers/Instances/Nodes/node.ML"}

\<^item> Section 2.1
  \<^item> Categories and Arrows
    @{file "ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/Categories/category.ML"}

  \<^item> Morphs
    \<^item> Morphism Base @{file "Gen_Zippers/Zippers5/Morphs/morph_base.ML"}
    \<^item> Morphisms @{file "Gen_Zippers/Zippers5/Morphs/morph.ML"}

  \<^item> Zippers
    \<^item> Zipper Morphs @{file "Gen_Zippers/Zippers5/Zippers/zipper_morphs.ML"}
    \<^item> Zipper Data @{file "Gen_Zippers/Zippers5/Zippers/zipper_data.ML"}
    \<^item> Zipper @{file "Gen_Zippers/Zippers5/Zippers/zipper.ML"}

  \<^item> Linked Zippers
    \<^item> Linked Zipper Morphs @{file "Gen_Zippers/Zippers5/Linked_Zippers/linked_zipper_morphs.ML"}
    \<^item> Linked Zippers @{file "Gen_Zippers/Zippers5/Linked_Zippers/linked_zipper.ML"}

  \<^item> Alternating Zippers
    \<^item> Alternating Zipper Morphs
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/alternating_zipper_morphs.ML"}
    \<^item> Alternating Zippers
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/alternating_zipper.ML"}
    \<^item> Alternating Zipper Product
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/pair_alternating_zipper.ML"}

\<^item> Section 2.1.1
  \<^item> Monads
    @{file "ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/typeclass_base.ML"}

  \<^item> Kleisli Category
    @{file "ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/Categories/category_instance.ML"}

  \<^item> Generating Alternating Zippers from Node Zippers
    \<^item> Extending the Alternating Zipper
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/Instances/Nodes/alternating_zipper_nodes.ML"}
    \<^item> Extending and Lifting the Input Zippers
      @{file "Gen_Zippers/Zippers5/Zippers/extend_zipper_context.ML"}

  \<^item> Generating Node Zippers
    @{file "Gen_Zippers/Zippers5/Alternating_Zippers/Instances/Nodes/alternating_zipper_nodes_simple_zippers.ML"}

\<^item> Section 2.2
  \<^item> Lenses @{file "ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/Lenses/lens.ML"}

\<^item> Section 3
  \<^item> We implemented a generalisation of the state monad that also allows the state type to change
    during computation. Such states are not monads but (Atkey) indexed monads.
    \<^item> Atkey Indexed Monads @{file "ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/itypeclass_base.ML"}
    \<^item> Indexed State Monad @{file "ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/State/istate.ML"}
    \<^item> State Monad @{file "ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/State/istate.ML"}
  \<^item> Antiquotations
    \<^item> Sources
      @{file "ML_Typeclasses/Antiquotations/ML_Eval_Antiquotation.thy"}
      @{file "ML_Typeclasses/Antiquotations/ML_Args_Antiquotations.thy"}
      @{file "Antiquotations/ML_IMap_Antiquotation.thy"}
    \<^item> Example Configuration and Follow-Up ML-Code Generation
      @{file "Gen_Zippers/Zippers5/Morphs/ML_Morphs.thy"}

\<^item> Section 4. We highlight the differences/extensions to the paper description
  \<^item> The zipper uses an additional "action cluster" layer that sits between a goal cluster and
    an action. Action clusters collect related actions, e.g. one could create an action cluster for
    classical reasoners, one for simplification actions, etc. This gives the search tree some more
    structure but is not strictly necessary (it is thus omitted in the paper).

  \<^item> Adding Actions @{file "Zippy/Actions/zippy_paction_mixin_base.ML"}
    \<^item> Action nodes do not store a static cost and action but, more generally,
      an "action with priority" (paction) that dynamically computes a priority, action pair.
    \<^item> Action clusters store a "copy" morphism such that actions generating new children can move
      their action siblings to the newly created child while updating their siblings' goal focuses
      (since the number and order of goals may have changed in the new child).

  \<^item> Adding Goals @{file "Zippy/Goals/zippy_goals_mixin_base.ML"}
    \<^item> Goal Clusters @{file "Zippy/Goals/Base/zippy_goal_clusters.ML"}
    \<^item> Goal Cluster @{file "Zippy/Goals/Base/zippy_goal_cluster.ML"}
    \<^item> Goal Focus @{file "Zippy/Goals/Base/zippy_goal_focus.ML"}
    \<^item> Union Find @{file "Union_Find//imperative_union_find.ML"}

  \<^item> Lifting Tactics
    \<^item> Lifting Isabelle Tactics to Zippy Tactics @{file "Zippy/Tactics/Base/zippy_ztactic.ML"}
    \<^item> Lifting Zippy Tactics to Actions @{file "Zippy/Instances/zippy_instance_tactic.ML"}

  \<^item> The Basic Search Tree Model @{file "Zippy/Instances/zippy_instance_base.ML"}
    Since there are is always exactly one goal clusters node, we do not use lists for the topmost layer.
    \<^item> List Zipper @{file "Gen_Zippers/Zippers5/Zippers/Instances/list_zipper.ML"}

  \<^item> Adding Failure and State @{file "Zippy/Instances/Zippy_Instance_Pure.thy"}
    \<^item> Option Monad and Transformers
      @{file "ML_Typeclasses/Gen_Typeclasses/Typeclasses_1/typeclass_base_instance.ML"}

  \<^item> Adding Positional Information
    \<^item> Extending the Alternating Zipper @{file "Zippy/Positions/zippy_positions_mixin_base.ML"}
    \<^item> Alternating (Global) Position Zipper
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/Instances/alternating_global_position_zipper.ML"}

  \<^item> Running a Search
    \<^item> Postorder Depth-First Enumeration for Zippers
      @{file "Gen_Zippers/Zippers5/Zippers/Utils/df_postorder_enumerate_zipper.ML"}
    \<^item> Postorder Depth-First Enumeration for Alternating Zippers
      @{file "Gen_Zippers/Zippers5/Alternating_Zippers/Utils/df_postorder_enumerate_alternating_zipper.ML"}
    \<^item> Runs @{file "Zippy/Runs/zippy_run_mixin.ML"}

  \<^item> Retrieving Theorems from the Tree
    @{file "Zippy/Goals/Lists/zippy_lists_goals_results_top_meta_vars_mixin.ML"}

  \<^item> Final example usages can be found here
    @{file "Zippy/Instances/Zip/Examples/Zip_Examples.thy"}.
\<close>

end
