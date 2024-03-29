From mathcomp Require Import all_ssreflect. (* from mathcomp *)
From mathcomp Require Import finmap multiset. (* from finmap *)
From mathcomp Require Import mathcomp_extra classical_sets. (* from analysis *)
From infotheo Require Import subgraph_partition.
Require Import mathcomp_extra graph complete_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.


Section independent_set.
Variable G : llugraph.

Section pred.
Variable S : {fset `V(G)}.

Definition is_independent_set := [forall e : `E(G), ~~ (`d(e) `<=` S)].

Lemma is_independent_setP :
  reflect {in S & S, forall u v, ~ exists e : `E(G), `d(e) = [fset u; v]}
          is_independent_set.
Proof.
apply: (iffP idP).
  move=> /forallP idG u v uS vS [] e deuv.
  have := idG e => /negP; apply; rewrite deuv.
  by apply/fsubsetP => x; rewrite !inE => /orP [] /eqP ->.
move=> H; apply/forallP => e.
apply/negP => /fsubsetP.
rewrite /{subset _ <= _}.
have := boundary_card2 e => /cardfs2_sig [] [u v] /= [] uv deuv.
rewrite deuv.
case/boolP: (u \in S); last first.
  move => /[swap] /(_ u) /[swap] /negPf ->.
  by rewrite !inE eqxx /= => /(_ erefl).
move=> uS /(_ v).
rewrite !inE eqxx orbT => /(_ erefl).
have := H _ _ uS => /[apply].
by apply; exists e.
Qed.
End pred.          

Definition independent_set := [fset S : {fset `V(G)} | is_independent_set S].

(* independence number; often denoted by \alpha(G) in the literature *)
Definition nindep := \max_(S in independent_set) #|` S |.

End independent_set.


Section independent_set_lemmas.
Variables (G : llugraph).

Local Notation independent_set := (independent_set G).

Lemma independent_setP (S : {fset `V(G)}) :
  reflect
    {in S & S, forall u v, ~ exists e : `E(G), `d(e) = [fset u; v]}
    (S \in independent_set).
Proof. by rewrite !inE andTb; exact: is_independent_setP. Qed.

Lemma fset1_independent (x : `V(G)) : [fset x ] \in independent_set.
Proof.
rewrite !inE /=.
apply/forallP => e.
apply/negP=> /fsubset_leq_card.
by rewrite boundary_card2 cardfs1.
Qed.

Lemma fset0_independent : fset0 \in independent_set.
Proof.
rewrite !inE /=.
apply/forallP => e.
apply/negP=> /fsubset_leq_card.
by rewrite boundary_card2 cardfs0.
Qed.

Section classical.
Let is_independent_set' (S : {fset `V(G)}) :=
  {in S & S, forall u v, ~ exists e : `E(G), `d(e) = [fset u; v]}.

Let is_independent_setP' (S : {fset `V(G)}) :
  (is_independent_set' S) <-> (is_independent_set S).
Proof.
Import boolp.
have -> : is_independent_set S <-> forall e : `E(G), ~~ (`d(e) `<=` S)
  by split; [move/forallP | move=>?; apply/forallP].
suff -> : (is_independent_set' S) = (forall e : `E(G), ~~ (`d(e) `<=` S)) by [].
rewrite /is_independent_set /is_independent_set' /prop_in11.
under [in LHS]eq_forall => u.
  under eq_forall => v.
    rewrite -forallNE.
    rewrite conj_imply_head -fset2SE.
    rewrite swap_imply_head.
    under eq_forall => e.
      rewrite implyE -!not_andE.
      rewrite [X in ~ X](_ : _ = (`d(e) `<=` S /\ `d(e) = [fset u; v])); last first.
        by rewrite propeqE; split => -[] ?; [move-> | move<-].
      rewrite andC not_andE -implyE.
      over.    
    over.
  rewrite swap_imply_head.
  under eq_forall do rewrite curry_imply_head.
  over.
rewrite swap_imply_head.
under eq_forall=> e.
  rewrite curry_imply_head.
  rewrite [X in X -> _](_ : _ = True); last first.
    rewrite propeqE; split=> // _.
    have:= boundary_card2 e=> /cardfs2_sig [] [] u v /= [] _ ->.
    by exists u, v.
  rewrite implyTP -negE.
  over.
done.
Qed.
End classical.

Lemma indepC_edgeI (S : {fset `E(G)}) :
  is_independent_set (fsetT `V(G) `\` VofESet S) <->
  forall e, edgeI S e.
Proof.
split.
  move=> /forallP iVDS e.
  have:= iVDS e.
  apply: contraNT.
  move/edgeIPn=> H.
  apply/fsubsetP=> u ude.
  rewrite !inE andbT.
  apply/bigfcupP=> -[] /= U.
  rewrite andbT.
  case/imfsetP=> f /= fS -> udf.
  have:= H f fS.
  move/fdisjointP/(_ u ude)/negPf.
  by rewrite udf.
move=> H; apply/forallP => e.
apply/fsubsetP => deVDS.
have:= H e => /edgeIP -[] f [] fS /negP /fdisjointP.
apply=> u ude.
apply/negP=> udf.
have:= deVDS u ude.
rewrite !inE andbT=> /bigfcupP.
apply; exists `d(f) => //.
rewrite andbT; apply/imfsetP.
by exists f.
Qed.

(*
Def.
nindep := \max_(S in indepenedent_set G) #|` S |

Lem.
nindmatch <= nindep
Proof. Construct an independent set from a given indeuced matching.

Lem.
2 * (nmatch - nmatch) <= nindep
*)          

(* TODO: rename *)
Lemma VDMmax_indep (M : {fset `E(G)}) :
  M \in maximal_matching G <->
  M \in matching G /\
    (fsetT `V(G) `\` VofESet M) \in independent_set.
Proof.
rewrite -(rwP (independent_setP _)) /=.
split.
  move => Mmax.
  split; first by case/maximal_matchingP: Mmax.
  move => u v.
  rewrite !inE !andbT => uM vM.
  case => e deuv.
  have:= maxmatch_edgeI e Mmax => -[] f [] fM.
  apply.
  apply/fdisjointP.
  move => x.
  rewrite deuv !inE => /orP [] /eqP -> .
    move/bigfcupP: uM.
    apply: contra_notN => udf.
    exists `d(f) => //.
    rewrite andbT.
    apply /imfsetP.
    by exists f.
  move/bigfcupP: vM.
  apply: contra_notN => vdf.
  exists `d(f) => //.
  rewrite andbT.
  apply /imfsetP.
  by exists f.            
case=> MmG.
rewrite (rwP (is_independent_setP _)) indepC_edgeI /edgeI => H.
apply maxmatch_edgeI_opp => //.
move => e.
have := H e => /existsP [f] /andP [fM] /negP ndedf.
by exists f; split.
Qed.

Lemma im_get1_boundary_indep (M : {fset `E(G)}) :
  M \in induced_matching G ->
        [fset get1_boundary e | e in M] \in independent_set.
Proof.
move=> /[dup] Mind /induced_matchingP Mind'.
rewrite !inE /=.
apply/forallP => x.
apply/fsubsetP.
have:= boundary_sig2 x => -[] [] u v /= [] /[swap] dxuv /[swap] /[!dxuv] dxM.
have ux : u \in [fset u; v] by rewrite !inE eqxx.
have vx : v \in [fset u; v] by rewrite !inE eqxx orbT.
have:= dxM u ux => /imfsetP [] e /= eM ute.
have:= dxM v vx => /imfsetP [] f /= fM vtf.
rewrite ute vtf => tauef.
have ef : e != f by apply/eqP; move: tauef => /[swap] ->; rewrite eqxx.
have:= Mind' e f eM fM ef x.
apply/orP.
rewrite dxuv [in X in _ || X]fsetUC.
rewrite /fdisjoint !fsetIUr !fsetI1 ute vtf !get1_in_boundary //.
by rewrite !fsetU_eq0 -!cardfs_eq0 !cardfs1 /=.
Qed.

End independent_set_lemmas.


Section nindep_lemmas.

Lemma leq_nindep (G : llugraph) (S : {fset `V(G)}) :
  S \in independent_set G -> #|` S | <= nindep G.
Proof.
move=> Sindep.
by apply:leq_bigmax_cond.
Qed.

Import Order.Theory.

Lemma exists_nindep (G : llugraph) :
  {S : {fset `V(G)} | S \in independent_set G & nindep G = #|` S |}.
Proof.
(*
under (@boolp.funext _ _ (fun S => nindep G = #|` S|)) => S.
  rewrite /nindep.
  rewrite (bigmax_eq_arg _ fset0) ?fset0_independent //.
  over.
exists [arg max_(i > fset0 in independent_set G) #|` i|] => //.
*)
eexists; last by rewrite /nindep (bigmax_eq_arg _ fset0) ?fset0_independent.
by case: arg_maxP => //; exact: fset0_independent.
Qed.  

(* Hirano and Matsuda *)
Lemma nindmatch_leq_nindep (G : llugraph) : nindmatch G <= nindep G.
Proof.
case: (exists_nindmatch G) => M Mind nM.
have mM : M \in matching G by have:= induced_sub_matching G => /fsubsetP; exact.
have:= im_get1_boundary_indep Mind.
set T := [fset get1_boundary e | e in M].
have TM: #|` T| = #|` M| by apply: card_in_imfset => ? ? /=; exact: (get1_boundary_inj mM).
by move=> Tind; rewrite nM -TM; exact: leq_bigmax_cond.
Qed.

Lemma nmatch_minmatch_leq_nindep G :
  (nmatch G - nminmatch G).*2 <= nindep G.
Proof.
case: (exists_nminmatch G) => N /VDMmax_indep [] ? ? ->.
set X := leqLHS.
suff: X <= #|` fsetT `V(G) `\` VofESet N |.
  move/leq_trans; apply.
  exact: leq_bigmax_cond.
rewrite /X cardfsD fsetIT matching_double_card // doubleB cardfsT.
exact/leq_sub2r/double_nmatch_leq_cardVG.
Qed.

Lemma nindep_gt0 G (x : `V(G)) : 0 < nindep G.
Proof.
have:= (fset1_independent x) => /leq_nindep.
by apply: leq_trans; rewrite cardfs1.
Qed.

Lemma and_iff2l (A B C : Prop) : (A -> (B <-> C)) <-> (A /\ B <-> A /\ C).
Proof. tauto. Qed.

Local Notation is_complete_graph' G :=
  (forall v w : `V(G), v != w -> exists e : `E(G), `d(e) = [fset v; w]).

Lemma not_adjacent_indepP G (x y : `V(G)) :
  x != y -> ~ (exists e, `d(e) = [fset x; y]) <->
              (exists S, S \in independent_set G /\ x \in S /\ y \in S).
Proof.
move=> xy; split.
  move=> H; exists [fset x; y].
  rewrite !inE /= !eqxx orbT /=; split=> //.
  apply/is_independent_setP=> u v.
  rewrite !inE=> /orP [] /eqP -> /orP [] /eqP ->.
  - case=> e; rewrite fsetUid => e1.
    by have:= boundary_card2 e; rewrite e1 cardfs1.
  - by [].
  - by under boolp.eq_exists do rewrite fsetUC.
  - case=> e; rewrite fsetUid => e1.
    by have:= boundary_card2 e; rewrite e1 cardfs1.
case => /= S [] /independent_setP SG [] xS yS.
exact: SG.
Qed.

Lemma adjacent_indepP G (x y : `V(G)) :
  x != y -> (exists e, `d(e) = [fset x; y]) <->
              ~ (exists S, S \in independent_set G /\ x \in S /\ y \in S).
Proof. rewrite boolp.iff_notr; exact: not_adjacent_indepP. Qed.

Lemma nindep1P G (x : `V(G)) :
  injective (fun e : `E(G) => `d(e)) /\ nindep G = 1 <-> is_complete_graph G.
Proof.
rewrite -and_iff2l=> _.
have:= nindep_gt0 x.
rewrite leq_eqVlt => /orP [/eqP H|].
  rewrite -H; split=> // _ v w vw.
  rewrite adjacent_indepP // => -[] /= S [] SG [] vS wS.
  have: #|` S| <= nindep G by exact: leq_bigmax_cond.
  rewrite -H.
  have: 1 < #|` S|.
    rewrite cardfE; apply/card_gt1P.
    exists [` vS], [` wS]; split; rewrite ?inE //.
    by move/leq_trans/[apply].
have := exists_nindep G => -[] S Sind ->.
rewrite [X in 1 < X]cardfE=> /card_gt1P /= [] [] y /= yS [] [] z /= zS [] yS' zS' yz'.
have := Sind => /independent_setP => /(_ y z yS zS) Sind'.
have yz: y != z.
  move: yz'; apply: contra=> /eqP yz.
  by apply/eqP/val_inj.
clear yS' zS' yz'.
rewrite (rwP eqP) -(rwP (cardfs1P S)) [X in X <-> _](_ : _ <-> False); last first.
  split=> //.
  case=> u uS; move: yS; rewrite uS inE; move: zS; rewrite uS inE => /eqP <-.
  exact/negP.
by split=> // /(_ y z yz).
Qed.

End nindep_lemmas.

Section S_suspension.
End S_suspension.
