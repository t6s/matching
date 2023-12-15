From mathcomp Require Import all_ssreflect. (* from mathcomp *)
From mathcomp Require Import finmap multiset. (* from finmap *)
From mathcomp Require Import mathcomp_extra classical_sets. (* from analysis *)
From infotheo Require Import subgraph_partition.
Require Import mathcomp_extra graph complete_graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

Section is_independent_set.

Definition is_independent_set (G : llugraph) (S : {fset `V(G)}) :=
  [forall e : `E(G), ~~ (`d(e) `<=` S)].

(* TODO: rename *)
Definition is_independent_set' (G : llugraph) (S : {fset `V(G)}) :=
  forall u v, u \in S -> v \in S ->
    ~ exists e : `E(G), `d(e) = [fset u; v].

Lemma is_independent_set1 G (x : `V(G)) : is_independent_set [fset x].
Proof.
apply/forallP => e.
apply/negP=> /fsubset_leq_card.
by rewrite boundary_card2 cardfs1.
Qed.

Lemma is_independent_set0 G : is_independent_set (fset0 : {fset `V(G)}).
Proof.
apply/forallP => e.
apply/negP=> /fsubset_leq_card.
by rewrite boundary_card2 cardfs0.
Qed.

Section classical.
Lemma is_independent_setP' G (S : {fset `V(G)}) :
  (is_independent_set' S) <-> (is_independent_set S).
Proof.
Import boolp.
have -> : is_independent_set S <-> forall e : `E(G), ~~ (`d(e) `<=` S)
  by split; [move/forallP | move=>?; apply/forallP].
suff -> : (is_independent_set' S) = (forall e : `E(G), ~~ (`d(e) `<=` S)) by [].
rewrite /is_independent_set /is_independent_set'.
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

Lemma is_independent_setP G (S : {fset `V(G)}) :
  is_independent_set S <-> is_independent_set' S.
Proof.
split.
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

Definition edgeI (G : llugraph) (S : {fset `E(G)}) e :=
  [exists f, (f \in S) && ~~ [disjoint `d(e) & `d(f)]%fset].

Lemma edgeIP (G : llugraph) (S : {fset `E(G)}) e :
  reflect (exists f, f \in S /\ ~ [disjoint `d(e) & `d(f)]%fset) (edgeI S e).
Proof.
apply: existsPP=> f.
apply: andPP; first exact: idP.
by apply: negP.
Qed.

Lemma edgeIPn (G : llugraph) (S : {fset `E(G)}) e :
  reflect (forall f, f \in S -> [disjoint `d(e) & `d(f)]%fset) (~~ edgeI S e).
Proof.
apply: (iffP idP).
  rewrite negb_exists=> /forallP H f fS.
  by have:= H f; rewrite negb_and -implybE negbK => /implyP /(_ fS).
move=> H.
apply/edgeIP=> -[] f [] fS.
by apply; exact: (H f fS).
Qed.

Lemma indepC_edgeI (G : llugraph) (S : {fset `E(G)}) :
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

Lemma fproperD_neq0 (K : choiceType) (A B : {fset K}) :
  A `<` B -> B `\` A != fset0.
Proof.
move/(fsetDpS (fsubset_refl B)).
by rewrite fsetDv fproper0.
Qed.

Lemma maxmatch_edgeI_opp (G : llugraph) (M : {fset `E(G)}) :
  M \in matching G ->
  (forall e, exists f, f \in M /\ ~ [disjoint `d(e) & `d(f)]%fset) ->
  M \in maximal_matching G.
Proof.
move=> MmG H.
apply/maximal_matchingP; split=> // S MS.
apply/negP=> /matchingP H0.
have:= MS => /fproperD_neq0 /fset0Pn [] e.
rewrite !inE => /andP [] enM eS.
have:= H e => -[] f [] fM nddef.
have ef: e != f by move: enM; apply: contra => /eqP ->.
apply/nddef/fdisjointP=> u ude.
apply/negP=> udf.
have fS : f \in S by have:= MS => /fproper_sub /fsubsetP /(_ f); apply.
by have:= H0 e f eS fS ef.
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

Lemma VDMmax_indep (G : llugraph) (M : {fset `E(G)}) :
  M \in maximal_matching G <->
  M \in matching G /\
    is_independent_set (fsetT `V(G) `\` VofESet M).
Proof.
rewrite is_independent_setP.
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
rewrite -is_independent_setP indepC_edgeI /edgeI => H.
apply maxmatch_edgeI_opp => //.
move => e.
have := H e => /existsP [f] /andP [fM] /negP ndedf.
by exists f; split.
Qed.

Definition independent_set (G : llugraph) :=
  [fset S : {fset `V(G)} | is_independent_set S].

End is_independent_set.

Section independence_number.
(* independence number; often denoted by \alpha(G) in the literature *)
Definition nindep (G : llugraph) := \max_(S in independent_set G) #|` S |.

Lemma exists_nindep (G : llugraph) :
  {S : {fset `V(G)} | is_independent_set S & nindep G = #|`S|}.
Proof.
exists ([arg max_(i > fset0 in independent_set G) #|` i |]).
  case: arg_maxnP.
    by rewrite !inE /=; exact: is_independent_set0.
  by move=> i; rewrite !inE /=.
rewrite /nindep (bigop.bigmax_eq_arg fset0) // !inE /=.
exact: is_independent_set0.
Qed.

(* Hirano and Matsuda *)
Lemma nindmatch_leq_nindep G : nindmatch G <= nindep G.
Proof.
case: (exists_nindmatch G) => M Mind ->.
Abort.

Lemma nmatch_minmatch_leq_nindep G :
  (nmatch G - nminmatch G).*2 <= nindep G.
Abort.

Lemma nindep1P G (x : `V(G)) : nindep G = 1 <-> is_complete_graph G.
Proof.
split.
(*rewrite /nindep.*)
move=> nindepG1.
have: forall S : {fset `V(G)}, is_independent_set S -> #|`  S| < 2.
  move=> S.
  apply: contraLR.
  rewrite -leqNgt.
Abort.

End independence_number.

Section S_suspension.
End S_suspension.
