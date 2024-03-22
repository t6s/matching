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

Section get1_boundary.
Variable G : llugraph.
(*
Let get1_boundary_ (G : llugraph) :  `E(G) -> `V(G).
move=> e.
move: (boundary_exists e).
by case/boolp.cid => v.
Defined.
Definition get1_boundary := Eval hnf in get1boundary_.
*)

Definition get1_boundary (e : `E(G)) :=
  sval (boolp.cid (boundary_exists e)).

Local Notation tau := get1_boundary.

Lemma get1_in_boundary e : get1_boundary e \in `d(e).
Proof. by rewrite /tau; case: boolp.cid => x. Qed.

Lemma get1_boundary_inj (M : {fset `E(G)}) :
  M \in matching G -> {in M & M, injective tau}.
Proof.
move => /matchingP MiG e0 e1 e0M e1M /eqP H.
apply/eqP; move: H; apply:contraLR => e01.
move: (MiG e0 e1 e0M e1M e01) => /fdisjointP disj01.
apply/eqP => p01.
move:(disj01 (tau e0)).
rewrite {2}p01 !get1_in_boundary //.
by move /(_ erefl) /negP /(_ erefl).
Qed.

(* move to graph.v *)
Lemma boundary_sig2 (e : `E(G)) : {uv | uv.1 != uv.2 /\ `d(e) = [fset uv.1; uv.2]}.
Proof. exact/cardfs2_sig/boundary_card2. Qed.

Lemma im_get1_boundary_indep (M : {fset `E(G)}) :
  M \in induced_matching G ->
        [fset tau e | e in M] \in independent_set G.
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

End get1_boundary.

Section independence_number.
(* independence number; often denoted by \alpha(G) in the literature *)
Definition nindep (G : llugraph) := \max_(S in independent_set G) #|` S |.

Lemma leq_nindep (G : llugraph) (S : {fset `V(G)}) :
  S \in independent_set G -> #|` S | <= nindep G.
Proof.
move=> Sindep.
by apply:leq_bigmax_cond.
Qed.

Lemma exists_nindep (G : llugraph) :
  {S : {fset `V(G)} | S \in independent_set G & nindep G = #|` S |}.
Proof.
apply: eq_bigmax_cond.
apply/card_gt0P.
exists fset0.
rewrite inE /=.
apply is_independent_set0.
Qed.

(* before exists_nindep's proof *)
(*
Proof.
exists ([arg max_(i > fset0 in independent_set G) #|` i |]).
  case: arg_maxnP.
    by rewrite !inE /=; exact: is_independent_set0.
  by move=> i; rewrite !inE /=.
rewrite /nindep (bigop.bigmax_eq_arg fset0) // !inE /=.
exact: is_independent_set0.
Qed.
 *)

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
