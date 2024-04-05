From mathcomp Require Import all_ssreflect. (* from mathcomp *)
From mathcomp Require Import finmap multiset. (* from finmap *)
From mathcomp Require Import mathcomp_extra classical_sets. (* from analysis *)
Require Import mathcomp_extra graph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

Section biboundary.
Variable G : llugraph.

Definition biboundary (e : `E(G)) :=
  let: exist (a, b) _ := cardfs2_sig (boundary_card2 e) in
  [fset (a, b); (b, a)].

Lemma biboundaryE (e : `E(G)) (a b : `V(G)) :
 `d(e) = [fset a; b] -> biboundary e = [fset (a, b); (b, a)].
Proof.
move=> deab.
have ab: a != b.
  apply/eqP; move:deab => /[swap] -> /(congr1 (size \o val)) /=.
  by rewrite boundary_card2 fsetUid cardfs1.
move: deab.
rewrite /biboundary /=.
case: cardfs2_sig => [] [u v] /= [uv] -> /fsetP uvab.
apply/fsetP=> -[x y].
rewrite !inE !xpair_eqE.
wlog: u v a b uv ab uvab / (u == a); last first.
  move: uvab => /[swap] /eqP -> /(_ b).
  by rewrite !inE (eq_sym b a) (negPf ab) eqxx /= => /eqP ->.
case/boolP: (u == a).
  by move /[swap] /[apply]; apply.
move=> ua.
move: (uvab) => /(_ u).
rewrite !inE eqxx (negPf ua) /= => /esym /[swap] /[apply].
rewrite [in X in _ -> _ = X]orbC.
apply=> //.
  by rewrite eq_sym.
by move: uvab; rewrite [X in _ =i X -> _]fsetUC.
Qed.

Lemma in_biboundary (e : `E(G)) a b :
  ((a, b) \in biboundary e) = (`d(e) == [fset a; b]).
Proof.
pose f (p : `V(G) * `V(G)) := let: (x,y) := p in [fset x; y].
apply/idP/idP.
  rewrite /biboundary.
  case: cardfs2_sig => -[u v] /= [] uv ->.
  by rewrite !inE => /orP [] /eqP abuv; rewrite -/(f (a, b)) abuv // fsetUC.
move /eqP /biboundaryE ->.
by rewrite !inE eqxx.
Qed.

Lemma in_biboundary_neq (e : `E(G)) (a b : `V(G)) :
  (a, b) \in biboundary e -> a != b.
Proof.
rewrite in_biboundary=> deab.
apply/eqP; move: deab=> /[swap] ->.
move/eqP/(congr1 (size \o val)).
by rewrite /= fsetUid boundary_card2 cardfs1.
Qed.

Lemma cardfs_biboundary (e : `E(G)) : #|` biboundary e | = 2.
Proof.
rewrite /biboundary.
case: cardfs2_sig => [] [u v] [uv deuv].
rewrite cardfs2 /=.
suff-> : (u, v) != (v, u) by [].
by rewrite xpair_eqE (eq_sym v u) !(negPf uv).
Qed.

Lemma boundary_biboundary_eq (e f : `E(G)) :
 (`d(e) == `d(f)) = (biboundary e == biboundary f).
Proof.
have := cardfs2_sig (boundary_card2 e) => -[] [] a b /= [] ab deab.
have := cardfs2_sig (boundary_card2 f) => -[] [] c d /= [] cd dfcd.
apply/idP/idP.
  move/eqP.
  rewrite dfcd => /biboundaryE ->.
  by rewrite (biboundaryE dfcd).
move/eqP/fsetP/(_ (a,b)).
rewrite (biboundaryE deab) in_biboundary 2!inE eqxx /=.
move/esym/eqP ->.
by apply/eqP.
Qed.

Lemma ex_biboundary_eq (e f : `E(G)) :
  (exists p, (p \in biboundary e) && (p \in biboundary f)) ->
  biboundary e = biboundary f.
Proof.
case=> -[a b] /andP [].
by rewrite !in_biboundary => /eqP /biboundaryE -> /eqP /biboundaryE ->.
Qed.

Lemma boundary_biboundary_inj :
  injective (fun e : `E(G) => `d(e)) <-> injective biboundary.
Proof.
by split; move=> H e f /eqP;
                 [ rewrite -boundary_biboundary_eq => /eqP
                 | rewrite boundary_biboundary_eq => /eqP ];
                 exact: H.
Qed.

End biboundary.

Module CompleteGraph.
Section def.
Variable V : finType.
Definition E :=
  [fset [fset p.1; p.2] |
    p in (fsetT V `*` fsetT V) `\` fset_diag (fsetT V)].
Definition boundary (e : E) : {fset V} := val e.
Definition axiom : forall e : E, #|` boundary e| = 2.
Proof.
move=> e; rewrite /boundary.
case: e => e /= /imfsetP [] [a b] /= /imfsetP [] [a' b'] /=.
rewrite !inE /= in_fset_diag !inE /= => p [] -> -> ->.
by rewrite cardfs2 p.
Qed.
Definition t := LooplessUndirectedGraph.mk axiom.
End def.
End CompleteGraph.

Notation "`K T" := (CompleteGraph.t T) (at level 0, format "`K T").
Notation "`K_ n" := (CompleteGraph.t [finType of 'I_n])
                     (at level 1, format "`K_ n").

Section is_complete_graph.
Implicit Type G : llugraph.

(*
Definition is_KT G := isomorphic G (`K `V(G)).
*)

Definition is_complete_graph G :=
  injective (fun e : `E(G) => `d(e)) /\
    forall v w : `V(G), v != w -> exists e : `E(G), `d(e) = [fset v; w].

Lemma KT_is_complete (T : finType) : is_complete_graph `K T.
Proof.
split; first by move=> *; apply: val_inj.
move=> v w vw.
have eP : [fset v; w] \in CompleteGraph.E T.
  apply/imfsetP.
  exists (v, w) => //=.
  by rewrite !inE in_fset_diag in_fsetT /= vw.
by exists [` eP] => /=.
Qed.

Lemma card_VKn n : #| `V(`K_n) | = n.
Proof. exact: card_ord. Qed.

Lemma card_Ecomplete_aux G :
  is_complete_graph G ->
  fcover [fset biboundary e | e in `E(G)]  =
    (fsetT `V(G) `*` fsetT `V(G)) `\` fset_diag (fsetT `V(G)).
Proof.
move=> icg.
apply/fsetP=> -[a b].
apply/idP/idP.
  move/bigfcupP => /= [] S /andP [Sbb _] abS.
  apply: in_imfset => //.
  rewrite /= !inE /=.
  move: Sbb => /imfsetP [] e /= eE.
  move: abS => /[swap] ->.
  move/in_biboundary_neq => ab.
  by rewrite in_fset_diag (negPf ab) andbF.
rewrite !inE 2!andbT in_fset_diag negb_and in_fsetT /= => ab.
apply/bigfcupP.
exists [fset (a, b); (b, a)]; last by rewrite !inE eqxx.
rewrite andbT.
case: icg => _ /(_ _ _ ab).
case => e.
move/biboundaryE <-.
apply/imfsetP => /=.
by exists e.
Qed.

Lemma card_Ecomplete G :
  is_complete_graph G -> (2 * #| `E(G) | = #| `V(G) | * (#| `V(G) | - 1)).
Proof.
move=> icg.
move: (icg) => /card_Ecomplete_aux /(congr1 (size \o val)) /=.
rewrite cardfs_diagC.
set X := #|` fsetT `V(G) |.
set Y := #| `V(G) |.
set P := (P in fcover P).
have /eqP <- : trivIfset P.
  apply/trivIfsetP=> p q /imfsetP [] e /= _ -> /imfsetP [] f /= _ -> bef.
  apply/fdisjointP=> -[a b] abe.
  apply/negP => abf.
  move/negP: bef; apply; apply/eqP.
  apply: ex_biboundary_eq.
  by exists (a,b); rewrite abe abf.
have-> : \sum_(B <- P) #|` B| = \sum_(B <- P) 2.
  rewrite !big_seq.
  apply: eq_bigr => b /imfsetP [] e _ ->.
  by rewrite cardfs_biboundary.
rewrite big_const_seq iter_addn count_predT addn0.
rewrite card_imfset /=; last first.
  apply/boundary_biboundary_inj.
  by case: icg.
rewrite cardE => ->.
suff-> : X = Y by [].
by rewrite /X card_imfset //= /Y cardE.
Qed.

Lemma card_EG_leq_Ecomplete G :
  injective (fun e : `E(G) => `d(e)) ->
  (2 * #| `E(G) | <= #| `V(G) | * (#| `V(G) | - 1)).
Proof.
move=> ib.
apply: (@leq_trans (2 * #| `E(`K(`V(G))) |)); last first.
  rewrite (_ : #| `V(G) | = #| `V(`K(`V(G))) |) //.
  rewrite card_Ecomplete //.
  exact: KT_is_complete.
rewrite leq_mul2l //=.
have-> : #| `E(G) | = #|` [fset `d e | e in fsetT `E(G)] |.
  by rewrite card_imfset //= cardfsT.
rewrite -cardfE.
apply/fsubset_leq_card/fsubsetP=> x.
move/imfsetP=> [] e /= _ ->.
apply/imfsetP => /=.
have:= boundary_card2 e => /cardfs2_sig [] [] a b /= [] ab ->.
exists (a, b) => //.
by rewrite !inE in_fset_diag in_fsetT (negPf ab).
Qed.

Lemma nindmatch_complete G :
  is_complete_graph G ->
  nindmatch G <= 1 ?= iff (2 <= #| `V(G) |).
Proof.
case=> /= injb cmp.
have-> : (2 <= #| `V(G) |) = (1 <= #| `E(G) |).
  apply/idP/idP.
    move/card_gt1P => [] x [] y [] xVG yVG xy.
    apply/card_gt0P.
    have:= cmp x y xy => -[] e dexy.
    by exists e.
  move/card_gt0P => [] e eEG.
  apply/card_gt1P.
  have:= boundary_card2 e => /cardfs2_sig [] [] x y /= [] xy dexy.
  by exists x, y; split.
apply/leqifP; case: ifPn; last first.
  by rewrite -leqNgt leqn0 => /eqP /nindmatch0 ->.
move=> EGgt0.
move/card_gt0P: (EGgt0) => [] e eEG.
have eim: [fset e] \in induced_matching G.
  by apply/induced_matchingP=> e0 e1 /[!inE] /eqP -> /eqP -> /[!eqxx].
suff: forall M, M \in induced_matching G -> #|` M | <= 1.
  move/bigmax_leqP=> H.
  apply/eqP/anti_leq.
  rewrite {}H /=.
  rewrite/nindmatch.
  have := (@leq_bigmax_cond (fset_finType `E(G)) _ (fun x => #|` x |) [fset e] eim).
  by rewrite cardfs1.
move=> M /induced_matchingP H.
apply/negbNE/negP; rewrite -ltnNge cardfE.
move/card_gt1P => [] x [] y [] xM yM xy.
have := H (val x) (val y).
have /[swap]/[apply] : val x \in M by exact:fsvalP.
have /[swap]/[apply] : val y \in M by exact:fsvalP.
move/(_ xy).
have := boundary_card2 (val x) => /cardfs2_sig [] [] a b /= [] ab dxab.
have := boundary_card2 (val y) => /cardfs2_sig [] [] c d /= [] cd dycd.
case/boolP: (a == c).
  move=> /eqP ac /(_ (fsval x)).
  rewrite dxab dycd ac.
  case.
    have: c \in [fset c; b] by rewrite !inE eqxx.
    by move/fdisjointXX.
  by move/fdisjointP=> /(_ c); rewrite !inE eqxx => /(_ erefl).
move/cmp=> [] f dfac /(_ f) /[!dfac].
by case=> /fdisjointP; [move/(_ a); rewrite dxab | move/(_ c); rewrite dycd ];
   rewrite !inE eqxx /= ?orbT => /(_ erefl).
Qed.

Lemma maximal_matching_complete G (S : {fset `E(G)}) :
  is_complete_graph G -> S \in maximal_matching G ->  #|` S | = #| `V(G) | ./2.
Proof.
case=> injb cmp SmG.
apply/eqP; move: SmG; apply: contraLR.
rewrite neq_ltn => /orP [] H; apply/maximal_matchingP => -[]; last first.
  move => SmG _.
  have := double_nmatch_leq_cardVG G.
  rewrite -geq_half_double.
  have := leq_nmatch SmG.
  move/leq_trans/[apply].
  by rewrite leqNgt H.
move=> SmG Smax; move: H.
rewrite geq_half_double -addn1 doubleD {2}doubleE /=.
rewrite -matching_double_card //.
rewrite -leq_psubRL //.
rewrite -cardfsT -cardfsDS; last by apply/fsubsetP => ?; rewrite inE.
case/cardfs_gt1_sig => -[] a b /= [] ab [].
rewrite !inE 2!andbT => aS bS.
have := cmp a b ab => -[] e deab.
have eS : e \notin S.
  apply/negP=> H.
  move/negP: aS; apply.
  apply/bigfcupP; exists `d(e); last by rewrite deab !inE eqxx.
  by rewrite in_imfset.
have := Smax (e |` S).
move/(_ _)/negP; apply; first exact: fproperU1.
apply/matchingP => x y; rewrite !inE.
case/orP => [/eqP -> | xS]; case/orP => [/eqP -> | yS]; rewrite ?eqxx //= => xy.
- apply/fdisjointP=> u.
  by rewrite deab !inE=> /orP [] /eqP ->; apply/negP => ad;
     [move/bigfcupP: aS | move/bigfcupP: bS];
     apply; exists `d(y) => //; rewrite in_imfset.
- rewrite fdisjoint_sym.
  apply/fdisjointP=> u.
  by rewrite deab !inE=> /orP [] /eqP ->; apply/negP => ad;
     [move/bigfcupP: aS | move/bigfcupP: bS];
     apply; exists `d(x) => //; rewrite in_imfset.
- by move/matchingP: SmG; apply.
Qed.

Lemma nmatch_complete G : is_complete_graph G -> nmatch G = #| `V(G) | ./2.
Proof.
move/maximal_matching_complete=> H.
rewrite -nmaxmatchE.
by have:= exists_nmaxmatch G => -[] M /H -> ->.
Qed.

Lemma nminmatch_complete G : is_complete_graph G -> nminmatch G = nmatch G.
Proof.
move=> icg.
move/maximal_matching_complete: (icg) => H.
rewrite nmatch_complete //.
by have:= exists_nminmatch G => -[] M /H -> ->.
Qed.

End is_complete_graph.
