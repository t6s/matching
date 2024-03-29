From mathcomp Require Import all_ssreflect. (* from mathcomp *)
From mathcomp Require Import finmap multiset. (* from finmap *)
From mathcomp Require Import mathcomp_extra classical_sets. (* from analysis *)
From infotheo Require Import subgraph_partition.
(*From HB Require Import structures.
From monae Require Import hierarchy.*)
Require Import mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "`V G" (at level 0, format "`V G").
Reserved Notation "`E G" (at level 0, format "`E G").
Reserved Notation "`d x" (at level 0, format "`d x").

(*
HB.mixin Record isEnumerableMonad (M : UU0 -> UU0) of Monad M := {
    enum : forall A : UU0, M A -> seq A;
!!!!!
Module MonadicGraph.
Section def.
Variable M : monad.
Record t := mk {
  V : finType;
  E : finType;
  boundary : E -> M V;
  _ : forall e : E, size (boundary e) = 2;
}.
End def.
Module Exports.
Notation ugraph := t.
(*Notation "`d x" := (boundary x).*)
End Exports.
End MonadicGraph.
*)

(* undirected graph *)
Module UndirectedGraph.
Section def.
Local Open Scope mset_scope.
Record t := mk {
  V : finType;
  E : finType;
  boundary : E -> {mset V};
  _ : forall e : E, size (boundary e) = 2;
}.
End def.
Module Exports.
Notation ugraph := t.
(*Notation "`d x" := (boundary x).*)
End Exports.
End UndirectedGraph.

(* undirected, loopless graph *)
Module LooplessUndirectedGraph.
Section def.
Record t := mk {
  V : finType;
  E : finType;
  boundary : E -> {fset V};
  _ : forall e : E, #|` boundary e | = 2;
}.
End def.
Module Exports.
Notation llugraph := t.
(*Coercion boundary : t >-> finset_of.*)
Notation "`d x" := (boundary x).
Notation "`E x" := (E x).
Notation "`V x" := (V x).
End Exports.
End LooplessUndirectedGraph.
Export LooplessUndirectedGraph.Exports.

Local Open Scope fset_scope.


Section llugraph_lemmas.

Lemma boundary_card2 G : forall e : `E(G) , #|` `d e| = 2.
Proof. by case: G. Qed.

Lemma boundary_exists G (e : `E(G)) : exists v : `V(G), v \in `d(e).
Proof.
have: 0 < #|` `d(e) | by rewrite boundary_card2.
rewrite cardfs_gt0.
by move/fset0Pn.
Qed.

Lemma boundary_exists2 G (e : `E(G)) :
  exists u v, u \in `d(e) /\ v \in `d(e) /\ u != v.
Proof.
move/eqP/cardfs2P: (boundary_card2 e) => [x [y [xy dexy]]].
by exists x, y; rewrite xy dexy; split; [| split => //];
   rewrite inE !in_fset1 eqxx ?orbT ?orTb.
Qed.

Lemma boundary_sig2 G (e : `E(G)) :
  {uv | uv.1 != uv.2 /\ `d(e) = [fset uv.1; uv.2]}.
Proof. exact/cardfs2_sig/boundary_card2. Qed.

Lemma boundary_disj_neq G (e f : `E(G)) : [disjoint `d(e) & `d(f)] -> e != f.
Proof.
apply:contraTN => /eqP ->.
by rewrite /fdisjoint fsetIid -cardfs_eq0 boundary_card2.
Qed.

End llugraph_lemmas.


Section matching.
Variable G : llugraph.

Section pred.
Variable S : {fset `E(G)}.

(*
Definition classical_matching : set (set G%:E) :=
  [set S | forall e f, e \in S -> f \in S -> ((`d e) `&` (`d f)) = fset0].
*)

Definition is_matching :=
  [forall e in S,
      [forall f in S,
          (e != f)
            ==> [disjoint `d(e) & `d(f)]%fset]].

Lemma is_matchingP :
  reflect
    {in S & S, forall e f, e != f -> [disjoint (`d e) & (`d f)]}
    is_matching.
Proof.
apply: (iffP idP) => H.
- move=> e f eS fS ef.
  by move:H => /forall_inP /(_ e eS) /forall_inP /(_ f fS) /implyP /(_ ef).
- apply/forall_inP => e eS.
  apply/forall_inP => f fS.
  apply/implyP => ef.
  exact:H.
Qed.

Definition inj_boundary :=
  {in S & S, injective (@LooplessUndirectedGraph.boundary G)}.

Definition trivIbound := trivIfset [fset `d(x) | x in S].

Lemma matching_inj_boundary : is_matching -> inj_boundary.
Proof.
move=> MmG e1 e2 e1M e2M.
move/is_matchingP: MmG => /(_ e1 e2 e1M e2M).
move => /contraR /(_ _)/eqP /[swap] d12.
apply.
by rewrite /fdisjoint d12 fsetIid -cardfs_eq0 boundary_card2.
Qed.

Lemma matching_trivIbound : is_matching -> trivIbound.
Proof.
move/is_matchingP => H.
apply/trivIfsetP => a b.
move=> /imfsetP [] x /= xS -> /imfsetP [] y /= yS -> dxy.
apply: H => //.
move:dxy.
apply:contraNN => /eqP ->.
exact: eqxx.
Qed.

(* TODO: rename? *)
Lemma is_matching_triv_inj :
  inj_boundary /\ trivIbound <-> is_matching.
Proof.
split; last first.
  move=> ?.
  by split; [apply: matching_inj_boundary | apply: matching_trivIbound].
case.
move=> bi.
move/trivIfsetP=> ibt.
apply/is_matchingP=> e f eS fS ef.
apply:ibt; [exact:in_imfset | exact:in_imfset |].
move:ef.
apply/contraNN.
move/eqP => dedf.
exact/eqP/bi.
Qed.
End pred.

Definition matching : {fset {fset `E(G)}} :=
  [fset S : {fset `E(G)} | is_matching S].

Definition nmatch := \max_(S in matching) #|` S |.

Lemma leq_nmatch (S : {fset `E(G)}) : S \in matching -> #|` S | <= nmatch.
Proof. by move=> mG; apply:leq_bigmax_cond. Qed.

End matching.


Module matching_trivIbound_counter_example.
Definition V := [finType of 'I_2].
Definition E := [finType of 'I_2].
Definition d (_ : E) : {fset V} := fsetT V.
Lemma axiom (e : E) : #|` d e | = 2.
Proof. by rewrite cardfsT card_ord. Qed.
Definition G := LooplessUndirectedGraph.mk axiom.

Example trivIbound_is_not_necessarily_matching :
  exists S : {fset `E(G)}, trivIbound S /\ ~ @is_matching G S.
Proof.
exists (fsetT `E(G)); split.
  apply/trivIfsetP => A B /imfsetP [] e /= ? -> /imfsetP [] f /= ? ->.
  by rewrite /d eqxx.
move/is_matchingP.
move/(_ (inord 0)) /(_ (inord 1)).
rewrite !inE /= => /(_ erefl erefl).
suff : inord 0 != inord 1 :> 'I_2
  by move /[swap] /[apply] /fdisjointP /(_ (inord 0)) /[!inE] /(_ erefl).
apply/eqP.
move=> /(congr1 val) /=.
by rewrite !inordK.
Qed.
End matching_trivIbound_counter_example.

Module matching_inj_boundary_counter_example.
Definition V := [finType of 'I_3].
Definition E := [finType of 'I_2].
Notation v0 := (ord0 : V).
Notation v1 := ((Ordinal (erefl (1 < 3))) : V).
Notation v2 := ((Ordinal (erefl (2 < 3))) : V).
Notation e0 := (ord0 : E).
Notation e1 := ((Ordinal (erefl (1 < 2))) : E).
Definition d (e : E) : {fset V} :=
  if e == e0 then [fset v0; v1] else [fset v1; v2].
Lemma axiom (e : E) : #|` d e | = 2.
Proof. by rewrite /d; case: ifP => _; rewrite cardfs2. Qed.
Definition G := LooplessUndirectedGraph.mk axiom.

Example inj_boundary_is_not_necessarily_matching :
  exists S : {fset `E(G)}, inj_boundary S /\ ~ @is_matching G S.
Proof.
exists (fsetT `E(G)); split.
  move => e f _ _ /=.
  rewrite /d.
  by case: ifPn; case: ifPn => /=; rewrite ?ord2_neq0;
     move=> /eqP -> /eqP -> // /eqP /fset_eqP /(_ ord0) /[!inE].
move /is_matchingP /(_ e0 e1) /[!inE] /(_ erefl erefl erefl).
by move /fdisjointP /(_ v1) /[!inE] /(_ erefl).
Qed.
End matching_inj_boundary_counter_example.

Section matching_lemmas.

Lemma matchingP G (S : {fset `E(G)})  :
  reflect
    {in S & S, forall e f, e != f -> [disjoint (`d e) & (`d f)]}
    (S \in matching G).
Proof.
rewrite !inE andTb.
exact: is_matchingP.
Qed.

Lemma fset0_matching G : fset0 \in matching G.
Proof. by apply/matchingP => ?; rewrite inE. Qed.

Lemma fset1_matching G (e : `E(G)) : [fset e] \in matching G.
Proof.
by apply/matchingP => ? ?; rewrite !in_fset1 => /eqP -> /eqP ->; rewrite eqxx.
Qed.

Lemma matching_neq0 G : matching G != fset0.
Proof. apply/fset0Pn; exists fset0; exact: fset0_matching. Qed.

Lemma card1_matching G : (#|` matching G | == 1) = (matching G == [fset fset0]).
Proof.
apply/idP/idP; last by move/eqP ->; rewrite cardfs1.
case/cardfs1P => ? H.
move: (fset0_matching G).
rewrite H.
by move/fset1P <-.
Qed.

Lemma matching_subT G : matching G `<=` fpowerset (fsetT _).
Proof.
apply/fsubsetP => ? ?.
rewrite fpowersetE.
by apply/fsubsetP => ? ?; rewrite inE.
Qed.

Lemma matching1Pn G :
  reflect (exists e, e \in `E(G)) (matching G != [fset fset0]).
Proof.
apply:(iffP idP).
  move=> H; apply/existsP; move: H; apply:contraNT; move/existsPn => G0.
  apply/fset_eqP=> S; rewrite in_fset1.
  apply/idP/idP; last by move/eqP ->; exact: fset0_matching.
  apply:contraTT => /fset0Pn [] e ei.
  by move: (G0 e).
case => e eG.
apply/eqP.
have := fset1_matching e.
move=> /[swap] ->.
rewrite in_fset1.
apply/negP/fset0Pn; exists e.
by rewrite in_fset1.
Qed.

Lemma matching1_negb_exists G :
  matching G == [fset fset0] = ~~ [exists e, e \in `E(G)].
Proof.
apply/idP/idP.
  move=> ?.
  by apply/existsP/matching1Pn.
by move/existsP/matching1Pn.
Qed.

Lemma exists_nmatch (G : llugraph) :
  { M : {fset `E(G)} | M \in matching G & nmatch G = #|` M| }.
Proof.
apply: eq_bigmax_cond.
apply/card_gt0P.
exists fset0.
exact: fset0_matching.
Qed.

Lemma nmatch0 (G : llugraph) : #| `E(G) | = 0 -> nmatch G = 0.
Proof.
move=> E0.
case: (exists_nmatch G) => M _ ->.
apply/eqP; rewrite -leqn0.
move: (fsubsetT M) => /fsubset_leq_card /leq_trans; apply.
rewrite leqn0 cardfsT.
by apply/eqP.
Qed.

Lemma matchingU1 (G : llugraph) (M : {fset `E(G)}) (e : `E(G)) :
  M \in matching G ->
  (forall f, f \in M -> [disjoint `d(e) & `d(f)]) ->
  (e |` M) \in matching G.
Proof.
move=> MmG edisjM.
apply/matchingP.
move=> e0 e1; rewrite !inE.
case/orP => He0; case/orP => He1.
  - by rewrite (eqP He0) (eqP He1) eqxx.
  - by rewrite (eqP He0) => _; exact: edisjM.
  - by rewrite fdisjoint_sym (eqP He1) => _; exact: edisjM.
  - by move/matchingP: MmG; apply.
Qed.  

End matching_lemmas.


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
End get1_boundary.


Section induced_matching.
Variable G : llugraph.

Section pred.
Variable S : {fset `E(G)}.

Definition is_induced_matching :=
  [forall e in S,
  [forall f in S,
      (e != f)
        ==>
        [forall g,
            [disjoint `d(e) & `d(g)]%fset || [disjoint `d(f) & `d(g)]%fset]]].

Lemma is_induced_matchingP :
  reflect
    {in S & S, forall e f,
          e != f ->
          forall g, [disjoint `d(e) & `d(g)] \/ [disjoint `d(f) & `d(g)]}
    is_induced_matching.
Proof.
apply: (iffP idP) => H.
- move=> e f eS fS ef g.
  apply/orP.
  by move: H => /forall_inP /(_ e eS) /forall_inP /(_ f fS) /implyP
                 /(_ ef) /forallP.
- apply/forall_inP => e eS.
  apply/forall_inP => f fS.
  apply/implyP => ef.
  apply/forallP => g.
  apply/orP.
  exact:H.
Qed.

End pred.

Definition induced_matching : {fset {fset `E(G)}} :=
  [fset S : {fset `E(G)} | is_induced_matching S].

Definition nindmatch := \max_(S in induced_matching) #|` S |.

Lemma leq_nindmatch (S : {fset `E(G)}) :
  S \in induced_matching -> #|` S | <= nindmatch.
Proof. by move=> mG; apply:leq_bigmax_cond. Qed.

End induced_matching.

Section induced_matching_lemmas.

Lemma induced_matchingP G (S : {fset `E(G)})  :
  reflect
    {in S & S, forall e f,
          e != f ->
          forall g, [disjoint `d(e) & `d(g)] \/ [disjoint `d(f) & `d(g)]}
    (S \in induced_matching G).
Proof.
rewrite !inE andTb.
exact: is_induced_matchingP.
Qed.

Lemma induced_sub_matching G : induced_matching G `<=` matching G.
Proof.
apply/fsubsetP => S /induced_matchingP imS.
apply/matchingP => e f eS fS ef.
move: (imS e f eS fS ef) => /(_ f) [] //.
case: (boundary_exists f) => x xf.
by move: (fdisjointXX xf).
Qed.

Lemma fset0_induced_matching G : fset0 \in induced_matching G.
Proof. by apply/induced_matchingP => ?; rewrite inE. Qed.

Lemma fset1_induced_matching G (e : `E(G)) : [fset e] \in induced_matching G.
Proof.
by apply/induced_matchingP => ? ?;
   rewrite !in_fset1 => /eqP -> /eqP ->; rewrite eqxx.
Qed.

Lemma induced_matching_neq0 G : induced_matching G != fset0.
Proof. apply/fset0Pn; exists fset0; exact: fset0_induced_matching. Qed.

Lemma card1_induced_matching G :
  (#|` induced_matching G | == 1) = (induced_matching G == [fset fset0]).
Proof.
apply/idP/idP; last by move/eqP ->; rewrite cardfs1.
case/cardfs1P => ? H.
move: (fset0_induced_matching G).
rewrite H.
by move/fset1P <-.
Qed.

Lemma induced_matching1Pn G :
  reflect (exists e, e \in `E(G)) (induced_matching G != [fset fset0]).
Proof.
apply:(iffP idP).
  move=> H; apply/existsP; move: H; apply:contraNT; move/existsPn => G0.
  apply/fset_eqP=> S; rewrite in_fset1.
  apply/idP/idP; last by move/eqP ->; exact: fset0_induced_matching.
  apply:contraTT => /fset0Pn [] e ei.
  by move: (G0 e).
case => e eG.
apply/eqP.
have := fset1_induced_matching e.
move=> /[swap] ->.
rewrite in_fset1.
apply/negP/fset0Pn; exists e.
by rewrite in_fset1.
Qed.

Lemma induced_matching1_negb_exists G :
  induced_matching G == [fset fset0] = ~~ [exists e, e \in `E(G)].
Proof.
apply/idP/idP.
  move=> ?.
  by apply/existsP/induced_matching1Pn.
by move/existsP/induced_matching1Pn.
Qed.

Lemma exists_nindmatch (G : llugraph) :
  { M : {fset `E(G)} | M \in induced_matching G & nindmatch G = #|` M| }.
Proof.
apply: eq_bigmax_cond.
apply/card_gt0P.
exists fset0.
exact: fset0_induced_matching.
Qed.

Lemma nindmatch0 (G : llugraph) : #| `E(G) | = 0 -> nindmatch G = 0.
Proof.
move=> E0.
case: (exists_nindmatch G) => M.
move/(fsubsetP (induced_sub_matching G)).
move: E0.
move/eq_leq; rewrite leqNgt => /card_gt0P.
move /matching1Pn /eqP ->.
by rewrite inE => /eqP -> ->.
Qed.

End induced_matching_lemmas.

Section minimal_matching.
Variable G : llugraph.

Section pred.
Variable S : {fset `E(G)}.

Definition is_maximal_matching :=
  (S \in matching G) &&
  [forall T : {fset `E(G)}, (S `<` T) ==> (T \notin matching G)].

Lemma is_maximal_matchingP :
  reflect
    (S \in matching G /\
     forall T : {fset `E(G)}, (S `<` T) -> (T \notin matching G))
    is_maximal_matching.
Proof.
apply: (iffP idP).
- case/andP => ? /forallP H.
  split => // T ST.
  by move: (H T) => /implyP /(_ ST).
- case => ? H.
  apply/andP; split => //.
  apply/forallP => T.
  apply/implyP.
  exact: (H T).
Qed.

End pred.

Definition maximal_matching : {fset {fset `E(G)}} :=
  [fset S : {fset `E(G)} | is_maximal_matching S].

Definition nmaxmatch := \max_(S in maximal_matching) #|` S |.

Definition nminmatch :=
  (* if #| `E(G) | == 0 then 0 else *)
  \big[Order.min/nmaxmatch]_(S in maximal_matching) #|` S |.

Lemma nminmatch_foldrE :
  nminmatch = foldr (fun S n => Order.min #|` S | n) nmaxmatch maximal_matching.
Proof.
Import Order.TotalTheory.
rewrite -(foldr_map (fun S => #|` S|)) foldrE big_map.
rewrite /nminmatch -[in LHS]big_filter.
apply: perm_big_AC; [exact:minA | exact:minC |].
apply uniq_perm; [exact/filter_uniq/index_enum_uniq | exact: fset_uniq |].
move=> S.
by rewrite mem_filter mem_index_enum andbT.
Qed.

Lemma geq_nminmatch (S : {fset `E(G)}) :
  S \in maximal_matching -> nminmatch <= #|` S |.
Proof. by move=> mG; rewrite /nminmatch -leEnat; apply: bigmin_le_cond. Qed.

End minimal_matching.

Section maximal_matching_lemmas.

Lemma maximal_matchingP G (S : {fset `E(G)})  :
  reflect
    (S \in matching G /\
     forall T : {fset `E(G)}, (S `<` T) -> (T \notin matching G))
    (S \in maximal_matching G).
Proof.
set P := (P in reflect P _).
rewrite !inE andTb.
exact: is_maximal_matchingP.
Qed.

Lemma ubound_maximal_matching G (S : {fset `E(G)}) : 
  S \in matching G ->
  exists T : {fset `E(G)},  S `<=` T  /\  T \in maximal_matching G.
Proof.
move=> SmG.
set T : Type := matching G.
pose R : T -> T -> Prop := (fun x y => @fsubset `E(G) (val x) (val y)).
have R_refl : forall t, R t t by move=> ?; exact: fsubset_refl.
have R_trans : forall r s t, R r s -> R s t -> R r t
    by move=> ? ? ?; exact: fsubset_trans.
have R_antisym : forall s t, R s t -> R t s -> s = t
    by move=> *; apply/val_inj/eqP; rewrite eqEfsubset; apply/andP; split.
have R_tot_max : forall A , total_on A R -> exists t, forall s, A s -> R s t.
  move=> A totAR.
  pose lub := \bigcup_(X in A) val X.
  have lubP: lub \in matching G.
    apply/matchingP => e0 e1.
    case/bigfcupP => /= M0 /[!mem_index_enum] /[!andTb] M0A eM0.
    case/bigfcupP => /= M1 /[!mem_index_enum] /[!andTb] M1A eM1.
    wlog: e0 e1 M0 M1 eM0 eM1 M0A M1A / R M0 M1.
      by case: (totAR M0 M1 (set_mem M0A) (set_mem M1A));
         move=> /[swap] /[apply]; last rewrite eq_sym fdisjoint_sym; apply.
    move=> RM01.
    have e0M1 : e0 \in fsval M1.
      by move: RM01; rewrite /R => /fsubsetP /(_ e0 eM0).
    have: fsval M1 \in matching G by [].
    by move/matchingP; apply.
  exists [` lubP] => *.
  by apply: bigfcup_sup; [rewrite mem_index_enum | rewrite inE].
have [max [RSmax Hmax]] := Zorn_over R_refl R_trans R_antisym R_tot_max [` SmG].
exists (val max); split => //.
apply/maximal_matchingP; split; first by rewrite -in_fsub fsubT.
move=> U maxU; apply/negP => UmG.
move: (Hmax [` UmG] (fproper_sub maxU)) (maxU) => <- /=.
exact /negP /fproper_irrefl.
Qed.

Lemma leq_nmaxmatch G (S : {fset `E(G)}) :
  S \in matching G -> #|` S | <= nmaxmatch G.
Proof.
move=> SmG.
have [T [/fsubset_leq_card ST TmG]] := ubound_maximal_matching SmG.
apply: (leq_trans ST).
by apply: leq_bigmax_cond.
Qed.

Lemma maximal_matching_neq0 G : maximal_matching G != fset0.
Proof.
apply/fset0Pn.
case: (ubound_maximal_matching (fset0_matching G)) => S [] _ ?.
by exists S.
Qed.

Lemma maximal_sub_matching G : maximal_matching G `<=` matching G.
Proof. by apply/fsubsetP => S /maximal_matchingP []. Qed.

Lemma in_maximal_matchingW G (S : {fset `E(G)}) :
  S \in maximal_matching G -> S \in matching G.
Proof. by have /fsubsetP/(_ S) := maximal_sub_matching G. Qed.

Lemma maximal_matching1Pn G :
  reflect (exists e, e \in `E(G)) (maximal_matching G != [fset fset0]).
Proof.
rewrite [X in reflect _ X](_ : _ = (matching G != [fset fset0]));
  first exact: matching1Pn.
case: matching1Pn.
  case=> e eE.
  case: (ubound_maximal_matching (fset1_matching e)) => S [eS SmG].
  apply/eqP.
  move: SmG => /[swap] -> /fset1P.
  move: eS => /[swap] -> /fsubsetP /(_ e).
  by rewrite in_fset0 in_fset1 eqxx => /(_ erefl).
move/matching1Pn/eqP => H.
have:= maximal_sub_matching G; rewrite H fsubset1.
rewrite (negPf (maximal_matching_neq0 G)) orbF => /eqP ->.
by rewrite eqxx.
Qed.

Lemma maximal_matching1_negb_exists G :
  maximal_matching G == [fset fset0] = ~~ [exists e, e \in `E(G)].
Proof.
apply/idP/idP.
  move=> ?.
  by apply/existsP/maximal_matching1Pn.
by move/existsP/maximal_matching1Pn.
Qed.

Lemma exists_nmaxmatch (G : llugraph) :
  { M : {fset `E(G)} | M \in maximal_matching G & nmaxmatch G = #|` M| }.
Proof.
case/fset0Pn/sigW: (maximal_matching_neq0 G) => S SmG.
apply: eq_bigmax_cond.
apply/card_gt0P.
by exists S.
Qed.

Lemma exists_nminmatch (G : llugraph) :
  { M : {fset `E(G)} | M \in maximal_matching G & nminmatch G = #|` M| }.
Proof.
case/fset0Pn/sigW: (maximal_matching_neq0 G) => S SmG.
apply: (eq_bigmin S) => //.
move=> T; rewrite topredE => TmG.
rewrite /nmaxmatch leEnat.
by apply:leq_bigmax_cond.
Qed.

Lemma nmaxmatch0 (G : llugraph) : #| `E(G) | = 0 -> nmaxmatch G = 0.
Proof.
move=> E0.
case: (exists_nmaxmatch G) => M.
move/(fsubsetP (maximal_sub_matching G)).
move: E0.
move/eq_leq; rewrite leqNgt => /card_gt0P.
move /matching1Pn /eqP ->.
by rewrite inE => /eqP -> ->.
Qed.

Lemma nminmatch0 (G : llugraph) : #| `E(G) | = 0 -> nminmatch G = 0.
Proof.
move=> E0.
case: (exists_nminmatch G) => M.
move/(fsubsetP (maximal_sub_matching G)).
move: E0.
move/eq_leq; rewrite leqNgt => /card_gt0P.
move /matching1Pn /eqP ->.
by rewrite inE => /eqP -> ->.
Qed.

Lemma maxmatch_edgeI (G : llugraph) (M : {fset `E(G)}) (e : `E(G)) :
  M \in maximal_matching G ->
  exists f, f \in M /\ ~ [disjoint `d(e) & `d(f)]%fset.
Proof.
case/boolP: (e \in M).
  move=> *; exists e; split => //.
  case: (boundary_exists e) => x xe.
  exact: (fdisjointXX xe).
move=> eM.
case/maximal_matchingP => MmG.
move/(_ (e |` M)) /(_ (fproperU1 eM)).
apply:boolp.contraPP=> /boolp.forallNP.
under (@boolp.eq_forall `E(G)) do rewrite not_andE contrapE -implyE.
by move/(matchingU1 MmG) ->.
Qed.

End maximal_matching_lemmas.

(*
(* not sure if this section is useful *)
Section span.
Variables (G : llugraph) (S : {fset `E(G)}).

Definition span_V := fcover [fset `d(e) | e in S].

Definition span_E := (fset_sub_finType S) : finType.

Definition span_boundary (e : span_E) := `d(fsval e).

Lemma span_boundary_card2 (e : span_E) :  #|` span_boundary e| = 2.
Proof. exact: boundary_card2. Qed.

Definition span : llugraph := LooplessUndirectedGraph.mk span_boundary_card2.

End span.
(*Notation "??? S" := @span _ S*)
*)


Section VofESet.

(* TODO: rename *)
Definition VofESet G (S : {fset `E(G)}) := fcover [fset `d(e) | e in S].

Lemma VofESetE G (S : {fset `E(G)}) : VofESet S = \bigcup_(e <- S) `d(e).
Proof. by rewrite -(bigfcup_image _ (fun e => `d(e)) id). Qed.

Section lemmas.
Variables (G : llugraph) (M : {fset `E(G)}) (MmG : M \in matching G).

Lemma matching_double_card : #|` VofESet M | = #|` M |.*2.
Proof.
move: MmG.
rewrite !inE /= => mM.
move/matching_trivIbound : (mM).
rewrite /trivIbound /trivIfset /= => H.
rewrite -(eqP H). (* rewritable since the LHS is an fcover *)
rewrite big_imfset /= ; last exact: matching_inj_boundary.
under eq_bigr do rewrite boundary_card2.
by rewrite big_const_seq.
Qed.

End lemmas.

Lemma double_nmatch_leq_cardVG G : (nmatch G).*2 <= #| `V(G) |.
Proof.
have [M H1 H2] := exists_nmatch G.
apply (@leq_trans #|` VofESet M|); last first.
  by rewrite -cardfsT; exact/fsubset_leq_card/fsubsetT.
by rewrite matching_double_card // leq_double H2.
Qed.

End VofESet.


(* TODO: remove duplications with graph.VofESet *)
Section edgeI.
(* NB: eqv. to ~~ [disjoint fcover [fset `d(f) | f in S] & `d(e)] *)
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

(* TODO: rename *)
Lemma maxmatch_edgeI_opp (G : llugraph) (M : {fset `E(G)}) :
  M \in matching G ->
  (forall e, exists f, f \in M /\ ~ [disjoint `d(e) & `d(f)]%fset) ->
  M \in maximal_matching G.
Proof.
move=> MmG H.
apply/maximal_matchingP; split=> // S MS.
apply/negP=> /matchingP H0.
have:= MS => /fproperDneq0 /fset0Pn [] e.
rewrite !inE => /andP [] enM eS.
have:= H e => -[] f [] fM nddef.
have ef: e != f by move: enM; apply: contra => /eqP ->.
apply/nddef/fdisjointP=> u ude.
apply/negP=> udf.
have fS : f \in S by have:= MS => /fproper_sub /fsubsetP /(_ f); apply.
by have:= H0 e f eS fS ef.
Qed.

End edgeI.


Section matching_number_lemmas.

Lemma nmaxmatchE G : nmaxmatch G = nmatch G.
Proof.
case/boolP: [exists e, e \in `E(G)]; last first.
  rewrite /nmaxmatch /nmatch.
  move => /[dup] /existsP /matching1Pn /eqP ->.
  by move => /[dup] /existsP /maximal_matching1Pn /eqP ->.
case/existsP => e eG.
apply/anti_leq/andP; split.
- apply/bigmax_leqP => S /maximal_matchingP [] ? ?.
  by apply: leq_bigmax_cond.
- apply/bigmax_leqP => S mG.
  case: (exists_nmaxmatch G) => T TG cT.
  apply: (@leq_trans #|` T|); last exact: leq_bigmax_cond.
  rewrite -cT.
  exact: leq_nmaxmatch.
Qed.

Lemma exists_nmatch_maximal (G : llugraph) :
  { M : {fset `E(G)} | M \in maximal_matching G & nmatch G = #|` M| }.
Proof.
suff: { M : {fset `E(G)} | M \in maximal_matching G & nmaxmatch G = #|` M| }.
  case => S SmmG nmmGE.
  exists S => //.
  by rewrite -nmmGE nmaxmatchE.
exact: exists_nmaxmatch.
Qed.

Lemma nminmatch_leq_nmatch G : nminmatch G <= nmatch G.
Proof.
case: (exists_nminmatch G) => S mmS cS.
apply: (leq_trans (geq_nminmatch mmS)).
apply: leq_nmatch.
exact: (in_maximal_matchingW mmS).
Qed.

Section nmatch_leq_double_nminmatch.
Variable G : llugraph.

(* TODO: avoid using AC or move onto classical_sets *)
Lemma maxmatch_edgeI' (M : {fset `E(G)}) (e : `E(G)):
  M \in maximal_matching G -> 
  exists f : `E(G), f \in M /\ exists v : `V(G), v \in `d(e) /\ v\in `d(f).
Proof.
case/(maxmatch_edgeI e) => f [] fM.
case/negP/fset0Pn => v /[!inE] /andP [] vde vdf.
exists f; split => //.
by exists v; split.
Qed.

Let phi_ (M : {fset `E(G)}) (Mmax : M \in maximal_matching G) :
  `E(G) -> `E(G) * `V(G).
move=> e.
move: (maxmatch_edgeI' e Mmax).
case/boolp.cid => f [] _.
case/boolp.cid => v _.
exact: (f, v).
Defined.

Let phi := Eval hnf in phi_.

Let phi_VofESet (M : {fset `E(G)}) (Mmax : M \in maximal_matching G) e :
  (phi Mmax e).2 \in VofESet M.
Proof.
rewrite VofESetE.
apply/bigfcupP.
rewrite /phi.
case: boolp.cid.
move=> f [] fM ?.
case: boolp.cid.
move=> v [] vde vdf.
exists f => //.
by rewrite andbT.
Qed.

Let phi_boundary (M : {fset `E(G)}) (Mmax : M \in maximal_matching G) e :
  (phi Mmax e).2 \in `d e.
Proof.
rewrite /phi.
case: boolp.cid.
move=> ? [] ? ?.
case: boolp.cid.
by move=> ? [].
Qed.

Let phi_boundary_self (M : {fset `E(G)}) (Mmax : M \in maximal_matching G) e :
  (phi Mmax e).2 \in `d ((phi Mmax e).1).
Proof.
rewrite /phi.
case: boolp.cid.
move=> ? [] ? ?.
case: boolp.cid.
by move=> ? [].
Qed.

Let phi_inj (M : {fset `E(G)}) (Mmax : M \in maximal_matching G)
    (N : {fset `E(G)}) e0 e1 :
  N \in matching G -> e0 \in N -> e1 \in N ->
  (phi Mmax e0).2 == (phi Mmax e1).2 -> e0 == e1.
Proof.
move/matchingP.
move=> NmG e0N e1N.
apply:contraLR => e01.
move: (NmG e0 e1 e0N e1N e01) => /fdisjointP disj01.
apply/eqP => p01.
move: (disj01 (phi Mmax e0).2).
rewrite {2}p01 !phi_boundary.
by move /(_ erefl) /negP /(_ erefl).
Qed.

Lemma nmatch_leq_double_nminmatch : nmatch G <= (nminmatch G).*2.
Proof.
case: (exists_nminmatch G) => M Mmax ->.
rewrite -matching_double_card; last by case/maximal_matchingP: Mmax.
case: (exists_nmatch G) => N Nm ->.
(* TODO: use classical/functions.v *)
(* TODO: use classical_sets instead of finmap *)
rewrite 2!cardfE.
set f : N -> VofESet M := fun n =>  [` (phi_VofESet Mmax (val n)) ].
apply: (leq_card f).
move => e0 e1.
move/eqP => H; apply/eqP; move: H.
move/(phi_inj Nm).
by rewrite 2!fsvalP => /(_ erefl erefl).
Qed.
(* Alternate Proof:
Let M be a matching with #|M| = nmatch G. 
Let S be a maximal matching with #|S| = nminmatch G. 
Since S is maximal matching, for all e \in E(G), the intersection of the boundary of e and V(S) is NOT empty. 
Hence, for each f_i = {v_i, w_i} \in M, v_i \in V(S) or w_i \in V(S).
We may assume that v_i \in V(S) for all 1 <= i <= #|M|. 
Since M is matching, v_i \neq v_j for all 1 <= i < j <= #|M|. 
Hence #|V(S)|>= #|M| = nmatch G. 
Since #|V(S)| = 2#|V(S)| = 2nminmatch G, we have nmatch G <= 2nminmatch G. 
QED    
*)

Section nindmatch_leq_nminmatch.

Let psi (M : {fset `E(G)}) (Mmax : M \in maximal_matching G) e :=
      (phi Mmax e).1.

Let psi_E (M : {fset `E(G)}) (Mmax : M \in maximal_matching G) e :
  psi Mmax e \in `E(G).
Proof.
by [].
Qed.

Let psi_M (M : {fset `E(G)}) (Mmax : M \in maximal_matching G) e :
  psi Mmax e \in M. 
Proof.
rewrite /psi /phi.
case: boolp.cid => ? [] *.
by case: boolp.cid.
Qed.

Lemma psi_inj (M : {fset `E(G)}) (Mmax : M \in maximal_matching G) (N : {fset `E(G)}) e0 e1 :
  N \in induced_matching G -> e0 \in N -> e1 \in N ->
  psi Mmax e0 == psi Mmax e1 -> e0 == e1.
Proof.
rewrite /psi.
move/induced_matchingP.
move/[apply] /[apply] => disj01.
apply: contraLR => nege01.
apply/eqP => p01.
case: (disj01 nege01 (phi Mmax e0).1).
  rewrite /fdisjoint => /fset0Pn; apply.
  exists (phi Mmax e0).2.
  by rewrite inE phi_boundary phi_boundary_self.
rewrite p01.
rewrite /fdisjoint => /fset0Pn; apply.
exists (phi Mmax e1).2.
by rewrite inE phi_boundary phi_boundary_self.
Qed.

Lemma nindmatch_leq_nminmatch : nindmatch G <= nminmatch G.
Proof.
case: (exists_nindmatch G) => N Nind ->.
case: (exists_nminmatch G) => M Mmax ->.
rewrite 2!cardfE.
set f : N -> M := fun n => [` (psi_M Mmax (val n)) ].
apply: (leq_card f).
move=> e0 e1.
move/eqP => fe01.
apply/eqP.
move: fe01.
move/(psi_inj Nind).
rewrite /f.
by rewrite 2!fsvalP => /(_ erefl erefl).
Qed.

End nindmatch_leq_nminmatch.

End nmatch_leq_double_nminmatch.

Lemma card_matching_leq_nmatch (G : llugraph) (M : {fset `E(G)}) :
  (M \in matching G) -> (#|` M | =  nmatch G) -> M \in maximal_matching G.
Proof.
move=> MmG.
rewrite /nmatch.
rewrite (bigop.bigmax_eq_arg fset0) ?fset0_matching //.
case: arg_maxnP; first exact:fset0_matching.
move=> S SmG /[swap] <- H.
apply/maximal_matchingP; split => //.
move=> T  /fproper_ltn_card MT; apply/negP => TmG.
have := H T TmG => /=.
apply/negP.
by rewrite -ltnNge.
Qed.

End matching_number_lemmas.
